//! Trace generation for the deferred transcript's 32-row Eidos compression chiplet.

use alloc::{collections::BTreeMap, vec, vec::Vec};
use core::ops::Range;

use miden_air::trace::and8_lookup::{
    AND8_LOOKUP_TRACE_HEIGHT, BYTE_LOOKUP_COUNT_LEN, BYTE_LOOKUP_KIND_AND8, BYTE_LOOKUP_KIND_COUNT,
    BYTE_LOOKUP_KIND_EIDOS_COMPRESSION_ROT7, BYTE_LOOKUP_KIND_EIDOS_COMPRESSION_ROT12,
    BYTE_PAIR_ROWS, NUM_AND8_LOOKUP_COLS, RANGE_CHECK_COUNT_OFFSET, RANGE_CHECK_LOOKUP_COL,
    byte_lookup_result,
};
use miden_core::{
    Felt, Word,
    deferred::{DEFERRED_AND_INIT_CV, DEFERRED_CHUNKS_DOMAIN, DEFERRED_NODE_DOMAIN},
    field::{Field, PrimeCharacteristicRing, PrimeField64},
    utils::RowMajorMatrix,
};
use miden_crypto::hash::eidos::Eidos;

use super::compression::{
    layout::{BLOCK_PERIOD as EIDOS_COMPRESSION_CYCLE_LEN, NUM_COLS as NUM_EIDOS_COMPRESSION_COLS},
    trace::{
        ByteLookupRecorder, EidosCompressionByteLookup,
        write_felt_trace_block_into_zeroed_with_lookups,
    },
};
use crate::{
    relations::ProvideMult,
    transcript::eidos::{
        COL_ABSORPTION_ID, COL_CHAIN_CONTEXT_BEGIN, COL_CV_IN_BEGIN, COL_IN_MULTIPLICITY,
        COL_IS_ABSORB, COL_IS_AND, COL_IS_CHUNKS, COL_IS_GENERIC, COL_IS_HEAD, COL_IS_OUTPUT,
        COL_IS_PAYLOAD, COL_OUT_MULTIPLICITY, COL_REMAINING, COL_REMAINING_INV, NUM_MAIN_COLS,
        digest::{EidosChainContext, EidosDigest},
    },
};

// ABSORPTION OUTPUT
// ================================================================================================

/// Logical input-block identifier used by the surrounding transcript relations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AbsorptionId(u32);

impl AbsorptionId {
    pub fn as_u32(self) -> u32 {
        self.0
    }

    #[cfg(test)]
    pub(crate) fn forged(absorption_id: u32) -> Self {
        Self(absorption_id)
    }
}

/// Contiguous logical input-block span occupied by one absorption.
///
/// Generic tagged nodes have one additional physical Eidos compression for `tag || 0w`;
/// that finalizer reuses the span tail's external id and is not counted here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AbsorptionSpan {
    start: u32,
    len: u32,
}

impl AbsorptionSpan {
    fn new(range: Range<u32>) -> Self {
        Self {
            start: range.start,
            len: range.end - range.start,
        }
    }

    pub fn head(self) -> AbsorptionId {
        AbsorptionId(self.start)
    }

    pub fn tail(self) -> AbsorptionId {
        AbsorptionId(self.start + self.len - 1)
    }

    pub fn n_cycles(self) -> u32 {
        self.len
    }
}

#[derive(Debug, Clone)]
pub struct AbsorptionOutput {
    pub digest: EidosDigest,
    pub span: AbsorptionSpan,
}

impl AbsorptionOutput {
    pub fn head(&self) -> AbsorptionId {
        self.span.head()
    }

    pub fn tail(&self) -> AbsorptionId {
        self.span.tail()
    }
}

// EIDOS ORACLE
// ================================================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AbsorptionKind {
    And,
    Chunks,
    Generic,
}

fn absorption_kind(context: EidosChainContext) -> AbsorptionKind {
    if context == EidosChainContext::and() {
        AbsorptionKind::And
    } else if context == EidosChainContext::chunk() {
        AbsorptionKind::Chunks
    } else {
        AbsorptionKind::Generic
    }
}

fn block_from_words(block_lo: [Felt; 4], block_hi: [Felt; 4]) -> [Felt; 8] {
    let mut block = [Felt::ZERO; 8];
    block[..4].copy_from_slice(&block_lo);
    block[4..].copy_from_slice(&block_hi);
    block
}

fn initial_cv(kind: AbsorptionKind, num_payload_blocks: usize) -> Word {
    let payload_felts = u32::try_from(num_payload_blocks * 8)
        .expect("deferred absorption felt length must fit in u32");
    match kind {
        AbsorptionKind::And => {
            assert_eq!(num_payload_blocks, 1, "AND must contain one digest pair");
            DEFERRED_AND_INIT_CV
        },
        AbsorptionKind::Chunks => Eidos::init_chaining_word(
            DEFERRED_CHUNKS_DOMAIN.as_canonical_u64() as u32,
            payload_felts,
        ),
        AbsorptionKind::Generic => Eidos::init_chaining_word(
            DEFERRED_NODE_DOMAIN.as_canonical_u64() as u32,
            payload_felts.checked_add(4).expect("generic node felt length overflow"),
        ),
    }
}

fn tag_block(context: EidosChainContext) -> [Felt; 8] {
    let mut block = [Felt::ZERO; 8];
    block[..4].copy_from_slice(&context.as_array());
    block
}

fn absorb_oracle(context: EidosChainContext, blocks: &[([Felt; 4], [Felt; 4])]) -> EidosDigest {
    let kind = absorption_kind(context);
    let mut cv = initial_cv(kind, blocks.len());
    for &(block_lo, block_hi) in blocks {
        cv = Eidos::compress(cv, block_from_words(block_lo, block_hi));
    }
    if kind == AbsorptionKind::Generic {
        cv = Eidos::compress(cv, tag_block(context));
    }
    EidosDigest(cv.into_elements())
}

// REQUIRES ACCUMULATOR
// ================================================================================================

#[derive(Debug, Clone)]
struct RecordedAbsorption {
    chain_context: EidosChainContext,
    blocks: Vec<([Felt; 4], [Felt; 4])>,
    digest: EidosDigest,
    range: Range<u32>,
    in_mult: ProvideMult,
    out_mult: ProvideMult,
}

#[derive(Debug, Clone, Default)]
pub struct EidosRequires {
    absorptions: Vec<RecordedAbsorption>,
    by_digest: BTreeMap<EidosDigest, usize>,
    next_seq: u32,
}

impl EidosRequires {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn digest_of(
        chain_context: EidosChainContext,
        blocks: &[([Felt; 4], [Felt; 4])],
    ) -> EidosDigest {
        assert!(!blocks.is_empty(), "absorption needs at least one block");
        absorb_oracle(chain_context, blocks)
    }

    pub fn require_absorption(
        &mut self,
        chain_context: EidosChainContext,
        blocks: impl IntoIterator<Item = ([Felt; 4], [Felt; 4])>,
    ) -> AbsorptionOutput {
        let blocks: Vec<_> = blocks.into_iter().collect();
        assert!(!blocks.is_empty(), "absorption needs at least one block");
        let digest = absorb_oracle(chain_context, &blocks);

        if let Some(&idx) = self.by_digest.get(&digest) {
            let rec = &mut self.absorptions[idx];
            debug_assert_eq!(
                rec.chain_context, chain_context,
                "equal digest must identify the same chain context"
            );
            debug_assert_eq!(rec.blocks, blocks, "equal digest must identify the same payload");
            rec.in_mult += 1;
            return AbsorptionOutput {
                digest,
                span: AbsorptionSpan::new(rec.range.clone()),
            };
        }

        let n = u32::try_from(blocks.len()).expect("absorption block count must fit in u32");
        let range = self.next_seq..self.next_seq + n;
        self.next_seq += n;
        let idx = self.absorptions.len();
        self.absorptions.push(RecordedAbsorption {
            chain_context,
            blocks,
            digest,
            range: range.clone(),
            in_mult: 1,
            out_mult: 0,
        });
        self.by_digest.insert(digest, idx);
        AbsorptionOutput { digest, span: AbsorptionSpan::new(range) }
    }

    pub fn require_one_shot(
        &mut self,
        chain_context: EidosChainContext,
        block_lo: [Felt; 4],
        block_hi: [Felt; 4],
    ) -> AbsorptionOutput {
        self.require_absorption(chain_context, core::iter::once((block_lo, block_hi)))
    }

    pub fn require_digest(&mut self, digest: EidosDigest) -> Option<AbsorptionSpan> {
        let &idx = self.by_digest.get(&digest)?;
        let rec = &mut self.absorptions[idx];
        rec.out_mult += 1;
        Some(AbsorptionSpan::new(rec.range.clone()))
    }

    pub fn lookup(&self, digest: EidosDigest) -> Option<AbsorptionSpan> {
        self.by_digest
            .get(&digest)
            .map(|&idx| AbsorptionSpan::new(self.absorptions[idx].range.clone()))
    }

    /// Number of logical payload compressions allocated to surrounding transcript buses.
    pub fn total_cycles(&self) -> u32 {
        self.next_seq
    }
}

// TRACE GENERATION
// ================================================================================================

/// The integrated PVM Eidos compression trace and its fixed byte-operation lookup trace.
#[derive(Debug)]
pub struct EidosTraceBundle {
    pub compression: RowMajorMatrix<Felt>,
    pub and8: RowMajorMatrix<Felt>,
}

#[derive(Debug)]
struct CompressionCycle {
    absorption_id: u32,
    in_mult: ProvideMult,
    out_mult: ProvideMult,
    is_head: bool,
    is_payload: bool,
    is_output: bool,
    kind: AbsorptionKind,
    remaining: usize,
    block: [Felt; 8],
    chain_context: EidosChainContext,
    cv_in: Word,
}

impl CompressionCycle {
    fn append_metadata(&self, row: &mut Vec<Felt>) {
        let start = row.len();
        row.resize(start + (NUM_MAIN_COLS - NUM_EIDOS_COMPRESSION_COLS), Felt::ZERO);
        let meta = &mut row[start..];
        let col = |absolute: usize| absolute - NUM_EIDOS_COMPRESSION_COLS;
        meta[col(COL_ABSORPTION_ID)] = Felt::from(self.absorption_id);
        meta[col(COL_IN_MULTIPLICITY)] = Felt::from(self.in_mult);
        meta[col(COL_OUT_MULTIPLICITY)] = Felt::from(self.out_mult);
        meta[col(COL_IS_HEAD)] = Felt::from_u8(self.is_head as u8);
        meta[col(COL_IS_ABSORB)] = Felt::from_u8((!self.is_head) as u8);
        meta[col(COL_IS_PAYLOAD)] = Felt::from_u8(self.is_payload as u8);
        meta[col(COL_IS_OUTPUT)] = Felt::from_u8(self.is_output as u8);
        meta[col(COL_IS_AND)] = Felt::from_u8((self.kind == AbsorptionKind::And) as u8);
        meta[col(COL_IS_CHUNKS)] = Felt::from_u8((self.kind == AbsorptionKind::Chunks) as u8);
        meta[col(COL_IS_GENERIC)] = Felt::from_u8((self.kind == AbsorptionKind::Generic) as u8);
        let remaining = Felt::from(
            u32::try_from(self.remaining).expect("remaining compression count must fit in u32"),
        );
        meta[col(COL_REMAINING)] = remaining;
        meta[col(COL_REMAINING_INV)] = if self.remaining == 1 {
            Felt::ZERO
        } else {
            (remaining - Felt::ONE).inverse()
        };
        meta[col(COL_CHAIN_CONTEXT_BEGIN)..col(COL_CHAIN_CONTEXT_BEGIN) + 4]
            .copy_from_slice(&self.chain_context.as_array());
        meta[col(COL_CV_IN_BEGIN)..col(COL_CV_IN_BEGIN) + 4].copy_from_slice(self.cv_in.as_slice());
    }
}

struct EidosCompressionLookupCounter<'a> {
    counts: &'a mut [u64],
}

impl ByteLookupRecorder for EidosCompressionLookupCounter<'_> {
    fn record(&mut self, lookup: EidosCompressionByteLookup, lhs: u8, rhs: u8, result: u32) {
        let kind = match lookup {
            EidosCompressionByteLookup::And8 => BYTE_LOOKUP_KIND_AND8,
            EidosCompressionByteLookup::Rot12 { byte } => {
                BYTE_LOOKUP_KIND_EIDOS_COMPRESSION_ROT12[byte]
            },
            EidosCompressionByteLookup::Rot7 { byte } => {
                BYTE_LOOKUP_KIND_EIDOS_COMPRESSION_ROT7[byte]
            },
        };
        debug_assert_eq!(byte_lookup_result(kind, lhs, rhs), result);
        let pair = ((lhs as usize) << 8) + rhs as usize;
        self.counts[kind * BYTE_PAIR_ROWS + pair] += 1;
    }
}

fn unpack_felts<const N: usize>(values: &[Felt]) -> [u32; N] {
    assert_eq!(
        2 * values.len(),
        N,
        "packed Felt slice must contain exactly {N} EidosCompression words",
    );

    let mut words = [0; N];
    for (idx, value) in values.iter().enumerate() {
        let packed = value.as_canonical_u64();
        words[2 * idx] = packed as u32;
        words[2 * idx + 1] = (packed >> 32) as u32;
    }
    words
}

fn record_message_range_checks(counts: &mut [u64], block: [u32; 16]) {
    for word in block {
        for limb in [word as u16, (word >> 16) as u16] {
            counts[RANGE_CHECK_COUNT_OFFSET + limb as usize] += 1;
        }
    }
}

fn build_and8_trace(counts: &[u64]) -> RowMajorMatrix<Felt> {
    assert_eq!(counts.len(), BYTE_LOOKUP_COUNT_LEN);
    let mut values = vec![Felt::ZERO; AND8_LOOKUP_TRACE_HEIGHT * NUM_AND8_LOOKUP_COLS];
    for pair in 0..BYTE_PAIR_ROWS {
        for kind in 0..BYTE_LOOKUP_KIND_COUNT {
            let count = counts[kind * BYTE_PAIR_ROWS + pair];
            assert!(count < Felt::ORDER_U64, "byte lookup multiplicity must be canonical");
            values[pair * NUM_AND8_LOOKUP_COLS + kind] = Felt::new_unchecked(count);
        }
        let count = counts[RANGE_CHECK_COUNT_OFFSET + pair];
        assert!(count < Felt::ORDER_U64, "range lookup multiplicity must be canonical");
        values[pair * NUM_AND8_LOOKUP_COLS + RANGE_CHECK_LOOKUP_COL] = Felt::new_unchecked(count);
    }
    RowMajorMatrix::new(values, NUM_AND8_LOOKUP_COLS)
}

fn build_eidos_compression_traces(
    cycles: &[CompressionCycle],
) -> (RowMajorMatrix<Felt>, RowMajorMatrix<Felt>) {
    let real_cycles = cycles.len();
    let height = (real_cycles * EIDOS_COMPRESSION_CYCLE_LEN)
        .next_power_of_two()
        .max(EIDOS_COMPRESSION_CYCLE_LEN);
    let cycle_count = height / EIDOS_COMPRESSION_CYCLE_LEN;
    let mut values = vec![Felt::ZERO; height * NUM_EIDOS_COMPRESSION_COLS];
    let (rows, remainder) = values.as_chunks_mut::<NUM_EIDOS_COMPRESSION_COLS>();
    debug_assert!(remainder.is_empty());
    let mut counts = vec![0u64; BYTE_LOOKUP_COUNT_LEN];

    for (physical_cycle_id, cycle_rows) in
        rows.as_chunks_mut::<EIDOS_COMPRESSION_CYCLE_LEN>().0.iter_mut().enumerate()
    {
        let (block, cv) = if let Some(cycle) = cycles.get(physical_cycle_id) {
            let block = unpack_felts::<16>(&cycle.block);
            let cv = unpack_felts::<8>(cycle.cv_in.as_slice());
            (block, cv)
        } else {
            ([0; 16], [0; 8])
        };

        record_message_range_checks(&mut counts, block);
        let mut recorder = EidosCompressionLookupCounter { counts: &mut counts };
        write_felt_trace_block_into_zeroed_with_lookups(
            cycle_rows,
            block,
            cv,
            physical_cycle_id as u64,
            &mut recorder,
        );
    }

    debug_assert_eq!(cycle_count, rows.len() / EIDOS_COMPRESSION_CYCLE_LEN);
    (
        RowMajorMatrix::new(values, NUM_EIDOS_COMPRESSION_COLS),
        build_and8_trace(&counts),
    )
}

pub fn generate_traces(requires: EidosRequires) -> EidosTraceBundle {
    let physical_cycles: usize = requires
        .absorptions
        .iter()
        .map(|rec| {
            rec.blocks.len()
                + usize::from(absorption_kind(rec.chain_context) == AbsorptionKind::Generic)
        })
        .sum();
    let mut cycles = Vec::with_capacity(physical_cycles);

    for rec in &requires.absorptions {
        let kind = absorption_kind(rec.chain_context);
        let extra = usize::from(kind == AbsorptionKind::Generic);
        let total = rec.blocks.len() + extra;
        let mut cv = initial_cv(kind, rec.blocks.len());

        for (idx, &(block_lo, block_hi)) in rec.blocks.iter().enumerate() {
            let block = block_from_words(block_lo, block_hi);
            let cv_out = Eidos::compress(cv, block);
            let is_output = kind != AbsorptionKind::Generic && idx + 1 == rec.blocks.len();
            cycles.push(CompressionCycle {
                absorption_id: rec.range.start + idx as u32,
                in_mult: rec.in_mult,
                out_mult: if is_output { rec.out_mult } else { 0 },
                is_head: idx == 0,
                is_payload: true,
                is_output,
                kind,
                remaining: total - idx,
                block,
                chain_context: rec.chain_context,
                cv_in: cv,
            });
            cv = cv_out;
        }

        if kind == AbsorptionKind::Generic {
            let block = tag_block(rec.chain_context);
            let cv_out = Eidos::compress(cv, block);
            cycles.push(CompressionCycle {
                absorption_id: rec.range.end - 1,
                in_mult: 0,
                out_mult: rec.out_mult,
                is_head: false,
                is_payload: false,
                is_output: true,
                kind,
                remaining: 1,
                block,
                chain_context: rec.chain_context,
                cv_in: cv,
            });
            cv = cv_out;
        }

        debug_assert_eq!(EidosDigest(cv.into_elements()), rec.digest);
    }

    let (eidos_compression, and8) = build_eidos_compression_traces(&cycles);
    let height = eidos_compression.values.len() / eidos_compression.width;
    debug_assert_eq!(height % EIDOS_COMPRESSION_CYCLE_LEN, 0);
    debug_assert!(cycles.len() * EIDOS_COMPRESSION_CYCLE_LEN <= height);

    let mut values = Vec::with_capacity(height * NUM_MAIN_COLS);
    for (row_idx, base_row) in
        eidos_compression.values.chunks_exact(eidos_compression.width).enumerate()
    {
        values.extend_from_slice(base_row);
        let cycle_idx = row_idx / EIDOS_COMPRESSION_CYCLE_LEN;
        if let Some(cycle) = cycles.get(cycle_idx) {
            cycle.append_metadata(&mut values);
        } else {
            values.extend([Felt::ZERO; NUM_MAIN_COLS - NUM_EIDOS_COMPRESSION_COLS]);
        }
    }

    EidosTraceBundle {
        compression: RowMajorMatrix::new(values, NUM_MAIN_COLS),
        and8,
    }
}

pub fn generate_trace(requires: EidosRequires) -> RowMajorMatrix<Felt> {
    generate_traces(requires).compression
}

const _: () = assert!(EIDOS_COMPRESSION_CYCLE_LEN == 32);
