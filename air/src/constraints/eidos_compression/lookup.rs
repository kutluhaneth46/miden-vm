//! Lookup columns for the 32-row Eidos compression layout.

#[cfg(test)]
use alloc::vec::Vec;
use core::borrow::Borrow;

use miden_core::{
    Felt,
    field::{Algebra, PrimeCharacteristicRing},
};
#[cfg(test)]
use miden_crypto::stark::air::WindowAccess;

use super::{
    algebra::{missing_rotation_result, pack_u32_le, universal_cv_word, xor_from_and},
    layout::*,
    selectors::EidosCompressionSelectors,
};
#[cfg(test)]
use crate::{constraints::lookup::MIDEN_MAX_MESSAGE_WIDTH, lookup::LookupAir};
use crate::{
    constraints::lookup::messages::{
        AeadEidosCompressionOutputPairMsg, BusId, eidos_compression_rot7_bus,
        eidos_compression_rot12_bus,
    },
    lookup::{
        Challenges, Deg, LookupBatch, LookupBuilder, LookupColumn, LookupGroup, LookupMessage,
    },
};

#[cfg(test)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum EidosCompressionMode {
    Compression,
    AeadXof,
}

#[cfg(test)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum NarrowLookupKind {
    And8,
    Rot12,
    Rot7,
    MessageWord,
    RangeCheck,
}

#[cfg(test)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NarrowLookup {
    pub kind: NarrowLookupKind,
    pub sign: i8,
}

#[cfg(test)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum OverlayRelationKind {
    FullCv,
    CompressionLink,
    AeadInput,
    AeadLowOutputPair,
    AeadHighOutputPair,
}

#[cfg(test)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct OverlayRelation {
    pub kind: OverlayRelationKind,
    pub sign: i8,
}

#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LookupPlan {
    pub narrow: Vec<NarrowLookup>,
    pub overlay_relations: Vec<OverlayRelation>,
}

#[cfg(test)]
impl LookupPlan {
    pub fn narrow_aux_columns(&self) -> usize {
        self.narrow.len().div_ceil(2)
    }
}

/// Typed view of the 108 Eidos compression main-trace columns.
#[repr(C)]
#[derive(Clone, Debug)]
pub struct EidosCompressionCols<T> {
    /// Physical columns in the layout documented by the Eidos compression module.
    pub columns: [T; NUM_COLS],
}

/// Mode-selected external input with a shared 16-field payload.
///
/// Compression and AEAD use the same `[block_or_state(8), cv_in(4), tail(4)]` field order. Only
/// their domain-separated bus prefixes differ, so selecting the mode never multiplies a witness
/// value and the encoded denominator remains linear.
#[derive(Debug)]
struct FooterInputMsg<E> {
    mode: E,
    block: [E; 8],
    cv_in: [E; 4],
    tail: [E; 4],
}

/// Cycle-tagged internal relation carrying all eight raw chaining-value words atomically.
#[derive(Debug)]
struct FullCvMsg<E> {
    compression_cycle_id: E,
    words: [E; 8],
}

impl<E, EF> LookupMessage<E, EF> for FooterInputMsg<E>
where
    E: PrimeCharacteristicRing,
    EF: Algebra<E>,
{
    fn encode(&self, challenges: &Challenges<EF>) -> EF {
        let compression_prefix =
            challenges.bus_prefix[BusId::HasherCompressionLink as usize].clone();
        let aead_prefix = challenges.bus_prefix[BusId::AeadEidosCompressionInput as usize].clone();
        let mut encoded =
            compression_prefix.clone() + (aead_prefix - compression_prefix) * self.mode.clone();
        for (idx, field) in
            self.block.iter().chain(self.cv_in.iter()).chain(self.tail.iter()).enumerate()
        {
            encoded += challenges.beta_powers[idx].clone() * field.clone();
        }
        encoded
    }
}

impl<E, EF> LookupMessage<E, EF> for FullCvMsg<E>
where
    E: PrimeCharacteristicRing,
    EF: Algebra<E>,
{
    fn encode(&self, challenges: &Challenges<EF>) -> EF {
        let fields: [E; 9] = core::array::from_fn(|idx| {
            if idx == 0 {
                self.compression_cycle_id.clone()
            } else {
                self.words[idx - 1].clone()
            }
        });
        challenges.encode(BusId::EidosCompressionInputCv as usize, fields)
    }
}

impl<T> Borrow<EidosCompressionCols<T>> for [T] {
    fn borrow(&self) -> &EidosCompressionCols<T> {
        debug_assert_eq!(self.len(), NUM_COLS);
        // SAFETY: `EidosCompressionCols<T>` is `repr(C)` and contains exactly one `[T; NUM_COLS]`
        // field. It therefore has the same alignment, size, and valid bit patterns as the input
        // slice after the length check above.
        let (prefix, cols, suffix) = unsafe { self.align_to::<EidosCompressionCols<T>>() };
        debug_assert!(prefix.is_empty());
        debug_assert!(suffix.is_empty());
        debug_assert_eq!(cols.len(), 1);
        &cols[0]
    }
}

/// Number of lookup fractions grouped into each Eidos compression auxiliary column.
pub(crate) const EIDOS_COMPRESSION_LOOKUP_COLUMN_SHAPE: [usize; AUX_COLS] = [2; AUX_COLS];

pub(crate) const NARROW_BATCH_COLUMNS: usize = 18;
pub(crate) const FOOTER_INPUT_COLUMN: usize = 18;
pub(crate) const FOOTER_OUTPUT_COLUMN: usize = 19;

#[cfg(test)]
const FOOTER_HIGH_AND8_LOOKUPS: usize = 2 * BYTES_PER_WORD;
#[cfg(test)]
const FOOTER_LOW_AND8_LOOKUPS: usize = 2 * BYTES_PER_WORD;
#[cfg(test)]
const FOOTER_TOP_BIT_AND8_LOOKUPS: usize = 1;
#[cfg(test)]
const FOOTER_AND8_LOOKUPS: usize =
    FOOTER_HIGH_AND8_LOOKUPS + FOOTER_LOW_AND8_LOOKUPS + FOOTER_TOP_BIT_AND8_LOOKUPS;

const BATCH2_DEG: Deg = Deg { v: 2, u: 2 };
const FOOTER_INPUT_DEG: Deg = Deg { v: 3, u: 2 };
const FOOTER_OUTPUT_BATCH2_DEG: Deg = Deg { v: 3, u: 2 };
fn selected_column_deg(aux_col: usize) -> Deg {
    match aux_col {
        0..NARROW_BATCH_COLUMNS => BATCH2_DEG,
        FOOTER_INPUT_COLUMN => FOOTER_INPUT_DEG,
        FOOTER_OUTPUT_COLUMN => FOOTER_OUTPUT_BATCH2_DEG,
        _ => unreachable!("32-row EidosCompression lookup aux column out of range"),
    }
}

#[cfg(test)]
#[derive(Copy, Clone, Debug, Default)]
pub struct EidosCompressionLookupAir;

/// Lookup builder accepted by the Eidos compression AIR.
pub(crate) trait EidosCompressionLookupBuilder: LookupBuilder<F = Felt> {}

impl<T> EidosCompressionLookupBuilder for T where T: LookupBuilder<F = Felt> {}

#[cfg(test)]
impl<LB> LookupAir<LB> for EidosCompressionLookupAir
where
    LB: EidosCompressionLookupBuilder,
{
    fn num_columns(&self) -> usize {
        EIDOS_COMPRESSION_LOOKUP_COLUMN_SHAPE.len()
    }

    fn column_shape(&self) -> &[usize] {
        &EIDOS_COMPRESSION_LOOKUP_COLUMN_SHAPE
    }

    fn max_message_width(&self) -> usize {
        MIDEN_MAX_MESSAGE_WIDTH
    }

    fn num_bus_ids(&self) -> usize {
        BusId::COUNT
    }

    fn eval(&self, builder: &mut LB) {
        let main = builder.main();
        let local: &EidosCompressionCols<_> = main.current_slice().borrow();
        let next: &EidosCompressionCols<_> = main.next_slice().borrow();
        let periodic_values: Vec<LB::Expr> =
            builder.periodic_values().iter().map(|value| (*value).into()).collect();
        let selectors = EidosCompressionSelectors::new(&periodic_values, 0);

        emit_lookup_columns(builder, local, next, &selectors);
    }
}

/// Emits all Eidos compression lookup groups in their fixed auxiliary-column order.
pub(crate) fn emit_lookup_columns<LB>(
    builder: &mut LB,
    local: &EidosCompressionCols<LB::Var>,
    next: &EidosCompressionCols<LB::Var>,
    selectors: &EidosCompressionSelectors<LB::Expr>,
) where
    LB: EidosCompressionLookupBuilder,
{
    for aux_col in 0..EIDOS_COMPRESSION_LOOKUP_COLUMN_SHAPE.len() {
        let column_deg = selected_column_deg(aux_col);
        builder.next_column(
            |col| {
                col.group(
                    "eidos_compression",
                    |group| emit_lookup_column::<LB, _>(group, local, next, selectors, aux_col),
                    column_deg,
                );
            },
            column_deg,
        );
    }
}

fn emit_lookup_column<LB, G>(
    group: &mut G,
    local: &EidosCompressionCols<LB::Var>,
    next: &EidosCompressionCols<LB::Var>,
    selectors: &EidosCompressionSelectors<LB::Expr>,
    aux_col: usize,
) where
    LB: EidosCompressionLookupBuilder,
    G: LookupGroup<Expr = LB::Expr, ExprEF = LB::ExprEF>,
{
    match aux_col {
        0..NARROW_BATCH_COLUMNS => {
            emit_narrow_pair::<LB, G>(group, local, next, selectors, aux_col)
        },
        FOOTER_INPUT_COLUMN..=FOOTER_OUTPUT_COLUMN => {
            emit_footer_column::<LB, G>(group, local, selectors, aux_col)
        },
        _ => unreachable!("32-row EidosCompression lookup aux column out of range"),
    }
}

fn emit_narrow_pair<LB, G>(
    group: &mut G,
    local: &EidosCompressionCols<LB::Var>,
    next: &EidosCompressionCols<LB::Var>,
    selectors: &EidosCompressionSelectors<LB::Expr>,
    aux_col: usize,
) where
    LB: EidosCompressionLookupBuilder,
    G: LookupGroup<Expr = LB::Expr, ExprEF = LB::ExprEF>,
{
    let slot0 = 2 * aux_col;
    let slot1 = slot0 + 1;
    let slot0_multiplicity = narrow_slot_multiplicity::<LB>(slot0, selectors);
    let slot1_multiplicity = narrow_slot_multiplicity::<LB>(slot1, selectors);
    let slot0_encoding = narrow_slot_encoding::<LB, G>(&*group, local, next, selectors, slot0);
    let slot1_encoding = narrow_slot_encoding::<LB, G>(&*group, local, next, selectors, slot1);

    group.selected_batch2_encoded(
        "narrow_pair",
        "slot0",
        slot0_multiplicity,
        || slot0_encoding,
        "slot1",
        slot1_multiplicity,
        || slot1_encoding,
    );
}

fn emit_footer_column<LB, G>(
    group: &mut G,
    local: &EidosCompressionCols<LB::Var>,
    selectors: &EidosCompressionSelectors<LB::Expr>,
    aux_col: usize,
) where
    LB: EidosCompressionLookupBuilder,
    G: LookupGroup<Expr = LB::Expr, ExprEF = LB::ExprEF>,
{
    let mode = c::<LB>(local, F_MODE_COL);
    let is_f3 = selectors.is_footer_row(FOOTER_ROWS - 1);

    match aux_col {
        FOOTER_INPUT_COLUMN => {
            // Both denominators are linear. The CV multiplicity has degree one and the selected
            // external-input multiplicity has degree two, so the batched U has degree two and V
            // has degree three. On the first fused row, and on a zero-multiplicity compression
            // padding footer, the external-input denominator remains in the cross product with
            // zero multiplicity. Its alpha coefficient is one, so it cannot vanish identically;
            // cancellation is limited to the standard random-denominator bad event. This layout
            // has at most 40 denominator factors per row, versus at most 44 in the 24-column
            // layout. The handwritten auxiliary pin covers rows where both relations are inactive.
            let cv_multiplicity = is_f3.clone() - selectors.is_first_fused();
            let input_multiplicity =
                -is_f3 * (c::<LB>(local, F_COMPRESSION_MULTIPLICITY_COL) + mode.clone());
            group.batch(
                "full_cv_and_external_input",
                LB::Expr::ONE,
                |batch| {
                    batch.insert(
                        "full_cv",
                        cv_multiplicity,
                        full_cv_msg::<LB>(local),
                        Deg { v: 1, u: 1 },
                    );
                    batch.insert(
                        "compression_or_aead_input",
                        input_multiplicity,
                        footer_input_msg::<LB>(local, mode),
                        Deg { v: 2, u: 1 },
                    );
                },
                FOOTER_INPUT_DEG,
            );
        },
        FOOTER_OUTPUT_COLUMN => {
            // Both outputs are active together in AEAD mode. A separate handwritten extension
            // constraint pins this auxiliary column to zero on every other row, including when
            // either denominator is zero. Each denominator is linear and the common multiplicity
            // has degree two, giving degree two for U and degree three for V.
            let multiplicity = -selectors.is_footer() * mode;
            group.batch(
                "aead_output_pairs",
                LB::Expr::ONE,
                |batch| {
                    batch.insert(
                        "aead_low_output_pair",
                        multiplicity.clone(),
                        aead_output_pair_msg_for_current_footer::<LB>(local, selectors, 0),
                        Deg { v: 2, u: 1 },
                    );
                    batch.insert(
                        "aead_high_output_pair",
                        multiplicity,
                        aead_output_pair_msg_for_current_footer::<LB>(local, selectors, 8),
                        Deg { v: 2, u: 1 },
                    );
                },
                FOOTER_OUTPUT_BATCH2_DEG,
            );
        },
        _ => unreachable!("32-row Eidos compression footer aux column out of range"),
    }
}

fn narrow_slot_multiplicity<LB>(
    slot: usize,
    selectors: &EidosCompressionSelectors<LB::Expr>,
) -> LB::Expr
where
    LB: EidosCompressionLookupBuilder,
{
    let fused = is_fused::<LB>(selectors);
    let footer = selectors.is_footer();

    match slot {
        0..=17 => -(fused + footer),
        18..=21 | 27 | 30..=31 => -fused,
        22..=26 | 28..=29 => -(fused + footer),
        32..=35 => fused - expr::<LB>(7) * footer,
        _ => unreachable!("32-row EidosCompression narrow slot out of range"),
    }
}

fn narrow_slot_encoding<LB, G>(
    group: &G,
    local: &EidosCompressionCols<LB::Var>,
    next: &EidosCompressionCols<LB::Var>,
    selectors: &EidosCompressionSelectors<LB::Expr>,
    slot: usize,
) -> G::ExprEF
where
    LB: EidosCompressionLookupBuilder,
    G: LookupGroup<Expr = LB::Expr, ExprEF = LB::ExprEF>,
{
    let mut encoded = G::ExprEF::ZERO;

    if slot <= 15 {
        add_bus(&mut encoded, group, BusId::And8Lookup, is_fused::<LB>(selectors));
        add_bus(&mut encoded, group, BusId::And8Lookup, selectors.is_footer());
    } else if slot <= 31 {
        add_rot_bus::<LB, G>(&mut encoded, group, slot, selectors);
        add_footer_overlay_slot::<LB, G>(&mut encoded, group, selectors, slot);
    } else if slot <= 35 {
        add_bus(
            &mut encoded,
            group,
            BusId::EidosCompressionMessageWord,
            is_fused::<LB>(selectors) + selectors.is_footer(),
        );
    } else {
        unreachable!("32-row EidosCompression narrow slot out of range");
    }

    let activity = narrow_slot_activity::<LB>(slot, selectors);
    add_bus(&mut encoded, group, BusId::RangeCheck, LB::Expr::ONE - activity);
    add_fields_direct(&mut encoded, group, narrow_slot_fields::<LB>(local, next, selectors, slot));
    encoded
}

fn narrow_slot_activity<LB>(
    slot: usize,
    selectors: &EidosCompressionSelectors<LB::Expr>,
) -> LB::Expr
where
    LB: EidosCompressionLookupBuilder,
{
    match slot {
        0..=17 | 22..=26 | 28..=29 | 32..=35 => is_fused::<LB>(selectors) + selectors.is_footer(),
        18..=21 | 27 | 30..=31 => is_fused::<LB>(selectors),
        _ => unreachable!("32-row EidosCompression narrow slot out of range"),
    }
}

fn add_footer_overlay_slot<LB, G>(
    encoded: &mut G::ExprEF,
    group: &G,
    selectors: &EidosCompressionSelectors<LB::Expr>,
    slot: usize,
) where
    LB: EidosCompressionLookupBuilder,
    G: LookupGroup<Expr = LB::Expr, ExprEF = LB::ExprEF>,
{
    let branch = selectors.is_footer();
    match slot {
        16 => {
            add_bus(encoded, group, BusId::And8Lookup, branch);
        },
        17 | 22..=26 | 28..=29 => {
            add_bus(encoded, group, BusId::RangeCheck, branch);
        },
        _ => {},
    }
}

fn add_rot_bus<LB, G>(
    encoded: &mut G::ExprEF,
    group: &G,
    slot: usize,
    selectors: &EidosCompressionSelectors<LB::Expr>,
) where
    LB: EidosCompressionLookupBuilder,
    G: LookupGroup<Expr = LB::Expr, ExprEF = LB::ExprEF>,
{
    let byte = slot % BYTES_PER_WORD;
    add_bus(encoded, group, eidos_compression_rot12_bus(byte), selectors.is_ab());
    add_bus(encoded, group, eidos_compression_rot7_bus(byte), selectors.is_cd());
}

fn add_bus<G>(encoded: &mut G::ExprEF, group: &G, bus: BusId, selector: G::Expr)
where
    G: LookupGroup,
{
    *encoded = encoded.clone() + group.bus_prefix(bus as usize) * selector;
}

fn add_fields_direct<G>(encoded: &mut G::ExprEF, group: &G, fields: [G::Expr; 3])
where
    G: LookupGroup,
{
    for (idx, field) in fields.into_iter().enumerate() {
        *encoded = encoded.clone() + group.beta_powers()[idx].clone() * field;
    }
}

fn footer_input_msg<LB>(
    local: &EidosCompressionCols<LB::Var>,
    mode: LB::Expr,
) -> FooterInputMsg<LB::Expr>
where
    LB: EidosCompressionLookupBuilder,
{
    FooterInputMsg {
        mode,
        block: footer_block::<LB>(local),
        cv_in: footer_cv_in::<LB>(local),
        tail: footer_tail::<LB>(local),
    }
}

fn full_cv_msg<LB>(local: &EidosCompressionCols<LB::Var>) -> FullCvMsg<LB::Expr>
where
    LB: EidosCompressionLookupBuilder,
{
    FullCvMsg {
        compression_cycle_id: c::<LB>(local, F_COMPRESSION_CYCLE_ID_COL),
        words: core::array::from_fn(|idx| cv_word::<LB>(local, idx)),
    }
}

fn footer_block<LB>(local: &EidosCompressionCols<LB::Var>) -> [LB::Expr; 8]
where
    LB: EidosCompressionLookupBuilder,
{
    core::array::from_fn(|idx| {
        if idx < 6 {
            c::<LB>(local, footer_r_col(FOOTER_ROWS - 1, idx))
        } else {
            let pair = idx - 6;
            pack_pair::<LB>(
                c::<LB>(local, footer_msg_word_col(2 * pair)),
                c::<LB>(local, footer_msg_word_col(2 * pair + 1)),
            )
        }
    })
}

fn footer_cv_in<LB>(local: &EidosCompressionCols<LB::Var>) -> [LB::Expr; 4]
where
    LB: EidosCompressionLookupBuilder,
{
    core::array::from_fn(|idx| {
        pack_pair::<LB>(cv_word::<LB>(local, 2 * idx), cv_word::<LB>(local, 2 * idx + 1))
    })
}

fn footer_tail<LB>(local: &EidosCompressionCols<LB::Var>) -> [LB::Expr; 4]
where
    LB: EidosCompressionLookupBuilder,
{
    core::array::from_fn(|idx| c::<LB>(local, footer_interface_tail_col(idx)))
}

fn cv_word<LB>(local: &EidosCompressionCols<LB::Var>, idx: usize) -> LB::Expr
where
    LB: EidosCompressionLookupBuilder,
{
    universal_cv_word(|col| c::<LB>(local, col), idx)
}

fn pack_pair<LB>(lo: LB::Expr, hi: LB::Expr) -> LB::Expr
where
    LB: EidosCompressionLookupBuilder,
{
    lo + expr::<LB>(1u64 << 32) * hi
}

fn aead_output_pair_msg_for_current_footer<LB>(
    local: &EidosCompressionCols<LB::Var>,
    selectors: &EidosCompressionSelectors<LB::Expr>,
    lane_offset: usize,
) -> AeadEidosCompressionOutputPairMsg<LB::Expr>
where
    LB: EidosCompressionLookupBuilder,
{
    let footer_idx = selectors.is_footer_row(1)
        + expr::<LB>(2) * selectors.is_footer_row(2)
        + expr::<LB>(3) * selectors.is_footer_row(3);
    let [value0, value1] = if lane_offset == 0 {
        footer_output_word::<LB>(local)
    } else {
        footer_high_word::<LB>(local)
    };

    AeadEidosCompressionOutputPairMsg {
        clk: c::<LB>(local, F_CLK_COL),
        first_lane_idx: expr::<LB>(lane_offset as u64) + expr::<LB>(2) * footer_idx,
        value0,
        value1,
    }
}

fn footer_output_word<LB>(local: &EidosCompressionCols<LB::Var>) -> [LB::Expr; 2]
where
    LB: EidosCompressionLookupBuilder,
{
    [
        footer_xor_word::<LB>(local, F_OUTPUT_EVEN_SLOT_BASE),
        footer_xor_word::<LB>(local, F_OUTPUT_ODD_SLOT_BASE),
    ]
}

fn footer_high_word<LB>(local: &EidosCompressionCols<LB::Var>) -> [LB::Expr; 2]
where
    LB: EidosCompressionLookupBuilder,
{
    [
        footer_xor_word::<LB>(local, F_HIGH_EVEN_SLOT_BASE),
        footer_xor_word::<LB>(local, F_HIGH_ODD_SLOT_BASE),
    ]
}

fn footer_xor_word<LB>(local: &EidosCompressionCols<LB::Var>, slot_base: usize) -> LB::Expr
where
    LB: EidosCompressionLookupBuilder,
{
    pack4::<LB>(
        footer_xor_byte::<LB>(local, slot_base),
        footer_xor_byte::<LB>(local, slot_base + 1),
        footer_xor_byte::<LB>(local, slot_base + 2),
        footer_xor_byte::<LB>(local, slot_base + 3),
    )
}

fn footer_xor_byte<LB>(local: &EidosCompressionCols<LB::Var>, slot: usize) -> LB::Expr
where
    LB: EidosCompressionLookupBuilder,
{
    let base = footer_xor_slot_col(slot, 0);
    let lhs = c::<LB>(local, base);
    let rhs = c::<LB>(local, base + 1);
    let and = c::<LB>(local, base + 2);
    xor_from_and(lhs, rhs, and)
}

fn narrow_slot_fields<LB>(
    local: &EidosCompressionCols<LB::Var>,
    next: &EidosCompressionCols<LB::Var>,
    selectors: &EidosCompressionSelectors<LB::Expr>,
    slot: usize,
) -> [LB::Expr; 3]
where
    LB: EidosCompressionLookupBuilder,
{
    match slot {
        0..=30 => fields_at::<LB>(local, byte_slot_base(0, slot)),
        31 => [
            c::<LB>(local, g_bd_rot_slot_col(MISSING_ROTATION_G, MISSING_ROTATION_BYTE, 0)),
            c::<LB>(local, g_bd_rot_slot_col(MISSING_ROTATION_G, MISSING_ROTATION_BYTE, 1)),
            missing_rotation_result(|col| c::<LB>(local, col), |col| c::<LB>(next, col)),
        ],
        32..=35 => {
            let g = slot - 32;
            [
                message_index::<LB>(selectors, g),
                c::<LB>(local, g_msg_word_col(g)),
                c::<LB>(local, G_COMPRESSION_CYCLE_ID_COL),
            ]
        },
        _ => unreachable!("32-row EidosCompression narrow slot out of range"),
    }
}

fn message_index<LB>(selectors: &EidosCompressionSelectors<LB::Expr>, g: usize) -> LB::Expr
where
    LB: EidosCompressionLookupBuilder,
{
    let footer = selectors.is_footer();
    let footer_idx = selectors.is_footer_row(1)
        + expr::<LB>(2) * selectors.is_footer_row(2)
        + expr::<LB>(3) * selectors.is_footer_row(3);
    selectors.sigma_msg_index(g) + expr::<LB>(g as u64) * footer + expr::<LB>(4) * footer_idx
}

fn fields_at<LB>(local: &EidosCompressionCols<LB::Var>, base: usize) -> [LB::Expr; 3]
where
    LB: EidosCompressionLookupBuilder,
{
    [c::<LB>(local, base), c::<LB>(local, base + 1), c::<LB>(local, base + 2)]
}

fn is_fused<LB>(selectors: &EidosCompressionSelectors<LB::Expr>) -> LB::Expr
where
    LB: EidosCompressionLookupBuilder,
{
    selectors.is_ab() + selectors.is_cd()
}

#[inline]
fn c<LB>(local: &EidosCompressionCols<LB::Var>, idx: usize) -> LB::Expr
where
    LB: EidosCompressionLookupBuilder,
{
    local.columns[idx].into()
}

#[inline]
fn expr<LB>(value: u64) -> LB::Expr
where
    LB: EidosCompressionLookupBuilder,
{
    LB::Expr::from(Felt::new_unchecked(value))
}

fn pack4<LB>(b0: LB::Expr, b1: LB::Expr, b2: LB::Expr, b3: LB::Expr) -> LB::Expr
where
    LB: EidosCompressionLookupBuilder,
{
    pack_u32_le(b0, b1, b2, b3)
}

#[cfg(test)]
pub fn lookup_plan(row: usize, mode: EidosCompressionMode) -> LookupPlan {
    let mut plan = LookupPlan {
        narrow: Vec::new(),
        overlay_relations: Vec::new(),
    };

    match row_kind(row) {
        RowKind::Ab => {
            add_fused_g_lookups(&mut plan, NarrowLookupKind::Rot12);
            if row == 0 {
                plan.overlay_relations.push(OverlayRelation {
                    kind: OverlayRelationKind::FullCv,
                    sign: -1,
                });
            }
        },
        RowKind::AbDiag => add_fused_g_lookups(&mut plan, NarrowLookupKind::Rot12),
        RowKind::Cd | RowKind::CdDiag => add_fused_g_lookups(&mut plan, NarrowLookupKind::Rot7),
        RowKind::Footer(footer) => add_footer_lookups(&mut plan, footer, mode),
    }

    plan
}

#[cfg(test)]
fn add_fused_g_lookups(plan: &mut LookupPlan, rotation_kind: NarrowLookupKind) {
    push_narrow(plan, NarrowLookupKind::And8, -1, BYTE_SLOTS_PER_STEP);
    push_narrow(plan, rotation_kind, -1, BYTE_SLOTS_PER_STEP);
    push_narrow(plan, NarrowLookupKind::MessageWord, 1, NUM_G);
}

#[cfg(test)]
fn add_footer_lookups(plan: &mut LookupPlan, footer: usize, mode: EidosCompressionMode) {
    push_narrow(plan, NarrowLookupKind::And8, -1, FOOTER_AND8_LOOKUPS);
    push_narrow(plan, NarrowLookupKind::MessageWord, -7, F_MSG_WORD_SLOTS);
    push_narrow(plan, NarrowLookupKind::RangeCheck, -1, F_RANGE_SLOTS);

    if footer == FOOTER_ROWS - 1 {
        plan.overlay_relations.push(OverlayRelation {
            kind: OverlayRelationKind::FullCv,
            sign: 1,
        });
    }

    match mode {
        EidosCompressionMode::Compression => {
            if footer == FOOTER_ROWS - 1 {
                plan.overlay_relations.push(OverlayRelation {
                    kind: OverlayRelationKind::CompressionLink,
                    sign: -1,
                });
            }
        },
        EidosCompressionMode::AeadXof => {
            if footer == FOOTER_ROWS - 1 {
                plan.overlay_relations.push(OverlayRelation {
                    kind: OverlayRelationKind::AeadInput,
                    sign: -1,
                });
            }
            plan.overlay_relations.push(OverlayRelation {
                kind: OverlayRelationKind::AeadLowOutputPair,
                sign: -1,
            });
            plan.overlay_relations.push(OverlayRelation {
                kind: OverlayRelationKind::AeadHighOutputPair,
                sign: -1,
            });
        },
    }
}

#[cfg(test)]
fn push_narrow(plan: &mut LookupPlan, kind: NarrowLookupKind, sign: i8, count: usize) {
    plan.narrow.extend((0..count).map(|_| NarrowLookup { kind, sign }));
}
