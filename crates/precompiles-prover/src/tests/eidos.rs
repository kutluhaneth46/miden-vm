//! Tests for the deferred transcript's native 32-row Eidos compression AIR.

use std::{fs, path::Path, string::String, vec, vec::Vec};

use miden_air::{
    BaseAir,
    logup::{BusId as MidenBusId, MIDEN_MAX_MESSAGE_WIDTH},
    lookup::{
        Challenges as MidenChallenges, build_lookup_fractions,
        debug::{ValidateLayout, ValidateLookupAir, check_trace_balance, trace::BalanceReport},
    },
    trace::eidos_compression::{
        self as mvm_eidos_compression, TraceMode as MvmTraceMode,
        generate_felt_trace_block as generate_mvm_block,
    },
};
use miden_core::{
    Felt,
    deferred::{DEFERRED_AND_INIT_CV, DEFERRED_CHUNKS_DOMAIN, DEFERRED_NODE_DOMAIN, Tag},
    field::{PrimeCharacteristicRing, QuadFelt},
    utils::RowMajorMatrix,
};
use miden_crypto::{hash::eidos::Eidos, stark::air::ConstraintDegrees};
use miden_lifted_air::LiftedAir;
use miden_precompiles::{CurvePrecompile, Keccak256Precompile};

use crate::{
    logup::{Challenges, LookupMessage, NUM_PUBLIC_VALUES, NUM_RANDOMNESS},
    relations::{BusId, MAX_MESSAGE_WIDTH, NUM_BUS_IDS},
    session::Session,
    transcript::eidos::{
        COL_ABSORPTION_ID, COL_CHAIN_CONTEXT_BEGIN, COL_CV_IN_BEGIN, COL_EIDOS_COMPRESSION_END,
        COL_IN_MULTIPLICITY, COL_IS_ABSORB, COL_IS_GENERIC, COL_IS_HEAD, COL_IS_OUTPUT,
        COL_IS_PAYLOAD, COL_OUT_MULTIPLICITY, COL_REMAINING, EIDOS_DOMAIN_NODE, EidosChainContext,
        EidosChainInputMsg, EidosCompressionAir, EidosCompressionInterfaceAir,
        EidosCompressionNarrowAir, EidosDigest, EidosOutMsg, INTERNAL_CV_BUS_ID, NUM_AUX_COLS,
        NUM_MAIN_COLS,
        compression::{
            layout::{
                BLOCK_PERIOD as EIDOS_COMPRESSION_CYCLE_LEN, F_COMPRESSION_CYCLE_ID_COL,
                F_CV_STORAGE_COLS, FOOTER_START, G_COMPRESSION_CYCLE_ID_COL,
                NUM_COLS as NUM_EIDOS_COMPRESSION_COLS, footer_digest_col, footer_r_col,
            },
            trace::{
                EidosCompressionFeltTraceBlock, generate_felt_trace_block_with_cycle_id,
                rewrite_felt_footer_for_test,
            },
        },
        trace::{EidosRequires, generate_traces},
    },
};

fn block(a: u32) -> ([Felt; 4], [Felt; 4]) {
    (
        core::array::from_fn(|i| Felt::from(a + i as u32)),
        core::array::from_fn(|i| Felt::from(a + 4 + i as u32)),
    )
}

#[test]
fn full_empty_session_bus_stack_balances() {
    let mut session = Session::new();
    let root = session.assert_and_fold(core::iter::empty());
    let traces = session.finish(root);
    let challenges = Challenges::new(
        QuadFelt::from_u64(101),
        QuadFelt::from_u64(103),
        MAX_MESSAGE_WIDTH,
        NUM_BUS_IDS,
    );
    let residual =
        crate::tests::bus_balance::session_stack_residual(&traces.mains(), &[], &challenges);
    assert!(residual.is_empty(), "{residual:#?}");
}

fn as_block((lo, hi): ([Felt; 4], [Felt; 4])) -> [Felt; 8] {
    let mut out = [Felt::ZERO; 8];
    out[..4].copy_from_slice(&lo);
    out[4..].copy_from_slice(&hi);
    out
}

fn unpack_felts<const N: usize>(values: &[Felt]) -> [u32; N] {
    let words: Vec<u32> = values
        .iter()
        .flat_map(|value| {
            let packed = value.as_canonical_u64();
            [packed as u32, (packed >> 32) as u32]
        })
        .collect();
    words.try_into().unwrap_or_else(|words: Vec<u32>| {
        panic!("expected {N} unpacked words, got {}", words.len())
    })
}

fn two_cycle_matrix(
    first: &EidosCompressionFeltTraceBlock,
    second: &EidosCompressionFeltTraceBlock,
) -> RowMajorMatrix<Felt> {
    let values = first
        .rows
        .iter()
        .chain(&second.rows)
        .flat_map(|row| row.iter().copied())
        .collect();
    RowMajorMatrix::new(values, NUM_EIDOS_COMPRESSION_COLS)
}

fn miden_lookup_challenges() -> MidenChallenges<QuadFelt> {
    MidenChallenges::new(
        QuadFelt::from_u64(101),
        QuadFelt::from_u64(103),
        MIDEN_MAX_MESSAGE_WIDTH,
        MidenBusId::COUNT,
    )
}

fn narrow_balance(
    trace: &RowMajorMatrix<Felt>,
    challenges: &MidenChallenges<QuadFelt>,
) -> BalanceReport {
    let air = EidosCompressionNarrowAir;
    check_trace_balance(&air, trace, &air.periodic_columns(), &[], &[], challenges)
}

fn parent_matrix_from_core(trace: &RowMajorMatrix<Felt>) -> RowMajorMatrix<Felt> {
    let mut values =
        Vec::with_capacity(trace.values.len() / NUM_EIDOS_COMPRESSION_COLS * NUM_MAIN_COLS);
    for row in trace.values.chunks_exact(NUM_EIDOS_COMPRESSION_COLS) {
        values.extend_from_slice(row);
        values.extend([Felt::ZERO; NUM_MAIN_COLS - NUM_EIDOS_COMPRESSION_COLS]);
    }
    RowMajorMatrix::new(values, NUM_MAIN_COLS)
}

fn interface_lookup_challenges() -> Challenges<QuadFelt> {
    Challenges::new(
        QuadFelt::from_u64(101),
        QuadFelt::from_u64(103),
        MAX_MESSAGE_WIDTH,
        NUM_BUS_IDS,
    )
}

fn interface_balance(trace: &RowMajorMatrix<Felt>) -> BalanceReport {
    let air = EidosCompressionInterfaceAir;
    check_trace_balance(
        &air,
        trace,
        &air.periodic_columns(),
        &[],
        &[],
        &interface_lookup_challenges(),
    )
}

fn net_multiplicity(report: &BalanceReport, denominator: QuadFelt) -> Felt {
    report
        .unmatched
        .iter()
        .find(|entry| entry.denom == denominator)
        .map_or(Felt::ZERO, |entry| entry.net_multiplicity)
}

#[test]
fn chain_contexts_match_vm_sources() {
    let len_bytes = 136u32;
    assert_eq!(EidosChainContext::chunk().as_array(), Tag::CHUNKS.as_word());
    assert_eq!(EidosChainContext::and().as_array(), Tag::AND.as_word());
    assert_eq!(
        EidosChainContext::keccak256_assertion(len_bytes).as_array(),
        Keccak256Precompile::assert_tag(len_bytes).as_word(),
    );
    assert_eq!(
        EidosChainContext::ec_msm_context().as_array(),
        [
            CurvePrecompile::id(),
            Felt::from_u32(CurvePrecompile::MSM_OP_ID as u32),
            Felt::ZERO,
            Felt::ZERO,
        ],
    );
}

#[test]
fn atomic_chain_input_messages_bind_domain_and_every_payload_field() {
    let challenges = Challenges::<QuadFelt>::new(
        QuadFelt::from_u64(7),
        QuadFelt::from_u64(5),
        MAX_MESSAGE_WIDTH,
        NUM_BUS_IDS,
    );
    let chain_step_id = Felt::from_u32(1);
    let message = core::array::from_fn(|idx| Felt::from_u32(10 + idx as u32));
    let chain_context = core::array::from_fn(|idx| Felt::from_u32(30 + idx as u32));
    let node = EidosChainInputMsg::node(chain_step_id, message, chain_context).encode(&challenges);

    let [m0, m1, m2, m3, m4, m5, m6, m7] = message;
    let [c0, c1, c2, c3] = chain_context;
    assert_eq!(
        node,
        challenges.encode(
            BusId::EidosIn as usize,
            [
                chain_step_id,
                Felt::from_u8(EIDOS_DOMAIN_NODE),
                m0,
                m1,
                m2,
                m3,
                m4,
                m5,
                m6,
                m7,
                c0,
                c1,
                c2,
                c3,
            ],
        ),
        "atomic chain input field order drifted",
    );

    assert_ne!(
        node,
        EidosChainInputMsg::and(chain_step_id, message, chain_context).encode(&challenges),
    );
    assert_ne!(
        node,
        EidosChainInputMsg::chunks(chain_step_id, message, chain_context).encode(&challenges),
    );

    for field in 0..8 {
        let mut mutated = message;
        mutated[field] += Felt::ONE;
        assert_ne!(
            node,
            EidosChainInputMsg::node(chain_step_id, mutated, chain_context).encode(&challenges),
            "message field {field} was not bound",
        );
    }
    for field in 0..4 {
        let mut mutated = chain_context;
        mutated[field] += Felt::ONE;
        assert_ne!(
            node,
            EidosChainInputMsg::node(chain_step_id, message, mutated).encode(&challenges),
            "chain-context field {field} was not bound",
        );
    }
    assert_ne!(node, EidosOutMsg { chain_step_id, digest: chain_context }.encode(&challenges),);
}

#[test]
fn air_layout_matches_32_row_eidos_compression_spec() {
    assert_eq!(EIDOS_COMPRESSION_CYCLE_LEN, 32);
    assert_eq!(COL_EIDOS_COMPRESSION_END, 108);
    assert_eq!(COL_IS_HEAD, 111);
    assert_eq!(COL_IS_ABSORB, 112);
    assert_eq!(COL_CHAIN_CONTEXT_BEGIN, 120);
    assert_eq!(COL_CV_IN_BEGIN, 124);
    assert_eq!(NUM_MAIN_COLS, 128);
    assert_eq!(NUM_AUX_COLS, 20);

    let layout =
        <EidosCompressionAir as LiftedAir<Felt, QuadFelt>>::air_layout(&EidosCompressionAir);
    assert_eq!(layout.preprocessed_width, 0);
    assert_eq!(layout.main_width, NUM_MAIN_COLS);
    assert_eq!(layout.num_public_values, NUM_PUBLIC_VALUES);
    assert_eq!(layout.permutation_width, NUM_AUX_COLS);
    assert_eq!(layout.num_permutation_challenges, NUM_RANDOMNESS);
    assert_eq!(layout.num_permutation_values, 2);
    assert_eq!(layout.num_periodic_columns, 14);
    assert_eq!(
        <EidosCompressionAir as BaseAir<Felt>>::periodic_columns(&EidosCompressionAir)
            .iter()
            .map(Vec::len)
            .collect::<Vec<_>>(),
        vec![EIDOS_COMPRESSION_CYCLE_LEN; 14],
    );
}

#[test]
fn constraint_degree_remains_three() {
    let degree = ConstraintDegrees::from_air::<Felt, QuadFelt, _>(&EidosCompressionAir);
    assert_eq!(degree, ConstraintDegrees { base: 3, ext: 3 });
    assert_eq!(crate::tests::log_quotient_degree(&EidosCompressionAir), 1);
}

#[test]
fn lookup_degree_annotations_match_the_two_family_layout() {
    let common = |trace_width, permutation_width| ValidateLayout {
        preprocessed_width: 0,
        trace_width,
        num_public_values: NUM_PUBLIC_VALUES,
        num_periodic_columns: 14,
        permutation_width,
        num_permutation_challenges: NUM_RANDOMNESS,
        num_permutation_values: 1,
    };

    EidosCompressionNarrowAir
        .validate(common(NUM_EIDOS_COMPRESSION_COLS, 18))
        .unwrap_or_else(|error| {
            panic!("PVM Eidos compression core lookup validation failed: {error}")
        });
    EidosCompressionInterfaceAir
        .validate(common(NUM_MAIN_COLS, 2))
        .unwrap_or_else(|error| {
            panic!("PVM EidosCompression interface lookup validation failed: {error}")
        });
}

#[test]
fn lookup_interaction_liveness_matches_the_18_plus_2_design() {
    let mut requires = EidosRequires::new();
    let output = requires.require_absorption(EidosChainContext::and(), [block(10)]);
    requires.require_digest(output.digest);
    let compression = generate_traces(requires).compression;
    let core = crate::composite::extract_band(&compression, 0..NUM_EIDOS_COMPRESSION_COLS);

    let narrow = build_lookup_fractions(
        &EidosCompressionNarrowAir,
        &core,
        None,
        &EidosCompressionNarrowAir.periodic_columns(),
        &miden_lookup_challenges(),
    );
    assert_eq!(narrow.shape(), &[2; 18]);
    for row in 0..EIDOS_COMPRESSION_CYCLE_LEN {
        let actual = &narrow.counts()[row * 18..(row + 1) * 18];
        if row < FOOTER_START {
            assert_eq!(actual, &[2; 18], "fused row {row}");
        } else {
            let mut expected = [0; 18];
            expected[..9].fill(2);
            expected[11..13].fill(2);
            expected[13] = 1;
            expected[14] = 2;
            expected[16..18].fill(2);
            assert_eq!(actual, &expected, "footer row {row}");
            assert_eq!(actual.iter().sum::<usize>(), 29);
        }
    }

    let interface = build_lookup_fractions(
        &EidosCompressionInterfaceAir,
        &compression,
        None,
        &EidosCompressionInterfaceAir.periodic_columns(),
        &interface_lookup_challenges(),
    );
    assert_eq!(interface.shape(), &[1, 2]);
    for row in 0..EIDOS_COMPRESSION_CYCLE_LEN {
        let actual = &interface.counts()[row * 2..(row + 1) * 2];
        let expected = match row {
            0 => [0, 1],
            31 => [1, 2],
            _ => [0, 0],
        };
        assert_eq!(actual, expected, "interface row {row}");
    }
}

#[test]
fn digests_match_eidos_framing_and_integrated_eidos_compression_air_holds() {
    let and_block = block(10);
    let chunk_blocks = [block(20), block(30), block(40)];
    let generic_blocks = [block(50), block(60)];
    let generic_context = EidosChainContext::keccak256_assertion(17);

    let mut requires = EidosRequires::new();
    let and = requires.require_absorption(EidosChainContext::and(), [and_block]);
    let chunks = requires.require_absorption(EidosChainContext::chunk(), chunk_blocks);
    let generic = requires.require_absorption(generic_context, generic_blocks);
    for digest in [and.digest, chunks.digest, generic.digest] {
        requires.require_digest(digest).expect("recorded digest");
    }

    let expected_and = Eidos::compress(DEFERRED_AND_INIT_CV, as_block(and_block));
    assert_eq!(and.digest, EidosDigest(expected_and.into_elements()));

    let mut expected_chunks =
        Eidos::init_chaining_word(DEFERRED_CHUNKS_DOMAIN.as_canonical_u64() as u32, 24);
    for input in chunk_blocks {
        expected_chunks = Eidos::compress(expected_chunks, as_block(input));
    }
    assert_eq!(chunks.digest, EidosDigest(expected_chunks.into_elements()));

    let mut expected_generic =
        Eidos::init_chaining_word(DEFERRED_NODE_DOMAIN.as_canonical_u64() as u32, 20);
    for input in generic_blocks {
        expected_generic = Eidos::compress(expected_generic, as_block(input));
    }
    let mut final_block = [Felt::ZERO; 8];
    final_block[..4].copy_from_slice(&generic_context.as_array());
    expected_generic = Eidos::compress(expected_generic, final_block);
    assert_eq!(generic.digest, EidosDigest(expected_generic.into_elements()));

    let traces = generate_traces(requires);
    crate::tests::check_local(EidosCompressionAir, &traces.compression);

    // Seven real compressions occupy seven full 32-row cycles, padded to eight cycles.
    assert_eq!(traces.compression.values.len() / NUM_MAIN_COLS, 8 * 32);
    let row = |cycle: usize, c: usize| {
        traces.compression.values[cycle * EIDOS_COMPRESSION_CYCLE_LEN * NUM_MAIN_COLS + c]
    };
    assert_eq!(row(0, COL_IS_HEAD), Felt::ONE);
    assert_eq!(row(1, COL_REMAINING), Felt::from_u32(3));
    assert_eq!(row(4, COL_IS_GENERIC), Felt::ONE);
    assert_eq!(row(6, COL_IS_PAYLOAD), Felt::ZERO);
    assert_eq!(row(6, COL_IS_OUTPUT), Felt::ONE);

    // The PVM output relation reads the digest directly from the native Eidos compression footer.
    // There is no bridge trace between the compression witness and the value seen by transcript
    // consumers.
    let footer_digest = |cycle: usize| {
        let footer = cycle * EIDOS_COMPRESSION_CYCLE_LEN + EIDOS_COMPRESSION_CYCLE_LEN - 1;
        core::array::from_fn(|i| {
            traces.compression.values[footer * NUM_MAIN_COLS + footer_digest_col(i)]
        })
    };
    assert_eq!(footer_digest(0), and.digest.as_array());
    assert_eq!(footer_digest(3), chunks.digest.as_array());
    assert_eq!(footer_digest(6), generic.digest.as_array());

    for cycle in 0..7 {
        let first = cycle * EIDOS_COMPRESSION_CYCLE_LEN * NUM_MAIN_COLS;
        for row in 1..EIDOS_COMPRESSION_CYCLE_LEN {
            let current = first + row * NUM_MAIN_COLS;
            assert_eq!(
                &traces.compression.values[current + COL_ABSORPTION_ID..current + NUM_MAIN_COLS],
                &traces.compression.values[first + COL_ABSORPTION_ID..first + NUM_MAIN_COLS],
                "PVM metadata changed within physical Eidos compression cycle {cycle} at row {row}",
            );
        }
    }
}

#[test]
fn identical_eidos_compression_states_remain_distinct_ordered_pvm_cycles() {
    let payload = block(70);
    let mut requires = EidosRequires::new();
    let first = requires.require_absorption(EidosChainContext::keccak256_assertion(8), [payload]);
    let second = requires.require_absorption(EidosChainContext::keccak256_assertion(9), [payload]);
    assert_ne!(first.digest, second.digest);
    assert_eq!(requires.total_cycles(), 2);

    let compression = generate_traces(requires).compression;
    let row = |cycle: usize, col: usize| {
        compression.values[cycle * EIDOS_COMPRESSION_CYCLE_LEN * NUM_MAIN_COLS + col]
    };

    // Both generic absorptions start from the same Eidos init CV and payload block, so their first
    // Eidos compression states are identical. They must nevertheless remain two physical cycles
    // because the external absorption IDs and distinct tag-finalization cycles are ordered
    // protocol data.
    let second_start = 2 * EIDOS_COMPRESSION_CYCLE_LEN * NUM_MAIN_COLS;
    for col in 0..NUM_EIDOS_COMPRESSION_COLS {
        if col != G_COMPRESSION_CYCLE_ID_COL {
            assert_eq!(compression.values[col], compression.values[second_start + col]);
        }
    }
    assert_eq!(row(0, COL_ABSORPTION_ID), Felt::ZERO);
    assert_eq!(row(1, COL_ABSORPTION_ID), Felt::ZERO);
    assert_eq!(row(2, COL_ABSORPTION_ID), Felt::ONE);
    assert_eq!(row(3, COL_ABSORPTION_ID), Felt::ONE);
    crate::tests::check_local(EidosCompressionAir, &compression);
}

#[test]
fn physical_cycle_id_rejects_two_cycle_cv_swap() {
    let block_a = core::array::from_fn(|i| 10 + i as u32);
    let block_b = core::array::from_fn(|i| 100 + i as u32);
    let cv_a = core::array::from_fn(|i| 1_000 + i as u32);
    let cv_b = core::array::from_fn(|i| 2_000 + i as u32);

    // Each computation consumes the other cycle's CV while its footer advertises the CV assigned
    // to this physical cycle. The physical cycle ID must prevent that cross-cycle substitution.
    let mut forged_a = generate_felt_trace_block_with_cycle_id(block_a, cv_b, 0);
    let mut forged_b = generate_felt_trace_block_with_cycle_id(block_b, cv_a, 1);
    rewrite_felt_footer_for_test(&mut forged_a.rows, block_a, cv_a, forged_a.final_v, 0);
    rewrite_felt_footer_for_test(&mut forged_b.rows, block_b, cv_b, forged_b.final_v, 1);

    let forged_core = two_cycle_matrix(&forged_a, &forged_b);
    // Every core polynomial constraint still holds. Rejection comes specifically from the
    // cycle-tagged atomic CV bridge in the PVM interface lookup family.
    crate::tests::check_local(EidosCompressionNarrowAir, &forged_core);
    let forged = parent_matrix_from_core(&forged_core);
    let challenges = interface_lookup_challenges();
    let report = interface_balance(&forged);
    assert!(report.mutex_violations.is_empty());
    assert_eq!(report.unmatched.len(), 4);
    for (cycle_id, consumed, advertised) in [(0u64, cv_b, cv_a), (1, cv_a, cv_b)] {
        let encode = |cv: [u32; 8]| {
            let fields: [Felt; 9] = core::array::from_fn(|idx| {
                if idx == 0 {
                    Felt::new_unchecked(cycle_id)
                } else {
                    Felt::from(cv[idx - 1])
                }
            });
            challenges.encode(INTERNAL_CV_BUS_ID, fields)
        };
        assert_eq!(net_multiplicity(&report, encode(consumed)), -Felt::ONE);
        assert_eq!(net_multiplicity(&report, encode(advertised)), Felt::ONE);
    }
}

#[test]
fn physical_cycle_id_rejects_two_cycle_message_swap() {
    let block_a = core::array::from_fn(|i| 10 + i as u32);
    let block_b = core::array::from_fn(|i| 100 + i as u32);
    let cv_a = core::array::from_fn(|i| 1_000 + i as u32);
    let cv_b = core::array::from_fn(|i| 2_000 + i as u32);

    // Each computation consumes the other cycle's block. Replace only its footer's advertised
    // block, leaving the computed Eidos compression output intact.
    let mut forged_a = generate_felt_trace_block_with_cycle_id(block_b, cv_a, 0);
    let mut forged_b = generate_felt_trace_block_with_cycle_id(block_a, cv_b, 1);
    rewrite_felt_footer_for_test(&mut forged_a.rows, block_a, cv_a, forged_a.final_v, 0);
    rewrite_felt_footer_for_test(&mut forged_b.rows, block_b, cv_b, forged_b.final_v, 1);

    let forged = two_cycle_matrix(&forged_a, &forged_b);
    crate::tests::check_local(EidosCompressionNarrowAir, &forged);
    let challenges = miden_lookup_challenges();
    let report = narrow_balance(&forged, &challenges);
    let seven = Felt::from_u8(7);
    for (cycle_id, consumed, advertised) in [(0u64, block_b, block_a), (1, block_a, block_b)] {
        for word_index in 0..16 {
            let encode = |block: [u32; 16]| {
                challenges.encode(
                    MidenBusId::EidosCompressionMessageWord as usize,
                    [
                        Felt::from_usize(word_index),
                        Felt::from(block[word_index]),
                        Felt::new_unchecked(cycle_id),
                    ],
                )
            };
            assert_eq!(net_multiplicity(&report, encode(consumed)), seven);
            assert_eq!(net_multiplicity(&report, encode(advertised)), -seven);
        }
    }
}

#[test]
#[should_panic(expected = "constraint not satisfied")]
fn physical_cycle_id_is_pinned_to_zero() {
    let block = core::array::from_fn(|i| 10 + i as u32);
    let cv = core::array::from_fn(|i| 1_000 + i as u32);
    let first = generate_felt_trace_block_with_cycle_id(block, cv, 1);
    let second = generate_felt_trace_block_with_cycle_id(block, cv, 2);

    crate::tests::check_local(EidosCompressionNarrowAir, &two_cycle_matrix(&first, &second));
}

#[test]
#[should_panic(expected = "constraint not satisfied")]
fn physical_cycle_id_is_constant_across_fused_rows() {
    let block = core::array::from_fn(|i| 10 + i as u32);
    let cv = core::array::from_fn(|i| 1_000 + i as u32);
    let mut first = generate_felt_trace_block_with_cycle_id(block, cv, 0);
    let second = generate_felt_trace_block_with_cycle_id(block, cv, 1);
    first.rows[1][G_COMPRESSION_CYCLE_ID_COL] = Felt::ONE;

    crate::tests::check_local(EidosCompressionNarrowAir, &two_cycle_matrix(&first, &second));
}

#[test]
#[should_panic(expected = "constraint not satisfied")]
fn physical_cycle_id_bridges_fused_rows_to_footer() {
    let block = core::array::from_fn(|i| 10 + i as u32);
    let cv = core::array::from_fn(|i| 1_000 + i as u32);
    let mut first = generate_felt_trace_block_with_cycle_id(block, cv, 0);
    let second = generate_felt_trace_block_with_cycle_id(block, cv, 2);
    rewrite_felt_footer_for_test(&mut first.rows, block, cv, first.final_v, 1);

    crate::tests::check_local(EidosCompressionNarrowAir, &two_cycle_matrix(&first, &second));
}

#[test]
#[should_panic(expected = "constraint not satisfied")]
fn physical_cycle_id_increments_between_cycles() {
    let block = core::array::from_fn(|i| 10 + i as u32);
    let cv = core::array::from_fn(|i| 1_000 + i as u32);
    let first = generate_felt_trace_block_with_cycle_id(block, cv, 0);
    let second = generate_felt_trace_block_with_cycle_id(block, cv, 2);

    crate::tests::check_local(EidosCompressionNarrowAir, &two_cycle_matrix(&first, &second));
}

#[test]
#[should_panic(expected = "packed Eidos compression input must be a canonical field element")]
fn pvm_trace_writer_rejects_noncanonical_packed_input() {
    let mut block = [0; 16];
    block[0] = 1;
    block[1] = u32::MAX;
    let _ = generate_felt_trace_block_with_cycle_id(block, [0; 8], 0);
}

#[test]
fn mvm_and_pvm_writers_agree_on_shared_eidos_compression_witness() {
    assert_eq!(NUM_EIDOS_COMPRESSION_COLS, 108);
    assert_eq!(mvm_eidos_compression::NUM_EIDOS_COMPRESSION_COLS, 108);

    for case in 0..16_u32 {
        let block = core::array::from_fn(|i| {
            0x1020_3040_u32
                .wrapping_add(0x0102_0304_u32.wrapping_mul(i as u32))
                .rotate_left(case)
        });
        let cv = core::array::from_fn(|i| {
            0x5060_7080_u32
                .wrapping_add(0x0001_0203_u32.wrapping_mul(i as u32))
                .rotate_right(case)
        });
        let pvm = generate_felt_trace_block_with_cycle_id(block, cv, 0);
        let mvm = generate_mvm_block(block, cv, MvmTraceMode::Compression);

        assert_eq!(pvm.final_v, mvm.final_v, "final working state differs in case {case}");
        for row in 0..EIDOS_COMPRESSION_CYCLE_LEN {
            for col in 0..NUM_EIDOS_COMPRESSION_COLS {
                // The MVM-only compression-link multiplicity occupies an otherwise unused PVM
                // footer cell. It is outside the shared Eidos compression witness contract.
                if row >= FOOTER_START
                    && (col == mvm_eidos_compression::F_COMPRESSION_MULTIPLICITY_COL
                        || F_CV_STORAGE_COLS.contains(&col))
                {
                    continue;
                }
                assert_eq!(
                    pvm.rows[row][col], mvm.rows[row][col],
                    "MVM/PVM witness mismatch in case {case}, row {row}, column {col}",
                );
            }
        }
    }
}

fn contains_rust_identifier(source: &str, identifier: &str) -> bool {
    let is_identifier_byte = |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_';

    source.match_indices(identifier).any(|(start, _)| {
        let before = source.as_bytes().get(start.wrapping_sub(1)).copied();
        let after = source.as_bytes().get(start + identifier.len()).copied();
        before.is_none_or(|byte| !is_identifier_byte(byte))
            && after.is_none_or(|byte| !is_identifier_byte(byte))
    })
}

fn forbidden_mvm_eidos_compression_reference(source: &str) -> Option<&'static str> {
    for statement in source.split(';') {
        if !contains_rust_identifier(statement, "use")
            || !contains_rust_identifier(statement, "miden_air")
        {
            continue;
        }

        for forbidden in [
            "eidos_compression",
            "EidosCompressionCols",
            "NUM_EIDOS_COMPRESSION_COLS",
            "generate_felt_trace_block",
        ] {
            if contains_rust_identifier(statement, forbidden) {
                return Some(forbidden);
            }
        }
    }

    let compact: String = source.chars().filter(|ch| !ch.is_ascii_whitespace()).collect();
    [
        "miden_air::trace::eidos_compression::",
        "miden_air::constraints::eidos_compression::",
        "miden_air::eidos_compression::",
    ]
    .into_iter()
    .find(|forbidden| compact.contains(forbidden))
}

#[test]
fn production_pvm_sources_do_not_import_mvm_eidos_compression_implementation() {
    fn visit_rust_sources(path: &Path, files: &mut Vec<std::path::PathBuf>) {
        for entry in fs::read_dir(path).expect("read PVM Eidos source directory") {
            let path = entry.expect("read PVM Eidos source entry").path();
            if path.is_dir() {
                if path.file_name().is_some_and(|name| name == "tests") {
                    continue;
                }
                visit_rust_sources(&path, files);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                files.push(path);
            }
        }
    }

    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    visit_rust_sources(&root, &mut files);
    assert!(!files.is_empty(), "PVM Eidos source inventory must not be empty");

    for path in files {
        let source = fs::read_to_string(&path).expect("read PVM Eidos source");
        if let Some(forbidden) = forbidden_mvm_eidos_compression_reference(&source) {
            panic!(
                "{} imports the MVM Eidos compression implementation through `{forbidden}`",
                path.display(),
            );
        }
    }
}

#[test]
fn mvm_eidos_compression_import_guard_rejects_alternate_path_spellings() {
    for source in [
        "use miden_air::eidos_compression::write_felt_trace_block;",
        "use miden_air::trace::{eidos_compression::write_felt_trace_block};",
        "use miden_air::{trace::{eidos_compression::write_felt_trace_block}};",
        "use ::miden_air::{trace::{eidos_compression::write_felt_trace_block}};",
        "fn write() { miden_air::trace::eidos_compression::write_felt_trace_block(); }",
        "fn write() { miden_air :: constraints :: eidos_compression :: write(); }",
        "use miden_air::EidosCompressionCols;",
    ] {
        assert!(
            forbidden_mvm_eidos_compression_reference(source).is_some(),
            "guard accepted `{source}`",
        );
    }

    for source in [
        "use miden_air::BaseAir;",
        "use miden_air::logup::{BusId, eidos_compression_rot7_bus};",
        "use crate::transcript::eidos::compression::trace::write_felt_trace_block;",
    ] {
        assert!(
            forbidden_mvm_eidos_compression_reference(source).is_none(),
            "guard rejected `{source}`",
        );
    }
}

#[test]
fn interning_reuses_logical_span_and_tallies_multiplicity() {
    let mut requires = EidosRequires::new();
    let first = requires.require_absorption(EidosChainContext::chunk(), vec![block(7), block(17)]);
    let second = requires.require_absorption(EidosChainContext::chunk(), vec![block(7), block(17)]);
    assert_eq!(first.digest, second.digest);
    assert_eq!(first.head(), second.head());
    assert_eq!(first.tail(), second.tail());
    assert_eq!(requires.total_cycles(), 2);
}

#[test]
#[should_panic(expected = "constraint not satisfied")]
fn padding_cycle_cannot_emit_unproved_payload() {
    let mut requires = EidosRequires::new();
    let and = requires.require_absorption(EidosChainContext::and(), [block(1)]);
    let generic =
        requires.require_absorption(EidosChainContext::keccak256_assertion(8), [block(10)]);
    requires.require_digest(and.digest);
    requires.require_digest(generic.digest);
    let mut compression = generate_traces(requires).compression;
    // Three real cycles round to four. A padding cycle cannot impersonate a payload cycle.
    let padding_row = 3 * EIDOS_COMPRESSION_CYCLE_LEN;
    compression.values[padding_row * NUM_MAIN_COLS + COL_IS_PAYLOAD] = Felt::ONE;
    crate::tests::check_local(EidosCompressionAir, &compression);
}

#[test]
#[should_panic(expected = "constraint not satisfied")]
fn input_multiplicity_is_zero_off_payload_cycles() {
    let mut requires = EidosRequires::new();
    let generic =
        requires.require_absorption(EidosChainContext::keccak256_assertion(8), [block(10)]);
    requires.require_digest(generic.digest);
    let mut compression = generate_traces(requires).compression;

    // Cycle 1 is the generic tag-finalization compression: active and output, but not payload.
    for row in EIDOS_COMPRESSION_CYCLE_LEN..2 * EIDOS_COMPRESSION_CYCLE_LEN {
        compression.values[row * NUM_MAIN_COLS + COL_IN_MULTIPLICITY] = Felt::ONE;
    }
    crate::tests::check_local(EidosCompressionAir, &compression);
}

#[test]
#[should_panic(expected = "constraint not satisfied")]
fn output_multiplicity_is_zero_off_output_cycles() {
    let mut requires = EidosRequires::new();
    let chunks = requires.require_absorption(EidosChainContext::chunk(), [block(1), block(11)]);
    requires.require_digest(chunks.digest);
    let mut compression = generate_traces(requires).compression;

    // Cycle 0 is a payload chain head but not the terminal output cycle.
    for row in 0..EIDOS_COMPRESSION_CYCLE_LEN {
        compression.values[row * NUM_MAIN_COLS + COL_OUT_MULTIPLICITY] = Felt::ONE;
    }
    crate::tests::check_local(EidosCompressionAir, &compression);
}

#[test]
#[should_panic(expected = "constraint not satisfied")]
fn continuation_payload_id_must_follow_the_chain() {
    let mut requires = EidosRequires::new();
    let chunks = requires.require_absorption(EidosChainContext::chunk(), [block(1), block(11)]);
    requires.require_digest(chunks.digest);
    let mut compression = generate_traces(requires).compression;
    for row in EIDOS_COMPRESSION_CYCLE_LEN..2 * EIDOS_COMPRESSION_CYCLE_LEN {
        compression.values[row * NUM_MAIN_COLS + COL_ABSORPTION_ID] += Felt::ONE;
    }
    crate::tests::check_local(EidosCompressionAir, &compression);
}

#[test]
#[should_panic(expected = "constraint not satisfied")]
fn native_eidos_compression_core_witness_is_not_a_free_bridge_input() {
    let mut requires = EidosRequires::new();
    let output = requires.require_absorption(EidosChainContext::and(), [block(1)]);
    requires.require_digest(output.digest);
    let mut compression = generate_traces(requires).compression;

    let row = FOOTER_START + 1;
    compression.values[row * NUM_MAIN_COLS + footer_r_col(1, 0)] += Felt::ONE;
    crate::tests::check_local(EidosCompressionAir, &compression);
}

#[test]
#[should_panic(expected = "constraint not satisfied")]
fn physical_eidos_compression_cycles_must_carry_the_previous_chaining_word() {
    let second_block = block(11);
    let mut requires = EidosRequires::new();
    let output = requires.require_absorption(EidosChainContext::chunk(), [block(1), second_block]);
    requires.require_digest(output.digest);
    let mut compression = generate_traces(requires).compression;

    // Replace the second compression with a separately valid native Eidos compression cycle using a
    // forged input CV, and keep its cycle-constant PVM metadata self-consistent. The only
    // broken fact is the physical carry from cycle 0's Eidos compression output into cycle 1's
    // Eidos compression input.
    let mut forged_cv: [Felt; 4] = core::array::from_fn(|i| {
        compression.values[EIDOS_COMPRESSION_CYCLE_LEN * NUM_MAIN_COLS + COL_CV_IN_BEGIN + i]
    });
    forged_cv[0] += Felt::ONE;
    let (block_lo, block_hi) = second_block;
    let mut state = [Felt::ZERO; 12];
    state[..4].copy_from_slice(&block_lo);
    state[4..8].copy_from_slice(&block_hi);
    state[8..].copy_from_slice(&forged_cv);
    let forged = generate_felt_trace_block_with_cycle_id(
        unpack_felts::<16>(&state[..8]),
        unpack_felts::<8>(&forged_cv),
        1,
    );

    for row in 0..EIDOS_COMPRESSION_CYCLE_LEN {
        let dst = (EIDOS_COMPRESSION_CYCLE_LEN + row) * NUM_MAIN_COLS;
        compression.values[dst..dst + NUM_EIDOS_COMPRESSION_COLS]
            .copy_from_slice(&forged.rows[row]);
        compression.values[dst + COL_CV_IN_BEGIN..dst + COL_CV_IN_BEGIN + 4]
            .copy_from_slice(&forged_cv);
    }

    crate::tests::check_local(EidosCompressionAir, &compression);
}
