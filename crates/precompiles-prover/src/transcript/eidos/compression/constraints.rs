//! AIR constraints for the 32-row Eidos compression trace.

use miden_core::{Felt, field::PrimeCharacteristicRing};
use miden_crypto::stark::air::{AirBuilder, LiftedAirBuilder};

use super::{
    algebra::{pack_u32_le, sum_input_b, universal_cv_word, xor_from_and},
    layout::*,
    schedule::{EIDOS_COMPRESSION_IV, G_IDX_COL, G_IDX_DIAG, LaneMap},
    selectors::EidosCompressionSelectors,
};

/// Enforces all constraints which are active on the 28 fused Eidos compression rows of each cycle.
pub(crate) fn enforce_fused_rows<AB>(
    builder: &mut AB,
    local: &[AB::Var],
    next: &[AB::Var],
    selectors: &EidosCompressionSelectors<AB::Expr>,
) where
    AB: LiftedAirBuilder<F = Felt>,
{
    // The trace begins at a physical compression boundary. Together with the cycle-to-cycle
    // increment below, this makes every 32-row compression identifier unique and canonical.
    builder.when_first_row().assert_zero(fused_compression_cycle_id::<AB>(local));

    enforce_fused_row_locals(builder, local, selectors);
    enforce_initial_iv(builder, local, selectors);
    enforce_fused_row_transitions(builder, local, next, selectors);
}

/// Enforces the fused-to-footer bridge and all four footer rows of each cycle.
pub(crate) fn enforce_footer_rows<AB>(
    builder: &mut AB,
    local: &[AB::Var],
    next: &[AB::Var],
    selectors: &EidosCompressionSelectors<AB::Expr>,
) where
    AB: LiftedAirBuilder<F = Felt>,
{
    enforce_last_fused_to_f0(builder, local, next, selectors);
    enforce_footer_locals(builder, local, selectors);
    enforce_footer_transitions(builder, local, next, selectors);
}

fn enforce_fused_row_locals<AB>(
    builder: &mut AB,
    local: &[AB::Var],
    selectors: &EidosCompressionSelectors<AB::Expr>,
) where
    AB: LiftedAirBuilder<F = Felt>,
{
    let is_fused = selectors.is_ab() + selectors.is_cd();

    for g in 0..NUM_G {
        let k3 = c::<AB>(local, g_k3_col(g));
        let k2 = c::<AB>(local, G_K2_BASE_COL + g);
        builder.assert_zero(k3.clone() * (k3.clone() - AB::Expr::ONE) * (k3 - expr::<AB>(2)));
        builder.when(is_fused.clone()).assert_zero(k2.clone() * (AB::Expr::ONE - k2));
    }
}

fn enforce_initial_iv<AB>(
    builder: &mut AB,
    local: &[AB::Var],
    selectors: &EidosCompressionSelectors<AB::Expr>,
) where
    AB: LiftedAirBuilder<F = Felt>,
{
    let is_first = selectors.is_first_fused();

    for g in 0..NUM_G {
        let builder = &mut builder.when(is_first.clone());
        builder.assert_zero(
            input_c_for_rotation::<AB>(local, g, 16) - expr::<AB>(EIDOS_COMPRESSION_IV[g] as u64),
        );
        builder
            .assert_zero(input_d::<AB>(local, g) - expr::<AB>(EIDOS_COMPRESSION_IV[4 + g] as u64));
    }
}

fn enforce_fused_row_transitions<AB>(
    builder: &mut AB,
    local: &[AB::Var],
    next: &[AB::Var],
    selectors: &EidosCompressionSelectors<AB::Expr>,
) where
    AB: LiftedAirBuilder<F = Felt>,
{
    let is_col = AB::Expr::ONE - selectors.is_diag();
    let is_diag = selectors.is_diag();
    let is_inner_fused_transition =
        selectors.is_ab() + selectors.is_cd() - selectors.is_last_fused();

    builder
        .when_transition()
        .when(is_inner_fused_transition)
        .assert_eq(fused_compression_cycle_id::<AB>(next), fused_compression_cycle_id::<AB>(local));

    // The transition relation uses the row family's fixed first rotation. Selecting between
    // rotations inside the payload would raise the gated transition degree above 3.
    enforce_transition_for_maps::<AB>(
        builder,
        selectors.is_ab() * is_col.clone(),
        local,
        next,
        &G_IDX_COL,
        &G_IDX_COL,
        16,
        8,
    );
    enforce_transition_for_maps::<AB>(
        builder,
        selectors.is_cd() * is_col,
        local,
        next,
        &G_IDX_COL,
        &G_IDX_DIAG,
        8,
        16,
    );
    enforce_transition_for_maps::<AB>(
        builder,
        selectors.is_ab() * is_diag.clone(),
        local,
        next,
        &G_IDX_DIAG,
        &G_IDX_DIAG,
        16,
        8,
    );
    enforce_transition_for_maps::<AB>(
        builder,
        selectors.is_cd() * is_diag - selectors.is_last_fused(),
        local,
        next,
        &G_IDX_DIAG,
        &G_IDX_COL,
        8,
        16,
    );
}

fn enforce_transition_for_maps<AB>(
    builder: &mut AB,
    gate: AB::Expr,
    local: &[AB::Var],
    next: &[AB::Var],
    local_map: &LaneMap,
    next_map: &LaneMap,
    d_rotation: u32,
    next_d_rotation: u32,
) where
    AB: LiftedAirBuilder<F = Felt>,
{
    for word_idx in 0..16 {
        let (g, position) = lane_position(local_map, word_idx);
        // The missing tuple's lookup and the total-B relation below imply this transition once
        // the other three B transitions hold.
        if g == MISSING_ROTATION_G && position == 1 {
            continue;
        }
        let lhs = transition_output_word::<AB>(local, local_map, word_idx, d_rotation);
        let rhs = input_word::<AB>(next, next_map, word_idx, next_d_rotation);
        builder.when(gate.clone()).assert_zero(lhs - rhs);
    }
}

fn enforce_last_fused_to_f0<AB>(
    builder: &mut AB,
    local: &[AB::Var],
    next: &[AB::Var],
    selectors: &EidosCompressionSelectors<AB::Expr>,
) where
    AB: LiftedAirBuilder<F = Felt>,
{
    let gate = selectors.is_last_fused();
    let final_w = |idx| output_word::<AB>(local, &G_IDX_DIAG, idx, selectors);
    let f0_words = footer_words::<AB>(next);

    builder.when(gate.clone()).assert_zero(f0_words.v_low_even - final_w(0));
    builder.when(gate.clone()).assert_zero(f0_words.v_low_odd - final_w(1));
    builder.when(gate.clone()).assert_zero(f0_words.v_high_even - final_w(8));
    builder.when(gate.clone()).assert_zero(f0_words.v_high_odd - final_w(9));
    builder.when(gate.clone()).assert_eq(
        c::<AB>(next, F_COMPRESSION_CYCLE_ID_COL),
        fused_compression_cycle_id::<AB>(local),
    );

    for (idx, word_idx) in F_FUTURE_W_WORD_INDICES.into_iter().enumerate() {
        // The affected B word is carried by the total relation instead of a direct bridge.
        if word_idx == G_IDX_DIAG[MISSING_ROTATION_G][1] {
            continue;
        }
        builder
            .when(gate.clone())
            .assert_zero(c::<AB>(next, footer_future_w_col(0, idx)) - final_w(word_idx));
    }

    let footer_b_sum = [4usize, 5, 6, 7].into_iter().fold(AB::Expr::ZERO, |sum, word_idx| {
        let idx = F_FUTURE_W_WORD_INDICES
            .iter()
            .position(|&candidate| candidate == word_idx)
            .expect("all final B words are carried by footer 0");
        sum + c::<AB>(next, footer_future_w_col(0, idx))
    });
    builder
        .when(gate)
        .assert_zero(sum_input_b(|col| c::<AB>(next, col)) - footer_b_sum);
}

fn enforce_footer_locals<AB>(
    builder: &mut AB,
    local: &[AB::Var],
    selectors: &EidosCompressionSelectors<AB::Expr>,
) where
    AB: LiftedAirBuilder<F = Felt>,
{
    let is_footer = selectors.is_footer();
    let words = footer_words::<AB>(local);

    builder
        .when(is_footer.clone())
        .assert_zero(words.high_even_duplicate.clone() - words.v_high_even.clone());
    builder
        .when(is_footer.clone())
        .assert_zero(words.high_odd_duplicate.clone() - words.v_high_odd.clone());
    builder
        .when(is_footer.clone())
        .assert_zero(c::<AB>(local, F_TOP_BIT_SLOT_BASE_COL) - words.out_odd_byte3.clone());
    builder.when(is_footer.clone()).assert_zero(
        c::<AB>(local, F_TOP_BIT_SLOT_BASE_COL + 1) - expr::<AB>(F_TOP_BIT_MASK as u64),
    );

    let top_bit = c::<AB>(local, F_TOP_BIT_SLOT_BASE_COL + 2);
    builder
        .when(is_footer)
        .assert_zero(top_bit.clone() * (top_bit - expr::<AB>(F_TOP_BIT_MASK as u64)));

    for footer in 0..FOOTER_ROWS {
        enforce_footer_row_locals::<AB>(builder, local, selectors, footer, &words);
    }
}

fn enforce_footer_row_locals<AB>(
    builder: &mut AB,
    local: &[AB::Var],
    selectors: &EidosCompressionSelectors<AB::Expr>,
    footer: usize,
    words: &FooterWords<AB::Expr>,
) where
    AB: LiftedAirBuilder<F = Felt>,
{
    let gate = selectors.is_footer_row(footer);
    let top_bit_masked = c::<AB>(local, F_TOP_BIT_SLOT_BASE_COL + 2);

    builder
        .when(gate.clone())
        .assert_zero(cv_word::<AB>(local, 2 * footer) - words.h_even.clone());
    builder
        .when(gate.clone())
        .assert_zero(cv_word::<AB>(local, 2 * footer + 1) - words.h_odd.clone());

    for word_slot in 0..F_MSG_WORD_SLOTS {
        let word = c::<AB>(local, footer_msg_word_col(word_slot));
        let lo = c::<AB>(local, footer_range_slot_col(2 * word_slot, 0));
        let hi = c::<AB>(local, footer_range_slot_col(2 * word_slot + 1, 0));

        builder.when(gate.clone()).assert_zero(word - lo - expr::<AB>(1 << 16) * hi);
    }

    for limb in 0..F_RANGE_SLOTS {
        let base = footer_range_slot_col(limb, 0);
        builder.when(gate.clone()).assert_zero(c::<AB>(local, base + 1));
        builder.when(gate.clone()).assert_zero(c::<AB>(local, base + 2));
    }

    for pair in 0..2 {
        let lo = c::<AB>(local, footer_msg_word_col(2 * pair));
        let hi = c::<AB>(local, footer_msg_word_col(2 * pair + 1));
        enforce_canonical_pair::<AB>(
            builder,
            gate.clone(),
            lo,
            hi,
            c::<AB>(local, F_R_CANON_INV_BASE_COL + pair),
            c::<AB>(local, F_R_CANON_Z_BASE_COL + pair),
        );
    }

    let masked_odd = words.out_odd.clone() - expr::<AB>(1 << 24) * top_bit_masked;
    let packed_output = pack_pair::<AB>(words.out_even.clone(), masked_odd);
    builder
        .when(gate.clone())
        .assert_eq(c::<AB>(local, footer_digest_col(footer)), packed_output);

    enforce_canonical_pair::<AB>(
        builder,
        gate,
        words.h_even.clone(),
        words.h_odd.clone(),
        c::<AB>(local, F_C_CANON_INV_COL),
        c::<AB>(local, F_C_CANON_Z_COL),
    );
}

fn enforce_footer_transitions<AB>(
    builder: &mut AB,
    local: &[AB::Var],
    next: &[AB::Var],
    selectors: &EidosCompressionSelectors<AB::Expr>,
) where
    AB: LiftedAirBuilder<F = Felt>,
{
    for footer in 0..FOOTER_ROWS - 1 {
        let gate = selectors.is_footer_row(footer);
        let next_words = footer_words::<AB>(next);
        let consumed = [
            next_words.v_low_even,
            next_words.v_low_odd,
            next_words.v_high_even,
            next_words.v_high_odd,
        ];

        for idx in 0..2 * footer {
            builder.when(gate.clone()).assert_zero(
                c::<AB>(local, footer_r_col(footer, idx))
                    - c::<AB>(next, footer_r_col(footer + 1, idx)),
            );
        }
        for pair in 0..2 {
            let lo = c::<AB>(local, footer_msg_word_col(2 * pair));
            let hi = c::<AB>(local, footer_msg_word_col(2 * pair + 1));
            builder.when(gate.clone()).assert_zero(
                pack_pair::<AB>(lo, hi)
                    - c::<AB>(next, footer_r_col(footer + 1, 2 * footer + pair)),
            );
        }
        for idx in 0..=2 * footer + 1 {
            builder
                .when(gate.clone())
                .assert_zero(cv_word::<AB>(local, idx) - cv_word::<AB>(next, idx));
        }
        for idx in 0..=footer {
            builder.when(gate.clone()).assert_eq(
                c::<AB>(local, footer_digest_col(idx)),
                c::<AB>(next, footer_digest_col(idx)),
            );
        }
        for (idx, expected) in consumed.into_iter().enumerate() {
            builder
                .when(gate.clone())
                .assert_zero(c::<AB>(local, footer_future_w_col(footer, idx)) - expected);
        }
        for idx in 0..footer_future_w_indices(footer + 1).len() {
            builder.when(gate.clone()).assert_zero(
                c::<AB>(local, footer_future_w_col(footer, 4 + idx))
                    - c::<AB>(next, footer_future_w_col(footer + 1, idx)),
            );
        }

        builder.when(gate.clone()).assert_eq(
            c::<AB>(next, F_COMPRESSION_CYCLE_ID_COL),
            c::<AB>(local, F_COMPRESSION_CYCLE_ID_COL),
        );
    }

    // Do not enforce this on the cyclic last-row wrap. `when_transition()` is zero there.
    builder
        .when_transition()
        .when(selectors.is_footer_row(FOOTER_ROWS - 1))
        .assert_eq(
            fused_compression_cycle_id::<AB>(next),
            c::<AB>(local, F_COMPRESSION_CYCLE_ID_COL) + AB::Expr::ONE,
        );
}

fn enforce_canonical_pair<AB>(
    builder: &mut AB,
    gate: AB::Expr,
    lo: AB::Expr,
    hi: AB::Expr,
    inv: AB::Expr,
    z: AB::Expr,
) where
    AB: LiftedAirBuilder<F = Felt>,
{
    let h = hi - expr::<AB>((1u64 << 32) - 1);
    let builder = &mut builder.when(gate);
    builder.assert_zero(h.clone() * inv + z.clone() - AB::Expr::ONE);
    builder.assert_zero(z.clone() * h);
    builder.assert_zero(z * lo);
}

fn input_word<AB>(row: &[AB::Var], lane_map: &LaneMap, word_idx: usize, d_rotation: u32) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    let (g, position) = lane_position(lane_map, word_idx);
    match position {
        0 => input_a::<AB>(row, g),
        1 => input_b::<AB>(row, g),
        2 => input_c_for_rotation::<AB>(row, g, d_rotation),
        3 => input_d::<AB>(row, g),
        _ => unreachable!("lane position must be in 0..4"),
    }
}

fn output_word<AB>(
    row: &[AB::Var],
    lane_map: &LaneMap,
    word_idx: usize,
    selectors: &EidosCompressionSelectors<AB::Expr>,
) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    let (g, position) = lane_position(lane_map, word_idx);
    match position {
        0 => a_new::<AB>(row, g),
        1 => b_new::<AB>(row, g),
        2 => c_new::<AB>(row, g),
        3 => d_new::<AB>(row, g, selectors),
        _ => unreachable!("lane position must be in 0..4"),
    }
}

fn transition_output_word<AB>(
    row: &[AB::Var],
    lane_map: &LaneMap,
    word_idx: usize,
    d_rotation: u32,
) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    let (g, position) = lane_position(lane_map, word_idx);
    match position {
        0 => a_new::<AB>(row, g),
        1 => b_new::<AB>(row, g),
        2 => c_new::<AB>(row, g),
        3 => d_new_for_rotation::<AB>(row, g, d_rotation),
        _ => unreachable!("lane position must be in 0..4"),
    }
}

#[derive(Clone)]
struct FooterWords<E> {
    v_low_even: E,
    v_low_odd: E,
    v_high_even: E,
    v_high_odd: E,
    high_even_duplicate: E,
    high_odd_duplicate: E,
    h_even: E,
    h_odd: E,
    out_even: E,
    out_odd: E,
    out_odd_byte3: E,
}

fn footer_words<AB>(row: &[AB::Var]) -> FooterWords<AB::Expr>
where
    AB: LiftedAirBuilder<F = Felt>,
{
    let (v_high_even, h_even, _) = footer_xor_word::<AB>(row, F_HIGH_EVEN_SLOT_BASE);
    let (v_high_odd, h_odd, _) = footer_xor_word::<AB>(row, F_HIGH_ODD_SLOT_BASE);
    let (v_low_even, high_even_duplicate, out_even) =
        footer_xor_word::<AB>(row, F_OUTPUT_EVEN_SLOT_BASE);
    let (v_low_odd, high_odd_duplicate, out_odd) =
        footer_xor_word::<AB>(row, F_OUTPUT_ODD_SLOT_BASE);
    let out_odd_byte3 = footer_xor_byte::<AB>(row, F_OUTPUT_ODD_SLOT_BASE + 3);

    FooterWords {
        v_low_even,
        v_low_odd,
        v_high_even,
        v_high_odd,
        high_even_duplicate,
        high_odd_duplicate,
        h_even,
        h_odd,
        out_even,
        out_odd,
        out_odd_byte3,
    }
}

fn footer_xor_word<AB>(row: &[AB::Var], slot_base: usize) -> (AB::Expr, AB::Expr, AB::Expr)
where
    AB: LiftedAirBuilder<F = Felt>,
{
    let lhs = pack4::<AB>(
        c::<AB>(row, footer_xor_slot_col(slot_base, 0)),
        c::<AB>(row, footer_xor_slot_col(slot_base + 1, 0)),
        c::<AB>(row, footer_xor_slot_col(slot_base + 2, 0)),
        c::<AB>(row, footer_xor_slot_col(slot_base + 3, 0)),
    );
    let rhs = pack4::<AB>(
        c::<AB>(row, footer_xor_slot_col(slot_base, 1)),
        c::<AB>(row, footer_xor_slot_col(slot_base + 1, 1)),
        c::<AB>(row, footer_xor_slot_col(slot_base + 2, 1)),
        c::<AB>(row, footer_xor_slot_col(slot_base + 3, 1)),
    );
    let xor = pack4::<AB>(
        footer_xor_byte::<AB>(row, slot_base),
        footer_xor_byte::<AB>(row, slot_base + 1),
        footer_xor_byte::<AB>(row, slot_base + 2),
        footer_xor_byte::<AB>(row, slot_base + 3),
    );

    (lhs, rhs, xor)
}

fn footer_xor_byte<AB>(row: &[AB::Var], slot: usize) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    let base = footer_xor_slot_col(slot, 0);
    let lhs = c::<AB>(row, base);
    let rhs = c::<AB>(row, base + 1);
    let and = c::<AB>(row, base + 2);
    xor_from_and(lhs, rhs, and)
}

fn lane_position(lane_map: &LaneMap, word_idx: usize) -> (usize, usize) {
    for (g, lane) in lane_map.iter().enumerate() {
        for (position, &idx) in lane.iter().enumerate() {
            if idx == word_idx {
                return (g, position);
            }
        }
    }
    unreachable!("word index must appear exactly once in the lane map");
}

#[inline]
fn c<AB>(row: &[AB::Var], idx: usize) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    row[idx].into()
}

#[inline]
fn expr<AB>(value: u64) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    AB::Expr::from(Felt::new_unchecked(value))
}

fn pack4<AB>(b0: AB::Expr, b1: AB::Expr, b2: AB::Expr, b3: AB::Expr) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    pack_u32_le(b0, b1, b2, b3)
}

fn pack_pair<AB>(lo: AB::Expr, hi: AB::Expr) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    lo + expr::<AB>(1u64 << 32) * hi
}

fn cv_word<AB>(row: &[AB::Var], idx: usize) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    universal_cv_word(|col| c::<AB>(row, col), idx)
}

fn input_a<AB>(row: &[AB::Var], g: usize) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    let k3 = c::<AB>(row, g_k3_col(g));
    a_new::<AB>(row, g) + expr::<AB>(1u64 << 32) * k3
        - input_b::<AB>(row, g)
        - msg_word::<AB>(row, g)
}

fn input_b<AB>(row: &[AB::Var], g: usize) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    pack4::<AB>(
        c::<AB>(row, g_bd_rot_slot_col(g, 0, 0)),
        c::<AB>(row, g_bd_rot_slot_col(g, 1, 0)),
        c::<AB>(row, g_bd_rot_slot_col(g, 2, 0)),
        c::<AB>(row, g_bd_rot_slot_col(g, 3, 0)),
    )
}

fn input_c_for_rotation<AB>(row: &[AB::Var], g: usize, d_rotation: u32) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    c_new::<AB>(row, g) + expr::<AB>(1u64 << 32) * c::<AB>(row, G_K2_BASE_COL + g)
        - d_new_for_rotation::<AB>(row, g, d_rotation)
}

fn input_d<AB>(row: &[AB::Var], g: usize) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    pack4::<AB>(
        c::<AB>(row, g_ac_byte_slot_col(g, 0, 0)),
        c::<AB>(row, g_ac_byte_slot_col(g, 1, 0)),
        c::<AB>(row, g_ac_byte_slot_col(g, 2, 0)),
        c::<AB>(row, g_ac_byte_slot_col(g, 3, 0)),
    )
}

fn msg_word<AB>(row: &[AB::Var], g: usize) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    c::<AB>(row, g_msg_word_col(g))
}

fn fused_compression_cycle_id<AB>(row: &[AB::Var]) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    c::<AB>(row, G_COMPRESSION_CYCLE_ID_COL)
}

fn a_new<AB>(row: &[AB::Var], g: usize) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    pack4::<AB>(
        c::<AB>(row, g_ac_byte_slot_col(g, 0, 1)),
        c::<AB>(row, g_ac_byte_slot_col(g, 1, 1)),
        c::<AB>(row, g_ac_byte_slot_col(g, 2, 1)),
        c::<AB>(row, g_ac_byte_slot_col(g, 3, 1)),
    )
}

fn c_new<AB>(row: &[AB::Var], g: usize) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    pack4::<AB>(
        c::<AB>(row, g_bd_rot_slot_col(g, 0, 1)),
        c::<AB>(row, g_bd_rot_slot_col(g, 1, 1)),
        c::<AB>(row, g_bd_rot_slot_col(g, 2, 1)),
        c::<AB>(row, g_bd_rot_slot_col(g, 3, 1)),
    )
}

fn b_new<AB>(row: &[AB::Var], g: usize) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    debug_assert_ne!(g, MISSING_ROTATION_G);
    (0..BYTES_PER_WORD).fold(AB::Expr::ZERO, |acc, byte| {
        acc + c::<AB>(
            row,
            g_bd_rot_result_col(g, byte)
                .expect("only the final lane has a derived rotation result"),
        )
    })
}

fn d_new<AB>(row: &[AB::Var], g: usize, selectors: &EidosCompressionSelectors<AB::Expr>) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    selectors.is_ab() * d_new_for_rotation::<AB>(row, g, 16)
        + selectors.is_cd() * d_new_for_rotation::<AB>(row, g, 8)
}

fn d_new_for_rotation<AB>(row: &[AB::Var], g: usize, rotation: u32) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    let xor = [
        xor_byte::<AB>(row, g, 0),
        xor_byte::<AB>(row, g, 1),
        xor_byte::<AB>(row, g, 2),
        xor_byte::<AB>(row, g, 3),
    ];

    match rotation {
        16 => pack4::<AB>(xor[2].clone(), xor[3].clone(), xor[0].clone(), xor[1].clone()),
        8 => pack4::<AB>(xor[1].clone(), xor[2].clone(), xor[3].clone(), xor[0].clone()),
        _ => unreachable!("EidosCompression first rotation must be 16 or 8 bits"),
    }
}

fn xor_byte<AB>(row: &[AB::Var], g: usize, byte: usize) -> AB::Expr
where
    AB: LiftedAirBuilder<F = Felt>,
{
    let lhs = c::<AB>(row, g_ac_byte_slot_col(g, byte, 0));
    let rhs = c::<AB>(row, g_ac_byte_slot_col(g, byte, 1));
    let and = c::<AB>(row, g_ac_byte_slot_col(g, byte, 2));
    xor_from_and(lhs, rhs, and)
}
