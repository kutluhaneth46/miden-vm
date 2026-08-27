//! Lookup columns for the 32-row Eidos compression layout.

use core::borrow::Borrow;

use miden_air::{
    logup::{BusId, eidos_compression_rot7_bus, eidos_compression_rot12_bus},
    lookup::{Deg, LookupBuilder, LookupColumn, LookupGroup},
};
use miden_core::{Felt, field::PrimeCharacteristicRing};

use super::{algebra::missing_rotation_result, layout::*, selectors::EidosCompressionSelectors};
/// Typed view of the PVM-owned Eidos compression main-trace columns.
#[repr(C)]
#[derive(Clone, Debug)]
pub struct EidosCompressionCols<T> {
    /// Physical columns in the layout documented by the Eidos compression module.
    pub columns: [T; NUM_COLS],
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

const NARROW_BATCH_COLUMNS: usize = 18;

const BATCH2_DEG: Deg = Deg { v: 2, u: 2 };

fn selected_column_deg(aux_col: usize) -> Deg {
    match aux_col {
        0..NARROW_BATCH_COLUMNS => BATCH2_DEG,
        _ => unreachable!("PVM EidosCompression lookup aux column out of range"),
    }
}

/// Lookup builder accepted by the Eidos compression AIR.
pub(in crate::transcript::eidos) trait EidosCompressionLookupBuilder:
    LookupBuilder<F = Felt>
{
}

impl<T> EidosCompressionLookupBuilder for T where T: LookupBuilder<F = Felt> {}

/// Emits all Eidos compression lookup groups in their fixed auxiliary-column order.
pub(in crate::transcript::eidos) fn emit_lookup_columns<LB>(
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
        _ => unreachable!("PVM EidosCompression lookup aux column out of range"),
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
