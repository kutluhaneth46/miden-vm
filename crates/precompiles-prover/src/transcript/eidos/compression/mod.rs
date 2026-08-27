//! PVM-owned 32-row Eidos compression core.
//!
//! This module intentionally owns its layout, constraints, selectors, lookup plan, and trace
//! writer. It shares the Eidos compression primitive and the fixed byte-pair table semantics with
//! the Miden VM, but it does not import the Miden VM's compression AIR or trace layout.

mod algebra;
pub(crate) mod constraints;
#[cfg(test)]
mod constraints_tests;
pub(crate) mod layout;
#[cfg(test)]
mod layout_tests;
mod lookup;
mod model;
mod periodic;
mod schedule;
pub(crate) mod selectors;
pub(crate) mod trace;

pub(super) use algebra::universal_cv_word;
pub(super) use lookup::{
    EIDOS_COMPRESSION_LOOKUP_COLUMN_SHAPE, EidosCompressionCols, emit_lookup_columns,
};
pub(crate) use periodic::{NUM_PERIODIC_COLUMNS, get_periodic_column_values};
