//! Trait & implementations for tree structure inspection.

pub mod dot;
pub(crate) mod page_range_hash;

mod r#trait;
pub use r#trait::*;

#[cfg(test)]
pub(crate) mod assert_count;
#[cfg(test)]
pub(crate) mod assert_order;
#[cfg(test)]
pub(crate) mod nop;
