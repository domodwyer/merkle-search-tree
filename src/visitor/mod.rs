//! Trait & implementations for tree structure inspection.

pub mod dot;

mod r#trait;
pub use r#trait::*;

#[cfg(test)]
pub(crate) mod assert_count;
#[cfg(test)]
pub(crate) mod assert_order;
#[cfg(test)]
pub(crate) mod nop;
