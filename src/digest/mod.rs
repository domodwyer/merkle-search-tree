//! Hash function abstraction & digest types.

pub mod siphash;
mod r#trait;
mod wrappers;

pub use r#trait::*;
pub use wrappers::*;

#[cfg(test)]
pub(crate) mod mock;
