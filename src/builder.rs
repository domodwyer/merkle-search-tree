//! A configurable [`MerkleSearchTree`] constructor.
//!
//! [`MerkleSearchTree`]: crate::MerkleSearchTree

use std::num::NonZeroU8;

use crate::DEFAULT_LEVEL_BASE;

/// A [`MerkleSearchTree`] builder to initialise trees with custom parameters.
///
/// [`MerkleSearchTree`]: crate::MerkleSearchTree
#[derive(Debug, Clone)]
pub struct Builder<H> {
    pub(crate) hasher: H,
    pub(crate) level_base: NonZeroU8,
}

impl Default for Builder<super::tree::DefaultHasher> {
    fn default() -> Self {
        Self {
            hasher: Default::default(),
            level_base: DEFAULT_LEVEL_BASE,
        }
    }
}

impl<H> Builder<H> {
    /// Use the provided [`Hasher`] to compute key and value digests.
    ///
    /// [`Hasher`]: crate::digest::Hasher
    pub fn with_hasher<T>(self, hasher: T) -> Builder<T> {
        Builder {
            hasher,
            level_base: self.level_base,
        }
    }

    /// Configure the value for the parameter `B` as described in the paper (the
    /// branching factor).
    ///
    /// Decreasing this value increases the hight of the tree, which increases
    /// the number of pages, and therefore decreases the average page size.
    pub fn with_level_base(self, b: NonZeroU8) -> Self {
        Self {
            level_base: b,
            ..self
        }
    }
}

// build() is in tree.rs
