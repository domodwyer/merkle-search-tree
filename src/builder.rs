//! A configurable [`MerkleSearchTree`] constructor.
//!
//! [`MerkleSearchTree`]: crate::MerkleSearchTree

/// A [`MerkleSearchTree`] builder to initialise trees with custom parameters.
///
/// [`MerkleSearchTree`]: crate::MerkleSearchTree
#[derive(Debug, Clone)]
pub struct Builder<H> {
    pub(crate) hasher: H,
}

impl Default for Builder<super::tree::DefaultHasher> {
    fn default() -> Self {
        Self {
            hasher: Default::default(),
        }
    }
}

impl<H> Builder<H> {
    /// Use the provided [`Hasher`] to compute key and value digests.
    ///
    /// [`Hasher`]: crate::digest::Hasher
    pub fn with_hasher<T>(&mut self, hasher: T) -> Builder<T> {
        Builder { hasher }
    }
}

// build() is in tree.rs
