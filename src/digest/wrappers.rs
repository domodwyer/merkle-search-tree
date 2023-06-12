use super::Digest;

/// The root hash of a [`MerkleSearchTree`], representative of the state of the
/// tree.
///
/// Two instances of a [`MerkleSearchTree`] are guaranteed to contain the same
/// state iff both [`RootHash`] read from the trees are identical (assuming
/// identical, deterministic [`Hasher`] implementations).
///
/// [`MerkleSearchTree`]: crate::MerkleSearchTree
/// [`Hasher`]: super::Hasher
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RootHash(Digest<16>);

impl std::ops::Deref for RootHash {
    type Target = Digest<16>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl RootHash {
    pub(crate) const fn new(value: PageDigest) -> Self {
        Self(value.0)
    }
}

/// Type wrapper over a [`Digest`] of a tree key, for readability / clarity /
/// compile-time safety.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct KeyDigest<const N: usize>(Digest<N>);

impl<const N: usize> std::ops::Deref for KeyDigest<N> {
    type Target = Digest<N>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const N: usize> KeyDigest<N> {
    pub(crate) const fn new(value: Digest<N>) -> Self {
        Self(value)
    }
}

impl<const N: usize> std::fmt::Display for KeyDigest<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for &v in self.as_ref() {
            f.write_fmt(format_args!("{}", v))?;
        }
        Ok(())
    }
}

/// Type wrapper over a [`Digest`] of a tree value, for readability / clarity /
/// compile-time safety.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ValueDigest<const N: usize>(Digest<N>);

impl<const N: usize> std::ops::Deref for ValueDigest<N> {
    type Target = Digest<N>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const N: usize> ValueDigest<N> {
    pub(crate) const fn new(value: Digest<N>) -> Self {
        Self(value)
    }
}

/// Type wrapper over a [`Digest`] of a [`Page`], representing the hash of the
/// nodes & subtree rooted at the [`Page`].
///
/// [`Page`]: crate::page::Page
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PageDigest(Digest<16>);

impl std::ops::Deref for PageDigest {
    type Target = Digest<16>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PageDigest {
    pub(crate) const fn new(value: Digest<16>) -> Self {
        Self(value)
    }
}
