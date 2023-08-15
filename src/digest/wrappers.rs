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

#[cfg(feature = "digest_base64")]
impl std::fmt::Display for RootHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
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
    /// Construct a new [`PageDigest`] from an untyped 16-byte [`Digest`].
    pub const fn new(value: Digest<16>) -> Self {
        Self(value)
    }
}

#[cfg(feature = "digest_base64")]
impl std::fmt::Display for PageDigest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
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

#[cfg(feature = "digest_base64")]
impl<const N: usize> std::fmt::Display for ValueDigest<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(feature = "digest_base64")]
    fn test_base64_format() {
        let d = Digest::new([0x62, 0x61, 0x6e, 0x61, 0x6e, 0x61, 0x73, 0x0a]);
        assert_eq!(d.to_string(), "YmFuYW5hcwo=");

        let value = ValueDigest::new(Digest::new([
            0x62, 0x61, 0x6e, 0x61, 0x6e, 0x61, 0x73, 0x0a,
        ]));
        assert_eq!(value.to_string(), "YmFuYW5hcwo=");

        let page = PageDigest::new(Digest::new([
            0x62, 0x61, 0x6e, 0x61, 0x6e, 0x61, 0x73, 0x0a, 0x62, 0x61, 0x6e, 0x61, 0x6e, 0x61,
            0x73, 0x0a,
        ]));
        assert_eq!(page.to_string(), "YmFuYW5hcwpiYW5hbmFzCg==");
    }

    #[test]
    fn test_as_bytes() {
        let b = [
            42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42,
        ];
        let d = PageDigest::new(Digest::new(b));
        assert_eq!(b, *d.as_bytes());
    }
}
