/// A hash function outputting a fixed-length digest of `N` bytes.
///
/// The hash function must produce strong digests with a low probability of
/// collision. Use of a cryptographic hash function is not required, but may be
/// preferred for security/compliance reasons.
///
/// Use of a faster hash function results in faster tree operations. Use of
/// 64bit hash values (`N == 8`) and smaller is not recommended due to the
/// higher probability of collisions.
///
/// # Determinism & Portability
///
/// Implementations are required to be deterministic across all peers which
/// compare tree values. Notably the standard library [`Hash`] derive does not
/// produce portable hashes across differing platforms, endian-ness or Rust
/// compiler versions.
///
/// # Default Implementation
///
/// The default [`Hasher`] implementation ([`SipHasher`]) outputs 128-bit/16
/// byte digests which are strong, but not of cryptographic quality.
///
/// [`SipHasher`] uses the [`Hash`] trait, which may produce non-portable hashes
/// as described above (and in the [`Hash`] documentation).
///
/// Users may choose to initialise the [`SipHasher`] with seed keys if untrusted
/// key/value user input is used in a tree in order to prevent chosen-hash
/// collision attacks.
///
/// [`SipHasher`]: super::siphash::SipHasher
pub trait Hasher<const N: usize, T> {
    /// Hash `T`, producing a unique, deterministic digest of `N` bytes length.
    fn hash(&self, value: &T) -> Digest<N>;
}

/// A variable bit length digest, output from a [`Hasher`] implementation.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Digest<const N: usize>([u8; N]);

impl<const N: usize> Digest<N> {
    /// Wrap an opaque byte array in a [`Digest`] for type safety.
    pub const fn new(digest: [u8; N]) -> Self {
        Self(digest)
    }
}

impl<const N: usize> AsRef<[u8]> for Digest<N> {
    fn as_ref(&self) -> &[u8] {
        &self.0
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

/// The root hash of a [`MerkleSearchTree`], representative of the state of the
/// tree.
///
/// Two instances of a [`MerkleSearchTree`] are guaranteed to contain the same
/// state iff both [`RootHash`] read from the trees are identical (assuming
/// identical, deterministic [`Hasher`] implementations).
///
/// [`MerkleSearchTree`]: crate::MerkleSearchTree
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

/// Extract the number of leading 0's when expressed as base 16 digits, defining
/// the tree level the hash should reside at.
pub(crate) fn level<const N: usize>(v: &Digest<N>) -> u8 {
    let mut out = 0;
    for v in v.0.into_iter().map(zero_prefix_len) {
        match v {
            2 => out += 2,
            1 => return out + 1,
            0 => return out,
            _ => unreachable!(),
        }
    }
    out
}

// Returns the number of consecutive zero characters when `v` is represented as
// a base16 string (evaluated LSB to MSB).
fn zero_prefix_len(v: u8) -> u8 {
    // Implemented as a look-up table for fast calculation.
    match v {
        0x00 => 2,
        0x10 => 1,
        0x20 => 1,
        0x30 => 1,
        0x40 => 1,
        0x50 => 1,
        0x60 => 1,
        0x70 => 1,
        0x80 => 1,
        0x90 => 1,
        0xA0 => 1,
        0xB0 => 1,
        0xC0 => 1,
        0xD0 => 1,
        0xE0 => 1,
        0xF0 => 1,
        _ => 0,
    }
}
