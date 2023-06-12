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
