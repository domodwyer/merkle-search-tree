//! A default [`Hasher`] implementation backed by [`SipHasher24`].

use siphasher::sip128::{Hasher128, SipHasher24};

use super::{Digest, Hasher};

/// A fast, non-cryptographic hash outputting 128-bit digests.
///
/// This implementation is used as the default [`Hasher`] implementation, using
/// the [`Hash`] trait, which may produce non-portable hashes as described in
/// the documentation of the [`Hash`] trait, and [`Hasher`].
///
/// Users may choose to initialise the [`SipHasher`] with seed keys if untrusted
/// key/value user input is used in a tree in order to prevent chosen-hash
/// collision attacks.
#[derive(Debug, Default, Clone)]
#[allow(missing_copy_implementations)]
pub struct SipHasher {
    hasher: SipHasher24,
}

impl SipHasher {
    /// Initialise a [`SipHasher`] with the provided seed key.
    ///
    /// All peers comparing tree hashes MUST be initialised with the same seed
    /// key.
    pub fn new(key: &[u8; 16]) -> Self {
        let hasher = SipHasher24::new_with_key(key);
        Self { hasher }
    }
}

impl<T> Hasher<16, T> for SipHasher
where
    T: std::hash::Hash,
{
    fn hash(&self, value: &T) -> Digest<16> {
        let mut h = self.hasher;
        value.hash(&mut h);
        Digest::new(h.finish128().as_bytes())
    }
}
