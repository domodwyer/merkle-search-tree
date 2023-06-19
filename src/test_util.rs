use std::fmt::Display;

/// An wrapper over integers, implementing `AsRef<[u8]>` with deterministic
/// output across platforms with differing endian-ness.
#[derive(PartialOrd, Ord, PartialEq, Eq, Clone, Hash)]
pub struct IntKey(u64, [u8; 8]);

impl std::fmt::Debug for IntKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("IntKey").field(&self.0).finish()
    }
}
impl IntKey {
    pub fn new(v: u64) -> Self {
        Self(v, v.to_be_bytes())
    }
    pub fn unwrap(&self) -> u64 {
        self.0
    }
}
impl AsRef<[u8]> for IntKey {
    fn as_ref(&self) -> &[u8] {
        &self.1
    }
}
impl Display for IntKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.0, f)
    }
}
