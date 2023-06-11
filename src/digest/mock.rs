use std::{fmt::Display, iter};

use super::*;

#[derive(Debug, Clone)]
pub struct LevelKey<T>(T, u8);

impl<T> PartialEq for LevelKey<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> PartialOrd for LevelKey<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<T> Display for LevelKey<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0.to_string().as_str())
    }
}

impl<T> LevelKey<T> {
    pub fn new(key: T, level: u8) -> Self
    where
        T: Display,
    {
        Self(key, level)
    }
}

#[derive(Debug, Default)]
pub struct MockHasher;

impl MockHasher {
    pub fn hash<T>(t: &T) -> Digest<32>
    where
        Self: Hasher<32, T>,
    {
        <Self as Hasher<32, T>>::hash(&Self::default(), t)
    }
}

impl<T> Hasher<32, LevelKey<T>> for MockHasher
where
    T: Display,
{
    fn hash(&self, value: &LevelKey<T>) -> Digest<32> {
        let level: u8 = value.1;
        let iter = iter::repeat(0).take(usize::try_from(level).expect("cast fail") / 2);

        let mut v: Vec<_> = if (level % 2) == 1 {
            iter.chain(iter::once(0xF0)).collect()
        } else {
            iter.collect()
        };

        v.resize(32, 1);
        Digest::new(v.try_into().unwrap())
    }
}

impl Hasher<32, &str> for MockHasher {
    fn hash(&self, value: &&str) -> Digest<32> {
        let mut v = value.as_bytes().to_vec();
        assert!(v.len() <= 32, "mock hash value is more than 32 bytes");

        v.resize(32, 1);
        Digest::new(v.try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mock_hasher() {
        let got = MockHasher::default().hash(&LevelKey::new("A", 0));
        assert_eq!(level(&got), 0);

        let got = MockHasher::default().hash(&LevelKey::new("A", 1));
        assert_eq!(level(&got), 1);

        let got = MockHasher::default().hash(&LevelKey::new("key_A", 2));
        assert_eq!(level(&got), 2);

        let got = MockHasher::default().hash(&LevelKey::new("key_A", 10));
        assert_eq!(level(&got), 10);
    }
}
