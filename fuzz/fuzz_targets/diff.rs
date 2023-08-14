#![no_main]

use libfuzzer_sys::{arbitrary::Arbitrary, fuzz_target};
use merkle_search_tree::{
    diff::{diff, PageRange},
    digest::{Digest, PageDigest},
};

// An owned PageRange payload, from which a PageRange instance will be
// projected.
#[derive(Debug)]
struct Input {
    start: Vec<u8>,
    end: Vec<u8>,
    hash: [u8; 16],
}

impl<'a> Arbitrary<'a> for Input {
    fn arbitrary(
        u: &mut libfuzzer_sys::arbitrary::Unstructured<'a>,
    ) -> libfuzzer_sys::arbitrary::Result<Self> {
        Ok(Self {
            start: u.arbitrary()?,
            end: u.arbitrary()?,
            hash: u.arbitrary()?,
        })
    }
}

impl<'a> From<&'a Input> for PageRange<'a, Vec<u8>> {
    fn from(v: &'a Input) -> Self {
        // Constructing a PageRange will panic if start > end.
        //
        // This forms the boundary of user responsibility - the user should
        // validate this property, and the diff() algorithm should never panic
        // when fed PageRange instances.
        PageRange::new(
            (&v.start).min(&v.end),
            (&v.start).max(&v.end),
            PageDigest::new(Digest::new(v.hash)),
        )
    }
}

// Feed the diff() algorithm with random PageRange lists.
fuzz_target!(|data: (Vec<Input>, Vec<Input>)| {
    let a = data.0.iter().map(PageRange::from);
    let b = data.1.iter().map(PageRange::from);

    diff(a, b);
});
