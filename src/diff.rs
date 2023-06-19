mod range_list;

#[derive(Debug, PartialEq)]
pub struct DiffRange<'a, K> {
    /// The inclusive start & end key bounds of this range to sync.
    start: &'a K,
    end: &'a K,
}

impl<'a, K> Clone for DiffRange<'a, K> {
    fn clone(&self) -> Self {
        Self {
            start: self.start.clone(),
            end: self.end.clone(),
        }
    }
}

impl<'a, K> DiffRange<'a, K> {
    pub fn overlaps(&self, p: &Self) -> bool
    where
        K: PartialOrd,
    {
        //   0 1 2 3 4 5 6 7 8 9
        // A |       |
        // B       |   |
        let leading_edge = self.start <= p.start && self.end >= p.start;
        let trailing_edge = p.start <= self.end && p.end >= self.end;
        leading_edge || trailing_edge
    }

    pub fn start(&self) -> &K {
        self.start
    }

    pub fn end(&self) -> &K {
        self.end
    }
}
