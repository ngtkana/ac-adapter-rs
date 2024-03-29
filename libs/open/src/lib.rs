use std::ops::Bound;
use std::ops::Range;
use std::ops::RangeBounds;

pub fn open(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    use Bound::Excluded;
    use Bound::Included;
    use Bound::Unbounded;
    (match range.start_bound() {
        Unbounded => 0,
        Included(&x) => x,
        Excluded(&x) => x + 1,
    })..(match range.end_bound() {
        Excluded(&x) => x,
        Included(&x) => x + 1,
        Unbounded => len,
    })
}
