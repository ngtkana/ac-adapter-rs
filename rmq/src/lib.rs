//! Min-position query や least ancestor query をします。
//!
//! # Features
//!
//! つぎのようなことができます。
//!
//! ## Min-position Query
//!
//! 項同士の全順序的な大小比較の可能な列が前もって与えられます。
//!
//! さらに、クエリごとに添字の区間が与えられます。
//! これに属する項のうち、値と添字の辞書式順序で最小なものの添字を
//! 答えるのがこちらの問題です。
//!
//! Extra constraints のところに ±1 - property と書いてあるものは、
//! 非常に一般的な定式化をすると、
//! 値が整数の順序保存的な作用を持っていて、隣接するものが
//! ±1 どちらかの作用で移り合うことが要求されます。
//! しかし、結局は値そのものが整数なものに帰着されますから、
//! あまり考える必要がないということがわかります。
//! 当ライブラリでも、制約のないものは [`Ord`] を実装したあらゆる型を受け取るのに対し、
//! ±1 - property 制約のあるものは [`usize`] しか受けとれないようになっています。
//!
//! | struct name        | construction  | min-position query | extra constraits | implementation                               |
//! |-                   | -             | -                  | -                | -                                            |
//! | [`FastMinimum`]    | Θ( N )       | Θ( 1 )            | nothing          | Cartesian tree + Eular Tour + Compound Table |
//! | [`CompoundTable`]  | Θ( n )       | Θ( 1 )            | ±1 - property   | Sparse table + Precalculate all              |
//! | [`SparseTable`]    | Θ( n lg n )  | Θ( 1 )            | nothing          | Sparse table                                 |
//! | [`Prec`]           | Θ( 2 ^ n n ) | Θ( 1 )            | ±1 - property   | Precalculate all                             |
//!
//!
//! ## Least common ancestor
//!
//! 木が隣接リストのかたちで与えられ、根が指定されます。
//!
//! クエリごとに頂点が 2 つ与えられます。
//! これらの共通な祖先であって深さが最大なものがただ一つ存在しますから、
//! それを答えましょうというのが、こちらの問題です。
//!
//!
//! | struct name             | construction  | LCA query | extra constraits | implementation              |
//! |-                        | -             | -         | -                | -                           |
//! | [`LeastCommonAncestor`] | Θ( N )       | Θ( 1 )   | nothing          | Eular Tour + Compound Table |
//!
//!
//! ## Cartesian tree
//!
//! 項同士の全順序的な大小比較の可能で、重複がないような列に対して、
//! 次の性質を満たす二分木が一意的に存在します。それを Cartesian tree といいます。
//!
//! - 各頂点は列の各項に対応します。
//! - in-order traversal の結果がもとの列になります。
//! - min-heap property を満たします。
//!
//! 重複がある列に対しては一意的でありませんが、
//! このライブラリでは値と添字の辞書式順序に関する
//! 一意的な Cartesian tree を返すことにします。
//!
//! | function name           | construction  | extra constraits | implementation              |
//! |-                        | -             | -                | -                           |
//! | [`LeastCommonAncestor`] | Θ( N )       | nothing          | Eular Tour + Compound Table |
//!
//! [`FastMinimum`]: struct.FastMinimum.html
//! [`CompoundTable`]: struct.CompoundTable.html
//! [`SparseTable`]: struct.SparseTable.html
//! [`Prec`]: struct.Prec.html
//! [`LeastCommonAncestor`]: struct.LeastCommonAncestor.html
//!
//! [`usize`]: https://doc.rust-lang.org/std/primitive.usize.html
//! [`Ord`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html

use ordtools::Ordtools;
use std::ops::{Bound, Range, RangeBounds};

// TODO: クレートを分けます。
trait BitPosition {
    fn pow_of_two(self) -> usize;
}

impl BitPosition for usize {
    fn pow_of_two(self) -> usize {
        1 << self
    }
}

trait Bit {
    fn flip(self) -> Self;
    fn reverse_and_flip(self) -> Self;
    fn lg_unchecked(self) -> u32;
    fn lg_usize_unchecked(self) -> usize;
    fn lg(self) -> Option<u32>;
    fn lg_usize(self) -> Option<usize>;
    fn lg_ceil(self) -> u32;
    fn lg_ceil_usize(self) -> usize;
}

impl Bit for usize {
    fn flip(self) -> Self {
        self ^ std::usize::MAX
    }
    fn reverse_and_flip(self) -> Self {
        self.reverse_bits() ^ std::usize::MAX
    }
    fn lg_ceil(self) -> u32 {
        self.next_power_of_two().trailing_zeros()
    }
    fn lg_ceil_usize(self) -> usize {
        self.lg_ceil() as usize
    }
    fn lg_unchecked(self) -> u32 {
        (self + 1).lg_ceil() - 1
    }
    fn lg_usize_unchecked(self) -> usize {
        self.lg_unchecked() as usize
    }
    fn lg(self) -> Option<u32> {
        if self == 0 {
            None
        } else {
            Some(self.lg_unchecked())
        }
    }
    fn lg_usize(self) -> Option<usize> {
        if self == 0 {
            None
        } else {
            Some(self.lg_usize_unchecked())
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// fast min-position ///////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
/// Min-position クエリに答えられるデータ構造です。
pub struct FastMinimum {
    body: FastMinimumBody,
}
pub enum FastMinimumBody {
    Empty,
    NonEmmpty {
        len: usize,
        lca: Box<LeastCommonAncestor>,
    },
}
impl FastMinimum {
    /// 構築をします。
    ///
    /// # Examples
    /// ```
    /// use rmq::FastMinimum;
    /// let fast_minimum = FastMinimum::build(&[3, 2, 8]);
    /// ```
    pub fn build<T: Ord>(seq: &[T]) -> Self {
        Self {
            body: if seq.is_empty() {
                FastMinimumBody::Empty
            } else {
                let parent = construct_cartesian_tree(seq);
                let mut tree = vec![vec![]; seq.len()];
                let mut root = 0;
                for (i, &p) in parent.iter().enumerate() {
                    if i == p {
                        root = i;
                    } else {
                        tree[i].push(p);
                        tree[p].push(i);
                    }
                }
                FastMinimumBody::NonEmmpty {
                    len: seq.len(),
                    lca: Box::new(LeastCommonAncestor::from_tree(root, &tree)),
                }
            },
        }
    }

    /// Min-position クエリにお答えします。
    ///
    /// `range` が空区間の場合は `None` を返します。
    ///
    /// # Examples
    /// ```
    /// use rmq::FastMinimum;
    /// let frm = FastMinimum::build(&[3, 2, 8, 1]);
    /// assert_eq!(frm.query(1..1), None);
    /// assert_eq!(frm.query(2..1), None);
    /// assert_eq!(frm.query(..), Some(3));
    /// assert_eq!(frm.query(0..=2), Some(1));
    /// ```
    pub fn query(&self, range: impl RangeBounds<usize>) -> Option<usize> {
        match &self.body {
            FastMinimumBody::Empty => None,
            FastMinimumBody::NonEmmpty { len, lca } => {
                let start = match range.start_bound() {
                    Bound::Excluded(&x) => x + 1,
                    Bound::Included(&x) => x,
                    Bound::Unbounded => 0,
                };
                let end = match range.end_bound() {
                    Bound::Excluded(&x) => {
                        if x == 0 {
                            return None;
                        } else {
                            x - 1
                        }
                    }
                    Bound::Included(&x) => x,
                    Bound::Unbounded => len - 1,
                };
                if start > end {
                    None
                } else {
                    Some(lca.query(start, end))
                }
            }
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// cartesian  tree /////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
/// Cartesian tree を構築します。
///
/// # Examples
///
/// ```
/// use rmq::construct_cartesian_tree;
/// let seq = [11, 11, 10];
/// let cartesian_tree = construct_cartesian_tree(&seq);
/// assert_eq!(cartesian_tree, vec![2, 0, 2]);
/// ```
pub fn construct_cartesian_tree<T: Ord>(seq: &[T]) -> Vec<usize> {
    let mut p = vec![0; seq.len()];
    let mut stack = vec![0];
    for x in 1..seq.len() {
        if let Some((j, y)) = stack
            .iter()
            .copied()
            .enumerate()
            .rfind(|&(_, y)| seq[y] <= seq[x])
        {
            p[x] = y;
            if j != stack.len() - 1 {
                let z = stack[j + 1];
                p[z] = x;
            }
            stack.truncate(j + 1);
            stack.push(x);
        } else {
            p[stack[0]] = x;
            p[x] = x;
            stack = vec![x];
        }
    }
    p
}

////////////////////////////////////////////////////////////////////////////////
// least common ancestor ///////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
/// Least common ancestor クエリに答えられるデータ構造です。
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LeastCommonAncestor {
    span: Vec<Range<usize>>,
    time_to_id: Vec<usize>,
    compound_table: CompoundTable,
}

impl LeastCommonAncestor {
    /// 隣接リストから構築します。
    ///
    /// # Restrictions
    ///
    /// 空の木渡すと実行時エラーになります。
    /// 親へのポインターは、あってもなくても動きます。（あったら読み飛ばします。）
    ///
    /// # Examples
    ///
    /// ```
    /// use rmq::LeastCommonAncestor;
    /// let lca = LeastCommonAncestor::from_tree(0, vec![vec![1, 2], vec![], vec![]].as_slice());
    /// ```
    pub fn from_tree(root: usize, tree: &[Vec<usize>]) -> Self {
        // dfs に渡したい環境変数を束ねます。
        #[derive(Debug, Eq, PartialEq)]
        struct Env<'a> {
            time: usize,
            time_to_id: Vec<usize>,
            span: Vec<Range<usize>>,
            depth_table: Vec<usize>,
            tree: &'a [Vec<usize>],
        }
        let mut env = Env {
            time: 0,
            time_to_id: vec![0; tree.len() * 2 - 1],
            depth_table: vec![0; tree.len() * 2 - 1],
            tree,
            span: std::iter::repeat(tree.len() * 2 - 1..0)
                .take(tree.len())
                .collect(),
        };

        fn dfs(x: usize, p: usize, d: usize, env: &mut Env) {
            env.time_to_id[env.time] = x;
            env.depth_table[env.time] = d;
            env.span[x].start.change_min(&env.time);
            env.time += 1;

            for y in env.tree[x].iter().copied().filter(|&y| y != p) {
                dfs(y, x, d + 1, env);
                env.time_to_id[env.time] = x;
                env.depth_table[env.time] = d;
                env.time += 1;
            }
            env.span[x].end.change_max(&(env.time));
        }
        dfs(root, root, 0, &mut env);

        Self {
            span: env.span,
            time_to_id: env.time_to_id,
            compound_table: CompoundTable::from_vec(env.depth_table),
        }
    }

    /// Least common ancestor の頂点番号を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use rmq::LeastCommonAncestor;
    /// let lca = LeastCommonAncestor::from_tree(0, vec![vec![1, 2], vec![], vec![]].as_slice());
    ///
    /// assert_eq!(lca.query(0, 0), 0);
    /// assert_eq!(lca.query(0, 1), 0);
    /// assert_eq!(lca.query(1, 1), 1);
    /// assert_eq!(lca.query(1, 2), 0);
    /// assert_eq!(lca.query(2, 2), 2);
    /// ```
    pub fn query(&self, u: usize, v: usize) -> usize {
        let Range {
            start: start_u,
            end: end_u,
        } = self.span[u];
        let Range {
            start: start_v,
            end: end_v,
        } = self.span[v];
        self.time_to_id[self
            .compound_table
            .query(start_u.min(start_v)..end_u.max(end_v))
            .unwrap()]
    }
}

////////////////////////////////////////////////////////////////////////////////
// CompoundTable ///////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
/// ±1-seq min-position クエリにお答えします。
///
/// アルゴリズムの解説です。
///
/// # Precalculation
///
/// - 長さ `max(lg(n) / 2, 1)` のブロックに切ります。
/// - それぞれのブロックの増減パターンを記録です。
/// - それぞれのブロックの min-position （絶対位置）を計算です。
/// - さらにあり得るすべての増減パターンについて累積 min-position を求めます。（[`Prec`] を構築します。）
///
/// # Query
///
/// - クエリ区間のうちちまちましたところは、増減パターンをシフトして前計算に帰着です。（[`Prec::query`])
/// を呼びます。
/// - どーんというところは、いまのところ愚直なのですが、sparse table に書き換える予定です。
///
/// [`Prec`]: struct.Prec.html
/// [`Prec::query`]: struct.Prec.html#method.query
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CompoundTable {
    seq: Vec<usize>,
    block_size: usize,
    pattern: Vec<usize>,
    prec: Prec,
    block_minimums: Vec<usize>,
    sparse_table: SparseTable<usize>,
}
impl CompoundTable {
    /// 構築をします。
    ///
    /// # Example
    ///
    /// ```
    /// use rmq::CompoundTable;
    /// let pm1_rmq = CompoundTable::from_vec((0..20).collect());
    /// ```
    pub fn from_vec(seq: Vec<usize>) -> Self {
        // ±1-property をチェックです。
        if !seq.is_empty() {
            for i in 0..seq.len() - 1 {
                assert!(seq[i] + 1 == seq[i + 1] || seq[i] == seq[i + 1] + 1);
            }
        }

        // n が 3 以下のとき 1 です。
        // n が 4 以上のとき lg(n) / 2 です。
        let block_size = seq.len().lg_usize().map(|x| x / 2).unwrap_or(1).max(1);

        // ブロック内の min-positions を計算しておきます。
        let block_minimums: Vec<_> = (0..seq.len())
            .collect::<Vec<_>>()
            .chunks(block_size)
            .map(|subseq| subseq.iter().copied().min_by_key(|&i| (seq[i], i)).unwrap())
            .collect();

        // ブロックごとのパターンを計算です。
        //
        // 減少する箇所に bit を立てます。
        // block_size で割り切れるところは読み飛ばして詰めています。
        //
        let mut pattern = vec![0; block_minimums.len()];
        for i in (0..seq.len()).filter(|&i| i % block_size != 0) {
            let q = i / block_size;
            let r = i - q * block_size;
            if seq[i - 1] > seq[i] {
                pattern[q] |= (r - 1).pow_of_two();
            }
        }

        Self {
            block_size,
            pattern,
            prec: Prec::with_len(block_size),
            block_minimums,
            sparse_table: SparseTable::from_vec(seq.clone()),
            seq,
        }
    }

    /// Min-position query にお答えします。
    ///
    /// `range` が空区間の場合は `None` を返します。
    ///
    /// # Example
    ///
    /// ```
    /// use rmq::CompoundTable;
    /// let pm1_rmq = CompoundTable::from_vec(vec![2, 1, 2, 3, 2, 1]);
    ///
    /// assert_eq!(pm1_rmq.query(0..0), None);
    /// assert_eq!(pm1_rmq.query(0..1), Some(0));
    /// assert_eq!(pm1_rmq.query(..), Some(1));
    /// assert_eq!(pm1_rmq.query(3..=5), Some(5));
    /// ```
    pub fn query(&self, range: impl RangeBounds<usize>) -> Option<usize> {
        let (start, end) = get_start_and_end(self.seq.len(), &range);
        if start >= end {
            None
        } else {
            let k = self.block_size;
            let start_block = start / k;
            let start_rem = start - start_block * k;
            let end_block = end / k;
            let end_rem = end - end_block * k;
            if start_block == end_block {
                self.prec.query(self.pattern[start_rem], start_rem..end_rem)
            } else {
                let left = self
                    .prec
                    .query(self.pattern[start_block], start_rem..)
                    .map(|i| start_block * self.block_size + i);
                let center = self.block_minimums[start_block + 0..end_block]
                    .iter()
                    .copied()
                    .min_by_key(|&i| (self.seq[i], i));
                let right = self
                    .pattern
                    .get(end_block)
                    .and_then(|&pattern| self.prec.query(pattern, 0..end_rem))
                    .map(|i| end_block * self.block_size + i);
                [left, center, right]
                    .iter()
                    .flatten()
                    .copied()
                    .min_by_key(|&i| self.seq[i])
            }
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// SparseTable /////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
/// Range minimum query に答えられるデータ構造です。
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SparseTable<T: Ord> {
    seq: Vec<T>,
    table: Vec<Vec<usize>>,
}

impl<T: Ord> SparseTable<T> {
    /// 構築をします。
    ///
    /// ```
    /// use rmq::SparseTable;
    /// let sparse_table = SparseTable::from_vec(vec![4, 5, 1]);
    /// ```
    pub fn from_vec(seq: Vec<T>) -> Self {
        Self {
            table: {
                let n = seq.len();
                let h = n.lg_usize().unwrap_or(0) + 1;
                let mut table = vec![vec![0; n]; h];
                table[0] = (0..n).collect();
                let mut d = 1;
                for i in 0..h - 1 {
                    for j in 0..n {
                        let x = [Some(&table[i][j]), table[i].get(j + d)]
                            .iter()
                            .flat_map(|&k| k)
                            .copied()
                            .min_by_key(|&k| (&seq[k], k))
                            .unwrap();
                        table[i + 1][j] = x;
                    }
                    d *= 2;
                }
                table
            },
            seq,
        }
    }
    /// Range min-position query にお答えします。
    ///
    /// `range` が空区間の場合は `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use rmq::SparseTable;
    /// let sparse_table = SparseTable::from_vec(vec![4, 5, 1]);
    ///
    /// assert_eq!(sparse_table.query(1..1), None);
    /// assert_eq!(sparse_table.query(1..0), None);
    /// assert_eq!(sparse_table.query(..), Some(2));
    /// assert_eq!(sparse_table.query(0..2), Some(0));
    /// ```
    pub fn query(&self, range: impl RangeBounds<usize>) -> Option<usize> {
        let (start, end) = get_start_and_end(self.seq.len(), &range);
        if start >= end {
            None
        } else {
            let i = (end - start).lg_usize_unchecked();
            [
                Some(self.table[i][start]),
                self.table[i].get(end - i.pow_of_two()).copied(),
            ]
            .iter()
            .flatten()
            .copied()
            .min_by_key(|&k| (&self.seq[k], k))
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Prec ////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// ±1 - property min-position を前計算します。
///
/// # Concepts
///
/// ±1-property を満たす、len - 1 で終わる長さ len の数列を辞書順の逆でエンコードしましょう。
///
/// このような列の部分列を指定されたときに、最小位置（のうち、最も左のもの、以下省略します。）を答えてくれます。
///
/// # Precalculation
///
/// ±1-property を満たす、`len - 1` で始まる長さ `len` の数列をすべて生成して、
/// そのすべての空でない prefix に対し、その最小の位置（のうち、最も左のもの）を計算します。
///
/// `len == 0` のときには、内部空 `Vec` を一つだけ持つ `Vec` を保持します。
/// これは空配列の長さ `0` 前計算です。
///
/// # Query
///
/// 数列番号を bit shift して、前計算済みのものに帰着します。
/// すると数列の後ろのほうが `0` 埋めされるのですが、
/// これは増加列に対応しますから、よいです。
///
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Prec {
    len: usize,
    table: Vec<Vec<usize>>,
}

impl Prec {
    /// 長さを指定して構築します。
    /// ```
    /// rmq::Prec::with_len(3);
    /// ```
    pub fn with_len(len: usize) -> Self {
        Self {
            len,
            table: if len == 0 {
                vec![vec![]]
            } else {
                let mut ans = vec![vec![0; len]; (len - 1).pow_of_two()];
                let mut a: Vec<usize> = (0..len).collect();
                for ans in ans.iter_mut() {
                    // 累積 min-position を計算していきます。
                    ans[0] = 0;
                    for i in 1..len {
                        let j = ans[i - 1];
                        ans[i] = if a[j] <= a[i] { j } else { i };
                    }

                    // a を次のイテレーションで使うものに変えます。
                    // もっとも左の Pos を Neg に変えて、それより前をすべて Pos に変えます。
                    if let Some(s) = (0..len - 1).find(|&i| a[i] < a[i + 1]) {
                        a[s] = a[s + 1] + 1;
                        (0..s).rev().for_each(|i| a[i] = a[i + 1] - 1);
                    }
                }
                ans
            },
        }
    }

    /// Min-position クエリにお答えします。
    ///
    /// `range` が空のときには `None` を返します。
    ///
    /// ```
    /// use rmq::Prec;
    /// let result = Prec::with_len(3);
    ///
    /// assert_eq!(result.query(1, 0..0), None);
    /// assert_eq!(result.query(1, 1..0), None);
    /// assert_eq!(result.query(1, 0..1), Some(0));
    /// assert_eq!(result.query(1, 1..2), Some(1));
    /// assert_eq!(result.query(1, 2..3), Some(2));
    /// assert_eq!(result.query(1, 0..2), Some(1));
    /// assert_eq!(result.query(1, 1..3), Some(1));
    /// assert_eq!(result.query(1, 2..3), Some(2));
    /// ```
    ///
    pub fn query(&self, seq_id: usize, range: impl RangeBounds<usize>) -> Option<usize> {
        let (start, end) = get_start_and_end(self.len, &range);
        if start >= end {
            None
        } else {
            Some(start + self.table[seq_id >> start][end - start - 1])
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Range utils  ////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

#[inline]
fn get_start_and_end(len: usize, range: &impl RangeBounds<usize>) -> (usize, usize) {
    (
        match range.start_bound() {
            Bound::Excluded(x) => x - 1,
            Bound::Included(x) => *x,
            Bound::Unbounded => 0,
        },
        match range.end_bound() {
            Bound::Excluded(x) => *x,
            Bound::Included(x) => x + 1,
            Bound::Unbounded => len,
        },
    )
}

////////////////////////////////////////////////////////////////////////////////
// construct_seq_from_seq_id ///////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
/// 与えられた `len`, `seq_id` に対応する数列を構成します。
///
/// # Examples
///
/// ```
/// use rmq::construct_seq_from_seq_id;
/// assert_eq!(construct_seq_from_seq_id(3, 0), vec![0, 1, 2]);
/// assert_eq!(construct_seq_from_seq_id(3, 1), vec![2, 1, 2]);
/// assert_eq!(construct_seq_from_seq_id(3, 2), vec![2, 3, 2]);
/// assert_eq!(construct_seq_from_seq_id(3, 3), vec![4, 3, 2]);
/// ```
pub fn construct_seq_from_seq_id(len: usize, seq_id: usize) -> Vec<usize> {
    assert!(seq_id < len.pow_of_two());
    let mut ans = vec![2 * len; len]; // あとで調整するので、とりあえず大きめの値にしておきます。`
    let mut x = seq_id;
    for i in 0..len - 1 {
        ans[i + 1] = if x % 2 == 0 { ans[i] + 1 } else { ans[i] - 1 };
        x /= 2;
    }
    let diff = ans[len - 1] - (len - 1);
    ans.iter_mut().for_each(|x| *x -= diff);
    ans
}
#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! verify_min_element {
        ($result:expr, $seq:ident [$l:expr;$r:expr]) => {
            let expected = ($l..$r).min_by_key(|&i| ($seq[i], i));
            assert_eq!(
                $result,
                expected,
                "seq = {seq:?}, range = {range:?}",
                seq = $seq,
                range = $l..$r
            );
        };
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Prec ////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test_prec() {
        for len in 1..8 {
            let prec = Prec::with_len(len);
            for seq_id in 0..(len - 1).pow_of_two() {
                let seq = construct_seq_from_seq_id(len, seq_id);
                for l in 0..=len {
                    for r in l..=len {
                        let result = prec.query(seq_id, l..r);
                        verify_min_element!(result, seq[l;r]);
                    }
                }
            }
        }

        // empty
        let prec = Prec::with_len(0);
        assert_eq!(prec.query(0, 0..0), None);
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Compound Table //////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test_compound_table() {
        for len in 1..8 {
            for seq_id in 0..(len - 1).pow_of_two() {
                let seq = construct_seq_from_seq_id(len, seq_id);
                let compound_table = CompoundTable::from_vec(seq.clone());
                for l in 0..=len {
                    for r in l..=len {
                        let result = compound_table.query(l..r);
                        verify_min_element!(result, seq[l;r]);
                    }
                }
            }
        }

        // empty
        let compound_table = CompoundTable::from_vec(vec![]);
        assert_eq!(compound_table.query(0..0), None);
    }

    ////////////////////////////////////////////////////////////////////////////////
    // SparseTable /////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test_sparse_table_pm1() {
        for len in 1..8 {
            for seq_id in 0..(len - 1).pow_of_two() {
                let seq = construct_seq_from_seq_id(len, seq_id);
                let sparse_table = SparseTable::from_vec(seq.clone());
                for l in 0..=len {
                    for r in l..=len {
                        let result = sparse_table.query(l..r);
                        verify_min_element!(result, seq[l;r]);
                    }
                }
            }
        }

        // empty
        let sparse_table = SparseTable::from_vec(Vec::<usize>::new());
        assert_eq!(sparse_table.query(0..0), None);
    }

    #[test]
    fn test_sparse_table_permutations() {
        fn next_permutation(seq: &mut [usize]) -> bool {
            if seq.is_empty() {
                false
            } else {
                if let Some(s) = (0..seq.len() - 1).rfind(|&s| seq[s] < seq[s + 1]) {
                    seq[s + 1..].reverse();
                    let t = (s + 1..).find(|&t| seq[s] < seq[t]).unwrap();
                    seq.swap(s, t);
                    true
                } else {
                    false
                }
            }
        }
        for len in 0..8 {
            let mut seq: Vec<_> = (0..len).collect();
            loop {
                let sparse_table = SparseTable::from_vec(seq.clone());
                for l in 0..=len {
                    for r in l..=len {
                        let result = sparse_table.query(l..r);
                        verify_min_element!(result, seq[l;r]);
                    }
                }
                if !next_permutation(seq.as_mut_slice()) {
                    break;
                }
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // LeastCommonAncestor /////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test_least_common_ancestor() {
        fn next_parent_pointers(seq: &mut [usize]) -> bool {
            if let Some(s) = (1..seq.len()).rfind(|&i| seq[i] != 0) {
                seq[s] = 0;
                (s + 1..seq.len()).for_each(|i| seq[i] = i - 1);
                true
            } else {
                false
            }
        }
        fn construct_tree_from_parent_pointers(seq: &[usize]) -> Vec<Vec<usize>> {
            let mut tree = vec![vec![]; seq.len() + 1];
            for (i, p) in seq.iter().enumerate().map(|(i, &p)| (i + 1, p)) {
                tree[i].push(p);
                tree[p].push(i);
            }
            tree
        }

        fn brute_force_least_common_ancestor(
            root: usize,
            u: usize,
            v: usize,
            tree: &[Vec<usize>],
        ) -> usize {
            #[derive(Debug, Clone, Eq, PartialEq)]
            struct Env<'a> {
                parent: Vec<usize>,
                tree: &'a [Vec<usize>],
            }
            let mut env = Env {
                parent: vec![0; tree.len()],
                tree,
            };

            fn dfs(x: usize, p: usize, env: &mut Env) {
                env.parent[x] = p;
                for y in env.tree[x].iter().copied().filter(|&y| y != p) {
                    dfs(y, x, env);
                }
            }
            dfs(root, root, &mut env);

            fn construct_ancestors_array(u: usize, env: &Env) -> Vec<usize> {
                let mut ans = vec![u];
                loop {
                    let x = *ans.last().unwrap();
                    let p = env.parent[x];
                    if x == p {
                        break;
                    }
                    ans.push(p);
                }
                ans
            }
            *construct_ancestors_array(u, &env)
                .iter()
                .rev()
                .zip(construct_ancestors_array(v, &env).iter().rev())
                .rfind(|(&x, &y)| x == y)
                .unwrap()
                .0
        }

        for len in 1..8 {
            let mut seq: Vec<_> = (0..len - 1).collect();
            loop {
                let tree = construct_tree_from_parent_pointers(&seq);
                for root in 0..len {
                    let lca = LeastCommonAncestor::from_tree(root, &tree);
                    for u in 0..len {
                        for v in 0..len {
                            let result = lca.query(u, v);
                            let expected = brute_force_least_common_ancestor(root, u, v, &tree);
                            assert_eq!(
                                result, expected,
                                "tree = {:?}, root = {}, u = {}, v = {}",
                                &tree, root, u, v
                            );
                        }
                    }
                }
                if !next_parent_pointers(seq.as_mut_slice()) {
                    break;
                }
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Cartesian Tree //////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test_cartesian_tree() {
        fn next_seq(seq: &mut [usize]) -> bool {
            if let Some((s, _)) = seq
                .iter()
                .copied()
                .enumerate()
                .rfind(|&(_, x)| x != seq.len() - 1)
            {
                seq[s] += 1;
                seq[s + 1..].iter_mut().for_each(|x| *x = 0);
                true
            } else {
                false
            }
        }
        fn brute_cartesian_parent(i: usize, seq: &[usize]) -> usize {
            [
                seq[..i]
                    .iter()
                    .copied()
                    .enumerate()
                    .rfind(|&(_, y)| y <= seq[i]),
                seq[i + 1..]
                    .iter()
                    .copied()
                    .enumerate()
                    .find(|&(_, y)| y < seq[i])
                    .map(|(d, y)| (i + 1 + d, y)),
            ]
            .iter()
            .flatten()
            .copied()
            .max_by_key(|&(j, y)| (y, j))
            .map(|(j, _)| j)
            .unwrap_or(i)
        }
        for len in 0..7 {
            let mut seq = vec![0; len];
            loop {
                let cartesian_tree = construct_cartesian_tree(&seq);
                for i in 0..seq.len() {
                    let result = cartesian_tree[i];
                    let expected = brute_cartesian_parent(i, &seq);
                    assert_eq!(result, expected, "seq = {:?}, i = {}", &seq, i);
                }
                if !next_seq(&mut seq) {
                    break;
                }
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // FastMinimum ////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test_fast_minimum_pm1() {
        for len in 1..8 {
            for seq_id in 0..(len - 1).pow_of_two() {
                let seq = construct_seq_from_seq_id(len, seq_id);
                let fast_minimum = FastMinimum::build(&seq);
                for l in 0..=len {
                    for r in l..=len {
                        let result = fast_minimum.query(l..r);
                        verify_min_element!(result, seq[l;r]);
                    }
                }
            }
        }

        // empty
        let fast_minimum = FastMinimum::build(&Vec::<usize>::new());
        assert_eq!(fast_minimum.query(0..0), None);
    }
}
