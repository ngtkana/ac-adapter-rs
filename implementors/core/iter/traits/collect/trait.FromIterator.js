(function() {var implementors = {
"avl_tree":[["impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;T&gt; for <a class=\"struct\" href=\"avl_tree/struct.AvlTree.html\" title=\"struct avl_tree::AvlTree\">AvlTree</a>&lt;T&gt;"]],
"bitvec":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.70.0/std/primitive.bool.html\">bool</a>&gt; for <a class=\"struct\" href=\"bitvec/struct.BitVec.html\" title=\"struct bitvec::BitVec\">BitVec</a>"]],
"dual_segtree":[["impl&lt;O: <a class=\"trait\" href=\"dual_segtree/trait.Ops.html\" title=\"trait dual_segtree::Ops\">Ops</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;&lt;O as <a class=\"trait\" href=\"dual_segtree/trait.Ops.html\" title=\"trait dual_segtree::Ops\">Ops</a>&gt;::<a class=\"associatedtype\" href=\"dual_segtree/trait.Ops.html#associatedtype.Value\" title=\"type dual_segtree::Ops::Value\">Value</a>&gt; for <a class=\"struct\" href=\"dual_segtree/struct.DualSegtree.html\" title=\"struct dual_segtree::DualSegtree\">DualSegtree</a>&lt;O&gt;"]],
"heap_tricks":[["impl&lt;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/cmp/trait.Ord.html\" title=\"trait core::cmp::Ord\">Ord</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/hash/trait.Hash.html\" title=\"trait core::hash::Hash\">Hash</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;T&gt; for <a class=\"struct\" href=\"heap_tricks/struct.RemovableHeap.html\" title=\"struct heap_tricks::RemovableHeap\">RemovableHeap</a>&lt;T&gt;"]],
"lazy_segtree":[["impl&lt;O: <a class=\"trait\" href=\"lazy_segtree/trait.Op.html\" title=\"trait lazy_segtree::Op\">Op</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;&lt;O as <a class=\"trait\" href=\"lazy_segtree/trait.Op.html\" title=\"trait lazy_segtree::Op\">Op</a>&gt;::<a class=\"associatedtype\" href=\"lazy_segtree/trait.Op.html#associatedtype.Value\" title=\"type lazy_segtree::Op::Value\">Value</a>&gt; for <a class=\"struct\" href=\"lazy_segtree/struct.LazySegtree.html\" title=\"struct lazy_segtree::LazySegtree\">LazySegtree</a>&lt;O&gt;<span class=\"where fmt-newline\">where\n    O::<a class=\"associatedtype\" href=\"lazy_segtree/trait.Op.html#associatedtype.Value\" title=\"type lazy_segtree::Op::Value\">Value</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,\n    O::<a class=\"associatedtype\" href=\"lazy_segtree/trait.Op.html#associatedtype.Operator\" title=\"type lazy_segtree::Op::Operator\">Operator</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,</span>"]],
"rb":[["impl&lt;O: <a class=\"trait\" href=\"rb/trait.Op.html\" title=\"trait rb::Op\">Op</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;&lt;O as <a class=\"trait\" href=\"rb/trait.Op.html\" title=\"trait rb::Op\">Op</a>&gt;::<a class=\"associatedtype\" href=\"rb/trait.Op.html#associatedtype.Value\" title=\"type rb::Op::Value\">Value</a>&gt; for <a class=\"struct\" href=\"rb/struct.Seg.html\" title=\"struct rb::Seg\">Seg</a>&lt;O&gt;"]],
"rbtree":[["impl&lt;A, O: <a class=\"trait\" href=\"rbtree/trait.Op.html\" title=\"trait rbtree::Op\">Op</a>&lt;Value = A&gt;&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;A&gt; for <a class=\"struct\" href=\"rbtree/struct.RbTree.html\" title=\"struct rbtree::RbTree\">RbTree</a>&lt;A, O&gt;"]],
"segtree":[["impl&lt;K, O: <a class=\"trait\" href=\"segtree/trait.Op.html\" title=\"trait segtree::Op\">Op</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;(K, &lt;O as <a class=\"trait\" href=\"segtree/trait.Op.html\" title=\"trait segtree::Op\">Op</a>&gt;::<a class=\"associatedtype\" href=\"segtree/trait.Op.html#associatedtype.Value\" title=\"type segtree::Op::Value\">Value</a>)&gt; for <a class=\"struct\" href=\"segtree/struct.SparseSegtree.html\" title=\"struct segtree::SparseSegtree\">SparseSegtree</a>&lt;K, O&gt;<span class=\"where fmt-newline\">where\n    K: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/cmp/trait.Ord.html\" title=\"trait core::cmp::Ord\">Ord</a>,\n    O::<a class=\"associatedtype\" href=\"segtree/trait.Op.html#associatedtype.Value\" title=\"type segtree::Op::Value\">Value</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,</span>"],["impl&lt;O: <a class=\"trait\" href=\"segtree/trait.Op.html\" title=\"trait segtree::Op\">Op</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;&lt;O as <a class=\"trait\" href=\"segtree/trait.Op.html\" title=\"trait segtree::Op\">Op</a>&gt;::<a class=\"associatedtype\" href=\"segtree/trait.Op.html#associatedtype.Value\" title=\"type segtree::Op::Value\">Value</a>&gt; for <a class=\"struct\" href=\"segtree/struct.Segtree.html\" title=\"struct segtree::Segtree\">Segtree</a>&lt;O&gt;<span class=\"where fmt-newline\">where\n    O::<a class=\"associatedtype\" href=\"segtree/trait.Op.html#associatedtype.Value\" title=\"type segtree::Op::Value\">Value</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,</span>"],["impl&lt;K, L, O: <a class=\"trait\" href=\"segtree/trait.Op.html\" title=\"trait segtree::Op\">Op</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;(K, L, &lt;O as <a class=\"trait\" href=\"segtree/trait.Op.html\" title=\"trait segtree::Op\">Op</a>&gt;::<a class=\"associatedtype\" href=\"segtree/trait.Op.html#associatedtype.Value\" title=\"type segtree::Op::Value\">Value</a>)&gt; for <a class=\"struct\" href=\"segtree/struct.Sparse2dSegtree.html\" title=\"struct segtree::Sparse2dSegtree\">Sparse2dSegtree</a>&lt;K, L, O&gt;<span class=\"where fmt-newline\">where\n    K: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/cmp/trait.Ord.html\" title=\"trait core::cmp::Ord\">Ord</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,\n    L: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/cmp/trait.Ord.html\" title=\"trait core::cmp::Ord\">Ord</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,\n    O::<a class=\"associatedtype\" href=\"segtree/trait.Op.html#associatedtype.Value\" title=\"type segtree::Op::Value\">Value</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,</span>"]],
"skew_heap":[["impl&lt;A: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/cmp/trait.Ord.html\" title=\"trait core::cmp::Ord\">Ord</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;A&gt; for <a class=\"struct\" href=\"skew_heap/struct.SkewHeap.html\" title=\"struct skew_heap::SkewHeap\">SkewHeap</a>&lt;A&gt;"]],
"sparse_table":[["impl&lt;O: <a class=\"trait\" href=\"sparse_table/trait.Op.html\" title=\"trait sparse_table::Op\">Op</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;&lt;O as <a class=\"trait\" href=\"sparse_table/trait.Op.html\" title=\"trait sparse_table::Op\">Op</a>&gt;::<a class=\"associatedtype\" href=\"sparse_table/trait.Op.html#associatedtype.Value\" title=\"type sparse_table::Op::Value\">Value</a>&gt; for <a class=\"struct\" href=\"sparse_table/struct.SparseTable.html\" title=\"struct sparse_table::SparseTable\">SparseTable</a>&lt;O&gt;"]],
"splay_tree":[["impl&lt;O: <a class=\"trait\" href=\"splay_tree/trait.LazyOps.html\" title=\"trait splay_tree::LazyOps\">LazyOps</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;&lt;O as <a class=\"trait\" href=\"splay_tree/trait.LazyOps.html\" title=\"trait splay_tree::LazyOps\">LazyOps</a>&gt;::<a class=\"associatedtype\" href=\"splay_tree/trait.LazyOps.html#associatedtype.Value\" title=\"type splay_tree::LazyOps::Value\">Value</a>&gt; for <a class=\"struct\" href=\"splay_tree/struct.SplayTree.html\" title=\"struct splay_tree::SplayTree\">SplayTree</a>&lt;O&gt;"]],
"suffix_sum":[["impl&lt;O: <a class=\"trait\" href=\"suffix_sum/trait.Op.html\" title=\"trait suffix_sum::Op\">Op</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;&lt;O as <a class=\"trait\" href=\"suffix_sum/trait.Op.html\" title=\"trait suffix_sum::Op\">Op</a>&gt;::<a class=\"associatedtype\" href=\"suffix_sum/trait.Op.html#associatedtype.Value\" title=\"type suffix_sum::Op::Value\">Value</a>&gt; for <a class=\"struct\" href=\"suffix_sum/struct.SuffixSum.html\" title=\"struct suffix_sum::SuffixSum\">SuffixSum</a>&lt;O&gt;"]],
"veb":[["impl&lt;V&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;(<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.70.0/std/primitive.usize.html\">usize</a>, V)&gt; for <a class=\"struct\" href=\"veb/struct.VebMap.html\" title=\"struct veb::VebMap\">VebMap</a>&lt;V&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.70.0/std/primitive.usize.html\">usize</a>&gt; for <a class=\"enum\" href=\"veb/enum.VebSet.html\" title=\"enum veb::VebSet\">VebSet</a>"]],
"wavelet_matrix":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.70.0/std/primitive.bool.html\">bool</a>&gt; for <a class=\"struct\" href=\"wavelet_matrix/struct.StaticBitVec.html\" title=\"struct wavelet_matrix::StaticBitVec\">StaticBitVec</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.70.0/std/primitive.usize.html\">usize</a>&gt; for <a class=\"struct\" href=\"wavelet_matrix/struct.WaveletMatrix.html\" title=\"struct wavelet_matrix::WaveletMatrix\">WaveletMatrix</a>"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()