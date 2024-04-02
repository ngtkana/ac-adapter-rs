(function() {var implementors = {
"accum":[["impl&lt;'a, T, F, I&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"accum/struct.Skipped.html\" title=\"struct accum::Skipped\">Skipped</a>&lt;'a, T, F, I&gt;<span class=\"where fmt-newline\">where\n    F: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/ops/function/trait.FnMut.html\" title=\"trait core::ops::function::FnMut\">FnMut</a>(<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.70.0/std/primitive.reference.html\">&amp;T</a>, <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.70.0/std/primitive.reference.html\">&amp;T</a>) -&gt; T,\n    I: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/ops/function/trait.FnMut.html\" title=\"trait core::ops::function::FnMut\">FnMut</a>() -&gt; T,</span>"]],
"avl_tree":[["impl&lt;'a, T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"avl_tree/struct.Iter.html\" title=\"struct avl_tree::Iter\">Iter</a>&lt;'a, T&gt;"],["impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"avl_tree/struct.IntoIter.html\" title=\"struct avl_tree::IntoIter\">IntoIter</a>&lt;T&gt;"]],
"bitutils":[["impl&lt;T: <a class=\"trait\" href=\"bitutils/trait.Unsigned.html\" title=\"trait bitutils::Unsigned\">Unsigned</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"bitutils/struct.Subsets.html\" title=\"struct bitutils::Subsets\">Subsets</a>&lt;T&gt;"],["impl&lt;T: <a class=\"trait\" href=\"bitutils/trait.Unsigned.html\" title=\"trait bitutils::Unsigned\">Unsigned</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"bitutils/struct.Combinations.html\" title=\"struct bitutils::Combinations\">Combinations</a>&lt;T&gt;"]],
"bitvec":[["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"bitvec/struct.Iter.html\" title=\"struct bitvec::Iter\">Iter</a>&lt;'a&gt;"]],
"erato":[["impl&lt;'a, T: <a class=\"trait\" href=\"erato/trait.Int.html\" title=\"trait erato::Int\">Int</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"erato/struct.PrimeFactorsByLookup.html\" title=\"struct erato::PrimeFactorsByLookup\">PrimeFactorsByLookup</a>&lt;'a, T&gt;"],["impl&lt;'a, T: <a class=\"trait\" href=\"erato/trait.Int.html\" title=\"trait erato::Int\">Int</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"erato/struct.PrimeFactorsByTrialDivision.html\" title=\"struct erato::PrimeFactorsByTrialDivision\">PrimeFactorsByTrialDivision</a>&lt;'a, T&gt;"],["impl&lt;'a, S: SieveKind, T: <a class=\"trait\" href=\"erato/trait.Int.html\" title=\"trait erato::Int\">Int</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"erato/struct.PrimeNumbers.html\" title=\"struct erato::PrimeNumbers\">PrimeNumbers</a>&lt;'a, S, T&gt;"],["impl&lt;T: <a class=\"trait\" href=\"erato/trait.Int.html\" title=\"trait erato::Int\">Int</a>, P: <a class=\"trait\" href=\"erato/trait.PrimeFactors.html\" title=\"trait erato::PrimeFactors\">PrimeFactors</a>&lt;T&gt;&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"erato/struct.Unique.html\" title=\"struct erato::Unique\">Unique</a>&lt;T, P&gt;"],["impl&lt;T: <a class=\"trait\" href=\"erato/trait.Int.html\" title=\"trait erato::Int\">Int</a>, P: <a class=\"trait\" href=\"erato/trait.PrimeFactors.html\" title=\"trait erato::PrimeFactors\">PrimeFactors</a>&lt;T&gt;&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"erato/struct.Rle.html\" title=\"struct erato::Rle\">Rle</a>&lt;T, P&gt;"]],
"filter_position":[["impl&lt;I: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>, F: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/ops/function/trait.Fn.html\" title=\"trait core::ops::function::Fn\">Fn</a>(I::<a class=\"associatedtype\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html#associatedtype.Item\" title=\"type core::iter::traits::iterator::Iterator::Item\">Item</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.70.0/std/primitive.bool.html\">bool</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"filter_position/struct.FilterPosition.html\" title=\"struct filter_position::FilterPosition\">FilterPosition</a>&lt;I, F&gt;"]],
"gridnei":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"gridnei/struct.Grid8.html\" title=\"struct gridnei::Grid8\">Grid8</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"gridnei/struct.Grid3.html\" title=\"struct gridnei::Grid3\">Grid3</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"gridnei/struct.Grid7.html\" title=\"struct gridnei::Grid7\">Grid7</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"gridnei/struct.Grid1.html\" title=\"struct gridnei::Grid1\">Grid1</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"gridnei/struct.Grid0.html\" title=\"struct gridnei::Grid0\">Grid0</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"gridnei/struct.Grid6.html\" title=\"struct gridnei::Grid6\">Grid6</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"gridnei/struct.Grid2.html\" title=\"struct gridnei::Grid2\">Grid2</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"gridnei/struct.Grid5.html\" title=\"struct gridnei::Grid5\">Grid5</a>"],["impl&lt;I: <a class=\"trait\" href=\"gridnei/trait.GridIterator.html\" title=\"trait gridnei::GridIterator\">GridIterator</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"gridnei/struct.Encode.html\" title=\"struct gridnei::Encode\">Encode</a>&lt;I&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"gridnei/struct.Grid4.html\" title=\"struct gridnei::Grid4\">Grid4</a>"]],
"hld":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"hld/struct.IterE.html\" title=\"struct hld::IterE\">IterE</a>&lt;'_&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"hld/struct.IterV.html\" title=\"struct hld::IterV\">IterV</a>&lt;'_&gt;"]],
"itermore":[["impl&lt;I: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"itermore/struct.OpenPrefixSum.html\" title=\"struct itermore::OpenPrefixSum\">OpenPrefixSum</a>&lt;I&gt;<span class=\"where fmt-newline\">where\n    I::<a class=\"associatedtype\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html#associatedtype.Item\" title=\"type core::iter::traits::iterator::Iterator::Item\">Item</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/ops/arith/trait.AddAssign.html\" title=\"trait core::ops::arith::AddAssign\">AddAssign</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a>,</span>"],["impl&lt;I: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"itermore/struct.ClosedPrefixSum.html\" title=\"struct itermore::ClosedPrefixSum\">ClosedPrefixSum</a>&lt;I&gt;<span class=\"where fmt-newline\">where\n    I::<a class=\"associatedtype\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html#associatedtype.Item\" title=\"type core::iter::traits::iterator::Iterator::Item\">Item</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/ops/arith/trait.AddAssign.html\" title=\"trait core::ops::arith::AddAssign\">AddAssign</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a>,</span>"],["impl&lt;I: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"itermore/struct.MaxIncrease.html\" title=\"struct itermore::MaxIncrease\">MaxIncrease</a>&lt;I&gt;<span class=\"where fmt-newline\">where\n    I::<a class=\"associatedtype\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html#associatedtype.Item\" title=\"type core::iter::traits::iterator::Iterator::Item\">Item</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/ops/arith/trait.Sub.html\" title=\"trait core::ops::arith::Sub\">Sub</a>&lt;Output = I::<a class=\"associatedtype\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html#associatedtype.Item\" title=\"type core::iter::traits::iterator::Iterator::Item\">Item</a>&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/cmp/trait.Ord.html\" title=\"trait core::cmp::Ord\">Ord</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a>,</span>"],["impl&lt;I: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"itermore/struct.MaxDecrease.html\" title=\"struct itermore::MaxDecrease\">MaxDecrease</a>&lt;I&gt;<span class=\"where fmt-newline\">where\n    I::<a class=\"associatedtype\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html#associatedtype.Item\" title=\"type core::iter::traits::iterator::Iterator::Item\">Item</a>: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/ops/arith/trait.Sub.html\" title=\"trait core::ops::arith::Sub\">Sub</a>&lt;Output = I::<a class=\"associatedtype\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html#associatedtype.Item\" title=\"type core::iter::traits::iterator::Iterator::Item\">Item</a>&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/cmp/trait.Ord.html\" title=\"trait core::cmp::Ord\">Ord</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a>,</span>"]],
"poly":[["impl&lt;T, A, B&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"poly/struct.PolySub.html\" title=\"struct poly::PolySub\">PolySub</a>&lt;T, A, B&gt;<span class=\"where fmt-newline\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/ops/arith/trait.Sub.html\" title=\"trait core::ops::arith::Sub\">Sub</a>&lt;Output = T&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/ops/arith/trait.Neg.html\" title=\"trait core::ops::arith::Neg\">Neg</a>&lt;Output = T&gt;,\n    A: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>&lt;Item = T&gt;,\n    B: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>&lt;Item = T&gt;,</span>"],["impl&lt;T, A, B&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"poly/struct.PolyAdd.html\" title=\"struct poly::PolyAdd\">PolyAdd</a>&lt;T, A, B&gt;<span class=\"where fmt-newline\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/ops/arith/trait.Add.html\" title=\"trait core::ops::arith::Add\">Add</a>&lt;Output = T&gt;,\n    A: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>&lt;Item = T&gt;,\n    B: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a>&lt;Item = T&gt;,</span>"]],
"rbtree":[["impl&lt;'a, T, O: <a class=\"trait\" href=\"rbtree/trait.Op.html\" title=\"trait rbtree::Op\">Op</a>&lt;Value = T&gt;&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"rbtree/struct.Iter.html\" title=\"struct rbtree::Iter\">Iter</a>&lt;'a, T, O&gt;"]],
"splay_tree":[["impl&lt;'a, O: <a class=\"trait\" href=\"splay_tree/trait.LazyOps.html\" title=\"trait splay_tree::LazyOps\">LazyOps</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"splay_tree/struct.Iter.html\" title=\"struct splay_tree::Iter\">Iter</a>&lt;'a, O&gt;"]],
"trial":[["impl&lt;T: <a class=\"trait\" href=\"trial/trait.Value.html\" title=\"trait trial::Value\">Value</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"trial/struct.PrimeFactorsRle.html\" title=\"struct trial::PrimeFactorsRle\">PrimeFactorsRle</a>&lt;T&gt;"],["impl&lt;T: <a class=\"trait\" href=\"trial/trait.Value.html\" title=\"trait trial::Value\">Value</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"trial/struct.PrimeFactors.html\" title=\"struct trial::PrimeFactors\">PrimeFactors</a>&lt;T&gt;"],["impl&lt;T: <a class=\"trait\" href=\"trial/trait.Value.html\" title=\"trait trial::Value\">Value</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"trial/struct.Divisors.html\" title=\"struct trial::Divisors\">Divisors</a>&lt;T&gt;"]],
"uf_checklist":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"uf_checklist/struct.Iter.html\" title=\"struct uf_checklist::Iter\">Iter</a>&lt;'_&gt;"]],
"wavelet_matrix":[["impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.70.0/core/iter/traits/iterator/trait.Iterator.html\" title=\"trait core::iter::traits::iterator::Iterator\">Iterator</a> for <a class=\"struct\" href=\"wavelet_matrix/struct.Spans.html\" title=\"struct wavelet_matrix::Spans\">Spans</a>&lt;'a&gt;"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()