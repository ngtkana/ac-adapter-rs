//! キー列（$0, \ldots, 25$ の値の列）を接頭辞で共有するトライ木による集合・辞書。
//!
//! 各ノードが $26$ 分木の子を持ち、キーの各要素を添字として子を辿ることでキーを表現する。
//! 共通の接頭辞を持つキーはノードを共有するため、途中のノードそのものが「その接頭辞を持つ
//! 部分集合」を表すトライとなる。[`TrieMap::for_each_prefix`] はこれを利用して、
//! あるキーのすべての接頭辞に対応するノードを根から順に訪問する。
//!
//! # 仕様
//!
//! - [`TrieMap`][]: キー（`impl IntoIterator<Item = usize>`、各要素は $[0, 26)$）から値への辞書
//! - [`TrieSet`][]: `TrieMap<()>` を包んだ集合
//!
//! # 例
//!
//! ```
//! use trie::TrieMap;
//!
//! let mut map = TrieMap::new();
//! map.insert([1, 2, 3], "a");
//! assert_eq!(map.get([1, 2, 3]), Some(&"a"));
//! assert_eq!(map.get([1, 2]), None);
//! ```
//!
//! # 計算量
//!
//! キー長を $k$ として、挿入・削除・取得はいずれも $O(k)$

/// トライの分岐数（キーの各要素が取り得る値の範囲は $[0, \text{DEGREE})$）。
pub const DEGREE: usize = 26;

mod trie_map;
mod trie_set;

pub use trie_map::TrieMap;
pub use trie_set::TrieSet;
