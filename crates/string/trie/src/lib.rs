//! ASCII 文字列を格納します。

/// `TrieSet`, `TrieMap` の分岐数は 26 固定です。
pub const DEGREE: usize = 26;

mod trie_map;
mod trie_set;

pub use trie_map::TrieMap;
pub use trie_set::TrieSet;
