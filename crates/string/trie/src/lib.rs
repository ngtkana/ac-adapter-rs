//! A set and map data structure on trie.
//!
//! They are set and map datastructure with an extra operation `for_each_prefix`. We can visit all
//! the preficies of a key, receiving the corresponding node again as a trie.

/// Tries here have the fixed branching number 26.
pub const DEGREE: usize = 26;

mod trie_map;
mod trie_set;

pub use trie_map::TrieMap;
pub use trie_set::TrieSet;
