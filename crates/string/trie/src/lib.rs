//! ASCII 文字列を格納します。

const DEGREE: usize = 26;

#[derive(Clone, Debug, PartialEq, Default)]
pub struct Trie(Option<Box<Node>>);
impl Trie {
    pub fn new() -> Self {
        Self(None)
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }
    pub fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |node| node.len)
    }
    /// 普通に挿入します。
    pub fn insert(&mut self, iter: impl Iterator<Item = usize>) {
        self.inserting_for_each(iter, |_| {})
    }
    /// 挿入しながら、すべての n + 1 個ある prefix をすべて、子孫を挿入する前に訪問です。
    pub fn inserting_for_each(
        &mut self,
        mut iter: impl Iterator<Item = usize>,
        mut callback: impl FnMut(&Trie),
    ) {
        callback(self);
        let me = self.0.get_or_insert_with(|| Box::new(Node::new()));
        let next = iter.next();
        if let Some(next) = next {
            me.child[next].inserting_for_each(iter, callback);
        } else {
            me.len += 1;
            me.cnt += 1;
        }
    }
    /// 消去します。もともとあるものを消去できれば `true`、もともと存在しなければ `false` です。
    pub fn delete(&mut self, mut iter: impl Iterator<Item = usize>) -> bool {
        let next = iter.next();
        if let Some(next) = next {
            self.0
                .as_mut()
                .map_or(false, |me| me.child[next].delete(iter))
        } else if let Some(mut node) = self.0.take() {
            node.len -= 1;
            node.cnt -= 1;
            if node.cnt != 0 {
                self.0 = Some(node);
            }
            true
        } else {
            false
        }
    }
    /// ぴったり一致するものの個数を数えます。
    pub fn count_exact(&self, iter: impl Iterator<Item = usize>) -> usize {
        self.__get(iter).map_or(0, |node| node.cnt)
    }
    /// prefix になっているものを数えます。
    pub fn count_prefix(&self, iter: impl Iterator<Item = usize>) -> usize {
        self.__get(iter).map_or(0, |node| node.len)
    }
    fn __get(&self, mut iter: impl Iterator<Item = usize>) -> Option<&Node> {
        let next = iter.next();
        if let Some(next) = next {
            if let Some(me) = self.0.as_ref() {
                me.child[next].__get(iter)
            } else {
                None
            }
        } else {
            self.0.as_deref()
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Node {
    len: usize,
    cnt: usize,
    child: [Trie; DEGREE],
}
impl Default for Node {
    fn default() -> Self {
        Self::new()
    }
}
impl Node {
    pub fn new() -> Self {
        Self {
            len: 0,
            cnt: 0,
            child: <[Trie; DEGREE]>::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Trie;

    // TODO
}
