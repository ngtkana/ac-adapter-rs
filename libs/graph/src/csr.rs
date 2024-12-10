use std::fmt::Debug;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::Index;
use std::ops::IndexMut;

/// Compressed Sparse Row format
///
/// # Notation
///
/// - $X = [x_0, x_1, \dots, x_{n-1}]$: `data`
/// - $S = [s_0, s_1, \dots, s_{m}]$: `boundaries`
///
/// # Invariants
///
/// - $0 = s_0 \leq s_1 \leq \dots \leq s_m = n$
///
/// # Semantics
///
/// This struct represents a list of lists $A$ of elements of type `T`.
///
/// $$
/// A_{i, j} = X[s_i + j]
/// $$
///
pub struct Csr<T> {
    /// $X = [x_0, x_1, \dots, x_{n-1}]$
    pub data: Vec<T>,
    /// $S = [s_0, s_1, \dots, s_{m}]$
    pub boundary: Vec<usize>,
}

impl<T> Csr<T> {
    /// Create a CSR corrsponding to $A = [\ ]$.
    ///
    /// # Example
    ///
    /// ```
    /// use graph::Csr;
    /// let csr: Csr<usize> = Csr::new();
    /// assert!(csr.is_empty());
    /// ```
    pub fn new() -> Self {
        Csr {
            data: Vec::new(),
            boundary: vec![0],
        }
    }
    /// Create a CSR corrsponding to $A = [\ ]$ with preallocated memory.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let csr: Csr<usize> = Csr::with_capacity(10, 5);
    /// assert!(csr.is_empty());
    /// ```
    pub fn with_capacity(data_capacity: usize, sections_capacity: usize) -> Self {
        let data = Vec::with_capacity(data_capacity);
        let mut boundary = Vec::with_capacity(sections_capacity + 1);
        boundary.push(0);
        Csr { data, boundary }
    }
    /// Create a CSR from a list of sections.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let csr = Csr::from_sections(&[vec![1, 2, 3], vec![4, 5]]);
    /// assert_eq!(csr.section(0), &[1, 2, 3]);
    /// assert_eq!(csr.section(1), &[4, 5]);
    /// ```
    pub fn from_sections<A>(rows: &[A]) -> Self
    where
        A: AsRef<[T]>,
        T: Clone,
    {
        let mut csr = Csr::new();
        for row in rows {
            csr.push_section(row.as_ref());
        }
        csr
    }
    /// Get the $i$-th section $A_i$. Alias for `&self[i]`.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let csr = Csr::from_sections(&[vec![1, 2, 3], vec![4, 5]]);
    /// assert_eq!(csr.section(0), &[1, 2, 3]);
    /// ```
    pub fn section(&self, i: usize) -> &[T] {
        &self.data[self.boundary[i]..self.boundary[i + 1]]
    }
    /// Get the mutable $i$-th section $A_i$. Alias for `&mut self[i]`.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let mut csr = Csr::from_sections(&[vec![1, 2, 3], vec![4, 5]]);
    /// csr.section_mut(0)[0] = 42;
    /// assert_eq!(csr.section(0), &[42, 2, 3]);
    /// ```
    pub fn section_mut(&mut self, i: usize) -> &mut [T] {
        &mut self.data[self.boundary[i]..self.boundary[i + 1]]
    }
    /// Check if the CSR is empty. (i.e. $A = [\ ]$)
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let csr = Csr::<()>::new();
    /// assert!(csr.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.boundary.len() == 1
    }
    /// Get the number of sections $m = |A|$.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let csr = Csr::from_sections(&[vec![1, 2, 3], vec![4, 5]]);
    /// assert_eq!(csr.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.boundary.len() - 1
    }
    /// Get the total number of elements in $A$. (i.e. $\sum_{i=0}^{m-1} |A_i|$)
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let csr = Csr::from_sections(&[vec![1, 2, 3], vec![4, 5]]);
    /// assert_eq!(csr.flat_len(), 5);
    /// ```
    pub fn flat_len(&self) -> usize {
        self.data.len()
    }
    /// Get the mutable and extendable reference to the last section.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let mut csr = Csr::from_sections(&[vec![1, 2, 3], vec![4, 5]]);
    /// csr.last_mut().push(42);
    /// assert_eq!(csr.section(1), &[4, 5, 42]);
    /// ```
    pub fn last_mut(&mut self) -> LastMut<T> {
        LastMut { csr: self }
    }
    /// Push an empty section $A_m = [\ ]$.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let mut csr = Csr::<()>::new();
    /// csr.push_empty();
    /// assert_eq!(csr.section(0), &[]);
    /// ```
    pub fn push_empty(&mut self) {
        self.boundary.push(self.data.len());
    }
    /// Clone and push a section.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let mut csr = Csr::new();
    /// csr.push_section(&[1, 2, 3]);
    /// assert_eq!(csr.section(0), &[1, 2, 3]);
    /// ```
    pub fn push_section(&mut self, section: &[T])
    where
        T: Clone,
    {
        self.data.extend_from_slice(section);
        self.boundary.push(self.data.len());
    }
    /// Return an iterator over the sections.
    ///
    pub fn iter(&self) -> Iter<T> {
        Iter {
            data: &self.data,
            boundary: &self.boundary,
        }
    }
    /// Copies `self` into a new `Vec<Vec<T>>`.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let csr = Csr::from_sections(&[vec![1, 2, 3], vec![4, 5]]);
    /// assert_eq!(csr.to_vec(), vec![vec![1, 2, 3], vec![4, 5]]);
    /// ```
    pub fn to_vec(&self) -> Vec<Vec<T>>
    where
        T: Clone,
    {
        self.iter().map(<[T]>::to_vec).collect()
    }
}

/// Mutable and extendable reference to the last section.
pub struct LastMut<'a, T> {
    csr: &'a mut Csr<T>,
}
impl<'a, T> LastMut<'a, T> {
    /// Push an element to the last section.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let mut csr = Csr::from_sections(&[vec![1, 2, 3], vec![4, 5]]);
    /// csr.last_mut().push(42);
    /// assert_eq!(csr.section(1), &[4, 5, 42]);
    /// ```
    pub fn push(self, x: T) {
        self.csr.data.push(x);
        *self.csr.boundary.last_mut().unwrap() = self.csr.data.len();
    }
    /// Extend the last section with an iterator.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let mut csr = Csr::from_sections(&[vec![1, 2, 3], vec![4, 5]]);
    /// csr.last_mut().extend(vec![42, 43]);
    /// assert_eq!(csr.section(1), &[4, 5, 42, 43]);
    /// ```
    pub fn extend<I: IntoIterator<Item = T>>(self, iter: I) {
        self.csr.data.extend(iter);
        *self.csr.boundary.last_mut().unwrap() = self.csr.data.len();
    }

    /// Copy elements from a slice to the last section.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let mut csr = Csr::from_sections(&[vec![1, 2, 3], vec![4, 5]]);
    /// csr.last_mut().extend_from_slice(&[42, 43]);
    /// assert_eq!(csr.section(1), &[4, 5, 42, 43]);
    pub fn extend_from_slice(&mut self, slice: &[T])
    where
        T: Clone,
    {
        self.csr.data.extend_from_slice(slice);
        *self.csr.boundary.last_mut().unwrap() = self.csr.data.len();
    }
}
impl<T> Deref for LastMut<'_, T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        &self.csr.data[self.csr.boundary[self.csr.boundary.len() - 2]..]
    }
}
impl<T> DerefMut for LastMut<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.csr.data[self.csr.boundary[self.csr.boundary.len() - 2]..]
    }
}

impl<T, A> FromIterator<A> for Csr<T>
where
    A: IntoIterator<Item = T>,
{
    fn from_iter<I: IntoIterator<Item = A>>(iter: I) -> Self {
        let mut csr = Csr::new();
        for section in iter {
            csr.push_empty();
            for x in section {
                csr.last_mut().push(x);
            }
        }
        csr
    }
}

impl Csr<usize> {
    /// Create a CSR from a list of edges.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let csr = Csr::from_edges(3, &[(0, 1), (1, 2), (2, 0)]);
    /// assert_eq!(csr.to_vec(), vec![vec![1], vec![2], vec![0]]);
    /// ```
    pub fn from_edges(n: usize, edges: &[(usize, usize)]) -> Self {
        let mut csr = Csr {
            data: vec![usize::MAX; edges.len()],
            boundary: vec![0; n + 1],
        };
        for &(i, _) in edges {
            csr.boundary[i] += 1;
        }
        for i in 1..=n {
            csr.boundary[i] += csr.boundary[i - 1];
        }
        for &(i, j) in edges {
            csr.boundary[i] -= 1;
            csr.data[csr.boundary[i]] = j;
        }
        csr
    }
    /// Create CSRs of $G$ and $G^{\mathrm{op}}$ from a list of edges.
    ///
    /// # Example
    /// ```
    /// use graph::Csr;
    /// let (g, rg) = Csr::from_edges_and_rev(3, &[(0, 1), (1, 2), (2, 0)]);
    /// assert_eq!(g.to_vec(), vec![vec![1], vec![2], vec![0]]);
    /// assert_eq!(rg.to_vec(), vec![vec![2], vec![0], vec![1]]);
    /// ```
    pub fn from_edges_and_rev(n: usize, edges: &[(usize, usize)]) -> (Self, Self) {
        let mut forward = Csr {
            data: vec![usize::MAX; edges.len()],
            boundary: vec![0; n + 1],
        };
        let mut backward = Csr {
            data: vec![usize::MAX; edges.len()],
            boundary: vec![0; n + 1],
        };
        for &(i, j) in edges {
            forward.boundary[i] += 1;
            backward.boundary[j] += 1;
        }
        for i in 1..=n {
            forward.boundary[i] += forward.boundary[i - 1];
            backward.boundary[i] += backward.boundary[i - 1];
        }
        for &(i, j) in edges {
            forward.boundary[i] -= 1;
            forward.data[forward.boundary[i]] = j;
            backward.boundary[j] -= 1;
            backward.data[backward.boundary[j]] = i;
        }
        (forward, backward)
    }
}

impl<T> Default for Csr<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Debug for Csr<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Immutable iterator over rows.
pub struct Iter<'a, T> {
    pub(crate) data: &'a [T],
    pub(crate) boundary: &'a [usize],
}
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a [T];
    fn next(&mut self) -> Option<Self::Item> {
        if self.boundary.len() <= 1 {
            return None;
        }
        let &[l, r] = &self.boundary[..2] else { unreachable!() };
        self.boundary = &self.boundary[1..];
        Some(&self.data[l..r])
    }
}
impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.boundary.len() <= 1 {
            return None;
        }
        let &[l, r] = &self.boundary[self.boundary.len() - 2..] else { unreachable!() };
        self.boundary = &self.boundary[..self.boundary.len() - 1];
        Some(&self.data[l..r])
    }
}
impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.boundary.len() - 1
    }
}
impl<'a, T> IntoIterator for &'a Csr<T> {
    type Item = &'a [T];
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> Index<usize> for Csr<T> {
    type Output = [T];
    fn index(&self, i: usize) -> &[T] {
        self.section(i)
    }
}
impl<T> IndexMut<usize> for Csr<T> {
    fn index_mut(&mut self, i: usize) -> &mut [T] {
        self.section_mut(i)
    }
}
