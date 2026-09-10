use std::cell::UnsafeCell;
use std::mem::ManuallyDrop;
use std::ops::Deref;
use std::sync::Once;

union Data<T, F> {
    value: ManuallyDrop<T>,
    f: ManuallyDrop<F>,
}

unsafe impl<T: Sync + Send, F: Send> Sync for LazyLock<T, F> {}

/// 遅延初期化するセル。`std::sync::LazyLock` 安定化前の代替実装。
///
/// 初期化関数 `F` を保持し、初回アクセス（[`Self::force`] または `Deref`）時に
/// 一度だけ実行して結果をキャッシュする。`Once` によりスレッド間でも一度しか
/// 初期化されないことを保証する。
///
/// # 例
///
/// ```
/// use jolt::LazyLock;
/// let lock = LazyLock::new(|| 1 + 2);
/// assert_eq!(*lock, 3);
/// ```
pub struct LazyLock<T, F = fn() -> T> {
    once: Once,
    data: UnsafeCell<Data<T, F>>,
}
impl<T, F: FnOnce() -> T> LazyLock<T, F> {
    /// 初期化関数 `f` を保持する、未初期化の `LazyLock` を作る。
    #[inline]
    pub const fn new(f: F) -> LazyLock<T, F> {
        LazyLock {
            once: Once::new(),
            data: UnsafeCell::new(Data {
                f: ManuallyDrop::new(f),
            }),
        }
    }

    /// 初期化済みなら値への参照を返す。未初期化なら `None`（初期化は行わない）。
    #[inline]
    pub fn get(this: &LazyLock<T, F>) -> Option<&T> {
        if this.once.is_completed() {
            Some(unsafe { &(*this.data.get()).value })
        } else {
            None
        }
    }

    /// 未初期化なら `f` を実行して値を確定させ、その参照を返す。
    ///
    /// 2 回目以降の呼び出しではキャッシュされた値をそのまま返す。
    #[inline]
    pub fn force(this: &LazyLock<T, F>) -> &T {
        this.once.call_once(|| {
            let data = unsafe { &mut *this.data.get() };
            let f = unsafe { ManuallyDrop::take(&mut data.f) };
            let value = f();
            data.value = ManuallyDrop::new(value);
        });
        unsafe { &(*this.data.get()).value }
    }
}

impl<T, F: FnOnce() -> T> Deref for LazyLock<T, F> {
    type Target = T;

    /// [`Self::force`] を呼び出し、値への参照を返す。
    #[inline]
    fn deref(&self) -> &T {
        LazyLock::force(self)
    }
}

impl<T, F> Drop for LazyLock<T, F> {
    fn drop(&mut self) {
        let data = self.data.get_mut();
        if self.once.is_completed() {
            unsafe { ManuallyDrop::drop(&mut data.value) };
        } else {
            unsafe { ManuallyDrop::drop(&mut data.f) };
        }
    }
}
