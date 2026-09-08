//! 呼び出しのたびに flush しない出力マクロ。
//!
//! [`println`], [`print`] は呼び出しのたびに標準出力を flush するため、大量に呼び出すと低速。
//! [`dprintln`], [`dprint`] は内部バッファへの書き込みに留め、プログラム終了時（`atexit`）と
//! パニック時（[`std::panic::set_hook`]）にまとめて flush することで呼び出しあたりのコストを下げる。
//!
//! # 仕様
//!
//! - [`dprint!`][]: [`print!`] 相当。バッファに書き込むのみで flush しない
//! - [`dprintln!`][]: [`println!`] 相当。同様に遅延 flush
//! - flush されるタイミング: プログラム正常終了時、パニック時
//!
//! # 例
//!
//! ```
//! use io_writer::dprintln;
//!
//! dprintln!("{:?}", ["hello", "world!"]);
//! ```

use std::fmt;
use std::io::{self, Write};
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};

static BUFFER: Mutex<Vec<u8>> = Mutex::new(Vec::new());
static REGISTERED: AtomicBool = AtomicBool::new(false);

unsafe extern "C" {
    fn atexit(cb: extern "C" fn()) -> std::ffi::c_int;
}

extern "C" fn flush_on_exit() {
    flush_buffered_stdout();
}

fn flush_buffered_stdout() {
    let mut buf = BUFFER.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    if !buf.is_empty() {
        let stdout = io::stdout();
        let mut handle = stdout.lock();
        let _ = handle.write_all(&buf);
        let _ = handle.flush();
        buf.clear();
    }
}

fn init_dprinter() {
    if !REGISTERED.swap(true, Ordering::SeqCst) {
        unsafe {
            atexit(flush_on_exit);
        }

        let next_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |panic_info| {
            flush_buffered_stdout();
            next_hook(panic_info);
        }));
    }
}

#[doc(hidden)]
pub fn _print(args: fmt::Arguments) {
    if !REGISTERED.load(Ordering::Relaxed) {
        init_dprinter();
    }

    // Format into a local buffer first, without holding the shared lock: `args`
    // may contain a user-provided `Display`/`Debug` impl that panics, and
    // panicking while `BUFFER` is locked would deadlock the panic hook's own
    // attempt to lock `BUFFER` in order to flush already-buffered output.
    let mut local = Vec::new();
    let _ = local.write_fmt(args);
    let mut buf = BUFFER.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    buf.extend_from_slice(&local);
}

/// バッファリングして遅延 flush する [`print!`] 相当のマクロ。
///
/// 呼び出しのたびに flush する [`print!`] と異なり、内部バッファに書き込むだけに留める。
/// プログラム終了時またはパニック時にまとめて flush される。
///
/// # 例
///
/// ```
/// use io_writer::dprint;
///
/// dprint!("{}", 42);
/// ```
#[macro_export]
macro_rules! dprint {
    () => {
        $crate::_print(format_args!())
    };
    ($($arg:tt)*) => {
        $crate::_print(format_args!("{}", format_args!($($arg)*)))
    };
}

/// バッファリングして遅延 flush する [`println!`] 相当のマクロ。
///
/// 呼び出しのたびに flush する [`println!`] と異なり、内部バッファに書き込むだけに留める。
/// プログラム終了時またはパニック時にまとめて flush される。
///
/// # 例
///
/// ```
/// use io_writer::dprintln;
///
/// dprintln!("{:?}", ["hello", "world!"]);
/// ```
#[macro_export]
macro_rules! dprintln {
    () => {
        $crate::_print(format_args!("\n"))
    };
    ($($arg:tt)*) => {
        $crate::_print(format_args!("{}\n", format_args!($($arg)*)))
    };
}
