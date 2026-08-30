//! 競技プログラミング用の出力ライブラリです。
//!
//! [`println`], [`print`] はマクロの呼び出しのたびに flush されて遅いです。
//!
//! そこでプログラムの中断・終了時に纏めて flush する版として、[`dprintln`],
//! [`dprint`] を用意してあります。
//!
//! Flush は `atexit` と [`std::panic::set_hook`] に登録されます。
//!
//! # Examples
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
    if let Ok(mut buf) = BUFFER.lock()
        && !buf.is_empty()
    {
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

    if let Ok(mut buf) = BUFFER.lock() {
        let _ = buf.write_fmt(args);
    }
}

/// Flush を遅延した版の [`print`] です。
#[macro_export]
macro_rules! dprint {
    () => {
        $crate::_print(format_args!())
    };
    ($($arg:tt)*) => {
        $crate::_print(format_args!("{}", format_args!($($arg)*)))
    };
}

/// Flush を遅延した版の [`println`] です。
#[macro_export]
macro_rules! dprintln {
    () => {
        $crate::_print(format_args!("\n"))
    };
    ($($arg:tt)*) => {
        $crate::_print(format_args!("{}\n", format_args!($($arg)*)))
    };
}
