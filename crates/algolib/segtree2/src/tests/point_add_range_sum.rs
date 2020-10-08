use crate::Segtree;
use alg_traits::arith::Add;
use std::{
    fs::{metadata, read_dir, File},
    io::Read,
    path::{Path, PathBuf},
    process::Command,
};
use yansi::Paint;

const PROBLEM_DIR: &'static str =
    "../../../library-checker-problems/datastructure/point_add_range_sum";

fn main(in_str: &str, out_str: &mut String) {
    let mut buf = ngtio::with_str(in_str);
    let n = buf.usize();
    let q = buf.usize();
    let a = buf.vec::<u64>(n);
    let mut seg = Segtree::<Add<_>>::from_slice(&a);
    for _ in 0..q {
        let command = buf.usize();
        match command {
            0 => {
                let i = buf.usize();
                let x = buf.u64();
                let x = x + seg.fold(i..i + 1);
                seg.set(i, x);
            }
            1 => {
                let l = buf.usize();
                let r = buf.usize();
                let ans = seg.fold(l..r);
                out_str.push_str(&format!("{}\n", ans));
            }
            _ => panic!(),
        }
    }
}

#[test]
#[ignore]
fn point_add_range_sum() {
    YosupoTest::new(main, PathBuf::from(PROBLEM_DIR))
        .generate()
        .run_all();
}

fn echo_green(title: &str, payload: &str) {
    println!(
        "{} {}",
        Paint::green(format!("{:>12}", title)).bold(),
        payload,
    );
}

#[derive(Debug, Clone, PartialEq)]
struct YosupoTest<F>
where
    F: Fn(&str, &mut String),
{
    main: F,
    problem_name: String,
    problem_path: PathBuf,
}
impl<F> YosupoTest<F>
where
    F: Fn(&str, &mut String),
{
    fn new(main: F, problem_path: PathBuf) -> Self {
        Self {
            problem_name: problem_path
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .to_owned(),
            main,
            problem_path,
        }
    }
    fn run_all(&self) {
        let mut names = read_dir(self.problem_path.join(PathBuf::from("in")))
            .unwrap()
            .map(Result::unwrap)
            .map(|dir_entry| dir_entry.path())
            .map(|path| path.file_stem().unwrap().to_str().unwrap().to_string())
            .collect::<Vec<_>>();
        names.sort_by_key(|name| {
            metadata(
                self.problem_path
                    .join(PathBuf::from("in"))
                    .join(PathBuf::from(name))
                    .with_extension("in"),
            )
            .unwrap()
            .len()
        });
        names.into_iter().for_each(|name| self.run_one(&name));
    }
    fn generate(&self) -> &Self {
        let mut path = self.problem_path.clone();
        while path.file_name().unwrap().to_str().unwrap() != "library-checker-problems" {
            path.pop();
        }
        let script = path.join(Path::new("generate")).with_extension("py");
        echo_green("Generating", &self.problem_name);
        let success = Command::new("python3")
            .arg(&script)
            .arg("-p")
            .arg(&self.problem_name)
            .spawn()
            .unwrap()
            .wait()
            .unwrap()
            .success();
        assert!(success);
        &self
    }
    fn run_one(&self, name: &str) {
        echo_green("Yosping", &format!("{}/{}", &self.problem_name, name));
        let read = |kind: &str| -> String {
            let path = Path::new(&self.problem_path)
                .join(PathBuf::from(kind))
                .join(PathBuf::from(name))
                .with_extension(kind);

            let mut string = String::new();
            File::open(path)
                .unwrap()
                .read_to_string(&mut string)
                .unwrap();
            string
        };

        let in_string = read("in");
        let out_string = read("out");

        let mut result = String::new();
        (self.main)(&in_string, &mut result);

        if &result != &out_string {
            println!();
            println!("{}: test failed!", Paint::red("error").bold());
            println!();
            println!("{}", Paint::green("in"));
            println!("{}", &in_string);
            println!();
            println!("{}", Paint::green("out"));
            println!("{}", prettydiff::diff_lines(&result, &out_string));
            println!();
            std::process::abort();
        }
    }
}
