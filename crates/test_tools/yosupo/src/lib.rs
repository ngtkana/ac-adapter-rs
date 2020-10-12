use std::{
    fs::{metadata, read_dir, File},
    io::Read,
    path::{Path, PathBuf},
    process::Command,
};
use yansi::Paint;

pub fn run_all<F>(problem_path: &str, main: F)
where
    F: 'static + Fn(&str, &mut String) + Clone + Send,
{
    use std::thread::spawn;

    let problem_info = ProblemInfo::new(problem_path);
    generate(problem_info.path());

    let names = ls(problem_info.path());
    let mut handles = Vec::new();

    for name in names {
        let problem_info = problem_info.clone();
        let main = main.clone();
        let handle = spawn(move || {
            run_one(&TestcaseInfo { problem_info, name }, main);
        });
        handles.push(handle);
    }
    for handle in handles {
        handle.join().unwrap();
    }
}

fn run_one<F>(testcase_info: &TestcaseInfo, main: F)
where
    F: Fn(&str, &mut String),
{
    echo_green("Yosupoing", &testcase_info.pretty());
    let in_string = testcase_info.read(Kind::In);
    let out_string = testcase_info.read(Kind::Out);

    let mut result = String::new();
    main(&in_string, &mut result);

    if result != out_string {
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
    echo_green("Succeeded", &testcase_info.pretty());
}

#[derive(Debug, Clone, PartialEq)]
struct ProblemInfo(PathBuf);
impl ProblemInfo {
    fn new(src: &str) -> Self {
        Self(PathBuf::from(src.to_owned()))
    }
    fn path(&self) -> &Path {
        &self.0
    }
    fn name(&self) -> &str {
        self.0.file_name().unwrap().to_str().unwrap()
    }
}

#[derive(Debug, Clone, PartialEq)]
struct TestcaseInfo {
    problem_info: ProblemInfo,
    name: String,
}
impl TestcaseInfo {
    fn problem_path(&self) -> &Path {
        &self.problem_info.path()
    }
    fn problem_name(&self) -> &str {
        self.problem_info.name()
    }
    fn testcase_path(&self, kind: Kind) -> PathBuf {
        self.problem_path()
            .join(PathBuf::from(kind.expand()))
            .join(PathBuf::from(self.testcase_name()))
            .with_extension(kind.expand())
    }
    fn testcase_name(&self) -> &str {
        &self.name
    }
    fn pretty(&self) -> String {
        format!("{}/{}", self.problem_name(), self.testcase_name())
    }
    fn read(&self, kind: Kind) -> String {
        let path = self.testcase_path(kind);
        let mut string = String::new();
        File::open(path)
            .unwrap()
            .read_to_string(&mut string)
            .unwrap();
        string
    }
}

#[derive(Debug, Clone, PartialEq, Copy, Eq)]
enum Kind {
    In,
    Out,
}
impl Kind {
    fn expand(self) -> &'static str {
        match self {
            Kind::In => "in",
            Kind::Out => "out",
        }
    }
}

fn echo_green(title: &str, payload: &str) {
    println!(
        "{} {}",
        Paint::green(format!("{:>12}", title)).bold(),
        payload,
    );
}

fn ls(problem_path: &Path) -> Vec<String> {
    let mut names = read_dir(problem_path.join(PathBuf::from("in")))
        .unwrap()
        .map(Result::unwrap)
        .map(|dir_entry| dir_entry.path())
        .map(|path| path.file_stem().unwrap().to_str().unwrap().to_string())
        .collect::<Vec<_>>();
    names.sort_by_key(|name| {
        metadata(
            problem_path
                .join(PathBuf::from("in"))
                .join(PathBuf::from(name))
                .with_extension("in"),
        )
        .unwrap()
        .len()
    });
    names
}

fn generate(problem_path: &Path) {
    let problem_name = problem_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .to_owned();
    let mut path = problem_path.to_owned();
    while path.file_name().unwrap().to_str().unwrap() != "library-checker-problems" {
        path.pop();
    }
    let script = path.join(Path::new("generate")).with_extension("py");
    echo_green("Generating", &problem_name);
    let success = Command::new("python3")
        .arg(&script)
        .arg("-p")
        .arg(&problem_name)
        .spawn()
        .unwrap()
        .wait()
        .unwrap()
        .success();
    assert!(success);
}
