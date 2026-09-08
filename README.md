# AC Adapter

![AC Adapter Logo](contents/logo.png)

## API Document

https://ngtkana.github.io/ac-adapter-rs/

## Development

Install local pre-commit hooks:

```sh
cargo make hooks-install
```

Requires `cargo-make` and `cargo-nextest` (see `.github/actions/setup-rust/action.yml` for the versions CI uses). Runs `cargo fmt --check`, `clippy`, doctests, the full test suite, and doc generation before each commit — all confirmed lightweight (sub-second on an incrementally-built tree).

## Bundling for submission

`libbundle` inlines a crate (and its internal dependencies) into a single AtCoder-submittable snippet.

Install once:

```sh
cargo make install-libbundle
```

Then run from anywhere (e.g. your competitive-programming repo), pointing `AC_ADAPTER_RS_ROOT` at this repo:

```sh
export AC_ADAPTER_RS_ROOT="$HOME/repos/ac-adapter-rs"  # add to your shell rc
libbundle fp_fps dinic > bundled.rs                    # multiple crates, deduped
```


