# Contributing to Artichoke - rand_mt

Welcome to [Artichoke]. Thanks for taking the time to contribute.

Artichoke aspires to be a [recent MRI Ruby][mri-target]-compatible
implementation of the Ruby programming language. [There is lots to do].

[mri-target]:
  https://github.com/artichoke/artichoke/blob/trunk/RUBYSPEC.md#mri-target

rand_mt implements reference Mersenne Twister pseudorandom number generators.
Artichoke uses this crate to implement the default pseudorandom number generator
that backs the [`Random` core class].

If Artichoke does not run Ruby source code in the same way that MRI does, please
[file an issue so we can fix it]. [File bugs specific to rand_mt in this
repository].

Maintenance of this repository is Codex-first. Prefer asking Codex to prepare
routine code, documentation, CI, and dependency changes. Contributors should
focus on issue selection, review, release decisions, and validating that the
resulting diff and CI status match the intended change.

## Setup

rand_mt includes Rust and text sources. Developing on rand_mt requires
configuring several dependencies.

rand_mt uses [mise] to manage the local development toolchain declared in
[`mise.toml`](mise.toml), including Node.js, Rust, and auxiliary Rust tools. For
Rust, `mise` uses [rustup] under the hood. Nightly-only Rust workflows in this
repository continue to use `rustup` directly.

### Rust Toolchain

rand_mt depends on Rust and compiler plugins for linting and formatting. The
crate is guaranteed to build on the Rust version declared as the minimum
supported Rust version in [`Cargo.toml`](Cargo.toml), and it is tested on the
latest stable Rust compiler.

#### Installation

Install and activate [mise], then install the toolchains declared in
[`mise.toml`](mise.toml):

```sh
mise install
```

`mise.toml` configures the latest stable Rust toolchain with the `minimal`
profile plus the `clippy` and `rustfmt` components. `mise` installs that
toolchain via [rustup].

Documentation checks use nightly Rust. Install nightly with
`rustup toolchain install nightly` if you run those workflows locally.

To update your stable Rust compiler to the latest version, run:

```sh
rustup update stable
```

### Rust Crates

rand_mt depends on Rust crates from crates.io. Once you have the Rust toolchain
installed, you can fetch and build the crates specified in [`Cargo.toml`] by
running:

```sh
cargo build
```

rand_mt uses direct tool invocations instead of a repository task runner. The
most common development commands are:

```sh
cargo build --workspace
cargo test --workspace
cargo fmt
cargo clippy --workspace --all-features --all-targets
npm run fmt
RUSTDOCFLAGS="-D warnings -D rustdoc::broken_intra_doc_links --cfg docsrs" \
  cargo +nightly doc --workspace
```

### Node.js

Node.js is an optional dependency used for formatting text sources with
[prettier].

Node.js is only required for formatting if modifying the following filetypes:

- `md`
- `yaml`
- `yml`

Install Node.js with `mise`:

```sh
mise install
```

Install the repository-local Node.js dependencies with:

```sh
npm ci
```

## Linting

To lint and format Rust sources run:

```sh
cargo clippy --workspace --all-features --all-targets
cargo fmt
```

To lint and format text sources run:

```sh
npm run fmt
npm run fmt:check
```

## Testing

A PR must have new or existing tests for it to be merged. The [Rust book chapter
on testing] is a good place to start.

To run tests:

```sh
cargo test
```

`cargo test` accepts a filter argument that limits test execution to tests that
substring match.

Tests are run for every PR. All builds must pass before merging a PR.

## Codex Maintenance Workflow

Prefer asking Codex to prepare changes on a branch, including any docs and CI
updates needed for the patch. Review the resulting diff as authored code:

- Confirm the change is scoped to the issue or maintenance task.
- Confirm generated or mechanical changes are intentional.
- Confirm CI passes before merging.
- Ask Codex to follow up on review comments or failed checks.

## Updating Dependencies

### Rust Crates

Version specifiers in `Cargo.toml` are NPM caret-style by default. A version
specifier of `4.1.2` means `4.1.2 <= version < 5.0.0`.

To see what crates are outdated, you can use [cargo-outdated].

If you need to pull in an updated version of a crate for a bugfix or a new
feature, update the version number in `Cargo.toml`. See
[artichoke/artichoke#548] for an example.

Regular dependency bumps are handled by [@dependabot].

[artichoke]: https://github.com/artichoke
[there is lots to do]: https://github.com/artichoke/artichoke/issues
[`random` core class]: https://ruby-doc.org/core-3.1.2/Random.html
[filed an issue so we can fix it]:
  https://github.com/artichoke/artichoke/issues/new
[file bugs specific to rand_mt in this repository]:
  https://github.com/artichoke/rand_mt/issues/new
[mise]: https://mise.jdx.dev/
[rustup]: https://rustup.rs/
[prettier]: https://prettier.io/
[rust book chapter on testing]:
  https://doc.rust-lang.org/book/ch11-00-testing.html
[cargo-outdated]: https://github.com/kbknapp/cargo-outdated
[artichoke/artichoke#548]: https://github.com/artichoke/artichoke/pull/548
[@dependabot]: https://dependabot.com/
