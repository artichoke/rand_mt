# Contributing to Artichoke – rand_mt

👋 Hi and welcome to [Artichoke](https://github.com/artichoke). Thanks for
taking the time to contribute! 💪💎🙌

Artichoke aspires to be a Ruby 2.6.3-compatible implementation of the Ruby
programming language.
[There is lots to do](https://github.com/artichoke/artichoke/issues).

rand_mt is used to implement the default psuedorandom number generator that
backs the [`Random` core class](https://ruby-doc.org/core-2.6.3/Random.html).

If Artichoke does not run Ruby source code in the same way that MRI does, it is
a bug and we would appreciate if you
[filed an issue so we can fix it](https://github.com/artichoke/artichoke/issues/new).
[File bugs specific to rand_mt in this repository](https://github.com/artichoke/rand_mt/issues/new).

If you would like to contribute code to rand_mt 👩‍💻👨‍💻, find an issue that looks
interesting and leave a comment that you're beginning to investigate. If there
is no issue, please file one before beginning to work on a PR.
[Good first issues are labeled `E-easy`](https://github.com/artichoke/rand_mt/labels/E-easy).

## Discussion

If you'd like to engage in a discussion outside of GitHub, you can
[join Artichoke's public Discord server](https://discord.gg/QCe2tp2).

## Setup

rand_mt includes Rust and Text sources. Developing on rand_mt requires
configuring several dependencies.

### Rust Toolchain

rand_mt depends on Rust and several compiler plugins for linting and formatting.
rand_mt is guaranteed to build on the latest stable release of the Rust
compiler.

#### Installation

The recommended way to install the Rust toolchain is with
[rustup](https://rustup.rs/). On macOS, you can install rustup with
[Homebrew](https://docs.brew.sh/Installation):

```sh
brew install rustup-init
rustup-init
```

Once you have rustup, you can install the Rust toolchain needed to compile
rand_mt:

```sh
rustup toolchain install stable
rustup component add rustfmt
rustup component add clippy
```

To update your stable Rust compiler to the latest version, run:

```sh
rustup update stable
```

### Rust Crates

rand_mt depends on several Rust libraries, or crates. Once you have the Rust
toolchain installed, you can install the crates specified in
[`Cargo.toml`](Cargo.toml) by running:

```sh
cargo build
```

### Node.js

Node.js is an optional dependency that is used for formatting text sources with
[prettier](https://prettier.io/).

Node.js is only required for formatting if modifying the following filetypes:

- `md`
- `yaml`
- `yml`

You will need to install
[Node.js](https://nodejs.org/en/download/package-manager/).

On macOS, you can install Node.js with
[Homebrew](https://docs.brew.sh/Installation):

```sh
brew install node
```

## Linting

To lint and format Rust sources run:

```sh
cargo fmt
touch src/lib.rs
cargo clippy --all-targets --all-features
```

To lint and format text sources run:

```sh
npx prettier --write '**/*'
```

## Testing

A PR must have new or existing tests for it to be merged. The
[Rust book chapter on testing](https://doc.rust-lang.org/book/ch11-00-testing.html)
is a good place to start.

To run tests:

```sh
cargo test
```

`cargo test` accepts a filter argument that will limit test execution to tests
that substring match. For example, to run all of the tests for encoding:

```sh
cargo test encode
```

Tests are run for every PR. All builds must pass before merging a PR.

## Updating Dependencies

### Rust Crates

Version specifiers in `Cargo.toml` are NPM caret-style by default. A version
specifier of `4.1.2` means `4.1.2 <= version < 5.0.0`.

To see what crates are outdated, you can use
[cargo-outdated](https://github.com/kbknapp/cargo-outdated).

If you need to pull in an updated version of a crate for a bugfix or a new
feature, update the version number in `Cargo.toml`. See
[Artichoke GH-548](https://github.com/artichoke/artichoke/pull/548) for an
example.

Regular dependency bumps are handled by [@dependabot](https://dependabot.com/).
