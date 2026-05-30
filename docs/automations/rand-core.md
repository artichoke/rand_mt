# rand_core Maintenance Automation

The rand_core maintenance automation is a scheduled repository maintenance role
for keeping the optional `rand_core` integration current.

The automation must read `docs/automations/README.md` and this document before
running. Human feedback on any output it produces, including inbox follow-ups,
pull request comments, review decisions, failed validation, compatibility
misses, or release follow-ups, should be reviewed and used to update this
document before repeating the same class of issue. Automation-authored pull
request comments must start with the stable prefix `Codex automation note:`.
Treat comments with that prefix as automation state, not human feedback for this
learning loop.

## Schedule

Run once per week against this repository. `rand_core` releases are infrequent
enough that weekly checking is sufficient.

## Policy

Treat every new `rand_core` `0.x` minor as a breaking change. When the newest
stable `rand_core` release is on a newer `0.x` minor than this crate currently
uses, update the integration wholesale to that minor and prepare a new minor
release of `rand_mt`.

Once `rand_core` reaches `1.0`, stop treating every minor update as breaking. At
that point, this automation should only do the full minor-release workflow for
`rand_core` major version changes unless this runbook is updated with a more
specific compatibility policy.

Do not widen the `rand_core` dependency range across multiple `0.x` minors. Each
adopted `0.x` minor should be an exact dependency line in `Cargo.toml`, with
source changes made as needed for that minor's traits and APIs.

## Sources

Use authoritative upstream sources:

- crates.io metadata for `rand_core`;
- docs.rs API docs for the current and candidate versions;
- release notes, changelogs, tags, and commits in the `rust-random/rand`
  repository when API compatibility is unclear.

Ignore prereleases unless this crate already depends on a prerelease or a human
explicitly asks to evaluate one.

## Workflow

Start by reading:

- `Cargo.toml`, especially the `rand_core` dependency and `rand-traits` feature;
- `src/mt/rand.rs`;
- `src/mt64/rand.rs`;
- `README.md` and `src/lib.rs` feature documentation;
- the CI workflow.

Check the newest stable `rand_core` release. If this crate already uses the
newest relevant version, do not create a branch, commit, push, or pull request.
Open an inbox item with the checked versions and sources.

If a newer `rand_core` `0.x` minor exists, update to that minor as a breaking
integration update:

- update `Cargo.toml`;
- update any implementation code required by the new `rand_core` traits;
- update documentation if trait names, examples, or compatibility notes changed;
- update tests or add focused tests for changed trait behavior;
- prepare a separate release-prep pull request after the integration pull
  request merges.

If `rand_core` is `1.x` or later, update only when a newer major version exists,
unless release notes require a compatibility update sooner.

## Changes

Pull requests from this automation must include the `A-deps`, `A-release`,
`C-automation`, and `codex` labels.

Do not enable auto-merge for `rand_core` `0.x` minor updates. Treat them as
breaking integration changes even if the source diff is small. Assign the pull
request to `lopopolo` and open an inbox item with compatibility notes and
release-prep status.

After a `rand_core` update merges, open a separate release-prep pull request
that bumps the crate minor version, updates `html_root_url`, updates README
installation examples, and prepares the tag for the publish workflow. Do not
duplicate an existing open release-prep pull request.

## Validation and Summary

For `rand_core` changes, run:

```sh
cargo fmt --check
cargo test --workspace
cargo test --workspace --all-features
cargo test --workspace --no-default-features
cargo clippy --workspace --all-features --all-targets
RUSTDOCFLAGS="-D warnings -D rustdoc::broken_intra_doc_links --cfg docsrs" \
  cargo +nightly doc --workspace
pnpm exec prettier --check '**/*'
```

If a release-prep pull request is opened, also run `cargo package --allow-dirty`
before finalizing the pull request.

Open an inbox item after every run summarizing:

- current and newest `rand_core` versions checked;
- source links used;
- whether a `0.x` minor or post-`1.0` major update is available;
- compatibility findings and required source changes;
- validation run and any skipped checks;
- pull request and auto-merge status, if a pull request was opened;
- release-prep status or required human follow-up.
