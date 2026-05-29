# Repository Map

This file is a map for agents working in this repository. It points to the
source-of-truth docs, configuration, and code landmarks; it should not duplicate
the policy held by those files.

## Start Here

- `README.md`: crate purpose, compatibility claims, and public examples.
- `CONTRIBUTING.md`: local development setup and command expectations.
- `Cargo.toml`: crate metadata, feature flags, MSRV, dependency ranges, and
  docs.rs metadata.
- `docs/guardrails/README.md`: index for Rust, OSS, unsafe, platform, testing,
  API, FFI, and performance guardrails.
- `docs/dependencies.md`: dependency and supply-chain posture.
- `docs/automations/README.md`: recurring maintenance map.
- `.github/labels.yaml`: PR label vocabulary for this repository.

## Change Map

- Public API, semver, features, MSRV, or publishing:
  `docs/guardrails/api-stability-semver-and-msrv.md`,
  `docs/guardrails/working-in-public-and-publishing-oss-crates.md`,
  `Cargo.toml`, `README.md`, and `src/lib.rs`.
- Rust implementation quality, lints, generated docs, or error handling:
  `docs/guardrails/high-quality-rust-code.md`, `CONTRIBUTING.md`, `src/lib.rs`,
  and `.github/workflows/ci.yaml`.
- Output sequence compatibility, test vectors, or deterministic seeding:
  `docs/guardrails/testing-compatibility-and-conformance.md`, `src/vectors.rs`,
  `src/vectors/mt.rs`, `src/vectors/mt64.rs`, and
  `tests/ruby_reproducibility.rs`.
- `rand_core` integration or optional dependency behavior:
  `docs/automations/rand-core.md`, `Cargo.toml`, `src/mt/rand.rs`, and
  `src/mt64/rand.rs`.
- `no_std`, allocation, or performance-sensitive implementation work:
  `docs/guardrails/performance-allocation-and-memory-behavior.md`, `src/mt.rs`,
  `src/mt64.rs`, and `.github/workflows/ci.yaml`.
- Dependency, audit, or runner maintenance: `docs/dependencies.md`,
  `docs/automations/dependency-sweep.md`,
  `docs/automations/github-actions-runner-images.md`, `.github/dependabot.yml`,
  `.github/workflows/audit.yaml`, and `.github/workflows/repo-labels.yaml`.
- Markdown, YAML, JSON, or generated formatting changes: `package.json`,
  `.prettierrc.yaml`, and `pnpm-lock.yaml`.

## Code Map

- `src/lib.rs`: crate-level docs, feature gates, lint configuration, and public
  exports.
- `src/mt.rs`: MT19937 implementation and public 32-bit generator surface.
- `src/mt64.rs`: MT19937-64 implementation and public 64-bit generator surface.
- `src/mt/rand.rs` and `src/mt64/rand.rs`: optional `rand_core` integration.
- `src/vectors.rs`, `src/vectors/mt.rs`, and `src/vectors/mt64.rs`: reference
  vectors used to guard sequence compatibility.
- `tests/ruby_reproducibility.rs`: Ruby compatibility regression coverage.

## Pull Request Map

- Use labels from `.github/labels.yaml`; lopopolo-owned repositories require at
  least one `A-*` label.
- For automation-generated work, use `C-automation` and add the `codex` label.
  Keep `codex` as the last label definition in `.github/labels.yaml`.
- Do not add a Codex tag to PR titles or descriptions.
