# Agent Instructions

You are working in `artichoke/rand_mt`, a Rust crate that implements MT19937 and
MT19937-64 pseudorandom number generators.

Users rely on deterministic output sequences, documented Ruby compatibility,
`no_std` support, optional `rand_core` integration, MSRV, and the public crate
API. Treat those as compatibility surfaces.

## Operating Loop

1. Classify the change before editing.
2. Use the matching workflow section below to choose the guardrails and runbooks
   to consult.
3. Use [ARCHITECTURE.md](ARCHITECTURE.md) as the repository map for module
   responsibilities, boundaries, and architectural invariants.
4. Keep the diff narrow. Do not mix behavior, dependency posture, release
   metadata, formatting, and automation cleanup unless the task requires it.
5. Add or update focused tests for behavior changes, especially changes that can
   affect deterministic output or Ruby compatibility.
6. Run checks that match the risk of the change; use
   [CONTRIBUTING.md](CONTRIBUTING.md) for local command expectations. If a
   relevant check is skipped, explain why in the PR.
7. Update README, crate docs, [ARCHITECTURE.md](ARCHITECTURE.md), guardrails, or
   runbooks when public behavior, compatibility claims, feature behavior, MSRV,
   dependency policy, architectural invariants, or release process changes.

## Generator Behavior And Compatibility

Use this workflow for changes to MT19937, MT19937-64, seeding, generated output,
test vectors, or Ruby reproducibility.

Consult:

- [Testing and conformance](docs/guardrails/testing-compatibility-and-conformance.md),
  for deterministic output and compatibility coverage.
- [API stability, semver, and MSRV](docs/guardrails/api-stability-semver-and-msrv.md),
  if behavior changes affect public expectations.

Preserve existing output sequences unless the task explicitly asks for a
breaking compatibility change. Add regression coverage for every behavior fix.

## Public API, Features, MSRV, And Releases

Use this workflow for API shape, feature flags, docs.rs metadata, crate
metadata, MSRV, semver, publishing, changelog, and release-readiness changes.

Consult:

- [API stability, semver, and MSRV](docs/guardrails/api-stability-semver-and-msrv.md),
  for public contract and compatibility impact.
- [Working in public and publishing](docs/guardrails/working-in-public-and-publishing-oss-crates.md),
  for OSS release and communication expectations.

Call out compatibility impact in the PR. Keep release-prep changes separate from
unrelated implementation cleanup.

## `rand_core` Integration

Use this workflow for optional `rand_core` support, feature-gated RNG traits, or
dependency range compatibility.

Consult:

- [`rand_core` automation](docs/automations/rand-core.md), for the expected
  maintenance flow.
- [API stability, semver, and MSRV](docs/guardrails/api-stability-semver-and-msrv.md),
  for feature and dependency range impact.
- [Testing and conformance](docs/guardrails/testing-compatibility-and-conformance.md),
  for feature-matrix coverage.

Verify default, all-features, and no-default-features builds when this workflow
touches features or dependencies.

## `no_std`, Performance, And Memory Behavior

Use this workflow for allocation behavior, hot paths, `no_std`, panic behavior,
and implementation changes intended to affect performance or memory use.

Consult:

- [Performance, allocation, and memory behavior](docs/guardrails/performance-allocation-and-memory-behavior.md),
  for allocation and runtime-behavior expectations.
- [High-quality Rust code](docs/guardrails/high-quality-rust-code.md), for lint,
  documentation, and maintainability expectations.

Do not introduce allocation, `std` requirements, or unsafe code without explicit
justification in the PR.

## Dependencies, CI, And Automation

Use this workflow for dependency ranges, audits, Dependabot, GitHub Actions,
runner image updates, labels, and recurring maintenance.

Consult:

- [Dependency posture](docs/dependencies.md), for supply-chain expectations.
- [Dependency sweep automation](docs/automations/dependency-sweep.md), for
  dependency update procedure.
- [GitHub Actions runner images](docs/automations/github-actions-runner-images.md),
  for runner maintenance.
- [Working in public and publishing](docs/guardrails/working-in-public-and-publishing-oss-crates.md),
  if the change affects release or user-facing maintenance policy.

Keep mechanical dependency and automation updates separate from behavior
changes.

## Documentation-Only Changes

Use this workflow for README, crate docs, guardrails, runbooks, and PR/process
documentation.

Consult:

- [Architecture](ARCHITECTURE.md), for repository shape, module boundaries, and
  architectural invariants.
- [High-quality Rust code](docs/guardrails/high-quality-rust-code.md), for
  documentation quality expectations.
- [Working in public and publishing](docs/guardrails/working-in-public-and-publishing-oss-crates.md),
  for public-facing OSS communication.
- The guardrail for the topic being documented when docs describe API,
  compatibility, dependency, performance, or release behavior.

Docs-only PRs may skip Rust tests when the PR explains why. Still run the repo
formatter.

## Pull Requests

- State the change class and compatibility impact.
- Use labels from `.github/labels.yaml`; include at least one `A-*` label.
- For automation-generated work, use `C-automation` and the `codex` label.
- Do not add a Codex tag to the title or description.
