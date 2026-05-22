# AGENTS.md

This repository is now an AGCert workspace.

## Project Goal

Build a lightweight, independent verifier for computational algebraic geometry certificates:

```text
CAS output -> portable certificate -> independently checked algebraic claim.
```

The project should not become a full CAS, a proof-assistant formalization project, or a nodal-surface-only script collection. Nodal surfaces are archived case studies.

## Repository Layout

- `archive/nodal-surfaces/`: historical material from the previous nodal surfaces project.
- root directory: reserved for the new AGCert project.

Do not edit archived files unless the task explicitly asks for historical cleanup, migration, or case-study extraction.

## Active Technical Scope

Prioritize a small, auditable core:

- Exact coefficient rings: `Q`, finite fields, and eventually simple number fields.
- Sparse multivariate polynomials.
- Monomial orders and normal forms.
- Groebner basis certificate verification.
- Ideal membership / lift identity verification.
- Zero-dimensional quotient length via standard monomials.
- Saturation certificates, starting with `I : h^infty = J`.

Defer broad CAS features:

- Primary decomposition.
- General radical computation.
- Full algebraic number field towers.
- Numerical algebraic geometry.
- Automated proof search.

## Engineering Principles

- Certificate checking should be deterministic, exact, and small enough to audit.
- External CAS tools may generate certificates; the verifier must not trust them.
- Prefer clear certificate semantics over clever implicit reconstruction.
- Keep case studies separate from verifier core.
- Use archived nodal-surface examples as regression material only after the core format is stable.

## Historical Archive Policy

The old project in `archive/nodal-surfaces/` contains valuable work:

- Kummer quartic, Togliatti quintic, Barth sextic, Labs septic, and Endrass octic notes.
- Groebner/lift certificate experiments.
- Degree08 negative-result documents and search infrastructure.

Treat it as read-only history by default. New AGCert code and documentation should live outside the archive.

## Verification Expectations

For code changes, run the relevant focused tests first. Once a Rust workspace exists at the new root, prefer:

```text
cargo test --workspace
cargo clippy --workspace -- -D warnings
```

If only archive material is touched, run checks from `archive/nodal-surfaces/` when feasible and state any skipped checks clearly.
