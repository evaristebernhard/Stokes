# Archived Nodal Surfaces Project

This directory preserves the previous project state before the repository pivoted to AGCert.

It contains:

- `crates/`: the Rust workspace for nodal surface reproductions and certificate experiments.
- `doc/`: process documents, reading notes, engineering roadmaps, and degree08 negative-result analysis.
- `arxiv/`: local reference papers and extracted text.
- `Cargo.toml` / `Cargo.lock`: the old workspace manifest and lockfile.

## Status At Archive Time

The archived project had reproduced or partially reproduced:

- degree02 quadric cone.
- degree03 Cayley cubic.
- degree04 Kummer quartic.
- degree05 Togliatti quintic certificates.
- degree06 Barth sextic support-strata certificates.
- degree07 Labs septic partial certificate route.
- degree08 Endrass octic skeleton, search infrastructure, and negative-result documents.

The degree08 work should be read as historical exploration, not as a complete proof of Endrass' global singularity statement.

## How To Run

From this directory:

```text
cargo test --workspace
cargo clippy --workspace -- -D warnings
```

Some heavy or ignored tests may require local Singular/CAS setup described in `doc/cas-toolchain.md`.

## Role In AGCert

This archive is expected to provide case studies and regression material for the new AGCert verifier. The archive itself should remain stable unless a task explicitly asks to migrate or clean historical material.
