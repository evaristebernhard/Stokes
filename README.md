# AGCert Workspace

This repository is pivoting from the nodal-surface reproduction project to a software project for checkable computational algebraic geometry certificates.

## Current Direction

Working name:

```text
AGCert
```

Goal:

```text
Build a portable certificate format and independent verifier for computational algebraic geometry claims produced by CAS tools.
```

The intended gap is not "another CAS" and not "a replacement for Lean." The target layer is:

```text
CAS computes -> exporter writes certificate -> small verifier independently checks it.
```

Initial certificate families:

- Groebner basis certificates.
- Ideal membership / lift identities.
- Zero-dimensional quotient length via standard monomials.
- Narrow saturation certificates of the form `I : h^infty = J`.
- Later: projective saturation, reducedness/radicality, number-field coefficients, ordinary-node checks.

## Archive

The previous nodal-surface project has been archived at:

```text
archive/nodal-surfaces/
```

It contains the old Rust workspace, documents, arXiv references, search notes, and degree02-degree08 reproduction code. Treat it as historical material and case-study material for AGCert, not as the active project root.

To inspect or rerun the old workspace:

```text
cd archive/nodal-surfaces
cargo test --workspace
```

## Near-Term Plan

1. Extract the reusable certificate ideas from the archived `nodal-core`.
2. Design a small versioned certificate format independent of Singular/Macaulay2/OSCAR.
3. Build a verifier crate with strict, readable semantics.
4. Add exporters or conversion scripts for at least Singular first.
5. Use archived nodal-surface examples as regression case studies.
