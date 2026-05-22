# Degree 08 General `P8 - R4^2` Search

This note records Worker A's lightweight finite-field prototype for the general
eight-plane route.  It is intentionally a smoke search, not a claim that any
candidate lifts to a characteristic-zero octic with more nodes than Endrass.

## Relation To The 112 Skeleton

For eight planes `L_1,...,L_8` in `P^3` and a quartic `R`, consider

```text
F = L_1 ... L_8 - R^2.
```

If two distinct planes meet in a line `ell_ij`, then the product term has a
double zero along that line.  At a point of `ell_ij` with `R=0`, both `F` and
the first derivatives vanish.  When the plane arrangement is simple and the
restriction `R|ell_ij` is squarefree of degree 4, each of the 28 pairwise
intersection lines contributes 4 ordinary nodes over the algebraic closure:

```text
28 lines * 4 roots = 112 base nodes.
```

Endrass keeps this base skeleton and then engineers 56 additional nodes by a
high-symmetry Segre-quotient mechanism.  The general `P8 - R4^2` route keeps
the same base mechanism but relaxes the plane arrangement and the quartic `R`.
The hope is not merely to perturb Endrass locally; it is to find other
arrangements where extra singularities appear for different geometric reasons.

## Degeneracies Filtered

The smoke binary `search_p8` filters before scoring:

- repeated/proportional plane pairs;
- triples of planes that fail to meet in an isolated projective point;
- quadruples of planes with a common projective point;
- line restrictions `R|ell_ij` that are not degree-4 squarefree binary forms;
- triple-plane points where `R=0`.

These filters keep the 112 base-node interpretation clean.  More singular
arrangements can be mathematically interesting, but they should be handled as a
separate stratum with its own local model rather than mixed into the first
general-position smoke.

## Current Prototype

The binary is:

```text
cargo run -p degree08 --bin search_p8 -- --prime 31 --limit 8
```

It constructs a deterministic pool of low-parameter eight-plane arrangements:

- `coord-affine`: four coordinate planes plus four affine-generic planes;
- `skew-affine`: eight low-coefficient skew planes.

For each arrangement it tries two quartic models:

- `even`: sparse even quartic plus an `xyzw` term;
- `dense`: deterministic dense homogeneous quartic of degree 4.

Each accepted candidate is passed through the shared
`degree08::search_core::ProjectiveSurfaceScorerInput` and
`score_projective_surface` pipeline.  The output uses the shared
`ExperimentRecord` TSV/JSONL shape, with tags for arrangement type, quartic
model, parameters, algebraic-closure base length, visible base roots over
`F_31`, and the trivial-symmetry orbit profile.

## Reading Finite-Field Signals

The finite-field count is a triage signal only.  A high count over `F_31` may
come from:

- genuine characteristic-zero singularities reducing modulo 31;
- singularities defined over an extension field that happen to become visible;
- characteristic-31 accidents;
- bad reductions or degenerations hidden by the finite-field model.

Conversely, a weak `F_31` score does not rule out a useful characteristic-zero
family, because many of the 112 base nodes are only visible over extension
fields.  The `base_ac=112` tag means the line restrictions certify the expected
algebraic-closure base length in the finite-field model; it does not prove a
complex octic with 112 ordinary nodes.  Any serious candidate still needs an
exact characteristic-zero reconstruction and a projective Jacobian/saturation
certificate.

## Next Mathematical Splits

Once the shared search core stabilizes, this route should split into three
sub-strata:

- general-position eight-plane arrangements preserving the clean 112 skeleton;
- controlled degenerate arrangements with quadruple or higher incidence,
  studied by local normal forms instead of the current filter;
- arrangements with a chosen symmetry group smaller than Endrass' `D8`, where
  extra events can appear in orbits of size 2, 4, 8, or 16 rather than the
  rigid `56` package.
