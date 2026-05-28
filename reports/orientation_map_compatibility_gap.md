# Orientation.map Compatibility Gap

Date: 2026-05-25

## Current mathlib evidence

The local mathlib tree exposes the linear orientation API in
`Mathlib.LinearAlgebra.Orientation`:

- `Orientation.map`
- `Module.Oriented`
- basis orientations
- determinant criteria such as
  `Module.Basis.orientation_comp_linearEquiv_eq_iff_det_pos`

The current local search did not find a manifold-with-boundary oriented atlas
API that directly provides boundary chart transition compatibility or induced
boundary orientation fields for `extChartAt` chart changes.

## Project bridge now added

`Stokes/BoundaryChart/OrientationMapCompatibility.lean` adds a narrow,
compilable bridge:

- fixed tangent equivalence + `Orientation.map` equality is equivalent to
  positive `boundaryChartTransitionJacobian` for that same equivalence;
- the same statement is exposed through the project-local transported boundary
  frame sign;
- `BoundaryChartLinearOrientationMapSource` stores the minimal pointwise
  linear compatibility source;
- `BoundaryChartMathlibLinearOrientationAtlasSource` packages atlas-level
  linear `Orientation.map` sources;
- `BoundaryChartPositiveJacobianAtlasSource` packages the weaker positive
  Jacobian route and rebuilds `BoundaryChartOrientationMapData`;
- direct selected-box constructors preserve the original stored
  `Orientation.map` field when building `BoundaryChartAtlasBoundarySignData`.

## Remaining blocker

There is still no proved constructor from a bare upstream oriented smooth
manifold-with-boundary object to these fields, because no such upstream API was
identified in the current mathlib checkout.  The next real proof step is to
either:

- find or develop a manifold-level oriented atlas layer producing pointwise
  `Orientation.map` compatibility for boundary chart transitions; or
- prove positive tangential Jacobian for oriented boundary chart transitions
  and feed it through `BoundaryChartPositiveJacobianAtlasSource`.
