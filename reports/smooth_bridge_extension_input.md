# Smooth Singular Bridge Extension Input Audit

## What this round packaged

New file:

- `Stokes/SingularCube/SmoothBridgeExtensionInputAuto.lean`

The open-neighborhood hypotheses from `SmoothBridgeLocalityFacade` are now
packaged as:

- `ChartSingularCubeLocalExtensionInput`
- `ChartwiseSingularCubeOpenExtensionInput`

The packaged data consists of:

- a globally smooth Euclidean form `omegaExt`;
- one open coordinate set `extensionSet`;
- membership of the cube image and both boundary-face images in that set;
- `EqOn omegaExt localForm extensionSet`.

The file provides boundary-integral and chain-level wrappers both for the
local-data route and for the chartwise facade route:

- `ChartSingularCubeLocalExtensionInput.singular_boundary_stokes_local`
- `ChartSingularCubeLocalExtensionInput.singular_chain_stokes_local`
- `ChartwiseSingularCubeOpenExtensionInput.boundary_stokes`
- `ChartwiseSingularCubeOpenExtensionInput.chain_stokes`
- `chartwise_singular_boundary_stokes_of_openExtensionInput`
- `chartwise_singular_chain_stokes_of_openExtensionInput`

It also names the future theorem output shape as:

- `ExistsChartwiseSingularCubeOpenExtensionInput`

## Remaining real theorem shape

The next analytic theorem should produce a value of
`ChartwiseSingularCubeOpenExtensionInput omega chart cube`.

Concretely, from chartwise smoothness of the manifold form and a compact cube
image lying inside a chart/smoothness neighborhood, it should construct:

1. an open coordinate neighborhood `extensionSet` containing the cube image and
   all boundary-face images;
2. a globally `ContDiff` Euclidean form `omegaExt`;
3. equality of `omegaExt` with `chartLocalForm I chart omega` on
   `extensionSet`.

This is the exact point where one needs a genuine smooth extension/localization
result, for example via bump functions or a Whitney-style extension theorem
specialized to compact subsets of finite-dimensional Euclidean coordinate
space.

## Current status

The bridge no longer exposes pointwise `hderiv` or per-face neighborhood
equality at the theorem-facing layer.  The singular route now asks for one
natural extension input package, and the rest of the exterior-derivative
locality bookkeeping is automatic.
