# Smooth Extension Mathlib API Audit

Scope: smooth singular cube bridge, local Euclidean extension, `ContDiffOn`
transport, cube/face restriction, and `extDeriv`/pullback APIs.

## Current Project Surface

- `Stokes.SingularCube.SmoothBridgeExtensionInputAuto` already exposes
  `ChartwiseSingularCubeOpenExtensionInput`, whose fields are exactly what the
  current singular Stokes bridge consumes: a globally smooth Euclidean form,
  one open extension set, cube/face image containment, and equality on that set.
- New private audit module:
  `Stokes/SingularCube/SmoothExtensionMathlibAudit.lean`.
- It adds `cubeAndFacesImage`, so the extension theorem can target one image
  subset instead of three separate face/cube containment fields.
- It adds `ChartwiseSingularCubeCoreExtensionInput`, which expands into the
  existing open-extension input and immediately gives boundary and chain
  Stokes.

## Mathlib APIs We Can Use Directly

- Exterior derivative locality:
  `Filter.EventuallyEq.extDeriv_eq`,
  `Filter.EventuallyEq.extDerivWithin_eq_nhds`,
  `extDerivWithin_congr`, `extDerivWithin_congr'`.
- Exterior derivative pullback:
  `extDeriv_pullback` and `extDerivWithin_pullback`.
  These are the true mathlib route for `d(f^* omega) = f^*(d omega)`.
- Smoothness transport:
  `ContDiffOn.mono`, `ContDiffOn.congr`, `ContDiffOn.comp`,
  `ContDiffOn.prodMk`, `ContDiffOn.smul`,
  `ContDiffOn.clm_comp`, `ContDiffOn.clm_apply`.
- Alternating form pullback smoothness:
  project wrapper `ContinuousAlternatingMap.contDiffOn_compContinuousLinearMap`
  already packages the smoothness of
  `(eta, L) ↦ eta.compContinuousLinearMap L`.
- Manifold chart-change smoothness:
  mathlib provides `contDiffOn_ext_coord_change` and
  `contDiffOn_fderiv_coord_change`; project wrappers expose these as
  `ManifoldForm.contDiffOn_chartTransition` and
  `ManifoldForm.contDiffOn_chartTransitionDeriv`.
- Transition-pullback smoothness:
  `ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_chartAPI`
  now packages the route from chartwise smoothness plus chart-change API.
- Finite-dimensional cutoff functions:
  `exists_contDiff_tsupport_subset` gives a smooth compactly supported bump in
  any neighborhood of a point.
  `IsOpen.exists_contDiff_support_eq` gives a smooth function with prescribed
  open support.

## Main Gap

The missing theorem is not `extDeriv` or chart-change smoothness. It is the
local extension/globally smooth cutoff step:

```text
ContDiffOn Real top omega U
K compact/closed, K subset U open
----------------------------------
exists omegaExt, ContDiff Real top omegaExt
  and EqOn omegaExt omega on a neighborhood of K
```

For our singular bridge, `K` should be `cubeAndFacesImage cube`, or a compact
closed superset of it.

The likely proof route is:

1. Prove `cubeAndFacesImage cube` is compact from continuity of the smooth cube
   and compactness of the parameter cube/faces.
2. Choose an open `V` with `K subset V` and `closure V subset U`, or choose a
   cutoff `chi` with `chi = 1` near `K` and `tsupport chi subset U`.
3. Define `omegaExt y = chi y • omega y`.
4. Prove global `ContDiff` by using `ContDiffOn.smul` on `U` and local zero
   behavior off `tsupport chi`.
5. Use `chi = 1` near `K` to obtain the `EqOn` field required by
   `ChartwiseSingularCubeCoreExtensionInput`.

## Recommended Next Step

Prove a reusable Euclidean cutoff-extension lemma for forms:

```text
exists_euclideanForm_extension_eqOn_nhds_of_contDiffOn
```

with input `ContDiffOn Real top omega U`, `IsOpen U`, and compact/closed
`K subset U`, returning a `ChartwiseSingularCubeCoreExtensionInput`-compatible
extension package. This is the shortest path from local chart smoothness to
smooth singular Stokes without changing the public facade.
