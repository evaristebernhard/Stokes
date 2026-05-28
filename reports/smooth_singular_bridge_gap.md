# Smooth Singular Bridge Gap

Worker scope: analyze the smooth singular cube route and its bridge to the
current manifold/chart-box Stokes route.  No GPL prior-art code was copied; the
external development is referenced only by declaration names and design shape.

## Files inspected

- `Stokes/SingularCube.lean`
- `Stokes/SingularCube/ManifoldBridge.lean`
- `Stokes/ManifoldForm.lean`
- `external/lean-stokes-theorem/LeanStokes/CubeStokes/Bridge.lean`
- `external/lean-stokes-theorem/LeanStokes/SingularCubeStokes/*.lean`
- representative current global endpoints:
  `Stokes/Global/NaturalCompactSupportStokesStatement.lean`,
  `Stokes/Global/CanonicalNaturalCompactSupport.lean`,
  `Stokes/Global/CompactSupportEndpointFacade.lean`

I also added the safe facade
`Stokes/SingularCube/SmoothBridgeFacade.lean`.  It only packages existing
bridge data and theorem calls; it does not change existing imports and does not
claim to solve the local-to-global smoothness gap.

## Current bridge inventory

The local project already exposes the prior-art smooth singular layer under the
`Stokes` namespace:

- `SmoothSingularCube n m`
- `EuclideanForm m k`
- `pullbackForm`
- `integrateForm`
- `singularFace`
- `SingularChain`
- `singularBoundarySingle`
- `singularBoundary`
- `integrateChain`
- `singular_pullback_extDeriv`
- `singular_cube_stokes`
- `singular_cube_boundary_stokes`
- `singular_cube_chain_stokes`
- `singular_chain_stokes`
- `singular_boundary_boundary_zero`
- `singular_boundary_boundary_zero_general`

The clean-room manifold bridge already has the right first abstraction:

- `singularParameterCube`
- `chartLocalForm`
- `chartCubeMap`
- `chartCubePullback`
- `ChartSingularCubeLocalData`
- `ChartSingularCubeLocalData.ofChartwiseSmooth`
- `ChartSingularCubeLocalData.localForm_contDiffOn_of_subset`
- `ChartSingularCubeLocalData.singular_pullback_extDeriv_local`
- `ChartSingularCubeLocalData.singular_chain_stokes_local`
- `ChartSingularCubeLocalData.singular_boundary_stokes_local`

The manifold-form side provides the chart API needed to make the bridge
mathlib-compatible:

- `ManifoldForm.inChart`
- `ManifoldForm.ChartwiseSmooth`
- `ManifoldForm.inChart_chartTransition`
- `ManifoldForm.transitionPullbackInChart`
- `ManifoldForm.contDiffOn_transitionPullbackInChart_of_contDiffOn`
- `ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart`
- `ManifoldForm.chartTransitionDeriv_eq_fderivWithin`
- `ManifoldForm.contDiffOn_chartTransitionDeriv`

The external prior-art declarations most relevant to this route are:

- `SingularCubeStokes.SmoothSingularCube`
- `SingularCubeStokes.pullbackForm`
- `SingularCubeStokes.integrateForm`
- `SingularCubeStokes.pullback_extDeriv`
- `SingularCubeStokes.singularStokes`
- `SingularCubeStokes.stokes_singular_boundary`
- `SingularCubeStokes.stokes_singular_chain`
- `SingularCubeStokes.stokes_chain`
- `CubeStokes.toCoordNForm`
- `CubeStokes.extDeriv_topCoeff_eq_extDerivCoord`
- `CubeStokes.toCoordNForm_smooth`

The current global/chart-box route is much farther along for compact-support
manifold integration.  Its user-facing endpoints are records such as
`NaturalCompactSupportStokesInput` and public facades such as
`CompactSupportEndpointSource` / `CompactSupportEndpointExtDerivSource`.
Those should not be imported into the singular bridge layer; the singular route
should stay a parallel layer until there is a genuine theorem connecting
singular chains to the manifold integral interface.

## Can the smooth singular route proceed in parallel?

Yes.  It is largely independent of the current endpoint internals.

The chart-box/global route is currently solving analytic localization of
manifold integrals: compact support, partition localization, half-space boundary
charts, boundary change of variables, and artificial-face cancellation.

The smooth singular route instead needs:

1. A manifold-valued smooth singular cube/chains API.
2. A chart-local expression of pullbacks of manifold forms.
3. Local-to-global or localized singular Stokes for chart representatives.
4. Chart-change invariance of the singular integral.
5. Eventually a fundamental-chain or triangulation/chain model if this route is
   meant to prove the same global manifold Stokes theorem.

So it is a useful parallel track, especially for sign conventions, exterior
derivative naturality, chain boundary algebra, and chart-change invariance.
It does not immediately remove the need for the chart-box/global route, because
the final compact-support manifold integral theorem still needs measure-level
integration and boundary orientation.  But it can provide a second verified
route to parametrized local Stokes and a cleaner API for smooth chains.

## Main mismatch

`ChartSingularCubeLocalData` records the natural hypothesis produced by the
manifold route:

```lean
ContDiffOn Real top (chartLocalForm I chart omega) smoothSet
```

But the imported singular theorem currently requires:

```lean
ContDiff Real top (chartLocalForm I chart omega)
```

That is the real bridge gap.  The existing wrappers are honest about this:
`singular_chain_stokes_local` and `singular_boundary_stokes_local` still take a
global smoothness hypothesis.  The facade added in this worker keeps the same
gap explicit under shorter theorem names:

- `chartSingularCubeLocalDataOfChartwiseSmooth`
- `chartwise_singular_boundary_stokes_of_globalSmooth`
- `chartwise_singular_chain_stokes_of_globalSmooth`

## Next minimal theorem

The next smallest theorem should not try to prove global manifold Stokes.
It should remove the global smoothness hypothesis from the chart-local singular
Stokes call by assuming a controlled smooth extension of the chart
representative.

Recommended statement shape:

```lean
theorem ChartSingularCubeLocalData.singular_boundary_stokes_local_of_extension
    {n m : Nat} {I : ModelWithCorners Real (Fin m -> Real) H}
    {omega : ManifoldForm I M n}
    (D : ChartSingularCubeLocalData (d := n + 1) I omega)
    (omegaExt : EuclideanForm m n)
    (homegaExt : ContDiff Real top omegaExt)
    (homega_eq : EqOn omegaExt D.localForm D.smoothSet)
    (hdomega_eq :
      EqOn (fun y => extDeriv omegaExt y)
           (fun y => extDeriv D.localForm y) D.smoothSet) :
    SingularCubeStokes.bdryIntegral_singular D.cube D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y)
```

There should be a chain-level companion:

```lean
theorem ChartSingularCubeLocalData.singular_chain_stokes_local_of_extension
    ... :
    integrateChain (singularBoundarySingle D.cube) D.localForm =
      integrateForm D.cube (fun y => extDeriv D.localForm y)
```

Why this is the right next theorem:

- It is small enough to prove from existing singular Stokes plus congruence of
  the integrands.
- It makes the true analytic extension problem explicit and reusable.
- It avoids pulling current global endpoint internals into the singular route.
- It gives later agents a precise target for cutoff/extension lemmas.

The theorem will need two small support facts:

- face inclusions with `epsilon = 0` or `epsilon = 1` map
  `singularParameterCube n` into `singularParameterCube (n + 1)`;
- therefore every face of `D.cube` maps its parameter cube into `D.smoothSet`.

## Reusable declarations

Already reusable without touching endpoint internals:

- Pullback and integration:
  `pullbackForm`, `integrateForm`, `integrateChain`.
- Boundary and face algebra:
  `singularFace`, `singularBoundarySingle`, `singularBoundary`,
  `singular_boundary_boundary_zero_general`.
- Stokes and naturality:
  `singular_pullback_extDeriv`, `singular_cube_boundary_stokes`,
  `singular_cube_chain_stokes`, `singular_chain_stokes`.
- Manifold chart expression:
  `chartLocalForm`, `chartCubePullback`, `chartCubeMap`,
  `ChartSingularCubeLocalData`.
- Chart smoothness:
  `ManifoldForm.ChartwiseSmooth.contDiffOn_inChart`,
  `ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart`,
  `ManifoldForm.inChart_chartTransition`.

## Missing API

Small missing API:

- `faceInclusion` maps the unit cube into the unit cube for faces `0` and `1`.
- Congruence lemmas for `pullbackForm`, `integrateForm`,
  `bdryIntegral_singular`, and `integrateChain` under equality on the relevant
  cube image.
- A local version of singular Stokes from a smooth extension record, as stated
  above.
- A public facade module for singular bridge imports.  This worker added the
  first one.

Medium missing API:

- A `ManifoldSmoothSingularCube` record: a map from the parameter cube to `M`,
  plus local chart coordinate representatives and chartwise smoothness.
- Chart-change invariance of singular integrals:
  if two chart representatives describe the same manifold-valued cube, their
  pullback integrands agree after the derivative chain rule and
  `ManifoldForm.inChart_chartTransition`.
- A clean orientation/sign compatibility lemma between singular cubical
  boundary signs and the boundary chart orientation API.

Large missing API/mathlib work:

- Smooth cutoff or extension theorem for model-space form-valued functions:
  from `ContDiffOn` on an open neighborhood of a compact cube image, construct
  or assume a global smooth form agreeing near the image.
- If the singular route is meant to prove full manifold Stokes independently:
  smooth triangulations/fundamental chains or a cubical chain model for compact
  oriented manifolds with boundary.
- A licensing decision if the project keeps `LeanStokes` as a required Lake
  dependency.  The current work uses it as a pinned dependency and does not copy
  source into `Stokes/`, but publication/reuse policy should be explicit.

## Relation to current global endpoints

The existing global endpoint stack should not be a dependency of
`Stokes/SingularCube/*`.

Possible future connection points are:

- Use smooth singular chains as an alternate representation of local boundary
  pieces, then compare their integrals with chart-box integrals.
- Use singular chain Stokes as a verification harness for sign conventions:
  compare `(-1)^i` cubical signs with `halfSpaceBoundarySign n` and the current
  outward-first orientation bridge.
- Use chart-change invariance for singular integrals as a smaller pilot theorem
  before proving full boundary COV invariance in the measure-level route.

But the singular bridge should remain a separate layer until it has localized
Stokes and chart-change invariance.

## Next wave: three non-overlapping tasks

1. `Stokes/SingularCube/FaceAPI.lean`

   Prove unit-cube face inclusion facts and their consequences for
   `ChartSingularCubeLocalData`:
   face parameter cube maps into the parameter cube, face cubes land in
   `D.smoothSet`, and face cubes land in the selected chart target.

2. `Stokes/SingularCube/IntegralCongruence.lean`

   Prove congruence lemmas for `pullbackForm`, `integrateForm`,
   `bdryIntegral_singular`, and `integrateChain` under `EqOn` assumptions on
   cube images and face images.  This task should not touch manifold forms.

3. `Stokes/SingularCube/LocalExtension.lean`

   Combine the first two tasks with existing singular Stokes to prove
   `ChartSingularCubeLocalData.singular_boundary_stokes_local_of_extension`
   and the chain-level companion.  This file should assume the extension record
   or explicit `omegaExt` hypotheses; constructing the extension by cutoff is a
   later analytic task.

These three tasks are disjoint and can run in parallel with the endpoint
strict-buffer/localized-box work because they only depend on
`Stokes.SingularCube`, `Stokes.SingularCube.ManifoldBridge`, and
`Stokes.ManifoldForm`.

