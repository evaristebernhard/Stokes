# Lean 4 Stokes Formalization Workspace

This repository is pivoting to a Lean 4 formalization project for Stokes'
theorem, with the long-term target including smooth manifolds with boundary.

## Current Direction

Working goal:

```text
local Euclidean Stokes -> differential-form integration -> manifold Stokes
```

The project should build on mathlib's existing analysis, differential-form, and
smooth-manifold infrastructure. The first milestones are Euclidean box Stokes,
smooth singular cubes, and a clean bridge to mathlib's `extDeriv`; the later
milestones add chartwise integration, orientation, boundary orientation, and
global manifold integration.

See [ROADMAP.md](ROADMAP.md) for the external progress review and staged plan.

## Current Lean Baseline

The root Lake project is pinned to Lean 4.29.1 and imports the LeanStokes prior
artifact at commit `adffb99be9fd00a42369561068c9d11475cbedb8`.

The first project modules are:

```text
Stokes.Box
Stokes.SingularCube
Stokes.ManifoldForm
Stokes.HalfSpace
```

They expose the current baseline theorems under the `Stokes` namespace:

- `Stokes.box_stokes_on_box`
- `Stokes.box_stokes_extDeriv_smooth`
- `Stokes.singular_pullback_extDeriv`
- `Stokes.singular_cube_stokes`
- `Stokes.singular_cube_boundary_stokes`
- `Stokes.singular_cube_chain_stokes`
- `Stokes.singular_chain_stokes`
- `Stokes.singular_boundary_boundary_zero`
- `Stokes.singular_boundary_boundary_zero_general`
- `Stokes.ModelForm`
- `Stokes.ManifoldForm`
- `Stokes.ManifoldForm.inChart`
- `Stokes.ManifoldForm.inChart_chartTransition`
- `Stokes.ContinuousAlternatingMap.contDiffOn_compContinuousLinearMap`
- `Stokes.ManifoldForm.contDiffOn_chartTransition`
- `Stokes.ManifoldForm.contDiffOn_chartTransitionDeriv`
- `Stokes.ManifoldForm.chartTransitionDeriv_eq_fderivWithin`
- `Stokes.ManifoldForm.contDiffOn_transitionPullbackInChart_of_contDiffOn`
- `Stokes.ManifoldForm.contDiffOn_inChart_of_transitionPullback`
- `Stokes.ManifoldForm.contDiffOn_transitionPullbackInChart_of_contDiffOn_inChart`
- `Stokes.ManifoldForm.contDiffOn_transitionPullbackInChart_iff`
- `Stokes.ManifoldForm.pullback`
- `Stokes.ManifoldForm.ChartwiseSmooth`
- `Stokes.ManifoldForm.ChartwiseSmooth.contDiffOn_inChart`
- `Stokes.ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_contDiffOn`
- `Stokes.ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_chartAPI`
- `Stokes.ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart`
- `Stokes.boundaryInclusion`
- `Stokes.outwardNormal`
- `Stokes.boundaryTangentInclusion`
- `Stokes.boundaryTangentProjection`
- `Stokes.det_outwardFirstBoundaryMatrix`
- `Stokes.coordinateOrientationSign`
- `Stokes.outwardFirstBoundaryOrientationSign`
- `Stokes.halfSpaceBoundarySign_eq_outwardFirstBoundaryOrientationSign`
- `Stokes.halfSpaceBoundarySign_eq`
- `Stokes.outwardFirstHalfSpaceBoundaryFormIntegral`
- `Stokes.boundaryTangentPullbackForm`
- `Stokes.boundaryTangentPullbackForm_comp_apply_basisFun_eq_det_mul`
- `Stokes.ambientBoundaryForm_tangentMap_eq_det_mul`
- `Stokes.boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain`
- `Stokes.boxUpperCoordFaceTerm`
- `Stokes.boxLowerCoordFaceTerm`
- `Stokes.boxUpperFormFaceIntegral`
- `Stokes.boxLowerFormFaceIntegral`
- `Stokes.halfSpaceSupportBox`
- `Stokes.boxFaceCoeffTSupportInHalfSpaceBox`
- `Stokes.boxFormFaceCoeff_tsupport_subset`
- `Stokes.boxFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset`
- `Stokes.toCoordNForm_contDiffOn`
- `Stokes.exists_halfSpaceSupportBox_of_isCompact`
- `Stokes.boxRemainingFormFaceTerms`
- `Stokes.boxRemainingFormFaceTerms_eq_zero_of_face_cancellation`
- `Stokes.boxRemainingFormFaceTerms_eq_zero_of_support_disjoint`
- `Stokes.boxRemainingFormFaceTerms_eq_zero_of_tsupport_disjoint`
- `Stokes.boxRemainingFormFaceTerms_eq_zero_of_tsupport_subset_halfSpaceSupportBox`
- `Stokes.bdryIntegral_eq_lowerZero_add_remaining`
- `Stokes.box_stokes_extDeriv_contDiffOn_isOpen`
- `Stokes.halfSpaceLocalStokes_with_remainder`
- `Stokes.halfSpaceLocalStokes_with_remainder_of_contDiffOn_isOpen`
- `Stokes.halfSpaceLocalStokes_of_remainder_eq_zero`
- `Stokes.halfSpaceLocalStokes_of_remainder_eq_zero_of_contDiffOn_isOpen`
- `Stokes.halfSpaceLocalStokes_of_face_cancellation`
- `Stokes.halfSpaceLocalStokes_of_support_disjoint`
- `Stokes.halfSpaceLocalStokes_of_tsupport_disjoint`
- `Stokes.halfSpaceLocalStokes_compactSupport`
- `Stokes.halfSpaceLocalStokes_compactSupport_of_contDiffOn_isOpen`
- `Stokes.localHalfSpaceStokes_compactSupport`
- `Stokes.localHalfSpaceStokes_compactSupport_of_contDiffOn_isOpen`
- `Stokes.boxLowerZeroCoordFaceTerm_toCoordNForm_eq_halfSpaceBoundaryFormTerm`
- `Stokes.boxFaceCoeffTSupportInHalfSpaceBox_transitionPullback_of_tsupport_subset`
- `Stokes.halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset`
- `Stokes.exists_halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox_of_isCompact`
- `Stokes.boundaryChartDomain`
- `Stokes.boundaryChartSelectedBox`
- `Stokes.boundaryChartExtendedBox`
- `Stokes.boundaryChartTransition`
- `Stokes.boundaryChartTransitionTangentMap`
- `Stokes.boundaryChartTransitionMatrix`
- `Stokes.boundaryChartTransitionJacobian`
- `Stokes.boundaryChartTransitionPreservesBoundaryAt`
- `Stokes.boundaryChartTransitionDerivPreservesTangentAt`
- `Stokes.boundaryChartTransition_pointwise_pullback_det`
- `Stokes.boundaryChartTransitionCompatibleOn`
- `Stokes.boundaryChartOrientationCompatibleOn`
- `Stokes.boundaryChartTransitionJacobianIntegrand`
- `Stokes.boundaryChartOrientedChangeOfVariables`
- `Stokes.halfSpaceBoundaryTransitionFormIntegral_eq_inChart_of_orientedChangeOfVariables`
- `Stokes.outwardFirstBoundaryChartIntegral_eq_inChart_of_orientedChangeOfVariables`
- `Stokes.halfSpaceBoundaryInChartIntegral`
- `Stokes.outwardFirstBoundaryInChartIntegral`
- `Stokes.boundaryChartChangeCompatible`
- `Stokes.halfSpaceBoundaryTransitionFormIntegral_eq_inChart_of_boundaryFace_subset_overlap`
- `Stokes.outwardFirstBoundaryChartIntegral_eq_inChart_of_boundaryFace_subset_overlap`
- `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant`
- `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant_of_selectedBoxes`
- `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant_of_extendedBoxes`
- `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables`
- `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_selected`
- `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_extended`
- `Stokes.contDiffOn_transitionPullbackInChart_upperHalfSpaceBoundary`
- `Stokes.contDiffOn_transitionPullbackInChart_halfSpaceBox`
- `Stokes.boxLowerZeroCoordFaceTerm_transitionPullback_eq_halfSpaceBoundaryTransitionFormTerm`
- `Stokes.halfSpaceLocalStokes_transitionPullback_with_remainder`
- `Stokes.halfSpaceLocalStokes_transitionPullback_of_remainder_eq_zero`
- `Stokes.halfSpaceLocalStokes_transitionPullback_of_face_cancellation`
- `Stokes.halfSpaceLocalStokes_transitionPullback_of_support_disjoint`
- `Stokes.halfSpaceLocalStokes_transitionPullback_of_tsupport_disjoint`
- `Stokes.halfSpaceLocalStokes_transitionPullback_compactSupport`
- `Stokes.halfSpaceLocalStokes_transitionPullback_compactSupport_of_contDiffOn_isOpen`
- `Stokes.localHalfSpaceStokes_transitionPullback_compactSupport`
- `Stokes.localHalfSpaceStokes_transitionPullback_compactSupport_of_contDiffOn_isOpen`
- `Stokes.boundaryChartLocalStokes_transitionPullback_compactSupport`
- `Stokes.boundaryChartLocalStokes_transitionPullback_compactSupport_eq`
- `Stokes.outwardFirstBoundaryChartIntegral`
- `Stokes.outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul`
- `Stokes.boundaryChartLocalStokes_transitionPullback_of_extendedBox`
- `Stokes.boundaryChartLocalStokes_transitionPullback_of_extendedBox_package`
- `Stokes.boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst`
- `Stokes.boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst_package`

Build and check:

```text
lake build
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

The LeanStokes dependency is GPL-3.0-only. This repository currently imports it
as a pinned Lake dependency rather than copying its source.

## Archive

The previous nodal-surface project has been archived at:

```text
archive/nodal-surfaces/
```

It contains the old Rust workspace, documents, arXiv references, search notes,
and degree02-degree08 reproduction code. Treat it as historical material, not as
the active project root.

To inspect or rerun the old workspace:

```text
cd archive/nodal-surfaces
cargo test --workspace
```

## Near-Term Plan

1. Decide the repository license strategy around the GPL-3.0-only dependency.
2. Lift the M5.1 outward-normal-first sign bridge toward chart-change
   invariance for oriented boundary integrals.
3. Keep public APIs mathlib-native and avoid leaking coordinate-only helper
   types into future manifold-facing statements.
