# Stokes M7 Proof Obligations

Scope: report-only audit for the current Lean 4 Stokes workspace.  No Lean
source files were changed.

Date: 2026-05-24.

This report lists the remaining theorem obligations between the current global
assembly API and a general smooth-manifold Stokes theorem.  The intended
granularity is "parallel worker claim size": each item should be small enough
for one worker to own without also owning the final assembly theorem.

## Status Legend

- `PROVED`: the current Lean file contains a real proof of the stated local,
  algebraic, or API theorem.  It may still depend on explicit mathematical
  hypotheses, but the theorem itself is not merely a record field.
- `FIELD`: the current API stores the obligation as a structure field or an
  explicit hypothesis.  This is the main remaining work category.
- `WRAPPER`: the current theorem is field alignment, projection, finite-sum
  bookkeeping, or a final wrapper over already supplied fields.  It is not a
  mathematical proof obligation by itself.

Mixed rows are written as `PROVED + FIELD`: the algebraic bridge is proved,
but the geometric or analytic input feeding it remains fieldized.

## Current Endpoint

The nearest user-facing endpoint is:

```lean
Stokes.naturalGlobalStokes
  (D : NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece) :
  D.globalBulkIntegral = D.globalBoundaryIntegral
```

Current path:

```text
NaturalGlobalStokesInput
  -> SelectedMixedGlobalInput
  -> MixedGlobalStokesData
  -> GlobalStokesData
  -> GlobalStokesData.stokes
```

`GlobalStokesData.stokes`, `mixedGlobalStokes`,
`selectedMixedGlobalStokes`, and `naturalGlobalStokes` are pure assembly once
their data records are populated.  The remaining work is to replace the
fieldized data-record inputs by theorems derived from compact support,
partitions of unity, local chart geometry, orientation, and manifold
integration definitions.

## Top-Level Field Map

| Final field or package | Current status | Primary file | Remaining theorem owner |
|---|---:|---|---|
| `GlobalStokesData.globalBulkIntegral_eq_localBulkSum` | `FIELD` | `Stokes/Global/Theorem.lean`; `Stokes/Global/IntegralReconstruction.lean`; `Stokes/Global/BulkIntegralPartitionReconstruction.lean` | Global top-degree bulk integral localization. |
| `GlobalStokesData.globalBoundaryIntegral_eq_boundaryPartitionSum` | `FIELD` | `Stokes/Global/Theorem.lean`; `Stokes/Global/BoundaryIntegralReconstruction.lean`; `Stokes/Global/BoundaryIntegralPartitionReconstruction.lean` | Boundary integral reconstruction from chart-local partition terms. |
| `GlobalStokesData.interiorLocalStokes` | `PROVED + FIELD` | `Stokes/Global/InteriorLocalStokes.lean`; `Stokes/Global/LocalizedInteriorPieces.lean` | Local theorem is proved; construct all localized piece data from final partition. |
| `GlobalStokesData.boundaryLocalStokes` | `PROVED + FIELD` | `Stokes/Global/LocalIntegral.lean`; `Stokes/Global/BoundaryPieceFamilyConstructor.lean`; `Stokes/BoundaryChart/LocalStokes.lean` | Local theorem is proved; construct all boundary pieces from final boundary cover. |
| `GlobalStokesData.interiorBoundaryCancellation` | `PROVED + FIELD` | `Stokes/Global/Cancellation.lean`; `Stokes/Global/ArtificialFace*.lean` | Finite cancellation is proved; construct the actual artificial-face pairing. |
| `GlobalStokesData.chartChangeCancellation` | `PROVED + FIELD` | `Stokes/Global/ChartChange.lean`; `Stokes/BoundaryChart/ChangeOfVariablesFamily.lean`; `Stokes/Global/BoundaryCOVToChartChange.lean` | Finite chart-change sum is proved; construct COV data and align target terms. |
| `NaturalGlobalStokesInput.globalBulkIntegral_eq_reconstruction` | `FIELD` | `Stokes/Global/NaturalStatement.lean` | Identify the user-facing bulk integral with the selected reconstruction package. |
| `NaturalGlobalStokesInput.globalBoundaryIntegral_eq_reconstruction` | `FIELD` | `Stokes/Global/NaturalStatement.lean` | Identify the user-facing boundary integral with the selected reconstruction package. |
| Final theorem wrappers | `WRAPPER` | `Stokes/Global/Theorem.lean`; `Stokes/Global/MixedGlobalConstructor.lean`; `Stokes/Global/MixedSelectedConstructor.lean`; `Stokes/Global/NaturalStatement.lean` | No theorem obligation beyond populating input records. |

## Parallel Obligation Backlog

### A. Natural Statement And Genuine Integrals

| ID | Status | Claimable theorem target | Files and fields | Notes |
|---|---:|---|---|---|
| M7-NAT-01 | `FIELD` | Define the first genuine user-facing compact-support theorem, e.g. `naturalGlobalStokes_compactSupport` or `globalStokes_compactSupport`, whose inputs are an oriented smooth manifold with boundary, compactly supported `omega`, and the actual definitions of `integral_M (d omega)` and `integral_boundary_M omega`. | New or existing `Stokes/Global/NaturalStatement.lean`; fields `NaturalGlobalStokesInput.globalBulkIntegral`, `globalBoundaryIntegral`. | This is the theorem-shape owner.  It should not reprove local Stokes; it should assemble the theorem once obligations below produce a `NaturalGlobalStokesInput`. |
| M7-NAT-02 | `FIELD` | Prove `globalBulkIntegral_eq_reconstruction` for the genuine bulk integral. | `Stokes/Global/NaturalStatement.lean`; `NaturalGlobalStokesInput.globalBulkIntegral_eq_reconstruction`; bulk reconstruction packages below. | Depends on M7-BULK-01/02. |
| M7-NAT-03 | `FIELD` | Prove `globalBoundaryIntegral_eq_reconstruction` for the genuine boundary integral. | `Stokes/Global/NaturalStatement.lean`; `NaturalGlobalStokesInput.globalBoundaryIntegral_eq_reconstruction`; boundary reconstruction packages below. | Depends on M7-BDR-05/06. |
| M7-NAT-04 | `WRAPPER` | Add a constructor such as `NaturalGlobalStokesInput.ofSelectedMixedInput` after M7-NAT-02/03 exist. | `Stokes/Global/NaturalStatement.lean`. | Pure record construction; useful only after the genuine integral equalities are available. |

### B. Compact Partition And Localized Form Reconstruction

| ID | Status | Claimable theorem target | Files and fields | Notes |
|---|---:|---|---|---|
| M7-PART-01 | `PROVED` | Existence of a smooth partition of unity subordinate to chart sources. | `Stokes/Global/Partition.lean`; theorem `exists_smoothPartitionOfUnity_subordinate_chartAt_source`. | Already proved from mathlib. |
| M7-PART-02 | `PROVED` | Finite active set over compact support. | `Stokes/Global/FiniteActive.lean`; `finiteActiveSupportSet_finite`; `FiniteActiveOnCompact.ofCompact`; `FiniteActiveOnCompact.coeff_sum_eq_one_on` in `PartitionSumOne.lean`. | Already proves finite activity and sum-one on `K`. |
| M7-PART-03 | `FIELD` | Construct `SelectedBoxPartitionOfUnity` or `CompactActiveExtendedBoxData` from compact support, chart-source subordination, and chartwise smoothness. | `Stokes/Global/Partition.lean`; `SelectedBoxPartitionOfUnity.box`.  `Stokes/Global/CompactActiveBoxes.lean`; fields `Icc_subset_target`, `Icc_subset_overlap`, smooth-neighborhood fields. | The compact coordinate boxes exist, but fitting them into chart targets/overlaps and smooth neighborhoods is still explicit. |
| M7-PART-04 | `PROVED + FIELD` | Use coefficient sum-one on the relevant support to build `LocalizedFormReconstructionFields`. | `Stokes/Global/ReconstructionWrappers.lean`; `LocalizedFormReconstructionFields.ofCoeffSumEqOneOn`; `Stokes/Global/PartitionSumOne.lean`. | The wrapper is proved; the final support set and support membership theorem still need to be chosen. |
| M7-PART-05 | `FIELD` | Prove localized finite sum equals the original form on the exact support needed for bulk and boundary reconstruction. | `Stokes/Global/Reconstruction.lean`; theorem `localizedFormSum_eqOn_of_coeff_sum_eq_one_on`; `Stokes/Global/SupportFiniteSum.lean`. | This should specialize M7-PART-04 to compact support of `omega` or `d omega`, avoiding unnecessary everywhere hypotheses. |

### C. Exterior Derivative Reconstruction

| ID | Status | Claimable theorem target | Files and fields | Notes |
|---|---:|---|---|---|
| M7-EXT-01 | `PROVED` | Exterior derivative commutes with finite sums of differentiable model forms. | `Stokes/Global/ExtDerivOnSupport.lean`; theorem `extDeriv_finset_sum`; `extDeriv_transitionPullbackInChart_localizedFormSum`. | Algebraic finite-sum part is done. |
| M7-EXT-02 | `PROVED` | Local equality of model representatives implies equality of `extDeriv`. | `Stokes/Global/ExtDerivEventually.lean`; `extDeriv_eq_of_eventuallyEq`; `extDeriv_transitionPullbackInChart_eq_of_eventuallyEq`. | Done as a locality theorem for `extDeriv`. |
| M7-EXT-03 | `FIELD` | Fill `ExtDerivEventuallyEqData.chartwiseEventuallyEq_on` from partition sum-one on a neighborhood/support. | `Stokes/Global/ExtDerivEventually.lean`; field `chartwiseEventuallyEq_on`. | A good target theorem is `ExtDerivEventuallyEqData.ofPartitionSumOneOnSupport`. |
| M7-EXT-04 | `FIELD` | Fill `ExtDerivOnSupportData.chartwiseExtDeriv_eq_global_on` for compact support. | `Stokes/Global/ExtDerivOnSupport.lean`; field `chartwiseExtDeriv_eq_global_on`; constructor `ofCompactSupport`. | Can be proved either directly or through M7-EXT-03. |
| M7-EXT-05 | `WRAPPER` | Promote on-support reconstruction to `ExtDerivPartitionReconstructionData` when the support cover hypothesis is supplied. | `Stokes/Global/ExtDerivOnSupport.lean`; `toExtDerivPartitionReconstructionData`. | Pure projection once `hcover` is known. |

### D. Bulk Integral Reconstruction

| ID | Status | Claimable theorem target | Files and fields | Notes |
|---|---:|---|---|---|
| M7-BULK-01 | `FIELD` | Prove the genuine bulk integral localizes to the finite interior plus boundary bulk sums. | `Stokes/Global/IntegralReconstruction.lean`; field `BulkIntegralReconstructionData.globalBulkIntegral_eq_localBulkSum`.  `Stokes/Global/BulkIntegralPartitionReconstruction.lean`; fields `SplitBulkIntegralReconstructionInput.bulkIntegralLocalizes`, `BulkIntegralPartitionInput.bulkIntegralLocalizes`. | This is one of the two largest analytic obligations.  It should use finite partition reconstruction, support restriction, linearity, and chart integration definitions. |
| M7-BULK-02 | `FIELD` | Identify each interior localized bulk term with the chart integral of `d(rho_i * omega)`. | `Stokes/Global/LocalizedInteriorPieces.lean`; `bulkTerm`.  `Stokes/Global/InteriorLocalStokes.lean`; `projectInteriorBulkIntegral`. | Local wrappers exist; the missing part is their equality to the global integral contribution under the chosen manifold-integration definition. |
| M7-BULK-03 | `FIELD` | Identify each boundary-chart bulk term with the boundary chart contribution to the global bulk integral. | `Stokes/Global/BoundaryPieceFamilyConstructor.lean`; `boundaryBulkTerm`; `BoundaryPieceFamilyInput.boundaryBulkSum`. | Needed when boundary collar/chart pieces contribute to the bulk side near the boundary. |
| M7-BULK-04 | `WRAPPER` | Convert separated bulk reconstruction plus boundary fields to `PartitionReconstructionData` and `MixedGlobalStokesData`. | `Stokes/Global/IntegralReconstruction.lean`; `BulkIntegralReconstructionData.toPartitionReconstructionData`; `toMixedGlobalStokesData`. | Already pure record alignment. |

### E. Interior Local Pieces And Artificial Faces

| ID | Status | Claimable theorem target | Files and fields | Notes |
|---|---:|---|---|---|
| M7-INT-01 | `PROVED` | Interior chart local Stokes on an extended box. | `Stokes/Global/InteriorLocalStokes.lean`; theorem `projectInteriorLocalStokes_of_extendedBox`; package `InteriorLocalStokesData.ofExtendedBox`. | This is a true local theorem via box Stokes. |
| M7-INT-02 | `FIELD` | Construct `LocalizedInteriorPieces` from the selected partition, compact support, coefficient support control, and localized smoothness. | `Stokes/Global/LocalizedInteriorPieces.lean`; structure fields `active`, `coefficient`, `piece`.  `Stokes/Global/LocalizedSupport.lean`; `LocalizedSupportControl`.  `Stokes/Global/LocalizedSmoothness.lean`. | The target theorem can be `LocalizedInteriorPieces.ofSelectedBoxPartitionOfUnity` or similar. |
| M7-INT-03 | `PROVED + FIELD` | Adapt localized interior pieces to `MixedInteriorPackage`. | `Stokes/Global/InteriorPieceFamilyConstructor.lean`; `LocalizedInteriorMixedInput.toMixedInteriorPackage`; `LocalizedInteriorPieces.toMixedInteriorPackage`. | The adapter is proved.  It still waits on M7-INT-02 to produce actual pieces. |
| M7-INT-04 | `FIELD` | Decompose each selected interior box artificial boundary term into finitely many face terms. | `Stokes/Global/ArtificialFaceSelection.lean`; field `SelectedBoxArtificialFaceFamilyData.boundaryTerm_eq_faceSum`. | Expected theorem: expand `projectInteriorBoundaryIntegral` into coordinate face terms for the chosen face index family. |
| M7-INT-05 | `FIELD` | Construct the actual pairing of artificial faces from the selected interior decomposition. | `Stokes/Global/ArtificialFaceAdjacency.lean`; fields `pair`, `pair_mem`, `pair_involutive`, `paired_coordinateFace_opposite`, `paired_geometricFace_eq`, `paired_unsignedFaceTerm_eq`.  Also `Stokes/Global/ArtificialFaceOverlapPairing.lean`. | This is the geometric overlap/pairing theorem for adjacent artificial faces. |
| M7-INT-06 | `PROVED` | Given paired artificial faces, cancel the total artificial boundary sum. | `Stokes/Global/Cancellation.lean`; `Stokes/Global/ArtificialFacePairing.lean`; `Stokes/Global/ArtificialFaceGeometry.lean`; `Stokes/Global/ArtificialFaceOverlapPairing.lean`. | Finite-sum cancellation and signed/unsigned cancellation are true-proved. |
| M7-INT-07 | `WRAPPER` | Convert artificial face data to `GlobalStokesData.interiorBoundaryCancellation`. | `Stokes/Global/ArtificialFaceSelection.lean`; theorems `GlobalStokesData.interiorBoundaryCancellation_of_selectedBoxArtificialFaces*`; `SelectedMixedGlobalInput.interiorBoundaryCancellation`. | Pure once the artificial-face family is constructed. |

### F. Boundary Local Pieces, Orientation, And Chart Changes

| ID | Status | Claimable theorem target | Files and fields | Notes |
|---|---:|---|---|---|
| M7-BDR-01 | `PROVED` | Boundary chart local Stokes on selected/extended half-space boxes. | `Stokes/BoundaryChart/LocalStokes.lean`; `boundaryChartLocalStokes_transitionPullback_of_extendedBox*`.  `Stokes/Global/LocalIntegral.lean`; `projectLocalStokes_of_boundaryChartExtendedBox`. | True local theorem is done. |
| M7-BDR-02 | `PROVED + FIELD` | Build boundary local Stokes packages from finite boundary-piece input. | `Stokes/Global/BoundaryPieceFamilyConstructor.lean`; `BoundaryPieceFamilyInput.localStokes`; `toMixedBoundaryPackage`. | The package proves local Stokes once `sourceExtendedBox`, `targetSelectedBox`, and `imageData` fields are supplied. |
| M7-BDR-03 | `FIELD` | Construct the finite boundary piece family from a boundary cover or collar/trace of the partition. | `Stokes/Global/BoundaryPieceFamilyConstructor.lean`; fields of `BoundaryPieceFamilyInput`.  `Stokes/Global/BoundaryPieces.lean`; fields of `OrientedBoundaryProjectLocalPieces`. | This is the boundary analogue of M7-INT-02. |
| M7-BDR-04 | `FIELD` | Derive `BoundaryChartOrientedManifold` or `BoundaryChartOrientedAtlas` from the intended oriented smooth manifold with boundary. | `Stokes/BoundaryChart/Orientation.lean`; class `BoundaryChartOrientedManifold`; structure `BoundaryChartOrientedAtlas`. | Current orientation is project-local and fieldized; the general induced-boundary orientation theorem is missing. |
| M7-BDR-05 | `PROVED + FIELD` | Produce per-piece boundary chart COV data from selected source boxes and target image boxes. | `Stokes/BoundaryChart/ChangeOfVariables.lean`; `boundaryChartOrientedChangeOfVariables_*`.  `Stokes/BoundaryChart/OrientedAtlasSelectedBoxCOV.lean`; `BoundaryChartSelectedBoxCOVFamilyData`.  `Stokes/BoundaryChart/OrientationCovBridge.lean`; `BoundaryChartSelectedBoxOrientationCovData`. | Mathlib COV bridge is proved; target image/local inverse and orientation fields remain to be produced from chart geometry. |
| M7-BDR-06 | `FIELD` | Construct target boundary boxes and image/local-inverse data for chart transitions. | `Stokes/BoundaryChart/TransitionCompactBox.lean`; `BoundaryChartTransitionCompactBoxData.compactImage`, `localInverse`.  `Stokes/BoundaryChart/TargetBoxSelection.lean`; `BoundaryChartTargetBoxSelection`.  `Stokes/BoundaryChart/SelectedBoxImageConstructor.lean`. | This is a clean parallel target: local IFT/compact-image geometry for boundary chart transitions. |
| M7-BDR-07 | `PROVED + FIELD` | Convert boundary COV family to finite chart-change cancellation, aligned with global boundary partition terms. | `Stokes/BoundaryChart/ChangeOfVariablesFamily.lean`; `sum_eq_targetBoundarySum`.  `Stokes/Global/BoundaryCOVToChartChange.lean`; `ProjectLocalChartChangeCompatibility.boundaryPartitionTerm_eq`.  `Stokes/Global/BoundaryChartChangePieces.lean`; `BoundaryChartChangeFamilyData.boundaryPartitionTerm_eq`. | Finite summation is proved; matching the chosen `boundaryPartitionTerm` to the target integral is fieldized. |
| M7-BDR-08 | `WRAPPER` | Convert boundary-only project-local data to final/global packages. | `Stokes/Global/BoundaryGlobalConstructor.lean`; `BoundaryGlobalConstructorData`; `boundaryGlobalStokes_*`.  `Stokes/Global/BoundaryPieces.lean`; `toGlobalStokesData_*`. | Pure once boundary reconstruction and COV fields are supplied. |

### G. Boundary Integral Reconstruction

| ID | Status | Claimable theorem target | Files and fields | Notes |
|---|---:|---|---|---|
| M7-BNDINT-01 | `FIELD` | Define the genuine induced-boundary form integral in chart/partition terms. | New integration layer, or `Stokes/Global/BoundaryIntegralPartitionReconstruction.lean`; field `BoundaryIntegralPartitionReconstructionData.boundaryMeasureIntegral`. | This is paired with orientation M7-BDR-04. |
| M7-BNDINT-02 | `FIELD` | Prove the represented manifold boundary integral equals the boundary measure integral. | `BoundaryIntegralPartitionReconstructionData.manifoldBoundaryIntegral_eq_boundaryMeasureIntegral`. | Definition-dependent: can be reflexive if the boundary integral is defined this way. |
| M7-BNDINT-03 | `FIELD` | Prove the boundary measure integral reconstructs as the finite partition sum. | `BoundaryIntegralPartitionReconstructionData.boundaryMeasureIntegral_eq_partitionSum`; core package `BoundaryIntegralReconstructionData.manifoldBoundaryIntegral_eq_selectedBoundarySum`. | This is the boundary analogue of M7-BULK-01. |
| M7-BNDINT-04 | `WRAPPER` | Feed boundary reconstruction into final packages. | `Stokes/Global/BoundaryIntegralReconstruction.lean`; `ofBoundaryIntegralReconstruction`; `toGlobalStokesData_of_*_boundaryIntegralReconstruction`.  `Stokes/Global/BoundaryIntegralPartitionReconstruction.lean`. | Already pure projection once M7-BNDINT-02/03 are proved. |

### H. Selected Mixed Assembly

| ID | Status | Claimable theorem target | Files and fields | Notes |
|---|---:|---|---|---|
| M7-MIX-01 | `FIELD` | Build one `PartitionReconstructionData` whose active set, interior pieces, boundary pieces, and terms are exactly the outputs of the interior and boundary constructors. | `Stokes/Global/Reconstruction.lean`; `PartitionReconstructionData`.  `Stokes/Global/MixedSelectedConstructor.lean`; field `SelectedMixedGlobalInput.reconstruction`. | Depends on bulk and boundary reconstruction. |
| M7-MIX-02 | `FIELD` | Align `selectedPartition.active` with `reconstruction.activeCharts`. | `Stokes/Global/MixedSelectedConstructor.lean`; field `selectedPartition_active`. | Usually a definitional or `simp` theorem if M7-MIX-01 chooses indices well. |
| M7-MIX-03 | `FIELD` | Align artificial cancellation package with reconstruction interior indices and terms. | `SelectedMixedGlobalInput.artificialCancellation_*`. | Should be a wrapper after M7-INT-05/06 and M7-MIX-01. |
| M7-MIX-04 | `FIELD` | Align chart-change package with reconstruction boundary indices and terms. | `SelectedMixedGlobalInput.chartChange_*`. | Should be a wrapper after M7-BDR-07 and M7-MIX-01. |
| M7-MIX-05 | `WRAPPER` | Convert `SelectedMixedGlobalInput` to `MixedGlobalStokesData` and final theorem. | `Stokes/Global/MixedSelectedConstructor.lean`; `toMixedGlobalStokesData`; `selectedMixedGlobalStokes`. | Already done. |

## Already-Closed Theorem Islands

These modules should not be re-owned as open M7 work unless a later theorem
shape forces a refactor:

- Euclidean and singular-cube wrappers: `Stokes/Box.lean`,
  `Stokes/SingularCube.lean`.
- Manifold form chart-transition API: `Stokes/ManifoldForm.lean`.
- Half-space signs and local half-space Stokes:
  `Stokes/HalfSpace/*.lean`.
- Boundary chart local Stokes and chart-change invariance:
  `Stokes/BoundaryChart/LocalStokes.lean`,
  `Stokes/BoundaryChart/ChangeOfVariables.lean`.
- Finite-sum assembly:
  `Stokes/Global/Theorem.lean`, `Assembly.lean`, `ChartChange.lean`,
  `Cancellation.lean`.
- Finite-active partition and coefficient sum-one:
  `Stokes/Global/FiniteActive.lean`, `PartitionSumOne.lean`.
- Algebraic artificial-face cancellation:
  `Stokes/Global/ArtificialFacePairing.lean`,
  `ArtificialFaceGeometry.lean`, `ArtificialFaceOverlapPairing.lean`.
- Constructor and projection layers:
  `IntegralReconstruction.lean`, `BoundaryIntegralReconstruction.lean`,
  `BoundaryIntegralPartitionReconstruction.lean`,
  `MixedGlobalConstructor.lean`, `MixedSelectedConstructor.lean`,
  `NaturalStatement.lean`.

## Suggested Claim Order

1. Claim the two genuine reconstruction theorem families first:
   M7-BULK-01 and M7-BNDINT-03.  They determine the final integration
   definitions and prevent later workers from proving the wrong finite-sum
   target.
2. In parallel, claim geometry-producing packages: M7-INT-02,
   M7-INT-04/05, M7-BDR-03, M7-BDR-04, and M7-BDR-06.
3. Then claim the selected mixed assembly alignment: M7-MIX-01 through
   M7-MIX-04.
4. Finish with M7-NAT-01 through M7-NAT-03, which should be a short theorem
   once all previous records are constructible.

## Verification

This was a documentation-only audit.  I did not run `lake build`.

I did run the placeholder scan over current Lean sources while preparing this
report:

```text
rg "\bsorry\b|\badmit\b|^\s*axiom\b" Stokes --glob "*.lean"
```

It found no Lean placeholders in `Stokes/**/*.lean`.

## Notes For Future Workers

- `Stokes/Global.lean` currently imports the main M6/M7 constructor stack, but
  not every newer helper module, such as `NaturalStatement`,
  `BulkIntegralPartitionReconstruction`, `BoundaryIntegralPartitionReconstruction`,
  `BoundaryCOVToChartChange`, `ArtificialFaceAdjacency`,
  `ArtificialFaceOverlapPairing`, or the pure boundary-chart
  `OrientedAtlasSelectedBoxCOV` and `JacobianCOVBridge` helpers.  Public API
  aggregation is an engineering task, not a theorem obligation.
- Avoid treating a tautological `ofSelectedBoundaryPieceSum` or a record whose
  integral is defined to be a finite sum as the final manifold theorem.  Those
  are useful wrappers, but M7 needs the genuine integral definitions or an
  explicitly chosen compact-support first theorem.
- The cleanest current final path is mixed, not boundary-only:
  localized interior pieces should feed `MixedInteriorPackage`, boundary pieces
  should feed `MixedBoundaryPackage`, and reconstruction should feed
  `SelectedMixedGlobalInput`.
