# Stokes M6 Field Audit

Scope: read `AGENTS.md` and the current `Stokes/Global` files.  This report is
an API map for the two final data records in `Stokes/Global/Theorem.lean`.

Verification note: I did not run Lean, because this is a report-only audit and
no Lean files were changed.  A focused placeholder scan over `Stokes/Global`
found no `sorry`, `admit`, or top-level `axiom`.

## Package map

The new global layer is mostly a record-filling API.  The final theorem
`GlobalStokesData.stokes` and its wrapper `globalStokes` are pure finite-sum
bookkeeping once all record fields are supplied.

Main filler packages now present:

- Local terms and local Stokes:
  `projectLocalStokes_of_boundaryChartExtendedBox`,
  `projectLocalStokes_of_orientedAtlas_imageData`,
  `projectLocalStokes_of_orientedManifold_imageData`,
  `projectInteriorLocalStokes_of_extendedBox`,
  `InteriorLocalStokesData.ofExtendedBox`,
  `BoundaryProjectLocalPieces.localProjectStokes`,
  `OrientedBoundaryProjectLocalPieces.localProjectStokes_of_orientedAtlas`,
  `OrientedBoundaryProjectLocalPieces.localProjectStokes_of_orientedManifold`.
- Reconstruction wrappers:
  `PartitionReconstructionData.toGlobalStokesData`,
  `ExtDerivPartitionReconstructionData.toGlobalStokesData`,
  `MixedGlobalStokesData.toGlobalStokesData`,
  `InteriorProjectLocalPieces.toGlobalStokesData`,
  `BoundaryProjectLocalPieces.toProjectLocalGlobalStokesData`,
  `BoundaryProjectLocalPieces.toGlobalStokesData`,
  `BoundaryGlobalConstructorData.toGlobalStokesData_of_orientedAtlas`,
  `BoundaryGlobalConstructorData.toGlobalStokesData_of_orientedManifold`.
- Cancellation wrappers:
  `ArtificialBoundaryCancellationData.of_forall_eq_zero`,
  `ArtificialBoundaryCancellationData.of_pair_cancel`,
  `ArtificialFacePairingData.toArtificialBoundaryCancellationData`,
  `GlobalStokesData.interiorBoundaryCancellation_of_cancellationData`,
  `GlobalStokesData.interiorBoundaryCancellation_of_facePairing`.
- Chart-change wrappers:
  `ChartChangeCancellationData.chartChangeCancellation`,
  `GlobalStokesData.chartChangeCancellation_of_pointwise_eq`,
  `ProjectLocalGlobalStokesData.chartChangeCancellation_of_pointwise_eq`,
  `BoundaryChartChangeFamilyData.chartChangeCancellation_selected`,
  `BoundaryChartChangeFamilyData.chartChangeCancellation_extended`,
  `ProjectLocalGlobalStokesData.chartChangeCancellation_of_boundaryChartChange_selected`,
  `ProjectLocalGlobalStokesData.chartChangeCancellation_of_boundaryChartChange_extended`,
  `OrientedBoundaryChartChangeFamilyData.chartChangeCancellation`.
- Partition, support, and box selectors:
  `FiniteActiveOnCompact.ofCompact`,
  `SelectedBoxPartitionOfUnity`,
  `CompactActiveExtendedBoxData.toSelectedBoxPartitionOfUnity`,
  `CoefficientBoxSupportData.toLocalizedSupportControl`,
  `LocalizedSmoothnessData.interiorChartExtendedBox`,
  `PartitionSumOne` reconstruction lemmas,
  `ExtDerivReconstruction` finite-sum exterior-derivative lemmas.

## `GlobalStokesData` fields

| Field | Current filler API | Still missing real mathematics |
|---|---|---|
| `activeCharts` | Copied from `PartitionReconstructionData`, `MixedGlobalStokesData.reconstruction`, `InteriorProjectLocalPieces`, `BoundaryProjectLocalPieces`, `OrientedBoundaryProjectLocalPieces`; finite candidates come from `FiniteActiveOnCompact.ofCompact` and selected-box packages. | A canonical global cover/partition choice for the final manifold theorem, including boundary/interior splitting. |
| `interiorPieces` | Direct field of `PartitionReconstructionData`; from `InteriorProjectLocalPieces`; empty in boundary-only constructors. | Actual localized interior piece decomposition compatible with partition-of-unity support and selected boxes. |
| `boundaryPieces` | Direct field of `PartitionReconstructionData`; from `BoundaryProjectLocalPieces` or `OrientedBoundaryProjectLocalPieces`; empty in interior-only constructors. | Actual boundary-local decomposition and indexing from charts. |
| `interiorBulkTerm` | `InteriorProjectLocalPieces.interiorBulkTerm`; `LocalizedInteriorPieces.bulkTerm`; arbitrary term field in `PartitionReconstructionData` and `MixedInteriorPackage`. | Identification of these terms with the true localized global bulk integrals. |
| `interiorBoundaryTerm` | `InteriorLocalStokesData.artificialBoundaryTerm`; `InteriorProjectLocalPieces.interiorBoundaryTerm`; `ArtificialFacePairingData.interiorBoundaryTerm`; explicit field of `MixedGlobalStokesData`. | Geometric construction of artificial face terms for the chosen interior boxes. |
| `boundaryBulkTerm` | `BoundaryProjectLocalPieces.projectLocalBulkTerm`; `OrientedBoundaryProjectLocalPieces.projectLocalBulkTerm`; arbitrary term field in `PartitionReconstructionData` and `MixedBoundaryPackage`. | Boundary-local chart decomposition whose bulk terms sum to the global bulk contribution. |
| `boundaryBoundaryTerm` | `BoundaryProjectLocalPieces.projectLocalBoundaryTerm`; `OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm`; explicit field of `MixedGlobalStokesData`. | Concrete boundary representative choice before final chart-change/partition identification. |
| `boundaryPartitionTerm` | Direct field of `PartitionReconstructionData`, `BoundaryProjectLocalPieces`, and `OrientedBoundaryProjectLocalPieces`; target side of chart-change packages. | Definition as true partition-local boundary integral terms in global boundary integration. |
| `globalBulkIntegral` | Direct field of reconstruction and constructor packages. | The actual manifold integral of `dω` or compact-support variant, plus its reduction to local sums. |
| `globalBoundaryIntegral` | Direct field of reconstruction and constructor packages. | The actual boundary integral of `ω`, plus chart/partition reconstruction. |
| `globalBulkIntegral_eq_localBulkSum` | Filled by `PartitionReconstructionData.toGlobalStokesData_globalBulkIntegral_eq_localBulkSum`, `ExtDerivPartitionReconstructionData.toGlobalStokesData_globalBulkIntegral_eq_localBulkSum`, `InteriorProjectLocalPieces.toGlobalStokesData`, boundary-only constructors. | Real integral linearity and partition localization theorem for top-degree form integration. |
| `interiorLocalStokes` | `projectInteriorLocalStokes_of_extendedBox`, `InteriorLocalStokesData.localEquality`, `InteriorProjectLocalPieces.interiorLocalStokes`, `MixedInteriorPackage.localStokes`; vacuous in boundary-only constructors. | Mostly local theorem is present; still need systematic construction of localized extended boxes. |
| `boundaryLocalStokes` | `projectLocalStokes_of_boundaryChartExtendedBox`, oriented image-data local Stokes theorems, `BoundaryProjectLocalPieces.localProjectStokes`, `OrientedBoundaryProjectLocalPieces.localProjectStokes_*`, `MixedBoundaryPackage.localStokes`; vacuous in interior-only constructor. | Actual boundary chart boxes, oriented image data, and orientation hypotheses for the final boundary cover. |
| `interiorBoundaryCancellation` | `ArtificialBoundaryCancellationData`, `ArtificialFacePairingData`, `GlobalStokesData.interiorBoundaryCancellation_of_*`; vacuous in boundary-only constructors. | Real pairing/zero proof for artificial faces created by the chosen interior decomposition. |
| `chartChangeCancellation` | `ChartChangeCancellationData.chartChangeCancellation`; pointwise wrappers for `GlobalStokesData` and `ProjectLocalGlobalStokesData`; boundary COV family wrappers; oriented boundary family wrapper. | Pointwise analytic chart-change data for the final boundary partition terms. |
| `globalBoundaryIntegral_eq_boundaryPartitionSum` | Filled by `PartitionReconstructionData`, `ExtDerivPartitionReconstructionData`, `BoundaryGlobalConstructorData`, boundary/interior constructors. | Real boundary integral reconstruction from chart-local partition terms. |

## `ProjectLocalGlobalStokesData` fields

| Field | Current filler API | Still missing real mathematics |
|---|---|---|
| `activeCharts` | `BoundaryProjectLocalPieces.toProjectLocalGlobalStokesData`; finite active sets can be sourced from `FiniteActiveOnCompact` and `SelectedBoxPartitionOfUnity`. | Final boundary cover/partition selection. |
| `localPieces` | `BoundaryProjectLocalPieces.localPieces`. | Actual boundary piece indexing and finite selection. |
| `sourceChart` | `BoundaryProjectLocalPieces.sourceChart`. | Concrete source chart assignment from the boundary cover. |
| `targetChart` | `BoundaryProjectLocalPieces.targetChart`. | Concrete comparison or boundary target chart assignment. |
| `lowerCorner` | `BoundaryProjectLocalPieces.lowerCorner`; box helpers prove ordering/domain facts from `extendedBox`. | Coordinate box selection fitted to boundary-chart domains. |
| `upperCorner` | `BoundaryProjectLocalPieces.upperCorner`; box helpers prove ordering/domain facts from `extendedBox`. | Same as `lowerCorner`: real local box construction. |
| `boundaryPartitionTerm` | Explicit field of `BoundaryProjectLocalPieces`; chart-change family wrappers identify local boundary integrals with it. | Definition as a true boundary partition integral. |
| `globalBulkIntegral` | Explicit field of `BoundaryProjectLocalPieces`. | Actual global bulk integral and boundary-local reduction. |
| `globalBoundaryIntegral` | Explicit field of `BoundaryProjectLocalPieces`. | Actual global boundary integral. |
| `globalBulkIntegral_eq_projectLocalSum` | Copied by `BoundaryProjectLocalPieces.toProjectLocalGlobalStokesData`. | Real proof that global bulk reduces to these project-local half-space bulk integrals. |
| `localProjectStokes` | Filled by `BoundaryProjectLocalPieces.localProjectStokes`, using `projectLocalStokes_of_boundaryChartExtendedBox`. | Real construction of all `boundaryChartExtendedBox` witnesses. |
| `chartChangeCancellation` | `ProjectLocalGlobalStokesData.chartChangeCancellation_of_pointwise_eq`; `BoundaryChartChangeFamilyData.chartChangeCancellation_selected`; `BoundaryChartChangeFamilyData.chartChangeCancellation_extended`; copied from `BoundaryProjectLocalPieces`. | Concrete boundary COV family and proof that the chosen `boundaryPartitionTerm` is the transported target term. |
| `globalBoundaryIntegral_eq_boundaryPartitionSum` | Copied by `BoundaryProjectLocalPieces.toProjectLocalGlobalStokesData`. | Real boundary reconstruction theorem. |

## Quality notes

1. The final records are coherent as bookkeeping APIs: once the record is
   instantiated, `GlobalStokesData.stokes` and `ProjectLocalGlobalStokesData.stokes`
   need no further analysis.
2. The largest remaining assumptions are the two global reconstruction fields:
   `globalBulkIntegral_eq_*` and `globalBoundaryIntegral_eq_boundaryPartitionSum`.
   Current packages carry these as explicit fields; they do not yet prove the
   manifold integration theorem.
3. Interior localization has an API mismatch to watch: `LocalizedInteriorPieces`
   produces `InteriorLocalStokesData I (localizedForm ...)`, while
   `InteriorProjectLocalPieces I ω` expects `InteriorLocalStokesData I ω`.
   The mixed constructor avoids this by storing real-valued terms and local
   equalities abstractly, so the next interior path should probably go through
   `MixedInteriorPackage` rather than forcing `InteriorProjectLocalPieces`.
4. `PartitionSumOne` proves reconstruction on a compact set `K`, while
   `ExtDerivPartitionReconstructionData.ofPartitionReconstructionData_of_coeff_sum_eq_one`
   currently consumes an everywhere coefficient-sum hypothesis.  A compact
   support or "on support" version is still needed for the intended theorem.
5. Boundary chart-change has two useful layers now: project-local selected or
   extended target families, and oriented-boundary pointwise families.  The
   remaining work is not finite-sum algebra; it is producing the per-piece COV
   and target-box data from the actual atlas/partition geometry.

## Next minimal closed-loop targets

1. Build the boundary-only constructor path that removes manual
   `chartChangeCancellation`: `BoundaryProjectLocalPieces` plus
   `BoundaryChartChangeSelectedFamilyData` or `BoundaryChartChangeExtendedFamilyData`
   should instantiate `ProjectLocalGlobalStokesData` directly.
2. Add a compact-support boundary reconstruction package that fills
   `globalBoundaryIntegral_eq_boundaryPartitionSum` from finite boundary
   partition terms.
3. Add a compact-support bulk reconstruction package that combines
   `PartitionSumOne`, `ExtDerivReconstruction`, and integral linearity to fill
   `globalBulkIntegral_eq_localBulkSum`.
4. Route localized interior pieces into `MixedInteriorPackage`, then feed
   `MixedGlobalStokesData` instead of using the current `InteriorProjectLocalPieces`
   specialization.
5. Construct one real artificial-face cancellation source for the chosen
   interior pieces, preferably via `ArtificialFacePairingData`, and connect it
   to `MixedGlobalStokesData.interiorBoundaryCancellation`.
