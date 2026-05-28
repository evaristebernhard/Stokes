# Stokes M6 Parallel Integration Plan, Wave 2

Scope: scanned the current `Stokes/Global/*.lean` and
`Stokes/BoundaryChart/*.lean` files.  This is a report-only worker output: no
Lean source files were changed.

Date: 2026-05-24.

## Current Aggregator Boundary

The key cycle boundary is:

```text
Stokes.Global.InteriorChart -> Stokes.HalfSpace
```

Therefore anything imported by `Stokes.HalfSpace` must not import
`Stokes.Global.*`.  Pure `Stokes.BoundaryChart.*` files can live under the
`Stokes.HalfSpace` public aggregator.  Boundary-chart files that import global
assembly records must stay under `Stokes.Global`.

Current public aggregator gaps:

- `Stokes.Global.lean` does not yet import:
  `ArtificialFaceGeometry`, `ArtificialFaceSelection`,
  `BoundaryIntegralReconstruction`, `BoundaryPieceFamilyConstructor`,
  `CompactSupportChartBox`, `ExtDerivOnSupport`, `IntegralReconstruction`,
  `InteriorPieceFamilyConstructor`, `MixedSelectedConstructor`,
  `PartitionCompactSupport`, `ProjectLocalConstructor`, `SupportFiniteSum`.
- `Stokes.HalfSpace.lean` does not yet import:
  `BoundaryBoxSelection`, `ChangeOfVariablesFamily`,
  `SelectedBoxImageConstructor`, `TargetBoxSelection`,
  `TransitionCompactBox`, `TransitionDerivative`.
- `Stokes.BoundaryChart.BoundaryPieceConvenience` is already imported by
  `Stokes.Global` and should not be imported by `Stokes.HalfSpace`, because it
  imports `Stokes.Global.BoundaryPieces`.

## Recommended Ownership

| File | Public aggregator | Reason | Cycle note |
|---|---|---|---|
| `Stokes.BoundaryChart.TransitionCompactBox` | `Stokes.HalfSpace` | Pure boundary-chart compact box and target-image bookkeeping. | Imports only boundary-chart COV stack; safe below global. |
| `Stokes.BoundaryChart.BoundaryBoxSelection` | `Stokes.HalfSpace` | Boundary selected-box construction is now pure boundary-chart code. | Safe only while it does not import `Stokes.Global.BoxSelection`. |
| `Stokes.BoundaryChart.TargetBoxSelection` | `Stokes.HalfSpace` | Target boundary-box selection is pure boundary-chart code. | Safe only while it does not import `Stokes.Global.*`. |
| `Stokes.BoundaryChart.TransitionDerivative` | `Stokes.HalfSpace` | Frechet-derivative bridge for boundary chart transitions. | Depends on `OrientationCovBridge`, no global imports. |
| `Stokes.BoundaryChart.SelectedBoxImageConstructor` | `Stokes.HalfSpace` | Combines pure boundary source/target boxes with orientation COV data. | Safe after `BoundaryBoxSelection` and `TargetBoxSelection`; move to global only if it later imports global pieces. |
| `Stokes.BoundaryChart.ChangeOfVariablesFamily` | `Stokes.HalfSpace` | Finset-indexed family version of boundary COV, still phrased in local boundary integrals. | Pure boundary-chart layer; optional to keep independent until a public consumer needs it. |
| `Stokes.BoundaryChart.BoundaryPieceConvenience` | `Stokes.Global` | Wraps global boundary piece records. | Must not enter `Stokes.HalfSpace`; it imports `Stokes.Global.BoundaryPieces`. |
| `Stokes.Global.SupportFiniteSum` | `Stokes.Global` | Finite localized support control for global localization. | Global-only support layer. |
| `Stokes.Global.CompactSupportChartBox` | `Stokes.Global` | Connects compact chart supports to interior selected boxes. | Depends on global chart compact/support data. |
| `Stokes.Global.PartitionCompactSupport` | `Stokes.Global` | Compact-support API for partition-localized forms. | Depends on `PartitionSumOne` and `CompactSupportChartBox`. |
| `Stokes.Global.ExtDerivOnSupport` | `Stokes.Global` | On-support exterior-derivative reconstruction package. | Depends on global reconstruction/localized support. |
| `Stokes.Global.ArtificialFaceGeometry` | `Stokes.Global` | Geometric wrapper over global artificial-face pairing. | Imports `Stokes.Global.ArtificialFacePairing`; never add to `Stokes.HalfSpace`. |
| `Stokes.Global.ArtificialFaceSelection` | `Stokes.Global` | Selected-box artificial-face family and cancellation adapters. | Imports global cancellation, boxes, and boundary pieces. |
| `Stokes.Global.InteriorPieceFamilyConstructor` | `Stokes.Global` | Adapts localized interior pieces to `MixedInteriorPackage`. | Depends on `LocalizedInteriorPieces` and `MixedGlobalConstructor`. |
| `Stokes.Global.BoundaryPieceFamilyConstructor` | `Stokes.Global` | Boundary-piece family adapter for the mixed constructor. | Imports global boundary constructors and `BoundaryPieceConvenience`. |
| `Stokes.Global.BoundaryIntegralReconstruction` | `Stokes.Global` | Boundary finite-sum reconstruction wrappers for final records. | Imports global boundary constructors/wrappers. |
| `Stokes.Global.IntegralReconstruction` | `Stokes.Global` | Bulk-integral reconstruction package and mixed-wrapper projection. | Depends on `MixedGlobalConstructor`. |
| `Stokes.Global.ProjectLocalConstructor` | `Stokes.Global` | Thin constructor for `ProjectLocalGlobalStokesData`. | Depends on `BoundaryChartChangePieces`. |
| `Stokes.Global.MixedSelectedConstructor` | `Stokes.Global` | Selected-partition wrapper for `MixedGlobalStokesData`. | Depends on mixed, boundary, and interior global constructors. |

## Suggested Import Order

Phase 1: lower boundary-chart API into `Stokes.HalfSpace`.

```lean
import Stokes.BoundaryChart.ChangeOfVariablesFamily
import Stokes.BoundaryChart.TransitionCompactBox
import Stokes.BoundaryChart.TargetBoxSelection
import Stokes.BoundaryChart.BoundaryBoxSelection
import Stokes.BoundaryChart.TransitionDerivative
import Stokes.BoundaryChart.SelectedBoxImageConstructor
```

Place these after the existing imports that define their prerequisites:
`ChangeOfVariablesFamily` after `ChangeOfVariables`; `TransitionCompactBox`
and `TransitionDerivative` after `OrientationCovBridge`; `TargetBoxSelection`
and `BoundaryBoxSelection` after `TransitionCompactBox`;
`SelectedBoxImageConstructor` after the source and target selection files.

After Phase 1, remove the now-redundant direct `BoundaryBoxSelection` and
`TargetBoxSelection` imports from `Stokes.Global.lean` only if desired for
ownership clarity.  Leaving duplicate transitive imports is harmless, but it
obscures the intended boundary between half-space and global layers.

Phase 2: add support and compact-support global helpers.

```lean
import Stokes.Global.SupportFiniteSum
import Stokes.Global.CompactSupportChartBox
import Stokes.Global.PartitionCompactSupport
import Stokes.Global.ExtDerivOnSupport
```

Place `SupportFiniteSum` after `PartitionSumOne` or near
`LocalizedSupport`; place `CompactSupportChartBox` after
`ChartCompactImage` and `CoefficientBoxSupport`; place
`PartitionCompactSupport` after `CompactSupportChartBox`; place
`ExtDerivOnSupport` after both `ExtDerivReconstruction` and
`PartitionSumOne`.

Phase 3: add local family and cancellation adapters.

```lean
import Stokes.Global.ArtificialFaceGeometry
import Stokes.Global.ArtificialFaceSelection
import Stokes.Global.InteriorPieceFamilyConstructor
import Stokes.Global.BoundaryPieceFamilyConstructor
```

Place `ArtificialFaceGeometry` and `ArtificialFaceSelection` after
`ArtificialFacePairing`; place `InteriorPieceFamilyConstructor` after
`MixedGlobalConstructor` and `LocalizedInteriorPieces`; place
`BoundaryPieceFamilyConstructor` after `BoundaryGlobalConstructor`,
`BoundaryChartChangePieces`, `BoundaryPieceConvenience`, and
`MixedGlobalConstructor`.

Phase 4: add final reconstruction and constructor wrappers.

```lean
import Stokes.Global.BoundaryIntegralReconstruction
import Stokes.Global.IntegralReconstruction
import Stokes.Global.ProjectLocalConstructor
import Stokes.Global.MixedSelectedConstructor
```

Place `BoundaryIntegralReconstruction` after `BoundaryGlobalConstructor`,
`ReconstructionWrappers`, and `BoundaryPieceConvenience`;
`IntegralReconstruction` after `MixedGlobalConstructor`;
`ProjectLocalConstructor` after `BoundaryChartChangePieces`;
`MixedSelectedConstructor` after `InteriorGlobalConstructor`,
`BoundaryGlobalConstructor`, and `MixedGlobalConstructor`.

## Conflict Matrix

| Conflict surface | Modules involved | Recommendation |
|---|---|---|
| Half-space/global import cycle | Any `Stokes.HalfSpace` import that reaches `Stokes.Global.*` | Do not add `BoundaryPieceConvenience` or any `Stokes.Global.*` module to `Stokes.HalfSpace`. |
| Boundary box ownership | `BoundaryBoxSelection`, `TargetBoxSelection`, `SelectedBoxImageConstructor`, `Global.BoxSelection` | Keep compact coordinate box primitives in `BoundaryChart.TransitionCompactBox`; keep interior projections in `Global.BoxSelection`. |
| Global imports through boundary convenience | `BoundaryPieceConvenience`, `BoundaryPieceFamilyConstructor`, `BoundaryIntegralReconstruction` | Treat `BoundaryPieceConvenience` as a global-layer boundary-chart helper. |
| Artificial faces with half-space signs | `ArtificialFaceGeometry`, `ArtificialFacePairing`, `HalfSpace.Faces` | `ArtificialFaceGeometry` may import `HalfSpace.Faces`, but it remains global because it imports `ArtificialFacePairing`. |
| Partition support vs exterior derivative support | `SupportFiniteSum`, `PartitionCompactSupport`, `ExtDerivOnSupport` | Integrate support files before using on-support ext-derivative packages in final reconstruction proofs. |
| Constructor overlap | `ProjectLocalConstructor`, `BoundaryGlobalConstructor`, `MixedSelectedConstructor`, `IntegralReconstruction` | Keep constructors thin and field-alignment only; avoid adding new reconstruction mathematics there. |
| Public API width | `ChangeOfVariablesFamily`, `TransitionDerivative` | Cycle-safe for `Stokes.HalfSpace`; can remain independent temporarily if the public half-space API should stay minimal. |

## Verification Performed

Focused checks passed for the unaggregated boundary-chart candidates:

```text
lake env lean Stokes/BoundaryChart/TransitionCompactBox.lean
lake env lean Stokes/BoundaryChart/ChangeOfVariablesFamily.lean
lake env lean Stokes/BoundaryChart/TransitionDerivative.lean
lake env lean Stokes/BoundaryChart/BoundaryBoxSelection.lean
lake env lean Stokes/BoundaryChart/TargetBoxSelection.lean
lake env lean Stokes/BoundaryChart/SelectedBoxImageConstructor.lean
```

Focused checks passed for the unaggregated global candidates:

```text
lake env lean Stokes/Global/ArtificialFaceGeometry.lean
lake env lean Stokes/Global/ArtificialFaceSelection.lean
lake env lean Stokes/Global/BoundaryIntegralReconstruction.lean
lake env lean Stokes/Global/BoundaryPieceFamilyConstructor.lean
lake env lean Stokes/Global/CompactSupportChartBox.lean
lake env lean Stokes/Global/ExtDerivOnSupport.lean
lake env lean Stokes/Global/IntegralReconstruction.lean
lake env lean Stokes/Global/InteriorPieceFamilyConstructor.lean
lake env lean Stokes/Global/MixedSelectedConstructor.lean
lake env lean Stokes/Global/PartitionCompactSupport.lean
lake env lean Stokes/Global/ProjectLocalConstructor.lean
lake env lean Stokes/Global/SupportFiniteSum.lean
```

Current aggregators also passed:

```text
lake build Stokes.HalfSpace
lake build Stokes.Global
```

The placeholder scan over `Stokes/Global` and `Stokes/BoundaryChart` found no
matches:

```text
rg "\bsorry\b|\badmit\b|^\s*axiom\b" Stokes/Global Stokes/BoundaryChart --glob "*.lean"
```

## Post-Integration Verification Commands

After each phase, run the aggregator being changed:

```text
lake build Stokes.HalfSpace
lake build Stokes.Global
```

After all imports are added, run:

```text
lake build
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

For a focused failure, prefer checking the newly imported file first, then the
aggregator:

```text
lake env lean Stokes/BoundaryChart/SelectedBoxImageConstructor.lean
lake build Stokes.HalfSpace

lake env lean Stokes/Global/MixedSelectedConstructor.lean
lake build Stokes.Global
```

Use `lake build Stokes.Global` rather than a bare
`lake env lean Stokes/Global.lean` when object files may be missing or stale.
The build target will schedule dependencies correctly.

## Main Risks

1. The most serious risk is reintroducing a global import into a
   boundary-chart file that is added to `Stokes.HalfSpace`.  That creates the
   cycle `Global.InteriorChart -> HalfSpace -> BoundaryChart.* -> Global.*`.
2. `BoundaryPieceConvenience` looks like a boundary-chart file by path, but it
   is semantically global because it imports `Global.BoundaryPieces`.
3. `TransitionCompactBox` now owns `CompactCoordinateBoxSelection`; do not
   duplicate that primitive in `Global.BoxSelection`.
4. `TransitionDerivative` and `TransitionCompactBox` use nearby manifold
   regularity assumptions (`1` and `top`).  Recheck focused files after any
   API tightening around `IsManifold`.
5. `ExtDerivOnSupport` contains fragile finite-sum/ext-derivative algebra.
   Keep it in the support/reconstruction phase and verify it before any final
   global theorem wrappers depend on it.
6. Parallel workers should avoid simultaneous edits to `Stokes.Global.lean`
   and `Stokes.HalfSpace.lean`.  Let one integration worker own aggregator
   edits, landing phase by phase with focused builds.

