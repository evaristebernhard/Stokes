# Stokes M8 12-Agent Wave Coordination

Date: 2026-05-24.

Scope: documentation-only coordination report for the current 12-agent M8 wave.
This agent does not edit Lean files and does not run Lean builds.  The purpose
is to keep the implementation queue, true blocker ledger, and build strategy
clear while the Lean workers make focused changes.

## Wave Strategy

This wave should be smaller than the previous 20-agent restart.  The earlier
wave was good at surfacing wrappers and reducing field surfaces, but it also
created `.lake` contention when too many workers tried to build broad targets at
the same time.  The current wave should use 12 focused owners:

| Agent | Area | Expected output | Success signal |
|---|---|---|---|
| 1 | Bulk measure fields | Instantiate or shrink `BulkMeasureLocalizationFields` inputs from selected chart data. | A focused target around `Stokes.Global.BulkMeasureLocalizationFields` passes. |
| 2 | Bulk a.e. integrand input | Connect actual chartwise measures to `BulkIntegrandAEData`. | The a.e. equality is supplied for the real selected-support measure, not only an abstract field. |
| 3 | Measure-box comparison | Align measure-local bulk terms with project-local box terms. | `MeasureBoxAPI` gives the exact term equality needed by the bulk constructor. |
| 4 | Bulk localization constructor | Produce the bulk side of `M8MeasureLocalizationData` from Agents 1--3. | No new global Stokes wrapper; only the bulk measure-localization field is filled. |
| 5 | Boundary ambient measure | Define or select the boundary measure/integrand package used by selected boundary pieces. | Boundary a.e. indicator decomposition has a concrete measure target. |
| 6 | Boundary piece integrability and COV terms | Feed compact-support boundary integrability and COV equalities into boundary reconstruction. | Piece integrals match `boundaryPartitionTerm` for selected pieces. |
| 7 | Target boundary boxes | Construct target selected boxes and local inverse/image data from compact image/local openness inputs. | Pure `BoundaryChart` data can be adapted without importing `Global` into `HalfSpace`. |
| 8 | Artificial-face geometry | Choose either support-zero or overlap-pairing for artificial faces and build the needed geometry. | `ArtificialFaceResolvedData` is produced from selected boxes, not manually assumed. |
| 9 | Boundary orientation bridge | Connect selected boundary chart orientation predicates to the global oriented atlas/manifold data. | The outward-first boundary sign is supplied by orientation API, not a hand positive-Jacobian assumption. |
| 10 | Compact-support partition selection | Produce selected interior and boundary boxes from compact support and chart coverage. | The same finite active set feeds bulk, boundary, target-image, and artificial-face data. |
| 11 | M8 assembly constructor | Package the outputs into `M8MeasureLocalizationData` and call `m8GlobalStokes`. | The final theorem remains a short projection from stable records. |
| 12 | Blueprint and reports | Keep this queue and blocker ledger synchronized. | Documentation changes only; no Lean build run by this agent. |

## True Blocker Ledger

The wave should distinguish field plumbing from mathematical construction.
These are the actual blockers that remain after the previous wrapper work.

| Priority | Blocker | Current stable entry point | Required construction |
|---|---|---|---|
| P0 | Bulk measure localization | `BulkIntegralLocalizationConstructor`, `BulkMeasureLocalizationFields`, `BulkIntegrandAE` | Supply the genuine chartwise bulk measure, the a.e. replacement of the global exterior-derivative integrand, active-piece integrability, and equality between measure-local terms and selected box terms. |
| P0 | Boundary measure localization | `BoundaryMeasureLocalization`, `BoundaryCOVMeasureConstructor`, `BoundaryIntegrabilityCompactSupport` | Supply the ambient boundary measure/integrand, a.e. selected-piece indicator decomposition, termwise integrability, and equality of each piece integral with the boundary partition term. |
| P0 | M8 data construction | `M8MeasureLocalizationData`, `M8GlobalStokesInput`, `m8GlobalStokes` | Build the M8 measure-localization record from selected partition data instead of manually filling final fields. |
| P1 | Target boundary image data | `BoundaryChart.TargetImageFieldReduction`, `BoundaryTargetImageToAssembly` | Derive target boxes, image equalities, and local inverse data from local openness/inverse-function inputs for selected boundary chart changes. |
| P1 | Artificial-face cancellation | `ArtificialFaceFieldReduction`, `ArtificialFaceAdjacency`, `ArtificialFaceOverlapPairing` | Construct either support-zero data for artificial faces or an overlap pairing with opposite signs and equal unsigned terms. |
| P1 | Boundary orientation compatibility | `BoundaryChart.OrientedAtlasSelectedBoxCOV`, `BoundaryOrientationToGlobal` | Replace local hand orientation assumptions with oriented atlas/manifold data and outward-normal-first boundary orientation. |
| P1 | Compact-support selected boxes | `PartitionCompactSupport`, `SelectedInteriorAssembly`, `SelectedBoundaryAssembly` | Select a coherent finite family of interior, boundary, target, and support boxes from compact support and chart coverage. |
| P2 | Canonical integral API | `GlobalIntegralDefinitions`, `NaturalMeasureConstructor` | Replace represented real-valued integral fields by the final canonical manifold form integrals after M8 is stable. |

## Avoiding Full Lake Build In This Wave

The current wave should avoid broad `lake build` from parallel workers.  The
parent process can run a full build only after workers have stopped and the
import list is stable.

Worker build policy:

1. Lean workers run only focused targets, for example
   `lake build Stokes.Global.BulkIntegrandAE` or
   `lake build Stokes.BoundaryChart.TargetImageFieldReduction`.
2. A worker touching several files builds the narrowest top-level module that
   imports those files, not `lake build`.
3. Documentation-only workers do not run Lean builds.
4. The no-placeholder scan may be run by the parent or a single designated
   verification worker, but it should not be used as a substitute for focused
   module builds.
5. Aggregator imports such as `Stokes/Global.lean` are changed only after the
   relevant focused builds pass.
6. The final full `lake build` is serialized in the parent integration step,
   after all agents have either completed or been shut down.

This policy is meant to avoid Windows file locking and concurrent `.olean`
writer contention in `.lake/build`.  It also keeps failures local: a target
build failure should point to one owner, not to the whole global stack.

## Import Hygiene

The import boundary remains strict:

- `Stokes.Global.*` may import pure `Stokes.BoundaryChart.*` utilities.
- `Stokes.HalfSpace` must not import global adapters.
- `BoundaryChart` aggregator files, if introduced, must exclude
  `BoundaryPieceConvenience` or any other module that imports
  `Stokes.Global.*`.
- Global target-image adapters stay in `Stokes.Global`, while pure
  target-image selection stays in `Stokes.BoundaryChart`.

## Reporting Rule

When reporting progress from this wave, use three categories:

- Proved theorem: a Lean theorem with non-field hypotheses was proved.
- Constructor/projection: a record or theorem now packages existing fields more
  cleanly.
- True blocker discharged: one of the P0/P1 entries above is now constructed
  from chart, compact-support, measure, or orientation data.

Only the third category materially shortens the path to the final manifold
Stokes theorem.

