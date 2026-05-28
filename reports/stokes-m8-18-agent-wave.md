# Stokes M8 18-Agent Wave Coordination

Date: 2026-05-24.

Scope: documentation-only coordination report for the current 18-agent M8 wave.
This agent does not edit Lean files and must not run `lake build`.  The purpose
is to keep task ownership, field-reduction expectations, real mathematical
obligations, and concurrent build discipline explicit while implementation
agents work in isolated files.

## Wave Aim

The M8 layer already proves a conditional global Stokes theorem once the
measure localization, target-image boundary data, artificial-face cancellation,
and compact-support selected chart data are supplied.  This wave should not add
another theorem wrapper for its own sake.  Its goal is to construct more of the
`M8CompactSupportStokesInput` and `M8GlobalStokesInput` fields from natural
compact-support, selected-box, boundary-chart, and measure-localization data.

The expected direction is:

```text
compactly supported smooth form
  -> finite selected chart boxes and partition data
  -> bulk and boundary measure localization packages
  -> target-image and artificial-face resolved packages
  -> M8CompactSupportStokesInput
  -> m8CompactSupportStokes
```

## 18-Agent Division Of Labor

| Agent | Area | Expected output | Success signal |
|---|---|---|---|
| 1 | Compact-support-to-M8 measure bridge | Connect `CompactSupportBulkMeasure`, `BoundaryCompactMeasure`, and `M8MeasureConstructors`. | A constructor supplies `M8MeasureLocalizationData` from compact-support-facing bulk and boundary packages. |
| 2 | Bulk a.e. integrand data | Instantiate `BulkIntegrandAE` inputs from localized chart support and exterior-derivative reconstruction. | The bulk integrand replacement is no longer a naked field in the M8 constructor path. |
| 3 | Bulk measure-box term alignment | Use `MeasureBoxAPI` to identify measure-local bulk terms with selected project-local box terms. | The local bulk sum in M8 is produced by theorem, not by a hand equality. |
| 4 | Boundary compact measure reconstruction | Push `BoundaryCompactMeasure` into `BoundaryMeasureToM8`. | `boundaryMeasureIntegral_eq_partitionSum` is filled from set-integral/indicator hypotheses. |
| 5 | Boundary COV to partition term | Connect `BoundaryCOVMeasureConstructor` and target-image partition terms. | Boundary chart-change terms equal `measureLocalization.boundaryPartitionTerm`. |
| 6 | Boundary piece integrability | Derive selected boundary-piece integrability from compact support and local boundary boxes. | Boundary measure constructors no longer ask for independent integrability per selected piece. |
| 7 | Localized interior selected pieces | Extend `LocalizedInteriorConstructors` toward the natural selected partition input. | `localizedInterior`, `localized_active`, and `localized_coefficient` are automatic. |
| 8 | Target image from local inverse | Use `BoundaryChart.TargetImageFromLocalInverse` to build resolved target-image families. | Target boxes and local inverse/image data come from pure `BoundaryChart` inputs. |
| 9 | Target image to M8 | Adapt pure target-image families through `BoundaryTargetImageToAssembly` and `TargetImageToM8`. | `targetImages_*` and target-boundary term comparison fields are packaged. |
| 10 | Artificial-face support-zero route | Prove or package support-zero sufficient conditions for artificial faces. | `ArtificialFaceResolvedData` is produced without manual cancellation fields. |
| 11 | Artificial-face pairing route | Build overlap/adjacent face pairing data for selected boxes. | Interior artificial terms cancel by opposite-oriented paired faces. |
| 12 | Compact finite active selection | Construct coherent finite active interior and boundary boxes from compact support. | The same active set feeds bulk, boundary, target-image, and artificial-face inputs. |
| 13 | Boundary orientation bridge | Connect project boundary-chart orientation predicates to oriented atlas/manifold data. | `BoundaryChartOrientedAtlas` is no longer just a project-local assumption. |
| 14 | Boundary chart differential geometry | Supply local inverse, image, and tangential derivative facts for boundary chart transitions. | Target-box construction has the needed inverse-function/local-openness inputs. |
| 15 | Canonical integral API audit | Plan the replacement of represented `Real` fields by actual manifold-form integrals. | A minimal final API is proposed without destabilizing M8. |
| 16 | M8 assembly constructor | Combine Agents 1, 7, 9, and 10/11 into a smaller compact-support-facing constructor. | `M8CompactSupportStokesInput` visibly has fewer hand-filled fields. |
| 17 | Import/build coordinator | Audit aggregator imports and focused build ownership. | No `Global -> HalfSpace -> Global` cycle and no broad parallel builds. |
| 18 | Reports | Maintain this wave report. | Documentation only; optional no-sorry scan; no `lake build`. |

## Fields Expected To Disappear Behind Constructors

These are not all mathematically solved yet, but they are realistic targets for
this wave because the repository already has constructor/projection layers close
to the needed shape.

| M8 field surface | Expected constructor path | Remaining input after reduction |
|---|---|---|
| `localizedInterior`, `localized_active`, `localized_coefficient` | `SelectedBoxPartitionOfUnity.toLocalizedInteriorM8Fields` and related localized-interior constructors | The actual selected partition and local project equality data. |
| `bulkMeasureIntegral_eq_localBulkSum` | `CompactSupportBulkMeasure` + `BulkMeasureToM8` + `M8MeasureConstructors` | Genuine bulk measure, a.e. indicator decomposition, integrability, and measure-box term equality. |
| `boundaryMeasureIntegral_eq_partitionSum` | `BoundaryCompactMeasure` or `BoundaryCOVMeasureConstructor` + `BoundaryMeasureToM8` | Genuine boundary measure/integrand and selected boundary-piece indicator reconstruction. |
| `artificialFaces_active`, `artificialFaces_pieces`, `artificialFaces_term` | `ArtificialFaceToM8` from `ArtificialFaceResolvedData` | Either support-zero data or geometric paired-face cancellation. |
| `targetImages_active`, `targetImages_source_mem`, `targetImages_boundarySource_mem` | `TargetImageToM8` from `BoundaryTargetImageToAssemblyInput` | Pure boundary-chart target-image family plus oriented-atlas membership. |
| `targetBoundaryTerm_eq_partition` | `BoundaryTargetImageToAssembly` and boundary COV measure constructors | Chart-change/COV theorem aligning transported boundary terms with partition terms. |
| `selectedPartition_supportSet` | Compact-support finite active selection | Coherent construction of selected partition from `formData.supportSet`. |
| `globalBulkIntegral_eq_bulkMeasureIntegral`, `globalBoundaryIntegral_eq_boundaryMeasureIntegral` | Natural/global measure constructors | Final definitions of represented integrals or a later canonical integral API. |

The practical success metric is that future M8 inputs ask for theorem-produced
packages such as compact-support bulk measure data, boundary compact measure
data, resolved target-image family data, and resolved artificial-face data,
rather than asking for the final finite-sum equalities directly.

## True Mathematical Proof Nodes

The following nodes should not be described as done merely because a record
wrapper exists.  They are the remaining mathematical content between the current
M8 theorem and a natural smooth-manifold Stokes theorem.

| Node | Mathematical meaning | Why it remains hard |
|---|---|---|
| Compact support to finite chart boxes | A compact support set is covered by finitely many coordinate boxes compatible with interior and boundary charts. | Requires coherent selection of boxes, active sets, and support containment used by all later constructions. |
| Partition-of-unity localization | `omega` and `d omega` are decomposed into selected chart-local pieces. | Needs smoothness, support, and exterior-derivative reconstruction to line up with the scalar integrands used by measure lemmas. |
| Bulk measure localization | The global bulk integral equals a finite sum of local chart-box integrals. | Requires real measure/integrand definitions, a.e. indicator decompositions, integrability, and term equality with project-local Stokes boxes. |
| Boundary measure localization | The boundary integral equals a finite sum over selected boundary pieces. | Requires boundary measure/integrand definitions, boundary COV, selected-piece integrability, and compatibility with target-image data. |
| Boundary chart target images | Source boundary boxes map to target boxes with local inverse/image control. | This is inverse-function/local-openness geometry for boundary chart transitions, not only record plumbing. |
| Artificial-face cancellation | Interior faces introduced by local boxes either vanish by support or cancel in opposite-oriented pairs. | Needs actual selected-box face geometry, signs, and equality of unsigned face terms. |
| Boundary orientation compatibility | The project sign convention equals the induced outward-normal-first boundary orientation. | Must be connected to oriented atlas/manifold data rather than a hand positive-Jacobian predicate. |
| Canonical manifold integral API | Represented `Real` integrals become the final `integral of forms on M` and `integral on boundary`. | This should be done after localization is stable to avoid moving the target while proving measure facts. |

## Recommended Dependency Ladder

The following order keeps the work mathematical but avoids destabilizing the
existing theorem stack.

1. Build compact-support selected data:
   `CompactlySupportedSmoothFormData -> SelectedBoxPartitionOfUnity` plus
   coherent active interior/boundary boxes.
2. Derive localized interior pieces from the selected partition:
   automatic `localizedInterior` fields and local project equalities.
3. Prove bulk localization from compact-support data:
   a.e. integrand replacement, integrability, and measure-box equality.
4. Prove boundary localization from compact-support boundary data:
   selected boundary measure decomposition and COV term identification.
5. Construct target-image families from local inverse data:
   pure `BoundaryChart` first, then a `Global` adapter.
6. Discharge artificial faces:
   pick the support-zero route if the chart-box selection makes it cheap,
   otherwise build the adjacent-face pairing route.
7. Connect orientation to global oriented manifold data.
8. Replace represented integral fields by canonical manifold-form integrals.

## Concurrency And Build Strategy

Parallelism is useful here because many nodes are isolated, but broad parallel
Lake builds are counterproductive on this Windows workspace.  The wave should
follow these rules:

1. Lean agents own one narrow module or one new adapter file.
2. Agents should prefer `lake env lean path\to\File.lean` or a focused
   `lake build Stokes.Global.Module`; they should not run full `lake build`.
3. Documentation agents do not run Lean builds.  This Agent 18 may run the
   no-placeholder scan only.
4. The parent integration step runs the full `lake build` only after all agents
   have completed or been shut down.
5. Aggregator imports are added last and only after focused checks pass.
6. Never import `Stokes.Global.*` into `Stokes.HalfSpace`.
7. Pure `Stokes.BoundaryChart.*` utilities must stay free of `Stokes.Global.*`
   unless they are explicitly global adapters.

This keeps `.lake/build` from being written by many workers at once and makes
failures attributable to a single owner.

## Reporting Categories

Progress updates for this wave should use these labels:

- Proved theorem: a reusable Lean theorem with real mathematical hypotheses was
  proved.
- Constructor/projection: existing assumptions were repackaged into a cleaner
  API, but the mathematical proof obligation remains upstream.
- True blocker discharged: one of the mathematical nodes above was constructed
  from compact support, selected boxes, chart transitions, measure theory, or
  orientation data.

Only the third label materially shortens the remaining path to the final smooth
manifold Stokes theorem, though the second label can still be valuable when it
makes the next proof small enough to attack.

## Verification Policy For This Agent

This report agent edits only:

```text
reports/stokes-m8-18-agent-wave.md
```

Allowed verification:

```text
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

Forbidden for this agent:

```text
lake build
```

