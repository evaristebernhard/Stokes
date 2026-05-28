# M8 End-to-End Gap Audit

Date: 2026-05-25

Scope: audit what is still needed to construct a
`NaturalCompactSupportStokesInput` / `NaturalCompactSupportBuilderData` from
natural compact-support global data, so that the existing theorem
`naturalCompactSupportStokes_canonical` becomes usable as an end-to-end global
Stokes statement.

This task did not spawn or delegate to any sub-agent.  No Lean files or
aggregator imports were changed.

## Endpoint

The formal endpoint already exists:

```lean
naturalCompactSupportStokes_canonical
  (D : NaturalCompactSupportStokesInput I omega BoundaryPiece μ) :
  D.canonicalIntegralInterface.stokesStatement
```

This theorem is a correct wrapper around the M8 statement.  The remaining work
is not proving this theorem again; it is constructing the input `D` from
natural data:

```text
compactly supported smooth form
  + finite selected chart boxes
  + boundary target boxes
  + measure localization
  + orientation / boundary chart-change data
  -> NaturalCompactSupportStokesInput
  -> naturalCompactSupportStokes_canonical
```

## Required Fields

`NaturalCompactSupportStokesInput` requires:

- `formData : CompactlySupportedSmoothFormData I omega`
- `orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M`
- `selectedPartition : SelectedBoxPartitionOfUnity I omega`
- `selectedPartition_supportSet : selectedPartition.K = formData.supportSet`
- `targetImageInput : M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas BoundaryPiece`
- `measure : CompactSupportToM8MeasureData I omega selectedPartition targetImageInput.targetImages μ`
- `target_boundaryPartitionTerm : targetImageInput.assembly.boundaryPartitionTerm = measure.boundaryPartitionTerm`
- `artificial : M8ArtificialFaceFields I omega BoundaryPiece selectedPartition targetImageInput.targetImages measure.toM8MeasureLocalizationData`

`NaturalCompactSupportBuilderData` has the same core fields, plus:

- `localizedInterior : LocalizedInteriorM8Fields I omega selectedPartition`
- `measure_localizedInterior : measure.toM8MeasureLocalizationData.localizedInterior = localizedInterior.localizedInterior`

The builder-only `localizedInterior` equality is mostly bookkeeping now.  The
hard fields are still `targetImageInput`, `measure`, `target_boundaryPartitionTerm`,
and the construction route for `artificial`.

## Already Automated By Wrappers

These pieces are now mostly projection/constructor plumbing:

- Natural/M8 theorem wrappers:
  - `NaturalCompactSupportStokesInput.toM8CompactSupportStokesInput`
  - `NaturalCompactSupportStokesInput.canonical_stokes`
  - `naturalCompactSupportStokes_canonical`

- Compact-support measure to M8:
  - `CompactSupportToM8MeasureData.toM8MeasureLocalizationData`
  - `CompactSupportMeasureToM8BuilderData.toCompactSupportToM8MeasureData`
  - `CompactSupportMeasureToM8BuilderData.toM8MeasureLocalizationData`

- Bulk selected-box alignment:
  - `BulkMeasureSelectedBoxAlignment.ofMeasure`
  - `CompactSupportMeasureToM8BuilderData.toBulkMeasureSelectedBoxAlignment`
  - `NaturalCompactSupportBuilderData.ofMeasureBuilderWithFormInnerBoxBuffer`
  - `NaturalCompactSupportBuilderData.ofMeasureBuilderWithCoefficientInnerBoxBuffer`

- Selected partition / compact active box alignment:
  - `CompactActiveSelectedPartitionAlignment`
  - `CompactSupportFiniteActiveSelection.toCompactActiveSelectedPartitionAlignment`
  - `CompactActiveSelectedPartitionAlignment.toStrictBufferAlignment`

- Localized interior chart-label alignment, once chart labels are known:
  - `LocalizedInteriorPieceAlignment`
  - `LocalizedInteriorPieceAlignment.piece_transitionPullback_eq`

- Strict-buffer artificial-face route:
  - `LocalizedInteriorFormInnerBoxBuffer.toM8ArtificialFaceFields`
  - `LocalizedInteriorCoefficientInnerBoxBuffer.toM8ArtificialFaceFields`
  - `NaturalCompactSupportStokesInput.ofPackagesWithCompactActiveBoxAlignment`
  - `NaturalCompactSupportBuilderData.ofPackagesWithCompactActiveBoxAlignment`

- Boundary target selected-box alignment:
  - `BoundaryTargetSelectedBoxAlignmentData`
  - `M8TargetImageInput.boundaryTargetSelectedBoxAlignmentData`
  - resolved/local-openness/IFT target-image inputs all route to the same selected-box M8 input

- Target/orientation selected-box alignment:
  - `M8TargetImageInput.toM8TargetOrientationFields`
  - `M8TargetImageInput.sourceSelectedBoxOrientationCovData`
  - `M8TargetImageInput.sourceSelectedBox_orientedChangeOfVariables`

These wrappers reduce name and field threading.  They do not by themselves prove
the measure, inverse-function, or global orientation facts.

## Still Explicit Structure Fields

These are not mathematically impossible, but callers still have to provide them
as fields.

### Natural Form / Partition

- `CompactlySupportedSmoothFormData.supportSet`
- `isCompact_supportSet`
- `support_subset_supportSet`
- `chartwiseSmooth`
- `SelectedBoxPartitionOfUnity.partition`
- `K`, `isCompact_K`, `active`, `active_of_mem_fintsupport`
- selected box corners `lower`, `upper`
- active selected boxes `box`
- equality `selectedPartition.K = formData.supportSet`

Some compact-support finite-selection constructors exist, but the final
end-to-end constructor still needs to choose this data and keep it aligned with
the later bulk, boundary, target-image, and artificial-face packages.

### Localized Interior / Artificial Face

To use the strict-buffer route automatically, the current remaining explicit
data is:

- localized pieces with `sourceChart = x` and `targetChart = x`
- `LocalizedSupportControl` for each localized partition form
- a smooth neighborhood for each localized chart representative
- strict outer/inner margin inequalities between selected boxes and localized
  outer boxes
- `piece_transitionPullback_eq`, now reducible to the source/target chart
  equalities by `LocalizedInteriorPieceAlignment`

Once these are supplied, the artificial-face field is essentially automatic via
strict-buffer wrappers.

### Target Image Input

`M8TargetImageInput` is still nontrivial to build.  The resolved route asks for:

- `BoundaryChartTargetImageResolvedFamily`
- `sourceExtendedBox`
- `partitionTargetChart`
- `partitionTargetBox`
- `partitionSelectedBox`
- `boundaryPartitionTerm`
- `boundaryPartitionTerm_eq`
- `active_eq`
- `source_mem`
- `boundarySource_mem`
- `boundaryTarget_mem`

Wrappers connect this data to M8, but the data itself is not yet generated from
ordinary chart-box selection.

### Measure Package

`CompactSupportToM8MeasureData` still needs a bulk package and a boundary
package:

- `localized : LocalizedInteriorM8Fields`
- `targetImages_active`
- `globalBulkIntegral`
- `bulk : CompactSupportBulkMeasureData`
- `boundaryPartitionTerm`
- `boundary : BoundaryCompactMeasureFields`
- `globalBoundaryIntegral`
- `globalBoundaryIntegral_eq_boundaryMeasureIntegral`

`CompactSupportMeasureToM8BuilderData` packages the same need in a more
constructor-friendly form, but it still asks for the real bulk and boundary
analytic fields.

## Needs Real Mathlib Measure Theorems

These are the main measure-theoretic blockers.

### Bulk Side

For `BulkMeasureFromPartitionData` / `CompactSupportBulkMeasureData`, we still
need to derive from the actual form and selected partition:

- the global scalar bulk integrand `F`
- local interior scalar terms and boundary scalar terms
- localization boxes for each term
- `globalBulkIntegral = ∫ y, F y ∂μ`
- measurability of each active localization box
- compact support or integrability of every active local term
- zero-off-box/support containment for every active local term
- local set-integral identities:
  - interior local bulk term equals its set integral
  - boundary local bulk term equals its set integral
- finite pointwise or a.e. reconstruction:
  - `F` equals the selected finite sum of local scalar terms

This is where the ext-derivative/partition-of-unity reconstruction must meet
mathlib integration.

### Boundary Side

For `BoundaryCompactMeasureFields` /
`CanonicalBoundaryTargetCompactSupportInput`, we still need:

- the true boundary-side measure space and measure
- global boundary integrand
- selected boundary piece support sets
- selected boundary piece scalar integrands
- `boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ`
- active piece-set measurability
- compact support or `IntegrableOn` for every active boundary piece
- set-integral equality:
  - `assembly.boundaryPartitionTerm x q =
     ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ`
- a.e. reconstruction of the global boundary integrand by the finite selected
  indicator sum
- represented global boundary integral equals the boundary measure integral

The target/orientation wrappers give pointwise oriented COV data, but the
set-integral equality and a.e. finite reconstruction still have to be proved
using actual measure/change-of-variables theorems.

## Needs Real Manifold / Orientation Theorems

These are the main geometric blockers.

### Oriented Atlas From Mathlib Data

`BoundaryChartOrientedAtlas` is still a project-local bridge.  To make the
final theorem natural, we need a constructor from real oriented manifold data:

- chart set and cover
- `boundaryChartTransitionCompatibleOn` for atlas chart changes
- `boundaryChartPreservesOrientationOn` for atlas chart changes
- induced boundary orientation agrees with the project sign convention
  `halfSpaceBoundarySign n`

### Target Boxes From Local Openness / IFT

The target-image route still needs concrete boxes:

- local inverse or local openness for the boundary chart transition
- source boundary box cover
- target lower-zero boxes
- target box lies in the source image
- source compact image lies inside the chosen target box
- local inverse / `SurjOn` data for the selected target box

The current `BoundaryChartIFTTargetCoverData` still stores
`targetBox_subset_image` and `compactImage` as fields.  These should be derived
from inverse function theorem, local openness, compact image, and box selection.

### Boundary Chart Change

For each active boundary piece, we still need the true bridge:

```text
boundary chart transition + orientation compatibility + target image data
  -> change of variables for the boundary set integral
  -> project-local boundary term equals selected boundary set integral
```

The wrapper
`M8TargetImageInput.sourceSelectedBox_orientedChangeOfVariables` reaches the
project-local COV statement, but the boundary measure package still needs the
integral-level equality in the exact `BoundaryCompactMeasureFields` shape.

## Current Shortest Construction Route

The shortest current route should be:

```text
CompactlySupportedSmoothFormData
  + CompactSupportFiniteActiveSelection
  + selected localized interior pieces
  + strict compact-active box alignment
  + M8TargetImageInput
  + CompactSupportMeasureToM8BuilderData
  + target boundary-term equality
  -> NaturalCompactSupportBuilderData
  -> NaturalCompactSupportStokesInput
  -> naturalCompactSupportStokes_canonical
```

The strict-buffer/artificial-face branch is no longer the largest blocker.  The
largest blockers are now:

1. construct target-image boxes from real IFT/local openness;
2. prove bulk measure reconstruction from ext-derivative + partition;
3. prove boundary measure reconstruction from oriented boundary COV;
4. connect `BoundaryChartOrientedAtlas` to mathlib-oriented manifold data.

## Suggested Next Agent Wave

Use separate agents with disjoint write scopes.  No agent should edit
`Stokes/Global.lean`; the main thread should aggregate only after focused
checks pass.

1. File: `Stokes/Global/EndToEndRemainingInput.lean`
   Goal: define one zero-semantics record
   `NaturalCompactSupportEndToEndInput` that bundles exactly the remaining
   explicit fields and proves:
   - `NaturalCompactSupportEndToEndInput.toNaturalCompactSupportStokesInput`
   - `naturalCompactSupportStokes_canonical_of_endToEnd`

2. File: `Stokes/Global/BulkMeasureExtDerivFromPartition.lean`
   Goal: start the real bulk measure theorem:
   - construct canonical `F`, `interiorLocalTerm`, `boundaryLocalTerm`
   - prove the finite pointwise/a.e. reconstruction lemma against selected
     partition terms
   - target theorem shape:
     `SelectedBoxPartitionOfUnity.bulkMeasureFromExtDerivPartitionData`

3. File: `Stokes/Global/BoundaryMeasureFromTargetCOV.lean`
   Goal: consume
   `M8TargetImageInput.sourceSelectedBox_orientedChangeOfVariables` and prove
   the boundary set-integral field:
   - target theorem shape:
     `M8TargetImageInput.boundaryPartitionTerm_eq_setIntegral_of_orientedCOV`

4. File: `Stokes/BoundaryChart/TargetBoxFromIFT.lean`
   Goal: remove explicit target-box fields from IFT data:
   - prove target box selection from local openness plus compact image/box
     selection
   - target theorem shape:
     `exists_boundaryChartTargetBoxSelection_of_localOpenness_compactImage`

5. File: `Stokes/BoundaryChart/OrientedAtlasFromMathlib.lean`
   Goal: connect the project-local oriented atlas record to real mathlib
   orientation data:
   - target theorem shape:
     `BoundaryChartOrientedAtlas.ofMathlibOrientedManifold`

6. File: `Stokes/Global/CompactSupportSelectedBoxEndToEnd.lean`
   Goal: construct selected partition, compact active boxes, localized pieces,
   and strict-buffer alignment from compact support in one route:
   - target theorem shape:
     `exists_compactSupportSelectedPartition_withStrictBufferAlignment`

7. File: `Stokes/Global/BoundaryMeasureAEReconstruction.lean`
   Goal: prove the finite selected boundary indicator reconstruction once the
   piece sets and integrands are chosen:
   - target theorem shape:
     `boundaryIntegrand_ae_eq_selectedTargetIndicatorSum`

8. File: `Stokes/Global/MeasureBuilderFromCanonicalPieces.lean`
   Goal: combine successful bulk and boundary measure outputs into:
   - `CompactSupportMeasureToM8BuilderData`
   - then `CompactSupportToM8MeasureData`

The highest-leverage order is: first create `EndToEndRemainingInput` so the
exact target is visible, then split bulk measure, boundary COV/measure, target
box IFT, and oriented-atlas bridge in parallel.

