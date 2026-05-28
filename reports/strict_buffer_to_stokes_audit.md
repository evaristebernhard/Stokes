# Strict Buffer to Stokes Audit

Date: 2026-05-25

Scope: controlled audit task 5.  No subagents were spawned, no aggregation file
was changed, and no Lean wrapper was added.

Read files:

- `Stokes/Global/CompactSupportStrictBuffer.lean`
- `Stokes/Global/ArtificialFaceSupportZeroGeometry.lean`
- `Stokes/Global/ArtificialFaceNaturalBuilder.lean`
- `Stokes/Global/NaturalCompactSupportBuilder.lean`
- `Stokes/Global/BoundaryMeasureCanonicalRoute.lean`
- `Stokes/Global/BulkMeasureCanonicalRoute.lean`

## Executive Summary

The strict interior buffer route now solves one important local-Stokes boundary
problem: it kills artificial faces coming from auxiliary chart boxes.  It does
not yet construct the true boundary integral of the manifold, nor the true bulk
measure localization.  In the current architecture, `strict buffer -> artificial
faces vanish` is already consumable by the natural compact-support builder, but
`canonical_stokes` still needs three other packages to be genuinely built:

1. bulk measure localization,
2. boundary measure localization,
3. boundary target-image and orientation compatibility.

So the current status is:

```text
strict buffer
  -> artificial-face field solved
  -> NaturalCompactSupportBuilder can consume it
  -> canonical_stokes available only after measure + target/orientation packages exist
```

The strict buffer is therefore necessary, and the API route is good, but it is
not the last blocker.

## Field Chain: Strict Buffer to canonical_stokes

The concrete field chain is:

```text
CompactSupportBoxBuffer
  .strictSupport_subset_interiorBox

-> CompactSupportBoxBuffer.toSelectedPartitionSupportZeroGeometry
     produces SelectedPartitionSupportZeroGeometry.support_subset_interiorBox

-> SelectedPartitionSupportZeroGeometry.localizedArtificialBoundaryTerm_eq_zero
     proves each active projected artificial boundary integral is 0

-> SelectedPartitionSupportZeroGeometry.interiorBoundaryTerm_eq_zero
     rewrites this into the singleton M8 interior-boundary term

-> SelectedPartitionSupportZeroGeometry.toArtificialFaceResolvedData
     builds ArtificialFaceResolvedData.of_forall_eq_zero

-> SelectedPartitionSupportZeroGeometry.toM8ArtificialFaceFields
     builds M8ArtificialFaceFields.ofResolved

-> CompactSupportBoxBuffer.toM8ArtificialFaceFields
     exposes the same M8ArtificialFaceFields from the buffer package

-> NaturalCompactSupportBuilderData.ofPackagesWithCompactSupportBoxBuffer
     sets artificial := buffer.toM8ArtificialFaceFields

-> NaturalCompactSupportBuilderData.toNaturalCompactSupportStokesInput
     produces NaturalCompactSupportStokesInput with the artificial field solved

-> NaturalCompactSupportStokesInput.toArtificialFaceResolved
     exposes M8CompactSupportArtificialFaceResolvedData

-> NaturalCompactSupportStokesInput.toM8CompactSupportStokesInput
     assembles the compact-support M8 input

-> NaturalCompactSupportStokesInput.canonical_stokes
     delegates to D.toM8CompactSupportStokesInput.canonical_stokes
```

There is also a direct compact-support-resolved route:

```text
CompactSupportBoxBuffer.toCompactSupportArtificialFaceResolvedData
  -> M8CompactSupportArtificialFaceResolvedData.ofCompactSupportBoxBuffer
  -> M8CompactSupportStokesInput.artificialFaceResolved
```

This means the artificial-face side is architecturally connected.  The missing
work is not a missing projection lemma; it is the construction of the real
inputs consumed by the measure and boundary-target fields.

## What Strict Buffer Actually Solves

The relevant geometric input is:

```text
forall x, x in selectedPartition.active ->
  tsupport
    (ManifoldForm.transitionPullbackInChart I
      piece.sourceChart piece.targetChart piece.localizedForm)
    subset boxInteriorSupportBox piece.lowerCorner piece.upperCorner
```

Given this field, `ArtificialFaceSupportZeroGeometry.lean` proves:

- the projected artificial boundary term of each active local chart is zero;
- the M8 singleton interior-boundary term is zero;
- artificial faces can be packaged as `M8ArtificialFaceFields`;
- the package aligns active charts, singleton pieces, and the M8
  `interiorBoundaryTerm`.

`CompactSupportStrictBuffer.lean` adds two useful upstream routes:

- inner closed box plus strict coordinate margins gives strict interior support;
- strict support of transition coefficients gives strict support of localized
  transition-pullback representatives.

That is exactly the right bridge from compact-support chart-box selection to
artificial-face cancellation.

## What It Does Not Solve

Strict buffer only removes the artificial faces of selected coordinate boxes.
It does not prove anything about:

- the true manifold bulk integral of `d omega`;
- the true boundary integral of `omega`;
- boundary chart images and local inverse data;
- the orientation sign relating boundary charts to outward-normal-first
  conventions;
- the equality between local chart boundary integrals and the global boundary
  measure integral.

In other words, strict buffer closes the "extra box faces" part of local Stokes.
The real boundary of the manifold remains a separate measure, chart-change, and
orientation problem.

## Remaining Blocker 1: Bulk Measure Localization

`BulkMeasureCanonicalRoute.lean` is only a projection layer.  Once a
`NaturalCompactSupportStokesInput` already has
`D.measure : CompactSupportToM8MeasureData`, it exposes:

- `canonicalBulkCompactSupportData`;
- `canonicalBulkMeasureLocalizationFields`;
- `canonicalBulkM8Fields`;
- `canonicalBulkAEIndicatorLocalization`;
- compact-support integrability for interior and boundary local terms;
- the finite local-bulk-sum equality.

The real missing theorem is upstream of this file:

```text
geometric compact-support chart data
  -> CompactSupportToM8MeasureData
  -> CompactSupportBulkMeasureData
```

Concretely, we still need to prove that the true bulk integrand is almost
everywhere equal to the finite selected indicator sum, and that its integral
matches the M8 local-bulk finite sum.  This includes:

- defining the true bulk integrand for the manifold compact-support statement;
- aligning it with local chart representatives of `extDeriv omega`;
- proving piecewise compact-support integrability;
- proving the a.e. finite selected-partition reconstruction;
- proving the local set-integral terms are exactly the M8 `bulkTerm` and
  boundary-bulk terms used by local Stokes.

Strict buffer helps keep unwanted artificial boundary terms out of local Stokes,
but it does not supply this bulk measure reconstruction.

## Remaining Blocker 2: Boundary Measure Localization

`BoundaryMeasureCanonicalRoute.lean` also mostly projects existing data.  The
record `CanonicalBoundaryTargetCompactSupportInput` shows the true required
boundary-side inputs:

- `boundaryIntegrand`;
- `boundaryPieceSet`;
- `boundaryPieceIntegrand`;
- `boundaryMeasureIntegral`;
- measurable boundary piece sets;
- compact-support integrability for each boundary piece;
- equality between boundary partition terms and set integrals;
- a.e. reconstruction by selected boundary indicator pieces;
- equality between represented global boundary integral and boundary measure
  integral.

The missing theorem is:

```text
selected boundary chart data + target images + orientation COV
  -> CanonicalBoundaryTargetCompactSupportInput
  -> BoundaryCompactMeasureFields
  -> BoundaryMeasureLocalizationData
  -> M8BoundaryMeasureData
```

This is the main boundary-side mathematical payload.  It must show that the
true boundary integral decomposes into the selected oriented boundary chart
pieces and that every piece integral is the same term used by the local
half-space Stokes theorem.

Strict buffer does not affect this except indirectly: after artificial faces
vanish, the only remaining local boundary terms should be the genuine boundary
pieces.  The boundary measure theorem still has to identify those pieces with
the manifold boundary integral.

## Remaining Blocker 3: Orientation and Target Image

The natural compact-support statement requires:

```text
targetImageInput :
  M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas BoundaryPiece
```

and the canonical boundary measure route expects target pieces to already be
aligned with the boundary partition term:

```text
targetImageInput.assembly.boundaryPartitionTerm =
  measure.boundaryPartitionTerm
```

The remaining target/orientation work is:

- construct target boundary boxes from selected source boundary boxes;
- prove local inverse / image data for boundary chart transitions;
- prove the image of the source boundary box is the selected target boundary
  box, or at least an aligned measurable target piece;
- connect the boundary chart transition derivative to the tangential map used
  by the project-local API;
- connect project-local positive Jacobian or orientation predicates to the
  actual oriented manifold / oriented atlas data;
- prove the boundary chart change-of-variables theorem with the
  outward-normal-first sign convention.

This is exactly where the target-image auto wrappers and orientation sign
wrappers are useful, but they are still wrapper layers.  The hard proof is the
mathlib-facing chart transition, inverse-function/local-openness, and
orientation bridge.

## Remaining Blocker 4: Selected Box Alignment

The strict buffer has to refer to the exact boxes and local pieces stored in:

```text
measure.toM8MeasureLocalizationData.localizedInterior.piece x
```

The same selected active chart `x` also appears in:

- `selectedPartition.active`;
- `LocalizedInteriorM8Fields`;
- `targetImageInput.targetImages.activeCharts`;
- `measure.localized.localizedInterior.active`;
- bulk local terms;
- boundary target pieces;
- artificial-face terms.

The alignment theorem we still need is stronger than "there exists some box":

```text
selected compact-support chart-box construction
  -> selectedPartition
  -> localizedInterior
  -> measureLocalization
  -> targetImageInput
  -> same active charts and same selected boxes everywhere
```

Without this alignment, strict support may hold for a convenient auxiliary box
but not for the actual `lowerCorner` and `upperCorner` fields consumed by local
Stokes and M8.

## Recommended Next Proof Tasks

The next productive work should be split into four independent tracks:

1. Strict buffer construction:
   prove that compact support plus buffered chart-box selection produces
   `CompactSupportBoxBuffer` for the actual M8 localized-interior pieces.

2. Bulk measure construction:
   build `CompactSupportToM8MeasureData` from the true compact-support bulk
   integrand and selected partition data.

3. Boundary measure construction:
   build `CanonicalBoundaryTargetCompactSupportInput` from selected boundary
   chart pieces, including boundary COV and a.e. finite reconstruction.

4. Target/orientation construction:
   derive target boundary boxes, local inverse/image data, tangential derivative
   compatibility, and orientation sign compatibility from chart/oriented-atlas
   data.

The key dependency is:

```text
target/orientation construction
  -> boundary measure construction
  -> natural compact-support input

strict buffer construction
  -> artificial-face field of the same natural input

bulk measure construction
  -> measure field of the same natural input
```

Once all three branches feed the same selected partition and the same measure
localization package, `NaturalCompactSupportStokesInput.canonical_stokes` should
be a short projection theorem, not a new mathematical proof.

## Bottom Line

The strict interior buffer route is in good shape and should remain the
preferred route for artificial faces.  Its effect on local Stokes is clean:
all non-manifold chart-box faces disappear.

The distance to compact-support global Stokes is now concentrated in measure
and boundary-chart construction, not in artificial-face cancellation.  The next
highest-value theorem is a selected-box alignment theorem that constructs the
strict buffer and simultaneously fixes the boxes used by bulk, boundary, and
target-image localization.
