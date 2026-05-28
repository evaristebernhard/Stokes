# Target / Orientation Alignment Audit

Date: 2026-05-25

Scope: audit the path from selected boundary target-image data and oriented
atlas data to `M8TargetImageInput`, `M8TargetOrientationFields`, and the
boundary-measure route.  This task did not spawn or delegate to any sub-agent.

## Files Read

- `Stokes/BoundaryChart/OrientationAtlasBoundarySign.lean`
- `Stokes/BoundaryChart/TargetImageSelectedBoxAuto.lean`
- `Stokes/Global/OrientationBridgeToM8.lean`
- `Stokes/Global/OrientedAtlasToM8.lean`
- `Stokes/Global/TargetImageToM8.lean`

Additional context checked:

- `Stokes/Global/TargetImageResolvedToM8Input.lean`
- `Stokes/Global/BoundaryTargetImageToAssembly.lean`
- `Stokes/Global/BoundaryMeasureTargetAssembly.lean`
- `Stokes/Global/BoundaryMeasureCanonicalRoute.lean`

## Field Chain

Single selected box:

```text
BoundaryChartSelectedBoxTargetImageAutoData
  selectedBox
  targetBox
    lowerCorner / upperCorner
    compactImage
    localInverse
    imageData / mapsTo / surjOn

BoundaryChartAtlasBoundarySignData
  selectedBox
  compatibleOn
  orientationMapDataOn
  preservesOrientationOn
  boundary sign = outward-first sign

target image data + boundary sign/orientation data
  -> BoundaryChartSelectedBoxOrientationCovData
  -> boundaryChartOrientedChangeOfVariables
```

Finite target-image family:

```text
BoundaryChartTargetImageResolvedFamily
  activeCharts / localPieces
  sourceChart / boundarySourceChart / boundaryTargetChart
  sourceLowerCorner / sourceUpperCorner
  sourceSelectedBox
  targetBox
  targetSelectedBox

M8TargetImageResolvedInput
  family
  sourceExtendedBox
  partitionTargetChart / partitionTargetBox / partitionSelectedBox
  boundaryPartitionTerm / boundaryPartitionTerm_eq
  active_eq
  source_mem / boundarySource_mem / boundaryTarget_mem

  -> toAssemblyInput
  -> toM8TargetImageInput
```

M8 target/orientation route:

```text
M8TargetImageInput
  assembly
  active_eq
  source_mem
  boundarySource_mem
  boundaryTarget_mem

  -> targetImages : BoundaryPieceFamilyInput
  -> targetImages_active
  -> targetImages_source_mem
  -> targetImages_boundarySource_mem
  -> selectedBoundaryAssemblyData
  -> targetBoundaryTerm_eq_measureLocalization

M8TargetOrientationFields
  orientedBoundaryAtlas
  source_mem
  boundarySource_mem

M8TargetImageInput.toM8TargetOrientationFields   [new wrapper]
```

Boundary-measure route:

```text
M8TargetImageInput
  -> toSelectedBoundaryMeasurePartitionData
  -> boundaryMeasureLocalizationDataOfIntegrableOn
  -> boundaryMeasureDataOfIntegrableOn

CanonicalBoundaryTargetCompactSupportInput
  boundaryIntegrand
  boundaryPieceSet
  boundaryPieceIntegrand
  boundaryMeasureIntegral_eq_integral
  boundaryPieceSet_measurable
  boundaryPieceCompact
  boundaryPartitionTerm_eq_setIntegral
  boundaryIntegrand_ae_eq_indicatorSum
  globalBoundaryIntegral_eq_boundaryMeasureIntegral

  -> canonicalBoundaryCompactFields
  -> canonicalBoundaryLocalizationData
  -> canonicalBoundaryM8MeasureData
```

## Wrapper Layer Already Available

These parts are bookkeeping wrappers rather than new mathematics:

- `BoundaryChartSelectedBoxTargetImageAutoData` projects target corners,
  compact-image data, local inverse data, image data, `MapsTo`, and `SurjOn`
  from a selected target box.
- `BoundaryChartAtlasBoundarySignData` projects selected-box compatibility,
  orientation-map data, Jacobian positivity, and the outward-first sign
  convention.
- `BoundaryChartTargetImageResolvedFamily` converts proof-indexed target boxes
  into a proof-free target-box family and then into COV-family data.
- `M8TargetImageResolvedInput.toM8TargetImageInput` adds only global assembly,
  selected-partition active-set alignment, and oriented-atlas membership.
- `M8TargetImageInput.targetBoundaryTerm_eq_measureLocalization` already
  connects the target-image assembly boundary term to an `M8MeasureLocalizationData`
  boundary partition term, once the equality of terms is supplied.
- `M8OrientationBridgeFields.toM8TargetOrientationFields` forgets a future
  mathlib-oriented bridge into the exact M8 orientation fields.
- New file `Stokes/Global/TargetOrientationSelectedBoxAlignment.lean` adds:
  - `BoundaryChartSelectedBoxTargetImageAutoData.toOrientationCovData`
  - `BoundaryChartSelectedBoxTargetImageAutoData.orientedChangeOfVariables`
  - `M8TargetImageInput.toM8TargetOrientationFields`
  - `M8TargetImageInput.sourceSelectedBoxBoundarySignData`
  - `M8TargetImageInput.sourceSelectedBoxOrientationCovData`
  - `M8TargetImageInput.sourceSelectedBox_orientedChangeOfVariables`

The new wrapper is intentionally not imported by an aggregator in this task.

## Real Mathematical Inputs Still Needed

Target image / local inverse:

- Construct `BoundaryChartTargetBoxSelection` from actual inverse function
  theorem or local openness data.
- Prove the compact-image target-box field
  `boundaryChartCompactCoordinateImageForLocalInverseTargets`, i.e. the same
  target box selected by local inverse also contains the compact image of the
  source boundary box.
- Prove active selected boxes are aligned with the selected partition used by
  bulk, boundary measure, artificial faces, and target image.

Orientation:

- Derive `BoundaryChartMathlibOrientedAtlasBridge.compatibleOn` from the real
  mathlib manifold chart API.
- Derive `BoundaryChartMathlibOrientedAtlasBridge.preservesOrientationOn` from
  the real oriented manifold / oriented atlas data.
- For a global oriented manifold with boundary, prove that the induced boundary
  orientation matches the project convention
  `halfSpaceBoundarySign n = outwardFirstBoundaryOrientationSign n`.

Boundary assembly:

- Build `sourceExtendedBox` from the same selected chart-box data used by the
  compact-support localization.
- Build `partitionTargetBox` and `partitionSelectedBox` for the boundary
  partition representative.
- Prove `boundaryPartitionTerm_eq`, namely that the recorded boundary partition
  term is exactly the appropriate `projectLocalBoundaryIntegral`.
- Prove `measureLocalization_boundaryTerm`, identifying the assembly boundary
  partition term with the boundary term in the measure-localization package.

Boundary measure:

- Define the true boundary-side measurable space, measure, global integrand,
  piece support sets, and piece integrands.
- Prove active piece measurability and compact-support or integrability.
- Prove every active partition term is the corresponding set integral.
- Prove the global boundary integrand is almost everywhere the finite selected
  indicator sum.
- Prove the represented global boundary integral equals the boundary measure
  integral.

## Current Status

The target/orientation branch is now cleaner at the wrapper level:

```text
M8TargetImageInput
  -> M8TargetOrientationFields
  -> pointwise selected-box orientation/COV data
```

This removes one bookkeeping gap.  The remaining blockers are not naming
issues; they are the real geometry and measure proofs listed above.
