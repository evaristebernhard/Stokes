# Stokes module consolidation audit

Date: 2026-05-25

Scope: `Stokes/BoundaryChart` and `Stokes/Global`.  This is an architecture
audit only.  No existing Lean file was moved, deleted, or edited.  One small
BoundaryChart facade was added:

- `Stokes/BoundaryChart/BoundaryChartCOVFacade.lean`

## Snapshot

- `Stokes/BoundaryChart`: 49 files, about 16.6k Lean lines, about 1.1k top-level
  declarations matched by `structure|def|abbrev|theorem|lemma`.
- `Stokes/Global`: 192 files, about 57.0k Lean lines, about 3.7k matched
  top-level declarations.
- Name-pattern audit:
  - `BoundaryChart`: roughly 22 core/geometry files, 24 adapter/projection files,
    3 assembly/convenience files.
  - `Global`: roughly 49 core/geometry-support files, 100 adapter/projection
    files, 42 statement/assembly files.

The problem is not that splitting happened; the problem is that public entry
points and private implementation strata are not marked.  As a result each wave
imports deep implementation files directly and often creates another small
`*Auto` file instead of extending an existing family.

## BoundaryChart classification

### Keep as core implementation modules

These files contain definitions or mathematical geometry that should remain
available to proof developers, but should not be the default import for global
assembly users:

- `Stokes/BoundaryChart/Basic.lean`: boundary chart transition, tangential map,
  Jacobian, basic domain predicates.
- `Stokes/BoundaryChart/SelectedBox.lean`: selected source box predicate and
  derivative-on-box route.
- `Stokes/BoundaryChart/Orientation.lean`: local orientation predicates and
  positive Jacobian compatibility.
- `Stokes/BoundaryChart/LocalInverse.lean`: image data, local inverse data,
  inverse-image and surjectivity conversions.
- `Stokes/BoundaryChart/ChangeOfVariables.lean`: real COV theorem from mathlib,
  oriented chart-change invariant statements.
- `Stokes/BoundaryChart/LocalStokes.lean`: local half-space/boundary Stokes
  statements over selected boxes.
- `Stokes/BoundaryChart/TransitionDerivative.lean`: derivative bridge for chart
  transitions.
- `Stokes/BoundaryChart/TransitionCompactBox.lean`: compact chart-box transition
  selection.
- `Stokes/BoundaryChart/BoundaryBoxSelection.lean`: compact-support selected
  boundary box selection.
- `Stokes/BoundaryChart/TargetBoxSelection.lean`,
  `Stokes/BoundaryChart/TargetBoxFromIFT.lean`,
  `Stokes/BoundaryChart/TargetBoxCompactImage.lean`,
  `Stokes/BoundaryChart/TargetBoxSourceShrink.lean`,
  `Stokes/BoundaryChart/TargetBoxSourceShrinkInverse.lean`,
  `Stokes/BoundaryChart/TargetBoxSourceShrinkIFT.lean`: target-box and
  source-shrink geometry.
- `Stokes/BoundaryChart/CompactImageCover.lean` and
  `Stokes/BoundaryChart/TargetBoxFamilySelection.lean`: family-level compact
  image/target-box selection.

### Keep as private-ish projection/adapter modules

These files mostly convert one existing package into another, project fields,
or provide method-style wrappers.  They are useful, but future agents should
prefer importing a facade rather than importing these directly from global code:

- `Stokes/BoundaryChart/OrientationBridge.lean`
- `Stokes/BoundaryChart/OrientationConvenience.lean`
- `Stokes/BoundaryChart/OrientationCovBridge.lean`
- `Stokes/BoundaryChart/OrientationNatural.lean`
- `Stokes/BoundaryChart/OrientationMathlibBridge.lean`
- `Stokes/BoundaryChart/OrientedAtlasBridge.lean`
- `Stokes/BoundaryChart/OrientedAtlasFromMathlib.lean`
- `Stokes/BoundaryChart/OrientationAtlasBoundarySign.lean`
- `Stokes/BoundaryChart/OrientationAtlasSelectedBoxBuilder.lean`
- `Stokes/BoundaryChart/BoundaryChartPositiveJacobianFromAtlas.lean`
- `Stokes/BoundaryChart/PositiveJacobianOrientationRoute.lean`
- `Stokes/BoundaryChart/SelectedBoxCOVFromOrientationAuto.lean`
- `Stokes/BoundaryChart/CompactImageFromIFTAuto.lean`
- `Stokes/BoundaryChart/SelectedBoxIFTAuto.lean`
- `Stokes/BoundaryChart/SelectedBoxImageDataAuto.lean`
- `Stokes/BoundaryChart/SelectedBoxContainsAuto.lean`
- `Stokes/BoundaryChart/SelectedImageBoxFromTargetAuto.lean`
- `Stokes/BoundaryChart/SourceShrinkMapsToAuto.lean`
- `Stokes/BoundaryChart/TargetImageFieldReduction.lean`
- `Stokes/BoundaryChart/TargetImageFromLocalInverse.lean`
- `Stokes/BoundaryChart/TargetImageLocalOpenness.lean`
- `Stokes/BoundaryChart/TargetImageIFTBridge.lean`
- `Stokes/BoundaryChart/TargetImageSelectedBoxAuto.lean`
- `Stokes/BoundaryChart/TargetImageSelectedBoxBuilder.lean`

Special note:

- `Stokes/BoundaryChart/TargetBoxToM8Glue.lean` imports
  `Stokes.Global.TargetImageResolvedToM8Input`.  It is semantically global glue,
  not pure BoundaryChart geometry.  Do not import it from a BoundaryChart facade.
  Later, if a real reorganization is allowed, it should move logically under a
  global boundary-target namespace/file family.

### Public BoundaryChart facade

New public facade:

- `Stokes/BoundaryChart/BoundaryChartCOVFacade.lean`

Current import layer:

```lean
import Stokes.BoundaryChart.ChangeOfVariablesFamily
import Stokes.BoundaryChart.OrientedAtlasSelectedBoxCOV
import Stokes.BoundaryChart.BoundaryChartPositiveJacobianFromAtlas
import Stokes.BoundaryChart.SelectedBoxCOVFromOrientationAuto
import Stokes.BoundaryChart.SelectedBoxContainsAuto
import Stokes.BoundaryChart.SelectedImageBoxFromTargetAuto
import Stokes.BoundaryChart.SourceShrinkMapsToAuto
import Stokes.BoundaryChart.SelectedImageBoxContainmentFromShrinkAuto
import Stokes.BoundaryChart.SourceShrinkSelectedCOVFacade
```

Intended use:

- Global/M8 files that only need boundary chart COV, selected-box oriented COV,
  local-openness/IFT COV, or source-shrink-to-COV APIs should import this facade.
- The source-shrink route should use
  `SelectedImageBoxContainmentFromShrinkAuto` for the real box-containment
  geometry and `SourceShrinkSelectedCOVFacade` for theorem-facing COV wrappers.
- Local BoundaryChart proof files should keep importing narrower dependencies
  to preserve fast focused checks.
- This facade deliberately does not import `TargetBoxToM8Glue.lean`, because
  that would make BoundaryChart depend publicly on Global.

Suggested later facades, if needed:

- `Stokes/BoundaryChart/BoundaryChartGeometryFacade.lean`: `Basic`,
  `SelectedBox`, `LocalInverse`, `TransitionDerivative`, `TransitionCompactBox`,
  `BoundaryBoxSelection`, `TargetBoxSelection`, `TargetBoxFromIFT`,
  `TargetBoxCompactImage`, `TargetBoxSourceShrink*`.
- `Stokes/BoundaryChart/BoundaryChartOrientationFacade.lean`: orientation and
  atlas bridge files only.

## Global classification

### Stable public endpoint candidates

These are the files users or blueprint nodes should eventually import directly
or via a facade:

- `Stokes/Global/Theorem.lean`: final algebraic Stokes package.
- `Stokes/Global/M8Statement.lean`: M8-facing global Stokes statement.
- `Stokes/Global/M8CompactSupportStatement.lean`: compact-support M8 statement.
- `Stokes/Global/NaturalCompactSupportStokesStatement.lean`: natural compact
  support statement.
- `Stokes/Global/NaturalCompactSupportCombinedEndpoint.lean`: current combined
  compact-support endpoint with separated boundary measure.
- `Stokes/Global/NaturalCompactSupportEndpointConcrete.lean`: endpoint base
  sources.
- `Stokes/Global/SelectedReconstructionSourceAuto.lean` and
  `Stokes/Global/SelectedReconstructionSourceConstructorsAuto.lean`: endpoint
  reconstruction-source route.
- `Stokes/Global/NaturalCompactSupportEndpointMarginAuto.lean`: current endpoint
  strict-margin route.
- `Stokes/Global/CanonicalNaturalCompactSupport.lean`: canonical compact-support
  endpoint route.

Recommendation: expose these through a future
`Stokes/Global/CompactSupportEndpointFacade.lean`, then stop adding new imports
to `Stokes/Global.lean` for every tiny endpoint adapter.

### Real mathematical/support content

These files carry actual support, smoothness, compactness, integrability,
finite-active, chart-box, or cancellation work.  They should remain as
implementation modules and be cited by reports/blueprints:

- Partition and support:
  `Partition.lean`, `FiniteActive.lean`, `PartitionSumOne.lean`,
  `PartitionCompactSupport.lean`, `PartitionLocalizedEventually.lean`,
  `LocalizedSupport.lean`, `LocalizedSmoothness.lean`, `SupportFiniteSum.lean`,
  `IndicatorSupportLocalization.lean`.
- Chart boxes and compact support:
  `ChartCompactImage.lean`, `CompactSupportChartBox.lean`,
  `CompactSupportFiniteActiveSelection.lean`, `CompactActiveBoxes.lean`,
  `StrictInnerOuterBox.lean`, `CompactSupportStrictBuffer.lean`,
  `CompactSupportStrictBufferFromActive.lean`,
  `CoefficientBoxSupport.lean`, `CoefficientStrictBuffer.lean`,
  `CompactSupportBoxBufferBuilder.lean`.
- Ext-derivative/reconstruction support:
  `ExtDerivReconstruction.lean`, `ExtDerivOnSupport.lean`,
  `ExtDerivEventually.lean`, `ExtDerivPartitionConstructor.lean`,
  `BulkExtDerivFromExtDerivConstructor.lean`,
  `BulkExtDerivSelectedAlignmentAuto.lean`.
- Artificial-face geometry/cancellation:
  `ArtificialFaceGeometry.lean`, `ArtificialFacePairing.lean`,
  `ArtificialFaceOverlapPairing.lean`, `ArtificialFaceAdjacency.lean`,
  `ArtificialFaceSelection.lean`, `ArtificialFaceSupportZeroGeometry.lean`,
  `ArtificialFaceBufferSupport.lean`, `Cancellation.lean`.
- Boundary measure route:
  `BoundaryCanonicalFaceMeasureFacts.lean`,
  `BoundaryCanonicalFiniteReconstruction.lean`,
  `BoundaryIndicatorCompactSupport.lean`,
  `BoundaryCanonicalRouteFromContinuity.lean`,
  `BoundarySourceSetIntegral.lean`, `BoundaryPieceSupportFiniteSum.lean`.

### Private-ish global projection layers

These are valuable but should be considered implementation plumbing:

- All `*ToM8.lean` files:
  `ArtificialFaceToM8.lean`, `ArtificialFacePairingToM8.lean`,
  `ArtificialFaceSupportZeroToM8.lean`, `ArtificialFaceAdjacencyToM8.lean`,
  `ArtificialFaceNaturalToM8.lean`, `BulkMeasureToM8.lean`,
  `BoundaryMeasureToM8.lean`, `CompactSupportToM8Measure.lean`,
  `TargetImageToM8.lean`, `TargetImageResolvedToM8Input.lean`,
  `TargetImageLocalOpennessToM8.lean`, `TargetImageIFTToM8.lean`,
  `OrientedAtlasToM8.lean`, `OrientationBridgeToM8.lean`,
  `BulkExtDerivMeasureToM8.lean`, `BulkMeasureProjectLocalToM8.lean`.
- All `*Builder.lean`, `*Constructor.lean`, `*Adapters.lean`, `*Wrappers.lean`,
  `*Glue.lean`, `*FieldReduction.lean`, and most `*Auto.lean` files unless
  they are explicitly chosen as a public facade.
- Audit files such as `BuilderProjectionAudit.lean` and
  `MeasureLocalizationAudit.lean` should not be public imports.

### Existing global import issue

`Stokes/Global.lean` currently acts as a kitchen-sink import with more than 150
direct imports.  This is useful for `import Stokes.Global` smoke testing, but
bad as a development API.  Keep it as a heavy aggregate; do not make it the
only public path.

Recommended future public import hierarchy:

```text
Stokes.BoundaryChart.BoundaryChartCOVFacade
  -> selected-box/oriented COV and local-openness/IFT COV API

Stokes.Global.M8Facade                  [future]
  -> M8Statement, M8MeasureConstructors, TargetImage*ToM8, OrientedAtlasToM8

Stokes.Global.CompactSupportEndpointFacade  [future]
  -> NaturalCompactSupportCombinedEndpoint
  -> NaturalCompactSupportEndpointConcrete
  -> SelectedReconstructionSourceAuto
  -> SelectedReconstructionSourceConstructorsAuto
  -> NaturalCompactSupportEndpointSelected*Auto
  -> NaturalCompactSupportEndpointConstructorFieldsAuto
  -> NaturalCompactSupportEndpointMarginAuto
  -> CanonicalNaturalCompactSupport

Stokes.Global                            [existing heavy aggregate]
  -> import all stable modules for full build/regression only
```

## Concrete consolidation strategy

### Do not move files yet

Moving 200+ Lean modules while agents are active would create needless import
conflicts.  The short-term consolidation should be facade-first:

1. Add small public facade files.
2. Teach later agents to import the facade.
3. Stop adding every small adapter directly to `Stokes/Global.lean`.
4. Only after the theorem-facing API stabilizes, do a mechanical move/rename
   pass.

### Merge-by-family rules for future work

Use these rules before creating another file:

- If the new declaration is only a field projection, `rfl` theorem, or one-step
  constructor around an existing record, add it to the existing nearest
  `*Auto`, `*Builder`, or `*Constructor` file.
- If a file would contain fewer than about 5 meaningful declarations and no new
  theorem family, do not create it unless it breaks an import cycle.
- If the declaration is a user-facing theorem route, place it in a facade-facing
  module or add it to an existing public route file.
- If the proof introduces a new mathematical idea, such as compact image box
  selection from IFT or strict buffer selection from compact support, give it a
  real core module name, not another `*Auto`.
- If a file imports from `Stokes.Global`, it should not live under
  `Stokes.BoundaryChart` unless it is explicitly marked cross-layer glue.

### Recommended import discipline for agents

Boundary-chart COV work:

```lean
import Stokes.BoundaryChart.BoundaryChartCOVFacade
```

Boundary-chart local geometry work:

```lean
import Stokes.BoundaryChart.LocalInverse
import Stokes.BoundaryChart.TransitionDerivative
import Stokes.BoundaryChart.TargetBoxCompactImage
```

Global endpoint work:

```lean
-- future, after facade is added:
import Stokes.Global.CompactSupportEndpointFacade
```

Until that future facade exists, endpoint agents should extend one of:

- `NaturalCompactSupportEndpointConcrete.lean`
- `SelectedReconstructionSourceAuto.lean`
- `SelectedReconstructionSourceConstructorsAuto.lean`
- `NaturalCompactSupportEndpointConstructorFieldsAuto.lean`
- `NaturalCompactSupportEndpointMarginAuto.lean`

rather than creating another endpoint micro-file.

## Most important recommendations

1. Treat `Stokes/BoundaryChart/BoundaryChartCOVFacade.lean` as the public import
   for boundary chart COV work; keep deep `*Auto` files private-ish.
2. Add a future `Stokes/Global/CompactSupportEndpointFacade.lean` and route
   endpoint-facing work through it instead of growing `Stokes/Global.lean` every
   wave.
3. Move no files while parallel agents are active; consolidate first by
   facades, then do any mechanical reorganization in one dedicated wave.
4. Stop making new files for pure projections: append to the nearest existing
   family file unless a new import cycle or theorem family justifies a split.
5. Keep cross-layer glue out of BoundaryChart public facades.  In particular,
   `TargetBoxToM8Glue.lean` should be consumed from the Global side, not from a
   BoundaryChart facade.
