# Stokes Proof Wave Repair And Acceptance Report

Date: 2026-05-24.

Scope: documentation-only repair report for the latest Stokes proof wave.
This agent is Repair Agent 8/8.  It edits no Lean files and does not run
`lake build`.  The purpose is to make the post-wave cleanup strategy explicit:
which modules should be treated as real deliverables, which are duplicate or
mostly cosmetic wrappers, and which should remain unaggregated until they pass
focused checks.

## Repair Context

The recent proof waves added many small files.  That was useful for parallel
exploration, but it also creates a new risk: the project can look closer to
final Stokes than it really is because many modules only repackage existing
fields.  The repair pass should preserve the useful theorem boundaries while
preventing the import graph from becoming a large layer of overlapping
wrappers.

The target remains:

```text
compactly supported smooth manifold form
  -> finite selected chart boxes and partition data
  -> bulk measure localization
  -> boundary measure localization
  -> target-image/local-inverse data
  -> artificial-face cancellation
  -> orientation-compatible boundary terms
  -> compact-support Stokes statement
```

The repair standard is: a module is a formal milestone only if it either
constructs a previously assumed analytic/geometric field from lower-level data,
or gives a stable constructor that is clearly on the shortest path to such a
construction.

## Formal Deliverables To Preserve

These modules are worth keeping as real API progress after they pass or retain
focused checks.  They either expose a true proof node or reduce a final record
field to a mathematically named input.

| Module | Status | Why it should stay |
|---|---|---|
| `Stokes.Global.BulkIntegrandAEFromPartition` | Formal candidate | Moves bulk a.e. replacement toward partition-local eventual equality and measure support, instead of a raw M8 field. |
| `Stokes.Global.MeasureBoxProjectLocal` | Formal candidate | Names the exact comparison between measure-local box integrals and project-local Stokes box terms. |
| `Stokes.Global.BulkCompactSupportIntegrabilityToMeasure` | Formal candidate | Connects compact support and continuity assumptions to local integrability inputs for bulk measure localization. |
| `Stokes.Global.BoundaryMeasureFromPartition` | Formal candidate | Provides a boundary-partition-facing entrance to boundary measure localization. |
| `Stokes.Global.BoundaryMeasureTargetAssembly` | Formal candidate | Connects target-image assembly data to boundary measure localization inputs. |
| `Stokes.Global.BoundaryPieceIntegrabilityToMeasure` | Formal candidate | Uses existing boundary integrability packages to feed boundary measure fields. |
| `Stokes.Global.ArtificialFaceSupportZeroGeometry` | Formal candidate | Turns strict interior support containment into the support-zero artificial-face route. |
| `Stokes.BoundaryChart.TargetImageLocalOpenness` | Formal candidate | Separates local-openness target-box data in the pure `BoundaryChart` layer. |
| `Stokes.BoundaryChart.TargetImageIFTBridge` | Formal candidate | Gives the inverse-function/local-openness bridge shape for boundary chart target images. |
| `Stokes.Global.CompactSupportFiniteActiveToBuilder` | Builder candidate | Connects compact finite-active selection data to the M8 builder path. |

These files should not all be advertised as completed mathematics.  The correct
claim is narrower: they reduce the remaining assumptions to named proof nodes
that can be attacked independently.

## Duplicate Or Mostly Cosmetic Wrappers

These modules may still be useful, but they should be treated as candidates for
merge, rename, or delayed import.  They should not be counted as independent
mathematical progress unless later proofs consume them directly.

| Module or family | Repair note |
|---|---|
| `NaturalCompactSupportBuilder` | Mostly a second spelling of the existing natural compact-support input.  Keep only if it becomes the single public builder. |
| `CanonicalNaturalStokes` and `CanonicalNaturalCompactSupport` | Statement-surface work.  Useful names, but still represented values until the real manifold integral API is attached. |
| `OrientationBridgeToM8` and `OrientedAtlasToM8` | Overlapping orientation adapters.  Keep the smaller public route and leave the mathlib orientation proof as the real blocker. |
| `ArtificialFacePairingToM8` and `ArtificialFaceAdjacencyToM8` | Similar M8 adapters for the pairing route.  Choose one public API after focused build, or keep one as an alias layer only. |
| `TargetImageToM8`, `TargetImageResolvedToM8Input`, `TargetImageIFTToM8`, `TargetImageLocalOpennessToM8` | Multiple target-image adapter routes.  Consolidate around one path: pure `BoundaryChart` resolved family -> global assembly -> M8 input. |
| `NaturalBoundaryMeasureBuilder` and `NaturalBoundaryMeasureBuilder2` | Suspicious duplicate naming.  Audit before aggregator import; one should probably absorb the other. |
| `CompactSupportMeasureToM8Builder`, `CompactSupportToM8Measure`, `M8MeasureConstructors` | Potentially overlapping measure-builder layers.  Keep the one that best exposes bulk and boundary true proof nodes. |

The repair pass should prefer fewer public constructors with strong projection
lemmas over many nearly identical record wrappers.

## Modules To Keep Quarantined Until Focused Build

Do not add these to aggregators merely because they exist.  They should first
pass a focused file check, and the parent integration should confirm that their
imports do not broaden the dependency graph unnecessarily.

```text
Stokes.Global.BulkIntegrandAEFromPartition
Stokes.Global.MeasureBoxProjectLocal
Stokes.Global.BulkCompactSupportIntegrabilityToMeasure
Stokes.Global.BoundaryMeasureTargetAssembly
Stokes.Global.BoundaryPieceIntegrabilityToMeasure
Stokes.Global.NaturalBoundaryMeasureBuilder
Stokes.Global.NaturalBoundaryMeasureBuilder2
Stokes.Global.ArtificialFaceAdjacencyToM8
Stokes.Global.ArtificialFaceSupportZeroGeometry
Stokes.Global.OrientationBridgeToM8
Stokes.Global.CompactSupportFiniteActiveToBuilder
Stokes.Global.NaturalCompactSupportBuilder
Stokes.Global.CanonicalNaturalStokes
Stokes.Global.TargetImageIFTToM8
Stokes.Global.TargetImageLocalOpennessToM8
Stokes.BoundaryChart.OrientationMathlibBridge
Stokes.BoundaryChart.TargetImageFromLocalInverse
Stokes.BoundaryChart.TargetImageLocalOpenness
Stokes.BoundaryChart.TargetImageIFTBridge
```

Suggested focused checks for the parent process:

```text
lake env lean Stokes\Global\BulkIntegrandAEFromPartition.lean
lake env lean Stokes\Global\MeasureBoxProjectLocal.lean
lake env lean Stokes\Global\BulkCompactSupportIntegrabilityToMeasure.lean
lake env lean Stokes\Global\BoundaryMeasureTargetAssembly.lean
lake env lean Stokes\Global\BoundaryPieceIntegrabilityToMeasure.lean
lake env lean Stokes\Global\ArtificialFaceSupportZeroGeometry.lean
lake env lean Stokes\BoundaryChart\TargetImageLocalOpenness.lean
lake env lean Stokes\BoundaryChart\TargetImageIFTBridge.lean
```

After those pass, add aggregator imports in small batches and run the full
build only once from the parent integration thread.

## Aggregator Policy

`Stokes.Global.lean` should contain only modules that have passed focused
checks and have a clear public role.  Add imports in dependency order, not in
agent-completion order.

Recommended first batch, assuming focused checks pass:

```lean
import Stokes.BoundaryChart.TargetImageLocalOpenness
import Stokes.BoundaryChart.TargetImageIFTBridge
import Stokes.Global.BulkIntegrandAEFromPartition
import Stokes.Global.MeasureBoxProjectLocal
import Stokes.Global.BulkCompactSupportIntegrabilityToMeasure
import Stokes.Global.BoundaryMeasureTargetAssembly
import Stokes.Global.BoundaryPieceIntegrabilityToMeasure
import Stokes.Global.ArtificialFaceSupportZeroGeometry
```

Recommended second batch, after duplicate-wrapper audit:

```lean
import Stokes.Global.CompactSupportFiniteActiveToBuilder
import Stokes.Global.NaturalCompactSupportBuilder
import Stokes.Global.CanonicalNaturalStokes
```

Potentially postpone until API consolidation:

```lean
import Stokes.Global.ArtificialFaceAdjacencyToM8
import Stokes.Global.OrientationBridgeToM8
import Stokes.Global.TargetImageIFTToM8
import Stokes.Global.TargetImageLocalOpennessToM8
import Stokes.Global.NaturalBoundaryMeasureBuilder
import Stokes.Global.NaturalBoundaryMeasureBuilder2
```

## HalfSpace And BoundaryChart Safety Rules

Do not import `Stokes.Global.*` into `Stokes.HalfSpace`.

Do not add high-level global adapters to `Stokes.HalfSpace.lean`.  In
particular, `Stokes.BoundaryChart.BoundaryPieceConvenience` must stay out of
`Stokes.HalfSpace`, because it depends on `Stokes.Global.BoundaryPieces` and
can create the known cycle:

```text
Stokes.HalfSpace
  -> Stokes.BoundaryChart.BoundaryPieceConvenience
  -> Stokes.Global.BoundaryPieces
  -> Stokes.Global.Partition
  -> Stokes.Global.InteriorChart
  -> Stokes.HalfSpace
```

Pure `BoundaryChart` files may remain independent, but even then they should
usually be imported by the specific `Global` adapter that needs them, not by
the half-space base aggregator.

## Acceptance Labels

Use these labels in future reports and final summaries.

| Label | Meaning |
|---|---|
| Formal deliverable | Focused build passed, no placeholders, and the file has a stable public role. |
| True proof node | A theorem constructs analytic, geometric, measure, or orientation data from lower-level mathematical hypotheses. |
| Constructor/projection | Existing assumptions are repackaged into a cleaner API.  Useful, but not a proof node by itself. |
| Statement surface | The theorem is restated under better names, but no mathematical input has been discharged. |
| Quarantined | The file exists, but should not enter aggregators until focused build and duplicate-wrapper review pass. |
| Duplicate candidate | The file overlaps another wrapper and should be merged, renamed, or kept private. |

## Repair Checklist

The parent integration thread should perform this sequence:

1. Run focused checks for the formal-candidate modules.
2. Run placeholder scan.
3. Add first-batch aggregator imports only for focused-build-clean modules.
4. Run full `lake build` once.
5. If successful, classify those modules as formal deliverables.
6. Audit duplicate wrappers and choose one public route for each family.
7. Only then add second-batch imports.
8. Keep the final theorem claims honest: distinguish packaged assumptions from
   true mathematical discharges.

Allowed for this report agent:

```text
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

Forbidden for this report agent:

```text
lake build
lake env lean ...
```

