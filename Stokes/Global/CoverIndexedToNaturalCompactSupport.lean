import Stokes.Global.CoverIndexedMeasureFields
import Stokes.Global.NaturalCompactSupportInputBridgeReduction

/-!
# Cover-indexed core to natural compact-support adapters

This module is intentionally only a projection/congruence layer.  It connects
the cover-indexed finite-sum core equality to the compact-support field names
used by `NaturalCompactSupportStokesInput` and the reduced partition-cover
bridge input, without re-running or re-proving any local Stokes theorem.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedToNaturalCompactSupport

universe u v w b a aBulk aBoundary

variable {ι : Type u}
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

namespace CoverIndexedStokesSums

/--
If a cover-indexed core package represents the natural compact-support bulk
and boundary measure fields, its finite-sum Stokes theorem gives exactly the
field equality consumed by `NaturalCompactSupportStokesInput`.
-/
theorem naturalCompactSupportFields_eq
    (C : CoverIndexedStokesSums ι)
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ)
    (hbulk : C.globalBulk = D.measure.globalBulkIntegral)
    (hboundary :
      C.globalBoundary = D.measure.boundary.boundaryMeasureIntegral) :
    D.measure.globalBulkIntegral =
      D.measure.boundary.boundaryMeasureIntegral := by
  calc
    D.measure.globalBulkIntegral = C.globalBulk := hbulk.symm
    _ = C.globalBoundary := C.stokes
    _ = D.measure.boundary.boundaryMeasureIntegral := hboundary

end CoverIndexedStokesSums

/--
Minimal natural compact-support package whose Stokes equality is supplied by a
cover-indexed core result.  The `natural` field keeps the existing endpoint
ecosystem intact; the two comparison fields identify the cover-indexed real
terms with the endpoint measure fields.
-/
structure CoverIndexedNaturalCompactSupportInput
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ]
    (ι : Type u) where
  /-- Existing natural compact-support endpoint input. -/
  natural :
    NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ
  /-- Cover-indexed finite-sum core package. -/
  coverSums : CoverIndexedStokesSums ι
  /-- The cover-indexed bulk real is the natural represented bulk integral. -/
  cover_globalBulk :
    coverSums.globalBulk = natural.measure.globalBulkIntegral
  /-- The cover-indexed boundary real is the natural boundary measure integral. -/
  cover_globalBoundary :
    coverSums.globalBoundary =
      natural.measure.boundary.boundaryMeasureIntegral

namespace CoverIndexedNaturalCompactSupportInput

variable
    (D :
      CoverIndexedNaturalCompactSupportInput
        (α := α) I omega BoundaryPiece μ ι)

/-- The existing natural compact-support input carried by the adapter. -/
abbrev toNaturalCompactSupportStokesInput :
    NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ :=
  D.natural

/-- The compactly supported form data visible in the natural endpoint. -/
abbrev formData : CompactlySupportedSmoothFormData I omega :=
  D.natural.formData

/-- The oriented boundary atlas visible in the natural endpoint. -/
abbrev orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M :=
  D.natural.orientedBoundaryAtlas

@[simp]
theorem toNaturalCompactSupportStokesInput_measure :
    D.toNaturalCompactSupportStokesInput.measure = D.natural.measure :=
  rfl

/-- Natural compact-support Stokes in compact-support field names, via cover sums. -/
theorem stokes_compactSupportFields :
    D.natural.measure.globalBulkIntegral =
      D.natural.measure.boundary.boundaryMeasureIntegral :=
  D.coverSums.naturalCompactSupportFields_eq
    D.natural D.cover_globalBulk D.cover_globalBoundary

end CoverIndexedNaturalCompactSupportInput

section MeasureFields

variable {αBulk : Type aBulk} [TopologicalSpace αBulk]
variable [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk]
variable [T2Space αBulk]
variable {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]
variable {αBoundary : Type aBoundary} [TopologicalSpace αBoundary]
variable [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
variable [T2Space αBoundary]
variable {μBoundary : Measure αBoundary}
variable [IsFiniteMeasureOnCompacts μBoundary]
variable {active : Finset ι}

namespace CoverIndexedMeasureFields

/--
Measure-field variant of the adapter.  The cover-indexed measure package
already exposes a `CoverIndexedStokesSums`; the only remaining work is naming
which natural endpoint fields those two represented reals denote.
-/
theorem naturalCompactSupportFields_eq
    (C : CoverIndexedMeasureFields active μBulk μBoundary)
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ)
    (hbulk : C.globalBulk = D.measure.globalBulkIntegral)
    (hboundary :
      C.globalBoundary = D.measure.boundary.boundaryMeasureIntegral) :
    D.measure.globalBulkIntegral =
      D.measure.boundary.boundaryMeasureIntegral :=
  C.toCoverIndexedStokesSums.naturalCompactSupportFields_eq
    D hbulk hboundary

end CoverIndexedMeasureFields

end MeasureFields

section BridgeReduction

variable {rho : SmoothPartitionOfUnity M I M univ}
variable [IsManifold I 1 M]

namespace NaturalCompactSupportPartitionCoverBridgeReductionInput

variable
    (D :
      NaturalCompactSupportPartitionCoverBridgeReductionInput
        (Alpha := α) I omega BoundaryPiece rho μ)

/--
Reduced partition-cover bridge input, closed by a cover-indexed core result.
This targets exactly the field form used by the natural compact-support
endpoint theorem.
-/
theorem stokes_compactSupportFields_of_coverIndexedSums
    (C : CoverIndexedStokesSums ι)
    (hbulk : C.globalBulk = D.measure.globalBulkIntegral)
    (hboundary :
      C.globalBoundary = D.measure.boundary.boundaryMeasureIntegral) :
    D.measure.globalBulkIntegral =
      D.measure.boundary.boundaryMeasureIntegral := by
  exact C.naturalCompactSupportFields_eq
    D.toNaturalCompactSupportStokesInput hbulk hboundary

/--
Same bridge, starting from the cover-indexed measure-field package rather than
the bare core sums.
-/
theorem stokes_compactSupportFields_of_coverIndexedMeasureFields
    {αBulk : Type aBulk} [TopologicalSpace αBulk]
    [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk]
    [T2Space αBulk]
    {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]
    {αBoundary : Type aBoundary} [TopologicalSpace αBoundary]
    [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
    [T2Space αBoundary]
    {μBoundary : Measure αBoundary}
    [IsFiniteMeasureOnCompacts μBoundary]
    {active : Finset ι}
    (C : CoverIndexedMeasureFields active μBulk μBoundary)
    (hbulk : C.globalBulk = D.measure.globalBulkIntegral)
    (hboundary :
      C.globalBoundary = D.measure.boundary.boundaryMeasureIntegral) :
    D.measure.globalBulkIntegral =
      D.measure.boundary.boundaryMeasureIntegral :=
  C.naturalCompactSupportFields_eq
    D.toNaturalCompactSupportStokesInput hbulk hboundary

end NaturalCompactSupportPartitionCoverBridgeReductionInput

end BridgeReduction

end CoverIndexedToNaturalCompactSupport

end Stokes

end
