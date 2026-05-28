import Stokes.Global.CoverIndexedMeasureFields

/-!
# Cover-indexed compact-support public theorem

This module is a thin public wrapper around the cover-indexed compact-support
route.  The analytic and measure reconstruction hypotheses live in
`CoverIndexedMeasureFields`; the finite algebra lives in
`CoverIndexedStokesSums`.

The public input below keeps the theorem statement short while still exposing
the user-facing data that one expects from the compact-support route: a finite
active cover, a compact support carrier, a subordinate finite-sum identity, the
local Stokes sum package, and the bulk/boundary measure reconstruction package.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace Stokes

universe u a b

section CoverIndexedPublicTheorem

/--
User-facing cover-indexed compact-support Stokes input.

The `measureFields` field is authoritative for the represented bulk and
boundary values.  The `localStokesSums` field records the same finite algebra
in the small `CoverIndexedStokesSums` shape, and the compatibility field makes
that projection explicit.
-/
structure CoverIndexedCompactSupportStokesInput
    (ι : Type u)
    (αBulk : Type a) [TopologicalSpace αBulk]
    [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk] [T2Space αBulk]
    (μBulk : Measure αBulk) [IsFiniteMeasureOnCompacts μBulk]
    (αBoundary : Type b) [TopologicalSpace αBoundary]
    [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
    [T2Space αBoundary]
    (μBoundary : Measure αBoundary)
    [IsFiniteMeasureOnCompacts μBoundary] where
  /-- Finite active cover labels. -/
  active : Finset ι
  /-- Bulk/boundary measure reconstruction and active-piece integrability data. -/
  measureFields :
    CoverIndexedMeasureFields active μBulk μBoundary
  /-- Compact carrier for the represented compact-support form data. -/
  compactSupportSet : Set αBulk
  /-- The compact-support carrier is compact. -/
  compactSupportSet_isCompact : IsCompact compactSupportSet
  /-- The represented bulk integrand has support in the compact carrier. -/
  bulk_tsupport_subset_compactSupportSet :
    tsupport measureFields.bulk.integrand ⊆ compactSupportSet
  /--
  Subordinate finite-sum identity before indicator insertion.  The measure
  package stores the localized indicator identity; this field keeps the
  partition-of-unity shape visible at the public boundary.
  -/
  subordinatePartitionFiniteSumIdentity :
    measureFields.bulk.integrand =ᵐ[μBulk]
      fun y => Finset.sum active fun i => measureFields.bulk.pieceIntegrand i y
  /-- Small finite-sum package for the local Stokes algebra. -/
  localStokesSums : CoverIndexedStokesSums ι
  /-- The public local-sum package is exactly the measure-field projection. -/
  localStokesSums_eq_measureFields :
    localStokesSums = measureFields.toCoverIndexedStokesSums

namespace CoverIndexedCompactSupportStokesInput

variable {ι : Type u}
variable {αBulk : Type a} [TopologicalSpace αBulk]
variable [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk]
variable [T2Space αBulk]
variable {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]
variable {αBoundary : Type b} [TopologicalSpace αBoundary]
variable [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
variable [T2Space αBoundary]
variable {μBoundary : Measure αBoundary}
variable [IsFiniteMeasureOnCompacts μBoundary]

/-- The represented public bulk value. -/
abbrev globalBulk
    (D :
      CoverIndexedCompactSupportStokesInput
        (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) : Real :=
  D.localStokesSums.globalBulk

/-- The represented public boundary value. -/
abbrev globalBoundary
    (D :
      CoverIndexedCompactSupportStokesInput
        (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) : Real :=
  D.localStokesSums.globalBoundary

@[simp]
theorem localStokesSums_eq_toMeasureFields
    (D :
      CoverIndexedCompactSupportStokesInput
        (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.localStokesSums = D.measureFields.toCoverIndexedStokesSums :=
  D.localStokesSums_eq_measureFields

/--
The public represented Stokes equality, proved by reusing
`CoverIndexedMeasureFields.stokes`.
-/
theorem stokes
    (D :
      CoverIndexedCompactSupportStokesInput
        (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.globalBulk = D.globalBoundary := by
  change D.localStokesSums.globalBulk = D.localStokesSums.globalBoundary
  rw [D.localStokesSums_eq_measureFields]
  exact D.measureFields.stokes

/-- The same equality as a direct projection from the small finite-sum package. -/
theorem stokes_via_localSums
    (D :
      CoverIndexedCompactSupportStokesInput
        (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.globalBulk = D.globalBoundary :=
  D.localStokesSums.stokes

end CoverIndexedCompactSupportStokesInput

/--
User-facing cover-indexed compact-support Stokes theorem.

The output is the represented global bulk equality against the represented
global boundary value carried by the public input.
-/
theorem coverIndexedCompactSupportStokes
    {ι : Type u}
    {αBulk : Type a} [TopologicalSpace αBulk]
    [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk] [T2Space αBulk]
    {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]
    {αBoundary : Type b} [TopologicalSpace αBoundary]
    [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
    [T2Space αBoundary]
    {μBoundary : Measure αBoundary}
    [IsFiniteMeasureOnCompacts μBoundary]
    (D :
      CoverIndexedCompactSupportStokesInput
        (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.globalBulk = D.globalBoundary :=
  D.stokes

/--
Projection theorem: the public theorem is the same result as
`CoverIndexedStokesSums.stokes` for the carried local finite-sum package.
-/
theorem coverIndexedCompactSupportStokes_eq_coverIndexedStokesSums_stokes
    {ι : Type u}
    {αBulk : Type a} [TopologicalSpace αBulk]
    [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk] [T2Space αBulk]
    {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]
    {αBoundary : Type b} [TopologicalSpace αBoundary]
    [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
    [T2Space αBoundary]
    {μBoundary : Measure αBoundary}
    [IsFiniteMeasureOnCompacts μBoundary]
    (D :
      CoverIndexedCompactSupportStokesInput
        (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
        (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    coverIndexedCompactSupportStokes D = D.localStokesSums.stokes := by
  exact Subsingleton.elim _ _

end CoverIndexedPublicTheorem

end Stokes

end
