import Stokes.Global.CoverIndexedResolvedInput
import Stokes.Global.CoverIndexedCanonicalBridge
import Stokes.Global.CoverIndexedClosedCarrier
import Stokes.Global.CoverIndexedBulkMeasureConstructor
import Stokes.Global.CoverIndexedBoundaryMeasureConstructor

/-!
# Natural assembly layer for the cover-indexed route

This file is the parameterized integration point for the new middle layers.
It does not try to solve the remaining local smoothness, boundary COV, or
target-image construction problems.  Instead, it records the smaller data that
those constructors should eventually produce and assembles it into the already
proved `CoverIndexedResolvedCompactSupportInput`.

The important reduction is on the bulk side: the carrier is no longer an
arbitrary scattered field.  It is fixed to the closed compact carrier
`C.coverIndexClosedCarrier`, with compactness supplied automatically from the
closed-carrier layer and support transferred from the assigned open support
box.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalAssembly

universe uH uM uB

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}

variable {αBoundary : Type uB} [TopologicalSpace αBoundary]
variable [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
variable [T2Space αBoundary]
variable {μBulk : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μBulk]
variable {μBoundary : Measure αBoundary}
variable [IsFiniteMeasureOnCompacts μBoundary]

/--
Bulk data in the form expected from the closed-carrier middle layer.

The local carrier is fixed to `C.coverIndexClosedCarrier`.  Callers only prove
continuity on that closed carrier, support in the assigned open support box,
the local set-integral identity over the closed carrier, and the global
piece-sum reconstruction.
-/
structure CoverIndexedClosedCarrierBulkData
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  /-- Global coordinate representative for the bulk integrand. -/
  integrand : (Fin (n + 1) → Real) → Real
  /-- Local coordinate representatives for the localized bulk integrands. -/
  pieceIntegrand : C.CoverIndex → (Fin (n + 1) → Real) → Real
  /-- Represented global bulk integral. -/
  globalIntegral : Real
  /-- The represented global bulk integral is the integral of `integrand`. -/
  globalIntegral_eq_integral :
    globalIntegral = ∫ y, integrand y ∂μBulk
  /-- Local representatives are continuous on the closed carrier. -/
  piece_continuousOn_closedCarrier :
    ∀ j : C.CoverIndex,
      ContinuousOn (pieceIntegrand j) (C.coverIndexClosedCarrier j)
  /--
  The support control naturally comes from the assigned open support box; the
  assembly transfers it to the closed compact carrier.
  -/
  piece_tsupport_subset_assignedCoordinateBox :
    ∀ j : C.CoverIndex,
      tsupport (pieceIntegrand j) ⊆ C.assignedCoordinateBox j
  /-- Local bulk terms are the set integrals over the closed carrier. -/
  localBulk_eq_setIntegral_closedCarrier :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm ω j =
        ∫ y in C.coverIndexClosedCarrier j, pieceIntegrand j y ∂μBulk
  /-- The global bulk scalar is the finite sum of localized scalars, a.e. -/
  integrand_ae_eq_pieceSum :
    integrand =ᵐ[μBulk]
      fun y => ∑ j : C.CoverIndex, pieceIntegrand j y

namespace CoverIndexedClosedCarrierBulkData

variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/-- Closed-carrier bulk data as resolved bulk fields. -/
def toResolvedBulkFields
    (D : CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk) C P ω) :
    CoverIndexedResolvedBulkFields
      (C := C) (ω := ω)
      (αBulk := Fin (n + 1) → Real) (μBulk := μBulk) P :=
  CoverIndexedResolvedBulkFields.ofPieceSum
    (C := C) (ω := ω) (μBulk := μBulk) P
    D.integrand
    C.coverIndexClosedCarrier
    D.pieceIntegrand
    D.globalIntegral
    D.globalIntegral_eq_integral
    (fun j => C.coverIndex_closedCarrier_isCompact j)
    D.piece_continuousOn_closedCarrier
    (fun j =>
      C.coverIndex_tsupport_subset_closedCarrier_of_tsupport_subset_assignedCoordinateBox
        j (D.piece_tsupport_subset_assignedCoordinateBox j))
    D.localBulk_eq_setIntegral_closedCarrier
    D.integrand_ae_eq_pieceSum

@[simp]
theorem toResolvedBulkFields_measureIntegral
    (D : CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk) C P ω) :
    D.toResolvedBulkFields.measureIntegral = D.globalIntegral :=
  rfl

/-- The closed-carrier bulk package reconstructs the finite sum of local bulk terms. -/
theorem globalIntegral_eq_localBulkSum
    (D : CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk) C P ω) :
    D.globalIntegral =
      ∑ j : C.CoverIndex, P.coverIndexLocalBulkTerm ω j := by
  simpa using D.toResolvedBulkFields.measureIntegral_eq_localBulkSum

end CoverIndexedClosedCarrierBulkData

/--
Boundary data in the form expected from the resolved boundary chart/COV
middle layer.

Unlike the bulk side, the carrier type is still parameterized.  Boundary
constructors may use lower-dimensional target boxes, signed outward-first
representatives, or other resolved chart carriers before producing this
record.
-/
structure CoverIndexedNaturalBoundaryData
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  /-- Global scalar representative for the boundary integrand. -/
  integrand : αBoundary → Real
  /-- Cover-indexed boundary carrier sets. -/
  pieceSet : C.CoverIndex → Set αBoundary
  /-- Local scalar representatives for boundary pieces. -/
  pieceIntegrand : C.CoverIndex → αBoundary → Real
  /-- Represented global boundary integral. -/
  globalIntegral : Real
  /-- The represented global boundary integral is the integral of `integrand`. -/
  globalIntegral_eq_integral :
    globalIntegral = ∫ y, integrand y ∂μBoundary
  /-- Boundary carriers are compact. -/
  piece_isCompact :
    ∀ j : C.CoverIndex, IsCompact (pieceSet j)
  /-- Boundary pieces are continuous on their carriers. -/
  piece_continuousOn :
    ∀ j : C.CoverIndex,
      ContinuousOn (pieceIntegrand j) (pieceSet j)
  /-- Boundary scalar representatives are supported in their carriers. -/
  piece_tsupport_subset :
    ∀ j : C.CoverIndex,
      tsupport (pieceIntegrand j) ⊆ pieceSet j
  /-- Local boundary terms are the set integrals of the resolved representatives. -/
  localBoundary_eq_setIntegral :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBoundaryTerm ω j =
        ∫ y in pieceSet j, pieceIntegrand j y ∂μBoundary
  /-- The global boundary scalar is the finite sum of localized scalars, a.e. -/
  integrand_ae_eq_pieceSum :
    integrand =ᵐ[μBoundary]
      fun y => ∑ j : C.CoverIndex, pieceIntegrand j y

namespace CoverIndexedNaturalBoundaryData

variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/-- Natural boundary data as resolved boundary fields. -/
def toResolvedBoundaryFields
    (D : CoverIndexedNaturalBoundaryData
      (I := I) (K := K) (ω := ω)
      (αBoundary := αBoundary) (μBoundary := μBoundary) C P) :
    CoverIndexedResolvedBoundaryFields
      (C := C) (ω := ω)
      (αBoundary := αBoundary) (μBoundary := μBoundary) P :=
  CoverIndexedResolvedBoundaryFields.ofPieceSum
    (C := C) (ω := ω) (μBoundary := μBoundary) P
    D.integrand
    D.pieceSet
    D.pieceIntegrand
    D.globalIntegral
    D.globalIntegral_eq_integral
    D.piece_isCompact
    D.piece_continuousOn
    D.piece_tsupport_subset
    D.localBoundary_eq_setIntegral
    D.integrand_ae_eq_pieceSum

@[simp]
theorem toResolvedBoundaryFields_measureIntegral
    (D : CoverIndexedNaturalBoundaryData
      (I := I) (K := K) (ω := ω)
      (αBoundary := αBoundary) (μBoundary := μBoundary) C P) :
    D.toResolvedBoundaryFields.measureIntegral = D.globalIntegral :=
  rfl

/-- The natural boundary package reconstructs the finite sum of local boundary terms. -/
theorem localBoundarySum_eq_globalIntegral
    (D : CoverIndexedNaturalBoundaryData
      (I := I) (K := K) (ω := ω)
      (αBoundary := αBoundary) (μBoundary := μBoundary) C P) :
    (∑ j : C.CoverIndex, P.coverIndexLocalBoundaryTerm ω j) =
      D.globalIntegral := by
  simpa using D.toResolvedBoundaryFields.localBoundarySum_eq_measureIntegral

end CoverIndexedNaturalBoundaryData

/--
Parameterized natural assembly for the cover-indexed compact-support route.

This is the constructor target for the middle-layer workers: provide a
support-controlled chart-box cover, local Stokes fields, closed-carrier bulk
data, and resolved boundary data; the file assembles the existing resolved
compact-support input and exposes represented and canonical Stokes.
-/
structure CoverIndexedNaturalAssemblyInput where
  /-- Finite chart-box cover of the compact support set. -/
  chartBoxCover : CompactSupportChartCoverSelection I K
  /-- Support-controlled partition subordinate to the selected cover. -/
  controlledPartition :
    SupportControlledSelectedPartition chartBoxCover
  /-- Local support and smoothness fields proving local Stokes on cover pieces. -/
  localFields :
    SupportControlledCoverIndexedLocalStokesFields
      controlledPartition ω
  /-- Closed-carrier bulk reconstruction data. -/
  bulk :
    CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk)
      chartBoxCover controlledPartition ω
  /-- Resolved boundary reconstruction data. -/
  boundary :
    CoverIndexedNaturalBoundaryData
      (I := I) (K := K) (ω := ω)
      (αBoundary := αBoundary) (μBoundary := μBoundary)
      chartBoxCover controlledPartition

namespace CoverIndexedNaturalAssemblyInput

/-- The resolved compact-support input assembled from the grouped natural data. -/
def toResolvedInput
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    CoverIndexedResolvedCompactSupportInput
      (I := I) (K := K) (ω := ω)
      (αBulk := Fin (n + 1) → Real) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary) where
  chartBoxCover := D.chartBoxCover
  controlledPartition := D.controlledPartition
  localFields := D.localFields
  bulk := D.bulk.toResolvedBulkFields
  boundary := D.boundary.toResolvedBoundaryFields

/-- Compatibility projection to the older flat support-controlled input. -/
def toSupportControlledMeasureInput
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := Fin (n + 1) → Real) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary) :=
  D.toResolvedInput.toSupportControlledMeasureInput

/-- Represented global integral interface for the assembled data. -/
def representedGlobalIntegralInterface
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    GlobalIntegralInterface I ω :=
  D.toSupportControlledMeasureInput.representedGlobalIntegralInterface

/-- Canonical represented integral names for the assembled data. -/
def canonicalIntegralInterface
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    CanonicalIntegralInterface I ω :=
  D.toSupportControlledMeasureInput.canonicalIntegralInterface

/-- The represented global bulk value of the assembled input. -/
abbrev globalBulk
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    Real :=
  D.bulk.globalIntegral

/-- The represented global boundary value of the assembled input. -/
abbrev globalBoundary
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    Real :=
  D.boundary.globalIntegral

@[simp]
theorem toResolvedInput_globalBulk
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    D.toResolvedInput.globalBulk = D.globalBulk :=
  rfl

@[simp]
theorem toResolvedInput_globalBoundary
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    D.toResolvedInput.globalBoundary = D.globalBoundary :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_globalBulkIntegral
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    D.representedGlobalIntegralInterface.globalBulkIntegral =
      D.globalBulk :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_globalBoundaryIntegral
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    D.representedGlobalIntegralInterface.globalBoundaryIntegral =
      D.globalBoundary :=
  rfl

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.globalBulk :=
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    D.canonicalIntegralInterface.boundaryFormIntegral =
      D.globalBoundary :=
  rfl

/-- Compact-support represented Stokes from the grouped natural assembly data. -/
theorem stokes
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    D.globalBulk = D.globalBoundary := by
  exact D.toResolvedInput.stokes

/-- Same theorem, routed through the flat compatibility input. -/
theorem stokes_via_supportControlledMeasureInput
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    D.globalBulk = D.globalBoundary := by
  exact D.toSupportControlledMeasureInput.stokes

/-- Represented global-interface Stokes for the natural assembly input. -/
theorem representedGlobalIntegralInterface_stokes
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    D.representedGlobalIntegralInterface.stokesStatement := by
  exact D.toSupportControlledMeasureInput.representedGlobalIntegralInterface_stokes

/-- Canonical represented Stokes for the natural assembly input. -/
theorem canonical_stokes
    (D : CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk) (μBoundary := μBoundary)) :
    D.canonicalIntegralInterface.stokesStatement := by
  exact D.toSupportControlledMeasureInput.canonical_stokes

end CoverIndexedNaturalAssemblyInput

end NaturalAssembly

end Stokes

end
