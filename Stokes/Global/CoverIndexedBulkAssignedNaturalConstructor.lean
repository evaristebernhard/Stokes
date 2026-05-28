import Stokes.Global.CoverIndexedBulkLocalIntegral
import Stokes.Global.CoverIndexedBulkContinuityConstructor
import Stokes.Global.CoverIndexedBulkSetIntegralConstructor
import Stokes.Global.CoverIndexedNaturalAssembly

/-!
# Assigned-chart bulk constructors for the cover-indexed route

The project-local bulk term attached to a selected cover index is already
defined in the chart selected for that index.  Consequently the local integral
identity available without a bulk chart-change theorem is the self-chart one

`bulkIntegrand I (C.assignedChart j) (C.assignedChart j) ...`.

This file packages that observation into a bulk input whose local pieces use a
per-index assigned-chart self-pair.  The finite-sum representative can either
be used as the global bulk scalar directly, or an external global scalar can be
related to it by an a.e. equality.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section AssignedSelfBulk

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {μBulk : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μBulk]

namespace SupportControlledSelectedPartition

/-- The scalar bulk piece represented in the chart selected for `j` itself. -/
abbrev assignedSelfBulkPieceIntegrand
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n)
    (j : C.CoverIndex) :
    (Fin (n + 1) → Real) → Real :=
  fun y =>
    bulkIntegrand I (C.assignedChart j) (C.assignedChart j)
      (P.coverIndexLocalizedForm ω j) y

/--
The cover-indexed assigned-chart finite-sum bulk representative.  This is the
bulk scalar that needs no fixed-chart change-of-variables theorem.
-/
abbrev assignedSelfBulkIntegrand
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) :
    (Fin (n + 1) → Real) → Real :=
  fun y =>
    ∑ j : C.CoverIndex,
      P.assignedSelfBulkPieceIntegrand (I := I) ω j y

/-- The finite-sum representative is a.e. equal to its defining piece sum. -/
theorem assignedSelfBulkIntegrand_ae_eq_pieceSum
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n)
    (μ : Measure (Fin (n + 1) → Real)) :
    P.assignedSelfBulkIntegrand (I := I) ω =ᵐ[μ]
      fun y =>
        ∑ j : C.CoverIndex,
          P.assignedSelfBulkPieceIntegrand (I := I) ω j y :=
  Filter.Eventually.of_forall fun _ => rfl

/--
Smoothness data for the assigned-chart self-pair pieces.  This is the
per-index analogue of `CoverIndexedBulkSmoothnessFields`, with `x0 = x1`
allowed to vary with `j`.
-/
structure CoverIndexedAssignedSelfBulkSmoothnessFields
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  /-- Smoothness neighborhood for each assigned-chart scalar piece. -/
  smoothSet : C.CoverIndex → Set (Fin (n + 1) → Real)
  /-- The smoothness neighborhoods are open. -/
  isOpen_smoothSet :
    ∀ j : C.CoverIndex, IsOpen (smoothSet j)
  /-- Each closed carrier lies in its smoothness neighborhood. -/
  closedCarrier_subset_smoothSet :
    ∀ j : C.CoverIndex, C.coverIndexClosedCarrier j ⊆ smoothSet j
  /-- The localized assigned-chart representative is smooth on that neighborhood. -/
  localized_contDiffOn :
    ∀ j : C.CoverIndex,
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I
          (C.assignedChart j) (C.assignedChart j)
          (P.coverIndexLocalizedForm ω j)) (smoothSet j)

namespace CoverIndexedAssignedSelfBulkSmoothnessFields

/--
Assigned-chart smoothness gives the closed-carrier continuity required by the
bulk measure layer.
-/
theorem piece_continuousOn_closedCarrier
    {P : SupportControlledSelectedPartition C}
    (D : CoverIndexedAssignedSelfBulkSmoothnessFields
      (I := I) (C := C) P ω) :
    ∀ j : C.CoverIndex,
      ContinuousOn
        (P.assignedSelfBulkPieceIntegrand (I := I) ω j)
        (C.coverIndexClosedCarrier j) := by
  intro j
  simpa [SupportControlledSelectedPartition.assignedSelfBulkPieceIntegrand]
    using
      bulkIntegrand_continuousOn_of_contDiffOn_isOpen
        (I := I) (x0 := C.assignedChart j) (x1 := C.assignedChart j)
        (ω := P.coverIndexLocalizedForm ω j)
        (U := D.smoothSet j) (s := C.coverIndexClosedCarrier j)
        (D.isOpen_smoothSet j)
        (D.closedCarrier_subset_smoothSet j)
        (D.localized_contDiffOn j)

end CoverIndexedAssignedSelfBulkSmoothnessFields

/--
The assigned-chart self-pair local set-integral identity, transported to an
arbitrary measure propositionally equal to `volume`.
-/
theorem assignedSelf_localBulk_eq_setIntegral_assigned_of_tsupport_subset
    (P : SupportControlledSelectedPartition C)
    (hμ : μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (hsupp :
      ∀ j : C.CoverIndex,
        tsupport (P.assignedSelfBulkPieceIntegrand (I := I) ω j) ⊆
          C.assignedCoordinateBox j) :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm ω j =
        ∫ y in C.assignedCoordinateBox j,
          P.assignedSelfBulkPieceIntegrand (I := I) ω j y ∂μBulk := by
  have hlocal :=
    P.coverIndexLocalBulkTerm_eq_setIntegral_assigned_self_of_tsupport_subset_of_measure_eq_volume
      (C := C) (ω := ω) (μ := μBulk) hμ
      (by
        intro j
        simpa [SupportControlledSelectedPartition.assignedSelfBulkPieceIntegrand]
          using hsupp j)
  intro j
  simpa [SupportControlledSelectedPartition.assignedSelfBulkPieceIntegrand]
    using hlocal j

end SupportControlledSelectedPartition

/--
Grouped assigned-chart bulk input.

The local pieces use the selected chart of each cover index.  The global scalar
may be any representative that is a.e. equal to the assigned-chart finite sum.
Choosing `integrand = P.assignedSelfBulkIntegrand ω` makes that a.e. field
definitionally trivial.
-/
structure CoverIndexedAssignedSelfBulkInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n)
    (μBulk : Measure (Fin (n + 1) → Real)) where
  /-- Global bulk scalar representative. -/
  integrand : (Fin (n + 1) → Real) → Real
  /-- Represented global bulk integral. -/
  globalIntegral : Real
  /-- The represented global bulk integral is the integral of `integrand`. -/
  globalIntegral_eq_integral :
    globalIntegral = ∫ y, integrand y ∂μBulk
  /-- The coordinate bulk measure is the usual volume measure. -/
  measure_eq_volume :
    μBulk = (volume : Measure (Fin (n + 1) → Real))
  /-- Assigned-chart local scalar pieces are continuous on closed carriers. -/
  piece_continuousOn_closedCarrier :
    ∀ j : C.CoverIndex,
      ContinuousOn
        (P.assignedSelfBulkPieceIntegrand (I := I) ω j)
        (C.coverIndexClosedCarrier j)
  /-- Assigned-chart local scalar pieces are supported in assigned boxes. -/
  piece_tsupport_subset_assigned :
    ∀ j : C.CoverIndex,
      tsupport (P.assignedSelfBulkPieceIntegrand (I := I) ω j) ⊆
        C.assignedCoordinateBox j
  /-- The global scalar reconstructs the assigned-chart finite sum a.e. -/
  integrand_ae_eq_pieceSum :
    integrand =ᵐ[μBulk] P.assignedSelfBulkIntegrand (I := I) ω

namespace CoverIndexedAssignedSelfBulkInput

/-- Local assigned-box integrals are generated by the self-chart lemma. -/
theorem localBulk_eq_setIntegral_assigned
    (D : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk) :
    ∀ j : C.CoverIndex,
      P.coverIndexLocalBulkTerm ω j =
        ∫ y in C.assignedCoordinateBox j,
          P.assignedSelfBulkPieceIntegrand (I := I) ω j y ∂μBulk :=
  P.assignedSelf_localBulk_eq_setIntegral_assigned_of_tsupport_subset
    (I := I) (ω := ω) D.measure_eq_volume
    D.piece_tsupport_subset_assigned

/-- Local assigned-box integrals transported to the compact closed carriers. -/
theorem localBulk_eq_setIntegral_closedCarrier
    (D : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk)
    (j : C.CoverIndex) :
    P.coverIndexLocalBulkTerm ω j =
      ∫ y in C.coverIndexClosedCarrier j,
        P.assignedSelfBulkPieceIntegrand (I := I) ω j y ∂μBulk :=
  localTerm_eq_setIntegral_over_superset_of_tsupport_subset
    (μ := μBulk)
    (s := C.assignedCoordinateBox j)
    (t := C.coverIndexClosedCarrier j)
    (f := P.assignedSelfBulkPieceIntegrand (I := I) ω j)
    (hs := C.measurableSet_assignedCoordinateBox j)
    (ht := (C.coverIndex_closedCarrier_isCompact j).measurableSet)
    (hst := C.coverIndex_openSupportBox_subset_closedCarrier j)
    (htsupport := D.piece_tsupport_subset_assigned j)
    (hlocal := D.localBulk_eq_setIntegral_assigned j)

/-- Convert assigned-chart self-pair bulk input to closed-carrier bulk data. -/
def toClosedCarrierBulkData
    (D : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk) :
    CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk) C P ω where
  integrand := D.integrand
  pieceIntegrand :=
    fun j => P.assignedSelfBulkPieceIntegrand (I := I) ω j
  globalIntegral := D.globalIntegral
  globalIntegral_eq_integral := D.globalIntegral_eq_integral
  piece_continuousOn_closedCarrier := D.piece_continuousOn_closedCarrier
  piece_tsupport_subset_assignedCoordinateBox :=
    D.piece_tsupport_subset_assigned
  localBulk_eq_setIntegral_closedCarrier :=
    D.localBulk_eq_setIntegral_closedCarrier
  integrand_ae_eq_pieceSum := by
    simpa [SupportControlledSelectedPartition.assignedSelfBulkIntegrand]
      using D.integrand_ae_eq_pieceSum

/-- Assigned-chart self-pair bulk input as resolved bulk fields. -/
def toResolvedBulkFields
    (D : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk) :
    CoverIndexedResolvedBulkFields
      (C := C) (ω := ω)
      (αBulk := Fin (n + 1) → Real) (μBulk := μBulk) P :=
  D.toClosedCarrierBulkData.toResolvedBulkFields

@[simp]
theorem toClosedCarrierBulkData_integrand
    (D : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk) :
    D.toClosedCarrierBulkData.integrand = D.integrand :=
  rfl

@[simp]
theorem toClosedCarrierBulkData_globalIntegral
    (D : CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk) :
    D.toClosedCarrierBulkData.globalIntegral = D.globalIntegral :=
  rfl

/--
Constructor from per-index assigned-chart smoothness and an external global
representative a.e. equal to the assigned-chart finite sum.
-/
def ofSmoothness
    (integrand : (Fin (n + 1) → Real) → Real)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral = ∫ y, integrand y ∂μBulk)
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (smooth :
      SupportControlledSelectedPartition.CoverIndexedAssignedSelfBulkSmoothnessFields
        (I := I) (C := C) P ω)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport (P.assignedSelfBulkPieceIntegrand (I := I) ω j) ⊆
          C.assignedCoordinateBox j)
    (integrand_ae_eq_pieceSum :
      integrand =ᵐ[μBulk] P.assignedSelfBulkIntegrand (I := I) ω) :
    CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk where
  integrand := integrand
  globalIntegral := globalIntegral
  globalIntegral_eq_integral := globalIntegral_eq_integral
  measure_eq_volume := measure_eq_volume
  piece_continuousOn_closedCarrier :=
    smooth.piece_continuousOn_closedCarrier
  piece_tsupport_subset_assigned := piece_tsupport_subset_assigned
  integrand_ae_eq_pieceSum := integrand_ae_eq_pieceSum

/--
Canonical finite-sum constructor.  It avoids a separate finite-sum/a.e.
differentiability reconstruction by taking the global bulk scalar to be the
assigned-chart piece sum itself.
-/
def ofSmoothnessFiniteSum
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (smooth :
      SupportControlledSelectedPartition.CoverIndexedAssignedSelfBulkSmoothnessFields
        (I := I) (C := C) P ω)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport (P.assignedSelfBulkPieceIntegrand (I := I) ω j) ⊆
          C.assignedCoordinateBox j) :
    CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk where
  integrand := P.assignedSelfBulkIntegrand (I := I) ω
  globalIntegral :=
    ∫ y, P.assignedSelfBulkIntegrand (I := I) ω y ∂μBulk
  globalIntegral_eq_integral := rfl
  measure_eq_volume := measure_eq_volume
  piece_continuousOn_closedCarrier :=
    smooth.piece_continuousOn_closedCarrier
  piece_tsupport_subset_assigned := piece_tsupport_subset_assigned
  integrand_ae_eq_pieceSum :=
    P.assignedSelfBulkIntegrand_ae_eq_pieceSum (I := I) ω μBulk

end CoverIndexedAssignedSelfBulkInput

namespace SupportControlledSelectedPartition

/-- Direct closed-carrier bulk data constructor with assigned-chart self-pairs. -/
def assignedSelfClosedCarrierBulkData_of_smoothness
    (P : SupportControlledSelectedPartition C)
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (smooth :
      CoverIndexedAssignedSelfBulkSmoothnessFields
        (I := I) (C := C) P ω)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport (P.assignedSelfBulkPieceIntegrand (I := I) ω j) ⊆
          C.assignedCoordinateBox j) :
    CoverIndexedClosedCarrierBulkData
      (I := I) (K := K) (μBulk := μBulk) C P ω :=
  (CoverIndexedAssignedSelfBulkInput.ofSmoothnessFiniteSum
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk) measure_eq_volume smooth
    piece_tsupport_subset_assigned).toClosedCarrierBulkData

/-- Direct resolved bulk fields constructor with assigned-chart self-pairs. -/
def assignedSelfResolvedBulkFields_of_smoothness
    (P : SupportControlledSelectedPartition C)
    (measure_eq_volume :
      μBulk = (volume : Measure (Fin (n + 1) → Real)))
    (smooth :
      CoverIndexedAssignedSelfBulkSmoothnessFields
        (I := I) (C := C) P ω)
    (piece_tsupport_subset_assigned :
      ∀ j : C.CoverIndex,
        tsupport (P.assignedSelfBulkPieceIntegrand (I := I) ω j) ⊆
          C.assignedCoordinateBox j) :
    CoverIndexedResolvedBulkFields
      (C := C) (ω := ω)
      (αBulk := Fin (n + 1) → Real) (μBulk := μBulk) P :=
  (P.assignedSelfClosedCarrierBulkData_of_smoothness
    (I := I) (K := K) (ω := ω) (μBulk := μBulk)
    measure_eq_volume smooth piece_tsupport_subset_assigned
    ).toResolvedBulkFields

end SupportControlledSelectedPartition

end AssignedSelfBulk

end Stokes

end
