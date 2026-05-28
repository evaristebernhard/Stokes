import Stokes.Global.CoverIndexedBoundarySupportContinuityConstructor
import Stokes.Global.CoverIndexedNaturalConstructor

/-!
# Cover-indexed boundary a.e. finite-sum constructors

This file removes one bookkeeping field from the represented compact-support
boundary route.  When the global boundary scalar representative is chosen to be
the finite sum of the target boundary pieces, the a.e. reconstruction field
`boundaryIntegrand_ae_eq_pieceSum` is definitional.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedBoundaryAESum

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace SupportControlledSelectedPartition

/-- Canonical target-side global boundary scalar: the finite sum of all
cover-indexed target boundary pieces. -/
def coverIndexBoundaryTargetPieceSum
    (P : SupportControlledSelectedPartition C)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (ω : ManifoldForm I M n) :
    (Fin n → Real) → Real :=
  fun y =>
    ∑ j : C.CoverIndex,
      P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y

/-- The canonical target-side boundary scalar is a.e. the required target-piece
finite sum, by definition. -/
theorem coverIndexBoundaryTargetPieceSum_ae_eq_pieceSum
    (P : SupportControlledSelectedPartition C)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (ω : ManifoldForm I M n) :
    P.coverIndexBoundaryTargetPieceSum targetChart ω
      =ᵐ[(volume : Measure (Fin n → Real))]
        fun y =>
          ∑ j : C.CoverIndex,
            P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y := by
  exact Filter.EventuallyEq.rfl

/-- Pointwise equality with the target-piece sum automatically gives the a.e.
reconstruction field expected by the cover-indexed boundary constructors. -/
theorem boundaryIntegrand_ae_eq_targetPieceSum_of_pointwise
    (P : SupportControlledSelectedPartition C)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (ω : ManifoldForm I M n)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (hpiece :
      ∀ y,
        boundaryIntegrand y =
          ∑ j : C.CoverIndex,
            P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y) :
    boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
      fun y =>
        ∑ j : C.CoverIndex,
          P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y :=
  ae_of_all (volume : Measure (Fin n → Real)) hpiece

/-- Equality with the canonical target-piece-sum representative automatically
gives the a.e. reconstruction field. -/
theorem boundaryIntegrand_ae_eq_targetPieceSum_of_eq
    (P : SupportControlledSelectedPartition C)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (ω : ManifoldForm I M n)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (hpiece :
      boundaryIntegrand =
        P.coverIndexBoundaryTargetPieceSum targetChart ω) :
    boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
      fun y =>
        ∑ j : C.CoverIndex,
          P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y := by
  subst boundaryIntegrand
  exact P.coverIndexBoundaryTargetPieceSum_ae_eq_pieceSum targetChart ω

end SupportControlledSelectedPartition

namespace CoverIndexedResolvedBoundaryFields

variable (P : SupportControlledSelectedPartition C)

/-- Target-COV boundary resolved fields using the canonical target-piece-sum
global boundary representative. -/
def ofTargetCOVTargetPieceSum
    [IsManifold I 1 M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetChart ω y
          ∂(volume : Measure (Fin n → Real)))
    (boundaryPiece_isCompact :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsCompact (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
          (Sum.inr i)))
    (boundaryPiece_continuousOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContinuousOn
          (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i))
          (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
            (Sum.inr i)))
    (boundaryPiece_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i)) ⊆
          P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
            (Sum.inr i))
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (hcov :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartOrientedChangeOfVariables I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i)) :
    CoverIndexedResolvedBoundaryFields
      (C := C) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) P :=
  CoverIndexedResolvedBoundaryFields.ofTargetCOVPieceSum
    (C := C) (ω := ω) P targetChart targetLower targetUpper
    (P.coverIndexBoundaryTargetPieceSum targetChart ω)
    globalBoundaryIntegral globalBoundaryIntegral_eq_integral
    boundaryPiece_isCompact boundaryPiece_continuousOn
    boundaryPiece_tsupport_subset
    sourceSelfSelectedBox sourceTargetSelectedBox hcov
    (P.coverIndexBoundaryTargetPieceSum_ae_eq_pieceSum targetChart ω)

/-- Target-COV boundary resolved fields using canonical target-piece-sum
reconstruction and support/continuity data. -/
def ofTargetCOVTargetPieceSum_supportContinuity
    [IsManifold I 1 M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (supportContinuity :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetChart ω y
          ∂(volume : Measure (Fin n → Real)))
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (hcov :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartOrientedChangeOfVariables I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i)) :
    CoverIndexedResolvedBoundaryFields
      (C := C) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) P :=
  CoverIndexedResolvedBoundaryFields.ofTargetCOVTargetPieceSum
    (C := C) (ω := ω) P targetChart targetLower targetUpper
    globalBoundaryIntegral globalBoundaryIntegral_eq_integral
    supportContinuity.piece_isCompact
    supportContinuity.piece_continuousOn
    supportContinuity.piece_tsupport_subset
    sourceSelfSelectedBox sourceTargetSelectedBox hcov

end CoverIndexedResolvedBoundaryFields

namespace CoverIndexedTargetBoundaryMeasureData

/-- Target-boundary natural measure data using the canonical target-piece-sum
global boundary representative. -/
def ofTargetPieceSum
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetChart ω y
          ∂(volume : Measure (Fin n → Real)))
    (boundaryPiece_isCompact :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsCompact
          (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
            (Sum.inr i)))
    (boundaryPiece_continuousOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContinuousOn
          (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i))
          (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
            (Sum.inr i)))
    (boundaryPiece_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i)) ⊆
          P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
            (Sum.inr i))
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (orientedCOV :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartOrientedChangeOfVariables I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i)) :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω where
  targetChart := targetChart
  targetLower := targetLower
  targetUpper := targetUpper
  boundaryIntegrand :=
    P.coverIndexBoundaryTargetPieceSum targetChart ω
  globalIntegral := globalIntegral
  globalIntegral_eq_integral := globalIntegral_eq_integral
  boundaryPiece_isCompact := boundaryPiece_isCompact
  boundaryPiece_continuousOn := boundaryPiece_continuousOn
  boundaryPiece_tsupport_subset := boundaryPiece_tsupport_subset
  sourceSelfSelectedBox := sourceSelfSelectedBox
  sourceTargetSelectedBox := sourceTargetSelectedBox
  orientedCOV := orientedCOV
  boundaryIntegrand_ae_eq_pieceSum :=
    P.coverIndexBoundaryTargetPieceSum_ae_eq_pieceSum targetChart ω

/-- Target-boundary natural measure data from canonical target-piece-sum
reconstruction plus packaged target support/continuity facts. -/
def ofTargetPieceSum_supportContinuity
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (supportContinuity :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetChart ω y
          ∂(volume : Measure (Fin n → Real)))
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (orientedCOV :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartOrientedChangeOfVariables I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i)) :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω :=
  CoverIndexedTargetBoundaryMeasureData.ofTargetPieceSum
    (C := C) (P := P) (ω := ω)
    targetChart targetLower targetUpper
    globalIntegral globalIntegral_eq_integral
    supportContinuity.piece_isCompact
    supportContinuity.piece_continuousOn
    supportContinuity.piece_tsupport_subset
    sourceSelfSelectedBox sourceTargetSelectedBox orientedCOV

end CoverIndexedTargetBoundaryMeasureData

namespace CoverIndexedNaturalBoundaryData

variable (P : SupportControlledSelectedPartition C)

/-- Natural boundary data using the canonical target-piece-sum global boundary
representative.  This is the direct natural-assembly version of
`CoverIndexedTargetBoundaryMeasureData.ofTargetPieceSum`. -/
def ofTargetCOVTargetPieceSum
    [IsManifold I 1 M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetChart ω y
          ∂(volume : Measure (Fin n → Real)))
    (boundaryPiece_isCompact :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsCompact
          (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
            (Sum.inr i)))
    (boundaryPiece_continuousOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContinuousOn
          (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i))
          (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
            (Sum.inr i)))
    (boundaryPiece_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i)) ⊆
          P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
            (Sum.inr i))
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (hcov :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartOrientedChangeOfVariables I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i)) :
    CoverIndexedNaturalBoundaryData
      (I := I) (K := K) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) C P :=
  (CoverIndexedTargetBoundaryMeasureData.ofTargetPieceSum
    (C := C) (P := P) (ω := ω)
    targetChart targetLower targetUpper
    globalBoundaryIntegral globalBoundaryIntegral_eq_integral
    boundaryPiece_isCompact boundaryPiece_continuousOn
    boundaryPiece_tsupport_subset
    sourceSelfSelectedBox sourceTargetSelectedBox hcov).toNaturalBoundaryData

/-- Natural boundary data from canonical target-piece-sum reconstruction plus
packaged target support/continuity facts. -/
def ofTargetCOVTargetPieceSum_supportContinuity
    [IsManifold I 1 M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (supportContinuity :
      CoverIndexedBoundaryTargetSupportContinuityData
        (C := C) P ω targetChart targetLower targetUpper)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, P.coverIndexBoundaryTargetPieceSum targetChart ω y
          ∂(volume : Measure (Fin n → Real)))
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (hcov :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartOrientedChangeOfVariables I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i)) :
    CoverIndexedNaturalBoundaryData
      (I := I) (K := K) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) C P :=
  CoverIndexedNaturalBoundaryData.ofTargetCOVTargetPieceSum
    (C := C) (P := P) (ω := ω)
    targetChart targetLower targetUpper
    globalBoundaryIntegral globalBoundaryIntegral_eq_integral
    supportContinuity.piece_isCompact
    supportContinuity.piece_continuousOn
    supportContinuity.piece_tsupport_subset
    sourceSelfSelectedBox sourceTargetSelectedBox hcov

end CoverIndexedNaturalBoundaryData

end CoverIndexedBoundaryAESum

end Stokes

end
