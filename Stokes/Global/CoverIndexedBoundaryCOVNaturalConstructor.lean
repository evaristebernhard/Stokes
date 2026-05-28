import Stokes.Global.CoverIndexedNaturalConstructor

/-!
# Natural boundary COV constructors for the cover-indexed route

This file removes the orientation/COV bookkeeping from
`CoverIndexedTargetBoundaryMeasureData`.  Given the local assigned-box data, a
source-to-target selected boundary box, target image data, and either an
oriented boundary atlas or oriented-manifold instance, it fills the
source-self selected box and oriented change-of-variables fields automatically.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryCOVNaturalConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedAssignedBoxLocalData

/--
The boundary assigned-box local data already contains exactly the information
needed to view each localized boundary piece as a selected self chart box.
-/
theorem sourceSelfSelectedBox
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    boundaryChartSelectedBox I
      (C.boundaryChart i.1) (C.boundaryChart i.1)
      (P.coverIndexLocalizedForm ω (Sum.inr i))
      (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  rcases D.boundaryAssignedFields i with
    ⟨_hcompact, _hhalf, hbase, ha0, hle, hcoeff, hdomain,
      _hopen, _hbox⟩
  refine ⟨ha0, hle, hdomain, ?_⟩
  simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm] using
    (ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
        (I := I)
        (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
        (ρ := P.partition (Sum.inr i)) (ω := ω)
        (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
        (C := D.boundaryCoordSupport i) hbase hcoeff)

end CoverIndexedAssignedBoxLocalData

namespace CoverIndexedTargetBoundaryMeasureData

variable
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)

/--
Target-boundary measure data from a project-local oriented atlas.

The caller supplies the source-to-target selected boxes and image data.  The
self selected boxes are projected from the local assigned-box data, and the
oriented COV fields are generated from the oriented atlas bridge.
-/
def ofOrientedAtlas
    [IsManifold I 1 M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (A : BoundaryChartOrientedAtlas I M)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (imageData :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBoxImageData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i))
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      targetChart i ∈ A.charts)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, boundaryIntegrand y ∂(volume : Measure (Fin n → Real)))
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
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        fun y =>
          ∑ j : C.CoverIndex,
            P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y) :
    CoverIndexedTargetBoundaryMeasureData C P ω where
  targetChart := targetChart
  targetLower := targetLower
  targetUpper := targetUpper
  boundaryIntegrand := boundaryIntegrand
  globalIntegral := globalIntegral
  globalIntegral_eq_integral := globalIntegral_eq_integral
  boundaryPiece_isCompact := boundaryPiece_isCompact
  boundaryPiece_continuousOn := boundaryPiece_continuousOn
  boundaryPiece_tsupport_subset := boundaryPiece_tsupport_subset
  sourceSelfSelectedBox := localData.sourceSelfSelectedBox
  sourceTargetSelectedBox := sourceTargetSelectedBox
  orientedCOV := by
    let D :=
      P.coverIndexBoundaryChartOrientationInput
        (ω := ω) targetChart targetLower targetUpper
        sourceTargetSelectedBox imageData
    exact fun i =>
      D.orientedChangeOfVariablesOfOrientedAtlas A hsource htarget i
  boundaryIntegrand_ae_eq_pieceSum := boundaryIntegrand_ae_eq_pieceSum

/--
Target-boundary measure data from a global project-local oriented-manifold
instance.
-/
def ofOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (imageData :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBoxImageData I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i))
    (boundaryIntegrand : (Fin n → Real) → Real)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, boundaryIntegrand y ∂(volume : Measure (Fin n → Real)))
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
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        fun y =>
          ∑ j : C.CoverIndex,
            P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y) :
    CoverIndexedTargetBoundaryMeasureData C P ω where
  targetChart := targetChart
  targetLower := targetLower
  targetUpper := targetUpper
  boundaryIntegrand := boundaryIntegrand
  globalIntegral := globalIntegral
  globalIntegral_eq_integral := globalIntegral_eq_integral
  boundaryPiece_isCompact := boundaryPiece_isCompact
  boundaryPiece_continuousOn := boundaryPiece_continuousOn
  boundaryPiece_tsupport_subset := boundaryPiece_tsupport_subset
  sourceSelfSelectedBox := localData.sourceSelfSelectedBox
  sourceTargetSelectedBox := sourceTargetSelectedBox
  orientedCOV := by
    let D :=
      P.coverIndexBoundaryChartOrientationInput
        (ω := ω) targetChart targetLower targetUpper
        sourceTargetSelectedBox imageData
    exact fun i => D.orientedChangeOfVariablesOfOrientedManifold i
  boundaryIntegrand_ae_eq_pieceSum := boundaryIntegrand_ae_eq_pieceSum

/--
Target-selection variant of `ofOrientedAtlas`: the selected target image data
is projected from `BoundaryChartTargetBoxSelection`.
-/
def ofTargetSelectionOrientedAtlas
    [IsManifold I 1 M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (A : BoundaryChartOrientedAtlas I M)
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      targetChart i ∈ A.charts)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, boundaryIntegrand y ∂(volume : Measure (Fin n → Real)))
    (boundaryPiece_isCompact :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsCompact
          (P.coverIndexBoundaryTargetPieceSet
            (fun i => (targetSelection i).lowerCorner)
            (fun i => (targetSelection i).upperCorner)
            (Sum.inr i)))
    (boundaryPiece_continuousOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContinuousOn
          (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i))
          (P.coverIndexBoundaryTargetPieceSet
            (fun i => (targetSelection i).lowerCorner)
            (fun i => (targetSelection i).upperCorner)
            (Sum.inr i)))
    (boundaryPiece_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i)) ⊆
          P.coverIndexBoundaryTargetPieceSet
            (fun i => (targetSelection i).lowerCorner)
            (fun i => (targetSelection i).upperCorner)
            (Sum.inr i))
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        fun y =>
          ∑ j : C.CoverIndex,
            P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y) :
    CoverIndexedTargetBoundaryMeasureData C P ω :=
  ofOrientedAtlas
    (C := C) (P := P) (ω := ω)
    (targetChart := targetChart)
    (targetLower := fun i => (targetSelection i).lowerCorner)
    (targetUpper := fun i => (targetSelection i).upperCorner)
    localData A sourceTargetSelectedBox
    (fun i => (targetSelection i).imageData)
    hsource htarget boundaryIntegrand globalIntegral
    globalIntegral_eq_integral boundaryPiece_isCompact
    boundaryPiece_continuousOn boundaryPiece_tsupport_subset
    boundaryIntegrand_ae_eq_pieceSum

/--
Oriented-manifold target-selection variant of `ofOrientedManifold`.
-/
def ofTargetSelectionOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (sourceTargetSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (boundaryIntegrand : (Fin n → Real) → Real)
    (globalIntegral : Real)
    (globalIntegral_eq_integral :
      globalIntegral =
        ∫ y, boundaryIntegrand y ∂(volume : Measure (Fin n → Real)))
    (boundaryPiece_isCompact :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        IsCompact
          (P.coverIndexBoundaryTargetPieceSet
            (fun i => (targetSelection i).lowerCorner)
            (fun i => (targetSelection i).upperCorner)
            (Sum.inr i)))
    (boundaryPiece_continuousOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContinuousOn
          (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i))
          (P.coverIndexBoundaryTargetPieceSet
            (fun i => (targetSelection i).lowerCorner)
            (fun i => (targetSelection i).upperCorner)
            (Sum.inr i)))
    (boundaryPiece_tsupport_subset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω (Sum.inr i)) ⊆
          P.coverIndexBoundaryTargetPieceSet
            (fun i => (targetSelection i).lowerCorner)
            (fun i => (targetSelection i).upperCorner)
            (Sum.inr i))
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        fun y =>
          ∑ j : C.CoverIndex,
            P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y) :
    CoverIndexedTargetBoundaryMeasureData C P ω :=
  ofOrientedManifold
    (C := C) (P := P) (ω := ω)
    (targetChart := targetChart)
    (targetLower := fun i => (targetSelection i).lowerCorner)
    (targetUpper := fun i => (targetSelection i).upperCorner)
    localData sourceTargetSelectedBox
    (fun i => (targetSelection i).imageData)
    boundaryIntegrand globalIntegral globalIntegral_eq_integral
    boundaryPiece_isCompact boundaryPiece_continuousOn
    boundaryPiece_tsupport_subset boundaryIntegrand_ae_eq_pieceSum

end CoverIndexedTargetBoundaryMeasureData

end BoundaryCOVNaturalConstructor

end Stokes

end
