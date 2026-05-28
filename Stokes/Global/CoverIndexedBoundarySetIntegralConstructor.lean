import Stokes.Global.CoverIndexedResolvedInput
import Stokes.Global.BoundaryMeasureFromTargetCOV
import Stokes.BoundaryChart.CoverIndexedOrientationBridge
import Stokes.BoundaryChart.CoverIndexedTargetImageConstructor

/-!
# Cover-indexed boundary set-integral constructors

This file removes one real boundary-side field from the cover-indexed compact
support route.  The previous resolved boundary package still asked callers to
provide

`localBoundary_eq_setIntegral :
  P.coverIndexLocalBoundaryTerm omega j = ∫ y in pieceSet j, pieceIntegrand j y`.

For boundary cover indices, that equality is obtained from the oriented
boundary chart change-of-variables package.  Interior cover indices contribute
zero and are represented by the empty set with zero integrand.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BasicTargetSetIntegral

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- Target boundary carrier selected by a boundary chart change of variables. -/
def boundaryTargetInChartPieceSet
    (c d : Fin (n + 1) → Real) : Set (Fin n → Real) :=
  lowerZeroFaceDomain c d

/-- Target boundary scalar representative in the target chart. -/
def boundaryTargetInChartPieceIntegrand
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x : M) (ω : ManifoldForm I M n) (u : Fin n → Real) : Real :=
  outwardFirstBoundaryOrientationSign n *
    ManifoldForm.inChart I x ω (boundaryInclusion n u) (boundaryTangent n)

/--
An oriented boundary chart COV package turns the source project-local boundary
integral into the target in-chart set integral.
-/
theorem projectLocalBoundaryIntegral_eq_targetInChartSetIntegral_of_orientedCOV
    [IsManifold I 1 M]
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b c d : Fin (n + 1) → Real)
    (hcov : boundaryChartOrientedChangeOfVariables I x0 x1 ω a b c d) :
    projectLocalBoundaryIntegral I x0 x1 ω a b =
      ∫ u in boundaryTargetInChartPieceSet c d,
        boundaryTargetInChartPieceIntegrand I x1 ω u ∂volume := by
  calc
    projectLocalBoundaryIntegral I x0 x1 ω a b =
        outwardFirstBoundaryInChartIntegral I x1 ω c d := by
          simpa [projectLocalBoundaryIntegral] using
            outwardFirstBoundaryChartIntegral_eq_inChart_of_orientedChangeOfVariables
              x0 x1 ω a b c d hcov
    _ =
        ∫ u in boundaryTargetInChartPieceSet c d,
          boundaryTargetInChartPieceIntegrand I x1 ω u ∂volume := by
          simp [boundaryTargetInChartPieceSet,
            boundaryTargetInChartPieceIntegrand,
            outwardFirstBoundaryInChartIntegral,
            halfSpaceBoundaryInChartIntegral, halfSpaceBoundaryFormIntegral,
            ← integral_neg]

end BasicTargetSetIntegral

section CoverIndexedBoundarySetIntegral

universe u w a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}

namespace SupportControlledSelectedPartition

variable (P : SupportControlledSelectedPartition C)

/-- Source-side carrier for the concrete cover-indexed boundary term. -/
def coverIndexBoundarySourcePieceSet :
    SupportControlledSelectedPartition C →
    C.CoverIndex → Set (Fin n → Real)
  | _P, Sum.inl _ => ∅
  | _P, Sum.inr i => lowerZeroFaceDomain (C.boundaryLower i.1) (C.boundaryUpper i.1)

/-- Source-side scalar representative for the concrete cover-indexed boundary term. -/
def coverIndexBoundarySourcePieceIntegrand
    (ω : ManifoldForm I M n) :
    C.CoverIndex → (Fin n → Real) → Real
  | Sum.inl _ => fun _ => 0
  | Sum.inr i => fun u =>
      outwardFirstBoundaryOrientationSign n *
        ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (boundaryInclusion n u) (boundaryTangent n)

/--
The source-side project-local boundary term is definitionally a set integral.
This handles interior cover indices by the empty carrier/zero-integrand
convention.
-/
theorem coverIndexLocalBoundaryTerm_eq_sourceSetIntegral
    (j : C.CoverIndex) :
    P.coverIndexLocalBoundaryTerm ω j =
      ∫ u in P.coverIndexBoundarySourcePieceSet j,
        P.coverIndexBoundarySourcePieceIntegrand ω j u ∂volume := by
  rcases j with i | i
  · simp [coverIndexBoundarySourcePieceSet,
      coverIndexBoundarySourcePieceIntegrand,
      SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm]
  · simp [coverIndexBoundarySourcePieceSet,
      coverIndexBoundarySourcePieceIntegrand,
      SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm,
      projectLocalBoundaryIntegral, outwardFirstBoundaryChartIntegral,
      halfSpaceBoundaryTransitionFormIntegral, halfSpaceBoundaryFormIntegral,
      ← integral_neg]

/-- Target-side carrier for a cover-indexed boundary chart COV family. -/
def coverIndexBoundaryTargetPieceSet
    (P : SupportControlledSelectedPartition C)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real) :
    C.CoverIndex → Set (Fin n → Real)
  | Sum.inl _ => ∅
  | Sum.inr i => boundaryTargetInChartPieceSet (targetLower i) (targetUpper i)

/-- Target-side scalar representative for a cover-indexed boundary chart COV family. -/
def coverIndexBoundaryTargetPieceIntegrand
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (ω : ManifoldForm I M n) :
    C.CoverIndex → (Fin n → Real) → Real
  | Sum.inl _ => fun _ => 0
  | Sum.inr i => fun u =>
      boundaryTargetInChartPieceIntegrand I (targetChart i)
        (P.coverIndexLocalizedForm ω (Sum.inr i)) u

/--
Per-cover-index target set-integral equality from resolved oriented COV data.

The source side is exactly the boundary term currently used by
`P.coverIndexLocalBoundaryTerm`; the target side is the selected target
boundary box and target in-chart scalar representative.
-/
theorem coverIndexLocalBoundaryTerm_eq_targetSetIntegral_of_orientedCOV
    [IsManifold I 1 M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
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
          (targetLower i) (targetUpper i))
    (j : C.CoverIndex) :
    P.coverIndexLocalBoundaryTerm ω j =
      ∫ u in P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j,
        P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j u ∂volume := by
  rcases j with i | i
  · simp [coverIndexBoundaryTargetPieceSet, coverIndexBoundaryTargetPieceIntegrand,
      SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm]
  · calc
      P.coverIndexLocalBoundaryTerm ω (Sum.inr i) =
          projectLocalBoundaryIntegral I (C.boundaryChart i.1) (targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
            simpa [SupportControlledSelectedPartition.coverIndexLocalBoundaryTerm,
              projectLocalBoundaryIntegral] using
              outwardFirstBoundaryChartIntegral_chartChange_invariant_of_selectedBoxes
                (I := I)
                (x0 := C.boundaryChart i.1)
                (x1 := C.boundaryChart i.1)
                (x2 := targetChart i)
                (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
                (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
                (sourceSelfSelectedBox i) (sourceTargetSelectedBox i)
      _ =
          ∫ u in P.coverIndexBoundaryTargetPieceSet targetLower targetUpper
              (Sum.inr i),
            P.coverIndexBoundaryTargetPieceIntegrand targetChart ω
              (Sum.inr i) u ∂volume := by
            simpa [coverIndexBoundaryTargetPieceSet,
              coverIndexBoundaryTargetPieceIntegrand] using
              projectLocalBoundaryIntegral_eq_targetInChartSetIntegral_of_orientedCOV
                (I := I)
                (x0 := C.boundaryChart i.1) (x1 := targetChart i)
                (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
                (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
                (c := targetLower i) (d := targetUpper i)
                (hcov i)

/-- Indexed orientation input whose source side is the selected boundary cover. -/
def coverIndexBoundaryChartOrientationInput
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (selectedBox :
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
          (targetLower i) (targetUpper i)) :
    CoverIndexedBoundaryChartOrientationInput
      (M := M) I {x : M // x ∈ C.boundaryCenters} where
  sourceChart := fun i => C.boundaryChart i.1
  targetChart := targetChart
  form := fun i => P.coverIndexLocalizedForm ω (Sum.inr i)
  lower := fun i => C.boundaryLower i.1
  upper := fun i => C.boundaryUpper i.1
  targetLower := targetLower
  targetUpper := targetUpper
  selectedBox := selectedBox
  imageData := imageData

/--
Target set-integral equality obtained directly from a project-local oriented
atlas and selected target image data.
-/
theorem coverIndexLocalBoundaryTerm_eq_targetSetIntegral_of_orientedAtlas
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (selectedBox :
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
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (j : C.CoverIndex) :
    P.coverIndexLocalBoundaryTerm ω j =
      ∫ u in P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j,
        P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j u ∂volume := by
  let D :=
    P.coverIndexBoundaryChartOrientationInput
      (ω := ω) targetChart targetLower targetUpper selectedBox imageData
  exact
    P.coverIndexLocalBoundaryTerm_eq_targetSetIntegral_of_orientedCOV
      (ω := ω) targetChart targetLower targetUpper
      sourceSelfSelectedBox selectedBox
      (fun i =>
        D.orientedChangeOfVariablesOfOrientedAtlas A hsource htarget i)
      j

/--
Target set-integral equality obtained from global project-local
`BoundaryChartOrientedManifold` data and selected target image data.
-/
theorem coverIndexLocalBoundaryTerm_eq_targetSetIntegral_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (selectedBox :
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
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (j : C.CoverIndex) :
    P.coverIndexLocalBoundaryTerm ω j =
      ∫ u in P.coverIndexBoundaryTargetPieceSet targetLower targetUpper j,
        P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j u ∂volume := by
  let D :=
    P.coverIndexBoundaryChartOrientationInput
      (ω := ω) targetChart targetLower targetUpper selectedBox imageData
  exact
    P.coverIndexLocalBoundaryTerm_eq_targetSetIntegral_of_orientedCOV
      (ω := ω) targetChart targetLower targetUpper
      sourceSelfSelectedBox selectedBox
      (fun i => D.orientedChangeOfVariablesOfOrientedManifold i)
      j

end SupportControlledSelectedPartition

namespace CoverIndexedResolvedBoundaryFields

variable (P : SupportControlledSelectedPartition C)

/--
Build resolved cover-indexed boundary measure fields once oriented COV supplies
the target set-integral representative of each local boundary term.

Interior cover indices are handled internally by empty carriers and the zero
integrand.  The compactness/continuity/support hypotheses are only requested
for genuine boundary cover indices.
-/
def ofTargetCOVPieceSum
    [IsManifold I 1 M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, boundaryIntegrand y ∂(volume : Measure (Fin n → Real)))
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
          (targetLower i) (targetUpper i))
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        fun y => ∑ j : C.CoverIndex,
          P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y) :
    CoverIndexedResolvedBoundaryFields
      (C := C) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) P :=
  CoverIndexedResolvedBoundaryFields.ofPieceSum
    (C := C) (ω := ω)
    (αBoundary := Fin n → Real)
    (μBoundary := (volume : Measure (Fin n → Real)))
    P boundaryIntegrand
    (P.coverIndexBoundaryTargetPieceSet targetLower targetUpper)
    (P.coverIndexBoundaryTargetPieceIntegrand targetChart ω)
    globalBoundaryIntegral globalBoundaryIntegral_eq_integral
    (by
      intro j
      rcases j with i | i
      · simp [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet]
      · exact boundaryPiece_isCompact i)
    (by
      intro j
      rcases j with i | i
      · simp [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet,
          SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceIntegrand]
      · exact boundaryPiece_continuousOn i)
    (by
      intro j
      rcases j with i | i
      · simp [SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceSet,
          SupportControlledSelectedPartition.coverIndexBoundaryTargetPieceIntegrand]
      · exact boundaryPiece_tsupport_subset i)
    (by
      intro j
      exact
        P.coverIndexLocalBoundaryTerm_eq_targetSetIntegral_of_orientedCOV
          (ω := ω) targetChart targetLower targetUpper
          sourceSelfSelectedBox sourceTargetSelectedBox hcov j)
    boundaryIntegrand_ae_eq_pieceSum

/-- Oriented-atlas version of `ofTargetCOVPieceSum`. -/
def ofTargetOrientedAtlasPieceSum
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (selectedBox :
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
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (boundaryIntegrand : (Fin n → Real) → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, boundaryIntegrand y ∂(volume : Measure (Fin n → Real)))
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
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        fun y => ∑ j : C.CoverIndex,
          P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y) :
    CoverIndexedResolvedBoundaryFields
      (C := C) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) P := by
  let D :=
    P.coverIndexBoundaryChartOrientationInput
      (ω := ω) targetChart targetLower targetUpper selectedBox imageData
  exact
    ofTargetCOVPieceSum
      (C := C) (ω := ω) P targetChart targetLower targetUpper
      boundaryIntegrand globalBoundaryIntegral globalBoundaryIntegral_eq_integral
      boundaryPiece_isCompact boundaryPiece_continuousOn
      boundaryPiece_tsupport_subset
      sourceSelfSelectedBox selectedBox
      (fun i => D.orientedChangeOfVariablesOfOrientedAtlas A hsource htarget i)
      boundaryIntegrand_ae_eq_pieceSum

/-- Oriented-manifold version of `ofTargetCOVPieceSum`. -/
def ofTargetOrientedManifoldPieceSum
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (selectedBox :
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
    (sourceSelfSelectedBox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I
          (C.boundaryChart i.1) (C.boundaryChart i.1)
          (P.coverIndexLocalizedForm ω (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (boundaryIntegrand : (Fin n → Real) → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral =
        ∫ y, boundaryIntegrand y ∂(volume : Measure (Fin n → Real)))
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
    (boundaryIntegrand_ae_eq_pieceSum :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        fun y => ∑ j : C.CoverIndex,
          P.coverIndexBoundaryTargetPieceIntegrand targetChart ω j y) :
    CoverIndexedResolvedBoundaryFields
      (C := C) (ω := ω)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) P := by
  let D :=
    P.coverIndexBoundaryChartOrientationInput
      (ω := ω) targetChart targetLower targetUpper selectedBox imageData
  exact
    ofTargetCOVPieceSum
      (C := C) (ω := ω) P targetChart targetLower targetUpper
      boundaryIntegrand globalBoundaryIntegral globalBoundaryIntegral_eq_integral
      boundaryPiece_isCompact boundaryPiece_continuousOn
      boundaryPiece_tsupport_subset
      sourceSelfSelectedBox selectedBox
      (fun i => D.orientedChangeOfVariablesOfOrientedManifold i)
      boundaryIntegrand_ae_eq_pieceSum

end CoverIndexedResolvedBoundaryFields

end CoverIndexedBoundarySetIntegral

end Stokes

end
