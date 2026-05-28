import Stokes.Global.ArtificialFaceToM8
import Stokes.Global.M8CompactSupportStatement

/-!
# Support-zero artificial faces for M8

This file is a small M8-facing adapter for the support-zero route to artificial
face cancellation.  The geometric work is still explicit: one must supply, for
each selected interior chart box, local Stokes data whose transition-pullback
representative is supported in the strict interior of that box.  The adapter
then packages the resulting pointwise-zero artificial boundary terms as the
`M8ArtificialFaceFields` required by the M8 global statement.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFaceSupportZeroToM8

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Selected-interior support-zero data for the M8 artificial-face fields.

The selected partition has exactly one M8 interior piece over each active chart.
This package therefore records one `InteriorLocalStokesData` per chart label.
The real geometric obligation is the support containment field; the term
alignment field says that the M8 localized artificial-boundary term is the one
computed by the local Stokes data.
-/
structure M8ArtificialFaceSupportZeroData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /-- Local Stokes data for each selected interior chart box. -/
  localStokesData : M -> InteriorLocalStokesData I omega
  /--
  The chart representative of every active localized interior piece is strictly
  supported inside its auxiliary box.
  -/
  support_subset_interiorBox :
    forall x, x ∈ selectedPartition.active ->
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (localStokesData x).sourceChart
            (localStokesData x).targetChart omega) ⊆
        boxInteriorSupportBox
          (localStokesData x).lowerCorner
          (localStokesData x).upperCorner
  /--
  The M8 localized artificial-boundary term is the local artificial-boundary
  term supplied by the support-zero local Stokes data.
  -/
  interiorBoundaryTerm_eq :
    forall x, x ∈ selectedPartition.active ->
      measureLocalization.interiorBoundaryTerm x () =
        (localStokesData x).artificialBoundaryTerm

namespace M8ArtificialFaceSupportZeroData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/-- The singleton-piece version of the selected local Stokes data. -/
def localStokesDataOn
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureLocalization) :
    M -> Unit -> InteriorLocalStokesData I omega :=
  fun x _ => D.localStokesData x

@[simp]
theorem localStokesDataOn_unit
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureLocalization)
    (x : M) (q : Unit) :
    D.localStokesDataOn x q = D.localStokesData x := by
  cases q
  rfl

/--
Support containment in the singleton-piece shape expected by
`M8ArtificialFaceFields.ofInteriorSupportZeroBoundaryTerm`.
-/
theorem support_subset_interiorBox_unit
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureLocalization) :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ ({()} : Finset Unit) ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (D.localStokesDataOn x q).sourceChart
              (D.localStokesDataOn x q).targetChart omega) ⊆
          boxInteriorSupportBox
            (D.localStokesDataOn x q).lowerCorner
            (D.localStokesDataOn x q).upperCorner := by
  intro x hx q _hq
  cases q
  simpa [localStokesDataOn] using D.support_subset_interiorBox x hx

/--
Term alignment in the singleton-piece shape expected by
`M8ArtificialFaceFields.ofInteriorSupportZeroBoundaryTerm`.
-/
theorem interiorBoundaryTerm_eq_unit
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureLocalization) :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ ({()} : Finset Unit) ->
        measureLocalization.interiorBoundaryTerm x q =
          (D.localStokesDataOn x q).artificialBoundaryTerm := by
  intro x hx q _hq
  cases q
  simpa [localStokesDataOn] using D.interiorBoundaryTerm_eq x hx

/-- Pointwise vanishing of the M8 artificial-boundary term on active pieces. -/
theorem interiorBoundaryTerm_eq_zero
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureLocalization) :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ ({()} : Finset Unit) ->
        measureLocalization.interiorBoundaryTerm x q = 0 := by
  intro x hx q hq
  calc
    measureLocalization.interiorBoundaryTerm x q =
        (D.localStokesDataOn x q).artificialBoundaryTerm :=
      D.interiorBoundaryTerm_eq_unit x hx q hq
    _ = 0 :=
      (D.localStokesDataOn x q).artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
        (D.support_subset_interiorBox_unit x hx q hq)

/-- Convert selected support-zero data to the M8 artificial-face field package. -/
def toM8ArtificialFaceFields
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureLocalization) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  M8ArtificialFaceFields.ofBoundaryTermZero D.interiorBoundaryTerm_eq_zero

@[simp]
theorem toM8ArtificialFaceFields_eq_ofBoundaryTermZero
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureLocalization) :
    D.toM8ArtificialFaceFields =
      M8ArtificialFaceFields.ofBoundaryTermZero
        (BoundaryPiece := BoundaryPiece)
        (selectedPartition := selectedPartition) (targetImages := targetImages)
        (measureLocalization := measureLocalization)
        D.interiorBoundaryTerm_eq_zero :=
  rfl

@[simp]
theorem toM8ArtificialFaceFields_active
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.activeCharts =
      selectedPartition.active :=
  D.toM8ArtificialFaceFields.artificialFaces_active

@[simp]
theorem toM8ArtificialFaceFields_pieces
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.interiorPieces =
      fun _ : M => ({()} : Finset Unit) :=
  D.toM8ArtificialFaceFields.artificialFaces_pieces

@[simp]
theorem toM8ArtificialFaceFields_term
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.interiorBoundaryTerm =
      measureLocalization.interiorBoundaryTerm :=
  D.toM8ArtificialFaceFields.artificialFaces_term

/--
Support-zero data as the compact-support-facing artificial-face resolved input.

This is a convenience projection for `M8CompactSupportStokesInput`: the measure
package supplies the M8 measure-localization data, while this support-zero data
supplies the artificial-face package.
-/
def toCompactSupportArtificialFaceResolvedData
    {measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureResolved.measureLocalization) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  let A := D.toM8ArtificialFaceFields
  { artificialFaces := A.artificialFaces
    artificialFaces_active := A.artificialFaces_active
    artificialFaces_pieces := A.artificialFaces_pieces
    artificialFaces_term := A.artificialFaces_term }

@[simp]
theorem toCompactSupportArtificialFaceResolvedData_artificialFaces
    {measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}
    (D :
      M8ArtificialFaceSupportZeroData I omega selectedPartition targetImages
        measureResolved.measureLocalization) :
    D.toCompactSupportArtificialFaceResolvedData.artificialFaces =
      D.toM8ArtificialFaceFields.artificialFaces :=
  rfl

end M8ArtificialFaceSupportZeroData

namespace M8ArtificialFaceFields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
Direct constructor for M8 artificial-face fields from selected support-zero
local Stokes data.
-/
def ofSelectedInteriorSupportZero
    (localStokesData : M -> InteriorLocalStokesData I omega)
    (support_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (localStokesData x).sourceChart
              (localStokesData x).targetChart omega) ⊆
          boxInteriorSupportBox
            (localStokesData x).lowerCorner
            (localStokesData x).upperCorner)
    (interiorBoundaryTerm_eq :
      forall x, x ∈ selectedPartition.active ->
        measureLocalization.interiorBoundaryTerm x () =
          (localStokesData x).artificialBoundaryTerm) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  M8ArtificialFaceFields.ofBoundaryTermZero
    (by
      intro x hx q hq
      cases q
      exact (interiorBoundaryTerm_eq x hx).trans
        ((localStokesData x).artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
          (support_subset_interiorBox x hx)))

@[simp]
theorem ofSelectedInteriorSupportZero_eq_ofBoundaryTermZero
    (localStokesData : M -> InteriorLocalStokesData I omega)
    (support_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (localStokesData x).sourceChart
              (localStokesData x).targetChart omega) ⊆
          boxInteriorSupportBox
            (localStokesData x).lowerCorner
            (localStokesData x).upperCorner)
    (interiorBoundaryTerm_eq :
      forall x, x ∈ selectedPartition.active ->
        measureLocalization.interiorBoundaryTerm x () =
          (localStokesData x).artificialBoundaryTerm) :
    ofSelectedInteriorSupportZero (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      localStokesData support_subset_interiorBox interiorBoundaryTerm_eq =
      M8ArtificialFaceFields.ofBoundaryTermZero
        (BoundaryPiece := BoundaryPiece)
        (selectedPartition := selectedPartition) (targetImages := targetImages)
        (measureLocalization := measureLocalization)
        (by
          intro x hx q hq
          cases q
          exact (interiorBoundaryTerm_eq x hx).trans
            ((localStokesData x).artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
              (support_subset_interiorBox x hx))) :=
  rfl

@[simp]
theorem ofSelectedInteriorSupportZero_active
    (localStokesData : M -> InteriorLocalStokesData I omega)
    (support_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (localStokesData x).sourceChart
              (localStokesData x).targetChart omega) ⊆
          boxInteriorSupportBox
            (localStokesData x).lowerCorner
            (localStokesData x).upperCorner)
    (interiorBoundaryTerm_eq :
      forall x, x ∈ selectedPartition.active ->
        measureLocalization.interiorBoundaryTerm x () =
          (localStokesData x).artificialBoundaryTerm) :
    (ofSelectedInteriorSupportZero (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      localStokesData support_subset_interiorBox
      interiorBoundaryTerm_eq).artificialFaces.activeCharts =
        selectedPartition.active :=
  (M8ArtificialFaceSupportZeroData.toM8ArtificialFaceFields_active
    (M8ArtificialFaceSupportZeroData.mk localStokesData
      support_subset_interiorBox interiorBoundaryTerm_eq))

end M8ArtificialFaceFields

namespace M8CompactSupportArtificialFaceResolvedData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureResolved :
  M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}

/--
Compact-support-facing constructor for the artificial-face resolved package
from selected support-zero local Stokes data.
-/
def ofSelectedInteriorSupportZero
    (localStokesData : M -> InteriorLocalStokesData I omega)
    (support_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (localStokesData x).sourceChart
              (localStokesData x).targetChart omega) ⊆
          boxInteriorSupportBox
            (localStokesData x).lowerCorner
            (localStokesData x).upperCorner)
    (interiorBoundaryTerm_eq :
      forall x, x ∈ selectedPartition.active ->
        measureResolved.measureLocalization.interiorBoundaryTerm x () =
          (localStokesData x).artificialBoundaryTerm) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (M8ArtificialFaceSupportZeroData.mk localStokesData
    support_subset_interiorBox interiorBoundaryTerm_eq)
      |>.toCompactSupportArtificialFaceResolvedData

@[simp]
theorem ofSelectedInteriorSupportZero_active
    (localStokesData : M -> InteriorLocalStokesData I omega)
    (support_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (localStokesData x).sourceChart
              (localStokesData x).targetChart omega) ⊆
          boxInteriorSupportBox
            (localStokesData x).lowerCorner
            (localStokesData x).upperCorner)
    (interiorBoundaryTerm_eq :
      forall x, x ∈ selectedPartition.active ->
        measureResolved.measureLocalization.interiorBoundaryTerm x () =
          (localStokesData x).artificialBoundaryTerm) :
    (ofSelectedInteriorSupportZero (BoundaryPiece := BoundaryPiece)
      (measureResolved := measureResolved)
      localStokesData support_subset_interiorBox
      interiorBoundaryTerm_eq).artificialFaces.activeCharts =
        selectedPartition.active :=
  (M8ArtificialFaceSupportZeroData.toM8ArtificialFaceFields_active
    (M8ArtificialFaceSupportZeroData.mk localStokesData
      support_subset_interiorBox interiorBoundaryTerm_eq))

end M8CompactSupportArtificialFaceResolvedData

end ArtificialFaceSupportZeroToM8

end Stokes

end
