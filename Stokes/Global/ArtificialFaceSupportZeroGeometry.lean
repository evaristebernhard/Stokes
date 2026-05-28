import Stokes.Global.InteriorBoundarySupportZero
import Stokes.Global.ArtificialFaceSupportZeroToM8

/-!
# Selected support-zero geometry for M8 artificial faces

This file connects the strict-interior support lemmas from
`InteriorBoundarySupportZero` with the M8-facing artificial-face package from
`ArtificialFaceSupportZeroToM8`.

The genuine geometric input is still explicit: for every active selected chart
box, the localized chart representative must have topological support contained
in the strict interior support box.  From that input, this file proves the
localized artificial boundary term is zero and packages the result as the
`M8ArtificialFaceFields` required by the M8 statements.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFaceSupportZeroGeometry

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Selected-partition support-zero geometry for the M8 artificial-face fields.

The localized interior family is the one already recorded by the M8
measure-localization package.  The only non-bookkeeping field says that every
active localized chart representative is supported strictly inside its selected
auxiliary coordinate box.
-/
structure SelectedPartitionSupportZeroGeometry {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /--
  Strict support containment for every active localized interior piece.

  This is the real geometric obligation left to the chart-box selection layer.
  -/
  support_subset_interiorBox :
    forall x, x ∈ selectedPartition.active ->
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (measureLocalization.localizedInterior.piece x).sourceChart
            (measureLocalization.localizedInterior.piece x).targetChart
            (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
        boxInteriorSupportBox
          (measureLocalization.localizedInterior.piece x).lowerCorner
          (measureLocalization.localizedInterior.piece x).upperCorner

namespace SelectedPartitionSupportZeroGeometry

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
The localized artificial boundary term attached to an active selected chart is
zero under strict interior support.
-/
theorem localizedArtificialBoundaryTerm_eq_zero
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization)
    {x : M} (hx : x ∈ selectedPartition.active) :
    measureLocalization.localizedInterior.artificialBoundaryTerm x = 0 := by
  let P := measureLocalization.localizedInterior.piece x
  have hzero :
      projectInteriorBoundaryIntegral I P.sourceChart P.targetChart
          P.localizedForm P.lowerCorner P.upperCorner = 0 :=
    projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
      I P.sourceChart P.targetChart P.localizedForm P.lowerCorner P.upperCorner
      (D.support_subset_interiorBox x hx)
  simpa [LocalizedInteriorPieces.artificialBoundaryTerm, P] using hzero

/--
The M8 singleton artificial-boundary term is zero on active selected charts.
-/
theorem interiorBoundaryTerm_eq_zero
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ ({()} : Finset Unit) ->
        measureLocalization.interiorBoundaryTerm x q = 0 := by
  intro x hx q _hq
  cases q
  simpa [M8MeasureLocalizationData.interiorBoundaryTerm] using
    D.localizedArtificialBoundaryTerm_eq_zero hx

/--
Resolved artificial-face data obtained by killing every active singleton
interior boundary term via strict support.
-/
def toArtificialFaceResolvedData
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    ArtificialFaceResolvedData M Unit :=
  ArtificialFaceResolvedData.of_forall_eq_zero selectedPartition.active
    (fun _ : M => ({()} : Finset Unit))
    measureLocalization.interiorBoundaryTerm D.interiorBoundaryTerm_eq_zero

@[simp]
theorem toArtificialFaceResolvedData_activeCharts
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    D.toArtificialFaceResolvedData.activeCharts = selectedPartition.active := by
  rfl

@[simp]
theorem toArtificialFaceResolvedData_interiorPieces
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    D.toArtificialFaceResolvedData.interiorPieces =
      fun _ : M => ({()} : Finset Unit) := by
  rfl

@[simp]
theorem toArtificialFaceResolvedData_interiorBoundaryTerm
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    D.toArtificialFaceResolvedData.interiorBoundaryTerm =
      measureLocalization.interiorBoundaryTerm := by
  rfl

/--
Convert selected support-zero geometry directly to the M8 artificial-face field
package.
-/
def toM8ArtificialFaceFields
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  M8ArtificialFaceFields.ofResolved D.toArtificialFaceResolvedData
    D.toArtificialFaceResolvedData_activeCharts
    D.toArtificialFaceResolvedData_interiorPieces
    D.toArtificialFaceResolvedData_interiorBoundaryTerm

@[simp]
theorem toM8ArtificialFaceFields_artificialFaces
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces =
      D.toArtificialFaceResolvedData := by
  rfl

@[simp]
theorem toM8ArtificialFaceFields_active
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.activeCharts =
      selectedPartition.active :=
  D.toM8ArtificialFaceFields.artificialFaces_active

@[simp]
theorem toM8ArtificialFaceFields_pieces
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.interiorPieces =
      fun _ : M => ({()} : Finset Unit) :=
  D.toM8ArtificialFaceFields.artificialFaces_pieces

@[simp]
theorem toM8ArtificialFaceFields_term
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.interiorBoundaryTerm =
      measureLocalization.interiorBoundaryTerm :=
  D.toM8ArtificialFaceFields.artificialFaces_term

/--
Compact-support-facing artificial-face resolved package obtained from selected
support-zero geometry.
-/
def toCompactSupportArtificialFaceResolvedData
    {measureResolved :
      M8CompactSupportMeasureResolvedData I omega selectedPartition targetImages}
    (D :
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureResolved.measureLocalization) :
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
      SelectedPartitionSupportZeroGeometry I omega selectedPartition
        targetImages measureResolved.measureLocalization) :
    D.toCompactSupportArtificialFaceResolvedData.artificialFaces =
      D.toM8ArtificialFaceFields.artificialFaces :=
  rfl

end SelectedPartitionSupportZeroGeometry

namespace M8ArtificialFaceFields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
Selected-partition-facing constructor for M8 artificial-face fields from
strict support of each localized interior piece.
-/
def ofSelectedPartitionSupportZeroGeometry
    (support_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (measureLocalization.localizedInterior.piece x).sourceChart
              (measureLocalization.localizedInterior.piece x).targetChart
              (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  (SelectedPartitionSupportZeroGeometry.mk support_subset_interiorBox)
    |>.toM8ArtificialFaceFields

@[simp]
theorem ofSelectedPartitionSupportZeroGeometry_active
    (support_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (measureLocalization.localizedInterior.piece x).sourceChart
              (measureLocalization.localizedInterior.piece x).targetChart
              (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    (ofSelectedPartitionSupportZeroGeometry (BoundaryPiece := BoundaryPiece)
      (selectedPartition := selectedPartition) (targetImages := targetImages)
      (measureLocalization := measureLocalization)
      support_subset_interiorBox).artificialFaces.activeCharts =
        selectedPartition.active :=
  (SelectedPartitionSupportZeroGeometry.toM8ArtificialFaceFields_active
    (SelectedPartitionSupportZeroGeometry.mk support_subset_interiorBox))

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
Compact-support-facing constructor from strict support of each localized
interior piece.
-/
def ofSelectedPartitionSupportZeroGeometry
    (support_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (measureResolved.measureLocalization.localizedInterior.piece x).sourceChart
              (measureResolved.measureLocalization.localizedInterior.piece x).targetChart
              (measureResolved.measureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (measureResolved.measureLocalization.localizedInterior.piece x).lowerCorner
            (measureResolved.measureLocalization.localizedInterior.piece x).upperCorner) :
    M8CompactSupportArtificialFaceResolvedData I omega selectedPartition
      targetImages measureResolved :=
  (SelectedPartitionSupportZeroGeometry.mk support_subset_interiorBox)
    |>.toCompactSupportArtificialFaceResolvedData

@[simp]
theorem ofSelectedPartitionSupportZeroGeometry_active
    (support_subset_interiorBox :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (measureResolved.measureLocalization.localizedInterior.piece x).sourceChart
              (measureResolved.measureLocalization.localizedInterior.piece x).targetChart
              (measureResolved.measureLocalization.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (measureResolved.measureLocalization.localizedInterior.piece x).lowerCorner
            (measureResolved.measureLocalization.localizedInterior.piece x).upperCorner) :
    (ofSelectedPartitionSupportZeroGeometry (BoundaryPiece := BoundaryPiece)
      (measureResolved := measureResolved)
      support_subset_interiorBox).artificialFaces.activeCharts =
        selectedPartition.active :=
  (SelectedPartitionSupportZeroGeometry.toM8ArtificialFaceFields_active
    (SelectedPartitionSupportZeroGeometry.mk support_subset_interiorBox))

end M8CompactSupportArtificialFaceResolvedData

end ArtificialFaceSupportZeroGeometry

end Stokes

end
