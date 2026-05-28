import Stokes.Global.ArtificialFaceSupportZeroToM8
import Stokes.Global.LocalizedInteriorPieceAlignment

/-!
# Automatic support-zero artificial faces for M8

This file is the support-zero route in the shape needed by the compact-support
globalization proof.  Instead of asking for a separate family of
`InteriorLocalStokesData`, it reads the localized interior pieces already stored
in `M8MeasureLocalizationData`.

The mathematical input is the strict interior-box support condition for each
active localized chart representative.  With the usual chart-label alignment,
this can be stated in the natural selected-partition coordinates
`x/x, localizedForm (partition x) omega`.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialSupportZeroAutoM8

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

namespace M8MeasureLocalizationData

/-- The M8 singleton interior boundary term is definitionally the localized piece term. -/
@[simp]
theorem interiorBoundaryTerm_unit_eq_localizedInterior_artificialBoundaryTerm
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (x : M) (q : Unit) :
    D.interiorBoundaryTerm x q = D.localizedInterior.artificialBoundaryTerm x := by
  cases q
  rfl

/--
The M8 singleton interior boundary term is the project-local artificial
coordinate-box boundary integral of the stored localized piece.
-/
theorem interiorBoundaryTerm_eq_projectInteriorBoundaryIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (x : M) (q : Unit) :
    D.interiorBoundaryTerm x q =
      projectInteriorBoundaryIntegral I
        (D.localizedInterior.piece x).sourceChart
        (D.localizedInterior.piece x).targetChart
        (D.localizedInterior.piece x).localizedForm
        (D.localizedInterior.piece x).lowerCorner
        (D.localizedInterior.piece x).upperCorner := by
  cases q
  rfl

/--
Strict support inside the stored localized box makes every active M8 interior
artificial-boundary term vanish.
-/
theorem interiorBoundaryTerm_eq_zero_of_localized_tsupport_subset_interiorBox
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (hsupp :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (D.localizedInterior.piece x).sourceChart
              (D.localizedInterior.piece x).targetChart
              (D.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (D.localizedInterior.piece x).lowerCorner
            (D.localizedInterior.piece x).upperCorner) :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ ({()} : Finset Unit) ->
        D.interiorBoundaryTerm x q = 0 := by
  intro x hx q _hq
  calc
    D.interiorBoundaryTerm x q =
        projectInteriorBoundaryIntegral I
          (D.localizedInterior.piece x).sourceChart
          (D.localizedInterior.piece x).targetChart
          (D.localizedInterior.piece x).localizedForm
          (D.localizedInterior.piece x).lowerCorner
          (D.localizedInterior.piece x).upperCorner :=
      D.interiorBoundaryTerm_eq_projectInteriorBoundaryIntegral x q
    _ = 0 :=
      projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
        I
        (D.localizedInterior.piece x).sourceChart
        (D.localizedInterior.piece x).targetChart
        (D.localizedInterior.piece x).localizedForm
        (D.localizedInterior.piece x).lowerCorner
        (D.localizedInterior.piece x).upperCorner
        (hsupp x hx)

/--
Transport the natural selected-partition support hypothesis to the stored
localized-piece chart coordinates.
-/
theorem localized_tsupport_subset_interiorBox_of_selected
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (A : LocalizedInteriorPieceAlignment selectedPartition targetImages D)
    (hsupp :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I x x
              (ManifoldForm.localizedForm I (selectedPartition.partition x) omega)) ⊆
          boxInteriorSupportBox
            (D.localizedInterior.piece x).lowerCorner
            (D.localizedInterior.piece x).upperCorner) :
    forall x, x ∈ selectedPartition.active ->
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (D.localizedInterior.piece x).sourceChart
            (D.localizedInterior.piece x).targetChart
            (D.localizedInterior.piece x).localizedForm) ⊆
        boxInteriorSupportBox
          (D.localizedInterior.piece x).lowerCorner
          (D.localizedInterior.piece x).upperCorner := by
  intro x hx
  rw [A.piece_transitionPullback_eq x hx]
  exact hsupp x hx

/--
The natural selected-partition support hypothesis, plus chart-label alignment,
makes every active M8 interior artificial-boundary term vanish.
-/
theorem interiorBoundaryTerm_eq_zero_of_selected_tsupport_subset_interiorBox
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (A : LocalizedInteriorPieceAlignment selectedPartition targetImages D)
    (hsupp :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I x x
              (ManifoldForm.localizedForm I (selectedPartition.partition x) omega)) ⊆
          boxInteriorSupportBox
            (D.localizedInterior.piece x).lowerCorner
            (D.localizedInterior.piece x).upperCorner) :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ ({()} : Finset Unit) ->
        D.interiorBoundaryTerm x q = 0 :=
  D.interiorBoundaryTerm_eq_zero_of_localized_tsupport_subset_interiorBox
    (D.localized_tsupport_subset_interiorBox_of_selected A hsupp)

end M8MeasureLocalizationData

namespace M8ArtificialFaceFields

/--
Construct the M8 artificial-face package directly from support-zero of the
localized interior pieces stored in `M8MeasureLocalizationData`.
-/
def ofLocalizedInteriorSupportZero
    (hsupp :
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
  M8ArtificialFaceFields.ofBoundaryTermZero
    (measureLocalization
      |>.interiorBoundaryTerm_eq_zero_of_localized_tsupport_subset_interiorBox
        hsupp)

/--
Construct the M8 artificial-face package from the natural selected-partition
localized chart support condition.
-/
def ofSelectedLocalizedInteriorSupportZero
    (A :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    (hsupp :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I x x
              (ManifoldForm.localizedForm I (selectedPartition.partition x) omega)) ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  M8ArtificialFaceFields.ofBoundaryTermZero
    (measureLocalization
      |>.interiorBoundaryTerm_eq_zero_of_selected_tsupport_subset_interiorBox
        A hsupp)

@[simp]
theorem ofSelectedLocalizedInteriorSupportZero_eq_ofBoundaryTermZero
    (A :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    (hsupp :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I x x
              (ManifoldForm.localizedForm I (selectedPartition.partition x) omega)) ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    ofSelectedLocalizedInteriorSupportZero
        (BoundaryPiece := BoundaryPiece)
        (measureLocalization := measureLocalization) A hsupp =
      M8ArtificialFaceFields.ofBoundaryTermZero
        (BoundaryPiece := BoundaryPiece)
        (selectedPartition := selectedPartition)
        (targetImages := targetImages)
        (measureLocalization := measureLocalization)
        (measureLocalization
          |>.interiorBoundaryTerm_eq_zero_of_selected_tsupport_subset_interiorBox
            A hsupp) :=
  rfl

@[simp]
theorem ofSelectedLocalizedInteriorSupportZero_active
    (A :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    (hsupp :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I x x
              (ManifoldForm.localizedForm I (selectedPartition.partition x) omega)) ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    (ofSelectedLocalizedInteriorSupportZero
        (BoundaryPiece := BoundaryPiece)
        (measureLocalization := measureLocalization) A hsupp).artificialFaces.activeCharts =
      selectedPartition.active :=
  (ofSelectedLocalizedInteriorSupportZero
        (BoundaryPiece := BoundaryPiece)
        (measureLocalization := measureLocalization) A hsupp).artificialFaces_active

end M8ArtificialFaceFields

end ArtificialSupportZeroAutoM8

end Stokes

end
