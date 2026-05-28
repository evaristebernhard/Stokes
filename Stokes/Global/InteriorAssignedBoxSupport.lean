import Stokes.Global.FiniteBoxCoverPartition
import Stokes.Global.FiniteBoxCoverInteriorLocalStokes
import Stokes.Global.ArtificialSupportZeroAutoM8

/-!
# Interior assigned-box support

This file is the interior `Wave 2B / L2` bridge.  It does not construct a
partition subordinate to a finite box cover.  Instead, it consumes the honest
L1-style support-control hypotheses and pushes them through the existing
interior local Stokes and M8 artificial-face pipelines.

The mathematical shape is:

* if the base chart representative is supported in a coordinate control set,
  and the partition coefficient is supported in the assigned interior box on
  that control set, then the localized chart representative is supported in
  the assigned box;
* this strict assigned-box support makes the corresponding project-local
  interior boundary term and, with local Stokes data, the bulk term vanish;
* with the usual localized-piece chart alignment, the same hypotheses construct
  the M8 artificial-face fields.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section InteriorAssignedBoxSupport

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

namespace SelectedBoxPartitionOfUnity

variable (P : SelectedBoxPartitionOfUnity I omega)

/--
Assigned-box support from an L1-style coefficient support condition.  This is
just the selected-partition shape of the finite-box-cover support theorem.
-/
theorem localized_tsupport_subset_assignedInteriorBox_of_coordSupport
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    {lower upper : M -> Fin (n + 1) -> Real}
    (hbase :
      forall i, i ∈ P.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I i i omega) ⊆
          coordSupport i)
    (hcoeff :
      forall i, i ∈ P.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I i i
              (P.partition i)) ∩ coordSupport i ⊆
          boxInteriorSupportBox (lower i) (upper i))
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) omega)) ⊆
      boxInteriorSupportBox (lower i) (upper i) :=
  P.localized_transitionPullback_tsupport_subset_interiorBox_of_coordSupport
    (ω := omega) (coordSupport := coordSupport)
    (lower := lower) (upper := upper) hbase hcoeff hi

/-- Assigned-box support using the selected boxes already stored in `P`. -/
theorem localized_tsupport_subset_selectedInteriorBox_of_coordSupport
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall i, i ∈ P.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I i i omega) ⊆
          coordSupport i)
    (hcoeff :
      forall i, i ∈ P.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I i i
              (P.partition i)) ∩ coordSupport i ⊆
          boxInteriorSupportBox (P.lower i) (P.upper i))
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) omega)) ⊆
      boxInteriorSupportBox (P.lower i) (P.upper i) :=
  P.localized_tsupport_subset_assignedInteriorBox_of_coordSupport
    (omega := omega) (coordSupport := coordSupport)
    (lower := P.lower) (upper := P.upper) hbase hcoeff hi

/--
The selected-box localized project-local artificial boundary term vanishes
under the assigned-box support hypotheses.
-/
theorem localized_projectInteriorBoundaryIntegral_eq_zero_of_assignedBox
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall i, i ∈ P.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I i i omega) ⊆
          coordSupport i)
    (hcoeff :
      forall i, i ∈ P.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I i i
              (P.partition i)) ∩ coordSupport i ⊆
          boxInteriorSupportBox (P.lower i) (P.upper i))
    {i : M} (hi : i ∈ P.active) :
    projectInteriorBoundaryIntegral I i i
        (ManifoldForm.localizedForm I (P.partition i) omega)
        (P.lower i) (P.upper i) = 0 :=
  ManifoldForm.localized_projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
      (I := I) (ω := omega) (ρ := P.partition i)
      (x0 := i) (x1 := i) (a := P.lower i) (b := P.upper i)
      (P.localized_tsupport_subset_selectedInteriorBox_of_coordSupport
        (omega := omega) hbase hcoeff hi)

/--
The selected-box localized project-local bulk term vanishes once the local
interior Stokes box is available.
-/
theorem localized_projectInteriorBulkIntegral_eq_zero_of_assignedBox
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbox :
      forall i, i ∈ P.active ->
        interiorChartExtendedBox I i i
          (ManifoldForm.localizedForm I (P.partition i) omega)
          (P.lower i) (P.upper i))
    (hbase :
      forall i, i ∈ P.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I i i omega) ⊆
          coordSupport i)
    (hcoeff :
      forall i, i ∈ P.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I i i
              (P.partition i)) ∩ coordSupport i ⊆
          boxInteriorSupportBox (P.lower i) (P.upper i))
    {i : M} (hi : i ∈ P.active) :
    projectInteriorBulkIntegral I i i
        (ManifoldForm.localizedForm I (P.partition i) omega)
        (P.lower i) (P.upper i) = 0 :=
  ManifoldForm.localized_projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox
      (I := I) (ω := omega) (ρ := P.partition i)
      (x0 := i) (x1 := i) (a := P.lower i) (b := P.upper i)
      (hbox i hi)
      (P.localized_tsupport_subset_selectedInteriorBox_of_coordSupport
        (omega := omega) hbase hcoeff hi)

end SelectedBoxPartitionOfUnity

namespace M8MeasureLocalizationData

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable (D : M8MeasureLocalizationData I omega selectedPartition targetImages)

/--
Assigned-box support in the exact selected-partition coordinates consumed by
`M8MeasureLocalizationData.interiorBoundaryTerm_eq_zero_of_selected...`.
-/
theorem selected_tsupport_subset_assignedInteriorBoxes_of_coordSupport
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall x, x ∈ selectedPartition.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (hcoeff :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (selectedPartition.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox
            (D.localizedInterior.piece x).lowerCorner
            (D.localizedInterior.piece x).upperCorner)
    (x : M) (hx : x ∈ selectedPartition.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I
            (selectedPartition.partition x) omega)) ⊆
      boxInteriorSupportBox
        (D.localizedInterior.piece x).lowerCorner
        (D.localizedInterior.piece x).upperCorner :=
  selectedPartition
    |>.localized_tsupport_subset_assignedInteriorBox_of_coordSupport
      (omega := omega) (coordSupport := coordSupport)
      (lower := fun x => (D.localizedInterior.piece x).lowerCorner)
      (upper := fun x => (D.localizedInterior.piece x).upperCorner)
      hbase hcoeff hx

/--
The L1-style coefficient support hypotheses make every active M8 interior
artificial boundary term vanish, after the localized-piece chart labels are
aligned with the selected chart labels.
-/
theorem interiorBoundaryTerm_eq_zero_of_assignedInteriorBoxes
    (A : LocalizedInteriorPieceAlignment selectedPartition targetImages D)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall x, x ∈ selectedPartition.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (hcoeff :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (selectedPartition.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox
            (D.localizedInterior.piece x).lowerCorner
            (D.localizedInterior.piece x).upperCorner) :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ ({()} : Finset Unit) ->
        D.interiorBoundaryTerm x q = 0 :=
  D.interiorBoundaryTerm_eq_zero_of_selected_tsupport_subset_interiorBox
    A
    (D.selected_tsupport_subset_assignedInteriorBoxes_of_coordSupport
      (coordSupport := coordSupport) hbase hcoeff)

end M8MeasureLocalizationData

namespace M8ArtificialFaceFields

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/--
Construct the M8 artificial-face package directly from L1-style
support-controlled assigned interior boxes.
-/
def ofAssignedInteriorBoxSupport
    (A :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall x, x ∈ selectedPartition.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (hcoeff :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (selectedPartition.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  ofSelectedLocalizedInteriorSupportZero
    (BoundaryPiece := BoundaryPiece)
    (measureLocalization := measureLocalization)
    A
    (measureLocalization
      |>.selected_tsupport_subset_assignedInteriorBoxes_of_coordSupport
        (coordSupport := coordSupport) hbase hcoeff)

@[simp]
theorem ofAssignedInteriorBoxSupport_eq_ofBoundaryTermZero
    (A :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall x, x ∈ selectedPartition.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (hcoeff :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (selectedPartition.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox
            (measureLocalization.localizedInterior.piece x).lowerCorner
            (measureLocalization.localizedInterior.piece x).upperCorner) :
    ofAssignedInteriorBoxSupport
        (BoundaryPiece := BoundaryPiece)
        (measureLocalization := measureLocalization)
        A hbase hcoeff =
      M8ArtificialFaceFields.ofBoundaryTermZero
        (BoundaryPiece := BoundaryPiece)
        (selectedPartition := selectedPartition)
        (targetImages := targetImages)
        (measureLocalization := measureLocalization)
        (measureLocalization
          |>.interiorBoundaryTerm_eq_zero_of_assignedInteriorBoxes
            A hbase hcoeff) := by
  rfl

end M8ArtificialFaceFields

end InteriorAssignedBoxSupport

end Stokes

end
