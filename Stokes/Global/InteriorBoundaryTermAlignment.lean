import Stokes.Global.ArtificialFaceSupportZeroToM8
import Stokes.Global.LocalizedInteriorConstructors

/-!
# Interior boundary-term alignment

This file records the narrow projection equalities connecting the M8
measure-localization interior boundary term with the local Stokes data stored in
the selected localized-interior package.  The point is to make the
support-zero route feed `M8ArtificialFaceFields.ofBoundaryTermZero` without a
separate manual term-alignment field.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section InteriorBoundaryTermAlignment

universe u w b c

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ι : Type c}

namespace LocalizedInteriorPieces

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {ω : ManifoldForm I M n}

/--
The artificial boundary term stored in the localized family is exactly the
artificial boundary term of the derived local Stokes package for that piece.
-/
@[simp]
theorem localStokesData_artificialBoundaryTerm
    (D : LocalizedInteriorPieces (ι := ι) I ω) (i : ι) :
    (D.localStokesData i).artificialBoundaryTerm =
      D.artificialBoundaryTerm i := by
  rfl

end LocalizedInteriorPieces

namespace LocalizedInteriorM8Fields

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {ω : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I ω}

/--
Singleton M8 interior boundary terms are the local Stokes artificial boundary
terms of the selected localized pieces.
-/
theorem interiorBoundaryTerm_eq_localStokesData_artificialBoundaryTerm
    (D : LocalizedInteriorM8Fields I ω P) (x : M) (q : Unit) :
    D.interiorBoundaryTerm x q =
      (D.localizedInterior.localStokesData x).artificialBoundaryTerm := by
  cases q
  simp [LocalizedInteriorM8Fields.interiorBoundaryTerm]

end LocalizedInteriorM8Fields

namespace M8MeasureLocalizationData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/-- The M8 measure-localization interior boundary term unfolds to the localized family. -/
@[simp]
theorem interiorBoundaryTerm_eq_localizedArtificialBoundaryTerm
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (x : M) (q : Unit) :
    D.interiorBoundaryTerm x q =
      D.localizedInterior.artificialBoundaryTerm x := by
  cases q
  rfl

/--
The exact field-alignment lemma: the M8 interior boundary term is the
artificial boundary term of the derived local Stokes package for the selected
localized piece.
-/
theorem interiorBoundaryTerm_eq_localStokesData_artificialBoundaryTerm
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (x : M) (q : Unit) :
    D.interiorBoundaryTerm x q =
      (D.localizedInterior.localStokesData x).artificialBoundaryTerm := by
  cases q
  simp [M8MeasureLocalizationData.interiorBoundaryTerm]

/--
Support-zero vanishing in the exact shape consumed by
`M8ArtificialFaceFields.ofBoundaryTermZero`, using the localized local Stokes
data already stored in the M8 measure-localization package.
-/
theorem interiorBoundaryTerm_eq_zero_of_localized_tsupport_subset_interiorBox
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (hsupp :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (D.localizedInterior.localStokesData x).sourceChart
              (D.localizedInterior.localStokesData x).targetChart
              (D.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (D.localizedInterior.localStokesData x).lowerCorner
            (D.localizedInterior.localStokesData x).upperCorner) :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ ({()} : Finset Unit) ->
        D.interiorBoundaryTerm x q = 0 := by
  intro x hx q _hq
  calc
    D.interiorBoundaryTerm x q =
        (D.localizedInterior.localStokesData x).artificialBoundaryTerm :=
      D.interiorBoundaryTerm_eq_localStokesData_artificialBoundaryTerm x q
    _ = 0 :=
      (D.localizedInterior.localStokesData x)
        |>.artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
        (hsupp x hx)

/--
Constructor-level bridge from localized support-zero data to the M8
artificial-face fields.  This is just `ofBoundaryTermZero` fed by the preceding
alignment theorem; it introduces no new data field.
-/
def artificialFaceFieldsOfLocalizedSupportZero
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (hsupp :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (D.localizedInterior.localStokesData x).sourceChart
              (D.localizedInterior.localStokesData x).targetChart
              (D.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (D.localizedInterior.localStokesData x).lowerCorner
            (D.localizedInterior.localStokesData x).upperCorner) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages D :=
  M8ArtificialFaceFields.ofBoundaryTermZero
    (D.interiorBoundaryTerm_eq_zero_of_localized_tsupport_subset_interiorBox
      hsupp)

@[simp]
theorem artificialFaceFieldsOfLocalizedSupportZero_eq_ofBoundaryTermZero
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages)
    (hsupp :
      forall x, x ∈ selectedPartition.active ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (D.localizedInterior.localStokesData x).sourceChart
              (D.localizedInterior.localStokesData x).targetChart
              (D.localizedInterior.piece x).localizedForm) ⊆
          boxInteriorSupportBox
            (D.localizedInterior.localStokesData x).lowerCorner
            (D.localizedInterior.localStokesData x).upperCorner) :
    D.artificialFaceFieldsOfLocalizedSupportZero
        (BoundaryPiece := BoundaryPiece) hsupp =
      M8ArtificialFaceFields.ofBoundaryTermZero
        (BoundaryPiece := BoundaryPiece)
        (selectedPartition := selectedPartition) (targetImages := targetImages)
        (measureLocalization := D)
        (D.interiorBoundaryTerm_eq_zero_of_localized_tsupport_subset_interiorBox
          hsupp) :=
  rfl

end M8MeasureLocalizationData

end InteriorBoundaryTermAlignment

end Stokes

end
