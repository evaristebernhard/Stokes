import Stokes.Global.CompactSupportBoxBufferBuilder

/-!
# Strict compact-support buffers from inner boxes

This file proves the small but useful geometric step between the current closed
box support API and the artificial-face support-zero API.

The existing compact-support chart-box layer often gives support in an inner
closed box `Set.Icc c d`.  If that inner closed box sits strictly inside the
selected outer box `boxInteriorSupportBox a b`, then the support-zero route can
consume it as a `CompactSupportBoxBuffer`.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section StrictInteriorBoxes

/--
A closed coordinate box is contained in the strict interior of a larger box
when each lower and upper coordinate has a strict margin.
-/
theorem Icc_subset_boxInteriorSupportBox {n : Nat}
    {a b c d : Fin (n + 1) → Real}
    (hleft : ∀ i : Fin (n + 1), a i < c i)
    (hright : ∀ i : Fin (n + 1), d i < b i) :
    Set.Icc c d ⊆ boxInteriorSupportBox a b := by
  intro y hy i
  exact ⟨(hleft i).trans_le (hy.1 i), (hy.2 i).trans_lt (hright i)⟩

/--
If a function is supported in an inner closed box and that box has a strict
margin inside an outer box, then it is supported in the outer strict box.
-/
theorem tsupport_subset_boxInteriorSupportBox_of_subset_Icc {n : Nat}
    {β : Type*} [TopologicalSpace (Fin (n + 1) → Real)]
    [Zero β] {f : (Fin (n + 1) → Real) → β}
    {a b c d : Fin (n + 1) → Real}
    (hsupp : tsupport f ⊆ Set.Icc c d)
    (hleft : ∀ i : Fin (n + 1), a i < c i)
    (hright : ∀ i : Fin (n + 1), d i < b i) :
    tsupport f ⊆ boxInteriorSupportBox a b :=
  hsupp.trans (Icc_subset_boxInteriorSupportBox hleft hright)

end StrictInteriorBoxes

section CompactInteriorBoxExistence

/--
Every compact set in finite real coordinates fits in the strict interior of
some coordinate box.

This is the pure coordinate margin theorem.  Chart-domain containment of that
outer box is a separate local-geometry input, because an arbitrary chart domain
need not contain a single large rectangle around a disconnected compact set.
-/
theorem exists_boxInteriorSupportBox_subset_of_isCompact {n : Nat}
    {K : Set (Fin (n + 1) → Real)} (hK : IsCompact K) :
    ∃ a b : Fin (n + 1) → Real, a ≤ b ∧ K ⊆ boxInteriorSupportBox a b := by
  obtain ⟨R, _hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  let a : Fin (n + 1) → Real := fun _ => -(R + 1)
  let b : Fin (n + 1) → Real := fun _ => R + 1
  refine ⟨a, b, ?_, ?_⟩
  · intro i
    dsimp [a, b]
    linarith
  · intro x hx i
    have hxnorm : ‖x‖ ≤ R := hR x hx
    have hcoord_abs : |x i| ≤ R := by
      simpa [Real.norm_eq_abs] using
        (piReal_coord_norm_le_norm x i).trans hxnorm
    have hcoord_le : x i ≤ R := (le_abs_self (x i)).trans hcoord_abs
    have hcoord_ge : -R ≤ x i := (neg_le_neg hcoord_abs).trans (neg_abs_le (x i))
    constructor
    · dsimp [a]
      linarith
    · dsimp [b]
      linarith

end CompactInteriorBoxExistence

section LocalizedInteriorBuffers

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
Inner closed-box support data for the localized interior form representatives,
with a strict coordinate margin inside the selected outer boxes stored by the
M8 measure-localization package.
-/
structure LocalizedInteriorFormInnerBoxBuffer {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /-- Lower corners of the inner closed boxes. -/
  innerLower : M → Fin (n + 1) → Real
  /-- Upper corners of the inner closed boxes. -/
  innerUpper : M → Fin (n + 1) → Real
  /-- Localized form representative support lies in the inner closed box. -/
  localized_tsupport_subset_innerIcc :
    ∀ x, x ∈ selectedPartition.active →
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (measureLocalization.localizedInterior.piece x).sourceChart
            (measureLocalization.localizedInterior.piece x).targetChart
            (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
        Set.Icc (innerLower x) (innerUpper x)
  /-- The inner lower corner is strictly above the selected outer lower corner. -/
  lower_lt_innerLower :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      (measureLocalization.localizedInterior.piece x).lowerCorner j <
        innerLower x j
  /-- The inner upper corner is strictly below the selected outer upper corner. -/
  innerUpper_lt_upper :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      innerUpper x j <
        (measureLocalization.localizedInterior.piece x).upperCorner j

namespace LocalizedInteriorFormInnerBoxBuffer

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/-- The packaged inner-box data gives the strict localized-form support field. -/
theorem localized_tsupport_subset_interiorBox
    (D :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImages measureLocalization) :
    ∀ x, x ∈ selectedPartition.active →
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (measureLocalization.localizedInterior.piece x).sourceChart
            (measureLocalization.localizedInterior.piece x).targetChart
            (measureLocalization.localizedInterior.piece x).localizedForm) ⊆
        boxInteriorSupportBox
          (measureLocalization.localizedInterior.piece x).lowerCorner
          (measureLocalization.localizedInterior.piece x).upperCorner := by
  intro x hx
  exact tsupport_subset_boxInteriorSupportBox_of_subset_Icc
    (D.localized_tsupport_subset_innerIcc x hx)
    (D.lower_lt_innerLower x hx)
    (D.innerUpper_lt_upper x hx)

/--
Convert inner closed-box support for the localized form representatives into
the compact-support buffer consumed by the artificial-face support-zero route.
-/
def toCompactSupportBoxBuffer
    (D :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImages measureLocalization) :
    CompactSupportBoxBuffer I omega selectedPartition targetImages
      measureLocalization :=
  CompactSupportBoxBuffer.ofStrictSupportSubsetInteriorBox
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureLocalization := measureLocalization)
    D.localized_tsupport_subset_interiorBox

theorem toCompactSupportBoxBuffer_support
    (D :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImages measureLocalization) :
    D.toCompactSupportBoxBuffer.strictSupport_subset_interiorBox =
      D.localized_tsupport_subset_interiorBox :=
  rfl

/-- Direct M8 artificial-face fields from inner localized-form boxes. -/
def toM8ArtificialFaceFields
    (D :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImages measureLocalization) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  D.toCompactSupportBoxBuffer.toM8ArtificialFaceFields

@[simp]
theorem toM8ArtificialFaceFields_active
    (D :
      LocalizedInteriorFormInnerBoxBuffer I omega selectedPartition
        targetImages measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.activeCharts =
      selectedPartition.active :=
  D.toCompactSupportBoxBuffer.toM8ArtificialFaceFields_active

end LocalizedInteriorFormInnerBoxBuffer

namespace ManifoldForm

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {x0 x1 : M} {ρ : M → Real}
variable {a b c d : Fin (n + 1) → Real}

/--
Closed inner-box support for the transition coefficient, plus a strict margin
inside the selected outer box, gives strict support for the localized
transition-pullback representative.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coefficient_Icc
    (hρ :
      tsupport (transitionCoefficientInChart I x0 x1 ρ) ⊆ Set.Icc c d)
    (hleft : ∀ i : Fin (n + 1), a i < c i)
    (hright : ∀ i : Fin (n + 1), d i < b i) :
    tsupport
        (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      boxInteriorSupportBox a b :=
  transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coefficient
    (I := I) (ω := ω) (x0 := x0) (x1 := x1) (ρ := ρ) (a := a) (b := b)
    (tsupport_subset_boxInteriorSupportBox_of_subset_Icc hρ hleft hright)

end ManifoldForm

namespace LocalizedInteriorPiece

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {ρ : M → M → Real} {i : M}
variable {c d : Fin (n + 1) → Real}

/--
A localized interior piece has strict support in its selected outer box if its
transition coefficient is supported in an inner closed box with strict margins.
-/
theorem transitionPullback_tsupport_subset_interiorBox_of_coefficient_Icc
    (D : LocalizedInteriorPiece I ω ρ i)
    (hρ :
      tsupport
          (ManifoldForm.transitionCoefficientInChart I D.sourceChart
            D.targetChart (ρ i)) ⊆ Set.Icc c d)
    (hleft : ∀ j : Fin (n + 1), D.lowerCorner j < c j)
    (hright : ∀ j : Fin (n + 1), d j < D.upperCorner j) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart
          D.localizedForm) ⊆
      boxInteriorSupportBox D.lowerCorner D.upperCorner := by
  have hcoeff :
      tsupport
          (ManifoldForm.transitionCoefficientInChart I D.sourceChart
            D.targetChart (ρ i)) ⊆
        boxInteriorSupportBox D.lowerCorner D.upperCorner :=
    tsupport_subset_boxInteriorSupportBox_of_subset_Icc hρ hleft hright
  simpa [LocalizedInteriorPiece.localizedForm] using
    D.transitionPullback_tsupport_subset_interiorBox_of_coefficient hcoeff

end LocalizedInteriorPiece

/--
Inner closed-box support data for the localized interior coefficients, with a
strict coordinate margin inside the selected outer boxes stored by the M8
measure-localization package.
-/
structure LocalizedInteriorCoefficientInnerBoxBuffer {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /-- Lower corners of the inner closed boxes. -/
  innerLower : M → Fin (n + 1) → Real
  /-- Upper corners of the inner closed boxes. -/
  innerUpper : M → Fin (n + 1) → Real
  /-- Coefficient support lies in the inner closed box for every active chart. -/
  coefficient_tsupport_subset_innerIcc :
    ∀ x, x ∈ selectedPartition.active →
      tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (measureLocalization.localizedInterior.piece x).sourceChart
            (measureLocalization.localizedInterior.piece x).targetChart
            (measureLocalization.localizedInterior.coefficient x)) ⊆
        Set.Icc (innerLower x) (innerUpper x)
  /-- The inner lower corner is strictly above the selected outer lower corner. -/
  lower_lt_innerLower :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      (measureLocalization.localizedInterior.piece x).lowerCorner j <
        innerLower x j
  /-- The inner upper corner is strictly below the selected outer upper corner. -/
  innerUpper_lt_upper :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      innerUpper x j <
        (measureLocalization.localizedInterior.piece x).upperCorner j

namespace LocalizedInteriorCoefficientInnerBoxBuffer

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/-- The packaged inner-box data gives the strict coefficient-support field. -/
theorem coefficient_tsupport_subset_interiorBox
    (D :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImages measureLocalization) :
    ∀ x, x ∈ selectedPartition.active →
      tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (measureLocalization.localizedInterior.piece x).sourceChart
            (measureLocalization.localizedInterior.piece x).targetChart
            (measureLocalization.localizedInterior.coefficient x)) ⊆
        boxInteriorSupportBox
          (measureLocalization.localizedInterior.piece x).lowerCorner
          (measureLocalization.localizedInterior.piece x).upperCorner := by
  intro x hx
  exact tsupport_subset_boxInteriorSupportBox_of_subset_Icc
    (D.coefficient_tsupport_subset_innerIcc x hx)
    (D.lower_lt_innerLower x hx)
    (D.innerUpper_lt_upper x hx)

/--
Convert inner closed-box coefficient support with strict margins into the
compact-support buffer consumed by the artificial-face support-zero route.
-/
def toCompactSupportBoxBuffer
    (D :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImages measureLocalization) :
    CompactSupportBoxBuffer I omega selectedPartition targetImages
      measureLocalization :=
  CompactSupportBoxBuffer.ofLocalizedInteriorCoefficientBuffer
    (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureLocalization := measureLocalization)
    D.coefficient_tsupport_subset_interiorBox

theorem toCompactSupportBoxBuffer_support
    (D :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImages measureLocalization) :
    D.toCompactSupportBoxBuffer.strictSupport_subset_interiorBox =
      (CompactSupportBoxBuffer.ofLocalizedInteriorCoefficientBuffer
        (I := I) (omega := omega) (BoundaryPiece := BoundaryPiece)
        (selectedPartition := selectedPartition) (targetImages := targetImages)
        (measureLocalization := measureLocalization)
        D.coefficient_tsupport_subset_interiorBox).strictSupport_subset_interiorBox :=
  rfl

/-- Direct M8 artificial-face fields from inner coefficient boxes. -/
def toM8ArtificialFaceFields
    (D :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImages measureLocalization) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  D.toCompactSupportBoxBuffer.toM8ArtificialFaceFields

@[simp]
theorem toM8ArtificialFaceFields_active
    (D :
      LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
        targetImages measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.activeCharts =
      selectedPartition.active :=
  D.toCompactSupportBoxBuffer.toM8ArtificialFaceFields_active

end LocalizedInteriorCoefficientInnerBoxBuffer

end LocalizedInteriorBuffers

end Stokes

end
