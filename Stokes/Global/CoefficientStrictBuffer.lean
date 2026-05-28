import Stokes.Global.CompactSupportStrictBuffer
import Stokes.Global.CompactSupportChartBox

/-!
# Strict buffers from coefficient compact support

This file is the coefficient-facing entry point for the strict-buffer route.
It does not create compact support or chart containment facts.  Instead it
turns already selected coefficient boxes, together with an explicit strict
margin inside the localized outer box, into the
`LocalizedInteriorCoefficientInnerBoxBuffer` consumed by the artificial-face
support-zero API.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CoefficientStrictBuffer

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

namespace CoefficientBoxSupportData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ρ : M → Real}
variable {a b c d : Fin (n + 1) → Real}

/--
Coefficient support in an inner closed box becomes strict support in an outer
box once the inner box has coordinatewise positive margin.
-/
theorem coefficient_tsupport_subset_interiorBox
    (D : CoefficientBoxSupportData I x0 x1 ρ c d)
    (hleft : ∀ j : Fin (n + 1), a j < c j)
    (hright : ∀ j : Fin (n + 1), d j < b j) :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆
      boxInteriorSupportBox a b :=
  tsupport_subset_boxInteriorSupportBox_of_subset_Icc
    D.coefficient_tsupport_subset hleft hright

end CoefficientBoxSupportData

namespace CoefficientChartCompactSupportData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ρ : M → Real}
variable {a b : Fin (n + 1) → Real}

/--
The automatically selected coefficient compact-support box gives strict
support in a larger box once a strict margin is supplied.
-/
theorem coefficient_tsupport_subset_interiorBox_of_box_margin
    (D : CoefficientChartCompactSupportData I x0 x1 ρ)
    (hleft : ∀ j : Fin (n + 1), a j < D.box.a j)
    (hright : ∀ j : Fin (n + 1), D.box.b j < b j) :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆
      boxInteriorSupportBox a b :=
  tsupport_subset_boxInteriorSupportBox_of_subset_Icc
    D.coefficient_tsupport_subset_box hleft hright

/--
Package the automatically selected coefficient compact-support box as a
`CoefficientBoxSupportData`, while keeping the selected inner corners visible.
-/
def toInnerCoefficientBoxSupportData
    (D : CoefficientChartCompactSupportData I x0 x1 ρ) :
    CoefficientBoxSupportData I x0 x1 ρ D.box.a D.box.b :=
  D.coefficientBoxSupportData

end CoefficientChartCompactSupportData

namespace LocalizedInteriorPiece

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {ρ : M → M → Real} {i : M}
variable {c d : Fin (n + 1) → Real}

/--
Single-piece route: coefficient box support with a strict margin gives strict
support for the localized transition-pullback representative.
-/
theorem transitionPullback_tsupport_subset_interiorBox_of_coefficientBoxSupport
    (D : LocalizedInteriorPiece I ω ρ i)
    (B :
      CoefficientBoxSupportData I D.sourceChart D.targetChart (ρ i) c d)
    (hleft : ∀ j : Fin (n + 1), D.lowerCorner j < c j)
    (hright : ∀ j : Fin (n + 1), d j < D.upperCorner j) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart
          D.localizedForm) ⊆
      boxInteriorSupportBox D.lowerCorner D.upperCorner :=
  D.transitionPullback_tsupport_subset_interiorBox_of_coefficient_Icc
    B.coefficient_tsupport_subset hleft hright

/--
Single-piece route from compact coefficient support, using the selected compact
coefficient box as the inner box.
-/
theorem transitionPullback_tsupport_subset_interiorBox_of_coefficientChartCompactSupport
    (D : LocalizedInteriorPiece I ω ρ i)
    (C :
      CoefficientChartCompactSupportData I D.sourceChart D.targetChart (ρ i))
    (hleft : ∀ j : Fin (n + 1), D.lowerCorner j < C.box.a j)
    (hright : ∀ j : Fin (n + 1), C.box.b j < D.upperCorner j) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart
          D.localizedForm) ⊆
      boxInteriorSupportBox D.lowerCorner D.upperCorner :=
  D.transitionPullback_tsupport_subset_interiorBox_of_coefficientBoxSupport
    C.toInnerCoefficientBoxSupportData hleft hright

end LocalizedInteriorPiece

/--
Family-level coefficient support data for every selected active chart.  Each
coefficient is already supported in an inner closed box, and each inner box has
strict margin inside the corresponding localized outer box.
-/
structure LocalizedInteriorCoefficientBoxSupportFamily {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /-- Lower corners of the inner coefficient boxes. -/
  innerLower : M → Fin (n + 1) → Real
  /-- Upper corners of the inner coefficient boxes. -/
  innerUpper : M → Fin (n + 1) → Real
  /-- Coefficient box-support package for each selected active chart. -/
  coefficientBoxSupport :
    ∀ x, x ∈ selectedPartition.active →
      CoefficientBoxSupportData I
        (measureLocalization.localizedInterior.piece x).sourceChart
        (measureLocalization.localizedInterior.piece x).targetChart
        (measureLocalization.localizedInterior.coefficient x)
        (innerLower x) (innerUpper x)
  /-- Inner lower corners lie strictly above localized outer lower corners. -/
  lower_lt_innerLower :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      (measureLocalization.localizedInterior.piece x).lowerCorner j <
        innerLower x j
  /-- Inner upper corners lie strictly below localized outer upper corners. -/
  innerUpper_lt_upper :
    ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
      innerUpper x j <
        (measureLocalization.localizedInterior.piece x).upperCorner j

namespace LocalizedInteriorCoefficientBoxSupportFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/-- The family package gives the inner-box buffer expected by the strict route. -/
def toLocalizedInteriorCoefficientInnerBoxBuffer
    (D :
      LocalizedInteriorCoefficientBoxSupportFamily I omega selectedPartition
        targetImages measureLocalization) :
    LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
      targetImages measureLocalization where
  innerLower := D.innerLower
  innerUpper := D.innerUpper
  coefficient_tsupport_subset_innerIcc := fun x hx =>
    (D.coefficientBoxSupport x hx).coefficient_tsupport_subset
  lower_lt_innerLower := D.lower_lt_innerLower
  innerUpper_lt_upper := D.innerUpper_lt_upper

@[simp]
theorem toLocalizedInteriorCoefficientInnerBoxBuffer_innerLower
    (D :
      LocalizedInteriorCoefficientBoxSupportFamily I omega selectedPartition
        targetImages measureLocalization) :
    D.toLocalizedInteriorCoefficientInnerBoxBuffer.innerLower =
      D.innerLower :=
  rfl

/-- Direct compact-support buffer obtained from coefficient box-support data. -/
def toCompactSupportBoxBuffer
    (D :
      LocalizedInteriorCoefficientBoxSupportFamily I omega selectedPartition
        targetImages measureLocalization) :
    CompactSupportBoxBuffer I omega selectedPartition targetImages
      measureLocalization :=
  D.toLocalizedInteriorCoefficientInnerBoxBuffer.toCompactSupportBoxBuffer

/-- Direct M8 artificial-face fields obtained from coefficient box-support data. -/
def toM8ArtificialFaceFields
    (D :
      LocalizedInteriorCoefficientBoxSupportFamily I omega selectedPartition
        targetImages measureLocalization) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  D.toLocalizedInteriorCoefficientInnerBoxBuffer.toM8ArtificialFaceFields

@[simp]
theorem toM8ArtificialFaceFields_active
    (D :
      LocalizedInteriorCoefficientBoxSupportFamily I omega selectedPartition
        targetImages measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.activeCharts =
      selectedPartition.active :=
  D.toLocalizedInteriorCoefficientInnerBoxBuffer.toM8ArtificialFaceFields_active

end LocalizedInteriorCoefficientBoxSupportFamily

/--
Family-level compact coefficient support.  For each active chart, the compact
coefficient support package chooses an inner coordinate box; the caller supplies
the strict margin from that inner box to the localized outer box.
-/
structure LocalizedInteriorCoefficientChartCompactSupportFamily {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages) where
  /-- Compact support package for each active transition coefficient. -/
  chartSupport :
    ∀ x, x ∈ selectedPartition.active →
      CoefficientChartCompactSupportData I
        (measureLocalization.localizedInterior.piece x).sourceChart
        (measureLocalization.localizedInterior.piece x).targetChart
        (measureLocalization.localizedInterior.coefficient x)
  /-- Selected inner lower corners lie strictly above localized outer lowers. -/
  lower_lt_innerLower :
    ∀ x, (hx : x ∈ selectedPartition.active) → ∀ j : Fin (n + 1),
      (measureLocalization.localizedInterior.piece x).lowerCorner j <
        (chartSupport x hx).box.a j
  /-- Selected inner upper corners lie strictly below localized outer uppers. -/
  innerUpper_lt_upper :
    ∀ x, (hx : x ∈ selectedPartition.active) → ∀ j : Fin (n + 1),
      (chartSupport x hx).box.b j <
        (measureLocalization.localizedInterior.piece x).upperCorner j

namespace LocalizedInteriorCoefficientChartCompactSupportFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}

/-- The chosen inner lower corner for active indices; arbitrary off active set. -/
def innerLower
    (D :
      LocalizedInteriorCoefficientChartCompactSupportFamily I omega
        selectedPartition targetImages measureLocalization) :
    M → Fin (n + 1) → Real := by
  classical
  exact fun x =>
    if hx : x ∈ selectedPartition.active then
      (D.chartSupport x hx).box.a
    else
      0

/-- The chosen inner upper corner for active indices; arbitrary off active set. -/
def innerUpper
    (D :
      LocalizedInteriorCoefficientChartCompactSupportFamily I omega
        selectedPartition targetImages measureLocalization) :
    M → Fin (n + 1) → Real := by
  classical
  exact fun x =>
    if hx : x ∈ selectedPartition.active then
      (D.chartSupport x hx).box.b
    else
      0

@[simp]
theorem innerLower_active
    (D :
      LocalizedInteriorCoefficientChartCompactSupportFamily I omega
        selectedPartition targetImages measureLocalization)
    {x : M} (hx : x ∈ selectedPartition.active) :
    D.innerLower x = (D.chartSupport x hx).box.a := by
  classical
  simp [innerLower, hx]

@[simp]
theorem innerUpper_active
    (D :
      LocalizedInteriorCoefficientChartCompactSupportFamily I omega
        selectedPartition targetImages measureLocalization)
    {x : M} (hx : x ∈ selectedPartition.active) :
    D.innerUpper x = (D.chartSupport x hx).box.b := by
  classical
  simp [innerUpper, hx]

/--
Convert compact coefficient support packages into explicit coefficient
box-support packages by exposing the selected inner boxes.
-/
def toCoefficientBoxSupportFamily
    (D :
      LocalizedInteriorCoefficientChartCompactSupportFamily I omega
        selectedPartition targetImages measureLocalization) :
    LocalizedInteriorCoefficientBoxSupportFamily I omega selectedPartition
      targetImages measureLocalization where
  innerLower := D.innerLower
  innerUpper := D.innerUpper
  coefficientBoxSupport := by
    intro x hx
    simpa [D.innerLower_active hx, D.innerUpper_active hx] using
      (D.chartSupport x hx).toInnerCoefficientBoxSupportData
  lower_lt_innerLower := by
    intro x hx j
    simpa [D.innerLower_active hx] using D.lower_lt_innerLower x hx j
  innerUpper_lt_upper := by
    intro x hx j
    simpa [D.innerUpper_active hx] using D.innerUpper_lt_upper x hx j

/--
Compact coefficient support plus strict margins gives the inner-box buffer
consumed by the coefficient strict-buffer route.
-/
def toLocalizedInteriorCoefficientInnerBoxBuffer
    (D :
      LocalizedInteriorCoefficientChartCompactSupportFamily I omega
        selectedPartition targetImages measureLocalization) :
    LocalizedInteriorCoefficientInnerBoxBuffer I omega selectedPartition
      targetImages measureLocalization :=
  D.toCoefficientBoxSupportFamily.toLocalizedInteriorCoefficientInnerBoxBuffer

/-- Direct compact-support buffer from compact coefficient support packages. -/
def toCompactSupportBoxBuffer
    (D :
      LocalizedInteriorCoefficientChartCompactSupportFamily I omega
        selectedPartition targetImages measureLocalization) :
    CompactSupportBoxBuffer I omega selectedPartition targetImages
      measureLocalization :=
  D.toLocalizedInteriorCoefficientInnerBoxBuffer.toCompactSupportBoxBuffer

/-- Direct M8 artificial-face fields from compact coefficient support packages. -/
def toM8ArtificialFaceFields
    (D :
      LocalizedInteriorCoefficientChartCompactSupportFamily I omega
        selectedPartition targetImages measureLocalization) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  D.toLocalizedInteriorCoefficientInnerBoxBuffer.toM8ArtificialFaceFields

@[simp]
theorem toM8ArtificialFaceFields_active
    (D :
      LocalizedInteriorCoefficientChartCompactSupportFamily I omega
        selectedPartition targetImages measureLocalization) :
    D.toM8ArtificialFaceFields.artificialFaces.activeCharts =
      selectedPartition.active :=
  D.toLocalizedInteriorCoefficientInnerBoxBuffer.toM8ArtificialFaceFields_active

end LocalizedInteriorCoefficientChartCompactSupportFamily

end CoefficientStrictBuffer

end Stokes

end
