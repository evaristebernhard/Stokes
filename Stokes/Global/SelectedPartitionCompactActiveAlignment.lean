import Stokes.Global.CompactSupportStrictBufferFromActive

/-!
# Alignment between selected partitions and compact active boxes

This file records the definitional alignment between the selected partition
created from compact active boxes and the compact active box data itself.  It is
used to remove routine active-set and box-corner rewrites from the strict-buffer
route, while keeping the genuine M8 localized-piece and strict-margin inputs
explicit.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section SelectedPartitionCompactActiveAlignment

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

namespace CompactActiveExtendedBoxData

theorem toSelectedBoxPartitionOfUnity_active_subset_boxData_active
    (D : CompactActiveExtendedBoxData I omega) :
    ∀ x, x ∈ D.toSelectedBoxPartitionOfUnity.active →
      x ∈ D.boxData.finiteActive.active := by
  intro x hx
  simpa using hx

@[simp]
theorem toSelectedBoxPartitionOfUnity_partition_apply
    (D : CompactActiveExtendedBoxData I omega) (i x : M) :
    D.toSelectedBoxPartitionOfUnity.partition i x =
      D.boxData.finiteActive.partition i x := by
  rw [toSelectedBoxPartitionOfUnity_partition]

@[simp]
theorem toSelectedBoxPartitionOfUnity_lower_apply
    (D : CompactActiveExtendedBoxData I omega) (i : M) :
    D.toSelectedBoxPartitionOfUnity.lower i = D.boxData.lower i := by
  rw [toSelectedBoxPartitionOfUnity_lower]

@[simp]
theorem toSelectedBoxPartitionOfUnity_upper_apply
    (D : CompactActiveExtendedBoxData I omega) (i : M) :
    D.toSelectedBoxPartitionOfUnity.upper i = D.boxData.upper i := by
  rw [toSelectedBoxPartitionOfUnity_upper]

end CompactActiveExtendedBoxData

namespace CompactSupportFiniteActiveSelection

variable {ρ : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}

@[simp]
theorem selectedBoxPartitionOfUnity_active_compactActiveBoxData
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega) :
    (S.selectedBoxPartitionOfUnity smoothness).active =
      S.compactActiveBoxData.finiteActive.active := by
  change ((S.compactActiveExtendedBoxData smoothness).toSelectedBoxPartitionOfUnity).active =
    S.compactActiveBoxData.finiteActive.active
  rw [CompactActiveExtendedBoxData.toSelectedBoxPartitionOfUnity_active]
  rfl

theorem selectedBoxPartitionOfUnity_active_subset_compactActiveBoxData_active
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega) :
    ∀ x, x ∈ (S.selectedBoxPartitionOfUnity smoothness).active →
      x ∈ S.compactActiveBoxData.finiteActive.active := by
  intro x hx
  simpa using hx

@[simp]
theorem selectedBoxPartitionOfUnity_partition_compactActiveBoxData
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega) :
    (S.selectedBoxPartitionOfUnity smoothness).partition =
      S.compactActiveBoxData.finiteActive.partition := by
  change ((S.compactActiveExtendedBoxData smoothness).toSelectedBoxPartitionOfUnity).partition =
    S.compactActiveBoxData.finiteActive.partition
  rw [CompactActiveExtendedBoxData.toSelectedBoxPartitionOfUnity_partition]
  rfl

@[simp]
theorem selectedBoxPartitionOfUnity_lower_compactActiveBoxData
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega) :
    (S.selectedBoxPartitionOfUnity smoothness).lower =
      S.compactActiveBoxData.lower := by
  change ((S.compactActiveExtendedBoxData smoothness).toSelectedBoxPartitionOfUnity).lower =
    S.compactActiveBoxData.lower
  rw [CompactActiveExtendedBoxData.toSelectedBoxPartitionOfUnity_lower]
  rfl

@[simp]
theorem selectedBoxPartitionOfUnity_upper_compactActiveBoxData
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega) :
    (S.selectedBoxPartitionOfUnity smoothness).upper =
      S.compactActiveBoxData.upper := by
  change ((S.compactActiveExtendedBoxData smoothness).toSelectedBoxPartitionOfUnity).upper =
    S.compactActiveBoxData.upper
  rw [CompactActiveExtendedBoxData.toSelectedBoxPartitionOfUnity_upper]
  rfl

@[simp]
theorem selectedBoxPartitionOfUnity_partition_apply_compactActiveBoxData
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)
    (i x : M) :
    (S.selectedBoxPartitionOfUnity smoothness).partition i x =
      S.compactActiveBoxData.finiteActive.partition i x := by
  rw [selectedBoxPartitionOfUnity_partition_compactActiveBoxData]

@[simp]
theorem selectedBoxPartitionOfUnity_lower_apply_compactActiveBoxData
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)
    (i : M) :
    (S.selectedBoxPartitionOfUnity smoothness).lower i =
      S.compactActiveBoxData.lower i := by
  rw [selectedBoxPartitionOfUnity_lower_compactActiveBoxData]

@[simp]
theorem selectedBoxPartitionOfUnity_upper_apply_compactActiveBoxData
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega)
    (i : M) :
    (S.selectedBoxPartitionOfUnity smoothness).upper i =
      S.compactActiveBoxData.upper i := by
  rw [selectedBoxPartitionOfUnity_upper_compactActiveBoxData]

end CompactSupportFiniteActiveSelection

/--
The selected partition is the one generated by compact active box data.

This record packages only definitional/projection alignment: active-set
containment, the partition function, and selected box corners.  It intentionally
does not include M8 localized-piece equality or strict margins.
-/
structure CompactActiveSelectedPartitionAlignment
    (D : CompactActiveBoxData I omega)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega) where
  active_subset :
    ∀ x, x ∈ selectedPartition.active → x ∈ D.finiteActive.active
  partition_eq : selectedPartition.partition = D.finiteActive.partition
  lower_eq : selectedPartition.lower = D.lower
  upper_eq : selectedPartition.upper = D.upper

namespace CompactActiveSelectedPartitionAlignment

variable {D : CompactActiveBoxData I omega}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}

@[simp]
theorem partition_apply
    (A : CompactActiveSelectedPartitionAlignment D selectedPartition)
    (i x : M) :
    selectedPartition.partition i x = D.finiteActive.partition i x := by
  rw [A.partition_eq]

@[simp]
theorem lower_apply
    (A : CompactActiveSelectedPartitionAlignment D selectedPartition)
    (i : M) :
    selectedPartition.lower i = D.lower i := by
  rw [A.lower_eq]

@[simp]
theorem upper_apply
    (A : CompactActiveSelectedPartitionAlignment D selectedPartition)
    (i : M) :
    selectedPartition.upper i = D.upper i := by
  rw [A.upper_eq]

def toStrictBufferAlignment
    {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages}
    (A : CompactActiveSelectedPartitionAlignment D selectedPartition)
    (piece_transitionPullback_eq :
      ∀ x, x ∈ selectedPartition.active →
        ManifoldForm.transitionPullbackInChart I
            (measureLocalization.localizedInterior.piece x).sourceChart
            (measureLocalization.localizedInterior.piece x).targetChart
            (measureLocalization.localizedInterior.piece x).localizedForm =
          ManifoldForm.transitionPullbackInChart I x x
            (ManifoldForm.localizedForm I (D.finiteActive.partition x) omega))
    (outer_lower_lt_selectedLower :
      ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
        (measureLocalization.localizedInterior.piece x).lowerCorner j <
          selectedPartition.lower x j)
    (selectedUpper_lt_outer_upper :
      ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
        selectedPartition.upper x j <
          (measureLocalization.localizedInterior.piece x).upperCorner j) :
    CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
      measureLocalization where
  active_subset := A.active_subset
  piece_transitionPullback_eq := piece_transitionPullback_eq
  outer_lower_lt_innerLower := by
    intro x hx j
    simpa [A.lower_eq] using outer_lower_lt_selectedLower x hx j
  innerUpper_lt_outer_upper := by
    intro x hx j
    simpa [A.upper_eq] using selectedUpper_lt_outer_upper x hx j

def toStrictBufferAlignmentOfSelectedPartitionPiece
    {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages}
    (A : CompactActiveSelectedPartitionAlignment D selectedPartition)
    (piece_transitionPullback_eq :
      ∀ x, x ∈ selectedPartition.active →
        ManifoldForm.transitionPullbackInChart I
            (measureLocalization.localizedInterior.piece x).sourceChart
            (measureLocalization.localizedInterior.piece x).targetChart
            (measureLocalization.localizedInterior.piece x).localizedForm =
          ManifoldForm.transitionPullbackInChart I x x
            (ManifoldForm.localizedForm I (selectedPartition.partition x) omega))
    (outer_lower_lt_selectedLower :
      ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
        (measureLocalization.localizedInterior.piece x).lowerCorner j <
          selectedPartition.lower x j)
    (selectedUpper_lt_outer_upper :
      ∀ x, x ∈ selectedPartition.active → ∀ j : Fin (n + 1),
        selectedPartition.upper x j <
          (measureLocalization.localizedInterior.piece x).upperCorner j) :
    CompactActiveBoxStrictBufferAlignment D selectedPartition targetImages
      measureLocalization :=
  A.toStrictBufferAlignment
    (by
      intro x hx
      simpa [A.partition_eq] using piece_transitionPullback_eq x hx)
    outer_lower_lt_selectedLower selectedUpper_lt_outer_upper

end CompactActiveSelectedPartitionAlignment

namespace CompactActiveExtendedBoxData

def toCompactActiveSelectedPartitionAlignment
    (D : CompactActiveExtendedBoxData I omega) :
    CompactActiveSelectedPartitionAlignment D.boxData D.toSelectedBoxPartitionOfUnity where
  active_subset := D.toSelectedBoxPartitionOfUnity_active_subset_boxData_active
  partition_eq := by
    rw [toSelectedBoxPartitionOfUnity_partition]
  lower_eq := by
    rw [toSelectedBoxPartitionOfUnity_lower]
  upper_eq := by
    rw [toSelectedBoxPartitionOfUnity_upper]

end CompactActiveExtendedBoxData

namespace CompactSupportFiniteActiveSelection

variable {ρ : SmoothPartitionOfUnity M I M univ}
variable {K : Set M} {hK : IsCompact K}

def toCompactActiveSelectedPartitionAlignment
    (S : CompactSupportFiniteActiveSelection (I := I) ρ K hK omega)
    (smoothness : ActiveCompactBoxSmoothness S.finiteActive S.supportData.box omega) :
    CompactActiveSelectedPartitionAlignment S.compactActiveBoxData
      (S.selectedBoxPartitionOfUnity smoothness) where
  active_subset :=
    S.selectedBoxPartitionOfUnity_active_subset_compactActiveBoxData_active
      smoothness
  partition_eq := by
    rw [selectedBoxPartitionOfUnity_partition_compactActiveBoxData]
  lower_eq := by
    rw [selectedBoxPartitionOfUnity_lower_compactActiveBoxData]
  upper_eq := by
    rw [selectedBoxPartitionOfUnity_upper_compactActiveBoxData]

end CompactSupportFiniteActiveSelection

end SelectedPartitionCompactActiveAlignment

end Stokes

end
