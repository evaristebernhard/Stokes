import Stokes.Global.FiniteActive
import Stokes.Global.BoxSelection

/-!
# Compact active coordinate boxes

This file combines the finite-active compact-support bookkeeping with compact
coordinate box selections.  The genuinely geometric inputs that are not yet
proved in this global layer, such as chart-target and overlap containment, are
kept as explicit structure fields.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section CompactActiveBoxes

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [Preorder E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Finite-active compact-support data together with, for each active index, a
compact coordinate support set and a selected closed coordinate box containing
that set.

The target and overlap inclusions are fields on purpose: the abstract compact
box existence theorem only gives a containing closed box, while fitting that
box inside a particular chart-transition domain is a separate local-geometry
input.
-/
structure CompactActiveBoxData
    (I : ModelWithCorners Real E H) (ω : ManifoldForm I M k) where
  /-- The partition of unity and finite-active compact support package. -/
  finiteActive : FiniteActiveOnCompact (M := M) I
  /-- The compact coordinate support set attached to each partition index. -/
  coordSupport : M → Set E
  /-- Compactness of each active coordinate support set. -/
  isCompact_coordSupport :
    ∀ i ∈ finiteActive.active, IsCompact (coordSupport i)
  /-- A selected coordinate box for each index.  Only active indices are used. -/
  box : M → CompactCoordinateBoxSelection E
  /-- The selected coordinate box packages the corresponding coordinate support. -/
  box_K_eq_coordSupport :
    ∀ i ∈ finiteActive.active, (box i).K = coordSupport i
  /-- The coordinate support contains the transition-pullback topological support. -/
  tsupport_subset_coordSupport :
    ∀ i ∈ finiteActive.active,
      tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆ coordSupport i
  /-- The selected box lies in the target of the active chart. -/
  Icc_subset_target :
    ∀ i ∈ finiteActive.active,
      Set.Icc (box i).a (box i).b ⊆ (extChartAt I i).target
  /-- The selected box lies in the self-overlap domain for the active chart. -/
  Icc_subset_overlap :
    ∀ i ∈ finiteActive.active,
      Set.Icc (box i).a (box i).b ⊆ ManifoldForm.chartOverlap I i i

namespace CompactActiveBoxData

variable {I : ModelWithCorners Real E H} {ω : ManifoldForm I M k}

/-- Lower corner of the selected coordinate box for each index. -/
def lower (D : CompactActiveBoxData I ω) : M → E :=
  fun i => (D.box i).a

/-- Upper corner of the selected coordinate box for each index. -/
def upper (D : CompactActiveBoxData I ω) : M → E :=
  fun i => (D.box i).b

@[simp]
theorem lower_apply (D : CompactActiveBoxData I ω) (i : M) :
    D.lower i = (D.box i).a :=
  rfl

@[simp]
theorem upper_apply (D : CompactActiveBoxData I ω) (i : M) :
    D.upper i = (D.box i).b :=
  rfl

theorem isCompact_K (D : CompactActiveBoxData I ω) :
    IsCompact D.finiteActive.K :=
  D.finiteActive.isCompact

theorem coordSupport_subset_Icc
    (D : CompactActiveBoxData I ω) {i : M} (hi : i ∈ D.finiteActive.active) :
    D.coordSupport i ⊆ Set.Icc (D.lower i) (D.upper i) := by
  intro x hx
  change x ∈ Set.Icc (D.box i).a (D.box i).b
  exact (D.box i).subset_Icc (by
    simpa [D.box_K_eq_coordSupport i hi] using hx)

theorem tsupport_subset_box
    (D : CompactActiveBoxData I ω) {i : M} (hi : i ∈ D.finiteActive.active) :
    tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
      Set.Icc (D.lower i) (D.upper i) :=
  (D.tsupport_subset_coordSupport i hi).trans (D.coordSupport_subset_Icc hi)

/--
Each active compact coordinate support package produces the selected interior
chart box needed by local Stokes wrappers.
-/
theorem interiorChartSelectedBox
    (D : CompactActiveBoxData I ω) {i : M} (hi : i ∈ D.finiteActive.active) :
    Stokes.interiorChartSelectedBox I i i ω (D.lower i) (D.upper i) := by
  change Stokes.interiorChartSelectedBox I i i ω (D.box i).a (D.box i).b
  refine
    CompactCoordinateBoxSelection.interiorChartSelectedBox_of_tsupport_subset
      (D.box i) ?_ (D.Icc_subset_target i hi) (D.Icc_subset_overlap i hi)
  intro x hx
  simpa [D.box_K_eq_coordSupport i hi] using
    D.tsupport_subset_coordSupport i hi hx

theorem le
    (D : CompactActiveBoxData I ω) {i : M} (hi : i ∈ D.finiteActive.active) :
    D.lower i ≤ D.upper i :=
  (D.interiorChartSelectedBox hi).le

theorem Icc_subset_domain
    (D : CompactActiveBoxData I ω) {i : M} (hi : i ∈ D.finiteActive.active) :
    Set.Icc (D.lower i) (D.upper i) ⊆ interiorChartDomain I i i :=
  (D.interiorChartSelectedBox hi).Icc_subset_domain

end CompactActiveBoxData

/--
The compact active box data plus an open smoothness neighborhood for each
active selected box.  This is exactly the extra information required by the
existing `SelectedBoxPartitionOfUnity` wrapper, whose boxes are extended boxes.
-/
structure CompactActiveExtendedBoxData
    (I : ModelWithCorners Real E H) (ω : ManifoldForm I M k) where
  /-- The compact finite-active box-selection data. -/
  boxData : CompactActiveBoxData I ω
  /-- An ambient smoothness neighborhood for each selected coordinate box. -/
  smoothSet : M → Set E
  /-- The smoothness neighborhood is open for every active index. -/
  isOpen_smoothSet :
    ∀ i ∈ boxData.finiteActive.active, IsOpen (smoothSet i)
  /-- The selected closed coordinate box is contained in the smoothness neighborhood. -/
  Icc_subset_smoothSet :
    ∀ i ∈ boxData.finiteActive.active,
      Set.Icc (boxData.lower i) (boxData.upper i) ⊆ smoothSet i
  /-- The transition-pullback representative is smooth on the chosen neighborhood. -/
  contDiffOn_smoothSet :
    ∀ i ∈ boxData.finiteActive.active,
      ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I i i ω) (smoothSet i)

namespace CompactActiveExtendedBoxData

variable {I : ModelWithCorners Real E H} {ω : ManifoldForm I M k}

theorem interiorChartSelectedBox
    (D : CompactActiveExtendedBoxData I ω) {i : M}
    (hi : i ∈ D.boxData.finiteActive.active) :
    Stokes.interiorChartSelectedBox I i i ω (D.boxData.lower i) (D.boxData.upper i) :=
  D.boxData.interiorChartSelectedBox hi

theorem interiorChartExtendedBox
    (D : CompactActiveExtendedBoxData I ω) {i : M}
    (hi : i ∈ D.boxData.finiteActive.active) :
    Stokes.interiorChartExtendedBox I i i ω (D.boxData.lower i) (D.boxData.upper i) :=
  Stokes.interiorChartExtendedBox.mk (D.interiorChartSelectedBox hi)
    (D.isOpen_smoothSet i hi) (D.Icc_subset_smoothSet i hi)
    (D.contDiffOn_smoothSet i hi)

/--
Package compact active extended boxes as the existing selected-box partition
of unity data.
-/
def toSelectedBoxPartitionOfUnity
    (D : CompactActiveExtendedBoxData I ω) :
    SelectedBoxPartitionOfUnity I ω :=
  D.boxData.finiteActive.toSelectedBoxPartitionOfUnity D.boxData.lower D.boxData.upper
    fun i hi => D.interiorChartExtendedBox (i := i) hi

@[simp]
theorem toSelectedBoxPartitionOfUnity_partition
    (D : CompactActiveExtendedBoxData I ω) :
    D.toSelectedBoxPartitionOfUnity.partition = D.boxData.finiteActive.partition :=
  rfl

@[simp]
theorem toSelectedBoxPartitionOfUnity_K
    (D : CompactActiveExtendedBoxData I ω) :
    D.toSelectedBoxPartitionOfUnity.K = D.boxData.finiteActive.K :=
  rfl

@[simp]
theorem toSelectedBoxPartitionOfUnity_active
    (D : CompactActiveExtendedBoxData I ω) :
    D.toSelectedBoxPartitionOfUnity.active = D.boxData.finiteActive.active :=
  rfl

@[simp]
theorem toSelectedBoxPartitionOfUnity_lower
    (D : CompactActiveExtendedBoxData I ω) :
    D.toSelectedBoxPartitionOfUnity.lower = D.boxData.lower :=
  rfl

@[simp]
theorem toSelectedBoxPartitionOfUnity_upper
    (D : CompactActiveExtendedBoxData I ω) :
    D.toSelectedBoxPartitionOfUnity.upper = D.boxData.upper :=
  rfl

end CompactActiveExtendedBoxData

end CompactActiveBoxes

section PiRealActiveSelections

universe u v w

variable {ι : Type u} [Fintype ι]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
For finite real coordinate spaces, compact coordinate supports over a finite
active set have coordinate box selections simultaneously.

This proves the pure compact-coordinate-box part of the construction.  The
chart-target, overlap, and support-containment inputs remain separate fields in
`CompactActiveBoxData`.
-/
theorem exists_activeCompactCoordinateBoxSelections_piReal
    {I : ModelWithCorners Real (ι → Real) H}
    (P : FiniteActiveOnCompact (M := M) I)
    (coordSupport : M → Set (ι → Real))
    (hcompact : ∀ i ∈ P.active, IsCompact (coordSupport i)) :
    ∃ box : M → CompactCoordinateBoxSelection (ι → Real),
      ∀ i ∈ P.active, (box i).K = coordSupport i := by
  classical
  let fallback : CompactCoordinateBoxSelection (ι → Real) :=
    CompactCoordinateBoxSelection.of_subset (∅ : Set (ι → Real)) isCompact_empty 0 0
      le_rfl (empty_subset _)
  let box : M → CompactCoordinateBoxSelection (ι → Real) := fun i =>
    if hi : i ∈ P.active then
      Classical.choose (exists_compactCoordinateBoxSelection_piReal (hcompact i hi))
    else
      fallback
  refine ⟨box, ?_⟩
  intro i hi
  simpa [box, hi] using
    (Classical.choose_spec (exists_compactCoordinateBoxSelection_piReal (hcompact i hi)))

end PiRealActiveSelections

end Stokes

end
