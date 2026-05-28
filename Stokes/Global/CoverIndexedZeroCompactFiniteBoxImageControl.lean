import Stokes.Global.CoverIndexedZeroCompactContinuityShrink
import Stokes.Global.CoverIndexedZeroCompactFinalNaturalTheorem

/-!
# Finite box image control for compact zero endpoints

This file packages the ambient chart-transition image-control step for a
finite family of half-space boxes.  It is deliberately one layer above the
single-index shrink lemmas:

* a finite box family stores the boundary cover index owning each box;
* closed-preimage, open-preimage, and `ContinuousOn + image_subset` hypotheses
  are each batched over the whole family; and
* the output is the endpoint-shaped family of ambient `MapsTo` facts.

This is the finite-refinement version needed after a compact boundary piece is
subdivided into several small half-space boxes.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactFiniteBoxImageControl

universe uH uM uι

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {ι : Type uι} [Fintype ι]

/--
Minimal finite family of source/target coordinate boxes attached to the
boundary part of a compact-support chart cover.

The owner map records which boundary chart supplies the source chart for a
refined box.  The source corners are per-box rather than the original
`C.boundaryLower/C.boundaryUpper`, because a compact boundary chart piece may
have to be subdivided into several smaller boxes before the ambient transition
image is controlled.
-/
structure CoverIndexedFiniteBoxImageControlData
    (C : CompactSupportChartCoverSelection I K) (ι : Type uι) [Fintype ι] where
  owner : ι → {x : M // x ∈ C.boundaryCenters}
  targetChart : ι → M
  sourceLower : ι → Fin (n + 1) → Real
  sourceUpper : ι → Fin (n + 1) → Real
  targetLower : ι → Fin (n + 1) → Real
  targetUpper : ι → Fin (n + 1) → Real

namespace CoverIndexedFiniteBoxImageControlData

variable
    (D : CoverIndexedFiniteBoxImageControlData
      (I := I) (K := K) C ι)

/-- Source chart attached to a refined finite box. -/
def sourceChart (q : ι) : M :=
  C.boundaryChart (D.owner q).1

/-- Ambient chart transition attached to a refined finite box. -/
def chartTransition (q : ι) :
    (Fin (n + 1) → Real) → (Fin (n + 1) → Real) :=
  ManifoldForm.chartTransition I (D.sourceChart q) (D.targetChart q)

/-- Endpoint-shaped ambient `MapsTo` field for all boxes in the finite family. -/
def ChartTransitionMapsToField : Prop :=
  ∀ q : ι,
    MapsTo (D.chartTransition q)
      (halfSpaceSupportBox (D.sourceLower q) (D.sourceUpper q))
      (Icc (D.targetLower q) (D.targetUpper q))

/-- Closed-preimage control for all finite boxes. -/
def ClosedPreimageShrinkField : Prop :=
  ∀ q : ι,
    Icc (D.sourceLower q) (D.sourceUpper q) ⊆
      (D.chartTransition q) ⁻¹'
        Icc (D.targetLower q) (D.targetUpper q)

/-- Target-open image containment for all finite boxes. -/
def ImageSubsetTargetOpenField
    (targetOpen : ι → Set (Fin (n + 1) → Real)) : Prop :=
  ∀ q : ι,
    (D.chartTransition q) ''
      Icc (D.sourceLower q) (D.sourceUpper q) ⊆ targetOpen q

/-- Target-open subsets are contained in the selected closed target boxes. -/
def TargetOpenSubsetIccField
    (targetOpen : ι → Set (Fin (n + 1) → Real)) : Prop :=
  ∀ q : ι, targetOpen q ⊆ Icc (D.targetLower q) (D.targetUpper q)

/-- Open-preimage shrink control for all finite boxes. -/
def OpenPreimageShrinkField
    (sourceOpen targetOpen : ι → Set (Fin (n + 1) → Real)) : Prop :=
  ∀ q : ι,
    Icc (D.sourceLower q) (D.sourceUpper q) ⊆
      sourceOpen q ∩ (D.chartTransition q) ⁻¹' targetOpen q

/--
Closed-preimage finite image control.

This is the leanest endpoint route: if every source closed box is already in
the preimage of its target closed box, then every stricter half-space support
box maps into that target closed box.
-/
theorem chartTransition_mapsTo_of_closed_preimage_shrink
    (hpre : D.ClosedPreimageShrinkField) :
    D.ChartTransitionMapsToField := by
  intro q
  exact
    ManifoldForm.chartTransition_mapsTo_halfSpaceSupportBox_of_Icc_subset_preimage
      (I := I) (x0 := D.sourceChart q) (x1 := D.targetChart q)
      (a := D.sourceLower q) (b := D.sourceUpper q)
      (c := D.targetLower q) (d := D.targetUpper q)
      (hpre q)

/--
Image-subset finite image control through target-open sets.

This route is useful after compactness has produced finite boxes and continuity
has been used upstream to choose target open sets with enough margin.
-/
theorem chartTransition_mapsTo_of_image_subset_targetOpen
    (targetOpen : ι → Set (Fin (n + 1) → Real))
    (hVsubset : D.TargetOpenSubsetIccField targetOpen)
    (himage : D.ImageSubsetTargetOpenField targetOpen) :
    D.ChartTransitionMapsToField := by
  intro q y hy
  exact hVsubset q (himage q ⟨y, halfSpaceSupportBox_subset_Icc _ _ hy, rfl⟩)

/--
Open-preimage finite image control.

This is the batched version of the existing single-box shrink lemma:

`Icc source ⊆ sourceOpen ∩ chartTransition ⁻¹' targetOpen`,
`sourceOpen` sits in the chart-transition domain, and
`targetOpen ⊆ target Icc`.
-/
theorem chartTransition_mapsTo_of_open_preimage_shrink
    [IsManifold I ⊤ M]
    (sourceOpen targetOpen : ι → Set (Fin (n + 1) → Real))
    (hUopen : ∀ q : ι, IsOpen (sourceOpen q))
    (hUtarget :
      ∀ q : ι, sourceOpen q ⊆ (extChartAt I (D.sourceChart q)).target)
    (hUoverlap :
      ∀ q : ι,
        sourceOpen q ⊆
          ManifoldForm.chartOverlap I (D.sourceChart q) (D.targetChart q))
    (hVopen : ∀ q : ι, IsOpen (targetOpen q))
    (hVsubset : D.TargetOpenSubsetIccField targetOpen)
    (hbox : D.OpenPreimageShrinkField sourceOpen targetOpen) :
    D.ChartTransitionMapsToField := by
  intro q
  exact
    ManifoldForm.chartTransition_mapsTo_halfSpaceSupportBox_of_open_preimage_shrink
      (I := I) (x0 := D.sourceChart q) (x1 := D.targetChart q)
      (a := D.sourceLower q) (b := D.sourceUpper q)
      (c := D.targetLower q) (d := D.targetUpper q)
      (U := sourceOpen q) (V := targetOpen q)
      (hUopen q) (hUtarget q) (hUoverlap q)
      (hVopen q) (hVsubset q) (hbox q)

/--
For a finite family, continuity plus image containment constructs the
per-box `ChartBoxOpenNeighborhood` inside the transition preimage.

This is the honest `ContinuousOn + image_subset/open preimage` bridge.  The
compactness/finite-cover step supplies `hIcc_source` and `himage`; this lemma
turns them into the chart-box shrink object consumed by the MapsTo theorem.
-/
def preimageChartBoxOpenNeighborhoodOfContinuousOnImageSubset
    (sourceOpen targetOpen : ι → Set (Fin (n + 1) → Real))
    (hUopen : ∀ q : ι, IsOpen (sourceOpen q))
    (hcont :
      ∀ q : ι, ContinuousOn (D.chartTransition q) (sourceOpen q))
    (hVopen : ∀ q : ι, IsOpen (targetOpen q))
    (hIcc_source :
      ∀ q : ι, Icc (D.sourceLower q) (D.sourceUpper q) ⊆ sourceOpen q)
    (himage : D.ImageSubsetTargetOpenField targetOpen)
    (q : ι) :
    ChartBoxOpenNeighborhood
      ((D.chartTransition q) ⁻¹' targetOpen q)
      (D.sourceLower q) (D.sourceUpper q) where
  neighborhood := sourceOpen q ∩ (D.chartTransition q) ⁻¹' targetOpen q
  isOpen_neighborhood :=
    isOpen_inter_preimage_of_continuousOn
      (hUopen q) (hcont q) (hVopen q)
  Icc_subset_neighborhood := by
    intro y hy
    exact ⟨hIcc_source q hy, himage q ⟨y, hy, rfl⟩⟩
  neighborhood_subset_target := by
    intro y hy
    exact hy.2

@[simp]
theorem preimageChartBoxOpenNeighborhoodOfContinuousOnImageSubset_neighborhood
    (sourceOpen targetOpen : ι → Set (Fin (n + 1) → Real))
    (hUopen : ∀ q : ι, IsOpen (sourceOpen q))
    (hcont :
      ∀ q : ι, ContinuousOn (D.chartTransition q) (sourceOpen q))
    (hVopen : ∀ q : ι, IsOpen (targetOpen q))
    (hIcc_source :
      ∀ q : ι, Icc (D.sourceLower q) (D.sourceUpper q) ⊆ sourceOpen q)
    (himage : D.ImageSubsetTargetOpenField targetOpen)
    (q : ι) :
    (D.preimageChartBoxOpenNeighborhoodOfContinuousOnImageSubset
      sourceOpen targetOpen hUopen hcont hVopen hIcc_source himage q).neighborhood =
      sourceOpen q ∩ (D.chartTransition q) ⁻¹' targetOpen q :=
  rfl

/--
Finite image control from continuity on source opens and image containment of
the selected closed boxes into target opens.
-/
theorem chartTransition_mapsTo_of_continuousOn_image_subset
    (sourceOpen targetOpen : ι → Set (Fin (n + 1) → Real))
    (hUopen : ∀ q : ι, IsOpen (sourceOpen q))
    (hcont :
      ∀ q : ι, ContinuousOn (D.chartTransition q) (sourceOpen q))
    (hVopen : ∀ q : ι, IsOpen (targetOpen q))
    (hVsubset : D.TargetOpenSubsetIccField targetOpen)
    (hIcc_source :
      ∀ q : ι, Icc (D.sourceLower q) (D.sourceUpper q) ⊆ sourceOpen q)
    (himage : D.ImageSubsetTargetOpenField targetOpen) :
    D.ChartTransitionMapsToField := by
  intro q
  exact
    ManifoldForm.chartTransition_mapsTo_halfSpaceSupportBox_of_chartBoxOpenNeighborhood
      (I := I) (x0 := D.sourceChart q) (x1 := D.targetChart q)
      (a := D.sourceLower q) (b := D.sourceUpper q)
      (c := D.targetLower q) (d := D.targetUpper q)
      (V := targetOpen q)
      (hVsubset q)
      (D.preimageChartBoxOpenNeighborhoodOfContinuousOnImageSubset
        sourceOpen targetOpen hUopen hcont hVopen hIcc_source himage q)

end CoverIndexedFiniteBoxImageControlData

section BoundaryCenterSpecialization

variable {ω : ManifoldForm I M n}
variable {P : SupportControlledSelectedPartition C}
variable {μBulk : Measure (Fin (n + 1) → Real)}

namespace CoverIndexedBoundaryTargetBoxData

/--
The current one-box-per-boundary-center target-box data as a finite image
control family.  Later finite refinements should use
`CoverIndexedFiniteBoxImageControlData` directly with their refined index type.
-/
def toFiniteBoxImageControlData
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω) :
    CoverIndexedFiniteBoxImageControlData
      (I := I) (K := K) C {x : M // x ∈ C.boundaryCenters} where
  owner := id
  targetChart := D.targetChart
  sourceLower := fun i => C.boundaryLower i.1
  sourceUpper := fun i => C.boundaryUpper i.1
  targetLower := D.targetLower
  targetUpper := D.targetUpper

/-- Endpoint-shaped ambient `MapsTo` field from finite-image-control data in
the current one-box-per-boundary-center specialization. -/
theorem chartTransitionMapsToField_of_finite_closed_preimage_shrink
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)
    (hpre :
      (D.toFiniteBoxImageControlData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)).ClosedPreimageShrinkField) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (D.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (D.targetLower i) (D.targetUpper i)) := by
  have hmaps :
      CoverIndexedFiniteBoxImageControlData.ChartTransitionMapsToField
        (D.toFiniteBoxImageControlData
          (I := I) (K := K) (C := C) (P := P) (ω := ω)) :=
    CoverIndexedFiniteBoxImageControlData.chartTransition_mapsTo_of_closed_preimage_shrink
      (D.toFiniteBoxImageControlData
        (I := I) (K := K) (C := C) (P := P) (ω := ω))
      hpre
  simpa [toFiniteBoxImageControlData,
    CoverIndexedFiniteBoxImageControlData.ChartTransitionMapsToField,
    CoverIndexedFiniteBoxImageControlData.chartTransition,
    CoverIndexedFiniteBoxImageControlData.sourceChart] using hmaps

/-- Boundary-target-box version of finite open-preimage image control. -/
theorem chartTransitionMapsToField_of_finite_open_preimage_shrink
    [IsManifold I ⊤ M]
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)
    (sourceOpen targetOpen :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hUopen :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (sourceOpen i))
    (hUtarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        sourceOpen i ⊆ (extChartAt I (C.boundaryChart i.1)).target)
    (hUoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        sourceOpen i ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (D.targetChart i))
    (hVopen :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (targetOpen i))
    (hVsubset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetOpen i ⊆ Icc (D.targetLower i) (D.targetUpper i))
    (hbox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          sourceOpen i ∩
            (ManifoldForm.chartTransition I
              (C.boundaryChart i.1) (D.targetChart i)) ⁻¹'
              targetOpen i) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (D.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (D.targetLower i) (D.targetUpper i)) := by
  have hmaps :
      CoverIndexedFiniteBoxImageControlData.ChartTransitionMapsToField
        (D.toFiniteBoxImageControlData
          (I := I) (K := K) (C := C) (P := P) (ω := ω)) :=
    CoverIndexedFiniteBoxImageControlData.chartTransition_mapsTo_of_open_preimage_shrink
      (D.toFiniteBoxImageControlData
        (I := I) (K := K) (C := C) (P := P) (ω := ω))
      sourceOpen targetOpen hUopen hUtarget hUoverlap
      hVopen hVsubset hbox
  simpa [toFiniteBoxImageControlData,
    CoverIndexedFiniteBoxImageControlData.ChartTransitionMapsToField,
    CoverIndexedFiniteBoxImageControlData.OpenPreimageShrinkField,
    CoverIndexedFiniteBoxImageControlData.TargetOpenSubsetIccField,
    CoverIndexedFiniteBoxImageControlData.chartTransition,
    CoverIndexedFiniteBoxImageControlData.sourceChart] using hmaps

/-- Boundary-target-box version of finite `ContinuousOn + image_subset`
control. -/
theorem chartTransitionMapsToField_of_finite_continuousOn_image_subset
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)
    (sourceOpen targetOpen :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hUopen :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (sourceOpen i))
    (hcont :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContinuousOn
          (ManifoldForm.chartTransition I
            (C.boundaryChart i.1) (D.targetChart i))
          (sourceOpen i))
    (hVopen :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (targetOpen i))
    (hVsubset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetOpen i ⊆ Icc (D.targetLower i) (D.targetUpper i))
    (hIcc_source :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆ sourceOpen i)
    (himage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (D.targetChart i)) ''
          Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          targetOpen i) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (D.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (D.targetLower i) (D.targetUpper i)) := by
  have hmaps :
      CoverIndexedFiniteBoxImageControlData.ChartTransitionMapsToField
        (D.toFiniteBoxImageControlData
          (I := I) (K := K) (C := C) (P := P) (ω := ω)) :=
    CoverIndexedFiniteBoxImageControlData.chartTransition_mapsTo_of_continuousOn_image_subset
      (D.toFiniteBoxImageControlData
        (I := I) (K := K) (C := C) (P := P) (ω := ω))
      sourceOpen targetOpen hUopen hcont hVopen hVsubset
      hIcc_source himage
  simpa [toFiniteBoxImageControlData,
    CoverIndexedFiniteBoxImageControlData.ChartTransitionMapsToField,
    CoverIndexedFiniteBoxImageControlData.ImageSubsetTargetOpenField,
    CoverIndexedFiniteBoxImageControlData.TargetOpenSubsetIccField,
    CoverIndexedFiniteBoxImageControlData.chartTransition,
    CoverIndexedFiniteBoxImageControlData.sourceChart] using hmaps

end CoverIndexedBoundaryTargetBoxData

namespace CoverIndexedZeroCompactFinalNaturalBaseInput

/-- Convert a finite-control closed-preimage field into the final ambient
`MapsTo` input. -/
def toMapsToInputOfFiniteClosedPreimageShrink
    (D :
      CoverIndexedZeroCompactFinalNaturalBaseInput
        (I := I) (K := K) C P ω μBulk)
    (hpre :
      (D.targetData.targetBox.toFiniteBoxImageControlData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)).ClosedPreimageShrinkField) :
    CoverIndexedZeroCompactFinalNaturalMapsToInput
      (I := I) (K := K) C P ω μBulk where
  base := D
  chartTransition_mapsTo :=
    D.targetData.targetBox.chartTransitionMapsToField_of_finite_closed_preimage_shrink
      (I := I) (K := K) (C := C) (P := P) (ω := ω) hpre

/-- Convert finite open-preimage image control into the final ambient
`MapsTo` input. -/
def toMapsToInputOfFiniteOpenPreimageShrink
    [IsManifold I ⊤ M]
    (D :
      CoverIndexedZeroCompactFinalNaturalBaseInput
        (I := I) (K := K) C P ω μBulk)
    (sourceOpen targetOpen :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hUopen :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (sourceOpen i))
    (hUtarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        sourceOpen i ⊆ (extChartAt I (C.boundaryChart i.1)).target)
    (hUoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        sourceOpen i ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1)
            (D.targetData.targetBox.targetChart i))
    (hVopen :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (targetOpen i))
    (hVsubset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetOpen i ⊆
          Icc (D.targetData.targetBox.targetLower i)
            (D.targetData.targetBox.targetUpper i))
    (hbox :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          sourceOpen i ∩
            (ManifoldForm.chartTransition I
              (C.boundaryChart i.1)
              (D.targetData.targetBox.targetChart i)) ⁻¹'
              targetOpen i) :
    CoverIndexedZeroCompactFinalNaturalMapsToInput
      (I := I) (K := K) C P ω μBulk where
  base := D
  chartTransition_mapsTo :=
    D.targetData.targetBox.chartTransitionMapsToField_of_finite_open_preimage_shrink
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      sourceOpen targetOpen hUopen hUtarget hUoverlap
      hVopen hVsubset hbox

end CoverIndexedZeroCompactFinalNaturalBaseInput

end BoundaryCenterSpecialization

end CoverIndexedZeroCompactFiniteBoxImageControl

end Stokes

end
