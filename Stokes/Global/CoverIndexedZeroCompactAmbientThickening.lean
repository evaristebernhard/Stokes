import Stokes.Global.CoverIndexedZeroCompactPreimageShrink
import Stokes.Global.CoverIndexedZeroCompactSourceInnerOuterExistence

/-!
# Ambient half-space thickenings for compact zero Stokes

Boundary source-shrink data controls the lower-zero face through
`boundaryChartTransition`.  The compact zero endpoint needs a stronger ambient
statement: an actual half-space source box whose closed carrier lies in the
source chart target and in the source-to-target overlap.

This file records that honest geometric datum and connects it to the existing
inner/outer source-box API.  It deliberately does not claim that tangential
source-shrink data alone produces an ambient collar; the missing information is
the closed-box containment in the source chart target and chart overlap.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section AmbientThickeningSingleChart

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}

/--
Single-chart ambient collar data.

The `innerLower`/`innerUpper` box is the boundary-chart box already selected
for the local half-space piece.  The `sourceLower`/`sourceUpper` box is an
ambient thickening: an open collar neighborhood sits between the inner closed
box and this outer closed box, and the outer box lies in both the source chart
target and the source-to-target chart overlap.
-/
structure BoundaryChartAmbientThickeningData
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M)
    (innerLower innerUpper : Fin (n + 1) → Real) where
  /-- Lower corner of the ambient outer source box. -/
  sourceLower : Fin (n + 1) → Real
  /-- Upper corner of the ambient outer source box. -/
  sourceUpper : Fin (n + 1) → Real
  /-- Boundary convention for the ambient outer source box. -/
  sourceLower_zero : sourceLower 0 = 0
  /-- Coordinatewise order of the ambient outer source box. -/
  sourceLower_le_sourceUpper : sourceLower ≤ sourceUpper
  /-- The collar has positive normal thickness. -/
  normalUpper_pos : 0 < sourceUpper 0
  /-- Open collar between the inner closed box and the ambient outer box. -/
  sourceNeighborhood :
    InnerOuterChartBoxOpenSelection
      (extChartAt I x0).target innerLower innerUpper
      sourceLower sourceUpper
  /-- The ambient outer box lies in the source-to-target chart overlap. -/
  sourceBox_subset_overlap :
    Icc sourceLower sourceUpper ⊆ ManifoldForm.chartOverlap I x0 x1

namespace BoundaryChartAmbientThickeningData

variable {innerLower innerUpper : Fin (n + 1) → Real}
variable
    (D :
      BoundaryChartAmbientThickeningData
        I x0 x1 innerLower innerUpper)

/-- The inner closed box lies in the selected open collar. -/
theorem inner_Icc_subset_neighborhood :
    Icc innerLower innerUpper ⊆ D.sourceNeighborhood.neighborhood :=
  D.sourceNeighborhood.inner_Icc_subset_neighborhood

/-- The open collar lies in the ambient outer closed box. -/
theorem neighborhood_subset_outerSourceBox :
    D.sourceNeighborhood.neighborhood ⊆ Icc D.sourceLower D.sourceUpper :=
  D.sourceNeighborhood.neighborhood_subset_outerBox

/-- The ambient outer closed box lies in the source chart target. -/
theorem sourceBox_subset_sourceTarget :
    Icc D.sourceLower D.sourceUpper ⊆ (extChartAt I x0).target :=
  D.sourceNeighborhood.outerBox_subset_target

/-- The open collar lies in the source chart target. -/
theorem neighborhood_subset_sourceTarget :
    D.sourceNeighborhood.neighborhood ⊆ (extChartAt I x0).target :=
  D.sourceNeighborhood.neighborhood_subset_target

/-- The open collar lies in the source-to-target chart overlap. -/
theorem neighborhood_subset_overlap :
    D.sourceNeighborhood.neighborhood ⊆ ManifoldForm.chartOverlap I x0 x1 :=
  D.neighborhood_subset_outerSourceBox.trans D.sourceBox_subset_overlap

/-- The ambient outer closed box lies in the natural boundary chart domain. -/
theorem sourceBox_subset_boundaryChartDomain :
    Icc D.sourceLower D.sourceUpper ⊆ boundaryChartDomain I x0 x1 := by
  intro y hy
  exact ⟨D.sourceBox_subset_sourceTarget hy, D.sourceBox_subset_overlap hy⟩

/-- The ambient half-space support box lies in the natural boundary chart domain. -/
theorem halfSpaceSupportBox_subset_boundaryChartDomain :
    halfSpaceSupportBox D.sourceLower D.sourceUpper ⊆
      boundaryChartDomain I x0 x1 := by
  intro y hy
  exact
    D.sourceBox_subset_boundaryChartDomain
      (halfSpaceSupportBox_subset_Icc D.sourceLower D.sourceUpper hy)

/-- Points of the lower-zero face of the ambient outer box lie in the ambient
closed source box. -/
theorem boundaryInclusion_mem_sourceIcc
    {u : Fin n → Real}
    (hu : u ∈ lowerZeroFaceDomain D.sourceLower D.sourceUpper) :
    boundaryInclusion n u ∈ Icc D.sourceLower D.sourceUpper :=
  boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain
    D.sourceLower_zero D.sourceLower_le_sourceUpper hu

/-- Points of the lower-zero face of the ambient outer box lie in the natural
boundary chart domain. -/
theorem lowerZeroFace_subset_boundaryChartDomain :
    ∀ u ∈ lowerZeroFaceDomain D.sourceLower D.sourceUpper,
      boundaryInclusion n u ∈ boundaryChartDomain I x0 x1 := by
  intro u hu
  exact D.sourceBox_subset_boundaryChartDomain (D.boundaryInclusion_mem_sourceIcc hu)

/-- The single-chart ambient thickening is exactly the single-index source
inner/outer selection used by the cover-indexed API. -/
def toInnerOuterChartBoxOpenSelection :
    InnerOuterChartBoxOpenSelection
      (extChartAt I x0).target innerLower innerUpper
      D.sourceLower D.sourceUpper :=
  D.sourceNeighborhood

/--
Constructor from explicitly supplied ambient collar fields.

This is the minimal honest single-chart bridge: tangential source-shrink data
may provide useful inner corners, but the ambient collar/open-overlap facts are
separate inputs.
-/
def ofOpenNeighborhood
    (sourceLower sourceUpper : Fin (n + 1) → Real)
    (hzero : sourceLower 0 = 0)
    (hle : sourceLower ≤ sourceUpper)
    (hnormal : 0 < sourceUpper 0)
    (U : Set (Fin (n + 1) → Real))
    (hUopen : IsOpen U)
    (hinner : Icc innerLower innerUpper ⊆ U)
    (hUouter : U ⊆ Icc sourceLower sourceUpper)
    (houterTarget : Icc sourceLower sourceUpper ⊆ (extChartAt I x0).target)
    (houterOverlap :
      Icc sourceLower sourceUpper ⊆ ManifoldForm.chartOverlap I x0 x1) :
    BoundaryChartAmbientThickeningData I x0 x1 innerLower innerUpper where
  sourceLower := sourceLower
  sourceUpper := sourceUpper
  sourceLower_zero := hzero
  sourceLower_le_sourceUpper := hle
  normalUpper_pos := hnormal
  sourceNeighborhood :=
    InnerOuterChartBoxOpenSelection.ofOpenNeighborhood
      (target := (extChartAt I x0).target)
      (innerLower := innerLower) (innerUpper := innerUpper)
      (outerLower := sourceLower) (outerUpper := sourceUpper)
      U hUopen hinner hUouter houterTarget
  sourceBox_subset_overlap := houterOverlap

/-- Strict-box constructor: use `boxInteriorSupportBox sourceLower sourceUpper`
as the open collar. -/
def ofInnerSubsetBoxInterior
    (sourceLower sourceUpper : Fin (n + 1) → Real)
    (hzero : sourceLower 0 = 0)
    (hle : sourceLower ≤ sourceUpper)
    (hnormal : 0 < sourceUpper 0)
    (hinner :
      Icc innerLower innerUpper ⊆
        boxInteriorSupportBox sourceLower sourceUpper)
    (houterTarget : Icc sourceLower sourceUpper ⊆ (extChartAt I x0).target)
    (houterOverlap :
      Icc sourceLower sourceUpper ⊆ ManifoldForm.chartOverlap I x0 x1) :
    BoundaryChartAmbientThickeningData I x0 x1 innerLower innerUpper where
  sourceLower := sourceLower
  sourceUpper := sourceUpper
  sourceLower_zero := hzero
  sourceLower_le_sourceUpper := hle
  normalUpper_pos := hnormal
  sourceNeighborhood :=
    InnerOuterChartBoxOpenSelection.ofInnerSubsetBoxInterior
      (target := (extChartAt I x0).target)
      (innerLower := innerLower) (innerUpper := innerUpper)
      (outerLower := sourceLower) (outerUpper := sourceUpper)
      hinner houterTarget
  sourceBox_subset_overlap := houterOverlap

end BoundaryChartAmbientThickeningData

namespace BoundaryChartSourceShrinkMapsToData

variable {a b c d : Fin (n + 1) → Real} {u : Fin n → Real}

/--
Tangential source-shrink data can seed the inner corners of an ambient collar,
but it does not supply the ambient collar itself.  This constructor records the
remaining honest inputs.
-/
def toAmbientThickeningDataOfOpenNeighborhood
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (outerLower outerUpper : Fin (n + 1) → Real)
    (hzero : outerLower 0 = 0)
    (hle : outerLower ≤ outerUpper)
    (hnormal : 0 < outerUpper 0)
    (U : Set (Fin (n + 1) → Real))
    (hUopen : IsOpen U)
    (hinner :
      Icc D.sourceLowerCorner D.sourceUpperCorner ⊆ U)
    (hUouter : U ⊆ Icc outerLower outerUpper)
    (houterTarget : Icc outerLower outerUpper ⊆ (extChartAt I x0).target)
    (houterOverlap :
      Icc outerLower outerUpper ⊆ ManifoldForm.chartOverlap I x0 x1) :
    BoundaryChartAmbientThickeningData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner :=
  BoundaryChartAmbientThickeningData.ofOpenNeighborhood
    (I := I) (x0 := x0) (x1 := x1)
    (innerLower := D.sourceLowerCorner)
    (innerUpper := D.sourceUpperCorner)
    outerLower outerUpper hzero hle hnormal U hUopen hinner hUouter
    houterTarget houterOverlap

/--
Strict-box version of `toAmbientThickeningDataOfOpenNeighborhood`.
-/
def toAmbientThickeningDataOfBoxInterior
    (D : BoundaryChartSourceShrinkMapsToData I x0 x1 a b c d u)
    (outerLower outerUpper : Fin (n + 1) → Real)
    (hzero : outerLower 0 = 0)
    (hle : outerLower ≤ outerUpper)
    (hnormal : 0 < outerUpper 0)
    (hinner :
      Icc D.sourceLowerCorner D.sourceUpperCorner ⊆
        boxInteriorSupportBox outerLower outerUpper)
    (houterTarget : Icc outerLower outerUpper ⊆ (extChartAt I x0).target)
    (houterOverlap :
      Icc outerLower outerUpper ⊆ ManifoldForm.chartOverlap I x0 x1) :
    BoundaryChartAmbientThickeningData I x0 x1
      D.sourceLowerCorner D.sourceUpperCorner :=
  BoundaryChartAmbientThickeningData.ofInnerSubsetBoxInterior
    (I := I) (x0 := x0) (x1 := x1)
    (innerLower := D.sourceLowerCorner)
    (innerUpper := D.sourceUpperCorner)
    outerLower outerUpper hzero hle hnormal hinner houterTarget houterOverlap

end BoundaryChartSourceShrinkMapsToData

end AmbientThickeningSingleChart

section CoverIndexedAmbientThickening

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
Cover-indexed family of ambient boundary thickenings for arbitrary per-index
inner corners.
-/
structure CoverIndexedBoundaryAmbientThickeningData
    (C : CompactSupportChartCoverSelection I K)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (innerLower innerUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real) where
  /-- Single-chart ambient thickening at each boundary index. -/
  data :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      BoundaryChartAmbientThickeningData I
        (C.boundaryChart i.1) (targetChart i)
        (innerLower i) (innerUpper i)

/-- The specialization whose inner boxes are the selected boundary boxes of
the compact-support chart cover. -/
abbrev CoverIndexedSelectedBoundaryAmbientThickeningData
    (C : CompactSupportChartCoverSelection I K)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M) :=
  CoverIndexedBoundaryAmbientThickeningData
    (I := I) (K := K) C targetChart
    (fun i => C.boundaryLower i.1)
    (fun i => C.boundaryUpper i.1)

namespace CoverIndexedBoundaryAmbientThickeningData

variable {targetChart : {x : M // x ∈ C.boundaryCenters} → M}
variable
    {innerLower innerUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real}
    (D :
      CoverIndexedBoundaryAmbientThickeningData
        (I := I) (K := K) C targetChart innerLower innerUpper)

/-- Ambient outer lower corners. -/
def sourceLower :
    {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real :=
  fun i => (D.data i).sourceLower

/-- Ambient outer upper corners. -/
def sourceUpper :
    {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real :=
  fun i => (D.data i).sourceUpper

@[simp]
theorem sourceLower_apply (i : {x : M // x ∈ C.boundaryCenters}) :
    D.sourceLower i = (D.data i).sourceLower :=
  rfl

@[simp]
theorem sourceUpper_apply (i : {x : M // x ∈ C.boundaryCenters}) :
    D.sourceUpper i = (D.data i).sourceUpper :=
  rfl

/-- Per-index boundary convention for ambient outer boxes. -/
theorem sourceLower_zero (i : {x : M // x ∈ C.boundaryCenters}) :
    D.sourceLower i 0 = 0 :=
  (D.data i).sourceLower_zero

/-- Per-index coordinatewise order for ambient outer boxes. -/
theorem sourceLower_le_sourceUpper
    (i : {x : M // x ∈ C.boundaryCenters}) :
    D.sourceLower i ≤ D.sourceUpper i :=
  (D.data i).sourceLower_le_sourceUpper

/-- Per-index positive normal thickness. -/
theorem normalUpper_pos (i : {x : M // x ∈ C.boundaryCenters}) :
    0 < D.sourceUpper i 0 :=
  (D.data i).normalUpper_pos

/-- The selected open collar at each index. -/
def sourceNeighborhood
    (i : {x : M // x ∈ C.boundaryCenters}) :
    InnerOuterChartBoxOpenSelection
      (extChartAt I (C.boundaryChart i.1)).target
      (innerLower i) (innerUpper i)
      (D.sourceLower i) (D.sourceUpper i) :=
  (D.data i).sourceNeighborhood

@[simp]
theorem sourceNeighborhood_neighborhood
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (D.sourceNeighborhood i).neighborhood =
      (D.data i).sourceNeighborhood.neighborhood :=
  rfl

/-- Ambient outer boxes lie in the source chart targets. -/
theorem sourceBox_subset_sourceTarget
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Icc (D.sourceLower i) (D.sourceUpper i) ⊆
      (extChartAt I (C.boundaryChart i.1)).target :=
  (D.data i).sourceBox_subset_sourceTarget

/-- Ambient outer boxes lie in the source-to-target overlaps. -/
theorem sourceBox_subset_overlap
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Icc (D.sourceLower i) (D.sourceUpper i) ⊆
      ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i) :=
  (D.data i).sourceBox_subset_overlap

/-- Ambient half-space support boxes lie in the natural boundary chart domains. -/
theorem halfSpaceSupportBox_subset_boundaryChartDomain
    (i : {x : M // x ∈ C.boundaryCenters}) :
    halfSpaceSupportBox (D.sourceLower i) (D.sourceUpper i) ⊆
      boundaryChartDomain I (C.boundaryChart i.1) (targetChart i) :=
  (D.data i).halfSpaceSupportBox_subset_boundaryChartDomain

/-- Lower-zero faces of the ambient outer boxes lie in the natural boundary
chart domains. -/
theorem lowerZeroFace_subset_boundaryChartDomain
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ∀ u ∈ lowerZeroFaceDomain (D.sourceLower i) (D.sourceUpper i),
      boundaryInclusion n u ∈
        boundaryChartDomain I (C.boundaryChart i.1) (targetChart i) :=
  (D.data i).lowerZeroFace_subset_boundaryChartDomain

/-- Constructor from explicitly supplied per-index ambient collar fields. -/
def ofOpenNeighborhoods
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, sourceLower i 0 = 0)
    (hle :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, sourceLower i ≤ sourceUpper i)
    (hnormal :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, 0 < sourceUpper i 0)
    (U :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hUopen :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (U i))
    (hinner :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (innerLower i) (innerUpper i) ⊆ U i)
    (hUouter :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        U i ⊆ Icc (sourceLower i) (sourceUpper i))
    (houterTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (houterOverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedBoundaryAmbientThickeningData
      (I := I) (K := K) C targetChart innerLower innerUpper where
  data := fun i =>
    BoundaryChartAmbientThickeningData.ofOpenNeighborhood
      (I := I) (x0 := C.boundaryChart i.1) (x1 := targetChart i)
      (innerLower := innerLower i) (innerUpper := innerUpper i)
      (sourceLower i) (sourceUpper i) (hzero i) (hle i) (hnormal i)
      (U i) (hUopen i) (hinner i) (hUouter i)
      (houterTarget i) (houterOverlap i)

/-- Constructor from strict per-index ambient collars. -/
def ofBoxInteriors
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, sourceLower i 0 = 0)
    (hle :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, sourceLower i ≤ sourceUpper i)
    (hnormal :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, 0 < sourceUpper i 0)
    (hinner :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (innerLower i) (innerUpper i) ⊆
          boxInteriorSupportBox (sourceLower i) (sourceUpper i))
    (houterTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (houterOverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedBoundaryAmbientThickeningData
      (I := I) (K := K) C targetChart innerLower innerUpper where
  data := fun i =>
    BoundaryChartAmbientThickeningData.ofInnerSubsetBoxInterior
      (I := I) (x0 := C.boundaryChart i.1) (x1 := targetChart i)
      (innerLower := innerLower i) (innerUpper := innerUpper i)
      (sourceLower i) (sourceUpper i) (hzero i) (hle i) (hnormal i)
      (hinner i) (houterTarget i) (houterOverlap i)

end CoverIndexedBoundaryAmbientThickeningData

namespace CoverIndexedSelectedBoundaryAmbientThickeningData

variable {targetChart : {x : M // x ∈ C.boundaryCenters} → M}
variable
    (D :
      CoverIndexedSelectedBoundaryAmbientThickeningData
        (I := I) (K := K) C targetChart)

/-- Selected-cover ambient thickening as the existing inner/outer source-box
selection. -/
def toInnerOuterSourceBoxSelection :
    CoverIndexedInnerOuterSourceBoxSelection
      (I := I) (K := K) C targetChart where
  sourceLower := D.sourceLower
  sourceUpper := D.sourceUpper
  sourceNeighborhood := D.sourceNeighborhood
  sourceBox_subset_overlap := D.sourceBox_subset_overlap

@[simp]
theorem toInnerOuterSourceBoxSelection_sourceLower :
    D.toInnerOuterSourceBoxSelection.sourceLower = D.sourceLower :=
  rfl

@[simp]
theorem toInnerOuterSourceBoxSelection_sourceUpper :
    D.toInnerOuterSourceBoxSelection.sourceUpper = D.sourceUpper :=
  rfl

@[simp]
theorem toInnerOuterSourceBoxSelection_sourceNeighborhood
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (D.toInnerOuterSourceBoxSelection.sourceNeighborhood i).neighborhood =
      (D.sourceNeighborhood i).neighborhood :=
  rfl

/-- Transition-neighborhood package generated from the ambient thickening. -/
def toBoundaryTransitionBoxNeighborhoods :
    CoverIndexedBoundaryTransitionBoxNeighborhoods
      (I := I) (K := K) C targetChart :=
  D.toInnerOuterSourceBoxSelection.toBoundaryTransitionBoxNeighborhoods

@[simp]
theorem toBoundaryTransitionBoxNeighborhoods_boundaryNeighborhood :
    D.toBoundaryTransitionBoxNeighborhoods.boundaryNeighborhood =
      fun i => (D.sourceNeighborhood i).neighborhood :=
  rfl

/-- The generated transition neighborhoods lie in the concrete chart-transition source. -/
theorem toBoundaryTransitionBoxNeighborhoods_subset_chartTransitionSource
    (i : {x : M // x ∈ C.boundaryCenters}) :
    D.toBoundaryTransitionBoxNeighborhoods.boundaryNeighborhood i ⊆
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (targetChart i) :=
  D.toInnerOuterSourceBoxSelection
    |>.toBoundaryTransitionBoxNeighborhoods_subset_chartTransitionSource
      (I := I) (K := K) (C := C) i

/-- If an existing smooth-neighborhood package uses the same boundary
neighborhoods, the ambient thickening supplies the transition-source field. -/
theorem boundaryNeighborhoodSubsetTransitionSource
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (htarget :
      transitionSupportData.targetChart = targetChart)
    (hneighborhood :
      neighborhoodData.boundaryNeighborhood =
        fun i => (D.sourceNeighborhood i).neighborhood) :
    CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (K := K) neighborhoodData transitionSupportData := by
  subst htarget
  exact
    neighborhoodData.boundaryNeighborhoodSubsetTransitionSource_of_innerOuterSourceBox
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData D.toInnerOuterSourceBoxSelection hneighborhood

/-- Ambient thickening plus a target-open preimage shrink gives the ambient
whole-half-space chart-transition `MapsTo` field. -/
theorem chartTransition_mapsTo_of_targetOpen_preimage_shrink
    [IsManifold I ⊤ M]
    (targetOpen :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (targetOpen_open :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (targetOpen i))
    (targetOpen_subset_Icc :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetOpen i ⊆ Icc (targetLower i) (targetUpper i))
    (sourceIcc_subset_preimage :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          (D.sourceNeighborhood i).neighborhood ∩
            (ManifoldForm.chartTransition I
              (C.boundaryChart i.1) (targetChart i)) ⁻¹'
              targetOpen i) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (targetLower i) (targetUpper i)) := by
  exact
    D.toInnerOuterSourceBoxSelection
      |>.chartTransition_mapsTo_of_targetOpen_preimage_shrink
        (I := I) (K := K) (C := C) (targetChart := targetChart)
        targetOpen targetLower targetUpper
        targetOpen_open targetOpen_subset_Icc
        (by
          intro i
          simpa using sourceIcc_subset_preimage i)

end CoverIndexedSelectedBoundaryAmbientThickeningData

namespace CoverIndexedBoundarySourceShrinkMapsToData

variable {targetChart : {x : M // x ∈ C.boundaryCenters} → M}
variable
    {targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real}
    (D :
      CoverIndexedBoundarySourceShrinkMapsToData
        (I := I) (K := K) C targetChart targetLower targetUpper)

/--
The cover-indexed source-shrink route can provide the inner boundary-face
corners for an ambient thickening.  The ambient outer box and overlap
containments remain explicit.
-/
def toAmbientThickeningDataOfOpenNeighborhoods
    (outerLower outerUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, outerLower i 0 = 0)
    (hle :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, outerLower i ≤ outerUpper i)
    (hnormal :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, 0 < outerUpper i 0)
    (U :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hUopen :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (U i))
    (hinner :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.sourceLower i) (D.sourceUpper i) ⊆ U i)
    (hUouter :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        U i ⊆ Icc (outerLower i) (outerUpper i))
    (houterTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (outerLower i) (outerUpper i) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (houterOverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (outerLower i) (outerUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedBoundaryAmbientThickeningData
      (I := I) (K := K) C targetChart D.sourceLower D.sourceUpper :=
  CoverIndexedBoundaryAmbientThickeningData.ofOpenNeighborhoods
    (I := I) (K := K) (C := C) (targetChart := targetChart)
    (innerLower := D.sourceLower) (innerUpper := D.sourceUpper)
    outerLower outerUpper hzero hle hnormal U hUopen hinner hUouter
    houterTarget houterOverlap

/-- Strict-box version of `toAmbientThickeningDataOfOpenNeighborhoods`. -/
def toAmbientThickeningDataOfBoxInteriors
    (outerLower outerUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (hzero :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, outerLower i 0 = 0)
    (hle :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, outerLower i ≤ outerUpper i)
    (hnormal :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, 0 < outerUpper i 0)
    (hinner :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.sourceLower i) (D.sourceUpper i) ⊆
          boxInteriorSupportBox (outerLower i) (outerUpper i))
    (houterTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (outerLower i) (outerUpper i) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (houterOverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (outerLower i) (outerUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedBoundaryAmbientThickeningData
      (I := I) (K := K) C targetChart D.sourceLower D.sourceUpper :=
  CoverIndexedBoundaryAmbientThickeningData.ofBoxInteriors
    (I := I) (K := K) (C := C) (targetChart := targetChart)
    (innerLower := D.sourceLower) (innerUpper := D.sourceUpper)
    outerLower outerUpper hzero hle hnormal hinner houterTarget houterOverlap

end CoverIndexedBoundarySourceShrinkMapsToData

end CoverIndexedAmbientThickening

end Stokes

end
