import Stokes.Global.CoverIndexedZeroCompactInnerOuterBoxSelection
import Stokes.Global.StrictInnerOuterBox
import Stokes.BoundaryChart.SourceShrinkMapsToAuto

/-!
# Source inner/outer existence constructors for compact zero Stokes

This file is the source-side constructor layer for the compact zero route.
It turns the mathematically natural shrink data

`Icc_inner ⊆ U ⊆ Icc_outer ⊆ chart overlap`

into `CoverIndexedInnerOuterSourceBoxSelection`.

The last section also records how the existing boundary-chart source-shrink
records can supply the source corner fields.  They do not, by themselves,
prove the ambient `Icc_outer ⊆ chartOverlap` fact: source-shrink maps-to data
controls the lower-zero boundary face.  The cover-indexed constructor therefore
keeps the ambient target/overlap containment as honest fields.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoxInteriorNeighborhood

variable {n : Nat}

/-- The strict coordinate box is open in the ambient finite-dimensional
coordinate space. -/
theorem isOpen_boxInteriorSupportBox
    (a b : Fin (n + 1) → Real) :
    IsOpen (boxInteriorSupportBox a b) := by
  rw [boxInteriorSupportBox, setOf_forall]
  refine isOpen_iInter_of_finite (ι := Fin (n + 1)) ?_
  intro i
  exact
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)

/-- The strict coordinate box is contained in the corresponding closed box. -/
theorem boxInteriorSupportBox_subset_Icc
    (a b : Fin (n + 1) → Real) :
    boxInteriorSupportBox a b ⊆ Icc a b := by
  intro y hy
  constructor
  · intro i
    exact le_of_lt (hy i).1
  · intro i
    exact le_of_lt (hy i).2

namespace InnerOuterChartBoxOpenSelection

variable {target : Set (Fin (n + 1) → Real)}
variable {innerLower innerUpper outerLower outerUpper : Fin (n + 1) → Real}

/-- Use the strict outer coordinate box itself as the intermediate open
neighborhood. -/
def ofInnerSubsetBoxInterior
    (hinner :
      Icc innerLower innerUpper ⊆
        boxInteriorSupportBox outerLower outerUpper)
    (houterTarget : Icc outerLower outerUpper ⊆ target) :
    InnerOuterChartBoxOpenSelection
      target innerLower innerUpper outerLower outerUpper :=
  InnerOuterChartBoxOpenSelection.ofOpenNeighborhood
    (target := target)
    (innerLower := innerLower) (innerUpper := innerUpper)
    (outerLower := outerLower) (outerUpper := outerUpper)
    (boxInteriorSupportBox outerLower outerUpper)
    (isOpen_boxInteriorSupportBox outerLower outerUpper)
    hinner
    (boxInteriorSupportBox_subset_Icc outerLower outerUpper)
    houterTarget

@[simp]
theorem ofInnerSubsetBoxInterior_neighborhood
    (hinner :
      Icc innerLower innerUpper ⊆
        boxInteriorSupportBox outerLower outerUpper)
    (houterTarget : Icc outerLower outerUpper ⊆ target) :
    (ofInnerSubsetBoxInterior
      (target := target)
      (innerLower := innerLower) (innerUpper := innerUpper)
      (outerLower := outerLower) (outerUpper := outerUpper)
      hinner houterTarget).neighborhood =
        boxInteriorSupportBox outerLower outerUpper := by
  rfl

end InnerOuterChartBoxOpenSelection

end BoxInteriorNeighborhood

section CoverIndexedSourceInnerOuterExistence

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {targetChart : {x : M // x ∈ C.boundaryCenters} → M}

namespace CoverIndexedInnerOuterSourceBoxSelection

/-- Direct constructor from the natural per-index data
`Icc_inner ⊆ U ⊆ Icc_outer ⊆ target` plus
`Icc_outer ⊆ chartOverlap`. -/
def ofOpenNeighborhoods
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (U : {x : M // x ∈ C.boundaryCenters} →
      Set (Fin (n + 1) → Real))
    (hUopen :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (U i))
    (hinner :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆ U i)
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
    CoverIndexedInnerOuterSourceBoxSelection
      (I := I) (K := K) C targetChart where
  sourceLower := sourceLower
  sourceUpper := sourceUpper
  sourceNeighborhood := fun i =>
    InnerOuterChartBoxOpenSelection.ofOpenNeighborhood
      (target := (extChartAt I (C.boundaryChart i.1)).target)
      (innerLower := C.boundaryLower i.1)
      (innerUpper := C.boundaryUpper i.1)
      (outerLower := sourceLower i)
      (outerUpper := sourceUpper i)
      (U i) (hUopen i) (hinner i) (hUouter i) (houterTarget i)
  sourceBox_subset_overlap := houterOverlap

@[simp]
theorem ofOpenNeighborhoods_sourceLower
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (U : {x : M // x ∈ C.boundaryCenters} →
      Set (Fin (n + 1) → Real))
    (hUopen :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (U i))
    (hinner :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆ U i)
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
    (ofOpenNeighborhoods
      (I := I) (K := K) (C := C) (targetChart := targetChart)
      sourceLower sourceUpper U hUopen hinner hUouter houterTarget
      houterOverlap).sourceLower = sourceLower := by
  rfl

@[simp]
theorem ofOpenNeighborhoods_sourceNeighborhood
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (U : {x : M // x ∈ C.boundaryCenters} →
      Set (Fin (n + 1) → Real))
    (hUopen :
      ∀ i : {x : M // x ∈ C.boundaryCenters}, IsOpen (U i))
    (hinner :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆ U i)
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
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ((ofOpenNeighborhoods
      (I := I) (K := K) (C := C) (targetChart := targetChart)
      sourceLower sourceUpper U hUopen hinner hUouter houterTarget
      houterOverlap).sourceNeighborhood i).neighborhood = U i := by
  rfl

/-- Constructor from strict inner/outer containment, using
`boxInteriorSupportBox sourceLower sourceUpper` as the open neighborhood. -/
def ofInnerSubsetBoxInterior
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (hinnerInterior :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          boxInteriorSupportBox (sourceLower i) (sourceUpper i))
    (houterTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (houterOverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedInnerOuterSourceBoxSelection
      (I := I) (K := K) C targetChart where
  sourceLower := sourceLower
  sourceUpper := sourceUpper
  sourceNeighborhood := fun i =>
    InnerOuterChartBoxOpenSelection.ofInnerSubsetBoxInterior
      (target := (extChartAt I (C.boundaryChart i.1)).target)
      (innerLower := C.boundaryLower i.1)
      (innerUpper := C.boundaryUpper i.1)
      (outerLower := sourceLower i)
      (outerUpper := sourceUpper i)
      (hinnerInterior i) (houterTarget i)
  sourceBox_subset_overlap := houterOverlap

@[simp]
theorem ofInnerSubsetBoxInterior_sourceNeighborhood
    (sourceLower sourceUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (hinnerInterior :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          boxInteriorSupportBox (sourceLower i) (sourceUpper i))
    (houterTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (houterOverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (sourceLower i) (sourceUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ((CoverIndexedInnerOuterSourceBoxSelection.ofInnerSubsetBoxInterior
      (I := I) (K := K) (C := C) (targetChart := targetChart)
      sourceLower sourceUpper hinnerInterior houterTarget houterOverlap).sourceNeighborhood
      i).neighborhood =
        boxInteriorSupportBox (sourceLower i) (sourceUpper i) := by
  rfl

/-- Active strict inner/outer selections can be used as source inner/outer data
when their active inner boxes are the already selected boundary boxes. -/
def ofActiveStrictInnerOuter
    {coordSupport : M → Set (Fin (n + 1) → Real)}
    (D :
      ActiveStrictInnerOuterBoxSelections
        C.boundaryCenters coordSupport)
    (hinnerLower :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        D.innerLower i.1 = C.boundaryLower i.1)
    (hinnerUpper :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        D.innerUpper i.1 = C.boundaryUpper i.1)
    (houterTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.outerLower i.1) (D.outerUpper i.1) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (houterOverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.outerLower i.1) (D.outerUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedInnerOuterSourceBoxSelection
      (I := I) (K := K) C targetChart :=
  ofInnerSubsetBoxInterior
    (I := I) (K := K) (C := C) (targetChart := targetChart)
    (fun i => D.outerLower i.1) (fun i => D.outerUpper i.1)
    (by
      intro i
      simpa [hinnerLower i, hinnerUpper i] using
        (D.innerIcc_subset_outerInterior i.1 i.2))
    houterTarget houterOverlap

end CoverIndexedInnerOuterSourceBoxSelection

/-! ## Boundary-chart source-shrink source corners -/

/-- Cover-indexed family of boundary-chart source-shrink `MapsTo` data.

This record exposes the source corners selected by the boundary-chart
source-shrink route.  It intentionally does not claim ambient source-box
containment: the underlying data only controls the lower-zero face. -/
structure CoverIndexedBoundarySourceShrinkMapsToData
    (C : CompactSupportChartCoverSelection I K)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real) where
  /-- Tangential source point used to select the shrunken lower-zero face. -/
  sourcePoint : {x : M // x ∈ C.boundaryCenters} → Fin n → Real
  /-- Per-boundary-index source-shrink maps-to data. -/
  data :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      BoundaryChartSourceShrinkMapsToData I
        (C.boundaryChart i.1) (targetChart i)
        (C.boundaryLower i.1) (C.boundaryUpper i.1)
        (targetLower i) (targetUpper i) (sourcePoint i)

namespace CoverIndexedBoundarySourceShrinkMapsToData

variable
    {targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real}
    (D :
      CoverIndexedBoundarySourceShrinkMapsToData
        (I := I) (K := K) C targetChart targetLower targetUpper)

/-- Lower corners selected by the boundary-chart source-shrink route. -/
def sourceLower :
    {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real :=
  fun i => (D.data i).sourceLowerCorner

/-- Upper corners selected by the boundary-chart source-shrink route. -/
def sourceUpper :
    {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real :=
  fun i => (D.data i).sourceUpperCorner

/-- The lower-zero source faces map into the selected target faces. -/
theorem mapsTo_target
    (i : {x : M // x ∈ C.boundaryCenters}) :
    MapsTo
      (boundaryChartTransition I (C.boundaryChart i.1) (targetChart i))
      (lowerZeroFaceDomain (D.sourceLower i) (D.sourceUpper i))
      (lowerZeroFaceDomain (targetLower i) (targetUpper i)) := by
  simpa [sourceLower, sourceUpper] using (D.data i).mapsTo_target

/-- The selected lower-zero source face is contained in the original lower-zero
face from the compact-support chart cover. -/
theorem lowerZeroFace_subset_original
    (i : {x : M // x ∈ C.boundaryCenters}) :
    lowerZeroFaceDomain (D.sourceLower i) (D.sourceUpper i) ⊆
      lowerZeroFaceDomain (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  simpa [sourceLower, sourceUpper] using (D.data i).sourceSubset_original

/-- Use source-shrink-selected source corners as the outer source box for the
cover-indexed inner/outer source selection, once the missing ambient source
neighborhood and overlap facts have been supplied. -/
def toInnerOuterSourceBoxSelectionOfAmbient
    (sourceNeighborhood :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        InnerOuterChartBoxOpenSelection
          (extChartAt I (C.boundaryChart i.1)).target
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (D.sourceLower i) (D.sourceUpper i))
    (houterOverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.sourceLower i) (D.sourceUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedInnerOuterSourceBoxSelection
      (I := I) (K := K) C targetChart where
  sourceLower := D.sourceLower
  sourceUpper := D.sourceUpper
  sourceNeighborhood := sourceNeighborhood
  sourceBox_subset_overlap := houterOverlap

/-- Strict-box version of
`toInnerOuterSourceBoxSelectionOfAmbient`, using the source-shrink-selected
source corners and the strict coordinate box as the intermediate open
neighborhood. -/
def toInnerOuterSourceBoxSelectionOfBoxInterior
    (hinnerInterior :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          boxInteriorSupportBox (D.sourceLower i) (D.sourceUpper i))
    (houterTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.sourceLower i) (D.sourceUpper i) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (houterOverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Icc (D.sourceLower i) (D.sourceUpper i) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedInnerOuterSourceBoxSelection
      (I := I) (K := K) C targetChart :=
  CoverIndexedInnerOuterSourceBoxSelection.ofInnerSubsetBoxInterior
    (I := I) (K := K) (C := C) (targetChart := targetChart)
    D.sourceLower D.sourceUpper hinnerInterior houterTarget houterOverlap

end CoverIndexedBoundarySourceShrinkMapsToData

end CoverIndexedSourceInnerOuterExistence

end Stokes

end
