import Stokes.Global.CoverIndexedZeroCompactTargetImageContainment
import Stokes.Global.CoverIndexedZeroCompactSourceShrinkSelection

/-!
# Chart-transition shrink for compact zero endpoints

This file isolates the honest geometric shrink used by the compact-support
relative Stokes endpoint.

The downstream target-support theorem wants a pointwise `MapsTo` statement on
the selected half-space support box.  The useful way to obtain it is to shrink
the selected closed source box inside a preimage of a target coordinate box (or
inside an open target neighborhood contained in that box).  The lemmas below
package exactly that route, including the continuity-open-preimage step for
chart transitions on an explicitly chosen source neighborhood.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroCompactChartTransitionShrink

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

namespace ManifoldForm

/-- Continuity-open-preimage form for a chart transition on an explicitly
chosen source neighborhood.  The neighborhood is required to lie in the source
chart target and in the source-to-target overlap, which is the honest
manifold-with-boundary replacement for assuming a globally open transition
source. -/
theorem chartTransition_isOpen_inter_preimage
    [IsManifold I ⊤ M]
    {x0 x1 : M} {U V : Set (Fin (n + 1) → Real)}
    (hUopen : IsOpen U)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ chartOverlap I x0 x1)
    (hVopen : IsOpen V) :
    IsOpen (U ∩ (chartTransition I x0 x1) ⁻¹' V) := by
  have hcont : ContinuousOn (chartTransition I x0 x1) U :=
    (contDiffOn_chartTransition (I := I) (x0 := x0) (x1 := x1)
      hUtarget hUoverlap).continuousOn
  exact hcont.isOpen_inter_preimage hUopen hVopen

/-- Build a `ChartBoxOpenNeighborhood` inside a chart-transition preimage from
an open source neighborhood and an open target neighborhood.  This is the
formal shrink produced by continuity once the selected closed source box has
been placed inside `U ∩ chartTransition ⁻¹' V`. -/
def chartTransition_preimageChartBoxOpenNeighborhood
    [IsManifold I ⊤ M]
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    {U V : Set (Fin (n + 1) → Real)}
    (hUopen : IsOpen U)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ chartOverlap I x0 x1)
    (hVopen : IsOpen V)
    (hbox :
      Icc a b ⊆ U ∩ (chartTransition I x0 x1) ⁻¹' V) :
    ChartBoxOpenNeighborhood ((chartTransition I x0 x1) ⁻¹' V) a b where
  neighborhood := U ∩ (chartTransition I x0 x1) ⁻¹' V
  isOpen_neighborhood :=
    chartTransition_isOpen_inter_preimage
      (I := I) (x0 := x0) (x1 := x1)
      hUopen hUtarget hUoverlap hVopen
  Icc_subset_neighborhood := hbox
  neighborhood_subset_target := by
    intro y hy
    exact hy.2

/-- If the selected closed source box is contained in the preimage of a target
closed coordinate box, then the stricter half-space support box maps into that
target box. -/
theorem chartTransition_mapsTo_halfSpaceSupportBox_of_Icc_subset_preimage
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hpre :
      Icc a b ⊆ (chartTransition I x0 x1) ⁻¹' Icc c d) :
    MapsTo (chartTransition I x0 x1)
      (halfSpaceSupportBox a b) (Icc c d) := by
  intro y hy
  exact hpre (halfSpaceSupportBox_subset_Icc a b hy)

/-- `ChartBoxOpenNeighborhood` spelling of
`chartTransition_mapsTo_halfSpaceSupportBox_of_Icc_subset_preimage`.  This is
the form consumed directly by chart-box shrink selections. -/
theorem chartTransition_mapsTo_halfSpaceSupportBox_of_chartBoxOpenNeighborhood
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    {V : Set (Fin (n + 1) → Real)}
    (hVsubset : V ⊆ Icc c d)
    (nbr :
      ChartBoxOpenNeighborhood
        ((chartTransition I x0 x1) ⁻¹' V) a b) :
    MapsTo (chartTransition I x0 x1)
      (halfSpaceSupportBox a b) (Icc c d) := by
  refine
    chartTransition_mapsTo_halfSpaceSupportBox_of_Icc_subset_preimage
      (I := I) (x0 := x0) (x1 := x1)
      (a := a) (b := b) (c := c) (d := d) ?_
  intro y hy
  exact hVsubset (nbr.neighborhood_subset_target (nbr.Icc_subset_neighborhood hy))

/-- Open-neighborhood shrink version: if a selected source closed box has been
shrunk inside an open source neighborhood and the preimage of an open target
neighborhood contained in the desired target `Icc`, then the half-space support
box maps into that target `Icc`. -/
theorem chartTransition_mapsTo_halfSpaceSupportBox_of_open_preimage_shrink
    [IsManifold I ⊤ M]
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    {U V : Set (Fin (n + 1) → Real)}
    (hUopen : IsOpen U)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ chartOverlap I x0 x1)
    (hVopen : IsOpen V)
    (hVsubset : V ⊆ Icc c d)
    (hbox :
      Icc a b ⊆ U ∩ (chartTransition I x0 x1) ⁻¹' V) :
    MapsTo (chartTransition I x0 x1)
      (halfSpaceSupportBox a b) (Icc c d) :=
  chartTransition_mapsTo_halfSpaceSupportBox_of_chartBoxOpenNeighborhood
    (I := I) (x0 := x0) (x1 := x1)
    (a := a) (b := b) (c := c) (d := d)
    hVsubset
    (chartTransition_preimageChartBoxOpenNeighborhood
      (I := I) (x0 := x0) (x1 := x1)
      (a := a) (b := b)
      hUopen hUtarget hUoverlap hVopen hbox)

end ManifoldForm

variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTransitionBoxNeighborhoods

variable {targetChart : {x : M // x ∈ C.boundaryCenters} → M}

/-- Cover-indexed shrink from transition neighborhoods: if each chosen
source-side transition neighborhood lies in the preimage of the selected target
box, then the selected half-space source support box maps into that target
box. -/
theorem chartTransition_mapsTo_halfSpaceSupportBox_of_boundaryNeighborhood_subset_preimage
    (nbrs :
      CoverIndexedBoundaryTransitionBoxNeighborhoods
        (I := I) (K := K) C targetChart)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (hpre :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.boundaryNeighborhood i ⊆
          (ManifoldForm.chartTransition I
            (C.boundaryChart i.1) (targetChart i)) ⁻¹'
            Icc (targetLower i) (targetUpper i)) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (targetLower i) (targetUpper i)) := by
  intro i
  exact
    ManifoldForm.chartTransition_mapsTo_halfSpaceSupportBox_of_Icc_subset_preimage
      (I := I) (x0 := C.boundaryChart i.1) (x1 := targetChart i)
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (c := targetLower i) (d := targetUpper i)
      (by
        intro y hy
        exact hpre i (nbrs.boundary_Icc_subset_neighborhood i hy))

/-- Cover-indexed `ChartBoxOpenNeighborhood` spelling.  This is useful when
the actual shrink selection already returns per-index source boxes inside a
target-open preimage. -/
theorem chartTransition_mapsTo_halfSpaceSupportBox_of_chartBoxOpenNeighborhoods
    (targetOpen :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} → Fin (n + 1) → Real)
    (hVsubset :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        targetOpen i ⊆ Icc (targetLower i) (targetUpper i))
    (nbr :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ChartBoxOpenNeighborhood
          ((ManifoldForm.chartTransition I
            (C.boundaryChart i.1) (targetChart i)) ⁻¹'
            targetOpen i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (targetLower i) (targetUpper i)) := by
  intro i
  exact
    ManifoldForm.chartTransition_mapsTo_halfSpaceSupportBox_of_chartBoxOpenNeighborhood
      (I := I) (x0 := C.boundaryChart i.1) (x1 := targetChart i)
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (c := targetLower i) (d := targetUpper i)
      (hVsubset i) (nbr i)

end CoverIndexedBoundaryTransitionBoxNeighborhoods

namespace CoverIndexedBoundaryTargetBoxData

variable
  (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)

/-- Target-box-data version of the transition-neighborhood shrink. -/
theorem chartTransitionMapsToField_of_transitionNeighborhoods_preimage
    (nbrs :
      CoverIndexedBoundaryTransitionBoxNeighborhoods
        (I := I) (K := K) C D.targetChart)
    (hpre :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.boundaryNeighborhood i ⊆
          (ManifoldForm.chartTransition I
            (C.boundaryChart i.1) (D.targetChart i)) ⁻¹'
            Icc (D.targetLower i) (D.targetUpper i)) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      MapsTo
        (ManifoldForm.chartTransition I
          (C.boundaryChart i.1) (D.targetChart i))
        (halfSpaceSupportBox (C.boundaryLower i.1)
          (C.boundaryUpper i.1))
        (Icc (D.targetLower i) (D.targetUpper i)) :=
  CoverIndexedBoundaryTransitionBoxNeighborhoods.chartTransition_mapsTo_halfSpaceSupportBox_of_boundaryNeighborhood_subset_preimage
    (I := I) (K := K) (C := C)
    (targetChart := D.targetChart)
    nbrs D.targetLower D.targetUpper hpre

/-- Direct target-zero support field from transition-neighborhood shrink
instead of a manually supplied chart-transition `MapsTo` field. -/
theorem targetInChartZero_tsupport_subset_Icc_of_transitionNeighborhoods_preimage
    (homegaSupport : ManifoldForm.support I omega ⊆ K)
    (nbrs :
      CoverIndexedBoundaryTransitionBoxNeighborhoods
        (I := I) (K := K) C D.targetChart)
    (hpre :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        nbrs.boundaryNeighborhood i ⊆
          (ManifoldForm.chartTransition I
            (C.boundaryChart i.1) (D.targetChart i)) ⁻¹'
            Icc (D.targetLower i) (D.targetUpper i)) :
    D.TargetInChartZeroTSupportSubsetIccField :=
  D.targetInChartZero_tsupport_subset_Icc_of_chartTransition_mapsTo
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    homegaSupport
    (D.chartTransitionMapsToField_of_transitionNeighborhoods_preimage
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      nbrs hpre)

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedZeroCompactChartTransitionShrink

end Stokes

end
