import Stokes.Global.CoverIndexedBoundaryTargetBoxDataConstructor

/-!
# Cover-indexed source-to-target selected boundary boxes

This file isolates the nontrivial input needed to build the
`sourceTargetSelectedBox` field in the cover-indexed boundary route.

The source chart-box data already supplies the lower-zero convention, ordered
corners, and source-chart target containment.  For a genuine target chart, the
remaining mathematical inputs are:

* the selected closed source box lies in the source-to-target chart overlap;
* the localized target-transition representative is supported in the source
  half-space support box.

The support theorem below derives the second item from the usual localized
support mechanism: base target-transition support plus partition-coefficient
support on a coordinate carrier.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedSourceTargetSelectedBoxConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace SupportControlledSelectedPartition

variable (P : SupportControlledSelectedPartition C)

/--
Source-to-target support for a localized boundary cover piece.

This is the cover-indexed version of
`transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport`:
if the base form in the source-to-target transition coordinates is carried by
`transitionCoordSupport`, and the partition coefficient is supported in the
chosen source half-space box on that carrier, then the localized piece is
supported in the source half-space box.
-/
theorem boundary_sourceTarget_tsupport_subset_halfSpaceSupportBox_of_coordSupport
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (transitionCoordSupport :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hbase :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          transitionCoordSupport i)
    (hcoeff :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.boundaryChart i.1) (targetChart i)
              (P.partition (Sum.inr i))) ∩
            transitionCoordSupport i ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      halfSpaceSupportBox
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm] using
    (ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := targetChart i)
      (ρ := P.partition (Sum.inr i)) (ω := ω)
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (C := transitionCoordSupport i)
      (hbase i) (hcoeff i))

/--
Build one source-to-target selected boundary box from explicit overlap and
localized support control.

The lower-zero and ordered-corner fields come from the selected cover, and the
source-chart target containment is read from the self boundary-box domain
stored in the cover.  The two real target-chart inputs are `hoverlap` and
`hsupp`.
-/
theorem boundary_sourceTargetSelectedBox_of_tsupport_subset
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (hoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (hsupp :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    boundaryChartSelectedBox I
      (C.boundaryChart i.1) (targetChart i)
      (P.coverIndexLocalizedForm ω (Sum.inr i))
      (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  refine
    boundaryChartSelectedBox.mk_of_subsets
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (C.boundary_lower_zero i.1 i.2)
      (C.boundary_le i.1 i.2)
      ?_ (hoverlap i) (hsupp i)
  intro y hy
  exact (C.boundary_Icc_subset_domain i.1 i.2 hy).1

/--
One-shot source-to-target selected-box constructor from target-transition
coordinate support data.
-/
theorem boundary_sourceTargetSelectedBox_of_coordSupport
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (transitionCoordSupport :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (hbase :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          transitionCoordSupport i)
    (hcoeff :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.boundaryChart i.1) (targetChart i)
              (P.partition (Sum.inr i))) ∩
            transitionCoordSupport i ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    boundaryChartSelectedBox I
      (C.boundaryChart i.1) (targetChart i)
      (P.coverIndexLocalizedForm ω (Sum.inr i))
      (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  P.boundary_sourceTargetSelectedBox_of_tsupport_subset
    (ω := ω) targetChart hoverlap
    (P.boundary_sourceTarget_tsupport_subset_halfSpaceSupportBox_of_coordSupport
      (ω := ω) targetChart transitionCoordSupport hbase hcoeff)
    i

end SupportControlledSelectedPartition

namespace CoverIndexedAssignedBoxLocalData

/--
Assigned local data supplies the source selected-box geometry.  To change the
comparison chart from the source chart to `targetChart`, it remains only to
provide source-box overlap with the target chart and support of the localized
target-transition representative in the source half-space support box.
-/
theorem sourceTargetSelectedBox_of_tsupport_subset
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (hoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (hsupp :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    boundaryChartSelectedBox I
      (C.boundaryChart i.1) (targetChart i)
      (P.coverIndexLocalizedForm ω (Sum.inr i))
      (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  rcases D.boundaryAssignedFields i with
    ⟨_hcompact, _hhalf, _hbase, ha0, hle, _hcoeff, hdomain,
      _hopen, _hbox⟩
  refine
    boundaryChartSelectedBox.mk_of_subsets
      (I := I)
      (x0 := C.boundaryChart i.1) (x1 := targetChart i)
      (ω := P.coverIndexLocalizedForm ω (Sum.inr i))
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      ha0 hle ?_ (hoverlap i) (hsupp i)
  intro y hy
  exact (hdomain hy).1

/--
Assigned-local-data version of the one-shot source-to-target selected-box
constructor from target-transition coordinate support data.
-/
theorem sourceTargetSelectedBox_of_coordSupport
    (D : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (transitionCoordSupport :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (hbase :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          transitionCoordSupport i)
    (hcoeff :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.boundaryChart i.1) (targetChart i)
              (P.partition (Sum.inr i))) ∩
            transitionCoordSupport i ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    boundaryChartSelectedBox I
      (C.boundaryChart i.1) (targetChart i)
      (P.coverIndexLocalizedForm ω (Sum.inr i))
      (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  sourceTargetSelectedBox_of_tsupport_subset
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    D targetChart hoverlap
    (P.boundary_sourceTarget_tsupport_subset_halfSpaceSupportBox_of_coordSupport
      (ω := ω) targetChart transitionCoordSupport hbase hcoeff)
    i

end CoverIndexedAssignedBoxLocalData

namespace CoverIndexedBoundaryTargetBoxData

/--
Build the grouped target-box data from target-box selections and the exact
target-transition support data needed to generate the source-to-target selected
boxes.
-/
def ofTargetSelectionAndCoordSupport
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (transitionCoordSupport :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (hbase :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          transitionCoordSupport i)
    (hcoeff :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.boundaryChart i.1) (targetChart i)
              (P.partition (Sum.inr i))) ∩
            transitionCoordSupport i ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω :=
  CoverIndexedBoundaryTargetBoxData.ofTargetSelection
    (C := C) (P := P) (ω := ω)
    targetChart
    (CoverIndexedAssignedBoxLocalData.sourceTargetSelectedBox_of_coordSupport
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      localData
      targetChart transitionCoordSupport hoverlap hbase hcoeff)
    targetSelection

/--
Variant for callers that have already proved the localized target-transition
support statement directly.
-/
def ofTargetSelectionAndTSupport
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (hoverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (hsupp :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω :=
  CoverIndexedBoundaryTargetBoxData.ofTargetSelection
    (C := C) (P := P) (ω := ω)
    targetChart
    (CoverIndexedAssignedBoxLocalData.sourceTargetSelectedBox_of_tsupport_subset
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      localData
      targetChart hoverlap hsupp)
    targetSelection

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedSourceTargetSelectedBoxConstructor

end Stokes

end
