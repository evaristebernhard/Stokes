import Stokes.Global.CoverIndexedSourceTargetSelectedBoxConstructor
import Stokes.Global.TransitionCoefficientSupportBridge

/-!
# Cover-indexed source-to-target transition coordinate support

This file removes one layer of low-level input from the boundary target-box
route.  The previous constructor
`CoverIndexedBoundaryTargetBoxData.ofTargetSelectionAndCoordSupport` required
callers to provide the coefficient support statement directly:

```lean
tsupport (transitionCoefficientInChart source target rho) ∩ coordSupport ⊆
  halfSpaceSupportBox a b
```

Here we prove that statement from the natural coordinate-carrier facts:

* the carrier maps back into the compact support set `K`;
* the carrier lies in the source chart target;
* the carrier lies in the source-to-target chart overlap.

The base-form support in the transition coordinates is still honest selection
data: it records the carrier that contains
`tsupport (transitionPullbackInChart source target omega)`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedTransitionCoordSupport

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
Source-to-target coefficient support on a coordinate carrier.

This is the non-self analogue of the existing self-chart bridge in
`TransitionCoefficientSupportBridge`: on the chart-transition overlap,
topological support of the coordinate coefficient maps back to topological
support of the manifold-side coefficient.  The support-controlled partition
subordination then puts the coordinate point in the selected half-space box.
-/
theorem transitionCoefficientInChart_tsupport_inter_coordSupport_subset_halfSpaceBox
    {x0 x1 : M} {ρ : M → Real}
    {coordSupport : Set (Fin (n + 1) → Real)}
    {a b : Fin (n + 1) → Real}
    (hcoordK :
      ∀ y ∈ coordSupport, (extChartAt I x0).symm y ∈ K)
    (hcoordTarget : coordSupport ⊆ (extChartAt I x0).target)
    (hcoordOverlap : coordSupport ⊆ ManifoldForm.chartOverlap I x0 x1)
    (hρ :
      tsupport ρ ∩ K ⊆ boundaryChartBoxNeighborhood I x0 a b) :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ∩
        coordSupport ⊆
      halfSpaceSupportBox a b := by
  rintro y ⟨hycoeff, hycoord⟩
  have hρsupp :
      (extChartAt I x0).symm y ∈ tsupport ρ :=
    ManifoldForm.transitionCoefficientInChart_tsupport_mapsTo_tsupport
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (y := y)
      (hcoordTarget hycoord) (hcoordOverlap hycoord) hycoeff
  have hmanifold :
      (extChartAt I x0).symm y ∈ boundaryChartBoxNeighborhood I x0 a b :=
    hρ ⟨hρsupp, hcoordK y hycoord⟩
  have hbox :
      (extChartAt I x0) ((extChartAt I x0).symm y) ∈
        halfSpaceSupportBox a b := by
    simpa [boundaryChartBoxNeighborhood] using hmanifold.2
  rwa [(extChartAt I x0).right_inv (hcoordTarget hycoord)] at hbox

namespace SupportControlledSelectedPartition

variable (P : SupportControlledSelectedPartition C)

/--
Cover-indexed coefficient support for a source-to-target transition carrier.

The only data specific to the target chart is that the carrier lies in the
source-to-target overlap; all partition subordination is reused from `P`.
-/
theorem boundary_transitionCoefficient_inter_transitionCoordSupport_subset_halfSpaceBox
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (transitionCoordSupport :
      {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real))
    (hcoordK :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ y ∈ transitionCoordSupport i,
          (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (hcoordTarget :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionCoordSupport i ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (hcoordOverlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        transitionCoordSupport i ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.transitionCoefficientInChart I
          (C.boundaryChart i.1) (targetChart i)
          (P.partition (Sum.inr i))) ∩
        transitionCoordSupport i ⊆
      halfSpaceSupportBox
        (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  exact
    transitionCoefficientInChart_tsupport_inter_coordSupport_subset_halfSpaceBox
      (I := I) (K := K)
      (x0 := C.boundaryChart i.1) (x1 := targetChart i)
      (ρ := P.partition (Sum.inr i))
      (coordSupport := transitionCoordSupport i)
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (hcoordK i) (hcoordTarget i) (hcoordOverlap i)
      (P.boundary_tsupport_inter_subset_assigned i)

end SupportControlledSelectedPartition

/--
Minimal source-to-target transition coordinate-support data.

This record packages exactly the remaining geometric support choices needed to
build `sourceTargetSelectedBox` from a target chart:

* source box overlap with the target chart;
* a carrier for the base source-to-target transition representative;
* carrier containment in the source chart target and chart overlap;
* carrier points map back into the compact support set.

The partition-coefficient support in the source half-space box is derived from
these fields, not stored as an assumption.
-/
structure CoverIndexedTransitionCoordSupportData
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) where
  targetChart : {x : M // x ∈ C.boundaryCenters} → M
  transitionCoordSupport :
    {x : M // x ∈ C.boundaryCenters} → Set (Fin (n + 1) → Real)
  Icc_subset_overlap :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
        ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)
  base_tsupport_subset :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (targetChart i) ω) ⊆
        transitionCoordSupport i
  coord_mapsTo_support :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ∀ y ∈ transitionCoordSupport i,
        (extChartAt I (C.boundaryChart i.1)).symm y ∈ K
  coord_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      transitionCoordSupport i ⊆
        (extChartAt I (C.boundaryChart i.1)).target
  coord_subset_overlap :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      transitionCoordSupport i ⊆
        ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)

namespace CoverIndexedTransitionCoordSupportData

variable
    (D : CoverIndexedTransitionCoordSupportData (I := I) (K := K) C P ω)

/--
Constructor choosing the transition carrier to be exactly the base
source-to-target `tsupport`.

This removes the separate proof of
`tsupport (transitionPullbackInChart source target omega) ⊆ carrier`; callers
only have to prove that this true base support maps back into `K` and lies in
the source target/overlap.
-/
def ofBaseTSupport
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (Icc_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (base_mapsTo_support :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ y ∈
          tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω),
          (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (base_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (base_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedTransitionCoordSupportData (I := I) (K := K) C P ω where
  targetChart := targetChart
  transitionCoordSupport := fun i =>
    tsupport
      (ManifoldForm.transitionPullbackInChart I
        (C.boundaryChart i.1) (targetChart i) ω)
  Icc_subset_overlap := Icc_subset_overlap
  base_tsupport_subset := fun _ => Subset.rfl
  coord_mapsTo_support := base_mapsTo_support
  coord_subset_target := base_subset_target
  coord_subset_overlap := base_subset_overlap

/-- Coefficient support in the selected source half-space box, derived from
the transition-carrier data. -/
theorem coefficient_tsupport_inter_subset_halfSpaceBox
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.transitionCoefficientInChart I
          (C.boundaryChart i.1) (D.targetChart i)
          (P.partition (Sum.inr i))) ∩
        D.transitionCoordSupport i ⊆
      halfSpaceSupportBox
        (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  P.boundary_transitionCoefficient_inter_transitionCoordSupport_subset_halfSpaceBox
    D.targetChart D.transitionCoordSupport
    D.coord_mapsTo_support D.coord_subset_target D.coord_subset_overlap i

/-- Localized source-to-target transition support in the selected source
half-space box. -/
theorem localized_tsupport_subset_halfSpaceBox
    (i : {x : M // x ∈ C.boundaryCenters}) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (D.targetChart i)
          (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
      halfSpaceSupportBox
        (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  P.boundary_sourceTarget_tsupport_subset_halfSpaceSupportBox_of_coordSupport
    (ω := ω)
    D.targetChart D.transitionCoordSupport
    D.base_tsupport_subset D.coefficient_tsupport_inter_subset_halfSpaceBox i

/-- Generate the source-to-target selected boundary box from transition
coordinate-support data. -/
theorem sourceTargetSelectedBox
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    boundaryChartSelectedBox I
      (C.boundaryChart i.1) (D.targetChart i)
      (P.coverIndexLocalizedForm ω (Sum.inr i))
      (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  CoverIndexedAssignedBoxLocalData.sourceTargetSelectedBox_of_tsupport_subset
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    localData D.targetChart D.Icc_subset_overlap
    D.localized_tsupport_subset_halfSpaceBox i

/-- One-shot target-box data constructor from target selections plus transition
coordinate-support data. -/
def toBoundaryTargetBoxData
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (D.targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω :=
  CoverIndexedBoundaryTargetBoxData.ofTargetSelection
    (C := C) (P := P) (ω := ω)
    D.targetChart
    (D.sourceTargetSelectedBox localData)
    targetSelection

end CoverIndexedTransitionCoordSupportData

namespace CoverIndexedBoundaryTargetBoxData

/--
Public one-shot constructor in the shape used by the compact-support
represented endpoint: target-box selections plus transition support data
produce grouped boundary target-box data.
-/
def ofTargetSelectionAndTransitionCoordSupport
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (D : CoverIndexedTransitionCoordSupportData (I := I) (K := K) C P ω)
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (D.targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω :=
  D.toBoundaryTargetBoxData localData targetSelection

/--
Convenience variant using the base transition-pullback `tsupport` itself as the
transition coordinate carrier.
-/
def ofTargetSelectionAndBaseTSupport
    (localData : CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω)
    (targetChart : {x : M // x ∈ C.boundaryCenters} → M)
    (targetSelection :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        BoundaryChartTargetBoxSelection I
          (C.boundaryChart i.1) (targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (Icc_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        Set.Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i))
    (base_mapsTo_support :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ∀ y ∈
          tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω),
          (extChartAt I (C.boundaryChart i.1)).symm y ∈ K)
    (base_subset_target :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          (extChartAt I (C.boundaryChart i.1)).target)
    (base_subset_overlap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (targetChart i) ω) ⊆
          ManifoldForm.chartOverlap I (C.boundaryChart i.1) (targetChart i)) :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω :=
  ofTargetSelectionAndTransitionCoordSupport
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    localData
    (CoverIndexedTransitionCoordSupportData.ofBaseTSupport
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      targetChart Icc_subset_overlap
      base_mapsTo_support base_subset_target base_subset_overlap)
    targetSelection

end CoverIndexedBoundaryTargetBoxData

end CoverIndexedTransitionCoordSupport

end Stokes

end
