import Stokes.ManifoldFormChartTransitionOpen
import Stokes.Global.CoverIndexedZeroSourceSupport

/-!
# Relative source fields for zero-extension boundary assembly

For boundary models, `ManifoldForm.chartTransitionSource` is usually not open
in the ambient model vector space.  The honest replacement is that it is a
neighborhood within `range I` at each source point.

This file packages that replacement at the cover-index level.  It deliberately
does not build the existing zero source-target assembly input, because that
record still stores the false-in-boundary ambient field

```
sourceOpen : IsOpen (ManifoldForm.chartTransitionSource ...)
```

The first downstream theorem that must be refactored is
`CoverIndexedCompactSupportNeighborhoodDataInfty.
  boundary_projectLocalStokes_of_zero_tsupport_subset_source`: it passes
`sourceOpen` to
`halfSpaceLocalStokes_transitionPullback_of_zero_tsupport_subset_contDiffOn_isOpen`.
The replacement local theorem should take a relative `range I` neighborhood, or
an explicitly chosen ambient open neighborhood contained in the transition
source, together with `ContDiffOn` on that local domain.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedZeroRelativeSource

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedCompactSupportTransitionSupportData

/-- Cover-index relative source field for boundary chart transitions.

This is the boundary-compatible replacement for the old ambient
`sourceOpen` field. -/
abbrev SourceMemNhdsWithinRangeField
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega) : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    ∀ y : Fin (n + 1) → Real,
      y ∈ ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i) →
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i) ∈
        𝓝[range I] y

variable
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)

/-- The relative source field is available for any model with corners, including
half-space boundary models. -/
theorem sourceMemNhdsWithinRangeField_from_chartAPI :
    SourceMemNhdsWithinRangeField
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData := by
  intro i y hy
  exact
    transitionSupportData.sourceMemNhdsWithinRangeField
      (I := I) (K := K) (C := C) (P := P) (omega := omega) i y hy

end CoverIndexedCompactSupportTransitionSupportData

namespace CoverIndexedCompactSupportNeighborhoodData

variable
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)

/-- Relative source neighborhood field restricted to selected boundary source
boxes.  The neighborhood package is an explicit parameter so callers can keep
this field aligned with the source-box data that produced the membership
proofs. -/
abbrev BoundarySourceBoxMemNhdsWithinRangeField
    (_neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodData
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega) : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    ∀ y : Fin (n + 1) → Real,
      y ∈ Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) →
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i) ∈
        𝓝[range I] y

/-- Every point of a selected boundary source box sees the chart-transition
source as a neighborhood within `range I`. -/
theorem boundarySourceBoxMemNhdsWithinRangeField :
    BoundarySourceBoxMemNhdsWithinRangeField
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData := by
  intro i y hy
  have hysource :
      y ∈ ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i) := by
    rw [ManifoldForm.chartTransitionSource_eq]
    exact
      ⟨CoverIndexedCompactSupportNeighborhoodData.boundary_neighborhood_subset_target
          neighborhoodData i
          (CoverIndexedCompactSupportNeighborhoodData.boundary_Icc_subset_neighborhood
            neighborhoodData i hy),
        transitionSupportData.sourceBox_subset_overlap i hy⟩
  exact
    transitionSupportData.sourceMemNhdsWithinRangeField_from_chartAPI
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      i y hysource

end CoverIndexedCompactSupportNeighborhoodData

namespace CoverIndexedCompactSupportNeighborhoodDataInfty

variable
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)

/-- Relative source neighborhood field restricted to selected boundary source
boxes for the `C^\infty` neighborhood package.  The neighborhood package is an
explicit parameter so callers can keep this field aligned with the source-box
data that produced the membership proofs. -/
abbrev BoundarySourceBoxMemNhdsWithinRangeField
    (_neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega) : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    ∀ y : Fin (n + 1) → Real,
      y ∈ Icc (C.boundaryLower i.1) (C.boundaryUpper i.1) →
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i) ∈
        𝓝[range I] y

/-- Every point of a selected `C^\infty` boundary source box sees the
chart-transition source as a neighborhood within `range I`. -/
theorem boundarySourceBoxMemNhdsWithinRangeField :
    BoundarySourceBoxMemNhdsWithinRangeField
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData := by
  intro i y hy
  exact
    transitionSupportData.sourceMemNhdsWithinRangeField_from_chartAPI
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      i y
      (CoverIndexedCompactSupportNeighborhoodDataInfty.boundary_sourceBox_subset_chartTransitionSource
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        neighborhoodData transitionSupportData i hy)

/-- Relative source neighborhood field restricted to an already shrunken
boundary neighborhood.  This is the exact relative analogue of the
`sourceNeighborhood` data used by the current zero assembly bridge. -/
abbrev BoundaryNeighborhoodMemNhdsWithinRangeField : Prop :=
  ∀ i : {x : M // x ∈ C.boundaryCenters},
    ∀ y : Fin (n + 1) → Real,
      y ∈ neighborhoodData.boundaryNeighborhood i →
      ManifoldForm.chartTransitionSource I
        (C.boundaryChart i.1) (transitionSupportData.targetChart i) ∈
        𝓝[range I] y

/-- A boundary neighborhood contained in the transition source gives a relative
source-neighborhood field on that neighborhood. -/
theorem boundaryNeighborhoodMemNhdsWithinRangeField_of_subset_transitionSource
    (sourceNeighborhood :
      BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData) :
    BoundaryNeighborhoodMemNhdsWithinRangeField
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData := by
  intro i y hy
  exact
    transitionSupportData.sourceMemNhdsWithinRangeField_from_chartAPI
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      i y (sourceNeighborhood i hy)

end CoverIndexedCompactSupportNeighborhoodDataInfty

/-- Boundary-compatible replacement skeleton for
`CoverIndexedZeroBoundarySourceTargetAssemblyBridgeInput`.

This record keeps the source-neighborhood and zero-support fields that are
already mathematically valid, and replaces `sourceOpen` by the relative source
field.  It is not yet an adapter to the old assembly record: that requires
refactoring the local half-space Stokes theorem named in the module docstring. -/
structure CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n) where
  neighborhoodData :
    CoverIndexedCompactSupportNeighborhoodDataInfty
      (I := I) (K := K) C P omega
  transitionSupportData :
    CoverIndexedCompactSupportTransitionSupportData
      (I := I) (K := K) C P omega
  sourceNeighborhood :
    CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
      (I := I) (K := K) neighborhoodData transitionSupportData
  sourceMemNhdsWithinRange :
    CoverIndexedCompactSupportTransitionSupportData.SourceMemNhdsWithinRangeField
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      transitionSupportData
  zero_tsupport_subset_source :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.transitionPullbackInChartZero I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
        halfSpaceSupportBox
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
  globalBoundaryIntegral : Real
  globalBoundaryIntegral_eq_sourceTargetBoundarySum :
    globalBoundaryIntegral =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)

namespace CoverIndexedZeroBoundaryRelativeSourceAssemblyInput

/-- Constructor deriving the relative source field and zero source support from
the existing transition-support package. -/
def ofSourceNeighborhoodAndTransitionSupport
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (sourceNeighborhood :
      CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodSubsetTransitionSource
        (I := I) (K := K) neighborhoodData transitionSupportData)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_sourceTargetBoundarySum :
      globalBoundaryIntegral =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
      (I := I) (K := K) C P omega where
  neighborhoodData := neighborhoodData
  transitionSupportData := transitionSupportData
  sourceNeighborhood := sourceNeighborhood
  sourceMemNhdsWithinRange :=
    transitionSupportData.sourceMemNhdsWithinRangeField_from_chartAPI
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
  zero_tsupport_subset_source :=
    transitionSupportData.zero_tsupport_subset_source
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBoundaryIntegral_eq_sourceTargetBoundarySum :=
    globalBoundaryIntegral_eq_sourceTargetBoundarySum

/-- Relative source field on the selected source boxes, projected from the
packaged input. -/
theorem boundarySourceBoxMemNhdsWithinRangeField
    (D :
      CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
        (I := I) (K := K) C P omega) :
    CoverIndexedCompactSupportNeighborhoodDataInfty.BoundarySourceBoxMemNhdsWithinRangeField
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      D.neighborhoodData D.transitionSupportData := by
  intro i y hy
  exact
    D.sourceMemNhdsWithinRange i y
      (CoverIndexedCompactSupportNeighborhoodDataInfty.boundary_sourceBox_subset_chartTransitionSource
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        D.neighborhoodData D.transitionSupportData i hy)

/-- Relative source field on the shrunken boundary neighborhoods, projected
from the packaged input. -/
theorem boundaryNeighborhoodMemNhdsWithinRangeField
    (D :
      CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
        (I := I) (K := K) C P omega) :
    CoverIndexedCompactSupportNeighborhoodDataInfty.BoundaryNeighborhoodMemNhdsWithinRangeField
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      D.neighborhoodData D.transitionSupportData := by
  intro i y hy
  exact D.sourceMemNhdsWithinRange i y (D.sourceNeighborhood i hy)

/-- The generated local source-target equality, using only the relative-source
assembly input and the selected open boundary neighborhoods.

This is the first zero-assembly statement in this route that no longer stores
or consumes the false-in-boundary ambient `sourceOpen` field. -/
theorem zeroBulkSetIntegralSum_eq_sourceTargetBoundarySum
    (D :
      CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M] :
    D.transitionSupportData.boundaryZeroBulkSetIntegralSum
        (I := I) (K := K) (C := C) (P := P) (omega := omega) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (C.boundaryChart i.1) (D.transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
  CoverIndexedCompactSupportTransitionSupportData.boundary_zeroBulkSetIntegralSum_eq_projectLocalBoundarySum_of_zero_tsupport_subset_sourceNeighborhood
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      D.neighborhoodData D.transitionSupportData
      D.sourceNeighborhood D.zero_tsupport_subset_source

/-- Source-target zero bulk assembly after the remaining boundary
reconstruction field is supplied, still without any ambient source-open
hypothesis. -/
theorem zeroBulkSetIntegralSum_eq_globalBoundaryIntegral
    (D :
      CoverIndexedZeroBoundaryRelativeSourceAssemblyInput
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M] :
    D.transitionSupportData.boundaryZeroBulkSetIntegralSum
        (I := I) (K := K) (C := C) (P := P) (omega := omega) =
      D.globalBoundaryIntegral := by
  calc
    D.transitionSupportData.boundaryZeroBulkSetIntegralSum
        (I := I) (K := K) (C := C) (P := P) (omega := omega) =
        Finset.sum C.boundaryCoverIndexFinset fun i =>
          projectLocalBoundaryIntegral I
            (C.boundaryChart i.1) (D.transitionSupportData.targetChart i)
            (P.coverIndexLocalizedForm omega (Sum.inr i))
            (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
      D.zeroBulkSetIntegralSum_eq_sourceTargetBoundarySum
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
    _ = D.globalBoundaryIntegral :=
      D.globalBoundaryIntegral_eq_sourceTargetBoundarySum.symm

end CoverIndexedZeroBoundaryRelativeSourceAssemblyInput

end CoverIndexedZeroRelativeSource

end Stokes

end
