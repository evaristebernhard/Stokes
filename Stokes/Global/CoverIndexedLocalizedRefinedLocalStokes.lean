import Stokes.Global.CoverIndexedLocalizedRefinedEndpoint
import Stokes.BoundaryChart.ZeroExtensionLocalStokes

/-!
# Local Stokes for localized refined boundary endpoint data

`CoverIndexedLocalizedRefinedEndpoint` keeps the endpoint algebra deliberately
minimal: it stores only refined boundary pieces and the already-generated local
bulk/boundary scalar terms.  This file supplies the preceding local-Stokes
adapter.  A separate `LocalStokesData` record remembers the charts, localized
forms, half-space boxes, and localized/zero support fields needed to prove the
nested finite-sum equality for that existing endpoint structure.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryLocalizedRefinedLocalStokes

universe uH uM uB

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type uB}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryLocalizedRefinedPartition

variable
    (D :
      CoverIndexedBoundaryLocalizedRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece)

/--
Geometry and support data needed to prove local half-space Stokes for the
minimal localized-refined endpoint structure.

The two equality fields connect the endpoint scalar terms to the concrete
project-local integrals.  The localized and zero support fields are both stored:
the main route below uses zero support to kill artificial faces, while the
direct localized-support route remains available for callers that already have
ordinary support of the old transition representative.
-/
structure LocalStokesData where
  /-- Source chart for one localized refined boundary piece. -/
  sourceChart :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → M
  /-- Target chart for one localized refined boundary piece. -/
  targetChart :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → M
  /-- Localized manifold form attached to one refined boundary piece. -/
  localizedForm :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → ManifoldForm I M n
  /-- Lower corner of the refined half-space box. -/
  lower :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → Fin (n + 1) → Real
  /-- Upper corner of the refined half-space box. -/
  upper :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → Fin (n + 1) → Real
  /-- Endpoint bulk term is the project-local bulk integral for this piece. -/
  localBulkTerm_eq :
    ∀ i q, q ∈ D.boundaryPieces i →
      D.localBulkTerm i q =
        projectLocalBulkIntegral I (sourceChart i q) (targetChart i q)
          (localizedForm i q) (lower i q) (upper i q)
  /-- Endpoint boundary term is the project-local outward-first boundary integral. -/
  localBoundaryTerm_eq :
    ∀ i q, q ∈ D.boundaryPieces i →
      D.localBoundaryTerm i q =
        projectLocalBoundaryIntegral I (sourceChart i q) (targetChart i q)
          (localizedForm i q) (lower i q) (upper i q)
  /-- Closed refined source boxes lie in their concrete chart-transition sources. -/
  Icc_subset_chartTransitionSource :
    ∀ i q, q ∈ D.boundaryPieces i →
      Icc (lower i q) (upper i q) ⊆
        ManifoldForm.chartTransitionSource I (sourceChart i q) (targetChart i q)
  /-- Direct support of the old localized transition representative. -/
  localized_tsupport_subset_halfSpaceSupportBox :
    ∀ i q, q ∈ D.boundaryPieces i →
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (sourceChart i q) (targetChart i q) (localizedForm i q)) ⊆
        halfSpaceSupportBox (lower i q) (upper i q)
  /-- Support of the zero-extended localized transition representative. -/
  zero_tsupport_subset_halfSpaceSupportBox :
    ∀ i q, q ∈ D.boundaryPieces i →
      tsupport
          (ManifoldForm.transitionPullbackInChartZero I
            (sourceChart i q) (targetChart i q) (localizedForm i q)) ⊆
        halfSpaceSupportBox (lower i q) (upper i q)

namespace LocalStokesData

variable {D}
variable (L : D.LocalStokesData (I := I) (K := K))

/-- Pointwise local Stokes using zero-extension support to kill artificial faces. -/
theorem localStokes_of_zeroSupport_interiorFields
    {i : CoverIndexedBoundaryIndex (I := I) C} {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i)
    (hfields :
      HalfSpaceBoxInteriorStokesFields
        (ManifoldForm.transitionPullbackInChart I
          (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q))
        (L.lower i q) (L.upper i q)) :
    D.localBulkTerm i q = D.localBoundaryTerm i q := by
  have hrem :
      halfSpaceLocalTransitionBoundaryRemainder I
          (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q)
          (L.lower i q) (L.upper i q) = 0 :=
    halfSpaceLocalTransitionBoundaryRemainder_eq_zero_of_zero_tsupport_subset
      (I := I) (x0 := L.sourceChart i q) (x1 := L.targetChart i q)
      (ω := L.localizedForm i q)
      (a := L.lower i q) (b := L.upper i q)
      hfields.le
      (U := ManifoldForm.chartTransitionSource I
        (L.sourceChart i q) (L.targetChart i q))
      (L.Icc_subset_chartTransitionSource i q hq)
      (fun _ hy => hy)
      (L.zero_tsupport_subset_halfSpaceSupportBox i q hq)
  have hlocal :
      halfSpaceLocalTransitionBulkIntegral I
          (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q)
          (L.lower i q) (L.upper i q) =
        halfSpaceBoundarySign n *
            halfSpaceBoundaryTransitionFormIntegral I
              (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q)
              (L.lower i q) (L.upper i q) := by
    have hremainder :
        halfSpaceLocalTransitionBulkIntegral I
            (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q)
            (L.lower i q) (L.upper i q) =
          halfSpaceBoundarySign n *
              halfSpaceBoundaryTransitionFormIntegral I
                (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q)
                (L.lower i q) (L.upper i q) +
            halfSpaceLocalTransitionBoundaryRemainder I
              (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q)
              (L.lower i q) (L.upper i q) := by
      simpa [halfSpaceLocalTransitionBulkIntegral,
        halfSpaceBoundaryTransitionFormIntegral,
        halfSpaceLocalTransitionBoundaryRemainder] using hfields.withRemainder
    simpa [hrem] using hremainder
  rw [L.localBulkTerm_eq i q hq, L.localBoundaryTerm_eq i q hq]
  simpa [projectLocalBulkIntegral, projectLocalBoundaryIntegral,
    halfSpaceLocalTransitionBulkIntegral,
    outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul] using hlocal

/-- Pointwise local Stokes using the stored support of the old localized representative. -/
theorem localStokes_of_localizedSupport_interiorFields
    {i : CoverIndexedBoundaryIndex (I := I) C} {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i)
    (hfields :
      HalfSpaceBoxInteriorStokesFields
        (ManifoldForm.transitionPullbackInChart I
          (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q))
        (L.lower i q) (L.upper i q)) :
    D.localBulkTerm i q = D.localBoundaryTerm i q := by
  have hface :
      boxFaceCoeffTSupportInHalfSpaceBox
        (ManifoldForm.transitionPullbackInChart I
          (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q))
        (L.lower i q) (L.upper i q) :=
    boxFaceCoeffTSupportInHalfSpaceBox_transitionPullback_of_tsupport_subset
      I (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q)
      (L.lower i q) (L.upper i q)
      (L.localized_tsupport_subset_halfSpaceSupportBox i q hq)
  have hlocal :
      halfSpaceLocalTransitionBulkIntegral I
          (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q)
          (L.lower i q) (L.upper i q) =
        halfSpaceBoundarySign n *
          halfSpaceBoundaryTransitionFormIntegral I
            (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q)
            (L.lower i q) (L.upper i q) := by
    simpa [halfSpaceLocalTransitionBulkIntegral,
      halfSpaceBoundaryTransitionFormIntegral] using
      halfSpaceLocalStokes_compactSupport_of_interiorFields
        (ManifoldForm.transitionPullbackInChart I
          (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q))
        (L.lower i q) (L.upper i q) hfields hface
  rw [L.localBulkTerm_eq i q hq, L.localBoundaryTerm_eq i q hq]
  simpa [projectLocalBulkIntegral, projectLocalBoundaryIntegral,
    halfSpaceLocalTransitionBulkIntegral,
    outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul] using hlocal

end LocalStokesData

/--
Localized refined boundary local Stokes, summed over all selected boundary
indices and refined boxes.

This is the local-sum equality consumed by the generated endpoint theorem.
It uses the existing minimal endpoint structure `D` and a separate local data
record `L` for geometry/support.
-/
theorem boundaryHalfSpaceBulkSum_eq_trueBoundarySum
    (L : D.LocalStokesData (I := I) (K := K))
    (hfields :
      ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q, q ∈ D.boundaryPieces i →
          HalfSpaceBoxInteriorStokesFields
            (ManifoldForm.transitionPullbackInChart I
              (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q))
            (L.lower i q) (L.upper i q)) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q => D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q => D.localBoundaryTerm i q := by
  classical
  exact
    coverIndexed_boundaryBulkSum_eq_trueBoundarySum
      (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C))
      D.boundaryPieces D.localBulkTerm D.localBoundaryTerm
      (by
        intro i hi q hq
        exact L.localStokes_of_zeroSupport_interiorFields hq
          (hfields i hi q hq))

/-- Local-sum theorem variant using ordinary localized support directly. -/
theorem boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_localizedSupport
    (L : D.LocalStokesData (I := I) (K := K))
    (hfields :
      ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q, q ∈ D.boundaryPieces i →
          HalfSpaceBoxInteriorStokesFields
            (ManifoldForm.transitionPullbackInChart I
              (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q))
            (L.lower i q) (L.upper i q)) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q => D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q => D.localBoundaryTerm i q := by
  classical
  exact
    coverIndexed_boundaryBulkSum_eq_trueBoundarySum
      (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C))
      D.boundaryPieces D.localBulkTerm D.localBoundaryTerm
      (by
        intro i hi q hq
        exact L.localStokes_of_localizedSupport_interiorFields hq
          (hfields i hi q hq))

end CoverIndexedBoundaryLocalizedRefinedPartition

end BoundaryLocalizedRefinedLocalStokes

end Stokes

end
