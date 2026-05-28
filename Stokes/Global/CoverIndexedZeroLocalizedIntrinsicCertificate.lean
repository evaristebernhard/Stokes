import Stokes.Global.CoverIndexedLocalizedRefinedLocalStokes

/-!
# Zero-localized intrinsic endpoint certificates

This module supplies the final endpoint assembly for the zero-localized route.
It deliberately works with the minimal endpoint structure
`CoverIndexedBoundaryLocalizedRefinedPartition` and a narrow local-data record
which stores only the support hypothesis actually used by the zero-extension
local Stokes proof.

In particular, `ZeroLocalStokesData` does not ask for ordinary total
`transitionPullbackInChart` support.  Artificial boundary faces are killed by
support of `transitionPullbackInChartZero`, then the generated endpoint equality
is obtained from the already-existing local finite-sum and represented-endpoint
algebra.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryZeroLocalizedIntrinsicCertificate

universe uH uM uB

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type uB}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryLocalizedRefinedPartition

variable
    (D :
      CoverIndexedBoundaryLocalizedRefinedPartition
        (I := I) (K := K) C P omega BoundaryPiece)

/--
Local Stokes data for the zero-localized endpoint route.

This is the intentionally narrow sibling of `LocalStokesData`: it remembers the
charts, localized forms, half-space boxes, endpoint-term identifications, and
the zero-extended support bound.  It does not require the old direct support
bound for the ordinary total `transitionPullbackInChart` representative.
-/
structure ZeroLocalStokesData where
  /-- Source chart for one localized refined boundary piece. -/
  sourceChart :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> M
  /-- Target chart for one localized refined boundary piece. -/
  targetChart :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> M
  /-- Localized manifold form attached to one refined boundary piece. -/
  localizedForm :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> ManifoldForm I M n
  /-- Lower corner of the refined half-space box. -/
  lower :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> Fin (n + 1) -> Real
  /-- Upper corner of the refined half-space box. -/
  upper :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> Fin (n + 1) -> Real
  /-- Endpoint bulk term is the project-local bulk integral for this piece. -/
  localBulkTerm_eq :
    forall i q, q ∈ D.boundaryPieces i ->
      D.localBulkTerm i q =
        projectLocalBulkIntegral I (sourceChart i q) (targetChart i q)
          (localizedForm i q) (lower i q) (upper i q)
  /-- Endpoint boundary term is the project-local outward-first boundary integral. -/
  localBoundaryTerm_eq :
    forall i q, q ∈ D.boundaryPieces i ->
      D.localBoundaryTerm i q =
        projectLocalBoundaryIntegral I (sourceChart i q) (targetChart i q)
          (localizedForm i q) (lower i q) (upper i q)
  /-- Closed refined source boxes lie in their concrete chart-transition sources. -/
  Icc_subset_chartTransitionSource :
    forall i q, q ∈ D.boundaryPieces i ->
      Icc (lower i q) (upper i q) ⊆
        ManifoldForm.chartTransitionSource I (sourceChart i q) (targetChart i q)
  /-- Zero-extended localized transition support lies in the half-space box. -/
  zero_tsupport_subset_halfSpaceSupportBox :
    forall i q, q ∈ D.boundaryPieces i ->
      tsupport
          (ManifoldForm.transitionPullbackInChartZero I
            (sourceChart i q) (targetChart i q) (localizedForm i q)) ⊆
        halfSpaceSupportBox (lower i q) (upper i q)

namespace ZeroLocalStokesData

variable {D}
variable (L : D.ZeroLocalStokesData (I := I) (K := K))

/--
Pointwise local Stokes for the generated endpoint term, using only zero
support to remove artificial faces.
-/
theorem localStokes_of_interiorFields
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

end ZeroLocalStokesData

/--
Zero-localized refined boundary local Stokes, summed over all selected boundary
indices and refined boxes.

Unlike `boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_localizedSupport`, this
route only consumes `ZeroLocalStokesData.zero_tsupport_subset_halfSpaceSupportBox`.
-/
theorem boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_zeroLocalStokesData
    (L : D.ZeroLocalStokesData (I := I) (K := K))
    (hfields :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
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
        exact L.localStokes_of_interiorFields hq (hfields i hi q hq))

/--
Generated represented Stokes from zero-localized local Stokes data.

This is the main certificate route exported by this file: the proof is exactly
the zero-support local finite-sum theorem followed by the minimal endpoint
reconstruction theorem.
-/
theorem representedStokes_of_zeroLocalStokesData
    (L : D.ZeroLocalStokesData (I := I) (K := K))
    (hfields :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          HalfSpaceBoxInteriorStokesFields
            (ManifoldForm.transitionPullbackInChart I
              (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q))
            (L.lower i q) (L.upper i q)) :
    D.generatedRepresentedBulkIntegral (I := I) (K := K) =
      D.generatedRepresentedBoundaryIntegral (I := I) (K := K) := by
  exact
    D.representedStokes_of_localStokes
      (I := I) (K := K)
      (D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_zeroLocalStokesData
        (I := I) (K := K) L hfields)

/--
Compatibility spelling for callers that already have the older `LocalStokesData`.
The theorem still uses the zero-support route
`boundaryHalfSpaceBulkSum_eq_trueBoundarySum`, not the ordinary localized
support route.
-/
theorem representedStokes_of_localStokesData_zeroSupport
    (L : D.LocalStokesData (I := I) (K := K))
    (hfields :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          HalfSpaceBoxInteriorStokesFields
            (ManifoldForm.transitionPullbackInChart I
              (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q))
            (L.lower i q) (L.upper i q)) :
    D.generatedRepresentedBulkIntegral (I := I) (K := K) =
      D.generatedRepresentedBoundaryIntegral (I := I) (K := K) := by
  exact
    D.representedStokes_of_localStokes
      (I := I) (K := K)
      (D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum
        (I := I) (K := K) L hfields)

/--
A compact certificate bundling an endpoint partition, zero-local data, and the
interior fields needed by the zero-localized route.
-/
structure ZeroLocalizedEndpointCertificate
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n) (BoundaryPiece : Type uB) where
  /-- Minimal generated endpoint partition. -/
  endpoint :
    CoverIndexedBoundaryLocalizedRefinedPartition
      (I := I) (K := K) C P omega BoundaryPiece
  /-- Local data without ordinary total transition support. -/
  localData : endpoint.ZeroLocalStokesData (I := I) (K := K)
  /-- Interior-box fields for every active refined boundary piece. -/
  interiorFields :
    forall i, i ∈
        (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
      forall q, q ∈ endpoint.boundaryPieces i ->
        HalfSpaceBoxInteriorStokesFields
          (ManifoldForm.transitionPullbackInChart I
            (localData.sourceChart i q) (localData.targetChart i q)
            (localData.localizedForm i q))
          (localData.lower i q) (localData.upper i q)

namespace ZeroLocalizedEndpointCertificate

variable
    (R :
      ZeroLocalizedEndpointCertificate
        (I := I) (K := K) C P omega BoundaryPiece)

/-- The generated represented bulk endpoint stored by the certificate. -/
def generatedRepresentedBulkIntegral : Real :=
  R.endpoint.generatedRepresentedBulkIntegral (I := I) (K := K)

/-- The generated represented boundary endpoint stored by the certificate. -/
def generatedRepresentedBoundaryIntegral : Real :=
  R.endpoint.generatedRepresentedBoundaryIntegral (I := I) (K := K)

/-- Represented Stokes for the bundled zero-localized endpoint certificate. -/
theorem representedStokes :
    R.generatedRepresentedBulkIntegral (I := I) (K := K) =
      R.generatedRepresentedBoundaryIntegral (I := I) (K := K) := by
  simpa [generatedRepresentedBulkIntegral, generatedRepresentedBoundaryIntegral] using
    R.endpoint.representedStokes_of_zeroLocalStokesData
      (I := I) (K := K) R.localData R.interiorFields

end ZeroLocalizedEndpointCertificate

end CoverIndexedBoundaryLocalizedRefinedPartition

end BoundaryZeroLocalizedIntrinsicCertificate

end Stokes

end
