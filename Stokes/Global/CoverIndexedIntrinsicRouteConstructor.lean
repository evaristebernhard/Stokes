import Stokes.Global.CoverIndexedIntrinsicEndpointConstructor
import Stokes.Global.CoverIndexedIntrinsicRegularityFields

/-!
# Intrinsic route constructors

This file is an integration checkpoint for the intrinsic compact-support
represented route.  It packages the zero-localized endpoint data introduced in
`CoverIndexedZeroLocalizedIntrinsicCertificate` into the conditional
`HasIntrinsicRoute` proposition of
`CoverIndexedZeroCompactRepresentedStokesIntrinsic`.

The completely natural constructor

```
pointwise + compact support + chartwise smooth + support control
  -> HasIntrinsicRoute
```

still requires the remaining internal construction lemmas.  The constructors
below deliberately avoid the old `CoverIndexedBoundaryLocalizedRefinedGeometry`
handoff, because that route still carried the ordinary total
`transitionPullbackInChart` support hypothesis.  The new handoff is the minimal
zero-localized one: endpoint partition + `ZeroLocalStokesData` + interior
fields.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section IntrinsicRouteConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable [FiniteDimensional Real (Fin (n + 1) -> Real)]
variable [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]

namespace CoverIndexedZeroCompactRepresentedStokesIntrinsicInput

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesIntrinsicInput
        (I := I) (ω := omega) K)

/--
Package an already constructed zero-localized endpoint into the conditional
intrinsic certificate.

This is the exact handoff the remaining intrinsic constructors should target:
no ordinary support statement for the total transition representative is
required.
-/
def intrinsicCertificateOfZeroEndpoint
    (D :
      CoverIndexedBoundaryLocalizedRefinedPartition
        (I := I) (K := K)
        (X.selectedCover (I := I) (K := K) (ω := omega))
        (X.selectedPartition (I := I) (K := K) (ω := omega)) omega
        (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega)))
    (boundaryPieces_eq_selectedFiniteCover :
      forall i : CoverIndexedBoundaryIndex
          (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)),
        D.boundaryPieces i =
          (X.selectedBoundaryFiniteCover
            (I := I) (K := K) (ω := omega)).sigmaBoundaryPieces i)
    (L : D.ZeroLocalStokesData (I := I) (K := K))
    (sourceChart_eq_selected :
      forall i q, q ∈ D.boundaryPieces i ->
        L.sourceChart i q =
          (X.selectedCover (I := I) (K := K) (ω := omega)).boundaryChart i.1)
    (lower_eq_selectedFiniteCover :
      forall i q, q ∈ D.boundaryPieces i ->
        L.lower i q =
          (X.selectedBoundaryFiniteCover
            (I := I) (K := K) (ω := omega)).lowerCorner q.1 q.2)
    (upper_eq_selectedFiniteCover :
      forall i q, q ∈ D.boundaryPieces i ->
        L.upper i q =
          (X.selectedBoundaryFiniteCover
            (I := I) (K := K) (ω := omega)).upperCorner q.1 q.2)
    (interiorFields :
      forall i,
        i ∈ (Finset.univ :
          Finset (CoverIndexedBoundaryIndex
            (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)))) ->
          forall q, q ∈ D.boundaryPieces i ->
            HalfSpaceBoxInteriorStokesFields
              (ManifoldForm.transitionPullbackInChart I
                (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q))
              (L.lower i q) (L.upper i q)) :
    X.IntrinsicCertificate (I := I) (K := K) (ω := omega) where
  endpoint := D
  boundaryPieces_eq_selectedFiniteCover := boundaryPieces_eq_selectedFiniteCover
  localData := L
  sourceChart_eq_selected := sourceChart_eq_selected
  lower_eq_selectedFiniteCover := lower_eq_selectedFiniteCover
  upper_eq_selectedFiniteCover := upper_eq_selectedFiniteCover
  interiorFields := interiorFields

/-- The same zero-endpoint constructor, as the route proposition consumed by
the intrinsic API. -/
theorem hasIntrinsicRoute_of_zeroEndpoint
    (D :
      CoverIndexedBoundaryLocalizedRefinedPartition
        (I := I) (K := K)
        (X.selectedCover (I := I) (K := K) (ω := omega))
        (X.selectedPartition (I := I) (K := K) (ω := omega)) omega
        (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega)))
    (boundaryPieces_eq_selectedFiniteCover :
      forall i : CoverIndexedBoundaryIndex
          (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)),
        D.boundaryPieces i =
          (X.selectedBoundaryFiniteCover
            (I := I) (K := K) (ω := omega)).sigmaBoundaryPieces i)
    (L : D.ZeroLocalStokesData (I := I) (K := K))
    (sourceChart_eq_selected :
      forall i q, q ∈ D.boundaryPieces i ->
        L.sourceChart i q =
          (X.selectedCover (I := I) (K := K) (ω := omega)).boundaryChart i.1)
    (lower_eq_selectedFiniteCover :
      forall i q, q ∈ D.boundaryPieces i ->
        L.lower i q =
          (X.selectedBoundaryFiniteCover
            (I := I) (K := K) (ω := omega)).lowerCorner q.1 q.2)
    (upper_eq_selectedFiniteCover :
      forall i q, q ∈ D.boundaryPieces i ->
        L.upper i q =
          (X.selectedBoundaryFiniteCover
            (I := I) (K := K) (ω := omega)).upperCorner q.1 q.2)
    (interiorFields :
      forall i,
        i ∈ (Finset.univ :
          Finset (CoverIndexedBoundaryIndex
            (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)))) ->
          forall q, q ∈ D.boundaryPieces i ->
            HalfSpaceBoxInteriorStokesFields
              (ManifoldForm.transitionPullbackInChart I
                (L.sourceChart i q) (L.targetChart i q) (L.localizedForm i q))
              (L.lower i q) (L.upper i q)) :
    X.HasIntrinsicRoute (I := I) (K := K) (ω := omega) :=
  ⟨X.intrinsicCertificateOfZeroEndpoint
    (I := I) (K := K) (omega := omega)
    D boundaryPieces_eq_selectedFiniteCover L sourceChart_eq_selected
    lower_eq_selectedFiniteCover upper_eq_selectedFiniteCover interiorFields⟩

/--
Build an intrinsic certificate from a smooth refinement of the canonical
selected boundary finite cover, using the zero-localized endpoint route.

The remaining explicit inputs are the true internal obligations not yet
generated from the four public intrinsic fields:

* the smooth refinement's finite pieces match the selected boundary cover;
* the zero-extended localized representatives are supported in their selected
  half-space boxes; and
* the Euclidean interior Stokes fields are available for those localized
  representatives.
-/
def intrinsicCertificateOfSelectedSmoothRefinement
    [DecidableEq
      (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega))]
    (S :
      BoundarySmoothBoxRefinement
        (I := I) (K := K)
        (X.selectedCover (I := I) (K := K) (ω := omega))
        (X.selectedPartition (I := I) (K := K) (ω := omega))
        (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega)))
    (_boundaryPieces_eq :
      forall i : CoverIndexedBoundaryIndex
          (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)),
        S.boundaryPieces i =
          (X.selectedBoundaryFiniteCover
            (I := I) (K := K) (ω := omega)).sigmaBoundaryPieces i)
    (hzero :
      forall i (q : Fin (n + 1) -> Real),
        q ∈ (X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := omega)).activePieces i ->
          tsupport
              (ManifoldForm.transitionPullbackInChartZero I
                ((X.selectedCover
                  (I := I) (K := K) (ω := omega)).boundaryChart i.1)
                ((X.selectedCover
                  (I := I) (K := K) (ω := omega)).boundaryChart i.1)
                (ManifoldForm.localizedForm I
                  (S.coefficient i ⟨i, q⟩) omega)) ⊆
            halfSpaceSupportBox
              ((X.selectedBoundaryFiniteCover
                (I := I) (K := K) (ω := omega)).lowerCorner i q)
              ((X.selectedBoundaryFiniteCover
                (I := I) (K := K) (ω := omega)).upperCorner i q))
    (interiorFields :
      forall i,
        i ∈ (Finset.univ :
          Finset (CoverIndexedBoundaryIndex
            (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)))) ->
          forall (q : Fin (n + 1) -> Real),
            q ∈ (X.selectedBoundaryFiniteCover
              (I := I) (K := K) (ω := omega)).activePieces i ->
              HalfSpaceBoxInteriorStokesFields
                (ManifoldForm.transitionPullbackInChart I
                  ((X.selectedCover
                    (I := I) (K := K) (ω := omega)).boundaryChart i.1)
                  ((X.selectedCover
                    (I := I) (K := K) (ω := omega)).boundaryChart i.1)
                  (ManifoldForm.localizedForm I
                    (S.coefficient i ⟨i, q⟩) omega))
                ((X.selectedBoundaryFiniteCover
                  (I := I) (K := K) (ω := omega)).lowerCorner i q)
                ((X.selectedBoundaryFiniteCover
                  (I := I) (K := K) (ω := omega)).upperCorner i q)) :
    X.IntrinsicCertificate (I := I) (K := K) (ω := omega) := by
  classical
  let C0 := X.selectedCover (I := I) (K := K) (ω := omega)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := omega)
  let D :=
    X.endpointPartitionOfSelectedBoundaryFiniteCover
      (I := I) (K := K) (ω := omega) S
  let L : D.ZeroLocalStokesData (I := I) (K := K) :=
    X.zeroLocalStokesDataOfSelectedBoundaryFiniteCover
      (I := I) (K := K) (ω := omega) S
      (by
        intro i q hq
        have hactive : q.2 ∈ F.activePieces q.1 :=
          F.sigmaBoundaryPieces_active hq
        have howner : q.1 = i := (F.mem_sigmaBoundaryPieces.mp hq).1
        cases howner
        simpa [D, F, C0, selectedBoundarySelfChart, selectedBoundaryLocalizedForm,
          selectedBoundaryFiniteCoverLower, selectedBoundaryFiniteCoverUpper] using
          hzero q.1 q.2 hactive)
  refine
    X.intrinsicCertificateOfZeroEndpoint
      (I := I) (K := K) (omega := omega)
      D ?_ L ?_ ?_ ?_ ?_
  · intro i
    rfl
  · intro i q hq
    have howner : q.1 = i := (F.mem_sigmaBoundaryPieces.mp hq).1
    cases howner
    rfl
  · intro i q hq
    rfl
  · intro i q hq
    rfl
  · intro i hi q hq
    have hactive : q.2 ∈ F.activePieces q.1 :=
      F.sigmaBoundaryPieces_active hq
    have howner : q.1 = i := (F.mem_sigmaBoundaryPieces.mp hq).1
    cases howner
    simpa [D, L, F, C0, selectedBoundarySelfChart, selectedBoundaryLocalizedForm,
      selectedBoundaryFiniteCoverLower, selectedBoundaryFiniteCoverUpper] using
      interiorFields q.1 hi q.2 hactive

/-- Route proposition generated by
`intrinsicCertificateOfSelectedSmoothRefinement`. -/
theorem hasIntrinsicRoute_of_selectedSmoothRefinement
    [DecidableEq
      (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega))]
    (S :
      BoundarySmoothBoxRefinement
        (I := I) (K := K)
        (X.selectedCover (I := I) (K := K) (ω := omega))
        (X.selectedPartition (I := I) (K := K) (ω := omega))
        (X.selectedBoundaryPiece (I := I) (K := K) (ω := omega)))
    (boundaryPieces_eq :
      forall i : CoverIndexedBoundaryIndex
          (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)),
        S.boundaryPieces i =
          (X.selectedBoundaryFiniteCover
            (I := I) (K := K) (ω := omega)).sigmaBoundaryPieces i)
    (hzero :
      forall i (q : Fin (n + 1) -> Real),
        q ∈ (X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := omega)).activePieces i ->
          tsupport
              (ManifoldForm.transitionPullbackInChartZero I
                ((X.selectedCover
                  (I := I) (K := K) (ω := omega)).boundaryChart i.1)
                ((X.selectedCover
                  (I := I) (K := K) (ω := omega)).boundaryChart i.1)
                (ManifoldForm.localizedForm I
                  (S.coefficient i ⟨i, q⟩) omega)) ⊆
            halfSpaceSupportBox
              ((X.selectedBoundaryFiniteCover
                (I := I) (K := K) (ω := omega)).lowerCorner i q)
              ((X.selectedBoundaryFiniteCover
                (I := I) (K := K) (ω := omega)).upperCorner i q))
    (interiorFields :
      forall i,
        i ∈ (Finset.univ :
          Finset (CoverIndexedBoundaryIndex
            (I := I) (X.selectedCover (I := I) (K := K) (ω := omega)))) ->
          forall (q : Fin (n + 1) -> Real),
            q ∈ (X.selectedBoundaryFiniteCover
              (I := I) (K := K) (ω := omega)).activePieces i ->
              HalfSpaceBoxInteriorStokesFields
                (ManifoldForm.transitionPullbackInChart I
                  ((X.selectedCover
                    (I := I) (K := K) (ω := omega)).boundaryChart i.1)
                  ((X.selectedCover
                    (I := I) (K := K) (ω := omega)).boundaryChart i.1)
                  (ManifoldForm.localizedForm I
                    (S.coefficient i ⟨i, q⟩) omega))
                ((X.selectedBoundaryFiniteCover
                  (I := I) (K := K) (ω := omega)).lowerCorner i q)
                ((X.selectedBoundaryFiniteCover
                  (I := I) (K := K) (ω := omega)).upperCorner i q)) :
    X.HasIntrinsicRoute (I := I) (K := K) (ω := omega) :=
  ⟨X.intrinsicCertificateOfSelectedSmoothRefinement
    (I := I) (K := K) (omega := omega)
    S boundaryPieces_eq hzero interiorFields⟩

end CoverIndexedZeroCompactRepresentedStokesIntrinsicInput

end IntrinsicRouteConstructor

end Stokes

end
