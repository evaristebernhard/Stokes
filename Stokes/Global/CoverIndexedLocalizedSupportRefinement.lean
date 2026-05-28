import Stokes.Global.CoverIndexedRelativeLocalStokes

/-!
# Local Stokes from direct localized support

The older assigned-box local Stokes wrappers derive localized support from
separate base-support and coefficient-support fields.  For the intrinsic route
that is too rigid: the honest datum we need after zero-extension/localization
is simply that the localized coordinate representative is supported in the
selected half-space support box.

This file exposes that direct form, both for a single boundary box and for a
cover-indexed finite family.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryLocalizedSupportLocalStokes

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {ρ : M → Real}
variable {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/-- Project-local boundary Stokes from direct support control of the localized
transition representative.

This is the support interface needed by the zero/localized intrinsic route:
the bottom half-space theorem only needs this support statement to kill the
artificial boundary faces. -/
theorem boundaryAssignedBox_projectLocalStokes_of_localized_tsupport_interiorFields
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆
        halfSpaceSupportBox a b)
    (D :
      HalfSpaceBoxInteriorStokesFields
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) a b) :
    projectLocalBulkIntegral I x0 x1
        (ManifoldForm.localizedForm I ρ ω) a b =
      projectLocalBoundaryIntegral I x0 x1
        (ManifoldForm.localizedForm I ρ ω) a b := by
  have hface :
      boxFaceCoeffTSupportInHalfSpaceBox
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) a b :=
    boxFaceCoeffTSupportInHalfSpaceBox_transitionPullback_of_tsupport_subset
      I x0 x1 (ManifoldForm.localizedForm I ρ ω) a b hsupp
  have hstokes :
      halfSpaceLocalBulkIntegral
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) a b =
        halfSpaceBoundarySign n *
          halfSpaceBoundaryTransitionFormIntegral I x0 x1
            (ManifoldForm.localizedForm I ρ ω) a b := by
    simpa [halfSpaceBoundaryTransitionFormIntegral] using
      halfSpaceLocalStokes_compactSupport_of_interiorFields
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) a b D hface
  simpa [projectLocalBulkIntegral, projectLocalBoundaryIntegral,
    halfSpaceLocalTransitionBulkIntegral,
    outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul] using hstokes

end BoundaryLocalizedSupportLocalStokes

section CoverIndexedLocalizedSupportLocalStokes

universe uH uM uι uB

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type uι} {BoundaryPiece : Type uB}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- Cover-indexed local Stokes from direct localized support and the Euclidean
interior-box fields. -/
theorem coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_localizedSupport_interiorFields
    (active : Finset ι)
    (boundaryPieces : ι → Finset BoundaryPiece)
    (sourceChart targetChart : ι → BoundaryPiece → M)
    (rho : ι → BoundaryPiece → M → Real)
    (lower upper : ι → BoundaryPiece → Fin (n + 1) → Real)
    (hlocalized :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i →
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (sourceChart i q) (targetChart i q)
                (ManifoldForm.localizedForm I (rho i q) ω)) ⊆
            halfSpaceSupportBox (lower i q) (upper i q))
    (hfields :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i →
          HalfSpaceBoxInteriorStokesFields
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart i q) (targetChart i q)
              (ManifoldForm.localizedForm I (rho i q) ω))
            (lower i q) (upper i q)) :
    (Finset.sum active fun i =>
        Finset.sum (boundaryPieces i) fun q =>
          projectLocalBulkIntegral I (sourceChart i q) (targetChart i q)
            (ManifoldForm.localizedForm I (rho i q) ω)
            (lower i q) (upper i q)) =
      Finset.sum active fun i =>
        Finset.sum (boundaryPieces i) fun q =>
          projectLocalBoundaryIntegral I (sourceChart i q) (targetChart i q)
            (ManifoldForm.localizedForm I (rho i q) ω)
            (lower i q) (upper i q) := by
  exact
    coverIndexed_boundaryBulkSum_eq_trueBoundarySum active boundaryPieces
      (fun i q =>
        projectLocalBulkIntegral I (sourceChart i q) (targetChart i q)
          (ManifoldForm.localizedForm I (rho i q) ω)
          (lower i q) (upper i q))
      (fun i q =>
        projectLocalBoundaryIntegral I (sourceChart i q) (targetChart i q)
          (ManifoldForm.localizedForm I (rho i q) ω)
          (lower i q) (upper i q))
      (by
        intro i hi q hq
        exact
          boundaryAssignedBox_projectLocalStokes_of_localized_tsupport_interiorFields
            (I := I) (x0 := sourceChart i q) (x1 := targetChart i q)
            (ρ := rho i q) (ω := ω)
            (a := lower i q) (b := upper i q)
            (hlocalized i hi q hq) (hfields i hi q hq))

section Refined

variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryBoxRefinedPartition

variable {BoundaryPiece : Type uB}
variable
  (D :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω BoundaryPiece)

/-- Refined-partition local Stokes using only the stored localized support
field, not the older base/coefficient support derivation. -/
theorem boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_localizedSupport_interiorFields
    (hfields :
      ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q, q ∈ D.boundaryPieces i →
          HalfSpaceBoxInteriorStokesFields
            (ManifoldForm.transitionPullbackInChart I
              (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
            (D.lower i q) (D.upper i q)) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBoundaryTerm i q := by
  classical
  exact
    coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_localizedSupport_interiorFields
      (I := I) (ω := ω)
      (active := (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)))
      (boundaryPieces := D.boundaryPieces)
      (sourceChart := D.sourceChart) (targetChart := D.targetChart)
      (rho := D.coefficient)
      (lower := D.lower) (upper := D.upper)
      (fun i hi q hq =>
        D.localized_tsupport_subset_halfSpaceSupportBox i q hq)
      hfields

end CoverIndexedBoundaryBoxRefinedPartition

end Refined

end CoverIndexedLocalizedSupportLocalStokes

end Stokes

end
