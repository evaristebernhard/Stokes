import Stokes.Global.CoverIndexedIntrinsicSmoothRefinementConstructor
import Stokes.Global.CoverIndexedIntrinsicSelectedRegularityConstructor
import Stokes.Global.CoverIndexedZeroLocalizedSupport

/-!
# Zero-localized support for the canonical intrinsic smooth refinement

This module closes the support bridge for the natural intrinsic route.  The
proof is deliberately specialized to the canonical `selectedSmoothRefinement`:
that refinement is the one used by the final theorem, and its source charts,
active carriers, and half-space boxes are definitionally the selected finite
cover data.

The mathematical move is to rewrite the refined localization
`localizedForm (P_i * psi_q) omega` as the two-step localization
`localizedForm psi_q (localizedForm P_i omega)`.  The first localization has
support in the boundary active carrier, while the subpartition support is
subordinate to the selected open half-space box on that carrier.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section IntrinsicZeroSupportConstructor

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable [FiniteDimensional Real (Fin (n + 1) → Real)]
variable [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]

namespace CoverIndexedZeroCompactRepresentedStokesIntrinsicInput

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesIntrinsicInput
        (I := I) (ω := ω) K)

/-- The first boundary localization has support in the selected boundary
active carrier. -/
theorem selectedBoundaryLocalizedForm_support_subset_activeCarrier
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := ω))) :
    ManifoldForm.support I
        (ManifoldForm.localizedForm I
          ((X.selectedPartition
            (I := I) (K := K) (ω := ω)).partition (Sum.inr i)) ω) ⊆
      (X.selectedPartition
        (I := I) (K := K) (ω := ω)).boundaryActiveCarrier (I := I) i := by
  intro x hx
  constructor
  · have hxcoeff :
        x ∈ Function.support
          ((X.selectedPartition
            (I := I) (K := K) (ω := ω)).partition (Sum.inr i)) :=
      ManifoldForm.localizedForm_support_subset_coefficient_support
        (I := I)
        ((X.selectedPartition
          (I := I) (K := K) (ω := ω)).partition (Sum.inr i)) ω hx
    exact (subset_tsupport
      (f := (X.selectedPartition
        (I := I) (K := K) (ω := ω)).partition (Sum.inr i))) hxcoeff
  · exact X.support_subset_K
      (ManifoldForm.localizedForm_support_subset_form_support
        (I := I)
        ((X.selectedPartition
          (I := I) (K := K) (ω := ω)).partition (Sum.inr i)) ω hx)

/-- Coordinate points in the selected boundary active carrier map back to the
same active carrier under the selected boundary chart inverse. -/
theorem selectedBoundaryActiveCoordCarrier_symm_mem_activeCarrier
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := ω))) :
    ∀ y ∈
        (X.selectedPartition
          (I := I) (K := K) (ω := ω)).boundaryActiveCoordCarrier (I := I) i,
      (extChartAt I
        ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart i.1)).symm y ∈
        (X.selectedPartition
          (I := I) (K := K) (ω := ω)).boundaryActiveCarrier (I := I) i := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hxsource :
      x ∈ (extChartAt I
        ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart i.1)).source :=
    (X.selectedPartition
      (I := I) (K := K) (ω := ω)).boundaryActiveCarrier_subset_chart_source
        (I := I) i hx
  have hleft :
      (extChartAt I
        ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart i.1)).symm
          ((extChartAt I
            ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart i.1)) x) = x :=
    (extChartAt I
      ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart i.1)).left_inv
      hxsource
  rw [hleft]
  exact hx

/-- The selected boundary active coordinate carrier lies in the selected
boundary chart target. -/
theorem selectedBoundaryActiveCoordCarrier_subset_target
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := ω))) :
    (X.selectedPartition
        (I := I) (K := K) (ω := ω)).boundaryActiveCoordCarrier (I := I) i ⊆
      (extChartAt I
        ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart i.1)).target := by
  rintro y ⟨x, hx, rfl⟩
  exact
    (extChartAt I
      ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart i.1)).map_source
      ((X.selectedPartition
        (I := I) (K := K) (ω := ω)).boundaryActiveCarrier_subset_chart_source
          (I := I) i hx)

/-- A canonical selected subpartition coefficient is supported, on the boundary
active coordinate carrier, in its selected refined half-space box. -/
theorem selectedSmoothRefinement_subpartition_transitionCoefficient_tsupport_inter_activeCoordCarrier_subset_halfSpaceSupportBox
    [DecidableEq
      (X.selectedBoundaryPiece (I := I) (K := K) (ω := ω))]
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := ω)))
    (q : Fin (n + 1) → Real)
    (hq :
      q ∈ (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := ω)).activePieces i) :
    tsupport
        (ManifoldForm.transitionCoefficientInChart I
          ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart i.1)
          ((X.selectedCover (I := I) (K := K) (ω := ω)).boundaryChart i.1)
          ((X.selectedSmoothRefinement
            (I := I) (K := K) (omega := ω)).subpartition i
            ⟨(⟨i, q⟩ :
              X.selectedBoundaryPiece (I := I) (K := K) (ω := ω)), by
              exact
                ((X.selectedBoundaryFiniteCover
                  (I := I) (K := K) (ω := ω)).mem_sigmaBoundaryPieces
                    (i := i)
                    (q := (⟨i, q⟩ :
                      X.selectedBoundaryPiece (I := I) (K := K) (ω := ω)))).mpr
                  ⟨rfl, hq⟩⟩)) ∩
        (X.selectedPartition
          (I := I) (K := K) (ω := ω)).boundaryActiveCoordCarrier (I := I) i ⊆
      halfSpaceSupportBox
        ((X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := ω)).lowerCorner i q)
        ((X.selectedBoundaryFiniteCover
          (I := I) (K := K) (ω := ω)).upperCorner i q) := by
  classical
  let C0 := X.selectedCover (I := I) (K := K) (ω := ω)
  let P0 := X.selectedPartition (I := I) (K := K) (ω := ω)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := ω)
  let S := X.selectedSmoothRefinement (I := I) (K := K) (omega := ω)
  let qflat : X.selectedBoundaryPiece (I := I) (K := K) (ω := ω) := ⟨i, q⟩
  have hqflat : qflat ∈ F.sigmaBoundaryPieces i := by
    exact (F.mem_sigmaBoundaryPieces (i := i) (q := qflat)).mpr ⟨rfl, hq⟩
  have hθ :
      tsupport (S.subpartition i ⟨qflat, by simpa [S] using hqflat⟩) ∩
          P0.boundaryActiveCarrier (I := I) i ⊆
        boundaryChartBoxNeighborhood I (C0.boundaryChart i.1)
          (F.lowerCorner i q) (F.upperCorner i q) := by
    intro x hx
    have hxopen :
        x ∈ S.ambientOpen i qflat :=
      S.subpartition_tsupport_inter_carrier_subset_open i
        ⟨qflat, by simpa [S] using hqflat⟩
        (by simpa [S] using hx)
    have hbox :
        x ∈ boundaryChartBoxNeighborhood I (S.sourceChart i qflat)
          (S.lower i qflat) (S.upper i qflat) :=
      S.ambientOpen_subset_boundaryChartBox i qflat
        (by simpa [S] using hqflat) hxopen
    simpa [S, qflat, C0, F] using hbox
  simpa [S, C0, P0, F, qflat] using
    transitionCoefficientInChart_self_tsupport_inter_coordSupport_subset_halfSpaceBox
      (I := I)
      (K := P0.boundaryActiveCarrier (I := I) i)
      (x := C0.boundaryChart i.1)
      (ρ := S.subpartition i ⟨qflat, by simpa [S] using hqflat⟩)
      (coordSupport := P0.boundaryActiveCoordCarrier (I := I) i)
      (a := F.lowerCorner i q)
      (b := F.upperCorner i q)
      (X.selectedBoundaryActiveCoordCarrier_symm_mem_activeCarrier
        (I := I) (K := K) (ω := ω) i)
      (X.selectedBoundaryActiveCoordCarrier_subset_target
        (I := I) (K := K) (ω := ω) i)
      hθ

/-- The refined coefficient localization agrees with the two-stage
localization by the selected boundary coefficient and then by the selected
smooth subpartition coefficient. -/
theorem selectedSmoothRefinement_localizedForm_eq_subpartition_localizedForm
    [DecidableEq
      (X.selectedBoundaryPiece (I := I) (K := K) (ω := ω))]
    (i :
      CoverIndexedBoundaryIndex
        (I := I) (X.selectedCover (I := I) (K := K) (ω := ω)))
    (q : Fin (n + 1) → Real)
    (hq :
      q ∈ (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := ω)).activePieces i) :
    ManifoldForm.localizedForm I
        ((X.selectedSmoothRefinement
          (I := I) (K := K) (omega := ω)).coefficient i ⟨i, q⟩) ω =
      ManifoldForm.localizedForm I
        ((X.selectedSmoothRefinement
          (I := I) (K := K) (omega := ω)).subpartition i
          ⟨(⟨i, q⟩ :
            X.selectedBoundaryPiece (I := I) (K := K) (ω := ω)), by
            exact
              ((X.selectedBoundaryFiniteCover
                (I := I) (K := K) (ω := ω)).mem_sigmaBoundaryPieces
                  (i := i)
                  (q := (⟨i, q⟩ :
                    X.selectedBoundaryPiece (I := I) (K := K) (ω := ω)))).mpr
                ⟨rfl, hq⟩⟩)
        (ManifoldForm.localizedForm I
          ((X.selectedPartition
            (I := I) (K := K) (ω := ω)).partition (Sum.inr i)) ω) := by
  classical
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := ω)
  let S := X.selectedSmoothRefinement (I := I) (K := K) (omega := ω)
  let qflat : X.selectedBoundaryPiece (I := I) (K := K) (ω := ω) := ⟨i, q⟩
  have hqflat : qflat ∈ F.sigmaBoundaryPieces i := by
    exact (F.mem_sigmaBoundaryPieces (i := i) (q := qflat)).mpr ⟨rfl, hq⟩
  have hqS : qflat ∈ S.boundaryPieces i := by
    simpa [S] using hqflat
  ext x v
  simp only [ManifoldForm.localizedForm]
  change
    S.coefficient i qflat x * (ω x) v =
      (S.subpartition i ⟨qflat, hqS⟩ x) *
        (((X.selectedPartition
          (I := I) (K := K) (ω := ω)).partition (Sum.inr i)) x * (ω x) v)
  rw [S.coefficient_of_mem i hqS x]
  ring

/-- Zero-localized support for the canonical selected smooth refinement. -/
theorem zeroSupportOfSelectedSmoothRefinement
    [DecidableEq
      (X.selectedBoundaryPiece (I := I) (K := K) (ω := ω))] :
    ∀ i (q : Fin (n + 1) → Real),
      q ∈ (X.selectedBoundaryFiniteCover
        (I := I) (K := K) (ω := ω)).activePieces i →
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              ((X.selectedCover
                (I := I) (K := K) (ω := ω)).boundaryChart i.1)
              ((X.selectedCover
                (I := I) (K := K) (ω := ω)).boundaryChart i.1)
              (ManifoldForm.localizedForm I
                ((X.selectedSmoothRefinement
                  (I := I) (K := K) (omega := ω)).coefficient i ⟨i, q⟩) ω)) ⊆
          halfSpaceSupportBox
            ((X.selectedBoundaryFiniteCover
              (I := I) (K := K) (ω := ω)).lowerCorner i q)
            ((X.selectedBoundaryFiniteCover
              (I := I) (K := K) (ω := ω)).upperCorner i q) := by
  classical
  intro i q hq
  let C0 := X.selectedCover (I := I) (K := K) (ω := ω)
  let P0 := X.selectedPartition (I := I) (K := K) (ω := ω)
  let F := X.selectedBoundaryFiniteCover (I := I) (K := K) (ω := ω)
  let S := X.selectedSmoothRefinement (I := I) (K := K) (omega := ω)
  let qflat : X.selectedBoundaryPiece (I := I) (K := K) (ω := ω) := ⟨i, q⟩
  have hqflat : qflat ∈ F.sigmaBoundaryPieces i := by
    exact (F.mem_sigmaBoundaryPieces (i := i) (q := qflat)).mpr ⟨rfl, hq⟩
  let θ : M → Real := S.subpartition i ⟨qflat, by simpa [S] using hqflat⟩
  let η : ManifoldForm I M n :=
    ManifoldForm.localizedForm I (P0.partition (Sum.inr i)) ω
  have hηsupport :
      ManifoldForm.support I η ⊆ P0.boundaryActiveCarrier (I := I) i := by
    simpa [η, P0] using
      X.selectedBoundaryLocalizedForm_support_subset_activeCarrier
        (I := I) (K := K) (ω := ω) i
  have hcoord :
      chartCoordinateImage I (C0.boundaryChart i.1)
          (P0.boundaryActiveCarrier (I := I) i) ⊆
        P0.boundaryActiveCoordCarrier (I := I) i := by
    intro y hy
    simpa [SupportControlledSelectedPartition.boundaryActiveCoordCarrier,
      C0, P0] using hy
  have hcoeff :
      tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C0.boundaryChart i.1) (C0.boundaryChart i.1) θ) ∩
          P0.boundaryActiveCoordCarrier (I := I) i ⊆
        halfSpaceSupportBox (F.lowerCorner i q) (F.upperCorner i q) := by
    simpa [C0, P0, F, S, qflat, θ] using
      X.selectedSmoothRefinement_subpartition_transitionCoefficient_tsupport_inter_activeCoordCarrier_subset_halfSpaceSupportBox
        (I := I) (K := K) (ω := ω) i q hq
  have htwo :
      tsupport
          (ManifoldForm.transitionPullbackInChartZero I
            (C0.boundaryChart i.1) (C0.boundaryChart i.1)
            (ManifoldForm.localizedForm I θ η)) ⊆
        halfSpaceSupportBox (F.lowerCorner i q) (F.upperCorner i q) := by
    exact
      ManifoldForm.transitionPullbackInChartZero_localizedForm_tsupport_subset_halfSpaceSupportBox_of_support_subset_K
        (I := I)
        (K := P0.boundaryActiveCarrier (I := I) i)
        (x0 := C0.boundaryChart i.1)
        (x1 := C0.boundaryChart i.1)
        (ρ := θ)
        (ω := η)
        (coordSupport := P0.boundaryActiveCoordCarrier (I := I) i)
        (a := F.lowerCorner i q)
        (b := F.upperCorner i q)
        (P0.isCompact_boundaryActiveCarrier (I := I) X.hK i)
        (P0.boundaryActiveCarrier_subset_chart_source (I := I) i)
        hηsupport
        hcoord
        hcoeff
  have hform :
      ManifoldForm.localizedForm I (S.coefficient i qflat) ω =
        ManifoldForm.localizedForm I θ η := by
    simpa [C0, P0, F, S, qflat, θ, η] using
      X.selectedSmoothRefinement_localizedForm_eq_subpartition_localizedForm
        (I := I) (K := K) (ω := ω) i q hq
  simpa [C0, F, S, qflat, hform] using htwo

/-- The intrinsic route generated from the canonical selected smooth
refinement, its zero-localized support, and the selected regularity
constructor. -/
theorem hasIntrinsicRoute_intrinsic :
    X.HasIntrinsicRoute (I := I) (K := K) (ω := ω) := by
  classical
  exact
    X.hasIntrinsicRoute_of_selectedSmoothRefinement
      (I := I) (K := K) (omega := ω)
      (X.selectedSmoothRefinement (I := I) (K := K) (omega := ω))
      (by
        intro i
        exact
          X.selectedSmoothRefinement_boundaryPieces
            (I := I) (K := K) (omega := ω) i)
      (X.zeroSupportOfSelectedSmoothRefinement
        (I := I) (K := K) (ω := ω))
      (X.interiorFieldsOfSelectedSmoothRefinement
        (I := I) (K := K) (ω := ω)
        (X.selectedSmoothRefinement (I := I) (K := K) (omega := ω))
        (by
          intro i
          exact
            X.selectedSmoothRefinement_boundaryPieces
              (I := I) (K := K) (omega := ω) i))

/-- Canonical represented bulk integral generated by the intrinsic route. -/
def canonicalRepresentedBulkIntegral : Real :=
  X.representedBulkIntegral
    (I := I) (K := K) (ω := ω)
    (X.hasIntrinsicRoute_intrinsic (I := I) (K := K) (ω := ω))

/-- Canonical represented boundary integral generated by the intrinsic route. -/
def canonicalRepresentedBoundaryIntegral : Real :=
  X.representedBoundaryIntegral
    (I := I) (K := K) (ω := ω)
    (X.hasIntrinsicRoute_intrinsic (I := I) (K := K) (ω := ω))

/-- Natural compact-support represented Stokes for the intrinsic input.

The statement exposes only the four fields of
`CoverIndexedZeroCompactRepresentedStokesIntrinsicInput`: pointwise chart-box
data, compactness, chartwise smoothness, and global support control.
-/
theorem representedStokes :
    X.canonicalRepresentedBulkIntegral (I := I) (K := K) (ω := ω) =
      X.canonicalRepresentedBoundaryIntegral (I := I) (K := K) (ω := ω) := by
  simpa [canonicalRepresentedBulkIntegral, canonicalRepresentedBoundaryIntegral] using
    X.representedStokes_of_hasIntrinsicRoute
      (I := I) (K := K) (ω := ω)
      (X.hasIntrinsicRoute_intrinsic (I := I) (K := K) (ω := ω))

end CoverIndexedZeroCompactRepresentedStokesIntrinsicInput

end IntrinsicZeroSupportConstructor

end Stokes

end
