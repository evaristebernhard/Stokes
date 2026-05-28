import Stokes.Global.BoundaryIntegrabilityCompactSupport
import Stokes.Global.BoundaryPartitionReconstructionFromSupport
import Stokes.Global.PartitionFormSumIdentity

/-!
# Boundary scalar finite-sum identities

This file is the boundary-scalar analogue of `PartitionFormSumIdentity`.
The main point is simple but useful downstream: once the finite localized form
sum agrees with `ω` at the manifold point represented by a boundary coordinate,
evaluation in a boundary chart and on the standard boundary tangent frame also
agrees with the corresponding finite sum of scalar representatives.

The final lemmas expose the exact `boundaryMeasurePieceSum` shape consumed by
the boundary measure reconstruction route.  When the global boundary scalar
representative is supplied by an abstract construction, the explicit hypothesis
is that this scalar representative respects the finite selected-piece sum.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryScalarFromFormSum

universe u w c

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

/-- A chart representative respects the finite localized-form sum at a point. -/
theorem inChart_eq_sum_localized_inChart_of_coeff_sum_eq_one_on
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M n) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1)
    (x0 : M) {y : Fin (n + 1) → Real}
    (hy : (extChartAt I x0).symm y ∈ K) :
    ManifoldForm.inChart I x0 ω y =
      Finset.sum active fun i =>
        ManifoldForm.inChart I x0
          (ManifoldForm.localizedForm I (coefficient i) ω) y := by
  have hform :
      (Finset.sum active fun i =>
          ManifoldForm.localizedForm I (coefficient i) ω
            ((extChartAt I x0).symm y)) =
        ω ((extChartAt I x0).symm y) :=
    ManifoldForm.sum_localizedForm_eq_on
      (I := I) active coefficient ω hsum
      ((extChartAt I x0).symm y) hy
  let z : M := (extChartAt I x0).symm y
  let L := ManifoldForm.chartInverseDeriv I x0 y
  change
    (ContinuousAlternatingMap.compContinuousLinearMapₗ L) (ω z) =
      Finset.sum active fun i =>
        (ContinuousAlternatingMap.compContinuousLinearMapₗ L)
          (ManifoldForm.localizedForm I (coefficient i) ω z)
  rw [← hform]
  exact map_sum (ContinuousAlternatingMap.compContinuousLinearMapₗ L)
    (fun i => ManifoldForm.localizedForm I (coefficient i) ω z) active

/-- Boundary in-chart scalar representatives respect the finite localized-form
sum after evaluation on the standard boundary tangent frame. -/
theorem boundaryChartInChartIntegrand_eq_sum_localized_of_coeff_sum_eq_one_on
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M n) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1)
    (x0 : M) {u : Fin n → Real}
    (hu : (extChartAt I x0).symm (boundaryInclusion n u) ∈ K) :
    boundaryChartInChartIntegrand I x0 ω u =
      Finset.sum active fun i =>
        boundaryChartInChartIntegrand I x0
          (ManifoldForm.localizedForm I (coefficient i) ω) u := by
  have h :=
    inChart_eq_sum_localized_inChart_of_coeff_sum_eq_one_on
      (I := I) active coefficient ω hsum x0
      (y := boundaryInclusion n u) hu
  simpa [boundaryChartInChartIntegrand, Finset.sum_apply] using
    congrArg (fun η => η (boundaryTangent n)) h

/-- A transition-pullback chart representative respects the finite localized
form sum at the target-chart point used by the transition expression. -/
theorem transitionPullbackInChart_eq_sum_localized_of_coeff_sum_eq_one_on
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M n) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1)
    (x0 x1 : M) {y : Fin (n + 1) → Real}
    (hy :
      (extChartAt I x1).symm (ManifoldForm.chartTransition I x0 x1 y) ∈ K) :
    ManifoldForm.transitionPullbackInChart I x0 x1 ω y =
      Finset.sum active fun i =>
        ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I (coefficient i) ω) y := by
  have hchart :=
    inChart_eq_sum_localized_inChart_of_coeff_sum_eq_one_on
      (I := I) active coefficient ω hsum x1
      (y := ManifoldForm.chartTransition I x0 x1 y) hy
  let y' := ManifoldForm.chartTransition I x0 x1 y
  let L := ManifoldForm.chartTransitionDeriv I x0 x1 y
  change
    (ContinuousAlternatingMap.compContinuousLinearMapₗ L)
        (ManifoldForm.inChart I x1 ω y') =
      Finset.sum active fun i =>
        (ContinuousAlternatingMap.compContinuousLinearMapₗ L)
          (ManifoldForm.inChart I x1
            (ManifoldForm.localizedForm I (coefficient i) ω) y')
  rw [hchart]
  exact map_sum (ContinuousAlternatingMap.compContinuousLinearMapₗ L)
    (fun i =>
      ManifoldForm.inChart I x1
        (ManifoldForm.localizedForm I (coefficient i) ω) y') active

/-- Boundary transition-pullback scalar representatives respect the finite
localized-form sum.  This is the scalar integrand shape used by the canonical
lower-zero-face boundary route. -/
theorem boundaryChartTransitionPullbackIntegrand_eq_sum_localized_of_coeff_sum_eq_one_on
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M n) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1)
    (x0 x1 : M) {u : Fin n → Real}
    (hu :
      (extChartAt I x1).symm
        (ManifoldForm.chartTransition I x0 x1 (boundaryInclusion n u)) ∈ K) :
    boundaryChartTransitionPullbackIntegrand I x0 x1 ω u =
      Finset.sum active fun i =>
        boundaryChartTransitionPullbackIntegrand I x0 x1
          (ManifoldForm.localizedForm I (coefficient i) ω) u := by
  have h :=
    transitionPullbackInChart_eq_sum_localized_of_coeff_sum_eq_one_on
      (I := I) active coefficient ω hsum x0 x1
      (y := boundaryInclusion n u) hu
  simpa [boundaryChartTransitionPullbackIntegrand, Finset.sum_apply] using
    congrArg (fun η => η (boundaryTangent n)) h

/-- The outward-first signed boundary scalar also respects the finite
localized-form sum. -/
theorem outwardFirst_boundaryChartTransitionPullbackIntegrand_eq_sum_localized
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (ω : ManifoldForm I M n) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1)
    (x0 x1 : M) {u : Fin n → Real}
    (hu :
      (extChartAt I x1).symm
        (ManifoldForm.chartTransition I x0 x1 (boundaryInclusion n u)) ∈ K) :
    outwardFirstBoundaryOrientationSign n *
        boundaryChartTransitionPullbackIntegrand I x0 x1 ω u =
      Finset.sum active fun i =>
        outwardFirstBoundaryOrientationSign n *
          boundaryChartTransitionPullbackIntegrand I x0 x1
            (ManifoldForm.localizedForm I (coefficient i) ω) u := by
  rw [boundaryChartTransitionPullbackIntegrand_eq_sum_localized_of_coeff_sum_eq_one_on
    (I := I) active coefficient ω hsum x0 x1 hu]
  rw [Finset.mul_sum]

namespace SelectedBoxPartitionOfUnity

variable [Preorder (Fin (n + 1) → Real)]
variable {ω : ManifoldForm I M n}

/-- Selected-partition version of the boundary transition-pullback scalar
finite-sum identity. -/
theorem boundaryChartTransitionPullbackIntegrand_eq_sum_localized_on
    (P : SelectedBoxPartitionOfUnity I ω)
    (x0 x1 : M) {u : Fin n → Real}
    (hu :
      (extChartAt I x1).symm
        (ManifoldForm.chartTransition I x0 x1 (boundaryInclusion n u)) ∈ P.K) :
    boundaryChartTransitionPullbackIntegrand I x0 x1 ω u =
      Finset.sum P.active fun i =>
        boundaryChartTransitionPullbackIntegrand I x0 x1
          (ManifoldForm.localizedForm I (fun z => P.partition i z) ω) u :=
  boundaryChartTransitionPullbackIntegrand_eq_sum_localized_of_coeff_sum_eq_one_on
    (I := I) P.active (fun i z => P.partition i z) ω
    P.coeff_sum_eq_one_on x0 x1 hu

/-- Selected-partition version with the outward-first boundary sign included. -/
theorem outwardFirst_boundaryChartTransitionPullbackIntegrand_eq_sum_localized_on
    (P : SelectedBoxPartitionOfUnity I ω)
    (x0 x1 : M) {u : Fin n → Real}
    (hu :
      (extChartAt I x1).symm
        (ManifoldForm.chartTransition I x0 x1 (boundaryInclusion n u)) ∈ P.K) :
    outwardFirstBoundaryOrientationSign n *
        boundaryChartTransitionPullbackIntegrand I x0 x1 ω u =
      Finset.sum P.active fun i =>
        outwardFirstBoundaryOrientationSign n *
          boundaryChartTransitionPullbackIntegrand I x0 x1
            (ManifoldForm.localizedForm I (fun z => P.partition i z) ω) u :=
  outwardFirst_boundaryChartTransitionPullbackIntegrand_eq_sum_localized
    (I := I) P.active (fun i z => P.partition i z) ω
    P.coeff_sum_eq_one_on x0 x1 hu

end SelectedBoxPartitionOfUnity

end BoundaryScalarFromFormSum

section BoundaryMeasurePieceSumShape

universe c p a

variable {Chart : Type c} {Piece : Type p}
variable {α : Type a}

/-- Pointwise finite-sum respect for a scalar boundary representative gives the
literal `boundaryMeasurePieceSum` identity consumed by the reconstruction
route. -/
theorem boundaryIntegrand_eq_pieceSum_of_scalarRepresentation_respects_finiteSums
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (hrespect :
      ∀ y,
        boundaryIntegrand y =
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q =>
              boundaryPieceIntegrand x q y) :
    boundaryIntegrand =
      boundaryMeasurePieceSum activeCharts boundaryPieces
        boundaryPieceIntegrand := by
  funext y
  simpa [boundaryMeasurePieceSum] using hrespect y

/-- A.e. version of
`boundaryIntegrand_eq_pieceSum_of_scalarRepresentation_respects_finiteSums`. -/
theorem boundaryIntegrand_ae_eq_pieceSum_of_scalarRepresentation_respects_finiteSums
    [MeasurableSpace α] {μ : Measure α}
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (hrespect :
      ∀ y,
        boundaryIntegrand y =
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q =>
              boundaryPieceIntegrand x q y) :
    boundaryIntegrand =ᵐ[μ]
      boundaryMeasurePieceSum activeCharts boundaryPieces
        boundaryPieceIntegrand :=
  ae_of_all μ fun y =>
    congrFun
      (boundaryIntegrand_eq_pieceSum_of_scalarRepresentation_respects_finiteSums
        activeCharts boundaryPieces boundaryIntegrand boundaryPieceIntegrand
        hrespect) y

/-- Direct handoff from a scalar representative that respects selected finite
sums, plus zero-off support control, to the existing indicator reconstruction
shape. -/
theorem boundaryIntegrand_ae_eq_indicatorSum_of_scalarRepresentation_respects_finiteSums
    [MeasurableSpace α] {μ : Measure α}
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (hrespect :
      ∀ y,
        boundaryIntegrand y =
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q =>
              boundaryPieceIntegrand x q y)
    (hzero :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          ∀ y, y ∉ boundaryPieceSet x q →
            boundaryPieceIntegrand x q y = 0) :
    boundaryIntegrand =ᵐ[μ]
      boundaryMeasureIndicatorSum activeCharts boundaryPieces
        boundaryPieceSet boundaryPieceIntegrand := by
  exact
    boundaryScalarIntegrand_ae_eq_indicatorSum_of_pieceSum_eq_of_eq_zero_off
      (mu := μ) activeCharts boundaryPieces boundaryIntegrand
      boundaryPieceSet boundaryPieceIntegrand
      (boundaryIntegrand_eq_pieceSum_of_scalarRepresentation_respects_finiteSums
        activeCharts boundaryPieces boundaryIntegrand boundaryPieceIntegrand
        hrespect)
      hzero

end BoundaryMeasurePieceSumShape

end Stokes

end
