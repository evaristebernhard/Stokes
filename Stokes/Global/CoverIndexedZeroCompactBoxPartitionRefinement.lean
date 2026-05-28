import Stokes.Global.CoverIndexedFromSupportControlledCover
import Stokes.Global.CoverIndexedLocalStokes

/-!
# Box-level refinement of boundary partition pieces

This file records the next honest handoff for the compact-support represented
Stokes route.  A selected boundary chart piece may have to be refined into
finitely many smaller half-space boxes before the ambient chart transition is
controlled on each box.  The structure below keeps that refinement visible:
for every selected boundary index it carries a finite family of box
coefficients, a reconstruction identity over the compact support, and the
coordinate support facts needed by the half-space local Stokes theorem.

The important proved content is the support bridge.  If a refined coefficient
is manifold-side supported, on the compact set, inside its assigned
boundary-chart box, then its chart coefficient is supported in the corresponding
half-space support box on any compact coordinate carrier.  Consequently the
localized chart representative has `tsupport` inside that half-space box.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoordinateBridge

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {x0 x1 : M} {ρ : M → Real}
variable {coordSupport box : Set (Fin (n + 1) → Real)}
variable {chartBoxNeighborhood : Set M}

/--
Generic transition-coefficient support bridge for a non-self chart transition.

The existing selected-cover bridge handles the self-transition case.  Box-level
boundary refinement needs the same argument after the source chart has been
paired with a possibly different target chart.  The only genuinely charty
extra input is that the coordinate carrier lies both in the source chart target
and in the chart-overlap source.
-/
theorem transitionCoefficientInChart_tsupport_inter_coordSupport_subset_box
    (hcoordK :
      ∀ y ∈ coordSupport, (extChartAt I x0).symm y ∈ K)
    (hcoordTarget : coordSupport ⊆ (extChartAt I x0).target)
    (hcoordOverlap : coordSupport ⊆ ManifoldForm.chartOverlap I x0 x1)
    (hρ :
      tsupport ρ ∩ K ⊆ chartBoxNeighborhood)
    (hbox :
      chartBoxNeighborhood ⊆
        {p | p ∈ (extChartAt I x0).source ∧ (extChartAt I x0) p ∈ box}) :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ∩
        coordSupport ⊆
      box := by
  rintro y ⟨hycoeff, hycoord⟩
  have hρsupp :
      (extChartAt I x0).symm y ∈ tsupport ρ :=
    ManifoldForm.transitionCoefficientInChart_tsupport_mapsTo_tsupport
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (y := y)
      (hcoordTarget hycoord) (hcoordOverlap hycoord) hycoeff
  have hmanifold :
      (extChartAt I x0).symm y ∈ chartBoxNeighborhood :=
    hρ ⟨hρsupp, hcoordK y hycoord⟩
  have hboxmem :
      (extChartAt I x0) ((extChartAt I x0).symm y) ∈ box :=
    (hbox hmanifold).2
  rwa [(extChartAt I x0).right_inv (hcoordTarget hycoord)] at hboxmem

/--
Boundary half-space specialization of
`transitionCoefficientInChart_tsupport_inter_coordSupport_subset_box`.
-/
theorem transitionCoefficientInChart_tsupport_inter_coordSupport_subset_refinedHalfSpaceBox
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
  exact
    transitionCoefficientInChart_tsupport_inter_coordSupport_subset_box
      (I := I) (K := K) (x0 := x0) (x1 := x1) (ρ := ρ)
      (coordSupport := coordSupport) (box := halfSpaceSupportBox a b)
      (chartBoxNeighborhood := boundaryChartBoxNeighborhood I x0 a b)
      hcoordK hcoordTarget hcoordOverlap hρ
      (by
        intro p hp
        simpa [boundaryChartBoxNeighborhood] using hp)

end CoordinateBridge

section BoxRefinedPartition

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/-- The selected boundary-index type of a compact chart-box cover. -/
abbrev CoverIndexedBoundaryIndex
    (C : CompactSupportChartCoverSelection I K) : Type w :=
  {x : M // x ∈ C.boundaryCenters}

/--
Box-level refinement of the boundary part of a support-controlled selected
partition.

For each selected boundary chart `i`, `boundaryPieces i` is the finite family of
smaller half-space boxes used to refine that chart piece.  The coefficient
family reconstructs the original selected coefficient on `K`, while the final
`localized_tsupport_subset_halfSpaceSupportBox` field is the exact support
shape consumed by local half-space Stokes.
-/
structure CoverIndexedBoundaryBoxRefinedPartition
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (ω : ManifoldForm I M n) (BoundaryPiece : Type b) where
  /-- Finite local half-space boxes attached to each selected boundary chart. -/
  boundaryPieces : CoverIndexedBoundaryIndex (I := I) C → Finset BoundaryPiece
  /-- Source chart used for a refined box. -/
  sourceChart : CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → M
  /-- Target chart used for the transition-pullback representative. -/
  targetChart : CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → M
  /-- Refined scalar coefficient, intended as a subpartition of the boundary coefficient. -/
  coefficient :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → M → Real
  /-- Compact coordinate carrier for the base chart representative on a refined box. -/
  coordSupport :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece →
      Set (Fin (n + 1) → Real)
  /-- Lower corner of the refined half-space support box. -/
  lower :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → Fin (n + 1) → Real
  /-- Upper corner of the refined half-space support box. -/
  upper :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → Fin (n + 1) → Real
  /-- The refined coefficients reconstruct the original boundary coefficient on `K`. -/
  reconstruct_on_K :
    ∀ i x, x ∈ K →
      (∑ q ∈ boundaryPieces i, coefficient i q x) =
        P.partition (Sum.inr i) x
  /-- Base representative support is contained in the coordinate carrier. -/
  base_tsupport_subset_coordSupport :
    ∀ i q, q ∈ boundaryPieces i →
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (sourceChart i q) (targetChart i q) ω) ⊆
        coordSupport i q
  /-- The coordinate carrier lies in the upper half-space. -/
  coordSupport_subset_upperHalfSpace :
    ∀ i q, q ∈ boundaryPieces i → coordSupport i q ⊆ upperHalfSpace n
  /-- Compactness of each coordinate carrier. -/
  isCompact_coordSupport :
    ∀ i q, q ∈ boundaryPieces i → IsCompact (coordSupport i q)
  /-- The lower normal coordinate is normalized to the boundary face. -/
  lower_zero :
    ∀ i q, q ∈ boundaryPieces i → lower i q 0 = 0
  /-- Ordered box corners. -/
  lower_le_upper :
    ∀ i q, q ∈ boundaryPieces i → lower i q ≤ upper i q
  /-- Closed refined boxes lie in the boundary chart-transition domain. -/
  Icc_subset_boundaryChartDomain :
    ∀ i q, q ∈ boundaryPieces i →
      Icc (lower i q) (upper i q) ⊆
        boundaryChartDomain I (sourceChart i q) (targetChart i q)
  /--
  Coefficient-level support field consumed directly by the cover-indexed local
  Stokes theorem.
  -/
  coefficient_tsupport_inter_coordSupport_subset_halfSpaceSupportBox :
    ∀ i q, q ∈ boundaryPieces i →
      tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (sourceChart i q) (targetChart i q) (coefficient i q)) ∩
          coordSupport i q ⊆
        halfSpaceSupportBox (lower i q) (upper i q)
  /--
  Exact support field used downstream: each refined localized representative is
  supported in its assigned half-space support box.
  -/
  localized_tsupport_subset_halfSpaceSupportBox :
    ∀ i q, q ∈ boundaryPieces i →
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (sourceChart i q) (targetChart i q)
            (ManifoldForm.localizedForm I (coefficient i q) ω)) ⊆
        halfSpaceSupportBox (lower i q) (upper i q)

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
  (D : CoverIndexedBoundaryBoxRefinedPartition
    (I := I) (K := K) C P ω BoundaryPiece)

/-- The localized manifold form attached to a refined boundary box. -/
def localizedForm
    (i : CoverIndexedBoundaryIndex (I := I) C) (q : BoundaryPiece) :
    ManifoldForm I M n :=
  ManifoldForm.localizedForm I (D.coefficient i q) ω

/-- The local bulk integral attached to a refined boundary box. -/
def localBulkTerm
    (i : CoverIndexedBoundaryIndex (I := I) C) (q : BoundaryPiece) : Real :=
  projectLocalBulkIntegral I (D.sourceChart i q) (D.targetChart i q)
    (D.localizedForm i q) (D.lower i q) (D.upper i q)

/-- The outward-first boundary integral attached to a refined boundary box. -/
def localBoundaryTerm
    (i : CoverIndexedBoundaryIndex (I := I) C) (q : BoundaryPiece) : Real :=
  projectLocalBoundaryIntegral I (D.sourceChart i q) (D.targetChart i q)
    (D.localizedForm i q) (D.lower i q) (D.upper i q)

/-- Restatement of the stored support field in the shape used by half-space Stokes. -/
theorem localized_tsupport_subset_halfSpaceSupportBox'
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q)) ⊆
      halfSpaceSupportBox (D.lower i q) (D.upper i q) :=
  D.localized_tsupport_subset_halfSpaceSupportBox i q hq

/--
Pointwise reconstruction of the original boundary localized form from the
box-refined localized forms, on the compact support set.
-/
theorem sum_localizedForm_apply_eq_coverIndexLocalizedForm_apply
    (i : CoverIndexedBoundaryIndex (I := I) C) {x : M} (hxK : x ∈ K) :
    (∑ q ∈ D.boundaryPieces i, D.localizedForm i q x) =
      P.coverIndexLocalizedForm ω (Sum.inr i) x := by
  classical
  calc
    (∑ q ∈ D.boundaryPieces i, D.localizedForm i q x)
        = ∑ q ∈ D.boundaryPieces i, D.coefficient i q x • ω x := by
          simp [localizedForm]
    _ = (∑ q ∈ D.boundaryPieces i, D.coefficient i q x) • ω x := by
          rw [Finset.sum_smul]
    _ = P.partition (Sum.inr i) x • ω x := by
          rw [D.reconstruct_on_K i x hxK]
    _ = P.coverIndexLocalizedForm ω (Sum.inr i) x := by
          rfl

/--
The refined support data is exactly the input required by the cover-indexed
boundary half-space local Stokes finite-sum theorem.
-/
theorem boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_contDiffOn
    {U :
      CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece →
        Set (Fin (n + 1) → Real)}
    (hU :
      ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q, q ∈ D.boundaryPieces i → IsOpen (U i q))
    (hUbox :
      ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q, q ∈ D.boundaryPieces i →
          Icc (D.lower i q) (D.upper i q) ⊆ U i q)
    (hrhoU :
      ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q, q ∈ D.boundaryPieces i →
          ContDiffOn Real ⊤
            (ManifoldForm.transitionCoefficientInChart I
              (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
            (U i q))
    (homegaU :
      ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q, q ∈ D.boundaryPieces i →
          ContDiffOn Real ⊤
            (ManifoldForm.transitionPullbackInChart I
              (D.sourceChart i q) (D.targetChart i q) ω)
            (U i q)) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBoundaryTerm i q := by
  classical
  exact
    coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_contDiffOn
      (I := I) (omega := ω)
      (active := (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)))
      (boundaryPieces := D.boundaryPieces)
      (sourceChart := D.sourceChart) (targetChart := D.targetChart)
      (rho := D.coefficient) (K := D.coordSupport)
      (lower := D.lower) (upper := D.upper) (U := U)
      (fun i _hi q hq => D.isCompact_coordSupport i q hq)
      (fun i _hi q hq => D.coordSupport_subset_upperHalfSpace i q hq)
      (fun i _hi q hq => D.base_tsupport_subset_coordSupport i q hq)
      (fun i _hi q hq => D.lower_zero i q hq)
      (fun i _hi q hq => D.lower_le_upper i q hq)
      (fun i _hi q hq =>
        (D.coefficient_tsupport_inter_coordSupport_subset_halfSpaceSupportBox i q hq))
      (fun i _hi q hq => D.Icc_subset_boundaryChartDomain i q hq)
      hU hUbox hrhoU homegaU

end CoverIndexedBoundaryBoxRefinedPartition

/--
Constructor from a more natural refined-partition support package.

Instead of asking for the final localized `tsupport` field directly, callers
may provide:

* base chart support in each coordinate carrier;
* carrier membership in `K`, chart target, and chart overlap;
* manifold-side refined coefficient support inside the assigned boundary box.

The constructor proves the coordinate coefficient support and the localized
half-space support field.
-/
def CoverIndexedBoundaryBoxRefinedPartition.ofManifoldSupportControl
    (boundaryPieces :
      CoverIndexedBoundaryIndex (I := I) C → Finset BoundaryPiece)
    (sourceChart targetChart :
      CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → M)
    (coefficient :
      CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → M → Real)
    (coordSupport :
      CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece →
        Set (Fin (n + 1) → Real))
    (lower upper :
      CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece →
        Fin (n + 1) → Real)
    (reconstruct_on_K :
      ∀ i x, x ∈ K →
        (∑ q ∈ boundaryPieces i, coefficient i q x) =
          P.partition (Sum.inr i) x)
    (base_tsupport_subset_coordSupport :
      ∀ i q, q ∈ boundaryPieces i →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart i q) (targetChart i q) ω) ⊆
          coordSupport i q)
    (coordSupport_subset_upperHalfSpace :
      ∀ i q, q ∈ boundaryPieces i → coordSupport i q ⊆ upperHalfSpace n)
    (isCompact_coordSupport :
      ∀ i q, q ∈ boundaryPieces i → IsCompact (coordSupport i q))
    (lower_zero :
      ∀ i q, q ∈ boundaryPieces i → lower i q 0 = 0)
    (lower_le_upper :
      ∀ i q, q ∈ boundaryPieces i → lower i q ≤ upper i q)
    (Icc_subset_boundaryChartDomain :
      ∀ i q, q ∈ boundaryPieces i →
        Icc (lower i q) (upper i q) ⊆
          boundaryChartDomain I (sourceChart i q) (targetChart i q))
    (coordSupport_mapsTo_K :
      ∀ i q, q ∈ boundaryPieces i →
        ∀ y ∈ coordSupport i q, (extChartAt I (sourceChart i q)).symm y ∈ K)
    (coordSupport_subset_sourceTarget :
      ∀ i q, q ∈ boundaryPieces i →
        coordSupport i q ⊆ (extChartAt I (sourceChart i q)).target)
    (coordSupport_subset_overlap :
      ∀ i q, q ∈ boundaryPieces i →
        coordSupport i q ⊆
          ManifoldForm.chartOverlap I (sourceChart i q) (targetChart i q))
    (coefficient_tsupport_inter_K_subset_sourceBox :
      ∀ i q, q ∈ boundaryPieces i →
        tsupport (coefficient i q) ∩ K ⊆
          boundaryChartBoxNeighborhood I (sourceChart i q)
            (lower i q) (upper i q)) :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω BoundaryPiece where
  boundaryPieces := boundaryPieces
  sourceChart := sourceChart
  targetChart := targetChart
  coefficient := coefficient
  coordSupport := coordSupport
  lower := lower
  upper := upper
  reconstruct_on_K := reconstruct_on_K
  base_tsupport_subset_coordSupport := base_tsupport_subset_coordSupport
  coordSupport_subset_upperHalfSpace := coordSupport_subset_upperHalfSpace
  isCompact_coordSupport := isCompact_coordSupport
  lower_zero := lower_zero
  lower_le_upper := lower_le_upper
  Icc_subset_boundaryChartDomain := Icc_subset_boundaryChartDomain
  coefficient_tsupport_inter_coordSupport_subset_halfSpaceSupportBox := by
    intro i q hq
    exact
      transitionCoefficientInChart_tsupport_inter_coordSupport_subset_refinedHalfSpaceBox
        (I := I) (K := K) (x0 := sourceChart i q)
        (x1 := targetChart i q) (ρ := coefficient i q)
        (coordSupport := coordSupport i q)
        (a := lower i q) (b := upper i q)
        (coordSupport_mapsTo_K i q hq)
        (coordSupport_subset_sourceTarget i q hq)
        (coordSupport_subset_overlap i q hq)
        (coefficient_tsupport_inter_K_subset_sourceBox i q hq)
  localized_tsupport_subset_halfSpaceSupportBox := by
    intro i q hq
    exact
      ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
        (I := I) (x0 := sourceChart i q) (x1 := targetChart i q)
        (ρ := coefficient i q) (ω := ω)
        (C := coordSupport i q) (a := lower i q) (b := upper i q)
        (base_tsupport_subset_coordSupport i q hq)
        (transitionCoefficientInChart_tsupport_inter_coordSupport_subset_refinedHalfSpaceBox
          (I := I) (K := K) (x0 := sourceChart i q)
          (x1 := targetChart i q) (ρ := coefficient i q)
          (coordSupport := coordSupport i q)
          (a := lower i q) (b := upper i q)
          (coordSupport_mapsTo_K i q hq)
          (coordSupport_subset_sourceTarget i q hq)
          (coordSupport_subset_overlap i q hq)
          (coefficient_tsupport_inter_K_subset_sourceBox i q hq))

end BoxRefinedPartition

end Stokes

end
