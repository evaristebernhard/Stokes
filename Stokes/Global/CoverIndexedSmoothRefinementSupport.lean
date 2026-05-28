import Stokes.Global.CoverIndexedZeroCompactSmoothBoxRefinement
import Stokes.Global.TransitionCoefficientSupportBridge

/-!
# Strong support lemmas for cover-indexed smooth refinements

The older refined-partition API mostly used support control after intersecting
with the compact support set `K`.  For the zero/localized route we also need the
global support information coming from the refined smooth subpartition itself.

The key point is small but useful: if

`D.coefficient i q = P.partition (Sum.inr i) * D.subpartition i q`,

then the topological support of the product is contained in the topological
support of the subpartition coefficient.  Since
`SmoothPartitionOfUnity.IsSubordinate` is already a global
`tsupport ⊆ ambientOpen`, this gives global support of the refined coefficient
inside the selected boundary chart box, without using `K`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section SmoothRefinementSupport

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b} [DecidableEq BoundaryPiece]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace BoundarySmoothBoxRefinement

variable
  (D : BoundarySmoothBoxRefinement
    (I := I) (K := K) C P BoundaryPiece)

/--
Global support of a refined boundary coefficient in the ambient open set used
for the smooth subpartition.

Unlike `coefficient_tsupport_inter_K_subset_boundaryChartBox`, this does not
intersect with `K`: it uses global subordination of the smooth subpartition and
the elementary support inclusion for products.
-/
theorem coefficient_tsupport_subset_ambientOpen
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i) :
    tsupport (D.coefficient i q) ⊆ D.ambientOpen i q := by
  intro x hx
  have hcoeff_eq :
      D.coefficient i q =
        (fun x => P.partition (Sum.inr i) x *
          D.subpartition i ⟨q, hq⟩ x) := by
    funext x
    simp [BoundarySmoothBoxRefinement.coefficient, hq]
  have hx_product :
      x ∈ tsupport
        (fun x => P.partition (Sum.inr i) x *
          D.subpartition i ⟨q, hq⟩ x) := by
    simpa [hcoeff_eq] using hx
  have hx_sub :
      x ∈ tsupport (D.subpartition i ⟨q, hq⟩) :=
    (tsupport_mul_subset_right
      (f := P.partition (Sum.inr i))
      (g := D.subpartition i ⟨q, hq⟩)) hx_product
  exact D.subpartition_subordinate i ⟨q, hq⟩ hx_sub

/--
Global support of a refined boundary coefficient in its selected boundary
chart box.
-/
theorem coefficient_tsupport_subset_boundaryChartBox
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i) :
    tsupport (D.coefficient i q) ⊆
      boundaryChartBoxNeighborhood I (D.sourceChart i q)
        (D.lower i q) (D.upper i q) :=
  (D.coefficient_tsupport_subset_ambientOpen i hq).trans
    (D.ambientOpen_subset_boundaryChartBox i q hq)

/--
Coordinate-support form of the preceding lemma for a totalized transition
coefficient.

The statement deliberately intersects with a coordinate carrier that is known
to lie in the source chart target and the source-to-target chart overlap.  It
does not claim any support control for `transitionCoefficientInChart` outside
the domain where the totalized chart expression represents a genuine chart
transition.
-/
theorem transitionCoefficientInChart_tsupport_inter_coordSupport_subset_halfSpaceBox
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i)
    (targetChart : M)
    (coordSupport : Set (Fin (n + 1) → Real))
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (D.sourceChart i q)).target)
    (hcoordOverlap :
      coordSupport ⊆
        ManifoldForm.chartOverlap I (D.sourceChart i q) targetChart) :
    tsupport
        (ManifoldForm.transitionCoefficientInChart I
          (D.sourceChart i q) targetChart (D.coefficient i q)) ∩
        coordSupport ⊆
      halfSpaceSupportBox (D.lower i q) (D.upper i q) := by
  rintro y ⟨hycoeff, hycoord⟩
  have hcoeff_tsupport :
      (extChartAt I (D.sourceChart i q)).symm y ∈
        tsupport (D.coefficient i q) :=
    ManifoldForm.transitionCoefficientInChart_tsupport_mapsTo_tsupport
      (I := I) (x0 := D.sourceChart i q) (x1 := targetChart)
      (ρ := D.coefficient i q) (y := y)
      (hcoordTarget hycoord) (hcoordOverlap hycoord) hycoeff
  have hmanifold :
      (extChartAt I (D.sourceChart i q)).symm y ∈
        boundaryChartBoxNeighborhood I (D.sourceChart i q)
          (D.lower i q) (D.upper i q) :=
    D.coefficient_tsupport_subset_boundaryChartBox i hq hcoeff_tsupport
  have hbox :
      (extChartAt I (D.sourceChart i q))
          ((extChartAt I (D.sourceChart i q)).symm y) ∈
        halfSpaceSupportBox (D.lower i q) (D.upper i q) := by
    simpa [boundaryChartBoxNeighborhood] using hmanifold.2
  rwa [(extChartAt I (D.sourceChart i q)).right_inv
    (hcoordTarget hycoord)] at hbox

/--
Self-chart specialization of
`transitionCoefficientInChart_tsupport_inter_coordSupport_subset_halfSpaceBox`.
-/
theorem transitionCoefficientInChart_self_tsupport_inter_coordSupport_subset_halfSpaceBox
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i)
    (coordSupport : Set (Fin (n + 1) → Real))
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (D.sourceChart i q)).target)
    (hcoordOverlap :
      coordSupport ⊆
        ManifoldForm.chartOverlap I (D.sourceChart i q) (D.sourceChart i q)) :
    tsupport
        (ManifoldForm.transitionCoefficientInChart I
          (D.sourceChart i q) (D.sourceChart i q) (D.coefficient i q)) ∩
        coordSupport ⊆
      halfSpaceSupportBox (D.lower i q) (D.upper i q) :=
  D.transitionCoefficientInChart_tsupport_inter_coordSupport_subset_halfSpaceBox
    i hq (D.sourceChart i q) coordSupport hcoordTarget hcoordOverlap

end BoundarySmoothBoxRefinement

end SmoothRefinementSupport

end Stokes

end
