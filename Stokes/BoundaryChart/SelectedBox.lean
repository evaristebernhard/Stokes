import Stokes.BoundaryChart.Basic

/-!
# Selected boundary chart boxes

This file was split out of Stokes.HalfSpace as part of the M6.0
module-structure pass.  The theorem statements and proofs are intended to
remain identical to the monolithic version.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
A selected half-space box that can be used inside a boundary chart transition.

It records the boundary-face convention `a 0 = 0`, the nondegenerate box order,
the fact that the closed box is contained in the chart transition domain, and
the compact-support condition needed to kill artificial faces.
-/
def boundaryChartSelectedBox {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Prop :=
  a 0 = 0 ∧ a ≤ b ∧ Set.Icc a b ⊆ boundaryChartDomain I x0 x1 ∧
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      halfSpaceSupportBox a b

theorem boundaryChartSelectedBox.mk_of_subsets {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (htarget : Set.Icc a b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      halfSpaceSupportBox a b) :
    boundaryChartSelectedBox I x0 x1 ω a b :=
  ⟨ha0, hle, fun _ hy => ⟨htarget hy, hoverlap hy⟩, hsupp⟩

theorem boundaryChartSelectedBox.ha0 {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    a 0 = 0 :=
  hbox.1

theorem boundaryChartSelectedBox.le {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    a ≤ b :=
  hbox.2.1

theorem boundaryChartSelectedBox.Icc_subset_domain {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    Set.Icc a b ⊆ boundaryChartDomain I x0 x1 :=
  hbox.2.2.1

theorem boundaryChartSelectedBox.tsupport_subset {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      halfSpaceSupportBox a b :=
  hbox.2.2.2

theorem boundaryChartSelectedBox.boundaryFace_subset_domain {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    ∀ x ∈ lowerZeroFaceDomain a b,
      boundaryInclusion n x ∈ boundaryChartDomain I x0 x1 := by
  intro x hx
  exact hbox.Icc_subset_domain
    (boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain hbox.ha0 hbox.le hx)

theorem lowerZeroFaceDomain_subset_boundaryChartTransitionBoundarySource_of_selectedBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    lowerZeroFaceDomain a b ⊆
      boundaryChartTransitionBoundarySource I x0 x1 := by
  intro u hu
  exact hbox.boundaryFace_subset_domain u hu

theorem boundaryChartSelectedBox.boundaryFace_subset_target {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    ∀ x ∈ lowerZeroFaceDomain a b,
      boundaryInclusion n x ∈ (extChartAt I x0).target := by
  intro x hx
  exact (hbox.boundaryFace_subset_domain x hx).1

theorem boundaryChartSelectedBox.boundaryFace_subset_overlap {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    ∀ x ∈ lowerZeroFaceDomain a b,
      boundaryInclusion n x ∈ ManifoldForm.chartOverlap I x0 x1 := by
  intro x hx
  exact (hbox.boundaryFace_subset_domain x hx).2

theorem boundaryChartSelectedBox.boundaryFace_subset_range {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    ∀ x ∈ lowerZeroFaceDomain a b, boundaryInclusion n x ∈ range I := by
  intro x hx
  exact extChartAt_target_subset_range x0 (hbox.boundaryFace_subset_target x hx)

/--
Selected chart boxes provide the derivative hypothesis needed by mathlib's
Euclidean change-of-variables theorem for the boundary chart transition.
-/
theorem boundaryChartTransition_hasFDerivWithinAt_of_selectedBox {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H} [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    ∀ u ∈ lowerZeroFaceDomain a b,
      HasFDerivWithinAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u)
        (lowerZeroFaceDomain a b) u := by
  intro u hu
  exact boundaryChartTransition_hasFDerivWithinAt x0 x1
    hbox.boundaryFace_subset_range
    (hbox.boundaryFace_subset_target u hu)
    (hbox.boundaryFace_subset_overlap u hu)

/--
A selected boundary chart box together with an ambient smooth extension
neighborhood for the total model-coordinate representative.

The ambient extension is separate from `boundaryChartDomain`: for genuine
manifolds with boundary, chart targets are generally only relatively open in
`range I`, so the ambient open set needed by the current `extDeriv`-based box
Stokes theorem cannot be inferred from `ChartwiseSmooth` alone.
-/
def boundaryChartExtendedBox {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Prop :=
  boundaryChartSelectedBox I x0 x1 ω a b ∧
    ∃ U : Set (Fin (n + 1) → Real),
      IsOpen U ∧ Set.Icc a b ⊆ U ∧
        ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U

theorem boundaryChartExtendedBox.mk {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hselected : boundaryChartSelectedBox I x0 x1 ω a b)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hωU : ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    boundaryChartExtendedBox I x0 x1 ω a b :=
  ⟨hselected, ⟨U, hU, hUbox, hωU⟩⟩

theorem boundaryChartExtendedBox.mk_of_subsets {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (htarget : Set.Icc a b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      halfSpaceSupportBox a b)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hωU : ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    boundaryChartExtendedBox I x0 x1 ω a b :=
  boundaryChartExtendedBox.mk
    (boundaryChartSelectedBox.mk_of_subsets ha0 hle htarget hoverlap hsupp)
    hU hUbox hωU

theorem boundaryChartExtendedBox.selectedBox {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartExtendedBox I x0 x1 ω a b) :
    boundaryChartSelectedBox I x0 x1 ω a b :=
  hbox.1

theorem boundaryChartExtendedBox.exists_smooth_nhds {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartExtendedBox I x0 x1 ω a b) :
    ∃ U : Set (Fin (n + 1) → Real),
      IsOpen U ∧ Set.Icc a b ⊆ U ∧
        ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U :=
  hbox.2

theorem boundaryChartExtendedBox.boundaryFace_subset_overlap {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartExtendedBox I x0 x1 ω a b) :
    ∀ x ∈ lowerZeroFaceDomain a b,
      boundaryInclusion n x ∈ ManifoldForm.chartOverlap I x0 x1 :=
  hbox.selectedBox.boundaryFace_subset_overlap

/--
The half-space boundary integral fed by a chart-transition pullback of a
manifold form.
-/
def halfSpaceBoundaryTransitionFormIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  halfSpaceBoundaryFormIntegral (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b

/-- Boundary integral of the `x0` chart representative itself. -/
def halfSpaceBoundaryInChartIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  halfSpaceBoundaryFormIntegral (ManifoldForm.inChart I x0 ω) a b

/--
Boundary integral of the `x0` chart representative with the boundary
orientation induced by the outward-normal-first convention.
-/
def outwardFirstBoundaryInChartIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  outwardFirstBoundaryOrientationSign n *
    halfSpaceBoundaryInChartIntegral I x0 ω a b

/--
The boundary-chart integral with the boundary orientation induced by the
outward-normal-first convention.
-/
def outwardFirstBoundaryChartIntegral {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Real :=
  outwardFirstBoundaryOrientationSign n *
    halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b

theorem outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) :
    outwardFirstBoundaryChartIntegral I x0 x1 ω a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  rw [outwardFirstBoundaryChartIntegral,
    ← halfSpaceBoundarySign_eq_outwardFirstBoundaryOrientationSign]

end ManifoldBoundary

end Stokes

end
