import Stokes.BoundaryChart.SelectedBox
import Stokes.BoundaryChart.TransitionCompactBox

/-!
# Boundary chart box selection from compact support

This file packages the compact-support selection step for boundary chart boxes.
The purely compact part is supplied by `exists_halfSpaceSupportBox_of_isCompact`;
the geometric fact that the resulting closed box lies in the chart-transition
domain remains an explicit input, as in the global interior box-selection layer.
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
Compact-support data for a selected boundary chart box.

The compact set `K` is the coordinate support set being boxed.  The selected
corners satisfy the boundary convention `a 0 = 0`, the coordinate order
`a ≤ b`, closed-box containment in the boundary chart domain, and support
containment in the half-space support box.
-/
structure BoundaryCompactBoxSelectionData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n) where
  /-- The compact coordinate support set being boxed. -/
  K : Set (Fin (n + 1) → Real)
  /-- Compactness of the coordinate support set. -/
  isCompact_K : IsCompact K
  /-- The transition-pullback topological support lies in the compact set. -/
  tsupport_subset_K :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K
  /-- The compact set lies in the ambient upper half-space. -/
  K_subset_upperHalfSpace : K ⊆ upperHalfSpace n
  /-- Lower corner of the selected boundary chart box. -/
  a : Fin (n + 1) → Real
  /-- Upper corner of the selected boundary chart box. -/
  b : Fin (n + 1) → Real
  /-- Boundary-face convention for selected boxes. -/
  ha0 : a 0 = 0
  /-- Coordinatewise order of the selected box corners. -/
  le : a ≤ b
  /-- The closed ambient box lies in the boundary chart transition domain. -/
  Icc_subset_domain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1
  /-- The compact support set lies in the half-space support box. -/
  K_subset_halfSpaceSupportBox : K ⊆ halfSpaceSupportBox a b

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}

/--
Selected boundary chart boxes put the transition-pullback representative away
from the artificial boundary of the chosen half-space box.
-/
theorem boundaryChartSelectedBox.artificialFaceSet_tsupport_disjoint
    {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    Disjoint (halfSpaceArtificialFaceSet a b)
      (tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω)) :=
  halfSpaceArtificialFaceSet_disjoint_tsupport_of_subset_halfSpaceSupportBox
    (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b hbox.tsupport_subset

/--
Artificial face terms vanish for a selected boundary chart box, stated directly
from the natural topological-support hypothesis carried by `boundaryChartSelectedBox`.
-/
theorem boundaryChartSelectedBox.boxRemainingFormFaceTerms_eq_zero
    {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    boxRemainingFormFaceTerms
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b = 0 :=
  boxRemainingFormFaceTerms_eq_zero_of_tsupport_subset_halfSpaceSupportBox'
    (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b hbox.tsupport_subset

/--
Boundary-chart local half-space Stokes from the natural selected-box support
hypothesis and smoothness on an ambient open neighborhood of the selected box.
-/
theorem boundaryChartSelectedBox.localStokes_transitionPullback_of_contDiffOn_isOpen
    {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hωU : ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    halfSpaceLocalBulkIntegral (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  simpa [halfSpaceBoundaryTransitionFormIntegral] using
    halfSpaceLocalStokes_of_tsupport_subset_halfSpaceSupportBox_contDiffOn'
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b hbox.le hbox.ha0
      hU hUbox hωU hbox.tsupport_subset

/--
`C^\infty` version of
`boundaryChartSelectedBox.localStokes_transitionPullback_of_contDiffOn_isOpen`.
-/
theorem boundaryChartSelectedBox.localStokes_transitionPullback_of_contDiffOn_isOpen_infty
    {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hωU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    halfSpaceLocalBulkIntegral (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω a b := by
  simpa [halfSpaceBoundaryTransitionFormIntegral] using
    halfSpaceLocalStokes_of_tsupport_subset_halfSpaceSupportBox_contDiffOn_infty'
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b hbox.le hbox.ha0
      hU hUbox hωU hbox.tsupport_subset

namespace BoundaryCompactBoxSelectionData

/-- The stored compact set is compact. -/
theorem isCompact (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    IsCompact D.K :=
  D.isCompact_K

/-- The transition-pullback support lies in the selected half-space support box. -/
theorem tsupport_subset_halfSpaceSupportBox
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      halfSpaceSupportBox D.a D.b :=
  D.tsupport_subset_K.trans D.K_subset_halfSpaceSupportBox

/-- The compact support package produces the existing selected-box predicate. -/
theorem selectedBox (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    boundaryChartSelectedBox I x0 x1 ω D.a D.b :=
  ⟨D.ha0, D.le, D.Icc_subset_domain, D.tsupport_subset_halfSpaceSupportBox⟩

/-- Closed-box containment in the source chart target. -/
theorem Icc_subset_target (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    Set.Icc D.a D.b ⊆ (extChartAt I x0).target := fun _ hy =>
  (D.Icc_subset_domain hy).1

/-- Closed-box containment in the chart overlap. -/
theorem Icc_subset_overlap (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    Set.Icc D.a D.b ⊆ ManifoldForm.chartOverlap I x0 x1 := fun _ hy =>
  (D.Icc_subset_domain hy).2

/-- Points of the lower-zero face lie in the selected closed ambient box. -/
theorem boundaryInclusion_mem_Icc
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω)
    {x : Fin n → Real} (hx : x ∈ lowerZeroFaceDomain D.a D.b) :
    boundaryInclusion n x ∈ Set.Icc D.a D.b :=
  boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain D.ha0 D.le hx

/-- Lower-zero face wrapper for the boundary chart domain containment. -/
theorem lowerZeroFace_subset_domain
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    ∀ x ∈ lowerZeroFaceDomain D.a D.b,
      boundaryInclusion n x ∈ boundaryChartDomain I x0 x1 :=
  D.selectedBox.boundaryFace_subset_domain

/-- Lower-zero face wrapper for the boundary-transition source predicate. -/
theorem lowerZeroFaceDomain_subset_boundaryChartTransitionBoundarySource
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    lowerZeroFaceDomain D.a D.b ⊆
      boundaryChartTransitionBoundarySource I x0 x1 :=
  lowerZeroFaceDomain_subset_boundaryChartTransitionBoundarySource_of_selectedBox D.selectedBox

/--
Half-space support-box wrapper for coordinate face coefficients of the
transition-pullback representative.
-/
theorem faceCoeffTSupportInHalfSpaceBox
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    boxFaceCoeffTSupportInHalfSpaceBox
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b :=
  boxFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset
    (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b
    D.tsupport_subset_halfSpaceSupportBox

/-- The selected half-space support box is disjoint from every artificial face. -/
theorem artificialFaces_tsupport_disjoint
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) D.a D.b)
        (tsupport
          (boxFormFaceCoeff
            (ManifoldForm.transitionPullbackInChart I x0 x1 ω) (0 : Fin (n + 1)))) ∧
      ∀ i : Fin n,
        Disjoint (boxUpperFaceSet i.succ D.a D.b)
            (tsupport
              (boxFormFaceCoeff
                (ManifoldForm.transitionPullbackInChart I x0 x1 ω) i.succ)) ∧
        Disjoint (boxLowerFaceSet i.succ D.a D.b)
            (tsupport
              (boxFormFaceCoeff
                (ManifoldForm.transitionPullbackInChart I x0 x1 ω) i.succ)) :=
  boxArtificialFaces_tsupport_disjoint_of_subset_halfSpaceSupportBox
    (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b
    D.faceCoeffTSupportInHalfSpaceBox

/--
Natural artificial-boundary disjointness for the selected compact-support
boundary box, before decomposing it into coordinate face coefficients.
-/
theorem artificialFaceSet_tsupport_disjoint
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    Disjoint (halfSpaceArtificialFaceSet D.a D.b)
      (tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω)) :=
  D.selectedBox.artificialFaceSet_tsupport_disjoint

/-- Artificial box faces vanish for the selected compact-support box. -/
theorem boxRemainingFormFaceTerms_eq_zero
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    boxRemainingFormFaceTerms
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b = 0 :=
  D.selectedBox.boxRemainingFormFaceTerms_eq_zero

/--
Boundary-chart local half-space Stokes for a compact-support selected box.
The support input is the natural `tsupport` containment stored in `D`; the only
analytic input left is smoothness on an ambient open neighborhood of the box.
-/
theorem localStokes_transitionPullback_of_contDiffOn_isOpen
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc D.a D.b ⊆ U)
    (hωU : ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    halfSpaceLocalBulkIntegral
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω D.a D.b :=
  D.selectedBox.localStokes_transitionPullback_of_contDiffOn_isOpen hU hUbox hωU

/-- `C^\infty` version of `localStokes_transitionPullback_of_contDiffOn_isOpen`. -/
theorem localStokes_transitionPullback_of_contDiffOn_isOpen_infty
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc D.a D.b ⊆ U)
    (hωU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    halfSpaceLocalBulkIntegral
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b =
      halfSpaceBoundarySign n *
        halfSpaceBoundaryTransitionFormIntegral I x0 x1 ω D.a D.b :=
  D.selectedBox.localStokes_transitionPullback_of_contDiffOn_isOpen_infty hU hUbox hωU

/--
Outward-normal-first spelling of the selected compact boundary chart local
Stokes theorem.
-/
theorem localStokes_transitionPullback_of_contDiffOn_isOpen_outwardFirst
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc D.a D.b ⊆ U)
    (hωU : ContDiffOn Real ⊤ (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    halfSpaceLocalBulkIntegral
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b =
      outwardFirstBoundaryChartIntegral I x0 x1 ω D.a D.b := by
  rw [outwardFirstBoundaryChartIntegral,
    ← halfSpaceBoundarySign_eq_outwardFirstBoundaryOrientationSign]
  exact D.localStokes_transitionPullback_of_contDiffOn_isOpen hU hUbox hωU

/--
Outward-normal-first `C^\infty` spelling of the selected compact boundary chart
local Stokes theorem.
-/
theorem localStokes_transitionPullback_of_contDiffOn_isOpen_outwardFirst_infty
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    (hUbox : Set.Icc D.a D.b ⊆ U)
    (hωU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    halfSpaceLocalBulkIntegral
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b =
      outwardFirstBoundaryChartIntegral I x0 x1 ω D.a D.b := by
  rw [outwardFirstBoundaryChartIntegral,
    ← halfSpaceBoundarySign_eq_outwardFirstBoundaryOrientationSign]
  exact D.localStokes_transitionPullback_of_contDiffOn_isOpen_infty hU hUbox hωU

end BoundaryCompactBoxSelectionData

namespace CompactCoordinateBoxSelection

/--
A boxed compact coordinate set gives a boundary selected box once the caller
supplies the boundary convention, domain containment, and the half-space
support-box containment.
-/
theorem boundaryChartSelectedBox_of_tsupport_subset_K {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (ha0 : B.a 0 = 0)
    (hdomain : Set.Icc B.a B.b ⊆ boundaryChartDomain I x0 x1)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ B.K)
    (hK : B.K ⊆ halfSpaceSupportBox B.a B.b) :
    boundaryChartSelectedBox I x0 x1 ω B.a B.b :=
  ⟨ha0, B.le, hdomain, hsupp.trans hK⟩

/--
Pack a `CompactCoordinateBoxSelection` as boundary compact box-selection data.
-/
def toBoundaryCompactBoxSelectionData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    (B : CompactCoordinateBoxSelection (Fin (n + 1) → Real))
    (ha0 : B.a 0 = 0)
    (hdomain : Set.Icc B.a B.b ⊆ boundaryChartDomain I x0 x1)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ B.K)
    (hhalf : B.K ⊆ upperHalfSpace n)
    (hK : B.K ⊆ halfSpaceSupportBox B.a B.b) :
    BoundaryCompactBoxSelectionData I x0 x1 ω where
  K := B.K
  isCompact_K := B.isCompact
  tsupport_subset_K := hsupp
  K_subset_upperHalfSpace := hhalf
  a := B.a
  b := B.b
  ha0 := ha0
  le := B.le
  Icc_subset_domain := hdomain
  K_subset_halfSpaceSupportBox := hK

end CompactCoordinateBoxSelection

/--
Build boundary compact box-selection data from a compact support set in the
upper half-space.

The `hdomain` hypothesis is the local chart-geometry input: the compactness
argument selects a half-space support box, and `hdomain` certifies that this
selected closed box is admissible for the boundary chart transition.
-/
theorem exists_boundaryCompactBoxSelectionData_of_isCompact {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    (hdomain :
      ∀ a b : Fin (n + 1) → Real,
        a 0 = 0 → a ≤ b → K ⊆ halfSpaceSupportBox a b →
          Set.Icc a b ⊆ boundaryChartDomain I x0 x1) :
    ∃ D : BoundaryCompactBoxSelectionData I x0 x1 ω, D.K = K := by
  rcases exists_halfSpaceSupportBox_of_isCompact hK hhalf with
    ⟨a, b, ha0, hle, hKbox⟩
  exact
    ⟨{ K := K
       isCompact_K := hK
       tsupport_subset_K := hsupp
       K_subset_upperHalfSpace := hhalf
       a := a
       b := b
       ha0 := ha0
       le := hle
       Icc_subset_domain := hdomain a b ha0 hle hKbox
       K_subset_halfSpaceSupportBox := hKbox },
      rfl⟩

/--
Existential compact-support boundary chart Stokes theorem.

The compact set `K` controls the topological support of the transition-pullback
representative.  The compact-support selection picks a half-space support box;
the selected box then has no artificial-boundary contribution, so the local
half-space Stokes theorem gives the outward-first boundary integral.
-/
theorem exists_boundaryCompactBoxSelectionData_localStokes_of_isCompact {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    (hdomain :
      ∀ a b : Fin (n + 1) → Real,
        a 0 = 0 → a ≤ b → K ⊆ halfSpaceSupportBox a b →
          Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    (hsmooth :
      ∀ D : BoundaryCompactBoxSelectionData I x0 x1 ω,
        D.K = K →
          ∃ U : Set (Fin (n + 1) → Real),
            IsOpen U ∧ Set.Icc D.a D.b ⊆ U ∧
              ContDiffOn Real ⊤
                (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    ∃ D : BoundaryCompactBoxSelectionData I x0 x1 ω,
      D.K = K ∧
        halfSpaceLocalBulkIntegral
            (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b =
          outwardFirstBoundaryChartIntegral I x0 x1 ω D.a D.b := by
  rcases exists_boundaryCompactBoxSelectionData_of_isCompact
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      hK hhalf hsupp hdomain with
    ⟨D, hDK⟩
  rcases hsmooth D hDK with ⟨U, hU, hUbox, hωU⟩
  exact
    ⟨D, hDK,
      D.localStokes_transitionPullback_of_contDiffOn_isOpen_outwardFirst
        hU hUbox hωU⟩

/--
Alias with the input order used by compact-support localization arguments:
first give a compact carrier `K`, then the support containment into it.
-/
theorem exists_boundaryCompactBoxSelectionData_localStokes_of_tsupport_subset_compact
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    (hhalf : K ⊆ upperHalfSpace n)
    (hdomain :
      ∀ a b : Fin (n + 1) → Real,
        a 0 = 0 → a ≤ b → K ⊆ halfSpaceSupportBox a b →
          Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    (hsmooth :
      ∀ D : BoundaryCompactBoxSelectionData I x0 x1 ω,
        D.K = K →
          ∃ U : Set (Fin (n + 1) → Real),
            IsOpen U ∧ Set.Icc D.a D.b ⊆ U ∧
              ContDiffOn Real ⊤
                (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    ∃ D : BoundaryCompactBoxSelectionData I x0 x1 ω,
      D.K = K ∧
        halfSpaceLocalBulkIntegral
            (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b =
          outwardFirstBoundaryChartIntegral I x0 x1 ω D.a D.b :=
  exists_boundaryCompactBoxSelectionData_localStokes_of_isCompact
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    hK hhalf hsupp hdomain hsmooth

/--
Existence form of selected boundary chart boxes from compact coordinate support.
-/
theorem exists_boundaryChartSelectedBox_of_isCompact {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    (hdomain :
      ∀ a b : Fin (n + 1) → Real,
        a 0 = 0 → a ≤ b → K ⊆ halfSpaceSupportBox a b →
          Set.Icc a b ⊆ boundaryChartDomain I x0 x1) :
    ∃ a b : Fin (n + 1) → Real,
      a 0 = 0 ∧ a ≤ b ∧ boundaryChartSelectedBox I x0 x1 ω a b := by
  rcases exists_boundaryCompactBoxSelectionData_of_isCompact
      (I := I) (x0 := x0) (x1 := x1) (ω := ω)
      hK hhalf hsupp hdomain with
    ⟨D, _hDK⟩
  exact ⟨D.a, D.b, D.ha0, D.le, D.selectedBox⟩

/--
Specialization where the transition-pullback topological support itself is the
compact coordinate set being boxed.
-/
theorem exists_boundaryCompactBoxSelectionData_of_compact_tsupport {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    (hK : IsCompact (tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω)))
    (hhalf :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        upperHalfSpace n)
    (hdomain :
      ∀ a b : Fin (n + 1) → Real,
        a 0 = 0 → a ≤ b →
          tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
            halfSpaceSupportBox a b →
          Set.Icc a b ⊆ boundaryChartDomain I x0 x1) :
    ∃ D : BoundaryCompactBoxSelectionData I x0 x1 ω,
      D.K = tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) :=
  exists_boundaryCompactBoxSelectionData_of_isCompact
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    hK hhalf (Subset.refl _) hdomain

/--
Existential local boundary-chart Stokes theorem when the transition-pullback
topological support itself is compact.
-/
theorem exists_boundaryCompactBoxSelectionData_localStokes_of_compact_tsupport
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    (hK : IsCompact (tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω)))
    (hhalf :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        upperHalfSpace n)
    (hdomain :
      ∀ a b : Fin (n + 1) → Real,
        a 0 = 0 → a ≤ b →
          tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
            halfSpaceSupportBox a b →
          Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    (hsmooth :
      ∀ D : BoundaryCompactBoxSelectionData I x0 x1 ω,
        D.K = tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) →
          ∃ U : Set (Fin (n + 1) → Real),
            IsOpen U ∧ Set.Icc D.a D.b ⊆ U ∧
              ContDiffOn Real ⊤
                (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    ∃ D : BoundaryCompactBoxSelectionData I x0 x1 ω,
      D.K = tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ∧
        halfSpaceLocalBulkIntegral
            (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b =
          outwardFirstBoundaryChartIntegral I x0 x1 ω D.a D.b :=
  exists_boundaryCompactBoxSelectionData_localStokes_of_isCompact
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    hK hhalf (Subset.refl _) hdomain hsmooth

/--
Selected-box existence directly from compact topological support of the
transition-pullback representative.
-/
theorem exists_boundaryChartSelectedBox_of_compact_tsupport {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    (hK : IsCompact (tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω)))
    (hhalf :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        upperHalfSpace n)
    (hdomain :
      ∀ a b : Fin (n + 1) → Real,
        a 0 = 0 → a ≤ b →
          tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
            halfSpaceSupportBox a b →
          Set.Icc a b ⊆ boundaryChartDomain I x0 x1) :
    ∃ a b : Fin (n + 1) → Real,
      a 0 = 0 ∧ a ≤ b ∧ boundaryChartSelectedBox I x0 x1 ω a b :=
  exists_boundaryChartSelectedBox_of_isCompact
    (I := I) (x0 := x0) (x1 := x1) (ω := ω)
    hK hhalf (Subset.refl _) hdomain

end ManifoldBoundary

end Stokes

end
