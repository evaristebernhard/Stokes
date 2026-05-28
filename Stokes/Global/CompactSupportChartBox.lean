import Stokes.Global.ChartCompactImage
import Stokes.Global.CoefficientBoxSupport

/-!
# Compact-support chart boxes

This file provides the natural input layer for chart-box selection: a chart
representative has topological support contained in a compact coordinate set
`K`.  In finite real coordinate spaces, the compact set selects a closed
coordinate box.  The genuinely local chart-geometry facts, such as target and
overlap containment of the selected box, remain explicit hypotheses.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false

universe u v w

section ChartCompactSupport

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [Preorder E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Compact coordinate support for a transition-pullback chart representative.

This is the direct input expected from compact-support arguments: the chart
representative's `tsupport` lies in a compact coordinate set `K`.
-/
structure ChartCompactSupportData
    (I : ModelWithCorners Real E H) (x0 x1 : M) (ω : ManifoldForm I M k) where
  /-- Compact coordinate set controlling the chart representative. -/
  K : Set E
  /-- Compactness of the coordinate support set. -/
  isCompact_K : IsCompact K
  /-- The chart representative is topologically supported in `K`. -/
  tsupport_subset_K :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K

namespace ChartCompactSupportData

variable {I : ModelWithCorners Real E H} {x0 x1 : M} {ω : ManifoldForm I M k}

/-- Constructor from the explicit compact support data. -/
def of (K : Set E) (hK : IsCompact K)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K) :
    ChartCompactSupportData I x0 x1 ω where
  K := K
  isCompact_K := hK
  tsupport_subset_K := hsupp

/--
Constructor from a compact chart-image package.  The compact image theorem is
supplied by `ChartCompactImage`; the support containment remains the analytic
input for the particular form.
-/
def ofChartCompactImage
    (C : ChartCompactImage I x0)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        C.coordSupport) :
    ChartCompactSupportData I x0 x1 ω where
  K := C.coordSupport
  isCompact_K := C.isCompact_coordSupport
  tsupport_subset_K := hsupp

-- The stored compact coordinate support is compact.
omit [Preorder E] in
theorem isCompact (D : ChartCompactSupportData I x0 x1 ω) :
    IsCompact D.K :=
  D.isCompact_K

/-- Use an already selected compact coordinate box to bound the chart support. -/
theorem tsupport_subset_Icc_of_box
    (D : ChartCompactSupportData I x0 x1 ω)
    (B : CompactCoordinateBoxSelection E) (hB : B.K = D.K) :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      Set.Icc B.a B.b := by
  intro y hy
  exact B.subset_Icc (by simpa [hB] using D.tsupport_subset_K hy)

/-- Package compact chart support and a selected compact box as an interior selected box. -/
theorem selectedBox_of_box
    (D : ChartCompactSupportData I x0 x1 ω)
    (B : CompactCoordinateBoxSelection E) (hB : B.K = D.K)
    (htarget : Set.Icc B.a B.b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc B.a B.b ⊆ ManifoldForm.chartOverlap I x0 x1) :
    interiorChartSelectedBox I x0 x1 ω B.a B.b :=
  CompactCoordinateBoxSelection.interiorChartSelectedBox_of_tsupport_subset B
    (by intro y hy; simpa [hB] using D.tsupport_subset_K hy)
    htarget hoverlap

end ChartCompactSupportData

end ChartCompactSupport

section PiRealChartCompactSupport

variable {ι : Type u} [Fintype ι]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real (ι → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M k}

namespace ChartCompactSupportData

/-- The selected compact coordinate box attached to compact chart support. -/
def box (D : ChartCompactSupportData I x0 x1 ω) :
    CompactCoordinateBoxSelection (ι → Real) :=
  Classical.choose (exists_compactCoordinateBoxSelection_piReal D.isCompact_K)

@[simp]
theorem box_K_eq (D : ChartCompactSupportData I x0 x1 ω) :
    D.box.K = D.K :=
  Classical.choose_spec (exists_compactCoordinateBoxSelection_piReal D.isCompact_K)

/-- The chart representative's topological support lies in the selected box. -/
theorem tsupport_subset_box (D : ChartCompactSupportData I x0 x1 ω) :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      Set.Icc D.box.a D.box.b :=
  D.tsupport_subset_Icc_of_box D.box D.box_K_eq

/--
Compact chart support produces an interior selected box once the selected
closed box is known to lie in the relevant chart target and overlap.
-/
theorem selectedBox
    (D : ChartCompactSupportData I x0 x1 ω)
    (htarget : Set.Icc D.box.a D.box.b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc D.box.a D.box.b ⊆ ManifoldForm.chartOverlap I x0 x1) :
    interiorChartSelectedBox I x0 x1 ω D.box.a D.box.b :=
  D.selectedBox_of_box D.box D.box_K_eq htarget hoverlap

end ChartCompactSupportData

end PiRealChartCompactSupport

section ActiveChartCompactSupport

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H}

/--
Compact coordinate support data for every active chart representative.

This is the pre-box API for `CompactActiveBoxData`: users provide the compact
coordinate sets and support containments; the finite real-coordinate section
below chooses boxes simultaneously.
-/
structure ActiveChartCompactSupportData
    (P : FiniteActiveOnCompact (M := M) I) (ω : ManifoldForm I M k) where
  /-- Compact coordinate support for each active chart index. -/
  coordSupport : M → Set E
  /-- Compactness of each active coordinate support. -/
  isCompact_coordSupport :
    ∀ i ∈ P.active, IsCompact (coordSupport i)
  /-- Each active chart representative is supported in its compact coordinate set. -/
  tsupport_subset_coordSupport :
    ∀ i ∈ P.active,
      tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆ coordSupport i

namespace ActiveChartCompactSupportData

variable {P : FiniteActiveOnCompact (M := M) I} {ω : ManifoldForm I M k}

/-- Constructor from explicit active compact coordinate supports. -/
def of (coordSupport : M → Set E)
    (hcompact : ∀ i ∈ P.active, IsCompact (coordSupport i))
    (hsupp :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          coordSupport i) :
    ActiveChartCompactSupportData P ω where
  coordSupport := coordSupport
  isCompact_coordSupport := hcompact
  tsupport_subset_coordSupport := hsupp

/--
Constructor from compact chart images.  This reuses the compact-image proof
from `ChartCompactImage`; the form support containment remains explicit.
-/
def ofChartCompactImages
    (C : ActiveChartCompactImages (I := I) P)
    (hsupp :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          C.coordSupport i) :
    ActiveChartCompactSupportData P ω where
  coordSupport := C.coordSupport
  isCompact_coordSupport := fun _ hi => C.isCompact_coordSupport hi
  tsupport_subset_coordSupport := hsupp

/-- The single-chart compact-support package at an active index. -/
def chartSupport
    (D : ActiveChartCompactSupportData P ω) (i : M) (hi : i ∈ P.active) :
    ChartCompactSupportData I i i ω where
  K := D.coordSupport i
  isCompact_K := D.isCompact_coordSupport i hi
  tsupport_subset_K := D.tsupport_subset_coordSupport i hi

@[simp]
theorem chartSupport_K
    (D : ActiveChartCompactSupportData P ω) {i : M} (hi : i ∈ P.active) :
    (D.chartSupport i hi).K = D.coordSupport i :=
  rfl

end ActiveChartCompactSupportData

end ActiveChartCompactSupport

section PiRealActiveChartCompactSupport

variable {ι : Type u} [Fintype ι]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real (ι → Real) H}
variable {P : FiniteActiveOnCompact (M := M) I}
variable {ω : ManifoldForm I M k}

namespace ActiveChartCompactSupportData

/-- Simultaneously selected boxes for the active compact chart supports. -/
def box (D : ActiveChartCompactSupportData P ω) :
    M → CompactCoordinateBoxSelection (ι → Real) :=
  Classical.choose
    (exists_activeCompactCoordinateBoxSelections_piReal (I := I) P D.coordSupport
      D.isCompact_coordSupport)

@[simp]
theorem box_K_eq_coordSupport
    (D : ActiveChartCompactSupportData P ω) {i : M} (hi : i ∈ P.active) :
    (D.box i).K = D.coordSupport i :=
  Classical.choose_spec
    (exists_activeCompactCoordinateBoxSelections_piReal (I := I) P D.coordSupport
      D.isCompact_coordSupport) i hi

/-- Active chart support is contained in its selected box. -/
theorem tsupport_subset_box
    (D : ActiveChartCompactSupportData P ω) {i : M} (hi : i ∈ P.active) :
    tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
      Set.Icc (D.box i).a (D.box i).b := by
  intro y hy
  exact (D.box i).subset_Icc (by
    simpa [D.box_K_eq_coordSupport hi] using
      D.tsupport_subset_coordSupport i hi hy)

/--
Build `CompactActiveBoxData` from compact supports for active chart
representatives.  The selected boxes are chosen here; chart target and overlap
containments remain explicit geometric inputs.
-/
def toCompactActiveBoxData
    (D : ActiveChartCompactSupportData P ω)
    (htarget :
      ∀ i ∈ P.active,
        Set.Icc (D.box i).a (D.box i).b ⊆ (extChartAt I i).target)
    (hoverlap :
      ∀ i ∈ P.active,
        Set.Icc (D.box i).a (D.box i).b ⊆ ManifoldForm.chartOverlap I i i) :
    CompactActiveBoxData I ω where
  finiteActive := P
  coordSupport := D.coordSupport
  isCompact_coordSupport := D.isCompact_coordSupport
  box := D.box
  box_K_eq_coordSupport := fun _ hi => D.box_K_eq_coordSupport hi
  tsupport_subset_coordSupport := D.tsupport_subset_coordSupport
  Icc_subset_target := htarget
  Icc_subset_overlap := hoverlap

@[simp]
theorem toCompactActiveBoxData_finiteActive
    (D : ActiveChartCompactSupportData P ω)
    (htarget :
      ∀ i ∈ P.active,
        Set.Icc (D.box i).a (D.box i).b ⊆ (extChartAt I i).target)
    (hoverlap :
      ∀ i ∈ P.active,
        Set.Icc (D.box i).a (D.box i).b ⊆ ManifoldForm.chartOverlap I i i) :
    (D.toCompactActiveBoxData htarget hoverlap).finiteActive = P :=
  rfl

@[simp]
theorem toCompactActiveBoxData_coordSupport
    (D : ActiveChartCompactSupportData P ω)
    (htarget :
      ∀ i ∈ P.active,
        Set.Icc (D.box i).a (D.box i).b ⊆ (extChartAt I i).target)
    (hoverlap :
      ∀ i ∈ P.active,
        Set.Icc (D.box i).a (D.box i).b ⊆ ManifoldForm.chartOverlap I i i) :
    (D.toCompactActiveBoxData htarget hoverlap).coordSupport =
      D.coordSupport :=
  rfl

@[simp]
theorem toCompactActiveBoxData_box
    (D : ActiveChartCompactSupportData P ω)
    (htarget :
      ∀ i ∈ P.active,
        Set.Icc (D.box i).a (D.box i).b ⊆ (extChartAt I i).target)
    (hoverlap :
      ∀ i ∈ P.active,
        Set.Icc (D.box i).a (D.box i).b ⊆ ManifoldForm.chartOverlap I i i) :
    (D.toCompactActiveBoxData htarget hoverlap).box = D.box :=
  rfl

end ActiveChartCompactSupportData

end PiRealActiveChartCompactSupport

section CoefficientChartCompactSupport

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [Preorder E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Compact coordinate support for a localized coefficient written in transition
chart coordinates.
-/
structure CoefficientChartCompactSupportData
    (I : ModelWithCorners Real E H) (x0 x1 : M) (ρ : M → Real) where
  /-- Compact coordinate set controlling the chart coefficient. -/
  K : Set E
  /-- Compactness of the coefficient support set. -/
  isCompact_K : IsCompact K
  /-- The chart coefficient's `tsupport` is contained in `K`. -/
  coefficient_tsupport_subset_K :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ K

namespace CoefficientChartCompactSupportData

variable {I : ModelWithCorners Real E H} {x0 x1 : M} {ρ : M → Real}

/-- Constructor from the explicit compact coefficient support data. -/
def of (K : Set E) (hK : IsCompact K)
    (hsupp :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ K) :
    CoefficientChartCompactSupportData I x0 x1 ρ where
  K := K
  isCompact_K := hK
  coefficient_tsupport_subset_K := hsupp

-- The stored coefficient support set is compact.
omit [Preorder E] in
theorem isCompact (D : CoefficientChartCompactSupportData I x0 x1 ρ) :
    IsCompact D.K :=
  D.isCompact_K

/-- Use an already selected compact coordinate box to package coefficient support. -/
def toCoefficientBoxSupportData
    (D : CoefficientChartCompactSupportData I x0 x1 ρ)
    (B : CompactCoordinateBoxSelection E) (hB : B.K = D.K) :
    CoefficientBoxSupportData I x0 x1 ρ B.a B.b :=
  B.coefficientBoxSupportData (by
    intro y hy
    simpa [hB] using D.coefficient_tsupport_subset_K hy)

/--
Use an already selected compact coordinate box to build localized support
control.  The target and overlap containments are the remaining chart-geometry
inputs.
-/
def toLocalizedSupportControl {k : Nat}
    (D : CoefficientChartCompactSupportData I x0 x1 ρ)
    (B : CompactCoordinateBoxSelection E) (hB : B.K = D.K)
    (ω : ManifoldForm I M k)
    (htarget : Set.Icc B.a B.b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc B.a B.b ⊆ ManifoldForm.chartOverlap I x0 x1) :
    LocalizedSupportControl I x0 x1 ρ ω B.a B.b :=
  (D.toCoefficientBoxSupportData B hB).toLocalizedSupportControl ω htarget hoverlap

end CoefficientChartCompactSupportData

end CoefficientChartCompactSupport

section PiRealCoefficientChartCompactSupport

variable {ι : Type u} [Fintype ι]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real (ι → Real) H}
variable {x0 x1 : M} {ρ : M → Real}

namespace CoefficientChartCompactSupportData

/-- The selected compact coordinate box attached to coefficient chart support. -/
def box (D : CoefficientChartCompactSupportData I x0 x1 ρ) :
    CompactCoordinateBoxSelection (ι → Real) :=
  Classical.choose (exists_compactCoordinateBoxSelection_piReal D.isCompact_K)

@[simp]
theorem box_K_eq (D : CoefficientChartCompactSupportData I x0 x1 ρ) :
    D.box.K = D.K :=
  Classical.choose_spec (exists_compactCoordinateBoxSelection_piReal D.isCompact_K)

/-- The coefficient chart support lies in the selected box. -/
theorem coefficient_tsupport_subset_box
    (D : CoefficientChartCompactSupportData I x0 x1 ρ) :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆
      Set.Icc D.box.a D.box.b := by
  intro y hy
  exact D.box.subset_Icc (by
    simpa [D.box_K_eq] using D.coefficient_tsupport_subset_K hy)

/-- Package the automatically selected box as coefficient box-support data. -/
def coefficientBoxSupportData
    (D : CoefficientChartCompactSupportData I x0 x1 ρ) :
    CoefficientBoxSupportData I x0 x1 ρ D.box.a D.box.b :=
  D.toCoefficientBoxSupportData D.box D.box_K_eq

/--
Compact coefficient chart support produces localized support control once the
selected closed box is known to lie in the relevant chart target and overlap.
-/
def localizedSupportControl {k : Nat}
    (D : CoefficientChartCompactSupportData I x0 x1 ρ)
    (ω : ManifoldForm I M k)
    (htarget : Set.Icc D.box.a D.box.b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc D.box.a D.box.b ⊆ ManifoldForm.chartOverlap I x0 x1) :
    LocalizedSupportControl I x0 x1 ρ ω D.box.a D.box.b :=
  D.toLocalizedSupportControl D.box D.box_K_eq ω htarget hoverlap

end CoefficientChartCompactSupportData

end PiRealCoefficientChartCompactSupport

end Stokes

end
