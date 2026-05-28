import Stokes.Global.LocalizedSmoothness
import Stokes.Global.LocalizedInteriorPieces

/-!
# From chartwise smoothness to local interior Stokes input

This file packages the common local constructor step: a chartwise-smooth form,
a selected interior chart box, and an open chart-box neighborhood inside the
transition domain produce the `interiorChartExtendedBox` and
`InteriorLocalStokesData` records consumed by the local Stokes layer.

The localized variant reuses `LocalizedSmoothnessData` and
`LocalizedSupportControl` so partition-of-unity pieces can be routed into the
existing localized interior-piece API.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ChartwiseSmoothToLocal

universe u w c

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
One selected interior chart box whose smoothness neighborhood is supplied by a
`ChartwiseSmooth` form.

The target/overlap fields state that the chosen open neighborhood is still
inside the transition domain.  `ChartwiseSmooth` is then enough to derive the
transition-pullback smoothness required by `interiorChartExtendedBox`.
-/
structure ChartwiseSmoothLocalBoxData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) where
  /-- Source chart for the transition-pulled representative. -/
  sourceChart : M
  /-- Comparison chart for the transition-pulled representative. -/
  targetChart : M
  /-- Lower corner of the selected coordinate box. -/
  lowerCorner : Fin (n + 1) → Real
  /-- Upper corner of the selected coordinate box. -/
  upperCorner : Fin (n + 1) → Real
  /-- The selected box before adding its ambient smoothness neighborhood. -/
  selectedBox :
    interiorChartSelectedBox I sourceChart targetChart ω lowerCorner upperCorner
  /-- Ambient open set on which the chart representative is smooth. -/
  smoothSet : Set (Fin (n + 1) → Real)
  /-- The ambient smoothness set is open. -/
  isOpen_smoothSet : IsOpen smoothSet
  /-- The selected closed box lies in the ambient smoothness set. -/
  Icc_subset_smoothSet : Set.Icc lowerCorner upperCorner ⊆ smoothSet
  /-- The base form is smooth in all charts. -/
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I ω
  /-- The smoothness neighborhood lies in the source chart target. -/
  smoothSet_subset_target : smoothSet ⊆ (extChartAt I sourceChart).target
  /-- The smoothness neighborhood lies in the comparison-chart overlap. -/
  smoothSet_subset_overlap :
    smoothSet ⊆ ManifoldForm.chartOverlap I sourceChart targetChart

namespace ChartwiseSmoothLocalBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- Constructor with field order matching the usual local-Stokes hypotheses. -/
def ofSelectedBox
    (x0 x1 : M) (a b : Fin (n + 1) → Real)
    (hselected : interiorChartSelectedBox I x0 x1 ω a b)
    {U : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hchart : ManifoldForm.ChartwiseSmooth I ω)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1) :
    ChartwiseSmoothLocalBoxData I ω where
  sourceChart := x0
  targetChart := x1
  lowerCorner := a
  upperCorner := b
  selectedBox := hselected
  smoothSet := U
  isOpen_smoothSet := hU
  Icc_subset_smoothSet := hUbox
  chartwiseSmooth := hchart
  smoothSet_subset_target := hUtarget
  smoothSet_subset_overlap := hUoverlap

/--
The transition-pullback representative is smooth on the recorded neighborhood.
-/
theorem transitionPullback_contDiffOn [IsManifold I ⊤ M]
    (D : ChartwiseSmoothLocalBoxData I ω) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart ω)
      D.smoothSet :=
  ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_chartAPI
    (I := I) D.chartwiseSmooth D.sourceChart D.targetChart
    D.smoothSet_subset_target D.smoothSet_subset_overlap

/--
The existential smooth-neighborhood witness required by
`interiorChartExtendedBox`.
-/
theorem smoothNeighborhood [IsManifold I ⊤ M]
    (D : ChartwiseSmoothLocalBoxData I ω) :
    ∃ U : Set (Fin (n + 1) → Real),
      IsOpen U ∧ Set.Icc D.lowerCorner D.upperCorner ⊆ U ∧
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart ω) U :=
  ⟨D.smoothSet, D.isOpen_smoothSet, D.Icc_subset_smoothSet,
    D.transitionPullback_contDiffOn⟩

/-- Package the selected box and derived smoothness as an extended box. -/
def interiorChartExtendedBox [IsManifold I ⊤ M]
    (D : ChartwiseSmoothLocalBoxData I ω) :
    Stokes.interiorChartExtendedBox I D.sourceChart D.targetChart ω
      D.lowerCorner D.upperCorner :=
  Stokes.interiorChartExtendedBox.mk D.selectedBox D.isOpen_smoothSet
    D.Icc_subset_smoothSet D.transitionPullback_contDiffOn

/-- The local Stokes input package induced by the chartwise-smooth box data. -/
def localStokesData [IsManifold I ⊤ M]
    (D : ChartwiseSmoothLocalBoxData I ω) :
    InteriorLocalStokesData I ω :=
  InteriorLocalStokesData.ofExtendedBox D.sourceChart D.targetChart
    D.lowerCorner D.upperCorner D.interiorChartExtendedBox

/-- Project-local Stokes for the recorded chartwise-smooth box. -/
theorem projectLocalEquality [IsManifold I ⊤ M]
    (D : ChartwiseSmoothLocalBoxData I ω) :
    projectInteriorBulkIntegral I D.sourceChart D.targetChart ω
        D.lowerCorner D.upperCorner =
      projectInteriorBoundaryIntegral I D.sourceChart D.targetChart ω
        D.lowerCorner D.upperCorner :=
  D.localStokesData.projectLocalEquality

/-- Direct extended-box constructor from a selected box and chartwise smoothness. -/
def interiorChartExtendedBox_of_chartwiseSmooth [IsManifold I ⊤ M]
    (x0 x1 : M) (a b : Fin (n + 1) → Real)
    (hselected : interiorChartSelectedBox I x0 x1 ω a b)
    {U : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hchart : ManifoldForm.ChartwiseSmooth I ω)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1) :
    Stokes.interiorChartExtendedBox I x0 x1 ω a b :=
  (ofSelectedBox x0 x1 a b hselected hU hUbox hchart hUtarget hUoverlap).interiorChartExtendedBox

/-- Direct local-Stokes-data constructor from a selected box and chartwise smoothness. -/
def interiorLocalStokesData_of_chartwiseSmooth [IsManifold I ⊤ M]
    (x0 x1 : M) (a b : Fin (n + 1) → Real)
    (hselected : interiorChartSelectedBox I x0 x1 ω a b)
    {U : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hchart : ManifoldForm.ChartwiseSmooth I ω)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1) :
    InteriorLocalStokesData I ω :=
  (ofSelectedBox x0 x1 a b hselected hU hUbox hchart hUtarget hUoverlap).localStokesData

end ChartwiseSmoothLocalBoxData

/--
Localized version of `ChartwiseSmoothLocalBoxData`.

It combines coefficient support control, coefficient smoothness in transition
coordinates, and chartwise smoothness of the base form.  The derived form is
the canonical localized form `ManifoldForm.localizedForm I rho omega`.
-/
structure LocalizedChartwiseSmoothLocalBoxData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) (ρ : M → Real) where
  /-- Source chart for the transition-pulled representative. -/
  sourceChart : M
  /-- Comparison chart for the transition-pulled representative. -/
  targetChart : M
  /-- Lower corner of the selected coordinate box. -/
  lowerCorner : Fin (n + 1) → Real
  /-- Upper corner of the selected coordinate box. -/
  upperCorner : Fin (n + 1) → Real
  /-- Coefficient support control for the localized form. -/
  supportControl :
    LocalizedSupportControl I sourceChart targetChart ρ ω lowerCorner upperCorner
  /-- Ambient open set on which the localized chart representative is smooth. -/
  smoothSet : Set (Fin (n + 1) → Real)
  /-- The ambient smoothness set is open. -/
  isOpen_smoothSet : IsOpen smoothSet
  /-- The selected closed box lies in the ambient smoothness set. -/
  Icc_subset_smoothSet : Set.Icc lowerCorner upperCorner ⊆ smoothSet
  /-- The transition-coordinate coefficient is smooth on the neighborhood. -/
  coefficient_contDiffOn :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionCoefficientInChart I sourceChart targetChart ρ)
      smoothSet
  /-- The base form is smooth in all charts. -/
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I ω
  /-- The smoothness neighborhood lies in the source chart target. -/
  smoothSet_subset_target : smoothSet ⊆ (extChartAt I sourceChart).target
  /-- The smoothness neighborhood lies in the comparison-chart overlap. -/
  smoothSet_subset_overlap :
    smoothSet ⊆ ManifoldForm.chartOverlap I sourceChart targetChart

namespace LocalizedChartwiseSmoothLocalBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n} {ρ : M → Real}

/-- Constructor with field order matching the usual localized local-Stokes hypotheses. -/
def ofSupportControl
    (x0 x1 : M) (a b : Fin (n + 1) → Real)
    (C : LocalizedSupportControl I x0 x1 ρ ω a b)
    {U : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hρ :
      ContDiffOn Real ⊤ (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hchart : ManifoldForm.ChartwiseSmooth I ω)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1) :
    LocalizedChartwiseSmoothLocalBoxData I ω ρ where
  sourceChart := x0
  targetChart := x1
  lowerCorner := a
  upperCorner := b
  supportControl := C
  smoothSet := U
  isOpen_smoothSet := hU
  Icc_subset_smoothSet := hUbox
  coefficient_contDiffOn := hρ
  chartwiseSmooth := hchart
  smoothSet_subset_target := hUtarget
  smoothSet_subset_overlap := hUoverlap

/--
Reusable localized smoothness package obtained from the coefficient smoothness
and chartwise smoothness fields.
-/
def localizedSmoothnessData [IsManifold I ⊤ M]
    (D : LocalizedChartwiseSmoothLocalBoxData I ω ρ) :
    LocalizedSmoothnessData I D.sourceChart D.targetChart ρ ω D.smoothSet :=
  LocalizedSmoothnessData.ofChartwiseSmooth D.coefficient_contDiffOn
    D.chartwiseSmooth D.smoothSet_subset_target D.smoothSet_subset_overlap

/--
The localized transition-pullback representative is smooth on the recorded
neighborhood.
-/
theorem transitionPullback_contDiffOn [IsManifold I ⊤ M]
    (D : LocalizedChartwiseSmoothLocalBoxData I ω ρ) :
    ContDiffOn Real ⊤
      (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart
        (ManifoldForm.localizedForm I ρ ω)) D.smoothSet :=
  (D.localizedSmoothnessData).localized_contDiffOn

/--
The existential smooth-neighborhood witness required by
`interiorChartExtendedBox` for the localized form.
-/
theorem smoothNeighborhood [IsManifold I ⊤ M]
    (D : LocalizedChartwiseSmoothLocalBoxData I ω ρ) :
    ∃ U : Set (Fin (n + 1) → Real),
      IsOpen U ∧ Set.Icc D.lowerCorner D.upperCorner ⊆ U ∧
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart
            (ManifoldForm.localizedForm I ρ ω)) U :=
  (D.localizedSmoothnessData).smoothNeighborhood D.isOpen_smoothSet
    D.Icc_subset_smoothSet

/-- Package the localized support and smoothness data as an extended box. -/
def interiorChartExtendedBox [IsManifold I ⊤ M]
    (D : LocalizedChartwiseSmoothLocalBoxData I ω ρ) :
    Stokes.interiorChartExtendedBox I D.sourceChart D.targetChart
      (ManifoldForm.localizedForm I ρ ω) D.lowerCorner D.upperCorner :=
  LocalizedSmoothnessData.interiorChartExtendedBox D.supportControl
    D.localizedSmoothnessData D.isOpen_smoothSet D.Icc_subset_smoothSet

/-- The local Stokes input package for the localized form. -/
def localStokesData [IsManifold I ⊤ M]
    (D : LocalizedChartwiseSmoothLocalBoxData I ω ρ) :
    InteriorLocalStokesData I (ManifoldForm.localizedForm I ρ ω) :=
  InteriorLocalStokesData.ofExtendedBox D.sourceChart D.targetChart
    D.lowerCorner D.upperCorner D.interiorChartExtendedBox

/-- Project-local Stokes for the localized chartwise-smooth box. -/
theorem projectLocalEquality [IsManifold I ⊤ M]
    (D : LocalizedChartwiseSmoothLocalBoxData I ω ρ) :
    projectInteriorBulkIntegral I D.sourceChart D.targetChart
        (ManifoldForm.localizedForm I ρ ω) D.lowerCorner D.upperCorner =
      projectInteriorBoundaryIntegral I D.sourceChart D.targetChart
        (ManifoldForm.localizedForm I ρ ω) D.lowerCorner D.upperCorner :=
  D.localStokesData.projectLocalEquality

/--
Expose localized chartwise-smooth box data as the existing
`LocalizedInteriorPiece` package.
-/
def localizedInteriorPiece [IsManifold I ⊤ M]
    {ρs : ι → M → Real} {i : ι}
    (D : LocalizedChartwiseSmoothLocalBoxData I ω (ρs i)) :
    LocalizedInteriorPiece I ω ρs i where
  sourceChart := D.sourceChart
  targetChart := D.targetChart
  lowerCorner := D.lowerCorner
  upperCorner := D.upperCorner
  supportControl := D.supportControl
  smoothNeighborhood := D.smoothNeighborhood

/-- Direct extended-box constructor for a localized chartwise-smooth box. -/
def interiorChartExtendedBox_of_chartwiseSmooth [IsManifold I ⊤ M]
    (x0 x1 : M) (a b : Fin (n + 1) → Real)
    (C : LocalizedSupportControl I x0 x1 ρ ω a b)
    {U : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hρ :
      ContDiffOn Real ⊤ (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hchart : ManifoldForm.ChartwiseSmooth I ω)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1) :
    Stokes.interiorChartExtendedBox I x0 x1
      (ManifoldForm.localizedForm I ρ ω) a b :=
  (ofSupportControl x0 x1 a b C hU hUbox hρ hchart hUtarget hUoverlap).interiorChartExtendedBox

/-- Direct local-Stokes-data constructor for a localized chartwise-smooth box. -/
def interiorLocalStokesData_of_chartwiseSmooth [IsManifold I ⊤ M]
    (x0 x1 : M) (a b : Fin (n + 1) → Real)
    (C : LocalizedSupportControl I x0 x1 ρ ω a b)
    {U : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hUbox : Set.Icc a b ⊆ U)
    (hρ :
      ContDiffOn Real ⊤ (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) U)
    (hchart : ManifoldForm.ChartwiseSmooth I ω)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1) :
    InteriorLocalStokesData I (ManifoldForm.localizedForm I ρ ω) :=
  (ofSupportControl x0 x1 a b C hU hUbox hρ hchart hUtarget hUoverlap).localStokesData

end LocalizedChartwiseSmoothLocalBoxData

end ChartwiseSmoothToLocal

end Stokes

end
