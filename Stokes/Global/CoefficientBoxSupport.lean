import Stokes.Global.LocalizedSupport
import Stokes.Global.BoxSelection

/-!
# Coefficient support in selected chart boxes

This file packages the support step for a partition-of-unity coefficient after
it is written in transition-chart coordinates.  The main data object records a
compact coordinate support set, its selected closed box, and the resulting
`tsupport` bound required by `LocalizedSupportControl`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false

universe u v w

section CoefficientBoxSupport

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [Preorder E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Coefficient support in transition-chart coordinates, together with a compact
coordinate set and a selected closed box containing it.

The field `coefficient_tsupport_subset` is the support fact consumed by
`LocalizedSupportControl`.  The preceding fields record the compact-support
route used to obtain it.
-/
structure CoefficientBoxSupportData
    (I : ModelWithCorners Real E H) (x0 x1 : M) (ρ : M → Real)
    (a b : E) where
  /-- Compact coordinate set used to control the coefficient support. -/
  K : Set E
  /-- Compactness of the coordinate support set. -/
  isCompact_K : IsCompact K
  /-- Lower and upper corners of the selected box are ordered. -/
  le : a ≤ b
  /-- The chart coefficient's topological support lies in the compact set. -/
  coefficient_tsupport_subset_K :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ K
  /-- The compact coordinate set lies in the selected closed box. -/
  K_subset_Icc : K ⊆ Set.Icc a b
  /-- The chart coefficient's topological support lies in the selected box. -/
  coefficient_tsupport_subset :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ Set.Icc a b

namespace CoefficientBoxSupportData

variable {I : ModelWithCorners Real E H} {x0 x1 : M} {ρ : M → Real} {a b : E}

/-- Constructor from an explicit compact coordinate support set inside a box. -/
def ofCompactSupport (K : Set E) (hK : IsCompact K) (hle : a ≤ b)
    (hsupp : tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ K)
    (hKbox : K ⊆ Set.Icc a b) :
    CoefficientBoxSupportData I x0 x1 ρ a b where
  K := K
  isCompact_K := hK
  le := hle
  coefficient_tsupport_subset_K := hsupp
  K_subset_Icc := hKbox
  coefficient_tsupport_subset := hsupp.trans hKbox

/-- Constructor when the compact coordinate support set is the coefficient `tsupport`. -/
def ofTSupportSubsetIcc
    (hcompact :
      IsCompact (tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ)))
    (hle : a ≤ b)
    (hsubset :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ Set.Icc a b) :
    CoefficientBoxSupportData I x0 x1 ρ a b :=
  ofCompactSupport
    (tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ))
    hcompact hle (fun _ hx => hx) hsubset

/-- The compact coordinate support set is contained in the selected box. -/
theorem support_subset_Icc (D : CoefficientBoxSupportData I x0 x1 ρ a b) :
    D.K ⊆ Set.Icc a b :=
  D.K_subset_Icc

/-- The coefficient support bound packaged by the data. -/
theorem tsupport_subset_Icc (D : CoefficientBoxSupportData I x0 x1 ρ a b) :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ Set.Icc a b :=
  D.coefficient_tsupport_subset

/-- A compact coordinate box selection gives coefficient box-support data. -/
def ofCompactCoordinateBoxSelection
    (B : CompactCoordinateBoxSelection E)
    (hsupp :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ B.K) :
    CoefficientBoxSupportData I x0 x1 ρ B.a B.b :=
  ofCompactSupport B.K B.isCompact_K B.le hsupp B.subset_Icc

/--
Turn coefficient box-support data into the support-control package for a
localized form.  The remaining hypotheses are the geometric chart-domain
inclusions required by `LocalizedSupportControl`.
-/
def toLocalizedSupportControl {k : Nat}
    (D : CoefficientBoxSupportData I x0 x1 ρ a b)
    (ω : ManifoldForm I M k)
    (htarget : Set.Icc a b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1) :
    LocalizedSupportControl I x0 x1 ρ ω a b where
  le := D.le
  Icc_subset_target := htarget
  Icc_subset_overlap := hoverlap
  coefficient_tsupport_subset := D.coefficient_tsupport_subset

end CoefficientBoxSupportData

namespace CompactCoordinateBoxSelection

variable {I : ModelWithCorners Real E H} {x0 x1 : M} {ρ : M → Real}

/-- Wrapper from a selected compact coordinate box to coefficient support data. -/
def coefficientBoxSupportData
    (B : CompactCoordinateBoxSelection E)
    (hsupp :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ B.K) :
    CoefficientBoxSupportData I x0 x1 ρ B.a B.b :=
  CoefficientBoxSupportData.ofCompactCoordinateBoxSelection B hsupp

/-- Wrapper from a selected compact coordinate box to `LocalizedSupportControl`. -/
def localizedSupportControl {k : Nat}
    (B : CompactCoordinateBoxSelection E)
    (hsupp :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ B.K)
    (ω : ManifoldForm I M k)
    (htarget : Set.Icc B.a B.b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc B.a B.b ⊆ ManifoldForm.chartOverlap I x0 x1) :
    LocalizedSupportControl I x0 x1 ρ ω B.a B.b :=
  (B.coefficientBoxSupportData hsupp).toLocalizedSupportControl ω htarget hoverlap

end CompactCoordinateBoxSelection

end CoefficientBoxSupport

section PiRealCoefficientBoxSupport

variable {ι : Type u} [Fintype ι]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real (ι → Real) H}
variable {x0 x1 : M} {ρ : M → Real} {a b : ι → Real}

/--
If the coefficient chart support, viewed by the identity coordinate map, is
contained in a selected coordinate-image box, then it is contained in the box.
-/
theorem coefficient_tsupport_subset_Icc_of_compactCoordinateImageBoxSelection
    (hbox :
      compactCoordinateImageBoxSelection (fun y : ι → Real => y)
        (tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ)) a b) :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ Set.Icc a b := by
  intro y hy
  exact hbox ⟨y, hy, rfl⟩

namespace CoefficientBoxSupportData

/--
Constructor from a compact coordinate support set whose identity coordinate
image is contained in the selected box.
-/
def ofCompactCoordinateImageBoxSelection
    (K : Set (ι → Real)) (hK : IsCompact K) (hle : a ≤ b)
    (hsupp :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ K)
    (hbox : compactCoordinateImageBoxSelection (fun y : ι → Real => y) K a b) :
    CoefficientBoxSupportData I x0 x1 ρ a b :=
  ofCompactSupport K hK hle hsupp (by
    intro y hy
    exact hbox ⟨y, hy, rfl⟩)

/--
Constructor for the common case where the compact coordinate support set is the
coefficient `tsupport` itself.
-/
def ofTSupportCompactCoordinateImageBoxSelection
    (hcompact :
      IsCompact (tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ)))
    (hle : a ≤ b)
    (hbox :
      compactCoordinateImageBoxSelection (fun y : ι → Real => y)
        (tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ)) a b) :
    CoefficientBoxSupportData I x0 x1 ρ a b :=
  ofCompactSupport
    (tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ))
    hcompact hle (fun _ hx => hx)
    (coefficient_tsupport_subset_Icc_of_compactCoordinateImageBoxSelection hbox)

end CoefficientBoxSupportData

namespace LocalizedSupportControl

variable {k : Nat} {ω : ManifoldForm I M k}

/--
The coefficient support bound needed by `LocalizedSupportControl`, obtained
from an identity coordinate-image box for the coefficient chart support.
-/
theorem coefficient_tsupport_subset_of_compactCoordinateImageBoxSelection
    (hbox :
      compactCoordinateImageBoxSelection (fun y : ι → Real => y)
        (tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ)) a b) :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ Set.Icc a b :=
  coefficient_tsupport_subset_Icc_of_compactCoordinateImageBoxSelection hbox

/--
Build localized support control from a compact coefficient chart support whose
identity coordinate image is contained in the selected box.
-/
def ofTSupportCompactCoordinateImageBoxSelection
    (hcompact :
      IsCompact (tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ)))
    (hle : a ≤ b)
    (htarget : Set.Icc a b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1)
    (hbox :
      compactCoordinateImageBoxSelection (fun y : ι → Real => y)
        (tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ)) a b) :
    LocalizedSupportControl I x0 x1 ρ ω a b :=
  (CoefficientBoxSupportData.ofTSupportCompactCoordinateImageBoxSelection
    hcompact hle hbox).toLocalizedSupportControl ω htarget hoverlap

end LocalizedSupportControl

end PiRealCoefficientBoxSupport

end Stokes

end
