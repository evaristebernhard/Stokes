import Stokes.Global.InteriorChart

/-!
# Localized manifold forms

This file records the project-local interface for partition-of-unity localized
forms.  The scalar multiplication is the honest pointwise multiplication of a
manifold form by a scalar function, while support control is kept as explicit
data: the analytic proof that a chosen partition term has chart support inside
a selected box belongs to the later partition/localization layer.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {k : Nat}

namespace ManifoldForm

/--
Pointwise localization of a manifold form by a scalar coefficient.

For a partition of unity term `ρ i`, later code should use
`localizedForm I (ρ i) ω`; support and smoothness facts are supplied separately
by the chart-box data below.
-/
def localizedForm (I : ModelWithCorners Real E H) (ρ : M → Real)
    (ω : ManifoldForm I M k) : ManifoldForm I M k :=
  fun x => ρ x • ω x

@[simp]
theorem localizedForm_apply (I : ModelWithCorners Real E H) (ρ : M → Real)
    (ω : ManifoldForm I M k) (x : M) :
    localizedForm I ρ ω x = ρ x • ω x :=
  rfl

end ManifoldForm

section LocalizedBoxData

variable [Preorder E]

/--
Data for one coefficient-localized form whose transition-pullback
representative is supported in a chosen interior chart box.

The field `localized_eq` ties the stored form to the project-local pointwise
definition.  The field `localized_tsupport_subset` is the explicit analytic
support input that future partition-of-unity code must prove for active terms.
-/
structure LocalizedFormData
    (I : ModelWithCorners Real E H) (x0 x1 : M)
    (ω : ManifoldForm I M k) (a b : E) where
  /-- Scalar coefficient, intended to be a partition-of-unity term. -/
  coefficient : M → Real
  /-- The localized manifold form. -/
  localized : ManifoldForm I M k
  /-- The localized form is the pointwise scalar multiple of the base form. -/
  localized_eq : localized = ManifoldForm.localizedForm I coefficient ω
  /-- Lower and upper corners are ordered. -/
  le : a ≤ b
  /-- The selected box lies in the source chart target. -/
  Icc_subset_target : Set.Icc a b ⊆ (extChartAt I x0).target
  /-- The selected box lies in the comparison-chart overlap. -/
  Icc_subset_overlap : Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1
  /-- The chart representative of the localized form is supported in the box. -/
  localized_tsupport_subset :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 localized) ⊆ Set.Icc a b

namespace LocalizedFormData

variable {I : ModelWithCorners Real E H} {x0 x1 : M}
variable {ω : ManifoldForm I M k} {a b : E}

/--
Constructor specialized to the canonical pointwise localized form.  The only
nontrivial support statement is left as an explicit hypothesis.
-/
def mkLocalized (ρ : M → Real)
    (hle : a ≤ b)
    (htarget : Set.Icc a b ⊆ (extChartAt I x0).target)
    (hoverlap : Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1)
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I x0 x1
            (ManifoldForm.localizedForm I ρ ω)) ⊆
        Set.Icc a b) :
    LocalizedFormData I x0 x1 ω a b where
  coefficient := ρ
  localized := ManifoldForm.localizedForm I ρ ω
  localized_eq := rfl
  le := hle
  Icc_subset_target := htarget
  Icc_subset_overlap := hoverlap
  localized_tsupport_subset := hsupp

/-- The stored localized form unfolds to the project-local pointwise definition. -/
theorem localized_eq_localizedForm (D : LocalizedFormData I x0 x1 ω a b) :
    D.localized = ManifoldForm.localizedForm I D.coefficient ω :=
  D.localized_eq

/-- Support bridge for the localized transition-pullback representative. -/
theorem transitionPullbackInChart_tsupport_subset_Icc
    (D : LocalizedFormData I x0 x1 ω a b) :
    tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 D.localized) ⊆
      Set.Icc a b :=
  D.localized_tsupport_subset

/--
Package the localized support data as an `interiorChartSelectedBox`, so later
local Stokes wrappers can consume the localized form through the existing box
interface.
-/
theorem interiorChartSelectedBox
    (D : LocalizedFormData I x0 x1 ω a b) :
    Stokes.interiorChartSelectedBox I x0 x1 D.localized a b :=
  Stokes.interiorChartSelectedBox.mk_of_subsets
    D.le D.Icc_subset_target D.Icc_subset_overlap D.localized_tsupport_subset

/-- Domain containment inherited from the selected-box package. -/
theorem Icc_subset_domain (D : LocalizedFormData I x0 x1 ω a b) :
    Set.Icc a b ⊆ Stokes.interiorChartDomain I x0 x1 :=
  D.interiorChartSelectedBox.Icc_subset_domain

end LocalizedFormData

end LocalizedBoxData

end Stokes

end
