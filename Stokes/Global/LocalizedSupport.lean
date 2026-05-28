import Stokes.Global.Localization

/-!
# Support bridges for localized manifold forms

This file adds the support bookkeeping for
`ManifoldForm.localizedForm I ρ ω = fun x => ρ x • ω x`.

The algebraic support lemmas are proved directly.  For the topological support
used by local Stokes boxes, the key point is that the transition-pullback of a
localized form is the scalar multiple of the transition-pullback of the base
form by the coefficient written in the comparison chart.
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

variable (I : ModelWithCorners Real E H)

/-- Algebraic support of a manifold form, phrased for the dependent tangent fibers. -/
def support (ω : ManifoldForm I M k) : Set M :=
  {x | ω x ≠ 0}

@[simp]
theorem mem_support {ω : ManifoldForm I M k} {x : M} :
    x ∈ support I ω ↔ ω x ≠ 0 :=
  Iff.rfl

/-- A localized form can only be nonzero where its coefficient is nonzero. -/
theorem localizedForm_support_subset_coefficient_support
    (ρ : M → Real) (ω : ManifoldForm I M k) :
    support I (localizedForm I ρ ω) ⊆ Function.support ρ := by
  intro x hx
  rw [Function.mem_support]
  intro hρ
  exact hx (by simp [localizedForm, hρ])

/-- A localized form can only be nonzero where the original form is nonzero. -/
theorem localizedForm_support_subset_form_support
    (ρ : M → Real) (ω : ManifoldForm I M k) :
    support I (localizedForm I ρ ω) ⊆ support I ω := by
  intro x hx
  rw [mem_support]
  intro hω
  exact hx (by simp [localizedForm, hω])

/-- Combined algebraic support control for the pointwise localized form. -/
theorem localizedForm_support_subset_inter
    (ρ : M → Real) (ω : ManifoldForm I M k) :
    support I (localizedForm I ρ ω) ⊆
      Function.support ρ ∩ support I ω := fun _ hx =>
  ⟨localizedForm_support_subset_coefficient_support (I := I) ρ ω hx,
    localizedForm_support_subset_form_support (I := I) ρ ω hx⟩

/-- The scalar coefficient of a localized form written in a single chart. -/
def coefficientInChart (x0 : M) (ρ : M → Real) : E → Real :=
  fun y => ρ ((extChartAt I x0).symm y)

/--
The scalar coefficient seen by the transition-pullback representative from
the `x0` chart to the comparison chart `x1`.
-/
def transitionCoefficientInChart (x0 x1 : M) (ρ : M → Real) : E → Real :=
  fun y => ρ ((extChartAt I x1).symm (chartTransition I x0 x1 y))

@[simp]
theorem coefficientInChart_apply (x0 : M) (ρ : M → Real) (y : E) :
    coefficientInChart I x0 ρ y = ρ ((extChartAt I x0).symm y) :=
  rfl

@[simp]
theorem transitionCoefficientInChart_apply (x0 x1 : M) (ρ : M → Real) (y : E) :
    transitionCoefficientInChart I x0 x1 ρ y =
      ρ ((extChartAt I x1).symm (chartTransition I x0 x1 y)) :=
  rfl

/--
On the chart overlap, the transition coefficient is the coefficient in the
source chart.
-/
theorem transitionCoefficientInChart_eq_coefficientInChart_of_mem_overlap
    {x0 x1 : M} {ρ : M → Real} {y : E}
    (hy : y ∈ chartOverlap I x0 x1) :
    transitionCoefficientInChart I x0 x1 ρ y =
      coefficientInChart I x0 ρ y := by
  exact congrArg ρ ((extChartAt I x1).left_inv hy)

/--
Pointwise bridge: the transition-pullback of a localized form is the base
transition-pullback multiplied by the coefficient written in the transition
chart.
-/
theorem transitionPullbackInChart_localizedForm_apply
    (x0 x1 : M) (ρ : M → Real) (ω : ManifoldForm I M k) (y : E) :
    transitionPullbackInChart I x0 x1 (localizedForm I ρ ω) y =
      transitionCoefficientInChart I x0 x1 ρ y •
        transitionPullbackInChart I x0 x1 ω y := by
  ext v
  simp only [transitionPullbackInChart, inChart, localizedForm,
    transitionCoefficientInChart, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [ContinuousAlternatingMap.smul_apply]
  rfl

/-- Function-level version of `transitionPullbackInChart_localizedForm_apply`. -/
theorem transitionPullbackInChart_localizedForm
    (x0 x1 : M) (ρ : M → Real) (ω : ManifoldForm I M k) :
    transitionPullbackInChart I x0 x1 (localizedForm I ρ ω) =
      fun y =>
        transitionCoefficientInChart I x0 x1 ρ y •
          transitionPullbackInChart I x0 x1 ω y := by
  funext y
  exact transitionPullbackInChart_localizedForm_apply (I := I) x0 x1 ρ ω y

/--
Algebraic support of a localized transition-pullback is contained in the
support of its chart coefficient.
-/
theorem transitionPullbackInChart_localizedForm_support_subset_coefficient
    (x0 x1 : M) (ρ : M → Real) (ω : ManifoldForm I M k) :
    Function.support
        (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      Function.support (transitionCoefficientInChart I x0 x1 ρ) := by
  rw [transitionPullbackInChart_localizedForm]
  exact Function.support_smul_subset_left
    (transitionCoefficientInChart I x0 x1 ρ)
    (transitionPullbackInChart I x0 x1 ω)

/--
Algebraic support of a localized transition-pullback is contained in the
support of the base transition-pullback.
-/
theorem transitionPullbackInChart_localizedForm_support_subset_form
    (x0 x1 : M) (ρ : M → Real) (ω : ManifoldForm I M k) :
    Function.support
        (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      Function.support (transitionPullbackInChart I x0 x1 ω) := by
  rw [transitionPullbackInChart_localizedForm]
  exact Function.support_smul_subset_right
    (transitionCoefficientInChart I x0 x1 ρ)
    (transitionPullbackInChart I x0 x1 ω)

/-- Combined algebraic support control for localized transition-pullbacks. -/
theorem transitionPullbackInChart_localizedForm_support_subset_inter
    (x0 x1 : M) (ρ : M → Real) (ω : ManifoldForm I M k) :
    Function.support
        (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      Function.support (transitionCoefficientInChart I x0 x1 ρ) ∩
        Function.support (transitionPullbackInChart I x0 x1 ω) := fun _ hy =>
  ⟨transitionPullbackInChart_localizedForm_support_subset_coefficient
      (I := I) x0 x1 ρ ω hy,
    transitionPullbackInChart_localizedForm_support_subset_form
      (I := I) x0 x1 ρ ω hy⟩

/--
Topological support of a localized transition-pullback is contained in the
topological support of its chart coefficient.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_coefficient
    (x0 x1 : M) (ρ : M → Real) (ω : ManifoldForm I M k) :
    tsupport (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      tsupport (transitionCoefficientInChart I x0 x1 ρ) := by
  rw [transitionPullbackInChart_localizedForm]
  exact tsupport_smul_subset_left
    (transitionCoefficientInChart I x0 x1 ρ)
    (transitionPullbackInChart I x0 x1 ω)

/--
Topological support of a localized transition-pullback is contained in the
topological support of the base transition-pullback.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_form
    (x0 x1 : M) (ρ : M → Real) (ω : ManifoldForm I M k) :
    tsupport (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      tsupport (transitionPullbackInChart I x0 x1 ω) := by
  rw [transitionPullbackInChart_localizedForm]
  exact tsupport_smul_subset_right
    (transitionCoefficientInChart I x0 x1 ρ)
    (transitionPullbackInChart I x0 x1 ω)

section Boxes

variable [Preorder E]

/--
If the chart coefficient is topologically supported in a selected box, then so
is the localized transition-pullback.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_Icc_of_coefficient
    {x0 x1 : M} {ρ : M → Real} {ω : ManifoldForm I M k} {a b : E}
    (hρ : tsupport (transitionCoefficientInChart I x0 x1 ρ) ⊆ Set.Icc a b) :
    tsupport (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      Set.Icc a b :=
  (transitionPullbackInChart_localizedForm_tsupport_subset_coefficient
    (I := I) x0 x1 ρ ω).trans hρ

/--
If the base transition-pullback is topologically supported in a selected box,
then so is any coefficient-localized transition-pullback.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_Icc_of_form
    {x0 x1 : M} {ρ : M → Real} {ω : ManifoldForm I M k} {a b : E}
    (hω :
      tsupport (transitionPullbackInChart I x0 x1 ω) ⊆ Set.Icc a b) :
    tsupport (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      Set.Icc a b :=
  (transitionPullbackInChart_localizedForm_tsupport_subset_form
    (I := I) x0 x1 ρ ω).trans hω

end Boxes

end ManifoldForm

section LocalizedSupportControl

variable [Preorder E]

/--
Support-control data tailored to a localized partition-of-unity term.

The genuine support bridge is proved in `ManifoldForm`: it is enough to control
the chart coefficient `transitionCoefficientInChart I x0 x1 ρ`.  The remaining
fields are the selected-box geometric hypotheses already required by
`LocalizedFormData`.
-/
structure LocalizedSupportControl
    (I : ModelWithCorners Real E H) (x0 x1 : M)
    (ρ : M → Real) (ω : ManifoldForm I M k) (a b : E) where
  /-- Lower and upper corners are ordered. -/
  le : a ≤ b
  /-- The selected box lies in the source chart target. -/
  Icc_subset_target : Set.Icc a b ⊆ (extChartAt I x0).target
  /-- The selected box lies in the comparison-chart overlap. -/
  Icc_subset_overlap : Set.Icc a b ⊆ ManifoldForm.chartOverlap I x0 x1
  /-- The localized coefficient, in transition coordinates, is supported in the box. -/
  coefficient_tsupport_subset :
    tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 ρ) ⊆ Set.Icc a b

namespace LocalizedSupportControl

variable {I : ModelWithCorners Real E H} {x0 x1 : M}
variable {ρ : M → Real} {ω : ManifoldForm I M k} {a b : E}

/-- The induced `tsupport` bound for the localized transition-pullback. -/
theorem localized_tsupport_subset
    (C : LocalizedSupportControl I x0 x1 ρ ω a b) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I ρ ω)) ⊆ Set.Icc a b :=
  ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_Icc_of_coefficient
    (I := I) C.coefficient_tsupport_subset

/-- Package coefficient support control as `LocalizedFormData`. -/
def toLocalizedFormData
    (C : LocalizedSupportControl I x0 x1 ρ ω a b) :
    LocalizedFormData I x0 x1 ω a b :=
  LocalizedFormData.mkLocalized ρ C.le C.Icc_subset_target C.Icc_subset_overlap
    C.localized_tsupport_subset

/--
Package coefficient support control directly as an interior selected box for
the canonical localized form.
-/
theorem interiorChartSelectedBox
    (C : LocalizedSupportControl I x0 x1 ρ ω a b) :
    Stokes.interiorChartSelectedBox I x0 x1
      (ManifoldForm.localizedForm I ρ ω) a b :=
  Stokes.interiorChartSelectedBox.mk_of_subsets
    C.le C.Icc_subset_target C.Icc_subset_overlap C.localized_tsupport_subset

/-- The selected box lies in the natural interior chart domain. -/
theorem Icc_subset_domain
    (C : LocalizedSupportControl I x0 x1 ρ ω a b) :
    Set.Icc a b ⊆ Stokes.interiorChartDomain I x0 x1 :=
  C.interiorChartSelectedBox.Icc_subset_domain

end LocalizedSupportControl

end LocalizedSupportControl

end Stokes

end
