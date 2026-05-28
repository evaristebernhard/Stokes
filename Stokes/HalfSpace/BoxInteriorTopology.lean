import Stokes.HalfSpace.Faces
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Open-box topology and measure helpers for half-space local Stokes

This file records small wrappers around mathlib's finite-product box API.  The
local half-space proof usually works on closed boxes for integration, while
smoothness and derivative hypotheses are naturally obtained on open
neighborhoods of their interiors.
-/

noncomputable section

set_option linter.unusedFintypeInType false

open Set MeasureTheory Filter
open scoped Topology Manifold

namespace Stokes

section PiRealBoxes

variable {ι : Type*}
variable (a b : ι → Real)

/-- The coordinate open box and closed box differ only by a null boundary. -/
theorem pi_Ioo_ae_eq_Icc_volume [Fintype ι] :
    (Set.pi Set.univ fun i => Set.Ioo (a i) (b i)) =ᵐ[volume] Set.Icc a b := by
  simpa using (Measure.univ_pi_Ioo_ae_eq_Icc (f := a) (g := b))

/-- Symmetric form of `pi_Ioo_ae_eq_Icc_volume`. -/
theorem Icc_ae_eq_pi_Ioo_volume [Fintype ι] :
    Set.Icc a b =ᵐ[volume] (Set.pi Set.univ fun i => Set.Ioo (a i) (b i)) :=
  (pi_Ioo_ae_eq_Icc_volume a b).symm

/-- Set integrals over a coordinate open box may be replaced by the closed box. -/
theorem integral_pi_Ioo_eq_integral_Icc [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] (f : (ι → Real) → E) :
    (∫ x in Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)), f x) =
      ∫ x in Set.Icc a b, f x :=
  MeasureTheory.setIntegral_congr_set (pi_Ioo_ae_eq_Icc_volume a b)

/-- Set integrals over a coordinate closed box may be replaced by the open box. -/
theorem integral_Icc_eq_integral_pi_Ioo [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] (f : (ι → Real) → E) :
    (∫ x in Set.Icc a b, f x) =
      ∫ x in Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)), f x :=
  MeasureTheory.setIntegral_congr_set (Icc_ae_eq_pi_Ioo_volume a b)

/-- A point in the coordinate open box is also in the corresponding closed box. -/
theorem mem_Icc_of_mem_pi_Ioo {x : ι → Real}
    (hx : x ∈ Set.pi Set.univ fun i => Set.Ioo (a i) (b i)) :
    x ∈ Set.Icc a b := by
  constructor
  · intro i
    exact (hx i (Set.mem_univ i)).1.le
  · intro i
    exact (hx i (Set.mem_univ i)).2.le

/-- The coordinate open box is contained in the corresponding closed box. -/
theorem pi_Ioo_subset_Icc :
    (Set.pi Set.univ fun i => Set.Ioo (a i) (b i)) ⊆ Set.Icc a b := by
  intro x hx
  exact mem_Icc_of_mem_pi_Ioo a b hx

/-- Coordinate open boxes are open in finite real products. -/
theorem isOpen_pi_Ioo [Fintype ι] :
    IsOpen (Set.pi Set.univ fun i => Set.Ioo (a i) (b i)) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

/-- Membership in a coordinate open box gives the open box as a neighborhood. -/
theorem pi_Ioo_mem_nhds_of_mem [Fintype ι] {x : ι → Real}
    (hx : x ∈ Set.pi Set.univ fun i => Set.Ioo (a i) (b i)) :
    (Set.pi Set.univ fun i => Set.Ioo (a i) (b i)) ∈ 𝓝 x :=
  (isOpen_pi_Ioo a b).mem_nhds hx

end PiRealBoxes

section DerivativeWrappers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {m : WithTop ℕ∞} {f : E → F} {U : Set E} {x : E}

/--
On an open set, a `C^m` function with `1 ≤ m` has the canonical Frechet
derivative at every point of the set.
-/
theorem hasFDerivAt_of_contDiffOn_isOpen_mem
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn Real m f U)
    (hm : (1 : WithTop ℕ∞) ≤ m) :
    HasFDerivAt f (fderiv Real f x) x :=
  ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le (by norm_num) hm))).hasFDerivAt

/-- Analytic-level specialization of `hasFDerivAt_of_contDiffOn_isOpen_mem`. -/
theorem hasFDerivAt_of_contDiffOn_top_isOpen_mem
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn Real ⊤ f U) :
    HasFDerivAt f (fderiv Real f x) x :=
  hasFDerivAt_of_contDiffOn_isOpen_mem (m := (⊤ : WithTop ℕ∞)) hU hx hf (by simp)

variable {n : Nat}

/--
Coordinate coefficients of a mathlib `n`-form inherit the pointwise Frechet
derivative supplied by `ContDiffOn` on an open set.
-/
theorem toCoordNForm_hasFDerivAt_of_contDiffOn_isOpen_mem
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    {x : Fin (n + 1) → Real} (hx : x ∈ U)
    (hω : ContDiffOn Real m ω U) (hm : (1 : WithTop ℕ∞) ≤ m)
    (i : Fin (n + 1)) :
    HasFDerivAt (CubeStokes.toCoordNForm ω i)
      (fderiv Real (CubeStokes.toCoordNForm ω i) x) x :=
  hasFDerivAt_of_contDiffOn_isOpen_mem hU hx
    (toCoordNForm_contDiffOn_of_level ω hω i) hm

/-- Smooth-level specialization for coordinate coefficients of a mathlib form. -/
theorem toCoordNForm_hasFDerivAt_of_contDiffOn_top_isOpen_mem
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    {U : Set (Fin (n + 1) → Real)} (hU : IsOpen U)
    {x : Fin (n + 1) → Real} (hx : x ∈ U)
    (hω : ContDiffOn Real ⊤ ω U) (i : Fin (n + 1)) :
    HasFDerivAt (CubeStokes.toCoordNForm ω i)
      (fderiv Real (CubeStokes.toCoordNForm ω i) x) x :=
  toCoordNForm_hasFDerivAt_of_contDiffOn_isOpen_mem (m := (⊤ : WithTop ℕ∞))
    ω hU hx hω (by simp) i

end DerivativeWrappers

end Stokes
