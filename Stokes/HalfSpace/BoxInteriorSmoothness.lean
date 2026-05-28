import Stokes.HalfSpace.BoxInteriorTopology
import Stokes.HalfSpace.BoxInteriorStokes
import Mathlib.Analysis.Calculus.TangentCone.Pi

/-!
# Half-space open-interior smoothness constructors

This module turns smoothness on an open neighborhood of the coordinate open box
into the lower-level interior-box fields used by `BoxInteriorStokes`.

The ambient smoothness set is only required to contain
`pi univ (fun i => Ioo (a i) (b i))`; it need not contain the closed box.
Continuity on the closed box and integrability of the coordinate divergence are
kept as explicit fields.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

/-- The coordinate open box associated to a half-space local box. -/
abbrev halfSpaceBoxOpenInterior {n : Nat} (a b : Fin (n + 1) → Real) :
    Set (Fin (n + 1) → Real) :=
  pi univ fun i : Fin (n + 1) => Ioo (a i) (b i)

/--
Smoothness data on an open neighborhood of only the coordinate open box.

The closed-box continuity and divergence integrability assumptions are retained
as fields because open-interior smoothness does not control boundary points of
the auxiliary closed box.
-/
structure HalfSpaceBoxOpenInteriorSmoothnessFields {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) where
  /-- The lower corner is componentwise below the upper corner. -/
  le : a ≤ b
  /-- The lower normal coordinate is the half-space boundary face. -/
  lower_zero : a 0 = 0
  /-- An open smoothness neighborhood of the coordinate open box. -/
  U : Set (Fin (n + 1) → Real)
  /-- The smoothness neighborhood is open. -/
  isOpen_U : IsOpen U
  /-- Only the coordinate open box is required to lie in `U`. -/
  openInterior_subset_U : halfSpaceBoxOpenInterior a b ⊆ U
  /-- The form is smooth on the open-interior neighborhood. -/
  contDiffOn_openInterior : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω U
  /-- Signed coordinate coefficients are continuous on the closed box. -/
  continuous_signedCoeff :
    ∀ i : Fin (n + 1),
      ContinuousOn (CubeStokes.signedCoeff (CubeStokes.toCoordNForm ω) i) (Icc a b)
  /-- The coordinate divergence integrand is integrable on the closed box. -/
  integrable_divergence :
    IntegrableOn
      (fun x => ∑ i : Fin (n + 1),
        ((-1 : Real) ^ (i : Nat) •
          fderiv Real (CubeStokes.toCoordNForm ω i) x) (Pi.single i 1))
      (Icc a b)

variable {n : Nat}

/--
The closed-box bulk integral equals the coordinate box integral when the form is
differentiable on the coordinate open box.  The proof avoids any closed-box
smoothness hypothesis by replacing `Icc a b` with the a.e.-equal open box.
-/
theorem halfSpaceLocalBulkIntegral_eq_boxIntegral_of_differentiableAt_on_openBox
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hdiff :
      ∀ x ∈ halfSpaceBoxOpenInterior a b, DifferentiableAt Real ω x) :
    halfSpaceLocalBulkIntegral ω a b =
      CubeStokes.boxIntegral (CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω)) a b := by
  unfold halfSpaceLocalBulkIntegral CubeStokes.boxIntegral
  calc
    (∫ x in Icc a b, extDeriv ω x (standardTopFrame n)) =
        ∫ x in halfSpaceBoxOpenInterior a b, extDeriv ω x (standardTopFrame n) := by
      exact integral_Icc_eq_integral_pi_Ioo a b
        (fun x => extDeriv ω x (standardTopFrame n))
    _ = ∫ x in halfSpaceBoxOpenInterior a b,
          CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω) x := by
      exact MeasureTheory.setIntegral_congr_fun (isOpen_pi_Ioo a b).measurableSet
        fun x hx => by
          simpa [halfSpaceBoxOpenInterior, standardTopFrame] using
            CubeStokes.extDeriv_topCoeff_eq_extDerivCoord ω x (hdiff x hx)
    _ = ∫ x in Icc a b,
          CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω) x := by
      exact (integral_Icc_eq_integral_pi_Ioo a b
        (fun x => CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω) x)).symm

/--
Relative closed-box smoothness is enough to make the signed coordinate
coefficients continuous on the closed box.

This is the part of the regularity package that genuinely follows from a
`ContDiffOn` statement on `Icc a b` alone.
-/
theorem continuous_signedCoeff_of_contDiffOn_Icc
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hω : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω (Icc a b)) :
    ∀ i : Fin (n + 1),
      ContinuousOn (CubeStokes.signedCoeff (CubeStokes.toCoordNForm ω) i) (Icc a b) := by
  intro i
  have hcoeff :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (CubeStokes.toCoordNForm ω i) (Icc a b) :=
    toCoordNForm_contDiffOn_of_level ω hω i
  exact continuousOn_const.mul hcoeff.continuousOn

/--
If a coordinate closed box is nondegenerate in every coordinate, then it has
the unique differentiability property.
-/
theorem uniqueDiffOn_Icc_pi_of_forall_lt
    (a b : Fin (n + 1) → Real) (hlt : ∀ i : Fin (n + 1), a i < b i) :
    UniqueDiffOn Real (Icc a b) := by
  have hpi :
      UniqueDiffOn Real (Set.pi Set.univ fun i : Fin (n + 1) => Icc (a i) (b i)) :=
    UniqueDiffOn.univ_pi fun i => uniqueDiffOn_Icc (hlt i)
  have hset :
      (Set.pi Set.univ fun i : Fin (n + 1) => Icc (a i) (b i)) = Icc a b := by
    ext x
    constructor
    · intro hx
      exact ⟨fun i => (hx i (mem_univ i)).1, fun i => (hx i (mem_univ i)).2⟩
    · intro hx i _hi
      exact ⟨hx.1 i, hx.2 i⟩
  simpa [hset] using hpi

/--
If a coordinate closed box is degenerate in at least one coordinate, then it
has zero Lebesgue measure.
-/
theorem volume_Icc_eq_zero_of_not_forall_lt
    (a b : Fin (n + 1) → Real) (h : ¬ ∀ i : Fin (n + 1), a i < b i) :
    volume (Icc a b) = 0 := by
  push Not at h
  obtain ⟨i, hi⟩ := h
  rw [Real.volume_Icc_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [ENNReal.ofReal_eq_zero]
  exact sub_nonpos.mpr hi

/--
Relative `C^\infty` smoothness on a closed coordinate box makes the coordinate
divergence integrand integrable on that box.

The nondegenerate case uses continuity of `fderivWithin` on `Icc` and the fact
that `fderivWithin` agrees with the ambient `fderiv` on the coordinate open
box, which is a.e.-equal to `Icc`.  Degenerate boxes have zero volume.
-/
theorem integrable_divergence_of_contDiffOn_Icc
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hω : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω (Icc a b)) :
    IntegrableOn
      (fun x => ∑ i : Fin (n + 1),
        ((-1 : Real) ^ (i : Nat) •
          fderiv Real (CubeStokes.toCoordNForm ω i) x) (Pi.single i 1))
      (Icc a b) := by
  classical
  by_cases hlt : ∀ i : Fin (n + 1), a i < b i
  · let divWithin : (Fin (n + 1) → Real) → Real := fun x =>
      ∑ i : Fin (n + 1),
        ((-1 : Real) ^ (i : Nat) •
          fderivWithin Real (CubeStokes.toCoordNForm ω i) (Icc a b) x)
            (Pi.single i 1)
    have hunique : UniqueDiffOn Real (Icc a b) :=
      uniqueDiffOn_Icc_pi_of_forall_lt a b hlt
    have hcontWithin : ContinuousOn divWithin (Icc a b) := by
      apply continuousOn_finset_sum
      intro i _hi
      have hcoeff :
          ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
            (CubeStokes.toCoordNForm ω i) (Icc a b) :=
        toCoordNForm_contDiffOn_of_level ω hω i
      have hfderiv :
          ContinuousOn
            (fderivWithin Real (CubeStokes.toCoordNForm ω i) (Icc a b))
            (Icc a b) :=
        hcoeff.continuousOn_fderivWithin hunique (by simp)
      have happly :
          ContinuousOn
            (fun x =>
              fderivWithin Real (CubeStokes.toCoordNForm ω i) (Icc a b) x
                (Pi.single i 1))
            (Icc a b) :=
        (ContinuousLinearMap.apply Real Real (Pi.single i 1)).continuous.comp_continuousOn
          hfderiv
      exact continuousOn_const.mul happly
    have hIntWithin : IntegrableOn divWithin (Icc a b) :=
      hcontWithin.integrableOn_compact isCompact_Icc
    refine hIntWithin.congr_fun_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [Icc_ae_eq_pi_Ioo_volume a b] with x hxsets hxIcc
    have hxopen : x ∈ halfSpaceBoxOpenInterior a b := by
      exact Eq.mp hxsets hxIcc
    have hnhds : Icc a b ∈ 𝓝 x :=
      mem_of_superset (pi_Ioo_mem_nhds_of_mem a b hxopen) (pi_Ioo_subset_Icc a b)
    simp only [divWithin]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [fderivWithin_of_mem_nhds (𝕜 := Real)
      (f := CubeStokes.toCoordNForm ω i) hnhds]
  · exact IntegrableOn.of_measure_zero
      (volume_Icc_eq_zero_of_not_forall_lt a b hlt)

/--
Bundled closed-box regularity generated by relative smoothness on the closed
coordinate box itself.
-/
theorem closedBoxRegularity_of_contDiffOn_Icc
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hω : ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞) ω (Icc a b)) :
    (∀ i : Fin (n + 1),
      ContinuousOn (CubeStokes.signedCoeff (CubeStokes.toCoordNForm ω) i) (Icc a b)) ∧
    IntegrableOn
      (fun x => ∑ i : Fin (n + 1),
        ((-1 : Real) ^ (i : Nat) •
          fderiv Real (CubeStokes.toCoordNForm ω i) x) (Pi.single i 1))
      (Icc a b) :=
  ⟨continuous_signedCoeff_of_contDiffOn_Icc ω a b hω,
    integrable_divergence_of_contDiffOn_Icc ω a b hω⟩

/--
If a closed box lies in an ambient open smoothness set, then the signed
coordinate coefficients are continuous on the closed box.
-/
theorem continuous_signedCoeff_of_contDiffOn_isOpen_Icc_subset
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    {V : Set (Fin (n + 1) → Real)} (_hV : IsOpen V) (hbox : Icc a b ⊆ V)
    (hω : ContDiffOn Real ⊤ ω V) :
    ∀ i : Fin (n + 1),
      ContinuousOn (CubeStokes.signedCoeff (CubeStokes.toCoordNForm ω) i) (Icc a b) :=
  continuous_signedCoeff_of_contDiffOn_Icc ω a b ((hω.mono hbox).of_le le_top)

/--
If a closed box lies in an ambient open smoothness set, then the coordinate
divergence integrand used by `CubeStokes.stokes_on_box` is integrable on the
closed box.

The open-neighborhood hypothesis is essential for this `fderiv`-based statement:
smoothness only on the coordinate open box does not control blow-up near the
closed-box boundary.
-/
theorem integrable_divergence_of_contDiffOn_isOpen_Icc_subset
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    {V : Set (Fin (n + 1) → Real)} (hV : IsOpen V) (hbox : Icc a b ⊆ V)
    (hω : ContDiffOn Real ⊤ ω V) :
    IntegrableOn
      (fun x => ∑ i : Fin (n + 1),
        ((-1 : Real) ^ (i : Nat) •
          fderiv Real (CubeStokes.toCoordNForm ω i) x) (Pi.single i 1))
      (Icc a b) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply continuousOn_finset_sum
  intro i _hi
  have hcoeff : ContDiffOn Real ⊤ (CubeStokes.toCoordNForm ω i) V :=
    toCoordNForm_contDiffOn ω hω i
  have hfderiv :
      ContinuousOn (fderiv Real (CubeStokes.toCoordNForm ω i)) V :=
    hcoeff.continuousOn_fderiv_of_isOpen hV (by simp)
  have happly :
      ContinuousOn
        (fun x => fderiv Real (CubeStokes.toCoordNForm ω i) x (Pi.single i 1)) V :=
    (ContinuousLinearMap.apply Real Real (Pi.single i 1)).continuous.comp_continuousOn hfderiv
  exact ((continuousOn_const.mul happly).mono hbox : _)

/--
Bundled closed-box regularity generated by ambient-open smoothness around the
closed box.
-/
theorem closedBoxRegularity_of_contDiffOn_isOpen_Icc_subset
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    {V : Set (Fin (n + 1) → Real)} (hV : IsOpen V) (hbox : Icc a b ⊆ V)
    (hω : ContDiffOn Real ⊤ ω V) :
    (∀ i : Fin (n + 1),
      ContinuousOn (CubeStokes.signedCoeff (CubeStokes.toCoordNForm ω) i) (Icc a b)) ∧
    IntegrableOn
      (fun x => ∑ i : Fin (n + 1),
        ((-1 : Real) ^ (i : Nat) •
          fderiv Real (CubeStokes.toCoordNForm ω i) x) (Pi.single i 1))
      (Icc a b) :=
  ⟨continuous_signedCoeff_of_contDiffOn_isOpen_Icc_subset ω a b hV hbox hω,
    integrable_divergence_of_contDiffOn_isOpen_Icc_subset ω a b hV hbox hω⟩

namespace HalfSpaceBoxOpenInteriorSmoothnessFields

variable
    {ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real}
    {a b : Fin (n + 1) → Real}

/-- Open-interior smoothness gives differentiability at every point of the
coordinate open box. -/
theorem differentiableAt_on_openInterior
    (D : HalfSpaceBoxOpenInteriorSmoothnessFields ω a b) :
    ∀ x ∈ halfSpaceBoxOpenInterior a b, DifferentiableAt Real ω x := by
  intro x hx
  exact
    (D.contDiffOn_openInterior.contDiffAt
      (D.isOpen_U.mem_nhds (D.openInterior_subset_U hx))).differentiableAt
      (by simp)

/-- The bulk bridge supplied by the open-interior smoothness data. -/
theorem bulk_eq_boxIntegral
    (D : HalfSpaceBoxOpenInteriorSmoothnessFields ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      CubeStokes.boxIntegral (CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω)) a b :=
  halfSpaceLocalBulkIntegral_eq_boxIntegral_of_differentiableAt_on_openBox
    ω a b D.differentiableAt_on_openInterior

/--
Build open-interior smoothness fields from separate open-interior smoothness
and ambient-open regularity around the closed box.

This is the reusable Agent-B constructor: upstream chart code can prove
smoothness on the legal open interior, and only needs an honest closed-box
regularity source when it wants Lean to fill `continuous_signedCoeff` and
`integrable_divergence`.
-/
def ofOpenInteriorAndClosedBoxContDiffOn
    (hle : a ≤ b) (ha0 : a 0 = 0)
    {U : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hopen : halfSpaceBoxOpenInterior a b ⊆ U)
    (hωU : ContDiffOn Real ⊤ ω U)
    {V : Set (Fin (n + 1) → Real)}
    (hV : IsOpen V) (hbox : Icc a b ⊆ V)
    (hωV : ContDiffOn Real ⊤ ω V) :
    HalfSpaceBoxOpenInteriorSmoothnessFields ω a b where
  le := hle
  lower_zero := ha0
  U := U
  isOpen_U := hU
  openInterior_subset_U := hopen
  contDiffOn_openInterior := hωU.of_le le_top
  continuous_signedCoeff :=
    continuous_signedCoeff_of_contDiffOn_isOpen_Icc_subset ω a b hV hbox hωV
  integrable_divergence :=
    integrable_divergence_of_contDiffOn_isOpen_Icc_subset ω a b hV hbox hωV

/--
Special case where the same ambient-open set contains the closed box and
provides all smoothness.
-/
def ofClosedBoxContDiffOn
    (hle : a ≤ b) (ha0 : a 0 = 0)
    {V : Set (Fin (n + 1) → Real)} (hV : IsOpen V) (hbox : Icc a b ⊆ V)
    (hωV : ContDiffOn Real ⊤ ω V) :
    HalfSpaceBoxOpenInteriorSmoothnessFields ω a b :=
  ofOpenInteriorAndClosedBoxContDiffOn (ω := ω) hle ha0 hV
    ((pi_Ioo_subset_Icc a b).trans hbox) hωV hV hbox hωV

end HalfSpaceBoxOpenInteriorSmoothnessFields

namespace HalfSpaceBoxInteriorStokesFields

variable
    {ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real}
    {a b : Fin (n + 1) → Real}

/--
Constructor from smoothness on an open neighborhood of only the coordinate open
box, plus the closed-box continuity and integrability fields required by
`CubeStokes.stokes_on_box`.
-/
def ofOpenInteriorSmoothness
    (D : HalfSpaceBoxOpenInteriorSmoothnessFields ω a b) :
    HalfSpaceBoxInteriorStokesFields ω a b where
  le := D.le
  lower_zero := D.lower_zero
  exceptional := ∅
  exceptional_countable := Set.countable_empty
  continuous_signedCoeff := D.continuous_signedCoeff
  hasFDerivAt_signedCoeff := by
    intro x hx i
    have hxopen : x ∈ halfSpaceBoxOpenInterior a b := hx.1
    have hxU : x ∈ D.U := D.openInterior_subset_U hxopen
    have hcoeffAt :
        ContDiffAt Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (CubeStokes.toCoordNForm ω i) x :=
      (toCoordNForm_contDiffOn_of_level ω D.contDiffOn_openInterior i).contDiffAt
        (D.isOpen_U.mem_nhds hxU)
    exact ((hcoeffAt.differentiableAt (by simp)).hasFDerivAt.const_mul
      ((-1 : Real) ^ (i : Nat)))
  integrable_divergence := D.integrable_divergence
  bulk_eq_boxIntegral := D.bulk_eq_boxIntegral

end HalfSpaceBoxInteriorStokesFields

/-- Public compact-support local half-space Stokes from open-interior
smoothness data. -/
theorem halfSpaceLocalStokes_compactSupport_of_openInteriorSmoothness
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (D : HalfSpaceBoxOpenInteriorSmoothnessFields ω a b)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  (HalfSpaceBoxInteriorStokesFields.ofOpenInteriorSmoothness D).compactSupport hsupp

end Stokes

end
