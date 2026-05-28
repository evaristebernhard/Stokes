import Stokes.HalfSpace.Basic

/-!
# Half-space box faces and support boxes

This file was split out of Stokes.HalfSpace as part of the M6.0
module-structure pass.  The theorem statements and proofs are intended to
remain identical to the monolithic version.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

def faceDomain {n : Nat} (i : Fin (n + 1)) (a b : Fin (n + 1) → Real) :
    Set (Fin n → Real) :=
  Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i)

/-- The box face domain for the lower face in coordinate `0`. -/
def lowerZeroFaceDomain {n : Nat} (a b : Fin (n + 1) → Real) : Set (Fin n → Real) :=
  faceDomain (0 : Fin (n + 1)) a b

/-- The coordinate contribution of the upper `i`-face in `bdryIntegral`. -/
def boxUpperCoordFaceTerm {n : Nat} (ω : CubeStokes.CoordNForm n)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real) : Real :=
  ∫ x in faceDomain i a b, CubeStokes.signedCoeff ω i (Fin.insertNth i (b i) x)

/-- The coordinate contribution of the lower `i`-face in `bdryIntegral`. -/
def boxLowerCoordFaceTerm {n : Nat} (ω : CubeStokes.CoordNForm n)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real) : Real :=
  -∫ x in faceDomain i a b, CubeStokes.signedCoeff ω i (Fin.insertNth i (a i) x)

/-- The signed coordinate contribution of a single box face. -/
def boxCoordFaceTerm {n : Nat} (ω : CubeStokes.CoordNForm n)
    (i : Fin (n + 1)) (upper : Bool) (a b : Fin (n + 1) → Real) : Real :=
  if upper then boxUpperCoordFaceTerm ω i a b else boxLowerCoordFaceTerm ω i a b

/-- The standard tangent frame on the `i`-th coordinate face. -/
def boxFaceTangentFrame {n : Nat} (i : Fin (n + 1)) :
    Fin n → (Fin (n + 1) → Real) :=
  fun k => Pi.single (Fin.succAbove i k) 1

/-- Integral of a mathlib form over the upper `i`-face with the coordinate tangent frame. -/
def boxUpperFormFaceIntegral {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real) : Real :=
  ∫ x in faceDomain i a b, ω (Fin.insertNth i (b i) x) (boxFaceTangentFrame i)

/-- Integral of a mathlib form over the lower `i`-face with the coordinate tangent frame. -/
def boxLowerFormFaceIntegral {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real) : Real :=
  ∫ x in faceDomain i a b, ω (Fin.insertNth i (a i) x) (boxFaceTangentFrame i)

/-- The scalar coefficient of a mathlib form on the `i`-th coordinate face frame. -/
def boxFormFaceCoeff {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) : (Fin (n + 1) → Real) → Real :=
  fun y => ω y (boxFaceTangentFrame i)

/-- Parameterization of a coordinate face at value `c` in coordinate `i`. -/
def boxFaceMap {n : Nat} (i : Fin (n + 1)) (c : Real)
    (x : Fin n → Real) : Fin (n + 1) → Real :=
  Fin.insertNth i c x

/-- Point set of the upper `i`-face of a box. -/
def boxUpperFaceSet {n : Nat} (i : Fin (n + 1)) (a b : Fin (n + 1) → Real) :
    Set (Fin (n + 1) → Real) :=
  boxFaceMap i (b i) '' faceDomain i a b

/-- Point set of the lower `i`-face of a box. -/
def boxLowerFaceSet {n : Nat} (i : Fin (n + 1)) (a b : Fin (n + 1) → Real) :
    Set (Fin (n + 1) → Real) :=
  boxFaceMap i (a i) '' faceDomain i a b

/--
The artificial boundary of a half-space box: the upper `0`-face and all upper
and lower tangential faces.  The lower `0`-face is omitted because it is the
true boundary face of the half-space chart.
-/
def halfSpaceArtificialFaceSet {n : Nat} (a b : Fin (n + 1) → Real) :
    Set (Fin (n + 1) → Real) :=
  boxUpperFaceSet (0 : Fin (n + 1)) a b ∪
    ⋃ i : Fin n, boxUpperFaceSet i.succ a b ∪ boxLowerFaceSet i.succ a b

/--
The half-space chart box region where compact support may live.

It allows support to meet the true boundary face `x₀ = a₀`, but keeps support
strictly away from the artificial upper `0`-face and all artificial tangential
faces.
-/
def halfSpaceSupportBox {n : Nat} (a b : Fin (n + 1) → Real) :
    Set (Fin (n + 1) → Real) :=
  {y | a 0 ≤ y 0 ∧ y 0 < b 0 ∧
    ∀ i : Fin n, a i.succ < y i.succ ∧ y i.succ < b i.succ}

/--
All coordinate face coefficients of a form have topological support inside the
selected half-space chart box.
-/
def boxFaceCoeffTSupportInHalfSpaceBox {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) : Prop :=
  ∀ i : Fin (n + 1), tsupport (boxFormFaceCoeff ω i) ⊆ halfSpaceSupportBox a b

/--
Evaluating a form on a fixed coordinate face frame cannot enlarge its
algebraic support.
-/
theorem boxFormFaceCoeff_support_subset {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) :
    Function.support (boxFormFaceCoeff ω i) ⊆ Function.support ω := by
  intro y hy
  rw [Function.mem_support] at hy ⊢
  intro hω
  exact hy (by simp [boxFormFaceCoeff, hω])

/--
Evaluating a form on a fixed coordinate face frame cannot enlarge its
topological support.
-/
theorem boxFormFaceCoeff_tsupport_subset {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) :
    tsupport (boxFormFaceCoeff ω i) ⊆ tsupport ω := by
  simpa [boxFormFaceCoeff, Function.comp_def] using
    (tsupport_comp_subset
      (g := fun η : (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real =>
        η (boxFaceTangentFrame i)) (by simp) ω)

/--
If the whole form is topologically supported in a selected half-space box, then
all coordinate face coefficients satisfy the selected-box support predicate.
-/
theorem boxFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hsupp : tsupport ω ⊆ halfSpaceSupportBox a b) :
    boxFaceCoeffTSupportInHalfSpaceBox ω a b := by
  intro i
  exact (boxFormFaceCoeff_tsupport_subset ω i).trans hsupp

/-- Coordinate coefficients of a mathlib form inherit local smoothness at any level. -/
theorem toCoordNForm_contDiffOn_of_level {n : Nat} {m : WithTop ℕ∞}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    {U : Set (Fin (n + 1) → Real)}
    (hω : ContDiffOn Real m ω U) (i : Fin (n + 1)) :
    ContDiffOn Real m (CubeStokes.toCoordNForm ω i) U := by
  change ContDiffOn Real m
    ((ContinuousAlternatingMap.apply Real (Fin (n + 1) → Real) Real
      (fun k => Pi.single (Fin.succAbove i k) 1)) ∘ ω) U
  exact hω.continuousLinearMap_comp
    (ContinuousAlternatingMap.apply Real (Fin (n + 1) → Real) Real
      (fun k => Pi.single (Fin.succAbove i k) 1))

/-- Coordinate coefficients of a mathlib form inherit analytic-level local smoothness. -/
theorem toCoordNForm_contDiffOn {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    {U : Set (Fin (n + 1) → Real)}
    (hω : ContDiffOn Real ⊤ ω U) (i : Fin (n + 1)) :
    ContDiffOn Real ⊤ (CubeStokes.toCoordNForm ω i) U :=
  toCoordNForm_contDiffOn_of_level ω hω i

theorem coord_norm_le_norm {n : Nat} (x : Fin (n + 1) → Real) (i : Fin (n + 1)) :
    ‖x i‖ ≤ ‖x‖ := by
  rw [Pi.norm_def]
  exact NNReal.coe_le_coe.mpr
    (Finset.le_sup (f := fun j : Fin (n + 1) => ‖x j‖₊) (Finset.mem_univ i))

theorem fin_coord_norm_le_norm {m : Nat} (x : Fin m → Real) (i : Fin m) :
    ‖x i‖ ≤ ‖x‖ := by
  rw [Pi.norm_def]
  exact NNReal.coe_le_coe.mpr
    (Finset.le_sup (f := fun j : Fin m => ‖x j‖₊) (Finset.mem_univ i))

/--
Compact half-space subsets have a selected chart box whose only allowed support
contact with the boundary is the true lower `0`-face.
-/
theorem exists_halfSpaceSupportBox_of_isCompact {n : Nat}
    {K : Set (Fin (n + 1) → Real)} (hK : IsCompact K)
    (hhalf : K ⊆ upperHalfSpace n) :
    ∃ a b : Fin (n + 1) → Real, a 0 = 0 ∧ a ≤ b ∧ K ⊆ halfSpaceSupportBox a b := by
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  let a : Fin (n + 1) → Real := Fin.cases (0 : Real) (fun _ : Fin n => -(R + 1))
  let b : Fin (n + 1) → Real := Fin.cases (R + 1) (fun _ : Fin n => R + 1)
  refine ⟨a, b, rfl, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ ?_ j
    · dsimp [a, b]
      linarith
    · intro i
      dsimp [a, b]
      linarith
  · intro y hy
    have hynorm : ‖y‖ ≤ R := hR y hy
    have hcoord_le : ∀ j : Fin (n + 1), y j ≤ R := by
      intro j
      exact (le_abs_self (y j)).trans ((coord_norm_le_norm y j).trans hynorm)
    have hcoord_ge : ∀ j : Fin (n + 1), -R ≤ y j := by
      intro j
      have habs : |y j| ≤ R := by
        simpa [Real.norm_eq_abs] using (coord_norm_le_norm y j).trans hynorm
      exact (neg_le_neg habs).trans (neg_abs_le (y j))
    refine ⟨?_, ?_, ?_⟩
    · simpa [a, upperHalfSpace] using hhalf hy
    · have hy0 := hcoord_le 0
      dsimp [b]
      linarith
    · intro i
      constructor
      · have hyi := hcoord_ge i.succ
        dsimp [a]
        linarith
      · have hyi := hcoord_le i.succ
        dsimp [b]
        linarith

/--
Compact subsets of the coordinate half-space fit in a support box.  This is the
set-builder version of `exists_halfSpaceSupportBox_of_isCompact`, convenient
when the half-space hypothesis is produced as `0 ≤ x 0`.
-/
theorem exists_halfSpaceSupportBox_of_isCompact_subset_halfSpace {n : Nat}
    {K : Set (Fin (n + 1) → Real)} (hK : IsCompact K)
    (hhalf : K ⊆ {x | 0 ≤ x 0}) :
    ∃ a b : Fin (n + 1) → Real, a 0 = 0 ∧ a ≤ b ∧ K ⊆ halfSpaceSupportBox a b := by
  exact exists_halfSpaceSupportBox_of_isCompact hK (by simpa [upperHalfSpace] using hhalf)

/--
If the topological support of a local form is compact and lies in the coordinate
half-space, then it fits in a half-space support box.
-/
theorem exists_halfSpaceSupportBox_of_compact_tsupport_subset_halfSpace {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (hK : IsCompact (tsupport ω))
    (hhalf : tsupport ω ⊆ {x | 0 ≤ x 0}) :
    ∃ a b : Fin (n + 1) → Real,
      a 0 = 0 ∧ a ≤ b ∧ tsupport ω ⊆ halfSpaceSupportBox a b := by
  exact exists_halfSpaceSupportBox_of_isCompact_subset_halfSpace hK hhalf

/--
A compact coordinate support certificate is enough to choose a half-space
support box for the form's topological support.
-/
theorem exists_halfSpaceSupportBox_of_tsupport_subset_compact_halfSpace {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    {K : Set (Fin (n + 1) → Real)} (hK : IsCompact K)
    (hsupp : tsupport ω ⊆ K) (hhalf : K ⊆ {x | 0 ≤ x 0}) :
    ∃ a b : Fin (n + 1) → Real,
      a 0 = 0 ∧ a ≤ b ∧ tsupport ω ⊆ halfSpaceSupportBox a b := by
  obtain ⟨a, b, ha0, hle, hKbox⟩ :=
    exists_halfSpaceSupportBox_of_isCompact_subset_halfSpace hK hhalf
  exact ⟨a, b, ha0, hle, hsupp.trans hKbox⟩

/-- The lower boundary face of a coordinate box is compact. -/
theorem isCompact_lowerZeroFaceDomain {n : Nat} (a b : Fin (n + 1) → Real) :
    IsCompact (lowerZeroFaceDomain a b : Set (Fin n → Real)) := by
  simpa [lowerZeroFaceDomain, faceDomain] using
    (isCompact_Icc :
      IsCompact (Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
        (b ∘ Fin.succAbove (0 : Fin (n + 1))) : Set (Fin n → Real)))

theorem lowerZeroFaceDomain_mem_nhds_of_lt {n : Nat}
    {a b : Fin (n + 1) → Real} {u : Fin n → Real}
    (ha : ∀ i : Fin n, a i.succ < u i)
    (hb : ∀ i : Fin n, u i < b i.succ) :
    lowerZeroFaceDomain a b ∈ 𝓝 u := by
  simpa [lowerZeroFaceDomain, faceDomain, Function.comp_def] using
    (pi_Icc_mem_nhds
      (a := a ∘ Fin.succAbove (0 : Fin (n + 1)))
      (b := b ∘ Fin.succAbove (0 : Fin (n + 1))) (x := u)
      (by intro i; simpa [Function.comp_def] using ha i)
      (by intro i; simpa [Function.comp_def] using hb i))

/--
Compact subsets of boundary coordinates fit into some lower-zero face domain.

This is the boundary-only analogue of `exists_halfSpaceSupportBox_of_isCompact`.
The normal coordinate of the ambient box is fixed to `0`; only the tangential
coordinates are used by `lowerZeroFaceDomain`.
-/
theorem exists_lowerZeroFaceDomain_of_isCompact {n : Nat}
    {K : Set (Fin n → Real)} (hK : IsCompact K) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      K ⊆ lowerZeroFaceDomain c d := by
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  let c : Fin (n + 1) → Real := Fin.cases (0 : Real) (fun _ : Fin n => -(R + 1))
  let d : Fin (n + 1) → Real := Fin.cases (0 : Real) (fun _ : Fin n => R + 1)
  refine ⟨c, d, rfl, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ ?_ j
    · dsimp [c, d]
      exact le_rfl
    · intro i
      dsimp [c, d]
      linarith
  · intro x hx
    have hxnorm : ‖x‖ ≤ R := hR x hx
    have hcoord_le : ∀ i : Fin n, x i ≤ R := by
      intro i
      exact (le_abs_self (x i)).trans ((fin_coord_norm_le_norm x i).trans hxnorm)
    have hcoord_ge : ∀ i : Fin n, -R ≤ x i := by
      intro i
      have habs : |x i| ≤ R := by
        simpa [Real.norm_eq_abs] using (fin_coord_norm_le_norm x i).trans hxnorm
      exact (neg_le_neg habs).trans (neg_abs_le (x i))
    rw [lowerZeroFaceDomain, faceDomain]
    constructor
    · intro i
      have hxi := hcoord_ge i
      dsimp [c, Function.comp_def]
      linarith
    · intro i
      have hxi := hcoord_le i
      dsimp [d, Function.comp_def]
      linarith

/--
Every neighborhood of a boundary-coordinate point contains a lower-zero face
box around that point.

This is the small-box selection step used after local openness from the inverse
function theorem.
-/
theorem exists_lowerZeroFaceDomain_subset_of_mem_nhds {n : Nat}
    {U : Set (Fin n → Real)} {y : Fin n → Real} (hU : U ∈ 𝓝 y) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      y ∈ lowerZeroFaceDomain c d ∧ lowerZeroFaceDomain c d ⊆ U := by
  obtain ⟨ε, hεpos, hεsubset⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  let c : Fin (n + 1) → Real := Fin.cases (0 : Real) (fun i : Fin n => y i - ε)
  let d : Fin (n + 1) → Real := Fin.cases (0 : Real) (fun i : Fin n => y i + ε)
  refine ⟨c, d, rfl, ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ ?_ j
    · dsimp [c, d]
      exact le_rfl
    · intro i
      dsimp [c, d]
      linarith
  · rw [lowerZeroFaceDomain, faceDomain]
    constructor
    · intro i
      dsimp [c, Function.comp_def]
      linarith
    · intro i
      dsimp [d, Function.comp_def]
      linarith
  · intro z hz
    apply hεsubset
    rw [Metric.mem_closedBall]
    rw [dist_pi_le_iff (le_of_lt hεpos)]
    intro i
    rw [Real.dist_eq, abs_sub_le_iff]
    rw [lowerZeroFaceDomain, faceDomain] at hz
    have hleft := hz.1 i
    have hright := hz.2 i
    constructor
    · have hzi : z i ≤ y i + ε := by
        simpa [d, Function.comp_def] using hright
      linarith
    · have hzi : y i - ε ≤ z i := by
        simpa [c, Function.comp_def] using hleft
      linarith

theorem boxUpperFormFaceIntegral_eq_zero_of_forall {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real)
    (h : ∀ x ∈ faceDomain i a b,
      ω (Fin.insertNth i (b i) x) (boxFaceTangentFrame i) = 0) :
    boxUpperFormFaceIntegral ω i a b = 0 := by
  unfold boxUpperFormFaceIntegral
  rw [show (∫ x in faceDomain i a b,
      ω (Fin.insertNth i (b i) x) (boxFaceTangentFrame i)) =
        ∫ x in faceDomain i a b, (0 : Real) from by
    refine MeasureTheory.setIntegral_congr_fun (by simp [faceDomain]) ?_
    intro x hx
    exact h x hx]
  simp

theorem boxLowerFormFaceIntegral_eq_zero_of_forall {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real)
    (h : ∀ x ∈ faceDomain i a b,
      ω (Fin.insertNth i (a i) x) (boxFaceTangentFrame i) = 0) :
    boxLowerFormFaceIntegral ω i a b = 0 := by
  unfold boxLowerFormFaceIntegral
  rw [show (∫ x in faceDomain i a b,
      ω (Fin.insertNth i (a i) x) (boxFaceTangentFrame i)) =
        ∫ x in faceDomain i a b, (0 : Real) from by
    refine MeasureTheory.setIntegral_congr_fun (by simp [faceDomain]) ?_
    intro x hx
    exact h x hx]
  simp

theorem boxUpperFormFaceIntegral_eq_zero_of_support_disjoint {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real)
    (h : Disjoint (boxUpperFaceSet i a b) (Function.support (boxFormFaceCoeff ω i))) :
    boxUpperFormFaceIntegral ω i a b = 0 :=
  boxUpperFormFaceIntegral_eq_zero_of_forall ω i a b fun x hx => by
    have hxface : boxFaceMap i (b i) x ∈ boxUpperFaceSet i a b :=
      ⟨x, hx, rfl⟩
    have hnot : boxFaceMap i (b i) x ∉ Function.support (boxFormFaceCoeff ω i) :=
      disjoint_left.1 h hxface
    simpa [boxFormFaceCoeff, boxFaceMap] using Function.notMem_support.mp hnot

theorem boxLowerFormFaceIntegral_eq_zero_of_support_disjoint {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real)
    (h : Disjoint (boxLowerFaceSet i a b) (Function.support (boxFormFaceCoeff ω i))) :
    boxLowerFormFaceIntegral ω i a b = 0 :=
  boxLowerFormFaceIntegral_eq_zero_of_forall ω i a b fun x hx => by
    have hxface : boxFaceMap i (a i) x ∈ boxLowerFaceSet i a b :=
      ⟨x, hx, rfl⟩
    have hnot : boxFaceMap i (a i) x ∉ Function.support (boxFormFaceCoeff ω i) :=
      disjoint_left.1 h hxface
    simpa [boxFormFaceCoeff, boxFaceMap] using Function.notMem_support.mp hnot

theorem boxUpperCoordFaceTerm_toCoordNForm {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real) :
    boxUpperCoordFaceTerm (CubeStokes.toCoordNForm ω) i a b =
      upperFaceSign i * boxUpperFormFaceIntegral ω i a b := by
  unfold boxUpperCoordFaceTerm boxUpperFormFaceIntegral boxFaceTangentFrame
  simp [CubeStokes.signedCoeff, CubeStokes.toCoordNForm, upperFaceSign, integral_const_mul]

theorem boxLowerCoordFaceTerm_toCoordNForm {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real) :
    boxLowerCoordFaceTerm (CubeStokes.toCoordNForm ω) i a b =
      lowerFaceSign i * boxLowerFormFaceIntegral ω i a b := by
  unfold boxLowerCoordFaceTerm boxLowerFormFaceIntegral boxFaceTangentFrame
  simp [CubeStokes.signedCoeff, CubeStokes.toCoordNForm, lowerFaceSign, integral_const_mul,
    neg_mul]

/-- The coordinate lower-face contribution in the `x₀ = a₀` face of `bdryIntegral`. -/
def boxLowerZeroCoordFaceTerm {n : Nat} (ω : CubeStokes.CoordNForm n)
    (a b : Fin (n + 1) → Real) : Real :=
  boxLowerCoordFaceTerm ω (0 : Fin (n + 1)) a b

/--
All box boundary terms except the lower `0`-face.  For a box sitting in the
upper half-space with `a 0 = 0`, this is the artificial boundary contribution
that later compact-support or cancellation hypotheses should remove.
-/
def boxRemainingCoordFaceTerms {n : Nat} (ω : CubeStokes.CoordNForm n)
    (a b : Fin (n + 1) → Real) : Real :=
  boxUpperCoordFaceTerm ω (0 : Fin (n + 1)) a b +
    ∑ i : Fin n,
      (boxUpperCoordFaceTerm ω i.succ a b + boxLowerCoordFaceTerm ω i.succ a b)

/-- The remaining artificial box faces, written directly for a mathlib form. -/
def boxRemainingFormFaceTerms {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) : Real :=
  upperFaceSign (0 : Fin (n + 1)) * boxUpperFormFaceIntegral ω (0 : Fin (n + 1)) a b +
    ∑ i : Fin n,
      (upperFaceSign i.succ * boxUpperFormFaceIntegral ω i.succ a b +
        lowerFaceSign i.succ * boxLowerFormFaceIntegral ω i.succ a b)

/-- If the upper `0`-face vanishes and every remaining signed face pair cancels, the artificial
box-boundary remainder is zero. -/
theorem boxRemainingFormFaceTerms_eq_zero_of_face_cancellation {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (h0 : boxUpperFormFaceIntegral ω (0 : Fin (n + 1)) a b = 0)
    (hsucc : ∀ i : Fin n,
      upperFaceSign i.succ * boxUpperFormFaceIntegral ω i.succ a b +
        lowerFaceSign i.succ * boxLowerFormFaceIntegral ω i.succ a b = 0) :
    boxRemainingFormFaceTerms ω a b = 0 := by
  unfold boxRemainingFormFaceTerms
  rw [h0]
  simp [hsucc]

/-- Pointwise vanishing on each artificial face makes the artificial box-boundary remainder zero. -/
theorem boxRemainingFormFaceTerms_eq_zero_of_forall {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (h0 : ∀ x ∈ faceDomain (0 : Fin (n + 1)) a b,
      ω (Fin.insertNth (0 : Fin (n + 1)) (b 0) x)
        (boxFaceTangentFrame (0 : Fin (n + 1))) = 0)
    (hsucc : ∀ i : Fin n,
      (∀ x ∈ faceDomain i.succ a b,
        ω (Fin.insertNth i.succ (b i.succ) x) (boxFaceTangentFrame i.succ) = 0) ∧
      (∀ x ∈ faceDomain i.succ a b,
        ω (Fin.insertNth i.succ (a i.succ) x) (boxFaceTangentFrame i.succ) = 0)) :
    boxRemainingFormFaceTerms ω a b = 0 := by
  apply boxRemainingFormFaceTerms_eq_zero_of_face_cancellation
  · exact boxUpperFormFaceIntegral_eq_zero_of_forall ω (0 : Fin (n + 1)) a b h0
  · intro i
    rw [boxUpperFormFaceIntegral_eq_zero_of_forall ω i.succ a b (hsucc i).1,
      boxLowerFormFaceIntegral_eq_zero_of_forall ω i.succ a b (hsucc i).2]
    simp

/-- If the algebraic support of the face coefficient misses every artificial face, the artificial
box-boundary remainder is zero. -/
theorem boxRemainingFormFaceTerms_eq_zero_of_support_disjoint {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (h0 : Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) a b)
      (Function.support (boxFormFaceCoeff ω (0 : Fin (n + 1)))))
    (hsucc : ∀ i : Fin n,
      Disjoint (boxUpperFaceSet i.succ a b) (Function.support (boxFormFaceCoeff ω i.succ)) ∧
      Disjoint (boxLowerFaceSet i.succ a b) (Function.support (boxFormFaceCoeff ω i.succ))) :
    boxRemainingFormFaceTerms ω a b = 0 := by
  apply boxRemainingFormFaceTerms_eq_zero_of_face_cancellation
  · exact boxUpperFormFaceIntegral_eq_zero_of_support_disjoint
      ω (0 : Fin (n + 1)) a b h0
  · intro i
    rw [boxUpperFormFaceIntegral_eq_zero_of_support_disjoint ω i.succ a b (hsucc i).1,
      boxLowerFormFaceIntegral_eq_zero_of_support_disjoint ω i.succ a b (hsucc i).2]
    simp

/--
If the algebraic support of the form is disjoint from the whole artificial
boundary of the half-space box, then the artificial boundary integral vanishes.

This is the direct formal analogue of
`supp α ∩ ∂ₐᵣₜ Q = ∅ -> ∫_{∂ₐᵣₜ Q} α = 0`.
-/
theorem boxRemainingFormFaceTerms_eq_zero_of_support_disjoint_artificial {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (h : Disjoint (halfSpaceArtificialFaceSet a b) (Function.support ω)) :
    boxRemainingFormFaceTerms ω a b = 0 := by
  refine boxRemainingFormFaceTerms_eq_zero_of_support_disjoint ω a b ?h0 ?hsucc
  · exact (h.mono_left (by
        intro y hy
        exact Or.inl hy)).mono_right
      (boxFormFaceCoeff_support_subset ω (0 : Fin (n + 1)))
  · intro i
    constructor
    · exact (h.mono_left (by
          intro y hy
          exact Or.inr (mem_iUnion.2 ⟨i, Or.inl hy⟩))).mono_right
        (boxFormFaceCoeff_support_subset ω i.succ)
    · exact (h.mono_left (by
          intro y hy
          exact Or.inr (mem_iUnion.2 ⟨i, Or.inr hy⟩))).mono_right
        (boxFormFaceCoeff_support_subset ω i.succ)

/-- Topological-support version of `boxRemainingFormFaceTerms_eq_zero_of_support_disjoint`,
matching the compact-support use case. -/
theorem boxRemainingFormFaceTerms_eq_zero_of_tsupport_disjoint {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (h0 : Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) a b)
      (tsupport (boxFormFaceCoeff ω (0 : Fin (n + 1)))))
    (hsucc : ∀ i : Fin n,
      Disjoint (boxUpperFaceSet i.succ a b) (tsupport (boxFormFaceCoeff ω i.succ)) ∧
      Disjoint (boxLowerFaceSet i.succ a b) (tsupport (boxFormFaceCoeff ω i.succ))) :
    boxRemainingFormFaceTerms ω a b = 0 :=
  boxRemainingFormFaceTerms_eq_zero_of_support_disjoint ω a b
    (h0.mono_right (subset_tsupport (boxFormFaceCoeff ω (0 : Fin (n + 1)))))
    fun i => ⟨(hsucc i).1.mono_right (subset_tsupport (boxFormFaceCoeff ω i.succ)),
      (hsucc i).2.mono_right (subset_tsupport (boxFormFaceCoeff ω i.succ))⟩

/--
If the topological support of the form is disjoint from the whole artificial
boundary of the half-space box, then the artificial boundary integral vanishes.

This is the support-theoretic form of
`supp α ∩ ∂ₐᵣₜ Q = ∅ -> ∫_{∂ₐᵣₜ Q} α = 0` for the current half-space box API.
-/
theorem boxRemainingFormFaceTerms_eq_zero_of_tsupport_disjoint_artificial {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (h : Disjoint (halfSpaceArtificialFaceSet a b) (tsupport ω)) :
    boxRemainingFormFaceTerms ω a b = 0 := by
  refine boxRemainingFormFaceTerms_eq_zero_of_tsupport_disjoint ω a b ?h0 ?hsucc
  · exact (h.mono_left (by
        intro y hy
        exact Or.inl hy)).mono_right
      (boxFormFaceCoeff_tsupport_subset ω (0 : Fin (n + 1)))
  · intro i
    constructor
    · exact (h.mono_left (by
          intro y hy
          exact Or.inr (mem_iUnion.2 ⟨i, Or.inl hy⟩))).mono_right
        (boxFormFaceCoeff_tsupport_subset ω i.succ)
    · exact (h.mono_left (by
          intro y hy
          exact Or.inr (mem_iUnion.2 ⟨i, Or.inr hy⟩))).mono_right
        (boxFormFaceCoeff_tsupport_subset ω i.succ)

/--
If the form is topologically supported in the half-space support box, then its
support is disjoint from the artificial boundary of the half-space box.
-/
theorem halfSpaceArtificialFaceSet_disjoint_tsupport_of_subset_halfSpaceSupportBox {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hsupp : tsupport ω ⊆ halfSpaceSupportBox a b) :
    Disjoint (halfSpaceArtificialFaceSet a b) (tsupport ω) := by
  rw [disjoint_left]
  intro y hy hω
  have hbox : y ∈ halfSpaceSupportBox a b := hsupp hω
  rw [halfSpaceArtificialFaceSet] at hy
  rcases hy with hy0 | hyRest
  · rcases hy0 with ⟨x, hx, rfl⟩
    have hlt : (boxFaceMap (0 : Fin (n + 1)) (b 0) x) 0 < b 0 := hbox.2.1
    unfold boxFaceMap at hlt
    rw [Fin.insertNth_apply_same] at hlt
    exact (lt_irrefl (b 0)) hlt
  · rcases mem_iUnion.1 hyRest with ⟨i, hi⟩
    rcases hi with hiUpper | hiLower
    · rcases hiUpper with ⟨x, hx, rfl⟩
      have hlt : (boxFaceMap i.succ (b i.succ) x) i.succ < b i.succ :=
        (hbox.2.2 i).2
      unfold boxFaceMap at hlt
      rw [Fin.insertNth_apply_same] at hlt
      exact (lt_irrefl (b i.succ)) hlt
    · rcases hiLower with ⟨x, hx, rfl⟩
      have hlt : a i.succ < (boxFaceMap i.succ (a i.succ) x) i.succ :=
        (hbox.2.2 i).1
      unfold boxFaceMap at hlt
      rw [Fin.insertNth_apply_same] at hlt
      exact (lt_irrefl (a i.succ)) hlt

/--
Natural compact-support form of artificial-boundary vanishing: the whole form,
not just its face coefficients, is topologically supported in the half-space
support box.
-/
theorem boxRemainingFormFaceTerms_eq_zero_of_tsupport_subset_halfSpaceSupportBox' {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hsupp : tsupport ω ⊆ halfSpaceSupportBox a b) :
    boxRemainingFormFaceTerms ω a b = 0 :=
  boxRemainingFormFaceTerms_eq_zero_of_tsupport_disjoint_artificial ω a b
    (halfSpaceArtificialFaceSet_disjoint_tsupport_of_subset_halfSpaceSupportBox ω a b hsupp)

/--
Selected-box lemma: if the relevant topological supports lie in the half-space
support box, then they are disjoint from every artificial face of the auxiliary
box.
-/
theorem boxArtificialFaces_tsupport_disjoint_of_subset_halfSpaceSupportBox {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) a b)
        (tsupport (boxFormFaceCoeff ω (0 : Fin (n + 1)))) ∧
      ∀ i : Fin n,
        Disjoint (boxUpperFaceSet i.succ a b) (tsupport (boxFormFaceCoeff ω i.succ)) ∧
        Disjoint (boxLowerFaceSet i.succ a b) (tsupport (boxFormFaceCoeff ω i.succ)) := by
  constructor
  · rw [disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    have hlt : (boxFaceMap (0 : Fin (n + 1)) (b 0) x) 0 < b 0 :=
      ((hsupp (0 : Fin (n + 1))) hy).2.1
    unfold boxFaceMap at hlt
    rw [Fin.insertNth_apply_same] at hlt
    exact (lt_irrefl (b 0)) hlt
  · intro i
    constructor
    · rw [disjoint_left]
      rintro y ⟨x, hx, rfl⟩ hy
      have hlt : (boxFaceMap i.succ (b i.succ) x) i.succ < b i.succ :=
        (((hsupp i.succ) hy).2.2 i).2
      unfold boxFaceMap at hlt
      rw [Fin.insertNth_apply_same] at hlt
      exact (lt_irrefl (b i.succ)) hlt
    · rw [disjoint_left]
      rintro y ⟨x, hx, rfl⟩ hy
      have hlt : a i.succ < (boxFaceMap i.succ (a i.succ) x) i.succ :=
        (((hsupp i.succ) hy).2.2 i).1
      unfold boxFaceMap at hlt
      rw [Fin.insertNth_apply_same] at hlt
      exact (lt_irrefl (a i.succ)) hlt

/-- Compact-support-in-a-selected-box version of artificial face vanishing. -/
theorem boxRemainingFormFaceTerms_eq_zero_of_tsupport_subset_halfSpaceSupportBox {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    boxRemainingFormFaceTerms ω a b = 0 := by
  rcases boxArtificialFaces_tsupport_disjoint_of_subset_halfSpaceSupportBox
    ω a b hsupp with ⟨h0, hsucc⟩
  exact boxRemainingFormFaceTerms_eq_zero_of_tsupport_disjoint ω a b h0 hsucc

theorem boxRemainingCoordFaceTerms_toCoordNForm {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) :
    boxRemainingCoordFaceTerms (CubeStokes.toCoordNForm ω) a b =
      boxRemainingFormFaceTerms ω a b := by
  unfold boxRemainingCoordFaceTerms boxRemainingFormFaceTerms
  rw [boxUpperCoordFaceTerm_toCoordNForm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [boxUpperCoordFaceTerm_toCoordNForm, boxLowerCoordFaceTerm_toCoordNForm]

/--
The box boundary integral splits into the geometric half-space boundary face
and all remaining artificial box faces.
-/
theorem bdryIntegral_eq_lowerZero_add_remaining {n : Nat}
    (ω : CubeStokes.CoordNForm n) (a b : Fin (n + 1) → Real) :
    CubeStokes.bdryIntegral ω a b =
      boxLowerZeroCoordFaceTerm ω a b + boxRemainingCoordFaceTerms ω a b := by
  unfold CubeStokes.bdryIntegral boxLowerZeroCoordFaceTerm boxRemainingCoordFaceTerms
    boxUpperCoordFaceTerm boxLowerCoordFaceTerm faceDomain
  rw [Fin.sum_univ_succ]
  simp [sub_eq_add_neg, add_assoc, add_comm]


end Stokes

end
