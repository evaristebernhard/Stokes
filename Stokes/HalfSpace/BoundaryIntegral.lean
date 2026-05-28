import Stokes.HalfSpace.Faces

/-!
# Half-space boundary integrals

This file was split out of Stokes.HalfSpace as part of the M6.0
module-structure pass.  The theorem statements and proofs are intended to
remain identical to the monolithic version.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

def halfSpaceBoundaryCoordTerm {n : Nat} (ω : CubeStokes.CoordNForm n)
    (a b : Fin (n + 1) → Real) : Real :=
  halfSpaceBoundarySign n *
    ∫ x in lowerZeroFaceDomain a b, ω (0 : Fin (n + 1)) (boundaryInclusion n x)

theorem lowerZeroSignedCoeff_eq_halfSpaceBoundarySign {n : Nat}
    (ω : CubeStokes.CoordNForm n) (x : Fin (n + 1) → Real) :
    -CubeStokes.signedCoeff ω (0 : Fin (n + 1)) x =
      halfSpaceBoundarySign n * ω (0 : Fin (n + 1)) x := by
  simp [CubeStokes.signedCoeff, halfSpaceBoundarySign, lowerFaceSign]

/--
For a box whose lower `0`-face lies on `{x₀ = 0}`, the coordinate lower-face
term in the box boundary integral is exactly the half-space boundary-sign term.
-/
theorem boxLowerZeroCoordFaceTerm_eq_halfSpaceBoundaryCoordTerm {n : Nat}
    (ω : CubeStokes.CoordNForm n) (a b : Fin (n + 1) → Real) (ha0 : a 0 = 0) :
    boxLowerZeroCoordFaceTerm ω a b = halfSpaceBoundaryCoordTerm ω a b := by
  have hfun :
      (fun x : Fin n → Real => ω (0 : Fin (n + 1)) (Fin.cons (0 : Real) x)) =
        fun x => ω (0 : Fin (n + 1)) (boundaryInclusion n x) := by
    funext x
    rw [cons_zero_eq_boundaryInclusion]
  simp [boxLowerZeroCoordFaceTerm, boxLowerCoordFaceTerm, faceDomain, lowerZeroFaceDomain,
    halfSpaceBoundaryCoordTerm, CubeStokes.signedCoeff, halfSpaceBoundarySign, lowerFaceSign,
    ha0, hfun]

/-- The integral of a mathlib form over the coordinate `x₀ = 0` boundary face. -/
def halfSpaceBoundaryFormIntegral {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) : Real :=
  ∫ x in lowerZeroFaceDomain a b, ω (boundaryInclusion n x) (boundaryTangent n)

/--
Boundary integral over `{x₀ = 0}` using the boundary orientation induced by the
outward-normal-first convention.
-/
def outwardFirstHalfSpaceBoundaryFormIntegral {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) : Real :=
  outwardFirstBoundaryOrientationSign n * halfSpaceBoundaryFormIntegral ω a b

theorem outwardFirstHalfSpaceBoundaryFormIntegral_eq_halfSpaceBoundarySign_mul {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) :
    outwardFirstHalfSpaceBoundaryFormIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b := by
  rw [outwardFirstHalfSpaceBoundaryFormIntegral,
    ← halfSpaceBoundarySign_eq_outwardFirstBoundaryOrientationSign]

/-- Pull an ambient `n`-form on `R^(n+1)` back to the boundary tangent space. -/
def boundaryTangentPullbackForm {n : Nat}
    (η : (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real) :
    (Fin n → Real) [⋀^Fin n]→L[Real] Real :=
  η.compContinuousLinearMap (boundaryTangentInclusion n)

theorem boundaryTangentPullbackForm_apply_basisFun {n : Nat}
    (η : (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real) :
    boundaryTangentPullbackForm η (Pi.basisFun Real (Fin n)) = η (boundaryTangent n) := by
  rw [boundaryTangentPullbackForm]
  change η (fun i : Fin n => boundaryTangentInclusion n ((Pi.basisFun Real (Fin n)) i)) =
    η (boundaryTangent n)
  congr 1
  funext i
  exact boundaryTangentInclusion_basisFun n i

/--
Top-degree boundary forms transform by the determinant of the tangent map.

This is the pointwise Jacobian algebra used before any measure-theoretic
change-of-variables theorem is invoked.
-/
theorem boundaryTangentPullbackForm_comp_apply_basisFun_eq_det_mul {n : Nat}
    (η : (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (L : (Fin n → Real) →L[Real] (Fin n → Real)) :
    boundaryTangentPullbackForm η (L ∘ Pi.basisFun Real (Fin n)) =
      (LinearMap.toMatrix' (L : (Fin n → Real) →ₗ[Real] (Fin n → Real))).det *
        η (boundaryTangent n) := by
  have hη :
      (boundaryTangentPullbackForm η).toAlternatingMap =
        (boundaryTangentPullbackForm η).toAlternatingMap (Pi.basisFun Real (Fin n)) •
          (Pi.basisFun Real (Fin n)).det :=
    AlternatingMap.eq_smul_basis_det
      (e := Pi.basisFun Real (Fin n)) (boundaryTangentPullbackForm η).toAlternatingMap
  have happ := congrArg
    (fun f : (Fin n → Real) [⋀^Fin n]→ₗ[Real] Real =>
      f (L ∘ Pi.basisFun Real (Fin n))) hη
  have hdet :
      (Pi.basisFun Real (Fin n)).det (L ∘ Pi.basisFun Real (Fin n)) =
        (LinearMap.toMatrix' (L : (Fin n → Real) →ₗ[Real] (Fin n → Real))).det := by
    have hcomp :=
      Module.Basis.det_comp (e := Pi.basisFun Real (Fin n))
        (f := (L : (Fin n → Real) →ₗ[Real] (Fin n → Real)))
        (v := Pi.basisFun Real (Fin n))
    calc
      (Pi.basisFun Real (Fin n)).det (L ∘ Pi.basisFun Real (Fin n)) =
          LinearMap.det (L : (Fin n → Real) →ₗ[Real] (Fin n → Real)) *
            (Pi.basisFun Real (Fin n)).det (Pi.basisFun Real (Fin n)) := hcomp
      _ = LinearMap.det (L : (Fin n → Real) →ₗ[Real] (Fin n → Real)) := by
        rw [Module.Basis.det_self, mul_one]
      _ = (LinearMap.toMatrix' (L : (Fin n → Real) →ₗ[Real] (Fin n → Real))).det := by
        exact (LinearMap.det_toMatrix'
          (L : (Fin n → Real) →ₗ[Real] (Fin n → Real))).symm
  have happ' :
      boundaryTangentPullbackForm η (L ∘ Pi.basisFun Real (Fin n)) =
        boundaryTangentPullbackForm η (Pi.basisFun Real (Fin n)) *
          (Pi.basisFun Real (Fin n)).det (L ∘ Pi.basisFun Real (Fin n)) := by
    simpa only [ContinuousAlternatingMap.coe_toAlternatingMap,
      AlternatingMap.smul_apply, smul_eq_mul] using happ
  calc
    boundaryTangentPullbackForm η (L ∘ Pi.basisFun Real (Fin n)) =
        boundaryTangentPullbackForm η (Pi.basisFun Real (Fin n)) *
          (Pi.basisFun Real (Fin n)).det (L ∘ Pi.basisFun Real (Fin n)) := happ'
    _ = η (boundaryTangent n) *
        (LinearMap.toMatrix' (L : (Fin n → Real) →ₗ[Real] (Fin n → Real))).det := by
      rw [boundaryTangentPullbackForm_apply_basisFun, hdet]
    _ = (LinearMap.toMatrix' (L : (Fin n → Real) →ₗ[Real] (Fin n → Real))).det *
        η (boundaryTangent n) := by
      rw [mul_comm]

theorem ambientBoundaryForm_tangentMap_eq_det_mul {n : Nat}
    (η : (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (L : (Fin n → Real) →L[Real] (Fin n → Real)) :
    η (boundaryTangentInclusion n ∘ L ∘ Pi.basisFun Real (Fin n)) =
      (LinearMap.toMatrix' (L : (Fin n → Real) →ₗ[Real] (Fin n → Real))).det *
        η (boundaryTangent n) := by
  simpa [boundaryTangentPullbackForm, Function.comp_assoc]
    using boundaryTangentPullbackForm_comp_apply_basisFun_eq_det_mul η L

/--
The boundary point obtained from a point of the lower `0`-face domain lies in
the ambient box whenever the box starts at `x₀ = 0`.
-/
theorem boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain {n : Nat}
    {a b : Fin (n + 1) → Real} (ha0 : a 0 = 0) (hle : a ≤ b)
    {x : Fin n → Real} (hx : x ∈ lowerZeroFaceDomain a b) :
    boundaryInclusion n x ∈ Set.Icc a b := by
  rcases hx with ⟨hlo, hhi⟩
  constructor
  · intro i
    refine Fin.cases ?_ ?_ i
    · simp [boundaryInclusion, ha0]
    · intro j
      simpa [lowerZeroFaceDomain, faceDomain, Function.comp_def, boundaryInclusion]
        using hlo j
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa [boundaryInclusion, ha0] using hle (0 : Fin (n + 1))
    · intro j
      simpa [lowerZeroFaceDomain, faceDomain, Function.comp_def, boundaryInclusion]
        using hhi j

/--
The lower `0`-face coordinate coefficient extracted from a mathlib form agrees
with evaluating the form on the standard boundary tangent frame.
-/
theorem lowerZero_toCoordNForm_eq_boundaryForm {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (x : Fin n → Real) :
    CubeStokes.toCoordNForm ω (0 : Fin (n + 1)) (boundaryInclusion n x) =
      ω (boundaryInclusion n x) (boundaryTangent n) := by
  rw [CubeStokes.toCoordNForm, zeroFaceBasis_eq_boundaryTangent]

/--
The half-space boundary-sign version of the lower `0`-face term for a mathlib
form is `-` the integral over the boundary tangent frame.
-/
theorem halfSpaceBoundaryCoordTerm_toCoordNForm {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) :
    halfSpaceBoundaryCoordTerm (CubeStokes.toCoordNForm ω) a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b := by
  simp [halfSpaceBoundaryCoordTerm, halfSpaceBoundaryFormIntegral,
    lowerZero_toCoordNForm_eq_boundaryForm]

/--
Combined bridge from the lower `0`-face term in the box boundary integral to
the half-space boundary-sign integral of a mathlib form.
-/
theorem boxLowerZeroCoordFaceTerm_toCoordNForm_eq_halfSpaceBoundaryFormTerm {n : Nat}
    (ω : (Fin (n + 1) → Real) → (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) (ha0 : a 0 = 0) :
    boxLowerZeroCoordFaceTerm (CubeStokes.toCoordNForm ω) a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b := by
  rw [boxLowerZeroCoordFaceTerm_eq_halfSpaceBoundaryCoordTerm _ _ _ ha0,
    halfSpaceBoundaryCoordTerm_toCoordNForm]

end Stokes

end
