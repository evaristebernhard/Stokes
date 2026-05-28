import LeanStokes.CubeStokes.Theorem
import LeanStokes.CubeStokes.Unified

/-!
# Euclidean Box Stokes Baseline

This module exposes the first project-level Stokes baseline under the `Stokes`
namespace. The proofs are currently thin wrappers around the cloned LeanStokes
artifact, which itself reduces box Stokes to mathlib's divergence theorem and
bridges coordinate forms to mathlib's `extDeriv`.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace Stokes

variable {n : Nat}

/-- Coordinate `n`-forms on `R^(n+1)`, re-exported from the upstream box layer. -/
abbrev CoordNForm (n : Nat) := CubeStokes.CoordNForm n

/-- Coordinate exterior derivative, re-exported from the upstream box layer. -/
abbrev extDerivCoord {n : Nat} : CoordNForm n -> (Fin (n + 1) -> Real) -> Real :=
  CubeStokes.extDerivCoord

/-- Integral over an axis-aligned box, re-exported from the upstream box layer. -/
abbrev boxIntegral {n : Nat} :
    ((Fin (n + 1) -> Real) -> Real) -> (Fin (n + 1) -> Real) ->
      (Fin (n + 1) -> Real) -> Real :=
  CubeStokes.boxIntegral

/-- Boundary integral over an axis-aligned box, re-exported from the upstream box layer. -/
abbrev bdryIntegral {n : Nat} :
    CoordNForm n -> (Fin (n + 1) -> Real) -> (Fin (n + 1) -> Real) -> Real :=
  CubeStokes.bdryIntegral

/--
Stokes' theorem on an axis-aligned box for coordinate forms.

This is the low-level version with explicit continuity, differentiability,
countable exceptional-set, and integrability hypotheses. It is a direct wrapper
around `CubeStokes.stokes_on_box`, whose proof calls mathlib's box divergence
theorem.
-/
theorem box_stokes_on_box (a b : Fin (n + 1) -> Real) (hle : a <= b)
    (omega : CoordNForm n)
    (s : Set (Fin (n + 1) -> Real)) (hs : s.Countable)
    (hc : ∀ i, ContinuousOn (CubeStokes.signedCoeff omega i) (Icc a b))
    (hd : ∀ x ∈ (pi univ fun i => Ioo (a i) (b i)) \ s,
      ∀ i, HasFDerivAt (CubeStokes.signedCoeff omega i)
        ((-1 : Real) ^ (i : Nat) • fderiv Real (omega i) x) x)
    (hi : IntegrableOn (fun x => ∑ i : Fin (n + 1),
      ((-1 : Real) ^ (i : Nat) • fderiv Real (omega i) x) (Pi.single i 1)) (Icc a b)) :
    boxIntegral (CubeStokes.extDerivCoord omega) a b = bdryIntegral omega a b :=
  CubeStokes.stokes_on_box a b hle omega s hs hc hd hi

/--
Stokes' theorem on a box for mathlib differential forms.

This is the clean M1 theorem: for a globally smooth mathlib `n`-form on
`R^(n+1)`, integrating `extDeriv omega` on the standard frame over a box equals
the coordinate boundary integral.
-/
theorem box_stokes_extDeriv_smooth
    (omega : (Fin (n + 1) -> Real) ->
      (Fin (n + 1) -> Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) -> Real) (hle : a <= b)
    (homega : ContDiff Real ⊤ omega) :
    (∫ x in Icc a b, extDeriv omega x (fun j => Pi.single j 1)) =
    CubeStokes.bdryIntegral (CubeStokes.toCoordNForm omega) a b :=
  CubeStokes.stokes_extDeriv_smooth omega a b hle homega

end Stokes

end
