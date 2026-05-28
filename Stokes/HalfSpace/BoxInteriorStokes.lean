import Stokes.HalfSpace.LocalStokes

/-!
# Half-space local Stokes from interior box fields

This module separates the genuinely Euclidean box-Stokes input from the
stronger "smooth on an ambient open neighborhood of the closed box" wrapper in
`Stokes.HalfSpace.LocalStokes`.

For a boundary chart, the closed half-space box may touch the model boundary,
so the downstream manifold layer should not be forced to manufacture an
ambient-open set contained in a chart target.  The record below stores exactly
the data needed to apply `CubeStokes.stokes_on_box`, plus the remaining bridge
from the mathlib `extDeriv` integrand to the coordinate divergence integrand.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

/--
Interior-box data sufficient to run the Euclidean box Stokes theorem for a
half-space local representative.

The fields `continuous_signedCoeff`, `hasFDerivAt_signedCoeff`, and
`integrable_divergence` are precisely the hypotheses consumed by
`CubeStokes.stokes_on_box`.  The field `bulk_eq_boxIntegral` is the only bridge
which still mentions the mathlib `extDeriv` integrand; later manifold wrappers
can prove it by an a.e. equality on the closed box, without requiring ambient
smoothness at boundary points.
-/
structure HalfSpaceBoxInteriorStokesFields {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) where
  /-- The lower corner is componentwise below the upper corner. -/
  le : a ≤ b
  /-- The lower normal coordinate is the half-space boundary face. -/
  lower_zero : a 0 = 0
  /-- Exceptional set where the coordinate functions need not be differentiable. -/
  exceptional : Set (Fin (n + 1) → Real)
  /-- The exceptional set is countable, as in mathlib's box divergence theorem. -/
  exceptional_countable : exceptional.Countable
  /-- Signed coordinate coefficients are continuous on the closed box. -/
  continuous_signedCoeff :
    ∀ i : Fin (n + 1),
      ContinuousOn (CubeStokes.signedCoeff (CubeStokes.toCoordNForm ω) i) (Icc a b)
  /-- The signed coordinate coefficients have the expected Frechet derivative
  on the box interior, away from the exceptional set. -/
  hasFDerivAt_signedCoeff :
    ∀ x ∈ (pi univ fun i : Fin (n + 1) => Ioo (a i) (b i)) \ exceptional,
      ∀ i : Fin (n + 1),
        HasFDerivAt (CubeStokes.signedCoeff (CubeStokes.toCoordNForm ω) i)
          ((-1 : Real) ^ (i : Nat) •
            fderiv Real (CubeStokes.toCoordNForm ω i) x) x
  /-- The coordinate divergence integrand is integrable on the closed box. -/
  integrable_divergence :
    IntegrableOn
      (fun x => ∑ i : Fin (n + 1),
        ((-1 : Real) ^ (i : Nat) •
          fderiv Real (CubeStokes.toCoordNForm ω i) x) (Pi.single i 1))
      (Icc a b)
  /-- The mathlib `extDeriv` top coefficient has the same closed-box integral
  as the coordinate divergence integrand used by `CubeStokes.stokes_on_box`. -/
  bulk_eq_boxIntegral :
    halfSpaceLocalBulkIntegral ω a b =
      CubeStokes.boxIntegral (CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω)) a b

namespace HalfSpaceBoxInteriorStokesFields

variable {n : Nat}
variable
    {ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real}
    {a b : Fin (n + 1) → Real}

/-- The underlying Euclidean box Stokes identity supplied by the interior
fields. -/
theorem boxStokes (D : HalfSpaceBoxInteriorStokesFields ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      CubeStokes.bdryIntegral (CubeStokes.toCoordNForm ω) a b := by
  rw [D.bulk_eq_boxIntegral]
  exact
    CubeStokes.stokes_on_box a b D.le (CubeStokes.toCoordNForm ω)
      D.exceptional D.exceptional_countable D.continuous_signedCoeff
      D.hasFDerivAt_signedCoeff D.integrable_divergence

/-- Half-space Stokes with the artificial-face remainder, using only the
interior-box fields. -/
theorem withRemainder (D : HalfSpaceBoxInteriorStokesFields ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b +
        halfSpaceLocalBoundaryRemainder ω a b := by
  unfold halfSpaceLocalBoundaryRemainder
  rw [D.boxStokes]
  rw [bdryIntegral_eq_lowerZero_add_remaining]
  rw [boxLowerZeroCoordFaceTerm_toCoordNForm_eq_halfSpaceBoundaryFormTerm _ _ _ D.lower_zero]
  rw [boxRemainingCoordFaceTerms_toCoordNForm]

/-- Compact-support half-space Stokes from interior-box fields and the standard
support condition killing artificial faces. -/
theorem compactSupport
    (D : HalfSpaceBoxInteriorStokesFields ω a b)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b := by
  rw [D.withRemainder,
    halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox
      ω a b hsupp, add_zero]

end HalfSpaceBoxInteriorStokesFields

/-- Public spelling of compact-support local half-space Stokes from interior
box fields. -/
theorem halfSpaceLocalStokes_compactSupport_of_interiorFields {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (D : HalfSpaceBoxInteriorStokesFields ω a b)
    (hsupp : boxFaceCoeffTSupportInHalfSpaceBox ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b :=
  D.compactSupport hsupp

/-- Public spelling of the remainder version from interior box fields. -/
theorem halfSpaceLocalStokes_with_remainder_of_interiorFields {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (D : HalfSpaceBoxInteriorStokesFields ω a b) :
    halfSpaceLocalBulkIntegral ω a b =
      halfSpaceBoundarySign n * halfSpaceBoundaryFormIntegral ω a b +
        halfSpaceLocalBoundaryRemainder ω a b :=
  D.withRemainder

end Stokes

end
