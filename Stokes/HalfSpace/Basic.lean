import LeanStokes.CubeStokes.Bridge
import LeanStokes.CubeStokes.Unified
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Algebra.Support
import Stokes.ManifoldForm

/-!
# Half-Space Boundary Conventions

This module starts the local half-space layer needed for boundary Stokes.  The
analytic integration theorem is not here yet; this file fixes the coordinate
objects and signs that later local proofs will use.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

/-- The closed upper half-space in `R^(n+1)`, with boundary coordinate `0`. -/
def upperHalfSpace (n : Nat) : Set (Fin (n + 1) → Real) :=
  {x | 0 ≤ x 0}

/-- The boundary hyperplane of `upperHalfSpace n`. -/
def upperHalfSpaceBoundary (n : Nat) : Set (Fin (n + 1) → Real) :=
  {x | x 0 = 0}

/-- The interior of the upper half-space. -/
def upperHalfSpaceInterior (n : Nat) : Set (Fin (n + 1) → Real) :=
  {x | 0 < x 0}

/--
The coordinate inclusion of the boundary hyperplane into `R^(n+1)`.

The first coordinate is the boundary coordinate and is set to `0`; the remaining
coordinates are shifted by `Fin.succ`.
-/
def boundaryInclusion (n : Nat) (x : Fin n → Real) : Fin (n + 1) → Real :=
  Fin.cases 0 x

@[simp]
theorem boundaryInclusion_zero (n : Nat) (x : Fin n → Real) :
    boundaryInclusion n x 0 = 0 :=
  rfl

@[simp]
theorem boundaryInclusion_succ (n : Nat) (x : Fin n → Real) (i : Fin n) :
    boundaryInclusion n x i.succ = x i :=
  rfl

theorem range_boundaryInclusion (n : Nat) :
    range (boundaryInclusion n) = upperHalfSpaceBoundary n := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [upperHalfSpaceBoundary]
  · intro hy
    refine ⟨fun i => y i.succ, ?_⟩
    funext i
    refine Fin.cases ?_ ?_ i
    · simpa [boundaryInclusion, upperHalfSpaceBoundary] using hy.symm
    · intro i
      simp [boundaryInclusion]

theorem boundaryInclusion_injective (n : Nat) :
    Function.Injective (boundaryInclusion n) := by
  intro x y h
  funext i
  exact congrFun h i.succ

theorem boundaryInclusion_mem_upperHalfSpace (n : Nat) (x : Fin n → Real) :
    boundaryInclusion n x ∈ upperHalfSpace n := by
  simp [upperHalfSpace]

/-- The inward unit coordinate normal for the upper half-space `{x₀ ≥ 0}`. -/
def inwardNormal (n : Nat) : Fin (n + 1) → Real :=
  Pi.single 0 1

/-- The outward unit coordinate normal for the upper half-space `{x₀ ≥ 0}`. -/
def outwardNormal (n : Nat) : Fin (n + 1) → Real :=
  -inwardNormal n

@[simp]
theorem inwardNormal_zero (n : Nat) : inwardNormal n 0 = 1 := by
  simp [inwardNormal]

@[simp]
theorem inwardNormal_succ (n : Nat) (i : Fin n) : inwardNormal n i.succ = 0 := by
  simp [inwardNormal]

@[simp]
theorem outwardNormal_zero (n : Nat) : outwardNormal n 0 = -1 := by
  simp [outwardNormal]

@[simp]
theorem outwardNormal_succ (n : Nat) (i : Fin n) : outwardNormal n i.succ = 0 := by
  simp [outwardNormal]

/-- The `i`-th standard tangent vector of the boundary hyperplane. -/
def boundaryTangent (n : Nat) (i : Fin n) : Fin (n + 1) → Real :=
  Pi.single i.succ 1

@[simp]
theorem boundaryTangent_zero (n : Nat) (i : Fin n) : boundaryTangent n i 0 = 0 := by
  simp [boundaryTangent]

@[simp]
theorem boundaryTangent_succ (n : Nat) (i j : Fin n) :
    boundaryTangent n i j.succ = (Pi.single i (1 : Real) : Fin n → Real) j := by
  by_cases h : i = j
  · subst h
    simp [boundaryTangent]
  · simp [boundaryTangent, h]

/-- Boundary tangent-vector inclusion `R^n → R^(n+1)`, with zero normal component. -/
def boundaryTangentInclusion (n : Nat) :
    (Fin n → Real) →L[Real] (Fin (n + 1) → Real) where
  toFun := boundaryInclusion n
  map_add' x y := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [boundaryInclusion]
    · intro j
      simp [boundaryInclusion]
  map_smul' c x := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [boundaryInclusion]
    · intro j
      simp [boundaryInclusion]
  cont := by
    exact continuous_pi fun i => by
      refine Fin.cases ?_ ?_ i
      · exact continuous_const
      · intro j
        exact continuous_apply j

@[simp]
theorem boundaryTangentInclusion_apply (n : Nat) (x : Fin n → Real) :
    boundaryTangentInclusion n x = boundaryInclusion n x :=
  rfl

@[simp]
theorem boundaryTangentInclusion_basisFun (n : Nat) (i : Fin n) :
    boundaryTangentInclusion n ((Pi.basisFun Real (Fin n)) i) = boundaryTangent n i := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [boundaryTangentInclusion, boundaryInclusion, boundaryTangent]
  · intro k
    by_cases h : i = k
    · subst h
      simp [boundaryTangentInclusion, boundaryInclusion, boundaryTangent, Pi.basisFun_apply]
    · simp [boundaryTangentInclusion, boundaryInclusion, boundaryTangent, Pi.basisFun_apply, h]

/-- Projection from ambient coordinates to boundary tangent coordinates. -/
def boundaryTangentProjection (n : Nat) :
    (Fin (n + 1) → Real) →L[Real] (Fin n → Real) where
  toFun x i := x i.succ
  map_add' x y := by
    funext i
    simp
  map_smul' c x := by
    funext i
    simp
  cont := by
    exact continuous_pi fun i => continuous_apply i.succ

@[simp]
theorem boundaryTangentProjection_apply (n : Nat) (x : Fin (n + 1) → Real) :
    boundaryTangentProjection n x = fun i : Fin n => x i.succ :=
  rfl

/--
The frame obtained by putting the outward normal first and then the standard
boundary-coordinate tangent frame.
-/
def outwardFirstBoundaryFrame (n : Nat) : Fin (n + 1) → (Fin (n + 1) → Real) :=
  Fin.cases (outwardNormal n) (boundaryTangent n)

@[simp]
theorem outwardFirstBoundaryFrame_zero (n : Nat) :
    outwardFirstBoundaryFrame n 0 = outwardNormal n :=
  rfl

@[simp]
theorem outwardFirstBoundaryFrame_succ (n : Nat) (i : Fin n) :
    outwardFirstBoundaryFrame n i.succ = boundaryTangent n i :=
  rfl

/-- Matrix whose columns are the outward-first boundary frame vectors. -/
def outwardFirstBoundaryMatrix (n : Nat) : Matrix (Fin (n + 1)) (Fin (n + 1)) Real :=
  fun row col => outwardFirstBoundaryFrame n col row

theorem outwardFirstBoundaryMatrix_eq_diagonal (n : Nat) :
    outwardFirstBoundaryMatrix n =
      Matrix.diagonal (Fin.cases (-1 : Real) (fun _ : Fin n => (1 : Real))) := by
  ext row col
  refine Fin.cases ?_ ?_ col
  · refine Fin.cases ?_ ?_ row
    · simp [outwardFirstBoundaryMatrix, outwardFirstBoundaryFrame, outwardNormal, inwardNormal]
    · intro i
      simp [outwardFirstBoundaryMatrix, outwardFirstBoundaryFrame, outwardNormal, inwardNormal]
  · intro j
    refine Fin.cases ?_ ?_ row
    · have hz : (0 : Fin (n + 1)) ≠ j.succ := by
        intro h
        exact Fin.succ_ne_zero j h.symm
      simp [outwardFirstBoundaryMatrix, outwardFirstBoundaryFrame, boundaryTangent, hz]
    · intro i
      by_cases h : j = i
      · subst h
        simp [outwardFirstBoundaryMatrix, outwardFirstBoundaryFrame, boundaryTangent]
      · have hij : i ≠ j := fun hij => h hij.symm
        simp [outwardFirstBoundaryMatrix, outwardFirstBoundaryFrame, boundaryTangent, hij]

theorem det_outwardFirstBoundaryMatrix (n : Nat) :
    (outwardFirstBoundaryMatrix n).det = -1 := by
  rw [outwardFirstBoundaryMatrix_eq_diagonal, Matrix.det_diagonal]
  rw [Fin.prod_univ_succ]
  simp

/--
Matrix whose columns are the vectors of a coordinate frame.

This is the tiny finite-dimensional orientation API used in the local
half-space layer: relative to the standard coordinate orientation, a frame is
measured by the determinant of this matrix.
-/
def coordinateFrameMatrix {m : Nat} (frame : Fin m → (Fin m → Real)) :
    Matrix (Fin m) (Fin m) Real :=
  fun row col => frame col row

theorem coordinateFrameMatrix_linearMap_basisFun {m : Nat}
    (L : (Fin m → Real) →L[Real] (Fin m → Real)) :
    coordinateFrameMatrix (L ∘ Pi.basisFun Real (Fin m)) =
      LinearMap.toMatrix' (L : (Fin m → Real) →ₗ[Real] (Fin m → Real)) := by
  ext row col
  rw [LinearMap.toMatrix'_apply]
  simp [coordinateFrameMatrix]

/-- Determinant sign of a coordinate frame relative to the standard orientation. -/
def coordinateOrientationSign {m : Nat} (frame : Fin m → (Fin m → Real)) : Real :=
  (coordinateFrameMatrix frame).det

theorem outwardFirstBoundaryOrientationSign_eq_det (n : Nat) :
    coordinateOrientationSign (outwardFirstBoundaryFrame n) =
      (outwardFirstBoundaryMatrix n).det :=
  rfl

/--
The sign carried by the standard boundary tangent frame when the boundary
orientation is induced by the outward-normal-first convention.
-/
def outwardFirstBoundaryOrientationSign (n : Nat) : Real :=
  coordinateOrientationSign (outwardFirstBoundaryFrame n)

@[simp]
theorem outwardFirstBoundaryOrientationSign_eq (n : Nat) :
    outwardFirstBoundaryOrientationSign n = -1 := by
  simpa [outwardFirstBoundaryOrientationSign, outwardFirstBoundaryOrientationSign_eq_det]
    using det_outwardFirstBoundaryMatrix n

/-- The cubical sign of the upper face in coordinate `i`. -/
def upperFaceSign {n : Nat} (i : Fin (n + 1)) : Real :=
  (-1 : Real) ^ (i : Nat)

/-- The cubical sign of the lower face in coordinate `i`. -/
def lowerFaceSign {n : Nat} (i : Fin (n + 1)) : Real :=
  -((-1 : Real) ^ (i : Nat))

@[simp]
theorem upperFaceSign_zero (n : Nat) : upperFaceSign (0 : Fin (n + 1)) = 1 := by
  simp [upperFaceSign]

@[simp]
theorem lowerFaceSign_zero (n : Nat) : lowerFaceSign (0 : Fin (n + 1)) = -1 := by
  simp [lowerFaceSign]

/--
The half-space boundary `{x₀ = 0}` is the lower face in coordinate `0`, hence
its cubical/Stokes sign is `-1`.
-/
def halfSpaceBoundarySign (n : Nat) : Real :=
  lowerFaceSign (0 : Fin (n + 1))

@[simp]
theorem halfSpaceBoundarySign_eq (n : Nat) : halfSpaceBoundarySign n = -1 := by
  simp [halfSpaceBoundarySign]

/--
The lower-face sign used by the half-space Stokes theorem is exactly the sign
of the standard boundary tangent frame under the outward-normal-first boundary
orientation convention.
-/
theorem halfSpaceBoundarySign_eq_outwardFirstBoundaryOrientationSign (n : Nat) :
    halfSpaceBoundarySign n = outwardFirstBoundaryOrientationSign n := by
  simp

theorem insertNth_zero_eq_boundaryInclusion (n : Nat) (x : Fin n → Real) :
    Fin.insertNth (0 : Fin (n + 1)) (0 : Real) x = boundaryInclusion n x := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [boundaryInclusion]
  · intro i
    simp [boundaryInclusion]

theorem cons_zero_eq_boundaryInclusion (n : Nat) (x : Fin n → Real) :
    Fin.cons (0 : Real) x = boundaryInclusion n x := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [boundaryInclusion]
  · intro i
    simp [boundaryInclusion]

theorem zeroFaceBasis_eq_boundaryTangent (n : Nat) :
    (fun k : Fin n => Pi.single (Fin.succAbove (0 : Fin (n + 1)) k) (1 : Real)) =
      boundaryTangent n := by
  funext k x
  simp [boundaryTangent]

theorem zeroFaceBasis_succ_eq_boundaryTangent (n : Nat) :
    (fun k : Fin n => Pi.single k.succ (1 : Real)) = boundaryTangent n := by
  funext k x
  simp [boundaryTangent]


end Stokes

end
