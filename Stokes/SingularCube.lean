import LeanStokes.SingularCubeStokes.BdryBdry

/-!
# Smooth Singular Cube Stokes

This module exposes the smooth singular cubical layer under the `Stokes`
namespace. The public statements keep the form argument in mathlib's
`ContinuousAlternatingMap` representation and use mathlib's `extDeriv`.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace Stokes

variable {n m : Nat}

/-- A smooth singular `n`-cube in `R^m`. -/
abbrev SmoothSingularCube (n m : Nat) :=
  SingularCubeStokes.SmoothSingularCube n m

/-- A mathlib `k`-form on `R^m`. -/
abbrev EuclideanForm (m k : Nat) :=
  (Fin m -> Real) -> (Fin m -> Real) [⋀^Fin k]→L[Real] Real

/-- Pullback of a form along a smooth singular cube, using the Frechet derivative. -/
abbrev pullbackForm {d m k : Nat} (sigma : SmoothSingularCube d m)
    (omega : EuclideanForm m k) :
    (Fin d -> Real) -> (Fin d -> Real) [⋀^Fin k]→L[Real] Real :=
  SingularCubeStokes.pullbackForm sigma omega

/-- Integration of a top-degree form over a smooth singular cube. -/
abbrev integrateForm {d m : Nat} (sigma : SmoothSingularCube d m)
    (omega : EuclideanForm m d) : Real :=
  SingularCubeStokes.integrateForm sigma omega

/-- The `i`-th face of a smooth singular cube. -/
abbrev singularFace (sigma : SmoothSingularCube (n + 1) m)
    (i : Fin (n + 1)) (epsilon : Real) : SmoothSingularCube n m :=
  SingularCubeStokes.singularFace sigma i epsilon

/-- A finite integer linear combination of smooth singular cubes. -/
abbrev SingularChain (n m : Nat) :=
  SingularCubeStokes.SingularChain n m

/-- Boundary of one smooth singular cube as a finite chain. -/
abbrev singularBoundarySingle (sigma : SmoothSingularCube (n + 1) m) :
    SingularChain n m :=
  SingularCubeStokes.singularBoundarySingle sigma

/-- Boundary operator on finite smooth singular cubical chains. -/
abbrev singularBoundary (c : SingularChain (n + 1) m) : SingularChain n m :=
  SingularCubeStokes.singularBoundary c

/-- Integration of a form over a finite smooth singular cubical chain. -/
abbrev integrateChain (c : SingularChain n m) (omega : EuclideanForm m n) : Real :=
  SingularCubeStokes.integrateChain c omega

/--
Naturality of pullback for the exterior derivative:
`d(sigma^* omega) = sigma^*(d omega)`.
-/
theorem singular_pullback_extDeriv (sigma : SmoothSingularCube (n + 1) m)
    (omega : EuclideanForm m n) (homega : ContDiff Real ⊤ omega)
    (x : Fin (n + 1) -> Real) :
    extDeriv (pullbackForm sigma omega) x =
    (extDeriv omega (sigma.toFun x)).compContinuousLinearMap
      (fderiv Real sigma.toFun x) :=
  SingularCubeStokes.pullback_extDeriv sigma omega homega x

/--
Stokes' theorem for one smooth singular cube:
the integral of `sigma^*(d omega)` over the unit cube is the alternating sum of
the integrals of `omega` over the faces.
-/
theorem singular_cube_stokes (sigma : SmoothSingularCube (n + 1) m)
    (omega : EuclideanForm m n) (homega : ContDiff Real ⊤ omega) :
    integrateForm sigma (fun y => extDeriv omega y) =
    ∑ i : Fin (n + 1),
      (-1 : Real) ^ (i : Nat) *
      (integrateForm (singularFace sigma i 1) omega -
       integrateForm (singularFace sigma i 0) omega) :=
  SingularCubeStokes.singularStokes sigma omega homega

/--
Boundary-integral form of smooth singular cube Stokes:
integrating `omega` over the oriented boundary equals integrating `d omega`
over the cube.
-/
theorem singular_cube_boundary_stokes (sigma : SmoothSingularCube (n + 1) m)
    (omega : EuclideanForm m n) (homega : ContDiff Real ⊤ omega) :
    SingularCubeStokes.bdryIntegral_singular sigma omega =
    integrateForm sigma (fun y => extDeriv omega y) :=
  SingularCubeStokes.stokes_singular_boundary sigma omega homega

/--
Chain-level Stokes for a single smooth singular cube:
integrating over the boundary chain equals integrating `d omega` over the cube.
-/
theorem singular_cube_chain_stokes (sigma : SmoothSingularCube (n + 1) m)
    (omega : EuclideanForm m n) (homega : ContDiff Real ⊤ omega) :
    integrateChain (singularBoundarySingle sigma) omega =
    integrateForm sigma (fun y => extDeriv omega y) :=
  SingularCubeStokes.stokes_singular_chain sigma omega homega

/--
Chain-level Stokes for finite smooth singular cubical chains.
-/
theorem singular_chain_stokes (c : SingularChain (n + 1) m)
    (omega : EuclideanForm m n) (homega : ContDiff Real ⊤ omega) :
    integrateChain (singularBoundary c) omega =
    integrateChain c (fun y => extDeriv omega y) :=
  SingularCubeStokes.stokes_chain c omega homega

/-- The boundary of the boundary of one smooth singular cube is zero. -/
theorem singular_boundary_boundary_zero (sigma : SmoothSingularCube (n + 2) m) :
    singularBoundary (singularBoundarySingle sigma) = 0 :=
  SingularCubeStokes.bdry_bdry_chain_zero sigma

/-- The boundary operator squares to zero on finite smooth singular cubical chains. -/
theorem singular_boundary_boundary_zero_general (c : SingularChain (n + 2) m) :
    singularBoundary (singularBoundary c) = 0 :=
  SingularCubeStokes.bdry_bdry_chain_zero_general c

end Stokes

end
