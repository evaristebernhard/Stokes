import Stokes.SingularCube.SmoothExtensionMathlibAudit
import Mathlib.Topology.Compactness.Compact

/-!
# Compact cube-and-faces image package

This module records the compact set sampled by the smooth singular bridge:
the image of the parameter cube together with all high and low boundary-face
images.
-/

noncomputable section

open Set
open scoped Topology

namespace Stokes
namespace SingularCubeSmoothExtensionAudit

section CompactImages

variable {n m d : Nat}

/-- The singular parameter cube `[0,1]^d` is compact. -/
theorem singularParameterCube_isCompact (d : Nat) :
    IsCompact (singularParameterCube d) := by
  simpa [singularParameterCube] using
    (isCompact_Icc :
      IsCompact (Icc (fun _ : Fin d => (0 : Real)) (fun _ : Fin d => (1 : Real))))

/-- A smooth singular cube is continuous as a map between Euclidean coordinate spaces. -/
theorem smoothSingularCube_continuous (cube : SmoothSingularCube d m) :
    Continuous cube.toFun :=
  cube.smooth.continuous

/-- A smooth singular cube is continuous on its parameter cube. -/
theorem smoothSingularCube_continuousOn_parameterCube
    (cube : SmoothSingularCube d m) :
    ContinuousOn cube.toFun (singularParameterCube d) :=
  (smoothSingularCube_continuous cube).continuousOn

/-- The coordinate image of a smooth singular cube over `[0,1]^d` is compact. -/
theorem smoothSingularCube_image_isCompact
    (cube : SmoothSingularCube d m) :
    IsCompact (cube.toFun '' singularParameterCube d) :=
  (singularParameterCube_isCompact d).image (smoothSingularCube_continuous cube)

/-- Any fixed boundary face image of a smooth singular cube is compact. -/
theorem face_image_isCompact
    (cube : SmoothSingularCube (n + 1) m) (i : Fin (n + 1)) (epsilon : Real) :
    IsCompact ((singularFace cube i epsilon).toFun '' singularParameterCube n) :=
  smoothSingularCube_image_isCompact (singularFace cube i epsilon)

/-- High boundary-face images are compact. -/
theorem highFace_image_isCompact
    (cube : SmoothSingularCube (n + 1) m) (i : Fin (n + 1)) :
    IsCompact ((singularFace cube i 1).toFun '' singularParameterCube n) :=
  face_image_isCompact cube i 1

/-- Low boundary-face images are compact. -/
theorem lowFace_image_isCompact
    (cube : SmoothSingularCube (n + 1) m) (i : Fin (n + 1)) :
    IsCompact ((singularFace cube i 0).toFun '' singularParameterCube n) :=
  face_image_isCompact cube i 0

/-- The union of all high boundary-face images is compact. -/
theorem highFace_images_iUnion_isCompact
    (cube : SmoothSingularCube (n + 1) m) :
    IsCompact
      (⋃ i : Fin (n + 1), (singularFace cube i 1).toFun '' singularParameterCube n) :=
  isCompact_iUnion fun i => highFace_image_isCompact cube i

/-- The union of all low boundary-face images is compact. -/
theorem lowFace_images_iUnion_isCompact
    (cube : SmoothSingularCube (n + 1) m) :
    IsCompact
      (⋃ i : Fin (n + 1), (singularFace cube i 0).toFun '' singularParameterCube n) :=
  isCompact_iUnion fun i => lowFace_image_isCompact cube i

/-- The full image plus all high/low boundary-face images form a compact carrier. -/
theorem cubeAndFacesImage_isCompact
    (cube : SmoothSingularCube (n + 1) m) :
    IsCompact (cubeAndFacesImage cube) := by
  simpa [cubeAndFacesImage] using
    (smoothSingularCube_image_isCompact cube).union
      ((highFace_images_iUnion_isCompact cube).union
        (lowFace_images_iUnion_isCompact cube))

/-- The compact cube-and-faces carrier is closed in Euclidean coordinates. -/
theorem cubeAndFacesImage_isClosed
    (cube : SmoothSingularCube (n + 1) m) :
    IsClosed (cubeAndFacesImage cube) :=
  (cubeAndFacesImage_isCompact cube).isClosed

/-- A packaged compact carrier for the cutoff-extension step. -/
structure CubeAndFacesCompactData
    (cube : SmoothSingularCube (n + 1) m) where
  carrier : Set (Fin m → Real)
  carrier_eq : carrier = cubeAndFacesImage cube
  isCompact_carrier : IsCompact carrier
  cube_image_subset_carrier :
    cube.toFun '' singularParameterCube (n + 1) ⊆ carrier
  highFace_image_subset_carrier :
    ∀ i : Fin (n + 1),
      (singularFace cube i 1).toFun '' singularParameterCube n ⊆ carrier
  lowFace_image_subset_carrier :
    ∀ i : Fin (n + 1),
      (singularFace cube i 0).toFun '' singularParameterCube n ⊆ carrier

/-- The canonical compact carrier is exactly `cubeAndFacesImage cube`. -/
def cubeAndFacesCompactData
    (cube : SmoothSingularCube (n + 1) m) :
    CubeAndFacesCompactData cube where
  carrier := cubeAndFacesImage cube
  carrier_eq := rfl
  isCompact_carrier := cubeAndFacesImage_isCompact cube
  cube_image_subset_carrier := cube_image_subset_cubeAndFacesImage cube
  highFace_image_subset_carrier := highFace_image_subset_cubeAndFacesImage cube
  lowFace_image_subset_carrier := lowFace_image_subset_cubeAndFacesImage cube

namespace CubeAndFacesCompactData

variable {cube : SmoothSingularCube (n + 1) m}

/-- The packaged carrier lies in an open extension set exactly when the
canonical cube-and-faces image does. -/
theorem carrier_subset_iff
    (D : CubeAndFacesCompactData cube) {U : Set (Fin m → Real)} :
    D.carrier ⊆ U ↔ cubeAndFacesImage cube ⊆ U := by
  constructor
  · intro h x hx
    exact h (by simpa [D.carrier_eq] using hx)
  · intro h x hx
    exact h (by simpa [D.carrier_eq] using hx)

/-- The canonical package has the expected carrier. -/
@[simp]
theorem canonical_carrier
    (cube : SmoothSingularCube (n + 1) m) :
    (cubeAndFacesCompactData cube).carrier = cubeAndFacesImage cube :=
  rfl

/-- The canonical package exposes the compactness theorem. -/
theorem canonical_isCompact
    (cube : SmoothSingularCube (n + 1) m) :
    IsCompact (cubeAndFacesCompactData cube).carrier :=
  cubeAndFacesImage_isCompact cube

end CubeAndFacesCompactData

end CompactImages

end SingularCubeSmoothExtensionAudit
end Stokes
