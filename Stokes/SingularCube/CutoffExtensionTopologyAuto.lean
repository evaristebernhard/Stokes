import Stokes.SingularCube.CubeAndFacesCompactAuto
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Topological neighborhood packages for singular-cube cutoff extension

This module supplies the purely topological part of the smooth singular-cube
cutoff-extension step.  The central carrier is the compact image consisting of
the cube together with all of its high and low faces.

The results here deliberately stop before constructing a smooth cutoff.  They
turn the common hypothesis

```
cubeAndFacesImage cube ⊆ U,  IsOpen U
```

into theorem-facing neighborhood, finite-subcover, and open-shrink packages.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Stokes
namespace SingularCubeSmoothExtensionAudit

section GeneralCompactCarrier

variable {X : Type*} [TopologicalSpace X]
variable {K U V : Set X}

/-- An open neighborhood of a compact carrier, packaged with its `nhdsSet`
membership. -/
structure CompactCarrierOpenNeighborhood (K : Set X) where
  openSet : Set X
  isOpen_openSet : IsOpen openSet
  carrier_subset_openSet : K ⊆ openSet

namespace CompactCarrierOpenNeighborhood

variable {K : Set X}

/-- The packaged open neighborhood belongs to the set-neighborhood filter of
the carrier. -/
theorem mem_nhdsSet (N : CompactCarrierOpenNeighborhood K) :
    N.openSet ∈ 𝓝ˢ K :=
  N.isOpen_openSet.mem_nhdsSet.2 N.carrier_subset_openSet

/-- Pointwise neighborhood form of the packaged set-neighborhood statement. -/
theorem mem_nhds_at (N : CompactCarrierOpenNeighborhood K) {x : X}
    (hx : x ∈ K) :
    N.openSet ∈ 𝓝 x :=
  mem_nhdsSet_iff_forall.1 N.mem_nhdsSet x hx

/-- Membership in the packaged open set for each carrier point. -/
theorem mem_openSet (N : CompactCarrierOpenNeighborhood K) {x : X}
    (hx : x ∈ K) :
    x ∈ N.openSet :=
  N.carrier_subset_openSet hx

/-- The carrier is contained in the interior of the packaged open set. -/
theorem carrier_subset_interior (N : CompactCarrierOpenNeighborhood K) :
    K ⊆ interior N.openSet :=
  subset_interior_iff_mem_nhdsSet.2 N.mem_nhdsSet

/-- Eventual form over the carrier neighborhood filter. -/
theorem eventually_mem (N : CompactCarrierOpenNeighborhood K) :
    (∀ᶠ x in 𝓝ˢ K, x ∈ N.openSet) :=
  N.mem_nhdsSet

@[simp]
theorem eventually_mem_iff (N : CompactCarrierOpenNeighborhood K) :
    (∀ᶠ x in 𝓝ˢ K, x ∈ N.openSet) :=
  N.eventually_mem

end CompactCarrierOpenNeighborhood

/-- Build a compact-carrier open-neighborhood package from an open set
containing the carrier. -/
def compactCarrierOpenNeighborhoodOfSubset
    (hUo : IsOpen U) (hKU : K ⊆ U) :
    CompactCarrierOpenNeighborhood K where
  openSet := U
  isOpen_openSet := hUo
  carrier_subset_openSet := hKU

@[simp]
theorem compactCarrierOpenNeighborhoodOfSubset_openSet
    (hUo : IsOpen U) (hKU : K ⊆ U) :
    (compactCarrierOpenNeighborhoodOfSubset (K := K) hUo hKU).openSet = U :=
  rfl

/-- An open set containing a carrier is a set-neighborhood of that carrier. -/
theorem mem_nhdsSet_of_isOpen_of_subset
    (hUo : IsOpen U) (hKU : K ⊆ U) :
    U ∈ 𝓝ˢ K :=
  hUo.mem_nhdsSet.2 hKU

/-- Pointwise neighborhood form for an open set containing a carrier. -/
theorem mem_nhds_of_isOpen_of_subset
    (hUo : IsOpen U) (hKU : K ⊆ U) {x : X} (hx : x ∈ K) :
    U ∈ 𝓝 x :=
  mem_nhdsSet_iff_forall.1 (mem_nhdsSet_of_isOpen_of_subset hUo hKU) x hx

/-- Eventual membership on the carrier neighborhood filter for an open
neighborhood of the carrier. -/
theorem eventually_mem_of_isOpen_of_subset
    (hUo : IsOpen U) (hKU : K ⊆ U) :
    (∀ᶠ x in 𝓝ˢ K, x ∈ U) :=
  mem_nhdsSet_of_isOpen_of_subset hUo hKU

/-- A finite open subcover of a compact carrier, as produced by compactness. -/
structure CompactCarrierFiniteOpenSubcover
    (K : Set X) {ι : Type*} (W : ι → Set X) where
  indices : Finset ι
  carrier_subset_iUnion :
    K ⊆ ⋃ i ∈ indices, W i

namespace CompactCarrierFiniteOpenSubcover

variable {K : Set X} {ι : Type*} {W : ι → Set X}

/-- The finite union selected by a finite subcover package. -/
def union (C : CompactCarrierFiniteOpenSubcover K W) : Set X :=
  ⋃ i ∈ C.indices, W i

omit [TopologicalSpace X] in
theorem carrier_subset_union (C : CompactCarrierFiniteOpenSubcover K W) :
    K ⊆ C.union := by
  simpa [union] using C.carrier_subset_iUnion

theorem union_isOpen (C : CompactCarrierFiniteOpenSubcover K W)
    (hWo : ∀ i, IsOpen (W i)) :
    IsOpen C.union := by
  classical
  simpa [union] using isOpen_biUnion fun i _ => hWo i

theorem union_mem_nhdsSet (C : CompactCarrierFiniteOpenSubcover K W)
    (hWo : ∀ i, IsOpen (W i)) :
    C.union ∈ 𝓝ˢ K :=
  (C.union_isOpen hWo).mem_nhdsSet.2 C.carrier_subset_union

theorem union_eventually_mem (C : CompactCarrierFiniteOpenSubcover K W)
    (hWo : ∀ i, IsOpen (W i)) :
    (∀ᶠ x in 𝓝ˢ K, x ∈ C.union) :=
  C.union_mem_nhdsSet hWo

end CompactCarrierFiniteOpenSubcover

/-- Compactness turns an open cover of a compact carrier into a finite
subcover package. -/
theorem exists_compactCarrierFiniteOpenSubcover
    (hK : IsCompact K) {ι : Type*} {W : ι → Set X}
    (hWo : ∀ i, IsOpen (W i)) (hKW : K ⊆ ⋃ i, W i) :
    ∃ _ : CompactCarrierFiniteOpenSubcover K W, True := by
  rcases hK.elim_finite_subcover W hWo hKW with ⟨t, ht⟩
  exact ⟨{ indices := t, carrier_subset_iUnion := ht }, trivial⟩

/-- Direct finite-subcover theorem, with the package projected away. -/
theorem exists_finite_open_subcover
    (hK : IsCompact K) {ι : Type*} {W : ι → Set X}
    (hWo : ∀ i, IsOpen (W i)) (hKW : K ⊆ ⋃ i, W i) :
    ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, W i :=
  hK.elim_finite_subcover W hWo hKW

/-- A finite neighborhood subcover of a compact carrier.  The selected centers
remain points of the carrier, and the finite union is a set-neighborhood of the
carrier. -/
structure CompactCarrierFiniteNhdsSubcover
    (K : Set X) (N : X → Set X) where
  centers : Finset X
  centers_subset_carrier : ∀ x ∈ centers, x ∈ K
  union_mem_nhdsSet : (⋃ x ∈ centers, N x) ∈ 𝓝ˢ K

namespace CompactCarrierFiniteNhdsSubcover

variable {K : Set X} {N : X → Set X}

/-- The finite union selected by a neighborhood-subcover package. -/
def union (C : CompactCarrierFiniteNhdsSubcover K N) : Set X :=
  ⋃ x ∈ C.centers, N x

theorem union_mem (C : CompactCarrierFiniteNhdsSubcover K N) :
    C.union ∈ 𝓝ˢ K := by
  simpa [union] using C.union_mem_nhdsSet

theorem carrier_subset_union (C : CompactCarrierFiniteNhdsSubcover K N) :
    K ⊆ C.union :=
  subset_of_mem_nhdsSet C.union_mem

theorem union_isOpen (C : CompactCarrierFiniteNhdsSubcover K N)
    (hNo : ∀ x ∈ K, IsOpen (N x)) :
    IsOpen C.union := by
  classical
  simpa [union] using
    isOpen_biUnion fun x hx => hNo x (C.centers_subset_carrier x hx)

def union_open_neighborhood (C : CompactCarrierFiniteNhdsSubcover K N)
    (hNo : ∀ x ∈ K, IsOpen (N x)) :
    CompactCarrierOpenNeighborhood K where
  openSet := C.union
  isOpen_openSet := C.union_isOpen hNo
  carrier_subset_openSet := C.carrier_subset_union

end CompactCarrierFiniteNhdsSubcover

/-- Compactness turns pointwise neighborhoods of a compact carrier into one
finite neighborhood-union set-neighborhood. -/
theorem exists_compactCarrierFiniteNhdsSubcover
    (hK : IsCompact K) {N : X → Set X}
    (hN : ∀ x ∈ K, N x ∈ 𝓝 x) :
    ∃ _ : CompactCarrierFiniteNhdsSubcover K N, True := by
  rcases hK.elim_nhds_subcover_nhdsSet hN with ⟨t, htK, ht⟩
  refine ⟨?_, trivial⟩
  refine ⟨t, htK, ht⟩

/-- Direct finite-neighborhood-subcover theorem, with the package projected
away. -/
theorem exists_finite_nhds_subcover_mem_nhdsSet
    (hK : IsCompact K) {N : X → Set X}
    (hN : ∀ x ∈ K, N x ∈ 𝓝 x) :
    ∃ t : Finset X,
      (∀ x ∈ t, x ∈ K) ∧ (⋃ x ∈ t, N x) ∈ 𝓝ˢ K :=
  hK.elim_nhds_subcover_nhdsSet hN

/-- An open shrink of a carrier inside an outer set, with closure controlled by
the outer set. -/
structure CompactCarrierOpenShrink (K U : Set X) where
  shrink : Set X
  isOpen_shrink : IsOpen shrink
  carrier_subset_shrink : K ⊆ shrink
  closure_shrink_subset_outer : closure shrink ⊆ U

namespace CompactCarrierOpenShrink

variable {K U : Set X}

theorem shrink_mem_nhdsSet (S : CompactCarrierOpenShrink K U) :
    S.shrink ∈ 𝓝ˢ K :=
  S.isOpen_shrink.mem_nhdsSet.2 S.carrier_subset_shrink

def shrink_open_neighborhood (S : CompactCarrierOpenShrink K U) :
    CompactCarrierOpenNeighborhood K where
  openSet := S.shrink
  isOpen_openSet := S.isOpen_shrink
  carrier_subset_openSet := S.carrier_subset_shrink

theorem shrink_subset_outer (S : CompactCarrierOpenShrink K U) :
    S.shrink ⊆ U :=
  subset_closure.trans S.closure_shrink_subset_outer

theorem carrier_subset_outer (S : CompactCarrierOpenShrink K U) :
    K ⊆ U :=
  S.carrier_subset_shrink.trans S.shrink_subset_outer

theorem closure_eventually_mem_outer (S : CompactCarrierOpenShrink K U) :
    closure S.shrink ⊆ U :=
  S.closure_shrink_subset_outer

theorem shrink_eventually_mem (S : CompactCarrierOpenShrink K U) :
    (∀ᶠ x in 𝓝ˢ K, x ∈ S.shrink) :=
  S.shrink_mem_nhdsSet

end CompactCarrierOpenShrink

/-- In a regular space, a compact carrier with a set-neighborhood `U` admits an
open shrink whose closure lies in `U`. -/
theorem exists_compactCarrierOpenShrink_of_mem_nhdsSet
    [RegularSpace X] (hK : IsCompact K) (hU : U ∈ 𝓝ˢ K) :
    ∃ _ : CompactCarrierOpenShrink K U, True := by
  rcases hK.exists_isOpen_closure_subset hU with ⟨V, hVo, hKV, hVU⟩
  refine ⟨?_, trivial⟩
  refine ⟨V, hVo, hKV, hVU⟩

/-- In a regular space, a compact carrier contained in an open set admits an
open shrink whose closure lies in the open set. -/
theorem exists_compactCarrierOpenShrink_of_isOpen_of_subset
    [RegularSpace X] (hK : IsCompact K)
    (hUo : IsOpen U) (hKU : K ⊆ U) :
    ∃ _ : CompactCarrierOpenShrink K U, True :=
  exists_compactCarrierOpenShrink_of_mem_nhdsSet hK
    (mem_nhdsSet_of_isOpen_of_subset hUo hKU)

/-- Projection form of `exists_compactCarrierOpenShrink_of_isOpen_of_subset`. -/
theorem exists_open_closure_subset_of_compact_subset_open
    [RegularSpace X] (hK : IsCompact K)
    (hUo : IsOpen U) (hKU : K ⊆ U) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U := by
  rcases exists_compactCarrierOpenShrink_of_isOpen_of_subset hK hUo hKU with
    ⟨S, _⟩
  exact ⟨S.shrink, S.isOpen_shrink, S.carrier_subset_shrink,
    S.closure_shrink_subset_outer⟩

end GeneralCompactCarrier

section CubeAndFacesTopology

variable {n m : Nat}
variable {cube : SmoothSingularCube (n + 1) m}
variable {U : Set (Fin m → Real)}

/-- An open set containing the cube-and-faces image is a set-neighborhood of
that image. -/
theorem cubeAndFacesImage_mem_nhdsSet_of_isOpen_of_subset
    (hUo : IsOpen U) (hU : cubeAndFacesImage cube ⊆ U) :
    U ∈ 𝓝ˢ (cubeAndFacesImage cube) :=
  mem_nhdsSet_of_isOpen_of_subset hUo hU

/-- Pointwise neighborhood statement for the cube-and-faces image. -/
theorem cubeAndFacesImage_mem_nhds_of_isOpen_of_subset
    (hUo : IsOpen U) (hU : cubeAndFacesImage cube ⊆ U)
    {x : Fin m → Real} (hx : x ∈ cubeAndFacesImage cube) :
    U ∈ 𝓝 x :=
  mem_nhds_of_isOpen_of_subset hUo hU hx

/-- Eventual membership in an open set around the cube-and-faces image. -/
theorem cubeAndFacesImage_eventually_mem_of_isOpen_of_subset
    (hUo : IsOpen U) (hU : cubeAndFacesImage cube ⊆ U) :
    (∀ᶠ x in 𝓝ˢ (cubeAndFacesImage cube), x ∈ U) :=
  eventually_mem_of_isOpen_of_subset hUo hU

/-- The canonical open-neighborhood package for a cube-and-faces image. -/
def cubeAndFacesImageOpenNeighborhood
    (hUo : IsOpen U) (hU : cubeAndFacesImage cube ⊆ U) :
    CompactCarrierOpenNeighborhood (cubeAndFacesImage cube) :=
  compactCarrierOpenNeighborhoodOfSubset hUo hU

@[simp]
theorem cubeAndFacesImageOpenNeighborhood_openSet
    (hUo : IsOpen U) (hU : cubeAndFacesImage cube ⊆ U) :
    (cubeAndFacesImageOpenNeighborhood (cube := cube) hUo hU).openSet = U :=
  rfl

/-- Finite open-subcover package for any open cover of the cube-and-faces
image. -/
theorem exists_cubeAndFacesImageFiniteOpenSubcover
    {ι : Type*} {W : ι → Set (Fin m → Real)}
    (hWo : ∀ i, IsOpen (W i))
    (hW : cubeAndFacesImage cube ⊆ ⋃ i, W i) :
    ∃ _ : CompactCarrierFiniteOpenSubcover (cubeAndFacesImage cube) W, True :=
  exists_compactCarrierFiniteOpenSubcover
    (cubeAndFacesImage_isCompact cube) hWo hW

/-- Direct finite open-subcover theorem for the cube-and-faces image. -/
theorem exists_cubeAndFacesImage_finite_open_subcover
    {ι : Type*} {W : ι → Set (Fin m → Real)}
    (hWo : ∀ i, IsOpen (W i))
    (hW : cubeAndFacesImage cube ⊆ ⋃ i, W i) :
    ∃ t : Finset ι, cubeAndFacesImage cube ⊆ ⋃ i ∈ t, W i :=
  exists_finite_open_subcover (cubeAndFacesImage_isCompact cube) hWo hW

/-- Finite pointwise-neighborhood subcover package for the cube-and-faces
image. -/
theorem exists_cubeAndFacesImageFiniteNhdsSubcover
    {N : (Fin m → Real) → Set (Fin m → Real)}
    (hN : ∀ x ∈ cubeAndFacesImage cube, N x ∈ 𝓝 x) :
    ∃ _ : CompactCarrierFiniteNhdsSubcover (cubeAndFacesImage cube) N, True :=
  exists_compactCarrierFiniteNhdsSubcover
    (cubeAndFacesImage_isCompact cube) hN

/-- Direct finite pointwise-neighborhood subcover theorem for the
cube-and-faces image. -/
theorem exists_cubeAndFacesImage_finite_nhds_subcover_mem_nhdsSet
    {N : (Fin m → Real) → Set (Fin m → Real)}
    (hN : ∀ x ∈ cubeAndFacesImage cube, N x ∈ 𝓝 x) :
    ∃ t : Finset (Fin m → Real),
      (∀ x ∈ t, x ∈ cubeAndFacesImage cube) ∧
        (⋃ x ∈ t, N x) ∈ 𝓝ˢ (cubeAndFacesImage cube) :=
  exists_finite_nhds_subcover_mem_nhdsSet
    (cubeAndFacesImage_isCompact cube) hN

/-- Open shrink of an open set containing the cube-and-faces image, with
closure still lying in the original open set. -/
theorem exists_cubeAndFacesImageOpenShrink
    (hUo : IsOpen U) (hU : cubeAndFacesImage cube ⊆ U) :
    ∃ _ : CompactCarrierOpenShrink (cubeAndFacesImage cube) U, True :=
  exists_compactCarrierOpenShrink_of_isOpen_of_subset
    (cubeAndFacesImage_isCompact cube) hUo hU

/-- Projection form of the cube-and-faces open-shrink theorem. -/
theorem exists_cubeAndFacesImage_open_closure_subset
    (hUo : IsOpen U) (hU : cubeAndFacesImage cube ⊆ U) :
    ∃ V : Set (Fin m → Real),
      IsOpen V ∧ cubeAndFacesImage cube ⊆ V ∧ closure V ⊆ U :=
  exists_open_closure_subset_of_compact_subset_open
    (cubeAndFacesImage_isCompact cube) hUo hU

/-- Open-shrink membership wrapper: the shrink is a set-neighborhood of the
cube-and-faces image. -/
theorem cubeAndFacesImage_openShrink_mem_nhdsSet
    {S : CompactCarrierOpenShrink (cubeAndFacesImage cube) U} :
    S.shrink ∈ 𝓝ˢ (cubeAndFacesImage cube) :=
  S.shrink_mem_nhdsSet

end CubeAndFacesTopology

namespace CubeAndFacesCompactData

variable {n m : Nat}
variable {cube : SmoothSingularCube (n + 1) m}
variable (D : CubeAndFacesCompactData cube)
variable {U : Set (Fin m → Real)}

/-- A packaged carrier inside an open set gives a set-neighborhood of the
packaged carrier. -/
theorem mem_nhdsSet_of_isOpen_of_subset
    (hUo : IsOpen U) (hU : D.carrier ⊆ U) :
    U ∈ 𝓝ˢ D.carrier :=
  Stokes.SingularCubeSmoothExtensionAudit.mem_nhdsSet_of_isOpen_of_subset hUo hU

/-- A packaged carrier inside an open set gives pointwise neighborhoods. -/
theorem mem_nhds_of_isOpen_of_subset
    (hUo : IsOpen U) (hU : D.carrier ⊆ U)
    {x : Fin m → Real} (hx : x ∈ D.carrier) :
    U ∈ 𝓝 x :=
  Stokes.SingularCubeSmoothExtensionAudit.mem_nhds_of_isOpen_of_subset hUo hU hx

/-- Eventual membership in an open set around the packaged carrier. -/
theorem eventually_mem_of_isOpen_of_subset
    (hUo : IsOpen U) (hU : D.carrier ⊆ U) :
    (∀ᶠ x in 𝓝ˢ D.carrier, x ∈ U) :=
  Stokes.SingularCubeSmoothExtensionAudit.eventually_mem_of_isOpen_of_subset hUo hU

/-- Turn an open containment of the packaged carrier into an open-neighborhood
package. -/
def openNeighborhood
    (hUo : IsOpen U) (hU : D.carrier ⊆ U) :
    CompactCarrierOpenNeighborhood D.carrier :=
  compactCarrierOpenNeighborhoodOfSubset hUo hU

@[simp]
theorem openNeighborhood_openSet
    (hUo : IsOpen U) (hU : D.carrier ⊆ U) :
    (D.openNeighborhood hUo hU).openSet = U :=
  rfl

/-- Rewrite a packaged-carrier neighborhood statement to the canonical
`cubeAndFacesImage` carrier. -/
theorem canonical_mem_nhdsSet_of_isOpen_of_subset
    (hUo : IsOpen U) (hU : cubeAndFacesImage cube ⊆ U) :
    U ∈ 𝓝ˢ D.carrier := by
  apply D.mem_nhdsSet_of_isOpen_of_subset hUo
  intro x hx
  exact hU (by simpa [D.carrier_eq] using hx)

/-- Rewrite a canonical cube-and-faces containment to the packaged carrier. -/
theorem carrier_subset_of_cubeAndFacesImage_subset
    (hU : cubeAndFacesImage cube ⊆ U) :
    D.carrier ⊆ U := by
  intro x hx
  exact hU (by simpa [D.carrier_eq] using hx)

/-- Rewrite a packaged-carrier containment to the canonical cube-and-faces
image. -/
theorem cubeAndFacesImage_subset_of_carrier_subset
    (hU : D.carrier ⊆ U) :
    cubeAndFacesImage cube ⊆ U := by
  intro x hx
  exact hU (by simpa [D.carrier_eq] using hx)

/-- Finite open-subcover package for an open cover of a packaged
cube-and-faces carrier. -/
theorem exists_finiteOpenSubcover
    {ι : Type*} {W : ι → Set (Fin m → Real)}
    (hWo : ∀ i, IsOpen (W i)) (hW : D.carrier ⊆ ⋃ i, W i) :
    ∃ _ : CompactCarrierFiniteOpenSubcover D.carrier W, True :=
  exists_compactCarrierFiniteOpenSubcover D.isCompact_carrier hWo hW

/-- Direct finite open-subcover theorem for a packaged cube-and-faces
carrier. -/
theorem exists_finite_open_subcover
    {ι : Type*} {W : ι → Set (Fin m → Real)}
    (hWo : ∀ i, IsOpen (W i)) (hW : D.carrier ⊆ ⋃ i, W i) :
    ∃ t : Finset ι, D.carrier ⊆ ⋃ i ∈ t, W i :=
  Stokes.SingularCubeSmoothExtensionAudit.exists_finite_open_subcover
    D.isCompact_carrier hWo hW

/-- Finite neighborhood-subcover package for a packaged cube-and-faces
carrier. -/
theorem exists_finiteNhdsSubcover
    {N : (Fin m → Real) → Set (Fin m → Real)}
    (hN : ∀ x ∈ D.carrier, N x ∈ 𝓝 x) :
    ∃ _ : CompactCarrierFiniteNhdsSubcover D.carrier N, True :=
  exists_compactCarrierFiniteNhdsSubcover D.isCompact_carrier hN

/-- Direct finite neighborhood-subcover theorem for a packaged carrier. -/
theorem exists_finite_nhds_subcover_mem_nhdsSet
    {N : (Fin m → Real) → Set (Fin m → Real)}
    (hN : ∀ x ∈ D.carrier, N x ∈ 𝓝 x) :
    ∃ t : Finset (Fin m → Real),
      (∀ x ∈ t, x ∈ D.carrier) ∧
        (⋃ x ∈ t, N x) ∈ 𝓝ˢ D.carrier :=
  Stokes.SingularCubeSmoothExtensionAudit.exists_finite_nhds_subcover_mem_nhdsSet
    D.isCompact_carrier hN

/-- Open shrink of an open set containing the packaged carrier, with closure
still lying in the original open set. -/
theorem exists_openShrink
    (hUo : IsOpen U) (hU : D.carrier ⊆ U) :
    ∃ _ : CompactCarrierOpenShrink D.carrier U, True :=
  exists_compactCarrierOpenShrink_of_isOpen_of_subset
    D.isCompact_carrier hUo hU

/-- Projection form of the packaged-carrier open-shrink theorem. -/
theorem exists_open_closure_subset
    (hUo : IsOpen U) (hU : D.carrier ⊆ U) :
    ∃ V : Set (Fin m → Real),
      IsOpen V ∧ D.carrier ⊆ V ∧ closure V ⊆ U :=
  Stokes.SingularCubeSmoothExtensionAudit.exists_open_closure_subset_of_compact_subset_open
    D.isCompact_carrier hUo hU

/-- Open shrink using the canonical `cubeAndFacesImage` containment as input. -/
theorem exists_openShrink_of_cubeAndFacesImage_subset
    (hUo : IsOpen U) (hU : cubeAndFacesImage cube ⊆ U) :
    ∃ _ : CompactCarrierOpenShrink D.carrier U, True :=
  D.exists_openShrink hUo (D.carrier_subset_of_cubeAndFacesImage_subset hU)

/-- Projection form of `exists_openShrink_of_cubeAndFacesImage_subset`. -/
theorem exists_open_closure_subset_of_cubeAndFacesImage_subset
    (hUo : IsOpen U) (hU : cubeAndFacesImage cube ⊆ U) :
    ∃ V : Set (Fin m → Real),
      IsOpen V ∧ D.carrier ⊆ V ∧ closure V ⊆ U :=
  D.exists_open_closure_subset hUo
    (D.carrier_subset_of_cubeAndFacesImage_subset hU)

/-- The cube image lies in any open set containing the packaged carrier. -/
theorem cube_mem_of_carrier_subset
    (hU : D.carrier ⊆ U) {x : Fin (n + 1) → Real}
    (hx : x ∈ singularParameterCube (n + 1)) :
    cube.toFun x ∈ U :=
  hU (D.cube_image_subset_carrier ⟨x, hx, rfl⟩)

/-- High face images lie in any open set containing the packaged carrier. -/
theorem highFace_mem_of_carrier_subset
    (hU : D.carrier ⊆ U) (i : Fin (n + 1))
    {x : Fin n → Real} (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 1).toFun x ∈ U :=
  hU (D.highFace_image_subset_carrier i ⟨x, hx, rfl⟩)

/-- Low face images lie in any open set containing the packaged carrier. -/
theorem lowFace_mem_of_carrier_subset
    (hU : D.carrier ⊆ U) (i : Fin (n + 1))
    {x : Fin n → Real} (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 0).toFun x ∈ U :=
  hU (D.lowFace_image_subset_carrier i ⟨x, hx, rfl⟩)

/-- If the packaged carrier is shrunk inside an outer set, the cube image lies
in the shrink. -/
theorem cube_mem_openShrink
    {S : CompactCarrierOpenShrink D.carrier U}
    {x : Fin (n + 1) → Real}
    (hx : x ∈ singularParameterCube (n + 1)) :
    cube.toFun x ∈ S.shrink :=
  S.carrier_subset_shrink (D.cube_image_subset_carrier ⟨x, hx, rfl⟩)

/-- If the packaged carrier is shrunk inside an outer set, the high-face image
lies in the shrink. -/
theorem highFace_mem_openShrink
    {S : CompactCarrierOpenShrink D.carrier U}
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 1).toFun x ∈ S.shrink :=
  S.carrier_subset_shrink (D.highFace_image_subset_carrier i ⟨x, hx, rfl⟩)

/-- If the packaged carrier is shrunk inside an outer set, the low-face image
lies in the shrink. -/
theorem lowFace_mem_openShrink
    {S : CompactCarrierOpenShrink D.carrier U}
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 0).toFun x ∈ S.shrink :=
  S.carrier_subset_shrink (D.lowFace_image_subset_carrier i ⟨x, hx, rfl⟩)

/-- If the packaged carrier is shrunk inside an outer set, the cube image lies
in the outer set. -/
theorem cube_mem_openShrink_outer
    {S : CompactCarrierOpenShrink D.carrier U}
    {x : Fin (n + 1) → Real}
    (hx : x ∈ singularParameterCube (n + 1)) :
    cube.toFun x ∈ U :=
  S.shrink_subset_outer (D.cube_mem_openShrink hx)

/-- If the packaged carrier is shrunk inside an outer set, the high-face image
lies in the outer set. -/
theorem highFace_mem_openShrink_outer
    {S : CompactCarrierOpenShrink D.carrier U}
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 1).toFun x ∈ U :=
  S.shrink_subset_outer (D.highFace_mem_openShrink i hx)

/-- If the packaged carrier is shrunk inside an outer set, the low-face image
lies in the outer set. -/
theorem lowFace_mem_openShrink_outer
    {S : CompactCarrierOpenShrink D.carrier U}
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 0).toFun x ∈ U :=
  S.shrink_subset_outer (D.lowFace_mem_openShrink i hx)

end CubeAndFacesCompactData

section CoreExtensionTopologyWrappers

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n m : Nat}
variable {I : ModelWithCorners Real (Fin m → Real) H}
variable {omega : ManifoldForm I M n}
variable {chart : M} {cube : SmoothSingularCube (n + 1) m}

/-- A theorem-facing carrier/open-neighborhood package for the core singular
cube extension input.  It isolates the topological part that a later cutoff
construction must satisfy. -/
structure ChartwiseSingularCubeCarrierNeighborhood
    (D : CubeAndFacesCompactData cube) where
  extensionSet : Set (Fin m → Real)
  isOpen_extensionSet : IsOpen extensionSet
  carrier_subset_extensionSet : D.carrier ⊆ extensionSet

namespace ChartwiseSingularCubeCarrierNeighborhood

variable {D : CubeAndFacesCompactData cube}

theorem extension_mem_nhdsSet
    (N : ChartwiseSingularCubeCarrierNeighborhood (cube := cube) D) :
    N.extensionSet ∈ 𝓝ˢ D.carrier :=
  D.mem_nhdsSet_of_isOpen_of_subset
    N.isOpen_extensionSet N.carrier_subset_extensionSet

theorem cubeAndFacesImage_subset_extensionSet
    (N : ChartwiseSingularCubeCarrierNeighborhood (cube := cube) D) :
    cubeAndFacesImage cube ⊆ N.extensionSet :=
  D.cubeAndFacesImage_subset_of_carrier_subset
    N.carrier_subset_extensionSet

theorem cube_mem_extensionSet
    (N : ChartwiseSingularCubeCarrierNeighborhood (cube := cube) D)
    {x : Fin (n + 1) → Real}
    (hx : x ∈ singularParameterCube (n + 1)) :
    cube.toFun x ∈ N.extensionSet :=
  D.cube_mem_of_carrier_subset N.carrier_subset_extensionSet hx

theorem highFace_mem_extensionSet
    (N : ChartwiseSingularCubeCarrierNeighborhood (cube := cube) D)
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 1).toFun x ∈ N.extensionSet :=
  D.highFace_mem_of_carrier_subset N.carrier_subset_extensionSet i hx

theorem lowFace_mem_extensionSet
    (N : ChartwiseSingularCubeCarrierNeighborhood (cube := cube) D)
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 0).toFun x ∈ N.extensionSet :=
  D.lowFace_mem_of_carrier_subset N.carrier_subset_extensionSet i hx

/-- Convert the carrier-neighborhood package into the exact
`cubeAndFacesImage` containment field used by
`ChartwiseSingularCubeCoreExtensionInput`. -/
theorem image_subset_extensionSet
    (N : ChartwiseSingularCubeCarrierNeighborhood (cube := cube) D) :
    cubeAndFacesImage cube ⊆ N.extensionSet :=
  N.cubeAndFacesImage_subset_extensionSet

end ChartwiseSingularCubeCarrierNeighborhood

/-- The canonical carrier-neighborhood package built from an open extension set
containing the canonical cube-and-faces image. -/
def chartwiseSingularCubeCarrierNeighborhoodOfCubeAndFacesSubset
    (D : CubeAndFacesCompactData cube)
    {extensionSet : Set (Fin m → Real)}
    (hOpen : IsOpen extensionSet)
    (hSubset : cubeAndFacesImage cube ⊆ extensionSet) :
    ChartwiseSingularCubeCarrierNeighborhood (cube := cube) D where
  extensionSet := extensionSet
  isOpen_extensionSet := hOpen
  carrier_subset_extensionSet :=
    D.carrier_subset_of_cubeAndFacesImage_subset hSubset

/-- Open-shrink package specialized to the carrier-neighborhood wrapper. -/
def chartwiseSingularCubeCarrierNeighborhoodOfOpenShrink
    (D : CubeAndFacesCompactData cube)
    {outer : Set (Fin m → Real)}
    (S : CompactCarrierOpenShrink D.carrier outer) :
    ChartwiseSingularCubeCarrierNeighborhood (cube := cube) D where
  extensionSet := S.shrink
  isOpen_extensionSet := S.isOpen_shrink
  carrier_subset_extensionSet := S.carrier_subset_shrink

@[simp]
theorem chartwiseSingularCubeCarrierNeighborhoodOfOpenShrink_extensionSet
    (D : CubeAndFacesCompactData cube)
    {outer : Set (Fin m → Real)}
    (S : CompactCarrierOpenShrink D.carrier outer) :
    (chartwiseSingularCubeCarrierNeighborhoodOfOpenShrink
      (cube := cube) D S).extensionSet = S.shrink :=
  rfl

end CoreExtensionTopologyWrappers

end SingularCubeSmoothExtensionAudit
end Stokes

end
