import Stokes.BoundaryChart.Orientation

/-!
# Boundary chart local inverse and image data

This file was split out of Stokes.HalfSpace as part of the M6.0
module-structure pass.  The theorem statements and proofs are intended to
remain identical to the monolithic version.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Image data for a boundary chart transition between selected boundary boxes.

For nonlinear chart changes the image of a coordinate rectangle is not itself a
rectangle by default.  This predicate records the local box choice: the source
boundary box maps into the target boundary box and covers it.
-/
def boundaryChartSelectedBoxImageData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real) : Prop :=
  MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d) ∧
    SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)

theorem boundaryChartSelectedBoxImageData.mapsTo {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d) :=
  himage.1

theorem boundaryChartSelectedBoxImageData.surjOn {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d) :=
  himage.2

/--
The compact-image half of a boundary chart-box selection: the source boundary
box maps into the chosen target boundary box.
-/
def boundaryChartCompactImageBoxSelection {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real) : Prop :=
  (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
    lowerZeroFaceDomain c d

/--
The inverse-function half of a boundary chart-box selection: the chosen target
boundary box lies inside the image of the source boundary box.
-/
def boundaryChartInverseImageBoxSelection {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real) : Prop :=
  lowerZeroFaceDomain c d ⊆
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b

theorem boundaryChartCompactImageBoxSelection.mapsTo {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d) :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d) := by
  intro u hu
  exact hcompact ⟨u, hu, rfl⟩

theorem boundaryChartInverseImageBoxSelection.surjOn {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hinverse : boundaryChartInverseImageBoxSelection I x0 x1 a b c d) :
    SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d) :=
  hinverse

theorem boundaryChartInverseImageBoxSelection.of_rightInverseOn {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (g : (Fin n → Real) → (Fin n → Real))
    (hmap : MapsTo g (lowerZeroFaceDomain c d) (lowerZeroFaceDomain a b))
    (hright : ∀ y ∈ lowerZeroFaceDomain c d,
      boundaryChartTransition I x0 x1 (g y) = y) :
    boundaryChartInverseImageBoxSelection I x0 x1 a b c d := by
  intro y hy
  exact ⟨g y, hmap hy, hright y hy⟩

/--
Local inverse data on a selected target boundary box.

This is the constructive form of `boundaryChartInverseImageBoxSelection`: it
packages an actual right inverse from the target boundary box back into the
source boundary box.
-/
def boundaryChartLocalInverseData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b c d : Fin (n + 1) → Real) : Prop :=
  ∃ g : (Fin n → Real) → (Fin n → Real),
    MapsTo g (lowerZeroFaceDomain c d) (lowerZeroFaceDomain a b) ∧
      ∀ y ∈ lowerZeroFaceDomain c d,
        boundaryChartTransition I x0 x1 (g y) = y

theorem boundaryChartLocalInverseData.of_rightInverseOn {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (g : (Fin n → Real) → (Fin n → Real))
    (hmap : MapsTo g (lowerZeroFaceDomain c d) (lowerZeroFaceDomain a b))
    (hright : ∀ y ∈ lowerZeroFaceDomain c d,
      boundaryChartTransition I x0 x1 (g y) = y) :
    boundaryChartLocalInverseData I x0 x1 a b c d :=
  ⟨g, hmap, hright⟩

theorem boundaryChartLocalInverseData.inverseImageBoxSelection {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    boundaryChartInverseImageBoxSelection I x0 x1 a b c d := by
  rcases hlocal with ⟨g, hmap, hright⟩
  exact boundaryChartInverseImageBoxSelection.of_rightInverseOn g hmap hright

theorem boundaryChartLocalInverseData.surjOn {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d) :=
  hlocal.inverseImageBoxSelection.surjOn

theorem boundaryChartLocalInverseData.of_inverseImageBoxSelection {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hinverse : boundaryChartInverseImageBoxSelection I x0 x1 a b c d) :
    boundaryChartLocalInverseData I x0 x1 a b c d := by
  classical
  let g : (Fin n → Real) → (Fin n → Real) := fun y =>
    if hy : y ∈ lowerZeroFaceDomain c d then
      Classical.choose (hinverse hy)
    else
      y
  refine ⟨g, ?_, ?_⟩
  · intro y hy
    simpa [g, hy] using (Classical.choose_spec (hinverse hy)).1
  · intro y hy
    simpa [g, hy] using (Classical.choose_spec (hinverse hy)).2

/-- A nonzero tangential Jacobian makes the boundary transition derivative surjective. -/
theorem boundaryChartTransitionTangentMap_range_eq_top_of_jacobian_ne_zero {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (u : Fin n → Real)
    (hdet : boundaryChartTransitionJacobian I x0 x1 u ≠ 0) :
    (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤ := by
  let L : (Fin n → Real) →ₗ[Real] (Fin n → Real) :=
    (boundaryChartTransitionTangentMap I x0 x1 u :
      (Fin n → Real) →ₗ[Real] (Fin n → Real))
  have hLdet : LinearMap.det L ≠ 0 := by
    rw [← boundaryChartTransitionMatrix_det_eq_linearMap_det]
    simpa [boundaryChartTransitionJacobian, L] using hdet
  have hker : LinearMap.ker L = ⊥ := by
    by_contra hker
    exact hLdet ((LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker)
  change LinearMap.range L = ⊤
  exact LinearMap.ker_eq_bot_iff_range_eq_top.mp hker

/--
Orientation compatibility gives the surjectivity hypothesis needed by the
inverse function theorem at each point of the selected boundary source.
-/
theorem boundaryChartTransitionTangentMap_range_eq_top_of_orientationCompatibleOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {s : Set (Fin n → Real)} {u : Fin n → Real}
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 s) (hu : u ∈ s) :
    (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤ :=
  boundaryChartTransitionTangentMap_range_eq_top_of_jacobian_ne_zero I x0 x1 u
    (ne_of_gt (horient u hu))

/--
Local openness from the inverse function theorem: if the boundary chart
transition has a strict derivative whose tangential linear map is surjective,
then the image of any source neighborhood is a neighborhood of the image point.
-/
theorem boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {u : Fin n → Real}
    (hstrict : HasStrictFDerivAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈
      𝓝 (boundaryChartTransition I x0 x1 u) := by
  rw [← hstrict.map_nhds_eq_of_surj hsurj]
  exact image_mem_map hsource

theorem boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_jacobian_ne_zero
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {u : Fin n → Real}
    (hstrict : HasStrictFDerivAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hdet : boundaryChartTransitionJacobian I x0 x1 u ≠ 0)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈
      𝓝 (boundaryChartTransition I x0 x1 u) :=
  boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj hstrict
    (boundaryChartTransitionTangentMap_range_eq_top_of_jacobian_ne_zero I x0 x1 u hdet)
    hsource

theorem boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_orientationCompatibleOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {s : Set (Fin n → Real)}
    {u : Fin n → Real}
    (hstrict : HasStrictFDerivAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 s) (hu : u ∈ s)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈
      𝓝 (boundaryChartTransition I x0 x1 u) :=
  boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj hstrict
    (boundaryChartTransitionTangentMap_range_eq_top_of_orientationCompatibleOn horient hu)
    hsource

/-- Smoothness plus the Frechet derivative upgrades to the strict derivative used by IFT. -/
theorem boundaryChartTransition_hasStrictFDerivAt_of_contDiffAt_hasFDerivAt {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {u : Fin n → Real}
    (hcont : ContDiffAt Real ⊤ (boundaryChartTransition I x0 x1) u)
    (hderiv : HasFDerivAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u) u) :
    HasStrictFDerivAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u) u :=
  hcont.hasStrictFDerivAt' hderiv (by simp)

/--
If the image of a source boundary box is a neighborhood of the image point, then
one can choose a target boundary box around that image point contained in the
source image.  This is the point-set selection step after local openness.
-/
theorem exists_boundaryChartInverseImageBoxSelection_of_image_mem_nhds {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) {a b : Fin (n + 1) → Real} {u : Fin n → Real}
    (himage : (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈
      𝓝 (boundaryChartTransition I x0 x1 u)) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartInverseImageBoxSelection I x0 x1 a b c d := by
  rcases exists_lowerZeroFaceDomain_subset_of_mem_nhds himage with
    ⟨c, d, hc0, hle, hmem, hsubset⟩
  exact ⟨c, d, hc0, hle, hmem, hsubset⟩

theorem exists_boundaryChartInverseImageBoxSelection_of_hasStrictFDerivAt_surj
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {u : Fin n → Real}
    (hstrict : HasStrictFDerivAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartInverseImageBoxSelection I x0 x1 a b c d :=
  exists_boundaryChartInverseImageBoxSelection_of_image_mem_nhds I x0 x1
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hstrict hsurj hsource)

theorem exists_boundaryChartInverseImageBoxSelection_of_hasStrictFDerivAt_orientationCompatibleOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {s : Set (Fin n → Real)}
    {u : Fin n → Real}
    (hstrict : HasStrictFDerivAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 s) (hu : u ∈ s)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartInverseImageBoxSelection I x0 x1 a b c d :=
  exists_boundaryChartInverseImageBoxSelection_of_hasStrictFDerivAt_surj
    hstrict
    (boundaryChartTransitionTangentMap_range_eq_top_of_orientationCompatibleOn horient hu)
    hsource

theorem exists_boundaryChartInverseImageBoxSelection_of_contDiffAt_deriv_orient
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {s : Set (Fin n → Real)}
    {u : Fin n → Real}
    (hcont : ContDiffAt Real ⊤ (boundaryChartTransition I x0 x1) u)
    (hderiv : HasFDerivAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 s) (hu : u ∈ s)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartInverseImageBoxSelection I x0 x1 a b c d :=
  exists_boundaryChartInverseImageBoxSelection_of_hasStrictFDerivAt_orientationCompatibleOn
    (boundaryChartTransition_hasStrictFDerivAt_of_contDiffAt_hasFDerivAt hcont hderiv)
    horient hu hsource

/--
Selected source boxes supply the Frechet derivative on the whole boundary
coordinate space whenever the source box is a neighborhood of the point.
-/
theorem boundaryChartTransition_hasFDerivAt_of_selectedBox_mem_nhds {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H} [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    HasFDerivAt (boundaryChartTransition I x0 x1)
      (boundaryChartTransitionTangentMap I x0 x1 u) u :=
  (hasFDerivWithinAt_of_mem_nhds hsource).mp
    ((boundaryChartTransition_hasFDerivWithinAt_of_selectedBox hbox) u hu)

theorem boundaryChartTransition_contDiffOn_of_selectedBox {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H} [IsManifold I ⊤ M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    ContDiffOn Real ⊤ (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) := by
  have hamb :
      ContDiffOn Real ⊤ (ManifoldForm.chartTransition I x0 x1)
        (boundaryInclusion n '' lowerZeroFaceDomain a b) :=
    ManifoldForm.contDiffOn_chartTransition (I := I)
      (s := boundaryInclusion n '' lowerZeroFaceDomain a b)
      (by
        rintro _ ⟨u, hu, rfl⟩
        exact hbox.boundaryFace_subset_target u hu)
      (by
        rintro _ ⟨u, hu, rfl⟩
        exact hbox.boundaryFace_subset_overlap u hu)
  have hincl : ContDiffOn Real ⊤ (boundaryInclusion n) (lowerZeroFaceDomain a b) :=
    (boundaryTangentInclusion n).contDiff.contDiffOn
  have hcomp :
      ContDiffOn Real ⊤
        (ManifoldForm.chartTransition I x0 x1 ∘ boundaryInclusion n)
        (lowerZeroFaceDomain a b) :=
    hamb.comp hincl (mapsTo_image (boundaryInclusion n) (lowerZeroFaceDomain a b))
  simpa [boundaryChartTransition, Function.comp_def, boundaryTangentProjection_apply] using
    (boundaryTangentProjection n).contDiff.comp_contDiffOn hcomp

theorem boundaryChartTransition_contDiffAt_of_selectedBox_mem_nhds {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H} [IsManifold I ⊤ M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ContDiffAt Real ⊤ (boundaryChartTransition I x0 x1) u :=
  (boundaryChartTransition_contDiffOn_of_selectedBox hbox).contDiffAt hsource

theorem exists_boundaryChartInverseImageBoxSelection_of_selectedBox_contDiffAt_orient
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcont : ContDiffAt Real ⊤ (boundaryChartTransition I x0 x1) u)
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartInverseImageBoxSelection I x0 x1 a b c d :=
  exists_boundaryChartInverseImageBoxSelection_of_contDiffAt_deriv_orient
    hcont
    (boundaryChartTransition_hasFDerivAt_of_selectedBox_mem_nhds hbox hu hsource)
    horient hu hsource

theorem exists_boundaryChartInverseImageBoxSelection_of_selectedBox_orientationCompatibleOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartInverseImageBoxSelection I x0 x1 a b c d :=
  exists_boundaryChartInverseImageBoxSelection_of_selectedBox_contDiffAt_orient
    hbox (boundaryChartTransition_contDiffAt_of_selectedBox_mem_nhds hbox hsource)
    horient hu hsource

theorem exists_boundaryChartInverseImageBoxSelection_of_selectedBox_contDiffAt_orient_lt
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcont : ContDiffAt Real ⊤ (boundaryChartTransition I x0 x1) u)
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (ha : ∀ i : Fin n, a i.succ < u i)
    (hb : ∀ i : Fin n, u i < b i.succ) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartInverseImageBoxSelection I x0 x1 a b c d := by
  have hu : u ∈ lowerZeroFaceDomain a b := by
    rw [lowerZeroFaceDomain, faceDomain]
    exact ⟨fun i => le_of_lt (ha i), fun i => le_of_lt (hb i)⟩
  exact
    exists_boundaryChartInverseImageBoxSelection_of_selectedBox_contDiffAt_orient
      hbox hcont horient hu (lowerZeroFaceDomain_mem_nhds_of_lt ha hb)

theorem exists_boundaryChartInverseImageBoxSelection_of_selectedBox_contDiffAt_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcont : ContDiffAt Real ⊤ (boundaryChartTransition I x0 x1) u)
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartInverseImageBoxSelection I x0 x1 a b c d :=
  exists_boundaryChartInverseImageBoxSelection_of_selectedBox_contDiffAt_orient
    hbox hcont (A.orientationCompatibleOn_selectedBox hx0 hx1 hbox) hu hsource

theorem exists_boundaryChartInverseImageBoxSelection_of_selectedBox_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartInverseImageBoxSelection I x0 x1 a b c d :=
  exists_boundaryChartInverseImageBoxSelection_of_selectedBox_orientationCompatibleOn
    hbox (A.orientationCompatibleOn_selectedBox hx0 hx1 hbox) hu hsource

theorem exists_boundaryChartInverseImageBoxSelection_of_selectedBox_contDiffAt_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hcont : ContDiffAt Real ⊤ (boundaryChartTransition I x0 x1) u)
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartInverseImageBoxSelection I x0 x1 a b c d :=
  exists_boundaryChartInverseImageBoxSelection_of_selectedBox_contDiffAt_orient
    hbox hcont (boundaryChartOrientationCompatibleOn_selectedBox_of_orientedManifold hbox)
    hu hsource

theorem exists_boundaryChartInverseImageBoxSelection_of_selectedBox_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M] [BoundaryChartOrientedManifold I M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartInverseImageBoxSelection I x0 x1 a b c d :=
  exists_boundaryChartInverseImageBoxSelection_of_selectedBox_orientationCompatibleOn
    hbox (boundaryChartOrientationCompatibleOn_selectedBox_of_orientedManifold hbox)
    hu hsource

theorem exists_boundaryChartLocalInverseData_of_image_mem_nhds {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) {a b : Fin (n + 1) → Real} {u : Fin n → Real}
    (himage : (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈
      𝓝 (boundaryChartTransition I x0 x1 u)) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartLocalInverseData I x0 x1 a b c d := by
  rcases exists_boundaryChartInverseImageBoxSelection_of_image_mem_nhds
      I x0 x1 himage with
    ⟨c, d, hc0, hle, hmem, hinverse⟩
  exact ⟨c, d, hc0, hle, hmem,
    boundaryChartLocalInverseData.of_inverseImageBoxSelection hinverse⟩

theorem exists_boundaryChartLocalInverseData_of_selectedBox_orient
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (horient : boundaryChartOrientationCompatibleOn I x0 x1 (lowerZeroFaceDomain a b))
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartLocalInverseData I x0 x1 a b c d := by
  rcases exists_boundaryChartInverseImageBoxSelection_of_selectedBox_orientationCompatibleOn
      hbox horient hu hsource with
    ⟨c, d, hc0, hle, hmem, hinverse⟩
  exact ⟨c, d, hc0, hle, hmem,
    boundaryChartLocalInverseData.of_inverseImageBoxSelection hinverse⟩

theorem exists_boundaryChartLocalInverseData_of_selectedBox_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartLocalInverseData I x0 x1 a b c d :=
  exists_boundaryChartLocalInverseData_of_selectedBox_orient
    hbox (A.orientationCompatibleOn_selectedBox hx0 hx1 hbox) hu hsource

theorem exists_boundaryChartLocalInverseData_of_selectedBox_orientedAtlas_lt
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (ha : ∀ i : Fin n, a i.succ < u i)
    (hb : ∀ i : Fin n, u i < b i.succ) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartLocalInverseData I x0 x1 a b c d := by
  have hu : u ∈ lowerZeroFaceDomain a b := by
    rw [lowerZeroFaceDomain, faceDomain]
    exact ⟨fun i => le_of_lt (ha i), fun i => le_of_lt (hb i)⟩
  exact exists_boundaryChartLocalInverseData_of_selectedBox_orientedAtlas
    A hx0 hx1 hbox hu (lowerZeroFaceDomain_mem_nhds_of_lt ha hb)

theorem exists_boundaryChartLocalInverseData_of_selectedBox_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M] [BoundaryChartOrientedManifold I M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hu : u ∈ lowerZeroFaceDomain a b)
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartLocalInverseData I x0 x1 a b c d :=
  exists_boundaryChartLocalInverseData_of_selectedBox_orient
    hbox (boundaryChartOrientationCompatibleOn_selectedBox_of_orientedManifold hbox)
    hu hsource

theorem exists_boundaryChartLocalInverseData_of_selectedBox_orientedManifold_lt
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I ⊤ M] [BoundaryChartOrientedManifold I M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (ha : ∀ i : Fin n, a i.succ < u i)
    (hb : ∀ i : Fin n, u i < b i.succ) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d ∧
        boundaryChartLocalInverseData I x0 x1 a b c d := by
  have hu : u ∈ lowerZeroFaceDomain a b := by
    rw [lowerZeroFaceDomain, faceDomain]
    exact ⟨fun i => le_of_lt (ha i), fun i => le_of_lt (hb i)⟩
  exact exists_boundaryChartLocalInverseData_of_selectedBox_orientedManifold
    hbox hu (lowerZeroFaceDomain_mem_nhds_of_lt ha hb)

theorem boundaryChartSelectedBoxImageData_of_mapsTo_subset_image {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsubset : lowerZeroFaceDomain c d ⊆
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b) :
    boundaryChartSelectedBoxImageData I x0 x1 a b c d :=
  ⟨hmaps, hsubset⟩

/--
Build packaged boundary-box image data from the two chart-box selection halves:
compact image selection gives `MapsTo`, and inverse-function/local-image
selection gives `SurjOn`.
-/
theorem boundaryChartSelectedBoxImageData_of_chartBoxSelections {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d)
    (hinverse : boundaryChartInverseImageBoxSelection I x0 x1 a b c d) :
    boundaryChartSelectedBoxImageData I x0 x1 a b c d :=
  ⟨hcompact.mapsTo, hinverse.surjOn⟩

theorem boundaryChartSelectedBoxImageData_of_mapsTo_localInverseData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    boundaryChartSelectedBoxImageData I x0 x1 a b c d :=
  ⟨hmaps, hlocal.surjOn⟩

theorem boundaryChartSelectedBoxImageData_of_compactImage_localInverseData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d)
    (hlocal : boundaryChartLocalInverseData I x0 x1 a b c d) :
    boundaryChartSelectedBoxImageData I x0 x1 a b c d :=
  boundaryChartSelectedBoxImageData_of_mapsTo_localInverseData
    hcompact.mapsTo hlocal

theorem boundaryChartSelectedBoxImageData_of_image_subset_target_subset_image
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b c d : Fin (n + 1) → Real}
    (himageSubset : (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
      lowerZeroFaceDomain c d)
    (htargetSubset : lowerZeroFaceDomain c d ⊆
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b) :
    boundaryChartSelectedBoxImageData I x0 x1 a b c d :=
  boundaryChartSelectedBoxImageData_of_chartBoxSelections himageSubset htargetSubset

/-- Continuous selected boundary chart transitions have compact source-box image. -/
theorem boundaryChartTransition_continuousOn_of_selectedBox {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H} [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    ContinuousOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) := by
  intro u hu
  exact (boundaryChartTransition_hasFDerivWithinAt_of_selectedBox hbox u hu).continuousWithinAt

/--
Compact image box selection: if the image of the source boundary box is compact,
then some target lower-zero face box contains it.
-/
theorem exists_boundaryChartCompactImageBoxSelection_of_isCompact_image {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real)
    (hK : IsCompact
      ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b)) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartCompactImageBoxSelection I x0 x1 a b c d := by
  rcases exists_lowerZeroFaceDomain_of_isCompact hK with ⟨c, d, hc0, hle, hsubset⟩
  exact ⟨c, d, hc0, hle, hsubset⟩

theorem exists_boundaryChartCompactImageBoxSelection_of_continuousOn {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (a b : Fin (n + 1) → Real)
    (hcont : ContinuousOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b)) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartCompactImageBoxSelection I x0 x1 a b c d := by
  exact exists_boundaryChartCompactImageBoxSelection_of_isCompact_image I x0 x1 a b
    ((isCompact_lowerZeroFaceDomain a b).image_of_continuousOn hcont)

theorem exists_boundaryChartCompactImageBoxSelection_of_selectedBox {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H} [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    ∃ c d : Fin (n + 1) → Real, c 0 = 0 ∧ c ≤ d ∧
      boundaryChartCompactImageBoxSelection I x0 x1 a b c d :=
  exists_boundaryChartCompactImageBoxSelection_of_continuousOn I x0 x1 a b
    (boundaryChartTransition_continuousOn_of_selectedBox hbox)

theorem boundaryChartTransition_injOn_of_selectedBox_orientedAtlas {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) :=
  boundaryChartTransition_injOn_of_selectedBox_compatibleOn hbox
    (A.transitionCompatibleOn_selectedBox hx0 hx1 hbox)

theorem boundaryChartTransition_injOn_of_selectedBox_orientedManifold {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b) :
    InjOn (boundaryChartTransition I x0 x1) (lowerZeroFaceDomain a b) :=
  boundaryChartTransition_injOn_of_selectedBox_compatibleOn hbox
    (boundaryChartTransitionCompatibleOn_selectedBox_of_orientedManifold hbox)

theorem boundaryChartTransition_bijOn_of_selectedBox_orientedAtlas_mapsTo_surjOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d) :=
  boundaryChartTransition_bijOn_of_selectedBox_compatibleOn_mapsTo_surjOn
    hbox (A.transitionCompatibleOn_selectedBox hx0 hx1 hbox) hmaps hsurj

theorem boundaryChartTransition_bijOn_of_selectedBox_orientedAtlas_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d) :=
  boundaryChartTransition_bijOn_of_selectedBox_orientedAtlas_mapsTo_surjOn
    A hx0 hx1 hbox himage.mapsTo himage.surjOn

theorem boundaryChartTransition_bijOn_of_selectedBox_orientedManifold_mapsTo_surjOn
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d) :=
  boundaryChartTransition_bijOn_of_selectedBox_compatibleOn_mapsTo_surjOn
    hbox (boundaryChartTransitionCompatibleOn_selectedBox_of_orientedManifold hbox)
    hmaps hsurj

theorem boundaryChartTransition_bijOn_of_selectedBox_orientedManifold_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    BijOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d) :=
  boundaryChartTransition_bijOn_of_selectedBox_orientedManifold_mapsTo_surjOn
    hbox himage.mapsTo himage.surjOn

theorem boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_selectedBox_orientedAtlas
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d :=
  boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_bijOn I x0 x1 a b c d
    (boundaryChartTransition_bijOn_of_selectedBox_orientedAtlas_mapsTo_surjOn
      A hx0 hx1 hbox hmaps hsurj)

theorem boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_orientedAtlas_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d :=
  boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_bijOn I x0 x1 a b c d
    (boundaryChartTransition_bijOn_of_selectedBox_orientedAtlas_imageData
      A hx0 hx1 hbox himage)

theorem boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_selectedBox_orientedManifold
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hmaps : MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d))
    (hsurj : SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b) (lowerZeroFaceDomain c d)) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d :=
  boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_bijOn I x0 x1 a b c d
    (boundaryChartTransition_bijOn_of_selectedBox_orientedManifold_mapsTo_surjOn
      hbox hmaps hsurj)

theorem boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_orientedManifold_imageData
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [BoundaryChartOrientedManifold I M] {x0 x1 : M}
    {ω : ManifoldForm I M n} {a b c d : Fin (n + 1) → Real}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b =
      lowerZeroFaceDomain c d :=
  boundaryChartTransition_image_eq_lowerZeroFaceDomain_of_bijOn I x0 x1 a b c d
    (boundaryChartTransition_bijOn_of_selectedBox_orientedManifold_imageData
      hbox himage)

end ManifoldBoundary

end Stokes

end
