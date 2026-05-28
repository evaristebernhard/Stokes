import Stokes.Global.ChartwiseSmoothToLocal
import Stokes.Global.CompactOpenBoxSelection

/-!
# Interior finite-box local Stokes pieces

This file records the local conclusion needed after a compact support has been
refined to finitely many interior coordinate boxes: once a localized chart
representative is supported in the strict interior of its selected coordinate
box, its project-local interior contribution is zero.

The finite-cover construction itself stays in `CompactOpenBoxSelection`; the
results here consume the selected box and support hypotheses produced by such a
refinement.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section FiniteBoxCoverInteriorLocalStokes

universe u w c

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type c}

namespace ManifoldForm

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {ρ : M → Real}
variable {x0 x1 : M}
variable {a b : Fin (n + 1) → Real}

/--
Localized project-local artificial boundary terms vanish when the localized
transition-pullback is strictly supported inside the selected interior box.
-/
theorem localized_projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
    (hsupp :
      tsupport
          (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
        boxInteriorSupportBox a b) :
    projectInteriorBoundaryIntegral I x0 x1 (localizedForm I ρ ω) a b = 0 :=
  projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
    I x0 x1 (localizedForm I ρ ω) a b hsupp

/--
Localized project-local bulk terms vanish when local Stokes is available and
the localized transition-pullback is strictly supported inside the selected
interior box.
-/
theorem localized_projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox
    (hbox : interiorChartExtendedBox I x0 x1 (localizedForm I ρ ω) a b)
    (hsupp :
      tsupport
          (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
        boxInteriorSupportBox a b) :
    projectInteriorBulkIntegral I x0 x1 (localizedForm I ρ ω) a b = 0 :=
  projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox
    I x0 x1 (localizedForm I ρ ω) a b hbox hsupp

/--
Turn a selected localized extended box into the existing local Stokes data
package.
-/
def localizedInteriorLocalStokesData_of_extendedBox
    (hbox : interiorChartExtendedBox I x0 x1 (localizedForm I ρ ω) a b) :
    InteriorLocalStokesData I (localizedForm I ρ ω) :=
  InteriorLocalStokesData.ofExtendedBox x0 x1 a b hbox

/-- The local Stokes data built from a strict-support localized box has zero boundary term. -/
theorem localizedInteriorLocalStokesData_artificialBoundaryTerm_eq_zero
    (hbox : interiorChartExtendedBox I x0 x1 (localizedForm I ρ ω) a b)
    (hsupp :
      tsupport
          (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
        boxInteriorSupportBox a b) :
    (localizedInteriorLocalStokesData_of_extendedBox
      (I := I) (ω := ω) (ρ := ρ) (x0 := x0) (x1 := x1)
      (a := a) (b := b) hbox).artificialBoundaryTerm = 0 :=
  InteriorLocalStokesData.artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
    (localizedInteriorLocalStokesData_of_extendedBox
      (I := I) (ω := ω) (ρ := ρ) (x0 := x0) (x1 := x1)
      (a := a) (b := b) hbox)
    hsupp

/-- The local Stokes data built from a strict-support localized box has zero bulk term. -/
theorem localizedInteriorLocalStokesData_bulkTerm_eq_zero
    (hbox : interiorChartExtendedBox I x0 x1 (localizedForm I ρ ω) a b)
    (hsupp :
      tsupport
          (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
        boxInteriorSupportBox a b) :
    (localizedInteriorLocalStokesData_of_extendedBox
      (I := I) (ω := ω) (ρ := ρ) (x0 := x0) (x1 := x1)
      (a := a) (b := b) hbox).bulkTerm = 0 :=
  InteriorLocalStokesData.bulkTerm_eq_zero_of_tsupport_subset_interiorBox
    (localizedInteriorLocalStokesData_of_extendedBox
      (I := I) (ω := ω) (ρ := ρ) (x0 := x0) (x1 := x1)
      (a := a) (b := b) hbox)
    hsupp

end ManifoldForm

namespace LocalizedChartwiseSmoothLocalBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {ρ : M → Real}

/--
A chartwise-smooth localized box with strict interior support has zero recorded
artificial boundary term.
-/
theorem artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
    [IsManifold I ⊤ M]
    (D : LocalizedChartwiseSmoothLocalBoxData I ω ρ)
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart
            (ManifoldForm.localizedForm I ρ ω)) ⊆
        boxInteriorSupportBox D.lowerCorner D.upperCorner) :
    D.localStokesData.artificialBoundaryTerm = 0 :=
  D.localStokesData.artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
    hsupp

/--
A chartwise-smooth localized box with strict interior support has zero recorded
bulk term.
-/
theorem bulkTerm_eq_zero_of_tsupport_subset_interiorBox
    [IsManifold I ⊤ M]
    (D : LocalizedChartwiseSmoothLocalBoxData I ω ρ)
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart
            (ManifoldForm.localizedForm I ρ ω)) ⊆
        boxInteriorSupportBox D.lowerCorner D.upperCorner) :
    D.localStokesData.bulkTerm = 0 :=
  D.localStokesData.bulkTerm_eq_zero_of_tsupport_subset_interiorBox hsupp

end LocalizedChartwiseSmoothLocalBoxData

section FiniteSums

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/--
Finite sum of localized project-local interior bulk terms vanishes when every
active piece is supported strictly inside its selected interior box.
-/
theorem sum_localized_projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox
    (active : Finset ι)
    (x0 x1 : ι → M) (ρ : ι → M → Real)
    (a b : ι → Fin (n + 1) → Real)
    (hbox :
      ∀ i, i ∈ active →
        interiorChartExtendedBox I (x0 i) (x1 i)
          (ManifoldForm.localizedForm I (ρ i) ω) (a i) (b i))
    (hsupp :
      ∀ i, i ∈ active →
        tsupport
            (ManifoldForm.transitionPullbackInChart I (x0 i) (x1 i)
              (ManifoldForm.localizedForm I (ρ i) ω)) ⊆
          boxInteriorSupportBox (a i) (b i)) :
    (∑ i ∈ active,
      projectInteriorBulkIntegral I (x0 i) (x1 i)
        (ManifoldForm.localizedForm I (ρ i) ω) (a i) (b i)) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro i hi
  exact
    ManifoldForm.localized_projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox
      (I := I) (ω := ω) (ρ := ρ i) (x0 := x0 i) (x1 := x1 i)
      (a := a i) (b := b i) (hbox i hi) (hsupp i hi)

/--
Finite sum of localized project-local artificial boundary terms vanishes under
the same strict interior support hypothesis.
-/
theorem sum_localized_projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
    (active : Finset ι)
    (x0 x1 : ι → M) (ρ : ι → M → Real)
    (a b : ι → Fin (n + 1) → Real)
    (hsupp :
      ∀ i, i ∈ active →
        tsupport
            (ManifoldForm.transitionPullbackInChart I (x0 i) (x1 i)
              (ManifoldForm.localizedForm I (ρ i) ω)) ⊆
          boxInteriorSupportBox (a i) (b i)) :
    (∑ i ∈ active,
      projectInteriorBoundaryIntegral I (x0 i) (x1 i)
        (ManifoldForm.localizedForm I (ρ i) ω) (a i) (b i)) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro i hi
  exact
    ManifoldForm.localized_projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
      (I := I) (ω := ω) (ρ := ρ i) (x0 := x0 i) (x1 := x1 i)
      (a := a i) (b := b i) (hsupp i hi)

/--
Finite sum of recorded localized `InteriorLocalStokesData` bulk terms vanishes
when every active data package has strict interior support.
-/
theorem sum_localizedInteriorLocalStokesData_bulkTerm_eq_zero_of_tsupport_subset_interiorBox
    (active : Finset ι) (ρ : ι → M → Real)
    (D : ∀ i : ι, InteriorLocalStokesData I (ManifoldForm.localizedForm I (ρ i) ω))
    (hsupp :
      ∀ i, i ∈ active →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (D i).sourceChart (D i).targetChart
              (ManifoldForm.localizedForm I (ρ i) ω)) ⊆
          boxInteriorSupportBox (D i).lowerCorner (D i).upperCorner) :
    (∑ i ∈ active, (D i).bulkTerm) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro i hi
  exact (D i).bulkTerm_eq_zero_of_tsupport_subset_interiorBox (hsupp i hi)

/--
Finite sum of recorded localized `InteriorLocalStokesData` artificial boundary
terms vanishes when every active data package has strict interior support.
-/
theorem sum_localizedInteriorData_artificialBoundaryTerm_eq_zero_of_strictSupport
    (active : Finset ι) (ρ : ι → M → Real)
    (D : ∀ i : ι, InteriorLocalStokesData I (ManifoldForm.localizedForm I (ρ i) ω))
    (hsupp :
      ∀ i, i ∈ active →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (D i).sourceChart (D i).targetChart
              (ManifoldForm.localizedForm I (ρ i) ω)) ⊆
          boxInteriorSupportBox (D i).lowerCorner (D i).upperCorner) :
    (∑ i ∈ active, (D i).artificialBoundaryTerm) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro i hi
  exact
    (D i).artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
      (hsupp i hi)

/--
Finite sum version specialized to chartwise-smooth localized box data.
-/
theorem sum_localizedChartwiseSmoothLocalBoxData_bulkTerm_eq_zero_of_tsupport_subset_interiorBox
    [IsManifold I ⊤ M]
    (active : Finset ι) (ρ : ι → M → Real)
    (D : ∀ i : ι, LocalizedChartwiseSmoothLocalBoxData I ω (ρ i))
    (hsupp :
      ∀ i, i ∈ active →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (D i).sourceChart (D i).targetChart
              (ManifoldForm.localizedForm I (ρ i) ω)) ⊆
          boxInteriorSupportBox (D i).lowerCorner (D i).upperCorner) :
    (∑ i ∈ active, (D i).localStokesData.bulkTerm) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro i hi
  exact (D i).bulkTerm_eq_zero_of_tsupport_subset_interiorBox (hsupp i hi)

/--
Finite artificial-boundary version specialized to chartwise-smooth localized box
data.
-/
theorem sum_localizedSmoothBoxData_artificialBoundaryTerm_eq_zero_of_strictSupport
    [IsManifold I ⊤ M]
    (active : Finset ι) (ρ : ι → M → Real)
    (D : ∀ i : ι, LocalizedChartwiseSmoothLocalBoxData I ω (ρ i))
    (hsupp :
      ∀ i, i ∈ active →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (D i).sourceChart (D i).targetChart
              (ManifoldForm.localizedForm I (ρ i) ω)) ⊆
          boxInteriorSupportBox (D i).lowerCorner (D i).upperCorner) :
    (∑ i ∈ active, (D i).localStokesData.artificialBoundaryTerm) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro i hi
  exact
    (D i).artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
      (hsupp i hi)

end FiniteSums

end FiniteBoxCoverInteriorLocalStokes

end Stokes

end
