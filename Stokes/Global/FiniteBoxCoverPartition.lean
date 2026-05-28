import Stokes.Global.PartitionCompactSupport
import Stokes.Global.CompactSupportFiniteActiveSelection
import Stokes.Global.ChartCompactImage
import Stokes.Global.CompactOpenBoxSelection

/-!
# Support-controlled localization from finite box covers

This file proves the conditional support lemma needed after replacing a false
single-box compact-open statement by a finite box cover.  It does not construct
a smooth partition subordinate to that cover.  Instead, it records the honest
input such a construction must provide: on the compact coordinate support, each
partition coefficient is supported inside its assigned strict coordinate box.

The main conclusion is that the chart representative of the localized form
inherits that same strict-box support.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section Core

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n k : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 i : M}
variable {ρ : M → Real}
variable {ω : ManifoldForm I M k}
variable {a b : Fin (n + 1) → Real}

namespace ManifoldForm

/--
If the intersection of the transition coefficient support and the base form
support is contained in a strict coordinate box, then the localized
transition-pullback representative is supported in that strict box.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_inter
    (hinter :
      tsupport (transitionCoefficientInChart I x0 x1 ρ) ∩
          tsupport (transitionPullbackInChart I x0 x1 ω) ⊆
        boxInteriorSupportBox a b) :
    tsupport (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      boxInteriorSupportBox a b := by
  intro y hy
  exact hinter
    ⟨transitionPullbackInChart_localizedForm_tsupport_subset_coefficient
        (I := I) x0 x1 ρ ω hy,
      transitionPullbackInChart_localizedForm_tsupport_subset_form
        (I := I) x0 x1 ρ ω hy⟩

/--
Coordinate-support version of the preceding theorem.  This is the form used
after a compact support has been mapped into a chart: the base representative
is controlled by a coordinate support `C`, and the coefficient is subordinate
to the assigned strict box on `C`.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coordSupport
    {C : Set (Fin (n + 1) → Real)}
    (hbase : tsupport (transitionPullbackInChart I x0 x1 ω) ⊆ C)
    (hcoeff :
      tsupport (transitionCoefficientInChart I x0 x1 ρ) ∩ C ⊆
        boxInteriorSupportBox a b) :
    tsupport (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      boxInteriorSupportBox a b := by
  refine
    transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_inter
      (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
      (a := a) (b := b) ?_
  intro y hy
  exact hcoeff ⟨hy.1, hbase hy.2⟩

/--
Specialization where the coordinate support is the image of a compact
manifold-side set under the source chart.
-/
theorem transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_chartImage
    {K : Set M}
    (hbase :
      tsupport (transitionPullbackInChart I x0 x1 ω) ⊆
        chartCoordinateImage I x0 K)
    (hcoeff :
      tsupport (transitionCoefficientInChart I x0 x1 ρ) ∩
          chartCoordinateImage I x0 K ⊆
        boxInteriorSupportBox a b) :
    tsupport (transitionPullbackInChart I x0 x1 (localizedForm I ρ ω)) ⊆
      boxInteriorSupportBox a b :=
  transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coordSupport
    (I := I) (x0 := x0) (x1 := x1) (ρ := ρ) (ω := ω)
    (a := a) (b := b) hbase hcoeff

end ManifoldForm

end Core

section FiniteActive

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n k : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {P : FiniteActiveOnCompact (M := M) I}
variable {ω : ManifoldForm I M k}

namespace FiniteActiveOnCompact

/--
Finite-active partition version with an arbitrary coordinate support family.
For each active index, if the base chart representative is supported in
`coordSupport i` and the coefficient is subordinate to the strict box on that
coordinate support, then the localized representative is supported in the box.
-/
theorem localized_transitionPullback_tsupport_subset_interiorBox_of_coordSupport
    (P : FiniteActiveOnCompact (M := M) I)
    {coordSupport : M → Set (Fin (n + 1) → Real)}
    {lower upper : M → Fin (n + 1) → Real}
    (hbase :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          coordSupport i)
    (hcoeff :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionCoefficientInChart I i i (P.partition i)) ∩
            coordSupport i ⊆
          boxInteriorSupportBox (lower i) (upper i))
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      boxInteriorSupportBox (lower i) (upper i) :=
  ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coordSupport
      (I := I) (x0 := i) (x1 := i) (ρ := P.partition i) (ω := ω)
      (a := lower i) (b := upper i) (hbase i hi) (hcoeff i hi)

/--
Version whose coordinate support is the chart image of the finite-active
compact control set `P.K`.
-/
theorem localized_transitionPullback_tsupport_subset_interiorBox_of_chartCoordinateImage
    (P : FiniteActiveOnCompact (M := M) I)
    {lower upper : M → Fin (n + 1) → Real}
    (hbase :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          chartCoordinateImage I i P.K)
    (hcoeff :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionCoefficientInChart I i i (P.partition i)) ∩
            chartCoordinateImage I i P.K ⊆
          boxInteriorSupportBox (lower i) (upper i))
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      boxInteriorSupportBox (lower i) (upper i) :=
  P.localized_transitionPullback_tsupport_subset_interiorBox_of_coordSupport
    (ω := ω) (coordSupport := fun i => chartCoordinateImage I i P.K)
    (lower := lower) (upper := upper) hbase hcoeff hi

/--
The same statement phrased directly as the intersection-control condition
already exposed by `PartitionCompactSupport`.
-/
theorem localized_transitionPullback_tsupport_subset_interiorBox_of_inter
    (P : FiniteActiveOnCompact (M := M) I)
    {lower upper : M → Fin (n + 1) → Real}
    (hinter :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionCoefficientInChart I i i (P.partition i)) ∩
            tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          boxInteriorSupportBox (lower i) (upper i))
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      boxInteriorSupportBox (lower i) (upper i) :=
  ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_inter
    (I := I) (x0 := i) (x1 := i) (ρ := P.partition i) (ω := ω)
    (a := lower i) (b := upper i) (hinter i hi)

end FiniteActiveOnCompact

end FiniteActive

section SelectedPartition

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n k : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M k}

namespace SelectedBoxPartitionOfUnity

/--
Selected-partition wrapper for finite-cover subordinate coefficients.
-/
theorem localized_transitionPullback_tsupport_subset_interiorBox_of_coordSupport
    (P : SelectedBoxPartitionOfUnity I ω)
    {coordSupport : M → Set (Fin (n + 1) → Real)}
    {lower upper : M → Fin (n + 1) → Real}
    (hbase :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          coordSupport i)
    (hcoeff :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionCoefficientInChart I i i (P.partition i)) ∩
            coordSupport i ⊆
          boxInteriorSupportBox (lower i) (upper i))
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      boxInteriorSupportBox (lower i) (upper i) :=
  P.toFiniteActiveOnCompact
    |>.localized_transitionPullback_tsupport_subset_interiorBox_of_coordSupport
      (ω := ω) (coordSupport := coordSupport) (lower := lower)
      (upper := upper) hbase hcoeff hi

/--
Selected-partition chart-image version with the selected compact set `P.K`.
-/
theorem localized_transitionPullback_tsupport_subset_interiorBox_of_chartCoordinateImage
    (P : SelectedBoxPartitionOfUnity I ω)
    {lower upper : M → Fin (n + 1) → Real}
    (hbase :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          chartCoordinateImage I i P.K)
    (hcoeff :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionCoefficientInChart I i i (P.partition i)) ∩
            chartCoordinateImage I i P.K ⊆
          boxInteriorSupportBox (lower i) (upper i))
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      boxInteriorSupportBox (lower i) (upper i) :=
  P.toFiniteActiveOnCompact
    |>.localized_transitionPullback_tsupport_subset_interiorBox_of_chartCoordinateImage
      (ω := ω) (lower := lower) (upper := upper) hbase hcoeff hi

/--
If the support-control box is the selected box already stored in `P`, the
localized representative has strict-box support in that selected box.
-/
theorem localized_transitionPullback_tsupport_subset_selected_interiorBox_of_chartCoordinateImage
    (P : SelectedBoxPartitionOfUnity I ω)
    (hbase :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          chartCoordinateImage I i P.K)
    (hcoeff :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionCoefficientInChart I i i (P.partition i)) ∩
            chartCoordinateImage I i P.K ⊆
          boxInteriorSupportBox (P.lower i) (P.upper i))
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      boxInteriorSupportBox (P.lower i) (P.upper i) :=
  P.localized_transitionPullback_tsupport_subset_interiorBox_of_chartCoordinateImage
    (ω := ω) (lower := P.lower) (upper := P.upper) hbase hcoeff hi

end SelectedBoxPartitionOfUnity

end SelectedPartition

section CompactlySupportedFormData

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

namespace CompactlySupportedSmoothFormData

/--
Compact-support input version.  Given support-control of the coefficient over
the coordinate image of `formData.supportSet`, the localized chart
representative is supported in its assigned strict box.
-/
theorem localized_transitionPullback_tsupport_subset_interiorBox_of_chartCoordinateImage
    (formData : CompactlySupportedSmoothFormData I ω)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {lower upper : M → Fin (n + 1) → Real}
    (hbase :
      ∀ i ∈ (formData.finiteActiveOfPartition ρ).active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          chartCoordinateImage I i formData.supportSet)
    (hcoeff :
      ∀ i ∈ (formData.finiteActiveOfPartition ρ).active,
        tsupport (ManifoldForm.transitionCoefficientInChart I i i (ρ i)) ∩
            chartCoordinateImage I i formData.supportSet ⊆
          boxInteriorSupportBox (lower i) (upper i))
    {i : M} (hi : i ∈ (formData.finiteActiveOfPartition ρ).active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (ρ i) ω)) ⊆
      boxInteriorSupportBox (lower i) (upper i) := by
  simpa [finiteActiveOfPartition] using
    (formData.finiteActiveOfPartition ρ)
      |>.localized_transitionPullback_tsupport_subset_interiorBox_of_chartCoordinateImage
        (ω := ω) (lower := lower) (upper := upper) hbase hcoeff hi

end CompactlySupportedSmoothFormData

end CompactlySupportedFormData

end Stokes

end
