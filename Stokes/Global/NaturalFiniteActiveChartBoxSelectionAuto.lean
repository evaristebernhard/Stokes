import Stokes.Global.NaturalCompactSupportPartitionConstructorAuto

/-!
# Natural finite-active chart-box selection constructors

This module is a narrow automation layer after the genuine geometric choices
have been made.  It does not try to construct a partition of unity.  Instead it
packages the reusable consequences of already chosen compact chart supports,
selected chart boxes, and chart-box smoothness neighborhoods.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped Manifold Topology

namespace Stokes

section ChartImageSelection

universe u v w

variable {ι : Type u} [Fintype ι]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real (ι -> Real) H} {k : Nat}

namespace FiniteActiveOnCompact

/--
Active compact-support data generated from compact manifold-side supports in
chart sources.  The coordinate supports are the compact chart images; the
support containment for the form is the remaining analytic input.
-/
def activeChartCompactSupportDataOfChartCompactImages
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K)
    (ω : ManifoldForm I M k)
    (sourceSupport : M -> Set M)
    (hcompact :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        IsCompact (sourceSupport i))
    (hsource :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        sourceSupport i ⊆ (extChartAt I i).source)
    (htsupport :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          (FiniteActiveOnCompact.activeChartCompactImagesOfCompactSupport
            ρ K hK sourceSupport hcompact hsource).coordSupport i) :
    ActiveChartCompactSupportData
      (FiniteActiveOnCompact.ofCompact ρ K hK) ω :=
  ActiveChartCompactSupportData.ofChartCompactImages
    (FiniteActiveOnCompact.activeChartCompactImagesOfCompactSupport
      ρ K hK sourceSupport hcompact hsource)
    htsupport

@[simp]
theorem activeChartCompactSupportDataOfChartCompactImages_coordSupport
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K)
    (ω : ManifoldForm I M k)
    (sourceSupport : M -> Set M)
    (hcompact :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        IsCompact (sourceSupport i))
    (hsource :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        sourceSupport i ⊆ (extChartAt I i).source)
    (htsupport :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          (FiniteActiveOnCompact.activeChartCompactImagesOfCompactSupport
            ρ K hK sourceSupport hcompact hsource).coordSupport i) :
    (activeChartCompactSupportDataOfChartCompactImages
      (I := I) ρ K hK ω sourceSupport hcompact hsource htsupport).coordSupport =
      (FiniteActiveOnCompact.activeChartCompactImagesOfCompactSupport
        ρ K hK sourceSupport hcompact hsource).coordSupport :=
  rfl

end FiniteActiveOnCompact

namespace CompactSupportFiniteActiveSelection

/--
Compact-support finite-active selection generated from compact source-side
chart supports.  The source supports give compact coordinate images and boxes;
the remaining chart-domain containment is supplied as a fieldized local input.
-/
def ofChartCompactImages
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K)
    (ω : ManifoldForm I M k)
    (sourceSupport : M -> Set M)
    (hcompact :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        IsCompact (sourceSupport i))
    (hsource :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        sourceSupport i ⊆ (extChartAt I i).source)
    (htsupport :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          (FiniteActiveOnCompact.activeChartCompactImagesOfCompactSupport
            ρ K hK sourceSupport hcompact hsource).coordSupport i)
    (hcontain :
      ActiveCompactBoxChartContainment
        (FiniteActiveOnCompact.ofCompact ρ K hK)
        (FiniteActiveOnCompact.activeChartCompactSupportDataOfChartCompactImages
          ρ K hK ω sourceSupport hcompact hsource htsupport).box) :
    CompactSupportFiniteActiveSelection (I := I) ρ K hK ω where
  supportData :=
    FiniteActiveOnCompact.activeChartCompactSupportDataOfChartCompactImages
      ρ K hK ω sourceSupport hcompact hsource htsupport
  containment := hcontain

@[simp]
theorem ofChartCompactImages_supportData
    (ρ : SmoothPartitionOfUnity M I M univ)
    (K : Set M) (hK : IsCompact K)
    (ω : ManifoldForm I M k)
    (sourceSupport : M -> Set M)
    (hcompact :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        IsCompact (sourceSupport i))
    (hsource :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        sourceSupport i ⊆ (extChartAt I i).source)
    (htsupport :
      ∀ i ∈ (FiniteActiveOnCompact.ofCompact ρ K hK).active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          (FiniteActiveOnCompact.activeChartCompactImagesOfCompactSupport
            ρ K hK sourceSupport hcompact hsource).coordSupport i)
    (hcontain :
      ActiveCompactBoxChartContainment
        (FiniteActiveOnCompact.ofCompact ρ K hK)
        (FiniteActiveOnCompact.activeChartCompactSupportDataOfChartCompactImages
          ρ K hK ω sourceSupport hcompact hsource htsupport).box) :
    (ofChartCompactImages ρ K hK ω sourceSupport hcompact hsource
      htsupport hcontain).supportData =
      FiniteActiveOnCompact.activeChartCompactSupportDataOfChartCompactImages
        ρ K hK ω sourceSupport hcompact hsource htsupport :=
  rfl

end CompactSupportFiniteActiveSelection

end ChartImageSelection

section ActiveBoxSmoothness

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [Preorder E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}
variable {P : FiniteActiveOnCompact (M := M) I}
variable {ω : ManifoldForm I M k}

/--
Open smoothness neighborhoods for active selected chart boxes.

Given chartwise smoothness of the form, this is exactly the local geometric
input needed to produce `ActiveCompactBoxSmoothness`: each open neighborhood
contains the selected closed box and lies in the source chart target and the
self-overlap domain.
-/
structure ActiveChartBoxSmoothnessNeighborhoods
    (P : FiniteActiveOnCompact (M := M) I)
    (box : M -> CompactCoordinateBoxSelection E) where
  smoothSet : M -> Set E
  isOpen_smoothSet :
    ∀ i ∈ P.active, IsOpen (smoothSet i)
  Icc_subset_smoothSet :
    ∀ i ∈ P.active, Set.Icc (box i).a (box i).b ⊆ smoothSet i
  smoothSet_subset_target :
    ∀ i ∈ P.active, smoothSet i ⊆ (extChartAt I i).target
  smoothSet_subset_overlap :
    ∀ i ∈ P.active, smoothSet i ⊆ ManifoldForm.chartOverlap I i i

namespace ActiveChartBoxSmoothnessNeighborhoods

variable {box : M -> CompactCoordinateBoxSelection E}

/--
Convert chart-box neighborhoods plus chartwise smoothness into the smoothness
package required by compact active extended boxes.
-/
def toActiveCompactBoxSmoothness [IsManifold I 1 M]
    (N : ActiveChartBoxSmoothnessNeighborhoods (I := I) P box)
    (hω : ManifoldForm.ChartwiseSmooth I ω) :
    ActiveCompactBoxSmoothness P box ω where
  smoothSet := N.smoothSet
  isOpen_smoothSet := N.isOpen_smoothSet
  Icc_subset_smoothSet := N.Icc_subset_smoothSet
  contDiffOn_smoothSet := fun i hi =>
    hω.contDiffOn_transitionPullbackInChart (I := I) i i
      (N.smoothSet_subset_target i hi)
      (N.smoothSet_subset_overlap i hi)

@[simp]
theorem toActiveCompactBoxSmoothness_smoothSet [IsManifold I 1 M]
    (N : ActiveChartBoxSmoothnessNeighborhoods (I := I) P box)
    (hω : ManifoldForm.ChartwiseSmooth I ω) :
    (N.toActiveCompactBoxSmoothness (ω := ω) hω).smoothSet = N.smoothSet :=
  rfl

@[simp]
theorem toActiveCompactBoxSmoothness_isOpen [IsManifold I 1 M]
    (N : ActiveChartBoxSmoothnessNeighborhoods (I := I) P box)
    (hω : ManifoldForm.ChartwiseSmooth I ω) :
    (N.toActiveCompactBoxSmoothness (ω := ω) hω).isOpen_smoothSet =
      N.isOpen_smoothSet :=
  rfl

end ActiveChartBoxSmoothnessNeighborhoods

end ActiveBoxSmoothness

section NaturalFiniteActiveChartBoxSelectionAuto

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {rho : SmoothPartitionOfUnity M I M univ}

namespace CompactlySupportedSmoothFormData

variable
    (formData : CompactlySupportedSmoothFormData I omega)

/--
Build the finite-active compact-support selection over the canonical support
set carried by `formData`, using compact manifold-side supports in active chart
sources.
-/
def finiteActiveSelectionOfChartCompactImages
    (sourceSupport : M -> Set M)
    (hcompact :
      ∀ i,
        i ∈ (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet).active ->
          IsCompact (sourceSupport i))
    (hsource :
      ∀ i,
        i ∈ (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet).active ->
          sourceSupport i ⊆ (extChartAt I i).source)
    (htsupport :
      ∀ i,
        i ∈ (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet).active ->
          tsupport (ManifoldForm.transitionPullbackInChart I i i omega) ⊆
            (FiniteActiveOnCompact.activeChartCompactImagesOfCompactSupport
              rho formData.supportSet formData.isCompact_supportSet
              sourceSupport hcompact hsource).coordSupport i)
    (hcontain :
      ActiveCompactBoxChartContainment
        (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet)
        (FiniteActiveOnCompact.activeChartCompactSupportDataOfChartCompactImages
          rho formData.supportSet formData.isCompact_supportSet omega
          sourceSupport hcompact hsource htsupport).box) :
    CompactSupportFiniteActiveSelection
      (I := I) rho formData.supportSet formData.isCompact_supportSet omega :=
  CompactSupportFiniteActiveSelection.ofChartCompactImages
    rho formData.supportSet formData.isCompact_supportSet omega
    sourceSupport hcompact hsource htsupport hcontain

@[simp]
theorem finiteActiveSelectionOfChartCompactImages_supportData
    (sourceSupport : M -> Set M)
    (hcompact :
      ∀ i,
        i ∈ (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet).active ->
          IsCompact (sourceSupport i))
    (hsource :
      ∀ i,
        i ∈ (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet).active ->
          sourceSupport i ⊆ (extChartAt I i).source)
    (htsupport :
      ∀ i,
        i ∈ (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet).active ->
          tsupport (ManifoldForm.transitionPullbackInChart I i i omega) ⊆
            (FiniteActiveOnCompact.activeChartCompactImagesOfCompactSupport
              rho formData.supportSet formData.isCompact_supportSet
              sourceSupport hcompact hsource).coordSupport i)
    (hcontain :
      ActiveCompactBoxChartContainment
        (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet)
        (FiniteActiveOnCompact.activeChartCompactSupportDataOfChartCompactImages
          rho formData.supportSet formData.isCompact_supportSet omega
          sourceSupport hcompact hsource htsupport).box) :
    (formData.finiteActiveSelectionOfChartCompactImages
      (I := I) (rho := rho) (omega := omega)
      sourceSupport hcompact hsource htsupport hcontain).supportData =
      FiniteActiveOnCompact.activeChartCompactSupportDataOfChartCompactImages
        rho formData.supportSet formData.isCompact_supportSet omega
        sourceSupport hcompact hsource htsupport :=
  rfl

/--
Use the chartwise-smooth field of `formData` to turn selected chart-box
neighborhoods into active box smoothness.
-/
def activeBoxSmoothnessOfNeighborhoods [IsManifold I 1 M]
    (selection :
      CompactSupportFiniteActiveSelection
        (I := I) rho formData.supportSet formData.isCompact_supportSet omega)
    (neighborhoods :
      ActiveChartBoxSmoothnessNeighborhoods
        (I := I) selection.finiteActive selection.supportData.box) :
    ActiveCompactBoxSmoothness selection.finiteActive
      selection.supportData.box omega :=
  neighborhoods.toActiveCompactBoxSmoothness formData.chartwiseSmooth

end CompactlySupportedSmoothFormData

/--
Natural data after compact support, finite active chart boxes, and smoothness
neighborhoods have been selected.

This record is the reusable boundary between geometric selection and the
current endpoint constructors: it derives active box smoothness from
`formData.chartwiseSmooth`, then exposes the existing
`NaturalCompactSupportPartitionConstructorData`.
-/
structure NaturalFiniteActiveChartBoxSelectionData
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (rho : SmoothPartitionOfUnity M I M univ) where
  formData : CompactlySupportedSmoothFormData I omega
  selection :
    CompactSupportFiniteActiveSelection
      (I := I) rho formData.supportSet formData.isCompact_supportSet omega
  neighborhoods :
    ActiveChartBoxSmoothnessNeighborhoods
      (I := I) selection.finiteActive selection.supportData.box

namespace NaturalFiniteActiveChartBoxSelectionData

variable
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)

/-- The canonical compact support set selected by the form data. -/
abbrev supportSet : Set M :=
  D.formData.supportSet

/-- The finite-active package generated by the selected chart boxes. -/
abbrev finiteActive : FiniteActiveOnCompact (M := M) I :=
  D.selection.finiteActive

/-- Compact active boxes generated by the finite-active selection. -/
abbrev compactActiveBoxData : CompactActiveBoxData I omega :=
  D.selection.compactActiveBoxData

/-- Active box smoothness derived from the chartwise smoothness of the form. -/
def smoothness [IsManifold I 1 M] :
    ActiveCompactBoxSmoothness D.selection.finiteActive
      D.selection.supportData.box omega :=
  D.formData.activeBoxSmoothnessOfNeighborhoods D.selection D.neighborhoods

/-- The selected partition generated from the selected boxes and smoothness. -/
abbrev selectedPartition [IsManifold I 1 M] :
    SelectedBoxPartitionOfUnity I omega :=
  D.selection.selectedBoxPartitionOfUnity D.smoothness

@[simp]
theorem selectedPartition_K [IsManifold I 1 M] :
    D.selectedPartition.K = D.formData.supportSet :=
  rfl

/-- The original form support is contained in the selected compact support. -/
theorem omegaSupport_subset_selected [IsManifold I 1 M] :
    ManifoldForm.support I omega ⊆ D.selectedPartition.K := by
  simpa [selectedPartition_K] using D.formData.support_subset_supportSet

/--
Expose the existing natural compact-support selected-partition constructor.
-/
def toPartitionConstructorData [IsManifold I 1 M] :
    NaturalCompactSupportPartitionConstructorData I omega rho where
  formData := D.formData
  selection := D.selection
  smoothness := D.smoothness

@[simp]
theorem toPartitionConstructorData_formData [IsManifold I 1 M] :
    D.toPartitionConstructorData.formData = D.formData :=
  rfl

@[simp]
theorem toPartitionConstructorData_selection [IsManifold I 1 M] :
    D.toPartitionConstructorData.selection = D.selection :=
  rfl

@[simp]
theorem toPartitionConstructorData_selectedPartition [IsManifold I 1 M] :
    D.toPartitionConstructorData.selectedPartition = D.selectedPartition :=
  rfl

end NaturalFiniteActiveChartBoxSelectionData

namespace CompactlySupportedSmoothFormData

variable
    (formData : CompactlySupportedSmoothFormData I omega)

/-- Natural finite-active chart-box data from an already built selection. -/
def naturalFiniteActiveChartBoxSelectionOfSelection
    (selection :
      CompactSupportFiniteActiveSelection
        (I := I) rho formData.supportSet formData.isCompact_supportSet omega)
    (neighborhoods :
      ActiveChartBoxSmoothnessNeighborhoods
        (I := I) selection.finiteActive selection.supportData.box) :
    NaturalFiniteActiveChartBoxSelectionData I omega rho where
  formData := formData
  selection := selection
  neighborhoods := neighborhoods

/--
Natural finite-active chart-box data from explicit compact coordinate supports.
-/
def naturalFiniteActiveChartBoxSelectionOfCoordSupport
    (coordSupport : M -> Set (Fin (n + 1) -> Real))
    (hcompact :
      ∀ i,
        i ∈ (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet).active ->
          IsCompact (coordSupport i))
    (hsupp :
      ∀ i,
        i ∈ (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet).active ->
          tsupport (ManifoldForm.transitionPullbackInChart I i i omega) ⊆
            coordSupport i)
    (hcontain :
      ActiveCompactBoxChartContainment
        (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet)
        (FiniteActiveOnCompact.activeChartCompactSupportDataOfCompactSupport
          rho formData.supportSet formData.isCompact_supportSet omega
          coordSupport hcompact hsupp).box)
    (neighborhoods :
      ActiveChartBoxSmoothnessNeighborhoods
        (I := I)
        (formData.finiteActiveSelectionOfCoordSupport
          (I := I) (rho := rho) (omega := omega)
          coordSupport hcompact hsupp hcontain).finiteActive
        (formData.finiteActiveSelectionOfCoordSupport
          (I := I) (rho := rho) (omega := omega)
          coordSupport hcompact hsupp hcontain).supportData.box) :
    NaturalFiniteActiveChartBoxSelectionData I omega rho :=
  formData.naturalFiniteActiveChartBoxSelectionOfSelection
    (rho := rho)
    (formData.finiteActiveSelectionOfCoordSupport
      (I := I) (rho := rho) (omega := omega)
      coordSupport hcompact hsupp hcontain)
    neighborhoods

/--
Natural finite-active chart-box data from compact manifold-side chart supports.
-/
def naturalFiniteActiveChartBoxSelectionOfChartCompactImages
    (sourceSupport : M -> Set M)
    (hcompact :
      ∀ i,
        i ∈ (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet).active ->
          IsCompact (sourceSupport i))
    (hsource :
      ∀ i,
        i ∈ (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet).active ->
          sourceSupport i ⊆ (extChartAt I i).source)
    (htsupport :
      ∀ i,
        i ∈ (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet).active ->
          tsupport (ManifoldForm.transitionPullbackInChart I i i omega) ⊆
            (FiniteActiveOnCompact.activeChartCompactImagesOfCompactSupport
              rho formData.supportSet formData.isCompact_supportSet
              sourceSupport hcompact hsource).coordSupport i)
    (hcontain :
      ActiveCompactBoxChartContainment
        (FiniteActiveOnCompact.ofCompact rho formData.supportSet
          formData.isCompact_supportSet)
        (FiniteActiveOnCompact.activeChartCompactSupportDataOfChartCompactImages
          rho formData.supportSet formData.isCompact_supportSet omega
          sourceSupport hcompact hsource htsupport).box)
    (neighborhoods :
      ActiveChartBoxSmoothnessNeighborhoods
        (I := I)
        (formData.finiteActiveSelectionOfChartCompactImages
          (I := I) (rho := rho) (omega := omega)
          sourceSupport hcompact hsource htsupport hcontain).finiteActive
        (formData.finiteActiveSelectionOfChartCompactImages
          (I := I) (rho := rho) (omega := omega)
          sourceSupport hcompact hsource htsupport hcontain).supportData.box) :
    NaturalFiniteActiveChartBoxSelectionData I omega rho :=
  formData.naturalFiniteActiveChartBoxSelectionOfSelection
    (rho := rho)
    (formData.finiteActiveSelectionOfChartCompactImages
      (I := I) (rho := rho) (omega := omega)
      sourceSupport hcompact hsource htsupport hcontain)
    neighborhoods

end CompactlySupportedSmoothFormData

end NaturalFiniteActiveChartBoxSelectionAuto

end Stokes

end
