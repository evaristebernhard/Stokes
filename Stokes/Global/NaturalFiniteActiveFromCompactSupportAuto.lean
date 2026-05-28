import Stokes.Global.NaturalFiniteActiveChartBoxSelectionAuto
import Stokes.Global.PartitionCompactSupport

/-!
# Natural finite-active chart-box data from compact-support source packages

This module moves the finite-active chart-box constructor one layer upstream.
Instead of asking callers to repeatedly pass the raw `sourceSupport`,
`coordSupport`, compactness, and selected-box containment fields, it packages
the chart-source compact supports and their selected boxes once, then projects
the existing `NaturalFiniteActiveChartBoxSelectionData`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped Manifold Topology

namespace Stokes

section NaturalFiniteActiveFromCompactSupportAuto

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {rho : SmoothPartitionOfUnity M I M univ}

/--
The compact-support finite-active package determined by `formData` and `rho`.
This abbreviation keeps later theorem statements from exposing the raw
`FiniteActiveOnCompact.ofCompact ...` expression.
-/
abbrev CompactlySupportedSmoothFormData.finiteActiveOnSupport
    (formData : CompactlySupportedSmoothFormData I omega) :
    FiniteActiveOnCompact (M := M) I :=
  FiniteActiveOnCompact.ofCompact rho formData.supportSet
    formData.isCompact_supportSet

namespace CompactlySupportedSmoothFormData

variable
    (formData : CompactlySupportedSmoothFormData I omega)

/--
Compact chart-source supports over the canonical compact support of
`formData`.

The field is an `ActiveChartCompactImages` package rather than four unrelated
functions/proofs: it already stores the manifold-side compact sets and the
chart-continuity facts needed to make compact coordinate images.
-/
structure SourceChartCompactImagesOnSupport where
  /-- Active manifold-side compact supports and their chart images. -/
  chartImages :
    ActiveChartCompactImages (I := I)
      (formData.finiteActiveOnSupport (rho := rho))

namespace SourceChartCompactImagesOnSupport

variable {formData}

/-- Constructor from explicit compact source sets contained in chart sources. -/
def ofSourceSupports
    (sourceSupport : M -> Set M)
    (hcompact :
      forall i,
        i ∈ (formData.finiteActiveOnSupport (rho := rho)).active ->
          IsCompact (sourceSupport i))
    (hsource :
      forall i,
        i ∈ (formData.finiteActiveOnSupport (rho := rho)).active ->
          sourceSupport i ⊆ (extChartAt I i).source) :
    SourceChartCompactImagesOnSupport
      (rho := rho) formData where
  chartImages :=
    ActiveChartCompactImages.ofSubsetSource
      (I := I)
      (P := formData.finiteActiveOnSupport (rho := rho))
      sourceSupport hcompact hsource

/-- The generated coordinate support family. -/
abbrev coordSupport
    (S :
      SourceChartCompactImagesOnSupport
        (rho := rho) formData) :
    M -> Set (Fin (n + 1) -> Real) :=
  S.chartImages.coordSupport

/-- The selected compact coordinate boxes generated from the source supports. -/
abbrev box
    (S :
      SourceChartCompactImagesOnSupport
        (rho := rho) formData) :
    M -> CompactCoordinateBoxSelection (Fin (n + 1) -> Real) :=
  S.chartImages.box

/-- Compactness of each active coordinate image. -/
theorem isCompact_coordSupport
    (S :
      SourceChartCompactImagesOnSupport
        (rho := rho) formData)
    {i : M} (hi : i ∈ (formData.finiteActiveOnSupport (rho := rho)).active) :
    IsCompact (S.coordSupport i) :=
  S.chartImages.isCompact_coordSupport hi

/-- The generated boxes package the generated coordinate supports. -/
@[simp]
theorem box_K_eq_coordSupport
    (S :
      SourceChartCompactImagesOnSupport
        (rho := rho) formData)
    {i : M} (hi : i ∈ (formData.finiteActiveOnSupport (rho := rho)).active) :
    (S.box i).K = S.coordSupport i :=
  S.chartImages.box_K_eq_coordSupport hi

/-- Coordinate supports lie in their selected closed boxes. -/
theorem coordSupport_subset_box
    (S :
      SourceChartCompactImagesOnSupport
        (rho := rho) formData)
    {i : M} (hi : i ∈ (formData.finiteActiveOnSupport (rho := rho)).active) :
    S.coordSupport i ⊆ Set.Icc (S.box i).a (S.box i).b :=
  S.chartImages.coordSupport_subset_box hi

end SourceChartCompactImagesOnSupport

/--
Source compact supports plus the remaining selected-box data needed to build
the current finite-active chart-box selection.

The only analytic field left here is support containment of the chart
representative in the generated coordinate image.  The selected-box target /
overlap and smoothness-neighborhood data are grouped against the generated
boxes, so downstream constructors no longer mention raw source-support or
coordinate-support functions.
-/
structure NaturalFiniteActiveFromCompactSupportData where
  /-- Compact source supports and compact coordinate images for active charts. -/
  source :
    SourceChartCompactImagesOnSupport
      (rho := rho) formData
  /-- Base chart representatives are supported in the generated coordinate images. -/
  tsupport_subset_coordSupport :
    forall i,
      i ∈ (formData.finiteActiveOnSupport (rho := rho)).active ->
        tsupport (ManifoldForm.transitionPullbackInChart I i i omega) ⊆
          source.coordSupport i
  /-- Target and self-overlap containments for the generated selected boxes. -/
  containment :
    ActiveCompactBoxChartContainment
      (formData.finiteActiveOnSupport (rho := rho)) source.box
  /-- Smoothness neighborhoods for the generated selected boxes. -/
  neighborhoods :
    ActiveChartBoxSmoothnessNeighborhoods
      (I := I) (formData.finiteActiveOnSupport (rho := rho)) source.box

namespace NaturalFiniteActiveFromCompactSupportData

variable {formData}

/-- Active compact coordinate-support data generated from the source package. -/
def toActiveChartCompactSupportData
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    ActiveChartCompactSupportData
      (formData.finiteActiveOnSupport (rho := rho)) omega :=
  ActiveChartCompactSupportData.ofChartCompactImages
    D.source.chartImages D.tsupport_subset_coordSupport

@[simp]
theorem toActiveChartCompactSupportData_coordSupport
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toActiveChartCompactSupportData.coordSupport =
      D.source.coordSupport := by
  rfl

@[simp]
theorem toActiveChartCompactSupportData_box
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toActiveChartCompactSupportData.box = D.source.box := by
  rfl

/--
Localized compact-support data for partition-localized representatives,
projected from the same base compact supports.
-/
def toActiveLocalizedChartCompactSupportData
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    ActiveLocalizedChartCompactSupportData
      (formData.finiteActiveOnSupport (rho := rho)) omega :=
  ActiveLocalizedChartCompactSupportData.ofBase
    D.source.coordSupport
    (fun _ hi => D.source.isCompact_coordSupport hi)
    D.tsupport_subset_coordSupport

@[simp]
theorem toActiveLocalizedChartCompactSupportData_coordSupport
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toActiveLocalizedChartCompactSupportData.coordSupport =
      D.source.coordSupport := by
  rfl

/-- Compact active box data generated by the packaged source supports. -/
def toCompactActiveBoxData
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    CompactActiveBoxData I omega :=
  D.toActiveChartCompactSupportData.toCompactActiveBoxDataOfContainment
    (by simpa [toActiveChartCompactSupportData_box] using D.containment)

@[simp]
theorem toCompactActiveBoxData_finiteActive
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toCompactActiveBoxData.finiteActive =
      formData.finiteActiveOnSupport (rho := rho) := by
  rfl

@[simp]
theorem toCompactActiveBoxData_coordSupport
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toCompactActiveBoxData.coordSupport =
      D.source.coordSupport := by
  rfl

@[simp]
theorem toCompactActiveBoxData_box
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toCompactActiveBoxData.box = D.source.box := by
  rfl

/-- Finite-active selection over `formData.supportSet`. -/
def toFiniteActiveSelection
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    CompactSupportFiniteActiveSelection
      (I := I) rho formData.supportSet formData.isCompact_supportSet omega where
  supportData := D.toActiveChartCompactSupportData
  containment := by
    simpa [toActiveChartCompactSupportData_box] using D.containment

@[simp]
theorem toFiniteActiveSelection_supportData
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toFiniteActiveSelection.supportData =
      D.toActiveChartCompactSupportData := by
  rfl

@[simp]
theorem toFiniteActiveSelection_finiteActive
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toFiniteActiveSelection.finiteActive =
      formData.finiteActiveOnSupport (rho := rho) := by
  rfl

/-- Natural finite-active chart-box data generated from the compact-source package. -/
def toNaturalFiniteActiveChartBoxSelectionData
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    NaturalFiniteActiveChartBoxSelectionData I omega rho where
  formData := formData
  selection := D.toFiniteActiveSelection
  neighborhoods := by
    simpa [toFiniteActiveSelection_supportData, toActiveChartCompactSupportData_box]
      using D.neighborhoods

@[simp]
theorem toNaturalFiniteActiveChartBoxSelectionData_formData
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toNaturalFiniteActiveChartBoxSelectionData.formData = formData := by
  rfl

@[simp]
theorem toNaturalFiniteActiveChartBoxSelectionData_selection
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toNaturalFiniteActiveChartBoxSelectionData.selection =
      D.toFiniteActiveSelection := by
  rfl

@[simp]
theorem toNaturalFiniteActiveChartBoxSelectionData_selectedPartition
    [IsManifold I 1 M]
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toNaturalFiniteActiveChartBoxSelectionData.selectedPartition =
      D.toFiniteActiveSelection.selectedBoxPartitionOfUnity
        (D.neighborhoods.toActiveCompactBoxSmoothness formData.chartwiseSmooth) := by
  rfl

/-- Projection to the selected-partition constructor layer. -/
def toPartitionConstructorData [IsManifold I 1 M]
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    NaturalCompactSupportPartitionConstructorData I omega rho :=
  D.toNaturalFiniteActiveChartBoxSelectionData.toPartitionConstructorData

@[simp]
theorem toPartitionConstructorData_selection [IsManifold I 1 M]
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    D.toPartitionConstructorData.selection = D.toFiniteActiveSelection := by
  rfl

end NaturalFiniteActiveFromCompactSupportData

/--
Direct constructor for natural finite-active chart-box data from a packaged
compact-source selection.
-/
def naturalFiniteActiveChartBoxSelectionOfCompactSourceData
    (D :
      NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData) :
    NaturalFiniteActiveChartBoxSelectionData I omega rho :=
  D.toNaturalFiniteActiveChartBoxSelectionData

/--
Direct constructor from explicit chart-source compact supports, with all later
fields typed against the generated compact-source package.
-/
def naturalFiniteActiveChartBoxSelectionOfSourceSupports
    (sourceSupport : M -> Set M)
    (hcompact :
      forall i,
        i ∈ (formData.finiteActiveOnSupport (rho := rho)).active ->
          IsCompact (sourceSupport i))
    (hsource :
      forall i,
        i ∈ (formData.finiteActiveOnSupport (rho := rho)).active ->
          sourceSupport i ⊆ (extChartAt I i).source)
    (htsupport :
      let source :=
        SourceChartCompactImagesOnSupport.ofSourceSupports
          (rho := rho) (formData := formData)
          sourceSupport hcompact hsource
      forall i,
        i ∈ (formData.finiteActiveOnSupport (rho := rho)).active ->
          tsupport (ManifoldForm.transitionPullbackInChart I i i omega) ⊆
            source.coordSupport i)
    (hcontain :
      let source :=
        SourceChartCompactImagesOnSupport.ofSourceSupports
          (rho := rho) (formData := formData)
          sourceSupport hcompact hsource
      ActiveCompactBoxChartContainment
        (formData.finiteActiveOnSupport (rho := rho)) source.box)
    (neighborhoods :
      let source :=
        SourceChartCompactImagesOnSupport.ofSourceSupports
          (rho := rho) (formData := formData)
          sourceSupport hcompact hsource
      ActiveChartBoxSmoothnessNeighborhoods
        (I := I) (formData.finiteActiveOnSupport (rho := rho)) source.box) :
    NaturalFiniteActiveChartBoxSelectionData I omega rho := by
  let source :=
    SourceChartCompactImagesOnSupport.ofSourceSupports
      (rho := rho) (formData := formData)
      sourceSupport hcompact hsource
  exact
    (NaturalFiniteActiveFromCompactSupportData.mk
      (formData := formData) source htsupport hcontain neighborhoods)
      |>.toNaturalFiniteActiveChartBoxSelectionData

end CompactlySupportedSmoothFormData

end NaturalFiniteActiveFromCompactSupportAuto

end Stokes

end
