import Stokes.Global.NaturalCompactSupportEndpointNaturalInputAuto
import Stokes.Global.NaturalStrictAlignmentFromFiniteSelectionAuto
import Stokes.Global.SelectedStrictMarginsFromChartBoxAuto

/-!
# Natural endpoint strict-alignment routes

This module connects the natural endpoint layer to the strict-alignment and
chart-box-containment routes.

The new declarations do not prove new analysis.  They remove theorem-facing
plumbing in two common situations:

* a caller already has `NaturalFiniteActiveStrictAlignmentData`;
* a caller has chart-box strict containment rather than two pointwise strict
  margin inequalities.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalEndpointStrictAlignmentRouteAuto

universe u w b a ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {alpha : Type a} [TopologicalSpace alpha] [MeasurableSpace alpha]
variable [OpensMeasurableSpace alpha] [T2Space alpha]
variable {muAlpha : Measure alpha} [IsFiniteMeasureOnCompacts muAlpha]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {rho : SmoothPartitionOfUnity M I M univ}
variable [IsManifold I 1 M]

namespace NaturalFiniteActiveStrictAlignmentData

variable
    (D :
      NaturalFiniteActiveStrictAlignmentData
        (alpha := alpha) I omega BoundaryPiece rho muAlpha)

/-- Canonical integral interface exposed by the strict-alignment route. -/
abbrev canonicalIntegralInterface :
    CanonicalIntegralInterface I omega :=
  D.toNaturalCompactSupportStokesInput.canonicalIntegralInterface

/-- The strict-alignment route displayed as the canonical equality. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [canonicalIntegralInterface, CanonicalIntegralInterface.stokesStatement]
    using D.canonical_stokes

/--
Chart-box containment specialized to the strict-alignment route.

This is the geometric input form callers usually have before converting to
`SelectedBoxStrictMarginData`.
-/
abbrev ChartBoxStrictContainmentData :=
  SelectedBoxChartBoxStrictContainmentData
    D.selectedPartition D.targetImageInput.targetImages
    D.measureBuilder.toM8MeasureLocalizationData

/-- Strict margins generated from chart-box containment. -/
def strictMarginsOfChartBoxContainment
    (C : D.ChartBoxStrictContainmentData) :
    SelectedBoxStrictMarginData D.selectedPartition
      D.targetImageInput.targetImages
      D.measureBuilder.toM8MeasureLocalizationData :=
  C.toSelectedBoxStrictMarginData

/--
Replace the strict-margin field of a strict-alignment route by one generated
from chart-box containment.
-/
def replaceStrictMarginsOfChartBoxContainment
    (C : D.ChartBoxStrictContainmentData) :
    NaturalFiniteActiveStrictAlignmentData
      (alpha := alpha) I omega BoundaryPiece rho muAlpha where
  finiteSelection := D.finiteSelection
  orientedBoundaryAtlas := D.orientedBoundaryAtlas
  targetImageInput := D.targetImageInput
  globalBulkIntegral := D.globalBulkIntegral
  bulk := D.bulk
  boundaryTarget := D.boundaryTarget
  localizedChartAlignment := D.localizedChartAlignment
  strictMargins := D.strictMarginsOfChartBoxContainment C

@[simp]
theorem replaceStrictMarginsOfChartBoxContainment_finiteSelection
    (C : D.ChartBoxStrictContainmentData) :
    (D.replaceStrictMarginsOfChartBoxContainment C).finiteSelection =
      D.finiteSelection := by
  rfl

@[simp]
theorem replaceStrictMarginsOfChartBoxContainment_strictMargins
    (C : D.ChartBoxStrictContainmentData) :
    (D.replaceStrictMarginsOfChartBoxContainment C).strictMargins =
      D.strictMarginsOfChartBoxContainment C := by
  rfl

/-- Canonical Stokes from a strict-alignment route whose margins are supplied by containment. -/
theorem canonical_stokes_ofChartBoxContainment
    (C : D.ChartBoxStrictContainmentData) :
    (D.replaceStrictMarginsOfChartBoxContainment C)
      |>.canonicalIntegralInterface
      |>.stokesStatement :=
  (D.replaceStrictMarginsOfChartBoxContainment C).canonical_stokes

/--
Canonical equality from a strict-alignment route whose margins are supplied by
chart-box containment.
-/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofChartBoxContainment
    (C : D.ChartBoxStrictContainmentData) :
    ((D.replaceStrictMarginsOfChartBoxContainment C)
      |>.canonicalIntegralInterface
      |>.manifoldExtDerivIntegral) =
    ((D.replaceStrictMarginsOfChartBoxContainment C)
      |>.canonicalIntegralInterface
      |>.boundaryFormIntegral) := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    D.canonical_stokes_ofChartBoxContainment C

end NaturalFiniteActiveStrictAlignmentData

namespace NaturalFiniteActiveChartBoxSelectionData

variable
    (D : NaturalFiniteActiveChartBoxSelectionData I omega rho)
variable
    (orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M)
    (targetImageInput :
      M8TargetImageInput I omega D.selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    {globalBulkIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData
        (α := alpha) (μ := muAlpha)
        D.selectedPartition targetImageInput.targetImages globalBulkIntegral)
    (boundaryTarget :
      CanonicalBoundaryTargetCompactSupportInput
        (α := alpha) targetImageInput muAlpha)

/-- Chart-box containment in the measure-localization package induced by the selected route. -/
abbrev ChartBoxStrictContainmentData :=
  SelectedBoxChartBoxStrictContainmentData
    D.selectedPartition targetImageInput.targetImages
    (boundaryTarget.toMeasureBuilderData bulk).toM8MeasureLocalizationData

/--
Strict-alignment data generated from finite-active chart boxes and chart-box
containment.
-/
def toStrictAlignmentDataOfChartBoxContainment
    (localizedChartAlignment :
      LocalizedInteriorM8ChartAlignment bulk.localized)
    (containment :
      D.ChartBoxStrictContainmentData
        orientedBoundaryAtlas targetImageInput bulk boundaryTarget) :
    NaturalFiniteActiveStrictAlignmentData
      (alpha := alpha) I omega BoundaryPiece rho muAlpha :=
  D.toStrictAlignmentData
    orientedBoundaryAtlas targetImageInput bulk boundaryTarget
    localizedChartAlignment containment.toSelectedBoxStrictMarginData

/-- Canonical Stokes from finite-active chart boxes and chart-box containment. -/
theorem canonical_stokes_ofChartBoxContainment
    (localizedChartAlignment :
      LocalizedInteriorM8ChartAlignment bulk.localized)
    (containment :
      D.ChartBoxStrictContainmentData
        orientedBoundaryAtlas targetImageInput bulk boundaryTarget) :
    ((D.toStrictAlignmentDataOfChartBoxContainment
        orientedBoundaryAtlas targetImageInput bulk boundaryTarget
        localizedChartAlignment containment)
        |>.canonicalIntegralInterface
        |>.stokesStatement) :=
  (D.toStrictAlignmentDataOfChartBoxContainment
    orientedBoundaryAtlas targetImageInput bulk boundaryTarget
    localizedChartAlignment containment)
    |>.canonical_stokes

/-- Canonical equality from finite-active chart boxes and chart-box containment. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofChartBoxContainment
    (localizedChartAlignment :
      LocalizedInteriorM8ChartAlignment bulk.localized)
    (containment :
      D.ChartBoxStrictContainmentData
        orientedBoundaryAtlas targetImageInput bulk boundaryTarget) :
    ((D.toStrictAlignmentDataOfChartBoxContainment
        orientedBoundaryAtlas targetImageInput bulk boundaryTarget
        localizedChartAlignment containment)
        |>.canonicalIntegralInterface
        |>.manifoldExtDerivIntegral) =
      ((D.toStrictAlignmentDataOfChartBoxContainment
        orientedBoundaryAtlas targetImageInput bulk boundaryTarget
        localizedChartAlignment containment)
        |>.canonicalIntegralInterface
        |>.boundaryFormIntegral) := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    D.canonical_stokes_ofChartBoxContainment
      orientedBoundaryAtlas targetImageInput bulk boundaryTarget
      localizedChartAlignment containment

end NaturalFiniteActiveChartBoxSelectionData

section NaturalEndpoint

variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]

namespace NaturalCompactSupportEndpointNaturalBoundaryMeasureInput

variable {D : NaturalFiniteActiveChartBoxSelectionData I omega rho}
variable
    (E :
      NaturalCompactSupportEndpointNaturalBoundaryMeasureInput
        (I := I) (omega := omega) (rho := rho)
        D ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)

/-- Chart-box containment specialized to the natural endpoint source. -/
abbrev StrictAlignmentChartBoxContainmentData :=
  (E.toSelectedReconstructionEndpointSource).EndpointSelectedBoxChartBoxStrictContainmentData

/-- Natural endpoint strict margins generated from chart-box containment. -/
def selectedStrictMarginsOfChartBoxContainment
    (C : E.StrictAlignmentChartBoxContainmentData) :
    E.toSelectedReconstructionEndpointSource.EndpointSelectedBoxStrictMargins :=
  E.toSelectedReconstructionEndpointSource
    |>.endpointSelectedBoxStrictMarginsOfChartBoxStrictContainment C

/--
Natural endpoint canonical Stokes from constructor chart alignment and chart-box
containment.
-/
theorem canonical_stokes_ofM8ChartAlignmentAndChartBoxContainmentStrictAlignment
    (A :
      LocalizedInteriorM8ChartAlignment
        E.toSelectedReconstructionEndpointSource.localized)
    (C : E.StrictAlignmentChartBoxContainmentData) :
    E.canonicalIntegralInterface.stokesStatement :=
  E.canonical_stokes_ofM8ChartAlignmentAndStrictMargins A
    (E.selectedStrictMarginsOfChartBoxContainment C)

/-- Natural endpoint canonical equality from chart-box containment. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndChartBoxContainmentStrictAlignment
    (A :
      LocalizedInteriorM8ChartAlignment
        E.toSelectedReconstructionEndpointSource.localized)
    (C : E.StrictAlignmentChartBoxContainmentData) :
    E.canonicalIntegralInterface.manifoldExtDerivIntegral =
      E.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    E.canonical_stokes_ofM8ChartAlignmentAndChartBoxContainmentStrictAlignment A C

end NaturalCompactSupportEndpointNaturalBoundaryMeasureInput

namespace NaturalCompactSupportEndpointNaturalInput

variable
    (N :
      NaturalCompactSupportEndpointNaturalInput
        I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu)

/-- Chart-box containment specialized to a fully packaged natural endpoint input. -/
abbrev StrictAlignmentChartBoxContainmentData :=
  N.boundaryMeasure.StrictAlignmentChartBoxContainmentData

/-- Natural endpoint strict margins generated from chart-box containment. -/
def selectedStrictMarginsOfChartBoxContainment
    (C : N.StrictAlignmentChartBoxContainmentData) :
    N.toSelectedReconstructionEndpointSource.EndpointSelectedBoxStrictMargins :=
  N.boundaryMeasure.selectedStrictMarginsOfChartBoxContainment C

/--
Fully packaged natural endpoint canonical Stokes from constructor chart
alignment and chart-box containment.
-/
theorem canonical_stokes_ofM8ChartAlignmentAndChartBoxContainmentStrictAlignment
    (A :
      LocalizedInteriorM8ChartAlignment
        N.toSelectedReconstructionEndpointSource.localized)
    (C : N.StrictAlignmentChartBoxContainmentData) :
    N.canonicalIntegralInterface.stokesStatement :=
  N.boundaryMeasure
    |>.canonical_stokes_ofM8ChartAlignmentAndChartBoxContainmentStrictAlignment A C

/-- Fully packaged natural endpoint canonical equality from chart-box containment. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndChartBoxContainmentStrictAlignment
    (A :
      LocalizedInteriorM8ChartAlignment
        N.toSelectedReconstructionEndpointSource.localized)
    (C : N.StrictAlignmentChartBoxContainmentData) :
    N.canonicalIntegralInterface.manifoldExtDerivIntegral =
      N.canonicalIntegralInterface.boundaryFormIntegral :=
  N.boundaryMeasure
    |>.manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndChartBoxContainmentStrictAlignment
      A C

end NaturalCompactSupportEndpointNaturalInput

end NaturalEndpoint

end NaturalEndpointStrictAlignmentRouteAuto

end Stokes

end
