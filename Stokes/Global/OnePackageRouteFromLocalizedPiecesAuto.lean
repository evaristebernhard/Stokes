import Stokes.Global.NaturalOnePackageFromRoutesAuto
import Stokes.Global.LocalizedChartAlignmentFromNaturalSelectionAuto

/-!
# One-package route inputs from localized-piece equalities

This module removes the raw `LocalizedInteriorM8ChartAlignment` argument from
the theorem-facing one-package route constructors.  The caller supplies the
localized-piece equality package instead, and the alignment field is generated
by `NaturalFiniteActiveLocalizedPieceEqData.toLocalizedInteriorM8ChartAlignment`.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section OnePackageRouteFromLocalizedPiecesAuto

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {rho : SmoothPartitionOfUnity M I M univ}
variable {mu : Measure (Fin (n + 1) -> Real)}
variable [IsFiniteMeasureOnCompacts mu]
variable [IsManifold I 1 M]

namespace NaturalOnePackageExtDerivRouteSelectedMarginInput

/-- Build the ext-deriv selected-margin route input from localized-piece equality data. -/
def ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ExtDerivConstructorRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (strictMargins :
      (((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
            (ExtInteriorPiece := ExtInteriorPiece)
            (ExtBoundaryPiece := ExtBoundaryPiece)
            route)
          |>.toSelectedReconstructionEndpointSource)
        |>.EndpointSelectedBoxStrictMargins)) :
    NaturalOnePackageExtDerivRouteSelectedMarginInput
      I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu where
  formData := formData
  compactSource := compactSource
  common := common
  route := route
  chartAlignment := localizedPieces.toLocalizedInteriorM8ChartAlignment
  strictMargins := strictMargins

/-- Canonical Stokes for the ext-deriv selected-margin route built from localized pieces. -/
theorem canonical_stokes_ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ExtDerivConstructorRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (strictMargins :
      (((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
            (ExtInteriorPiece := ExtInteriorPiece)
            (ExtBoundaryPiece := ExtBoundaryPiece)
            route)
          |>.toSelectedReconstructionEndpointSource)
        |>.EndpointSelectedBoxStrictMargins)) :
    ((ofLocalizedPieces
        (I := I) (omega := omega) (rho := rho)
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        (BoundaryPiece := BoundaryPiece) (mu := mu)
        formData compactSource common route localizedPieces strictMargins)
      |>.toOnePackageStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement) :=
  (ofLocalizedPieces
    (I := I) (omega := omega) (rho := rho)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    (BoundaryPiece := BoundaryPiece) (mu := mu)
    formData compactSource common route localizedPieces strictMargins)
    |>.canonical_stokes

/-- Equality form for the ext-deriv selected-margin route built from localized pieces. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ExtDerivConstructorRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (strictMargins :
      (((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
            (ExtInteriorPiece := ExtInteriorPiece)
            (ExtBoundaryPiece := ExtBoundaryPiece)
            route)
          |>.toSelectedReconstructionEndpointSource)
        |>.EndpointSelectedBoxStrictMargins)) :
    let D :=
      ofLocalizedPieces
        (I := I) (omega := omega) (rho := rho)
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        (BoundaryPiece := BoundaryPiece) (mu := mu)
        formData compactSource common route localizedPieces strictMargins
    D.toOnePackageStokesInput.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.toOnePackageStokesInput.canonicalIntegralInterface.boundaryFormIntegral :=
  (ofLocalizedPieces
    (I := I) (omega := omega) (rho := rho)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    (BoundaryPiece := BoundaryPiece) (mu := mu)
    formData compactSource common route localizedPieces strictMargins)
    |>.manifoldExtDerivIntegral_eq_boundaryFormIntegral

end NaturalOnePackageExtDerivRouteSelectedMarginInput

namespace NaturalOnePackageExtDerivRouteChartBoxInput

/-- Build the ext-deriv chart-box route input from localized-piece equality data. -/
def ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ExtDerivConstructorRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (containment :
      ((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
          (ExtInteriorPiece := ExtInteriorPiece)
          (ExtBoundaryPiece := ExtBoundaryPiece)
          route)
        |>.StrictAlignmentChartBoxContainmentData)) :
    NaturalOnePackageExtDerivRouteChartBoxInput
      I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu where
  formData := formData
  compactSource := compactSource
  common := common
  route := route
  chartAlignment := localizedPieces.toLocalizedInteriorM8ChartAlignment
  containment := containment

/-- Canonical Stokes for the ext-deriv chart-box route built from localized pieces. -/
theorem canonical_stokes_ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ExtDerivConstructorRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (containment :
      ((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
          (ExtInteriorPiece := ExtInteriorPiece)
          (ExtBoundaryPiece := ExtBoundaryPiece)
          route)
        |>.StrictAlignmentChartBoxContainmentData)) :
    ((ofLocalizedPieces
        (I := I) (omega := omega) (rho := rho)
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        (BoundaryPiece := BoundaryPiece) (mu := mu)
        formData compactSource common route localizedPieces containment)
      |>.toOnePackageChartBoxStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement) :=
  (ofLocalizedPieces
    (I := I) (omega := omega) (rho := rho)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    (BoundaryPiece := BoundaryPiece) (mu := mu)
    formData compactSource common route localizedPieces containment)
    |>.canonical_stokes

/-- Equality form for the ext-deriv chart-box route built from localized pieces. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ExtDerivConstructorRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (containment :
      ((common.toBoundaryMeasureInputOfExtDerivConstructorRoute
          (ExtInteriorPiece := ExtInteriorPiece)
          (ExtBoundaryPiece := ExtBoundaryPiece)
          route)
        |>.StrictAlignmentChartBoxContainmentData)) :
    let D :=
      ofLocalizedPieces
        (I := I) (omega := omega) (rho := rho)
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        (BoundaryPiece := BoundaryPiece) (mu := mu)
        formData compactSource common route localizedPieces containment
    D.toOnePackageChartBoxStokesInput.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.toOnePackageChartBoxStokesInput.canonicalIntegralInterface.boundaryFormIntegral :=
  (ofLocalizedPieces
    (I := I) (omega := omega) (rho := rho)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    (BoundaryPiece := BoundaryPiece) (mu := mu)
    formData compactSource common route localizedPieces containment)
    |>.manifoldExtDerivIntegral_eq_boundaryFormIntegral

end NaturalOnePackageExtDerivRouteChartBoxInput

namespace NaturalOnePackageReconstructionRouteSelectedMarginInput

/-- Build the reconstruction selected-margin route input from localized-piece equality data. -/
def ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ReconstructionRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfReconstructionRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (strictMargins :
      (((common.toBoundaryMeasureInputOfReconstructionRoute
            (ExtInteriorPiece := ExtInteriorPiece)
            (ExtBoundaryPiece := ExtBoundaryPiece)
            route)
          |>.toSelectedReconstructionEndpointSource)
        |>.EndpointSelectedBoxStrictMargins)) :
    NaturalOnePackageReconstructionRouteSelectedMarginInput
      I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu where
  formData := formData
  compactSource := compactSource
  common := common
  route := route
  chartAlignment := localizedPieces.toLocalizedInteriorM8ChartAlignment
  strictMargins := strictMargins

/-- Canonical Stokes for the reconstruction selected-margin route built from localized pieces. -/
theorem canonical_stokes_ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ReconstructionRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfReconstructionRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (strictMargins :
      (((common.toBoundaryMeasureInputOfReconstructionRoute
            (ExtInteriorPiece := ExtInteriorPiece)
            (ExtBoundaryPiece := ExtBoundaryPiece)
            route)
          |>.toSelectedReconstructionEndpointSource)
        |>.EndpointSelectedBoxStrictMargins)) :
    ((ofLocalizedPieces
        (I := I) (omega := omega) (rho := rho)
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        (BoundaryPiece := BoundaryPiece) (mu := mu)
        formData compactSource common route localizedPieces strictMargins)
      |>.toOnePackageStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement) :=
  (ofLocalizedPieces
    (I := I) (omega := omega) (rho := rho)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    (BoundaryPiece := BoundaryPiece) (mu := mu)
    formData compactSource common route localizedPieces strictMargins)
    |>.canonical_stokes

/-- Equality form for the reconstruction selected-margin route built from localized pieces. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ReconstructionRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfReconstructionRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (strictMargins :
      (((common.toBoundaryMeasureInputOfReconstructionRoute
            (ExtInteriorPiece := ExtInteriorPiece)
            (ExtBoundaryPiece := ExtBoundaryPiece)
            route)
          |>.toSelectedReconstructionEndpointSource)
        |>.EndpointSelectedBoxStrictMargins)) :
    let D :=
      ofLocalizedPieces
        (I := I) (omega := omega) (rho := rho)
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        (BoundaryPiece := BoundaryPiece) (mu := mu)
        formData compactSource common route localizedPieces strictMargins
    D.toOnePackageStokesInput.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.toOnePackageStokesInput.canonicalIntegralInterface.boundaryFormIntegral :=
  (ofLocalizedPieces
    (I := I) (omega := omega) (rho := rho)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    (BoundaryPiece := BoundaryPiece) (mu := mu)
    formData compactSource common route localizedPieces strictMargins)
    |>.manifoldExtDerivIntegral_eq_boundaryFormIntegral

end NaturalOnePackageReconstructionRouteSelectedMarginInput

namespace NaturalOnePackageReconstructionRouteChartBoxInput

/-- Build the reconstruction chart-box route input from localized-piece equality data. -/
def ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ReconstructionRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfReconstructionRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (containment :
      ((common.toBoundaryMeasureInputOfReconstructionRoute
          (ExtInteriorPiece := ExtInteriorPiece)
          (ExtBoundaryPiece := ExtBoundaryPiece)
          route)
        |>.StrictAlignmentChartBoxContainmentData)) :
    NaturalOnePackageReconstructionRouteChartBoxInput
      I omega rho ExtInteriorPiece ExtBoundaryPiece BoundaryPiece mu where
  formData := formData
  compactSource := compactSource
  common := common
  route := route
  chartAlignment := localizedPieces.toLocalizedInteriorM8ChartAlignment
  containment := containment

/-- Canonical Stokes for the reconstruction chart-box route built from localized pieces. -/
theorem canonical_stokes_ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ReconstructionRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfReconstructionRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (containment :
      ((common.toBoundaryMeasureInputOfReconstructionRoute
          (ExtInteriorPiece := ExtInteriorPiece)
          (ExtBoundaryPiece := ExtBoundaryPiece)
          route)
        |>.StrictAlignmentChartBoxContainmentData)) :
    ((ofLocalizedPieces
        (I := I) (omega := omega) (rho := rho)
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        (BoundaryPiece := BoundaryPiece) (mu := mu)
        formData compactSource common route localizedPieces containment)
      |>.toOnePackageChartBoxStokesInput
      |>.canonicalIntegralInterface
      |>.stokesStatement) :=
  (ofLocalizedPieces
    (I := I) (omega := omega) (rho := rho)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    (BoundaryPiece := BoundaryPiece) (mu := mu)
    formData compactSource common route localizedPieces containment)
    |>.canonical_stokes

/-- Equality form for the reconstruction chart-box route built from localized pieces. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofLocalizedPieces
    (formData : CompactlySupportedSmoothFormData I omega)
    (compactSource :
      CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData
        (rho := rho) formData)
    (common :
      NaturalBulkEndpointCommonData
        (I := I) (omega := omega) (rho := rho)
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        BoundaryPiece mu)
    (route :
      common.ReconstructionRoute
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece))
    (localizedPieces :
      NaturalFiniteActiveLocalizedPieceEqData
        compactSource.toNaturalFiniteActiveChartBoxSelectionData
        (((common.toBoundaryMeasureInputOfReconstructionRoute
              (ExtInteriorPiece := ExtInteriorPiece)
              (ExtBoundaryPiece := ExtBoundaryPiece)
              route)
            |>.toSelectedReconstructionEndpointSource)
          |>.localized))
    (containment :
      ((common.toBoundaryMeasureInputOfReconstructionRoute
          (ExtInteriorPiece := ExtInteriorPiece)
          (ExtBoundaryPiece := ExtBoundaryPiece)
          route)
        |>.StrictAlignmentChartBoxContainmentData)) :
    let D :=
      ofLocalizedPieces
        (I := I) (omega := omega) (rho := rho)
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        (BoundaryPiece := BoundaryPiece) (mu := mu)
        formData compactSource common route localizedPieces containment
    D.toOnePackageChartBoxStokesInput.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.toOnePackageChartBoxStokesInput.canonicalIntegralInterface.boundaryFormIntegral :=
  (ofLocalizedPieces
    (I := I) (omega := omega) (rho := rho)
    (ExtInteriorPiece := ExtInteriorPiece)
    (ExtBoundaryPiece := ExtBoundaryPiece)
    (BoundaryPiece := BoundaryPiece) (mu := mu)
    formData compactSource common route localizedPieces containment)
    |>.manifoldExtDerivIntegral_eq_boundaryFormIntegral

end NaturalOnePackageReconstructionRouteChartBoxInput

end OnePackageRouteFromLocalizedPiecesAuto

end Stokes

end
