import Stokes.Global.CompactSupportEndpointFacade
import Stokes.Global.CanonicalNaturalCompactSupport
import Stokes.Global.NaturalCompactSupportCombinedEndpoint

/-!
# Canonical compact-support endpoint facade

This file is theorem-facing glue only.  It connects the current compact-support
endpoint facades to `CanonicalIntegralInterface`, so callers can state the
endpoint conclusion as

`manifoldExtDerivIntegral = boundaryFormIntegral`

without unfolding the represented M8 measure-localization fields.

No new geometric input is proved here.  The remaining real data are the same as
in the underlying endpoint routes: M8 chart alignment, localized outer/strict
buffer boxes, separated boundary route data, and artificial-face cancellation.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CanonicalCompactSupportEndpointFacade

universe u w b ei eb a

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

namespace NaturalCompactSupportStokesInput

variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]

/-- Natural compact-support Stokes with the canonical equality visible. -/
theorem canonical_manifoldExtDerivIntegral_eq_boundaryFormIntegral
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using D.canonical_stokes

end NaturalCompactSupportStokesInput

namespace NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

variable [IsManifold I 1 M]
variable
    (S :
      NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- Canonical theorem-facing names for a source-packaged compact-support endpoint. -/
def canonicalIntegralInterface :
    CanonicalIntegralInterface I omega :=
  S.endpointMeasureLocalization.canonicalIntegralInterface

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral :
    S.canonicalIntegralInterface.manifoldExtDerivIntegral =
      S.endpointMeasureLocalization.bulkMeasureIntegral :=
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral :
    S.canonicalIntegralInterface.boundaryFormIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  rfl

/--
Endpoint Stokes with canonical names, from the public source-packaged endpoint
inputs and localized outer-box containment.
-/
theorem canonical_stokes_ofM8ChartAlignmentAndLocalizedOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    S.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface, CanonicalIntegralInterface.stokesStatement] using
    S.stokes_ofM8ChartAlignmentAndLocalizedOuterBox A D

/--
Endpoint Stokes with the equality `manifoldExtDerivIntegral =
boundaryFormIntegral` visible, from localized outer-box containment.
-/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndLocalizedOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    S.canonicalIntegralInterface.manifoldExtDerivIntegral =
      S.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    S.canonical_stokes_ofM8ChartAlignmentAndLocalizedOuterBox A D

/--
Endpoint Stokes with canonical names, from a compact-active strict-buffer
alignment over the selected compact boxes.
-/
theorem canonical_stokes_ofM8ChartAlignmentAndCompactActiveStrictBufferAlignment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (alignment :
      CompactActiveBoxStrictBufferAlignment S.selection.compactActiveBoxData
        S.endpointAutoBase.toBaseInput.selectedPartition
        S.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    S.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface, CanonicalIntegralInterface.stokesStatement] using
    S.stokes_ofM8ChartAlignmentAndCompactActiveStrictBufferAlignment A alignment

/-- Endpoint Stokes with canonical names, from named compact-active outer boxes. -/
theorem canonical_stokes_ofM8ChartAlignmentAndOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveOuterBoxData) :
    S.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface, CanonicalIntegralInterface.stokesStatement] using
    S.stokes_ofM8ChartAlignmentAndOuterBox A D

end NaturalCompactSupportEndpointSelectedReconstructionSourceBaseSources

namespace NaturalCompactSupportEndpointExtDerivBaseSources

variable [IsManifold I 1 M]
variable
    (S :
      NaturalCompactSupportEndpointExtDerivBaseSources
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- Canonical theorem-facing names for an ext-deriv compact-support endpoint source. -/
def canonicalIntegralInterface :
    CanonicalIntegralInterface I omega :=
  S.endpointMeasureLocalization.canonicalIntegralInterface

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral :
    S.canonicalIntegralInterface.manifoldExtDerivIntegral =
      S.endpointMeasureLocalization.bulkMeasureIntegral :=
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral :
    S.canonicalIntegralInterface.boundaryFormIntegral =
      S.endpointMeasureLocalization.boundaryMeasureIntegral :=
  rfl

/--
Ext-deriv endpoint Stokes with canonical names, using localized outer-box
containment after converting to the source-packaged endpoint facade.
-/
theorem canonical_stokes_ofM8ChartAlignmentAndLocalizedOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    S.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface, CanonicalIntegralInterface.stokesStatement] using
    S.stokes_ofM8ChartAlignmentAndLocalizedOuterBox A D

/--
Ext-deriv endpoint Stokes with the equality `manifoldExtDerivIntegral =
boundaryFormIntegral` visible.
-/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndLocalizedOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveLocalizedOuterBoxData) :
    S.canonicalIntegralInterface.manifoldExtDerivIntegral =
      S.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    S.canonical_stokes_ofM8ChartAlignmentAndLocalizedOuterBox A D

/-- Ext-deriv endpoint Stokes with canonical names, from strict-buffer alignment. -/
theorem canonical_stokes_ofM8ChartAlignmentAndCompactActiveStrictBufferAlignment
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (alignment :
      CompactActiveBoxStrictBufferAlignment S.selection.compactActiveBoxData
        S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.selectedPartition
        S.compactSupportEndpointSource.endpointAutoBase.toBaseInput.targetImageInput.targetImages
        S.endpointMeasureLocalization) :
    S.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface, CanonicalIntegralInterface.stokesStatement] using
    S.stokes_ofM8ChartAlignmentAndCompactActiveStrictBufferAlignment A alignment

/-- Ext-deriv endpoint Stokes with canonical names, from named compact-active outer boxes. -/
theorem canonical_stokes_ofM8ChartAlignmentAndOuterBox
    (A : LocalizedInteriorM8ChartAlignment S.localized)
    (D : S.EndpointCompactActiveOuterBoxData) :
    S.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface, CanonicalIntegralInterface.stokesStatement] using
    S.stokes_ofM8ChartAlignmentAndOuterBox A D

end NaturalCompactSupportEndpointExtDerivBaseSources

namespace NaturalCompactSupportBulkBoundarySeparatedInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportBulkBoundarySeparatedInput
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- Canonical theorem-facing names for the combined separated compact-support endpoint. -/
def canonicalIntegralInterface :
    CanonicalIntegralInterface I omega :=
  D.base.separatedMeasure.toM8MeasureLocalizationData.canonicalIntegralInterface

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.base.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral :=
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral :
    D.canonicalIntegralInterface.boundaryFormIntegral =
      D.base.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  rfl

/-- Combined separated endpoint Stokes in canonical statement form. -/
theorem canonical_stokes :
    D.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface, CanonicalIntegralInterface.stokesStatement] using
    D.stokes

/-- Combined separated endpoint Stokes with the canonical equality visible. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using D.canonical_stokes

end NaturalCompactSupportBulkBoundarySeparatedInput

namespace NaturalCompactSupportBulkBoundarySeparatedAutoStokesInput

variable [IsManifold I 1 M]
variable
    (D :
      NaturalCompactSupportBulkBoundarySeparatedAutoStokesInput
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/-- Canonical theorem-facing names for the auto combined separated endpoint. -/
def canonicalIntegralInterface :
    CanonicalIntegralInterface I omega :=
  D.base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData.canonicalIntegralInterface

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData.bulkMeasureIntegral :=
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral :
    D.canonicalIntegralInterface.boundaryFormIntegral =
      D.base.toBaseInput.separatedMeasure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  rfl

/-- Auto combined separated endpoint Stokes in canonical statement form. -/
theorem canonical_stokes :
    D.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface, CanonicalIntegralInterface.stokesStatement] using
    D.stokes

/-- Auto combined separated endpoint Stokes with the canonical equality visible. -/
theorem manifoldExtDerivIntegral_eq_boundaryFormIntegral :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.canonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using D.canonical_stokes

end NaturalCompactSupportBulkBoundarySeparatedAutoStokesInput

namespace NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

variable [IsManifold I 1 M]
variable
    (B :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece rho mu)

/--
Canonical theorem-facing names for the endpoint obtained from a bulk
project-local-auto input plus a lower-dimensional canonical boundary route.
-/
def bulkBoundarySeparatedCanonicalIntegralInterface
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (boundaryRoute :
      BoundaryCanonicalRouteMeasureInput B.targetImageInput boundaryProjectLocal) :
    CanonicalIntegralInterface I omega :=
  ((B.toBulkBoundarySeparatedBaseInput boundaryProjectLocal boundaryRoute)
    |>.separatedMeasure
    |>.toM8MeasureLocalizationData
    |>.canonicalIntegralInterface)

@[simp]
theorem bulkBoundarySeparatedCanonicalIntegralInterface_manifoldExtDerivIntegral
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (boundaryRoute :
      BoundaryCanonicalRouteMeasureInput B.targetImageInput boundaryProjectLocal) :
    (B.bulkBoundarySeparatedCanonicalIntegralInterface
      boundaryProjectLocal boundaryRoute).manifoldExtDerivIntegral =
      ((B.toBulkBoundarySeparatedBaseInput boundaryProjectLocal boundaryRoute)
        |>.separatedMeasure
        |>.toM8MeasureLocalizationData
        |>.bulkMeasureIntegral) :=
  rfl

@[simp]
theorem bulkBoundarySeparatedCanonicalIntegralInterface_boundaryFormIntegral
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (boundaryRoute :
      BoundaryCanonicalRouteMeasureInput B.targetImageInput boundaryProjectLocal) :
    (B.bulkBoundarySeparatedCanonicalIntegralInterface
      boundaryProjectLocal boundaryRoute).boundaryFormIntegral =
      ((B.toBulkBoundarySeparatedBaseInput boundaryProjectLocal boundaryRoute)
        |>.separatedMeasure
        |>.toM8MeasureLocalizationData
        |>.boundaryMeasureIntegral) :=
  rfl

/--
Stokes in canonical statement form, starting from the bulk project-local-auto
source and the remaining canonical boundary/artificial data.
-/
theorem canonical_stokes_bulkBoundarySeparated
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (boundaryRoute :
      BoundaryCanonicalRouteMeasureInput B.targetImageInput boundaryProjectLocal)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        (B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).selectedPartition
        (B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).targetImageInput.targetImages
        ((B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).separatedMeasure
            |>.toM8MeasureLocalizationData)) :
    (B.bulkBoundarySeparatedCanonicalIntegralInterface
      boundaryProjectLocal boundaryRoute).stokesStatement := by
  simpa [bulkBoundarySeparatedCanonicalIntegralInterface,
    CanonicalIntegralInterface.stokesStatement] using
    B.stokes_bulkBoundarySeparated
      boundaryProjectLocal boundaryRoute artificial

/--
The same route with the equality `manifoldExtDerivIntegral =
boundaryFormIntegral` visible.
-/
theorem bulkBoundarySeparated_manifoldExtDerivIntegral_eq_boundaryFormIntegral
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (boundaryRoute :
      BoundaryCanonicalRouteMeasureInput B.targetImageInput boundaryProjectLocal)
    (artificial :
      M8ArtificialFaceFields I omega BoundaryPiece
        (B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).selectedPartition
        (B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).targetImageInput.targetImages
        ((B.toBulkBoundarySeparatedBaseInput
          boundaryProjectLocal boundaryRoute).separatedMeasure
            |>.toM8MeasureLocalizationData)) :
    (B.bulkBoundarySeparatedCanonicalIntegralInterface
      boundaryProjectLocal boundaryRoute).manifoldExtDerivIntegral =
      (B.bulkBoundarySeparatedCanonicalIntegralInterface
        boundaryProjectLocal boundaryRoute).boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    B.canonical_stokes_bulkBoundarySeparated
      boundaryProjectLocal boundaryRoute artificial

end NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

end CanonicalCompactSupportEndpointFacade

end Stokes

end
