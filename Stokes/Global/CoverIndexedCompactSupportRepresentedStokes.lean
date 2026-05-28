import Stokes.Global.CoverIndexedAssignedSelfNaturalAssembly
import Stokes.Global.CoverIndexedBulkSupportFromCompact
import Stokes.Global.CoverIndexedBoundaryTargetSupportFromImage
import Stokes.Global.CoverIndexedAssignedSelfBulkSmoothnessConstructor
import Stokes.Global.CoverIndexedBoundaryTargetSmoothnessConstructor
import Stokes.Global.CoverIndexedBoundaryScalarImageSupport

/-!
# Compact-support represented Stokes endpoint

This file records the current clean endpoint for the cover-indexed,
compact-support represented route.

The bulk side uses the assigned-self chart representative, so the remaining
bulk inputs are only smoothness and the coordinate measure identification.
The assigned-box support field is generated from the local chart-box data.

The boundary side uses packaged target-box data.  The remaining boundary input
is the target support/continuity package, together with either an oriented
atlas or the project-local oriented-manifold class.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportRepresentedStokesEndpoint

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {μBulk : Measure (Fin (n + 1) → Real)}

namespace CoverIndexedBoundaryTargetBoxData

/--
Target-box data plus image-support and target smoothness gives the boundary
support/continuity package consumed by the represented endpoint.

The only geometric hypothesis here is `targetInChart_tsupport_subset_image`:
the selected target image data then pushes the support into the target box.
-/
def supportContinuityOfTargetImageSupportInfty
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω)
    (targetInChart_contDiffOn :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (ManifoldForm.inChart I (D.targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i)))
          (Icc (D.targetLower i) (D.targetUpper i)))
    (targetInChart_tsupport_subset_image :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.inChart I (D.targetChart i)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          boundaryChartTransitionAmbientBoundaryImage I
            (C.boundaryChart i.1) (D.targetChart i)
            (C.boundaryLower i.1) (C.boundaryUpper i.1)) :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω D.targetChart D.targetLower D.targetUpper :=
  (CoverIndexedBoundaryTargetSupportFromImageData.mk
    (P := P) (ω := ω)
    (targetChart := D.targetChart)
    (targetLower := D.targetLower)
    (targetUpper := D.targetUpper)
    D.targetLower_zero
    D.targetLower_le_targetUpper
    D.boundaryChartSelectedBoxImageData
    targetInChart_tsupport_subset_image).toSupportContinuityData_ofContDiffOnInfty
      targetInChart_contDiffOn

end CoverIndexedBoundaryTargetBoxData

/--
Compact-support represented Stokes endpoint input for the assigned-self bulk
route and target-box boundary route.

The true remaining fields are deliberately visible:

* assigned-self bulk smoothness;
* target boundary support/continuity;
* orientation data supplied later by either an oriented atlas or an oriented
  manifold instance;
* the represented global boundary integral equality.
-/
structure CoverIndexedCompactSupportRepresentedStokesInput where
  /-- Assigned-box local Stokes and support data selected from compact support. -/
  localData :
    CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω
  /-- The bulk coordinate measure is the standard volume measure. -/
  measure_eq_volume :
    μBulk = (volume : Measure (Fin (n + 1) → Real))
  /-- Smoothness of the assigned-self bulk scalar pieces. -/
  bulkSmooth :
    SupportControlledSelectedPartition.CoverIndexedAssignedSelfBulkSmoothnessFields
      (I := I) (C := C) P ω
  /-- Selected target boxes and source-to-target selected-box data. -/
  targetBox :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω
  /-- Target-box support and continuity of the boundary pieces. -/
  supportContinuity :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω targetBox.targetChart
      targetBox.targetLower targetBox.targetUpper
  /-- Represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- The represented boundary integral is the integral of the target piece sum. -/
  globalBoundaryIntegral_eq_integral :
    globalBoundaryIntegral =
      ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart ω y
        ∂(volume : Measure (Fin n → Real))

namespace CoverIndexedCompactSupportRepresentedStokesInput

variable
    (D :
      CoverIndexedCompactSupportRepresentedStokesInput
        (I := I) (K := K) (ω := ω) (C := C) (P := P)
        (μBulk := μBulk))

/--
Assigned-self bulk input generated from the endpoint fields.

The support of each scalar bulk piece is not an extra parameter: it follows
from the assigned-box local data.
-/
def assignedSelfBulkInput
    [IsFiniteMeasureOnCompacts μBulk] [IsManifold I ⊤ M] :
    CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk :=
  CoverIndexedAssignedSelfBulkInput.ofSmoothnessFiniteSum
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk)
    D.measure_eq_volume
    D.bulkSmooth
    (fun j => by
      simpa [SupportControlledSelectedPartition.assignedSelfBulkPieceIntegrand]
        using
          D.localData.bulkIntegrand_tsupport_subset_assignedCoordinateBox_self
            (I := I) (j := j))

/-- Boundary measure data from target-box data and an oriented boundary atlas. -/
def targetBoundaryMeasureDataOfOrientedAtlas
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetBox.targetChart i ∈ A.charts) :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω :=
  D.targetBox.toTargetBoundaryMeasureDataOfOrientedAtlas
    D.localData A hsource htarget D.supportContinuity
    D.globalBoundaryIntegral D.globalBoundaryIntegral_eq_integral

/-- Boundary measure data from target-box data and oriented-manifold data. -/
def targetBoundaryMeasureDataOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M] :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω :=
  D.targetBox.toTargetBoundaryMeasureDataOfOrientedManifold
    D.localData D.supportContinuity
    D.globalBoundaryIntegral D.globalBoundaryIntegral_eq_integral

/-- Natural assembly input for the oriented-atlas endpoint. -/
def naturalAssemblyInputOfOrientedAtlas
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetBox.targetChart i ∈ A.charts) :
    CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) :=
  CoverIndexedNaturalAssemblyInput.ofAssignedSelfBulkTargetBoundary
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk)
    D.localData
    D.assignedSelfBulkInput
    (D.targetBoundaryMeasureDataOfOrientedAtlas A hsource htarget)

/-- Natural assembly input for the oriented-manifold endpoint. -/
def naturalAssemblyInputOfOrientedManifold
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) :=
  CoverIndexedNaturalAssemblyInput.ofAssignedSelfBulkTargetBoundary
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk)
    D.localData
    D.assignedSelfBulkInput
    D.targetBoundaryMeasureDataOfOrientedManifold

/--
Represented compact-support Stokes for the oriented-atlas endpoint.

This is the core endpoint equality: the generated assigned-self bulk integral
equals the generated target-boundary integral.
-/
theorem representedStokes_of_orientedAtlas
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetBox.targetChart i ∈ A.charts) :
    (D.assignedSelfBulkInput).globalIntegral =
      (D.targetBoundaryMeasureDataOfOrientedAtlas
        A hsource htarget).globalIntegral :=
  CoverIndexedNaturalAssemblyInput.stokes_ofAssignedSelfBulkTargetBoundary
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk)
    D.localData
    D.assignedSelfBulkInput
    (D.targetBoundaryMeasureDataOfOrientedAtlas A hsource htarget)

/-- Oriented-atlas endpoint with the boundary integral field unfolded. -/
theorem representedStokes_globalBoundaryIntegral_of_orientedAtlas
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetBox.targetChart i ∈ A.charts) :
    (D.assignedSelfBulkInput).globalIntegral =
      D.globalBoundaryIntegral := by
  simpa [targetBoundaryMeasureDataOfOrientedAtlas]
    using D.representedStokes_of_orientedAtlas A hsource htarget

/--
Represented compact-support Stokes for the oriented-manifold endpoint.

This has no explicit atlas-membership parameters; they are supplied by the
project-local oriented-manifold class.
-/
theorem representedStokes_of_orientedManifold
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.assignedSelfBulkInput).globalIntegral =
      D.targetBoundaryMeasureDataOfOrientedManifold.globalIntegral :=
  CoverIndexedNaturalAssemblyInput.stokes_ofAssignedSelfBulkTargetBoundary
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk)
    D.localData
    D.assignedSelfBulkInput
    D.targetBoundaryMeasureDataOfOrientedManifold

/-- Oriented-manifold endpoint with the boundary integral field unfolded. -/
theorem representedStokes_globalBoundaryIntegral_of_orientedManifold
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.assignedSelfBulkInput).globalIntegral =
      D.globalBoundaryIntegral := by
  simpa [targetBoundaryMeasureDataOfOrientedManifold]
    using D.representedStokes_of_orientedManifold

end CoverIndexedCompactSupportRepresentedStokesInput

/--
More natural endpoint input: assigned-self bulk smoothness and boundary target
support/continuity are generated from local chart-box data, localized
chartwise smoothness, and target-image support.
-/
structure CoverIndexedCompactSupportRepresentedStokesNaturalInput where
  /-- Assigned-box local Stokes and support data selected from compact support. -/
  localData :
    CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω
  /-- The bulk coordinate measure is the standard volume measure. -/
  measure_eq_volume :
    μBulk = (volume : Measure (Fin (n + 1) → Real))
  /-- Selected target boxes and source-to-target selected-box data. -/
  targetBox :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω
  /-- Localized boundary pieces are chartwise smooth. -/
  localizedChartwiseSmooth :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ManifoldForm.ChartwiseSmooth I
        (P.coverIndexLocalizedForm ω (Sum.inr i))
  /-- Target boxes lie in their selected chart targets. -/
  targetBox_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
        (extChartAt I (targetBox.targetChart i)).target
  /-- The target representative is supported on the selected boundary image. -/
  targetInChart_tsupport_subset_image :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      tsupport
          (ManifoldForm.inChart I (targetBox.targetChart i)
            (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
        boundaryChartTransitionAmbientBoundaryImage I
          (C.boundaryChart i.1) (targetBox.targetChart i)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
  /-- Represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- The represented boundary integral is the integral of the target piece sum. -/
  globalBoundaryIntegral_eq_integral :
    globalBoundaryIntegral =
      ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart ω y
        ∂(volume : Measure (Fin n → Real))

namespace CoverIndexedCompactSupportRepresentedStokesNaturalInput

variable
    (D :
      CoverIndexedCompactSupportRepresentedStokesNaturalInput
        (I := I) (K := K) (ω := ω) (C := C) (P := P)
        (μBulk := μBulk))

/-- Assigned-self bulk input generated directly from local chart-box data. -/
def assignedSelfBulkInput
    [IsFiniteMeasureOnCompacts μBulk] [IsManifold I ⊤ M] :
    CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk :=
  CoverIndexedAssignedSelfBulkInput.ofLocalDataInftyFiniteSum
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk) D.measure_eq_volume D.localData

/-- Boundary target support/continuity generated from smoothness and image support. -/
def supportContinuity :
    CoverIndexedBoundaryTargetSupportContinuityData
      (C := C) P ω D.targetBox.targetChart
      D.targetBox.targetLower D.targetBox.targetUpper :=
  D.targetBox.toSupportContinuityDataOfLocalizedChartwiseSmooth
    D.localizedChartwiseSmooth
    D.targetBox_subset_target
    D.targetInChart_tsupport_subset_image

/-- Boundary measure data from target-box data and an oriented boundary atlas. -/
def targetBoundaryMeasureDataOfOrientedAtlas
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetBox.targetChart i ∈ A.charts) :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω :=
  D.targetBox.toTargetBoundaryMeasureDataOfOrientedAtlas
    D.localData A hsource htarget D.supportContinuity
    D.globalBoundaryIntegral D.globalBoundaryIntegral_eq_integral

/-- Boundary measure data from target-box data and oriented-manifold data. -/
def targetBoundaryMeasureDataOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M] :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω :=
  D.targetBox.toTargetBoundaryMeasureDataOfOrientedManifold
    D.localData D.supportContinuity
    D.globalBoundaryIntegral D.globalBoundaryIntegral_eq_integral

/-- Natural assembly input for the oriented-atlas endpoint. -/
def naturalAssemblyInputOfOrientedAtlas
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetBox.targetChart i ∈ A.charts) :
    CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) :=
  CoverIndexedNaturalAssemblyInput.ofAssignedSelfBulkTargetBoundary
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk)
    D.localData
    D.assignedSelfBulkInput
    (D.targetBoundaryMeasureDataOfOrientedAtlas A hsource htarget)

/-- Natural assembly input for the oriented-manifold endpoint. -/
def naturalAssemblyInputOfOrientedManifold
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    CoverIndexedNaturalAssemblyInput
      (I := I) (K := K) (ω := ω)
      (μBulk := μBulk)
      (αBoundary := Fin n → Real)
      (μBoundary := (volume : Measure (Fin n → Real))) :=
  CoverIndexedNaturalAssemblyInput.ofAssignedSelfBulkTargetBoundary
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk)
    D.localData
    D.assignedSelfBulkInput
    D.targetBoundaryMeasureDataOfOrientedManifold

/-- Represented compact-support Stokes for the natural oriented-atlas endpoint. -/
theorem representedStokes_globalBoundaryIntegral_of_orientedAtlas
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetBox.targetChart i ∈ A.charts) :
    (D.assignedSelfBulkInput).globalIntegral =
      D.globalBoundaryIntegral := by
  simpa [targetBoundaryMeasureDataOfOrientedAtlas]
    using
      CoverIndexedNaturalAssemblyInput.stokes_ofAssignedSelfBulkTargetBoundary
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk)
        D.localData
        D.assignedSelfBulkInput
        (D.targetBoundaryMeasureDataOfOrientedAtlas A hsource htarget)

/-- Represented compact-support Stokes for the natural oriented-manifold endpoint. -/
theorem representedStokes_globalBoundaryIntegral_of_orientedManifold
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.assignedSelfBulkInput).globalIntegral =
      D.globalBoundaryIntegral := by
  simpa [targetBoundaryMeasureDataOfOrientedManifold]
    using
      CoverIndexedNaturalAssemblyInput.stokes_ofAssignedSelfBulkTargetBoundary
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk)
        D.localData
        D.assignedSelfBulkInput
        D.targetBoundaryMeasureDataOfOrientedManifold

end CoverIndexedCompactSupportRepresentedStokesNaturalInput

/--
Natural endpoint input using boundary scalar image support.

This is the mathematically preferred boundary route: instead of requiring the
ambient target `inChart` representative to be supported on the boundary image,
it assumes support of the actual scalar boundary integrand on the selected
boundary-transition image.
-/
structure CoverIndexedCompactSupportRepresentedStokesScalarInput where
  /-- Assigned-box local Stokes and support data selected from compact support. -/
  localData :
    CoverIndexedAssignedBoxLocalData (I := I) (K := K) C P ω
  /-- The bulk coordinate measure is the standard volume measure. -/
  measure_eq_volume :
    μBulk = (volume : Measure (Fin (n + 1) → Real))
  /-- Selected target boxes and source-to-target selected-box data. -/
  targetBox :
    CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P ω
  /-- Localized boundary pieces are chartwise smooth. -/
  localizedChartwiseSmooth :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      ManifoldForm.ChartwiseSmooth I
        (P.coverIndexLocalizedForm ω (Sum.inr i))
  /-- Target boxes lie in their selected chart targets. -/
  targetBox_subset_target :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      Icc (targetBox.targetLower i) (targetBox.targetUpper i) ⊆
        (extChartAt I (targetBox.targetChart i)).target
  /-- The boundary scalar representative is supported on the selected image. -/
  scalarSupport :
    targetBox.BoundaryScalarSupportSubsetImageField
  /-- Represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- The represented boundary integral is the integral of the target piece sum. -/
  globalBoundaryIntegral_eq_integral :
    globalBoundaryIntegral =
      ∫ y, P.coverIndexBoundaryTargetPieceSum targetBox.targetChart ω y
        ∂(volume : Measure (Fin n → Real))

namespace CoverIndexedCompactSupportRepresentedStokesScalarInput

variable
    (D :
      CoverIndexedCompactSupportRepresentedStokesScalarInput
        (I := I) (K := K) (ω := ω) (C := C) (P := P)
        (μBulk := μBulk))

/-- Assigned-self bulk input generated directly from local chart-box data. -/
def assignedSelfBulkInput
    [IsFiniteMeasureOnCompacts μBulk] [IsManifold I ⊤ M] :
    CoverIndexedAssignedSelfBulkInput
      (I := I) (K := K) C P ω μBulk :=
  CoverIndexedAssignedSelfBulkInput.ofLocalDataInftyFiniteSum
    (I := I) (K := K) (C := C) (P := P) (ω := ω)
    (μBulk := μBulk) D.measure_eq_volume D.localData

/-- Boundary measure data from scalar image support and an oriented atlas. -/
def targetBoundaryMeasureDataOfOrientedAtlas
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetBox.targetChart i ∈ A.charts) :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω :=
  D.targetBox.toTargetBoundaryMeasureDataOfOrientedAtlasScalarImageSupport
    D.localData A hsource htarget D.localizedChartwiseSmooth
    D.targetBox_subset_target D.scalarSupport
    D.globalBoundaryIntegral D.globalBoundaryIntegral_eq_integral

/-- Boundary measure data from scalar image support and oriented-manifold data. -/
def targetBoundaryMeasureDataOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M] :
    CoverIndexedTargetBoundaryMeasureData
      (I := I) (K := K) C P ω :=
  D.targetBox.toTargetBoundaryMeasureDataOfOrientedManifoldScalarImageSupport
    D.localData D.localizedChartwiseSmooth D.targetBox_subset_target
    D.scalarSupport D.globalBoundaryIntegral
    D.globalBoundaryIntegral_eq_integral

/-- Represented compact-support Stokes for the scalar-support oriented-atlas endpoint. -/
theorem representedStokes_globalBoundaryIntegral_of_orientedAtlas
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (hsource : ∀ i : {x : M // x ∈ C.boundaryCenters},
      C.boundaryChart i.1 ∈ A.charts)
    (htarget : ∀ i : {x : M // x ∈ C.boundaryCenters},
      D.targetBox.targetChart i ∈ A.charts) :
    (D.assignedSelfBulkInput).globalIntegral =
      D.globalBoundaryIntegral := by
  simpa [targetBoundaryMeasureDataOfOrientedAtlas]
    using
      CoverIndexedNaturalAssemblyInput.stokes_ofAssignedSelfBulkTargetBoundary
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk)
        D.localData
        D.assignedSelfBulkInput
        (D.targetBoundaryMeasureDataOfOrientedAtlas A hsource htarget)

/-- Represented compact-support Stokes for the scalar-support oriented-manifold endpoint. -/
theorem representedStokes_globalBoundaryIntegral_of_orientedManifold
    [IsFiniteMeasureOnCompacts μBulk]
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    [BoundaryChartOrientedManifold I M] :
    (D.assignedSelfBulkInput).globalIntegral =
      D.globalBoundaryIntegral := by
  simpa [targetBoundaryMeasureDataOfOrientedManifold]
    using
      CoverIndexedNaturalAssemblyInput.stokes_ofAssignedSelfBulkTargetBoundary
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        (μBulk := μBulk)
        D.localData
        D.assignedSelfBulkInput
        D.targetBoundaryMeasureDataOfOrientedManifold

end CoverIndexedCompactSupportRepresentedStokesScalarInput

end CompactSupportRepresentedStokesEndpoint

end Stokes

end
