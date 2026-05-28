import Stokes.Global.MeasureBoxAPI
import Stokes.Global.NaturalMeasureConstructor

/-!
# Bulk integral localization constructor

This file bridges the bulk-side analytic handoff records to the existing global
bulk reconstruction API.

Several upstream analytic files are still settling, so the constructor keeps
the low-level local terms fieldized.  It reuses the already existing
`BulkMeasureLocalizationFields` from `NaturalMeasureConstructor` as the final
measure-level wrapper, and supplies local same-shape records for:

* measure-local interior and boundary terms,
* a.e. bulk-integrand replacement data,
* compact-support integrability preconditions,
* identification of analytic local terms with existing project-local box terms.

The main output is the exact `BulkIntegralPartitionInput.bulkIntegralLocalizes`
field, plus constructors for `BulkIntegralPartitionInput`,
`BulkIntegralReconstructionData`, and the final `BulkMeasureLocalizationFields`
wrapper.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkIntegralLocalizationConstructor

universe u w ιu cb pb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type ιu}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {BoundaryChart : Type cb} {BoundaryPiece : Type pb}

namespace BulkMeasureLocalizationTermFields

variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}

/--
The measure-local fields, after a.e. replacement, reconstruct the global bulk
integral from integrand-local terms.
-/
theorem globalBulkIntegral_eq_integrandLocalSum
    (measureTerms : BulkMeasureLocalizationTermFields interior boundary)
    (ae : BulkIntegrandAELocalFields measureTerms) :
    measureTerms.globalBulkIntegral =
      (Finset.sum interior.active fun i => ae.interiorIntegrandTerm i) +
        Finset.sum boundary.activeCharts fun x =>
          Finset.sum (boundary.boundaryPieces x) fun q =>
            ae.boundaryIntegrandTerm x q := by
  calc
    measureTerms.globalBulkIntegral = measureTerms.bulkMeasureIntegral :=
      measureTerms.globalBulkIntegral_eq_bulkMeasureIntegral
    _ =
        (Finset.sum interior.active fun i => measureTerms.interiorMeasureTerm i) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              measureTerms.boundaryMeasureTerm x q :=
      measureTerms.bulkMeasureIntegral_eq_measureSum
    _ =
        (Finset.sum interior.active fun i => ae.interiorIntegrandTerm i) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              ae.boundaryIntegrandTerm x q := by
      have hinterior :
          (Finset.sum interior.active fun i => measureTerms.interiorMeasureTerm i) =
            Finset.sum interior.active fun i => ae.interiorIntegrandTerm i :=
        Finset.sum_congr rfl fun i hi =>
          ae.interiorMeasureTerm_eq_integrandTerm i hi
      have hboundary :
          (Finset.sum boundary.activeCharts fun x =>
              Finset.sum (boundary.boundaryPieces x) fun q =>
                measureTerms.boundaryMeasureTerm x q) =
            Finset.sum boundary.activeCharts fun x =>
              Finset.sum (boundary.boundaryPieces x) fun q =>
                ae.boundaryIntegrandTerm x q :=
        Finset.sum_congr rfl fun x hx =>
          Finset.sum_congr rfl fun q hq =>
            ae.boundaryMeasureTerm_eq_integrandTerm x hx q hq
      rw [hinterior, hboundary]

/--
The local analytic field packages fill the exact
`BulkIntegralPartitionInput.bulkIntegralLocalizes` equality.
-/
theorem bulkIntegralLocalizes
    (measureTerms : BulkMeasureLocalizationTermFields interior boundary)
    (ae : BulkIntegrandAELocalFields measureTerms)
    (_integrability : CompactSupportIntegrability ae)
    (boxAPI : MeasureBoxAPI ae) :
    measureTerms.globalBulkIntegral =
      (Finset.sum interior.active fun i => interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum boundary := by
  calc
    measureTerms.globalBulkIntegral =
        (Finset.sum interior.active fun i => ae.interiorIntegrandTerm i) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              ae.boundaryIntegrandTerm x q :=
      measureTerms.globalBulkIntegral_eq_integrandLocalSum ae
    _ =
        (Finset.sum interior.active fun i => interior.bulkTerm i) +
          Finset.sum boundary.activeCharts fun x =>
            Finset.sum (boundary.boundaryPieces x) fun q =>
              BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q := by
      have hinterior :
          (Finset.sum interior.active fun i => ae.interiorIntegrandTerm i) =
            Finset.sum interior.active fun i => interior.bulkTerm i :=
        Finset.sum_congr rfl fun i hi =>
          boxAPI.interiorIntegrandTerm_eq_boxTerm i hi
      have hboundary :
          (Finset.sum boundary.activeCharts fun x =>
              Finset.sum (boundary.boundaryPieces x) fun q =>
                ae.boundaryIntegrandTerm x q) =
            Finset.sum boundary.activeCharts fun x =>
              Finset.sum (boundary.boundaryPieces x) fun q =>
                BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q :=
        Finset.sum_congr rfl fun x hx =>
          Finset.sum_congr rfl fun q hq =>
            boxAPI.boundaryIntegrandTerm_eq_boxTerm x hx q hq
      rw [hinterior, hboundary]
    _ =
        (Finset.sum interior.active fun i => interior.bulkTerm i) +
          BoundaryPieceFamilyInput.boundaryBulkSum boundary := by
      rfl

/--
Construct `BulkIntegralPartitionInput` by filling its localization field from
the local measure, a.e., compact-support, and box-identification packages.
-/
def toBulkIntegralPartitionInput
    (measureTerms : BulkMeasureLocalizationTermFields interior boundary)
    (ae : BulkIntegrandAELocalFields measureTerms)
    (integrability : CompactSupportIntegrability ae)
    (boxAPI : MeasureBoxAPI ae) :
    BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece) where
  interior := interior
  boundary := boundary
  globalBulkIntegral := measureTerms.globalBulkIntegral
  bulkIntegralLocalizes :=
    measureTerms.bulkIntegralLocalizes ae integrability boxAPI

/--
Construct `BulkIntegralReconstructionData` from the local analytic field
packages.
-/
def toBulkIntegralReconstructionData
    (measureTerms : BulkMeasureLocalizationTermFields interior boundary)
    (ae : BulkIntegrandAELocalFields measureTerms)
    (integrability : CompactSupportIntegrability ae)
    (boxAPI : MeasureBoxAPI ae) :
    BulkIntegralReconstructionData I ω (ι ⊕ BoundaryChart) Unit BoundaryPiece :=
  (measureTerms.toBulkIntegralPartitionInput ae integrability boxAPI)
    |>.toBulkIntegralReconstructionData

/--
Package the constructed reconstruction data in the existing
`BulkMeasureLocalizationFields` shape used by the natural measure constructor.
-/
def toBulkMeasureLocalizationFields
    (measureTerms : BulkMeasureLocalizationTermFields interior boundary)
    (ae : BulkIntegrandAELocalFields measureTerms)
    (integrability : CompactSupportIntegrability ae)
    (boxAPI : MeasureBoxAPI ae) :
    BulkMeasureLocalizationFields
      (measureTerms.toBulkIntegralReconstructionData ae integrability boxAPI) :=
  BulkMeasureLocalizationFields.ofBulkMeasureEq
    measureTerms.bulkMeasureIntegral
    measureTerms.globalBulkIntegral_eq_bulkMeasureIntegral
    (by
      calc
        measureTerms.bulkMeasureIntegral = measureTerms.globalBulkIntegral :=
          measureTerms.globalBulkIntegral_eq_bulkMeasureIntegral.symm
        _ =
            (measureTerms.toBulkIntegralReconstructionData
              ae integrability boxAPI).globalBulkIntegral :=
          rfl
        _ =
            BulkIntegralReconstructionData.localBulkSum
              (measureTerms.toBulkIntegralReconstructionData
                ae integrability boxAPI) :=
          (measureTerms.toBulkIntegralReconstructionData
            ae integrability boxAPI).globalBulkIntegral_eq_localBulkSum')

@[simp]
theorem toBulkIntegralPartitionInput_globalBulkIntegral
    (measureTerms : BulkMeasureLocalizationTermFields interior boundary)
    (ae : BulkIntegrandAELocalFields measureTerms)
    (integrability : CompactSupportIntegrability ae)
    (boxAPI : MeasureBoxAPI ae) :
    (measureTerms.toBulkIntegralPartitionInput
      ae integrability boxAPI).globalBulkIntegral =
      measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem toBulkIntegralReconstructionData_globalBulkIntegral
    (measureTerms : BulkMeasureLocalizationTermFields interior boundary)
    (ae : BulkIntegrandAELocalFields measureTerms)
    (integrability : CompactSupportIntegrability ae)
    (boxAPI : MeasureBoxAPI ae) :
    (measureTerms.toBulkIntegralReconstructionData
      ae integrability boxAPI).globalBulkIntegral =
      measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem toBulkMeasureLocalizationFields_bulkMeasureIntegral
    (measureTerms : BulkMeasureLocalizationTermFields interior boundary)
    (ae : BulkIntegrandAELocalFields measureTerms)
    (integrability : CompactSupportIntegrability ae)
    (boxAPI : MeasureBoxAPI ae) :
    (measureTerms.toBulkMeasureLocalizationFields
      ae integrability boxAPI).bulkMeasureIntegral =
      measureTerms.bulkMeasureIntegral :=
  rfl

end BulkMeasureLocalizationTermFields

/--
Bundled input for the bulk localization constructor.

This is convenient for parent assembly code: all analytic field packages are
stored next to the localized interior and boundary families that they reference.
-/
structure BulkIntegralLocalizationInput where
  /-- Localized partition-of-unity interior pieces. -/
  interior : LocalizedInteriorPieces (ι := ι) I ω
  /-- Boundary-chart bulk pieces. -/
  boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece
  /-- Local measure-split fields. -/
  measureTerms : BulkMeasureLocalizationTermFields interior boundary
  /-- A.e. replacement fields for the local bulk integrands. -/
  integrandAE : BulkIntegrandAELocalFields measureTerms
  /-- Compact-support integrability hypotheses for the analytic localization. -/
  integrability : CompactSupportIntegrability integrandAE
  /-- Box-identification fields connecting analytic terms to project-local boxes. -/
  measureBoxAPI : MeasureBoxAPI integrandAE

namespace BulkIntegralLocalizationInput

/-- The bulk localization equality supplied by a bundled localization input. -/
theorem bulkIntegralLocalizes
    (D : BulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.measureTerms.globalBulkIntegral =
      (Finset.sum D.interior.active fun i => D.interior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum D.boundary :=
  D.measureTerms.bulkIntegralLocalizes
    D.integrandAE D.integrability D.measureBoxAPI

/--
Convert a bundled localization input to the existing partition-input package,
with `bulkIntegralLocalizes` filled.
-/
def toBulkIntegralPartitionInput
    (D : BulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    BulkIntegralPartitionInput (ι := ι)
      (I := I) (ω := ω) (BoundaryChart := BoundaryChart)
      (BoundaryPiece := BoundaryPiece) where
  interior := D.interior
  boundary := D.boundary
  globalBulkIntegral := D.measureTerms.globalBulkIntegral
  bulkIntegralLocalizes := D.bulkIntegralLocalizes

/--
Convert a bundled localization input directly to the existing bulk
reconstruction package.
-/
def toBulkIntegralReconstructionData
    (D : BulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    BulkIntegralReconstructionData I ω (ι ⊕ BoundaryChart) Unit BoundaryPiece :=
  D.toBulkIntegralPartitionInput.toBulkIntegralReconstructionData

/--
Convert a bundled localization input to the existing natural-measure
bulk-localization wrapper.
-/
def toBulkMeasureLocalizationFields
    (D : BulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    BulkMeasureLocalizationFields D.toBulkIntegralReconstructionData :=
  D.measureTerms.toBulkMeasureLocalizationFields
    D.integrandAE D.integrability D.measureBoxAPI

@[simp]
theorem toBulkIntegralPartitionInput_globalBulkIntegral
    (D : BulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralPartitionInput.globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem toBulkIntegralReconstructionData_globalBulkIntegral
    (D : BulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkIntegralReconstructionData.globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem toBulkMeasureLocalizationFields_bulkMeasureIntegral
    (D : BulkIntegralLocalizationInput
      (ι := ι) (I := I) (ω := ω)
      (BoundaryChart := BoundaryChart) (BoundaryPiece := BoundaryPiece)) :
    D.toBulkMeasureLocalizationFields.bulkMeasureIntegral =
      D.measureTerms.bulkMeasureIntegral :=
  rfl

end BulkIntegralLocalizationInput

end BulkIntegralLocalizationConstructor

end Stokes

end
