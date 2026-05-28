import Stokes.Global.M8Statement
import Stokes.Global.BulkMeasureLocalizationFields
import Stokes.Global.BoundaryCOVMeasureConstructor

/-!
# Constructors for M8 measure-localization data

This file is an M8-facing adapter layer.  It turns the existing bulk and
boundary measure packages into `M8MeasureLocalizationData`, so downstream M8
statements do not have to fill all fields by hand.

The genuinely analytic inputs remain explicit in the lower-level records:

* bulk measure terms, a.e. replacement, integrability, and box-identification;
* boundary measure localization, or a COV source-sum boundary package.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section M8MeasureConstructors

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/--
Bulk-side constructor data in the exact M8 shape.

The lower analytic work is delegated to the existing bulk packages.  This record
only records that they are indexed by the selected partition charts and by the
selected boundary target-image family used by M8.
-/
structure M8BulkMeasureConstructorData where
  /-- Localized partition-of-unity interior pieces. -/
  localizedInterior : LocalizedInteriorPieces (ι := M) I omega
  /-- The localized active set is the selected partition active set. -/
  localized_active :
    localizedInterior.active = selectedPartition.active
  /-- The localized coefficients are the selected partition coefficients. -/
  localized_coefficient :
    localizedInterior.coefficient =
      fun i x => selectedPartition.partition i x
  /-- The target-image boundary family uses the selected active set. -/
  targetImages_active :
    targetImages.activeCharts = selectedPartition.active
  /-- Measure-local bulk terms. -/
  measureTerms :
    BulkMeasureLocalizationTermFields localizedInterior targetImages
  /-- A.e. replacement fields for local bulk integrands. -/
  integrandAE : BulkIntegrandAELocalFields measureTerms
  /-- Compact-support integrability fields. -/
  integrability : CompactSupportIntegrability integrandAE
  /-- Identifications of analytic local terms with project-local box terms. -/
  measureBoxAPI : MeasureBoxAPI integrandAE

namespace M8BulkMeasureConstructorData

/-- Repackage the M8 bulk-side fields as the existing bulk localization input. -/
def toBulkIntegralLocalizationInput
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    BulkIntegralLocalizationInput
      (ι := M) (I := I) (ω := omega)
      (BoundaryChart := M) (BoundaryPiece := BoundaryPiece) where
  interior := D.localizedInterior
  boundary := targetImages
  measureTerms := D.measureTerms
  integrandAE := D.integrandAE
  integrability := D.integrability
  measureBoxAPI := D.measureBoxAPI

@[simp]
theorem toBulkIntegralLocalizationInput_interior
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.toBulkIntegralLocalizationInput.interior = D.localizedInterior :=
  rfl

@[simp]
theorem toBulkIntegralLocalizationInput_boundary
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.toBulkIntegralLocalizationInput.boundary = targetImages :=
  rfl

@[simp]
theorem toBulkIntegralLocalizationInput_globalBulkIntegral
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.toBulkIntegralLocalizationInput.measureTerms.globalBulkIntegral =
      D.measureTerms.globalBulkIntegral :=
  rfl

/-- The existing bulk packages give the split local-bulk reconstruction. -/
theorem bulkIntegralLocalizes
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.measureTerms.globalBulkIntegral =
      (Finset.sum D.localizedInterior.active fun i =>
        D.localizedInterior.bulkTerm i) +
        BoundaryPieceFamilyInput.boundaryBulkSum targetImages :=
  D.toBulkIntegralLocalizationInput.bulkIntegralLocalizes

/--
Bulk measure localization rewritten in the exact finite-sum shape required by
`M8MeasureLocalizationData`.
-/
theorem bulkMeasureIntegral_eq_localBulkSum
    (D : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)) :
    D.measureTerms.bulkMeasureIntegral =
      (Finset.sum selectedPartition.active fun x =>
        Finset.sum ({()} : Finset Unit) fun _q =>
          D.localizedInterior.bulkTerm x) +
        Finset.sum selectedPartition.active fun x =>
          Finset.sum (targetImages.boundaryPieces x) fun q =>
            BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q := by
  calc
    D.measureTerms.bulkMeasureIntegral =
        D.measureTerms.globalBulkIntegral :=
      D.measureTerms.globalBulkIntegral_eq_bulkMeasureIntegral.symm
    _ =
        (Finset.sum D.localizedInterior.active fun i =>
          D.localizedInterior.bulkTerm i) +
          BoundaryPieceFamilyInput.boundaryBulkSum targetImages :=
      D.bulkIntegralLocalizes
    _ =
        (Finset.sum selectedPartition.active fun x =>
          Finset.sum ({()} : Finset Unit) fun _q =>
            D.localizedInterior.bulkTerm x) +
          Finset.sum selectedPartition.active fun x =>
            Finset.sum (targetImages.boundaryPieces x) fun q =>
              BoundaryPieceFamilyInput.boundaryBulkTerm targetImages x q := by
      simp [D.localized_active, D.targetImages_active,
        BoundaryPieceFamilyInput.boundaryBulkSum]

/--
Build M8 bulk constructor data from an already bundled
`BulkIntegralLocalizationInput`.
-/
def ofBulkIntegralLocalizationInput
    (bulk :
      BulkIntegralLocalizationInput
        (ι := M) (I := I) (ω := omega)
        (BoundaryChart := M) (BoundaryPiece := BoundaryPiece))
    (hactive : bulk.interior.active = selectedPartition.active)
    (hcoefficient :
      bulk.interior.coefficient =
        fun i x => selectedPartition.partition i x)
    (hboundary : bulk.boundary = targetImages)
    (htargetActive : targetImages.activeCharts = selectedPartition.active) :
    M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages) := by
  subst targetImages
  exact
    { localizedInterior := bulk.interior
      localized_active := hactive
      localized_coefficient := hcoefficient
      targetImages_active := htargetActive
      measureTerms := bulk.measureTerms
      integrandAE := bulk.integrandAE
      integrability := bulk.integrability
      measureBoxAPI := bulk.measureBoxAPI }

end M8BulkMeasureConstructorData

namespace M8MeasureLocalizationData

/--
Construct `M8MeasureLocalizationData` from the M8-shaped bulk package and the
natural boundary measure-localization fields.
-/
def ofBulkAndBoundaryFields
    (bulk : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (globalBoundaryIntegral : Real)
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    M8MeasureLocalizationData I omega selectedPartition targetImages where
  localizedInterior := bulk.localizedInterior
  localized_active := bulk.localized_active
  localized_coefficient := bulk.localized_coefficient
  globalBulkIntegral := bulk.measureTerms.globalBulkIntegral
  bulkMeasureIntegral := bulk.measureTerms.bulkMeasureIntegral
  globalBulkIntegral_eq_bulkMeasureIntegral :=
    bulk.measureTerms.globalBulkIntegral_eq_bulkMeasureIntegral
  bulkMeasureIntegral_eq_localBulkSum :=
    bulk.bulkMeasureIntegral_eq_localBulkSum
  boundaryPartitionTerm := boundaryPartitionTerm
  globalBoundaryIntegral := globalBoundaryIntegral
  boundaryMeasureIntegral := boundary.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    boundary.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_partitionSum :=
    boundary.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem ofBulkAndBoundaryFields_globalBulkIntegral
    (bulk : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (globalBoundaryIntegral : Real)
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (ofBulkAndBoundaryFields
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm globalBoundaryIntegral boundary).globalBulkIntegral =
      bulk.measureTerms.globalBulkIntegral :=
  rfl

@[simp]
theorem ofBulkAndBoundaryFields_bulkMeasureIntegral
    (bulk : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (globalBoundaryIntegral : Real)
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (ofBulkAndBoundaryFields
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm globalBoundaryIntegral boundary).bulkMeasureIntegral =
      bulk.measureTerms.bulkMeasureIntegral :=
  rfl

@[simp]
theorem ofBulkAndBoundaryFields_boundaryMeasureIntegral
    (bulk : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (globalBoundaryIntegral : Real)
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (ofBulkAndBoundaryFields
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm globalBoundaryIntegral boundary).boundaryMeasureIntegral =
      boundary.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem ofBulkAndBoundaryFields_boundaryPartitionTerm
    (bulk : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (globalBoundaryIntegral : Real)
    (boundary :
      BoundaryMeasureLocalizationFields selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm
        globalBoundaryIntegral) :
    (ofBulkAndBoundaryFields
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      bulk boundaryPartitionTerm globalBoundaryIntegral boundary).boundaryPartitionTerm =
      boundaryPartitionTerm :=
  rfl

/--
Construct M8 measure-localization data from the analytic
`BoundaryMeasureLocalizationData` package.
-/
def ofBulkAndBoundaryLocalizationData
    {α : Type a} [MeasurableSpace α]
    {μ : Measure α}
    (bulk : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (boundaryData :
      BoundaryMeasureLocalizationData μ selectedPartition.active
        targetImages.boundaryPieces boundaryPartitionTerm)
    (globalBoundaryIntegral : Real)
    (hboundary :
      globalBoundaryIntegral = boundaryData.boundaryMeasureIntegral) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  ofBulkAndBoundaryFields
    (I := I) (omega := omega)
    (selectedPartition := selectedPartition)
    (targetImages := targetImages)
    bulk boundaryPartitionTerm globalBoundaryIntegral
    (boundaryData.toBoundaryMeasureLocalizationFields
      globalBoundaryIntegral hboundary)

/--
Convert a COV source-sum boundary package to the boundary fields required by
M8.  The equalities align the COV family indexing with the selected target-image
family.
-/
def boundaryFieldsOfCOV
    [IsManifold I 1 M]
    {F : BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece}
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (globalBoundaryIntegral : Real)
    (cov :
      BoundaryChartChangeOfVariablesFamily.BoundaryCOVMeasureReconstructionFields
        F boundaryPartitionTerm globalBoundaryIntegral)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : ∀ x, F.localPieces x = targetImages.boundaryPieces x) :
    BoundaryMeasureLocalizationFields selectedPartition.active
      targetImages.boundaryPieces boundaryPartitionTerm
      globalBoundaryIntegral where
  boundaryMeasureIntegral := cov.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    cov.manifoldBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_partitionSum := by
    simpa [selectedBoundaryPieceSum, hactive, hpieces] using
      cov.boundaryMeasureIntegral_eq_partitionSum

/--
Construct M8 measure-localization data from bulk measure packages and a
boundary COV source-sum package.
-/
def ofBulkAndBoundaryCOV
    [IsManifold I 1 M]
    {F : BoundaryChartChangeOfVariablesFamily I omega M BoundaryPiece}
    (bulk : M8BulkMeasureConstructorData
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages))
    (boundaryPartitionTerm : M -> BoundaryPiece -> Real)
    (globalBoundaryIntegral : Real)
    (cov :
      BoundaryChartChangeOfVariablesFamily.BoundaryCOVMeasureReconstructionFields
        F boundaryPartitionTerm globalBoundaryIntegral)
    (hactive : F.activeCharts = selectedPartition.active)
    (hpieces : ∀ x, F.localPieces x = targetImages.boundaryPieces x) :
    M8MeasureLocalizationData I omega selectedPartition targetImages :=
  ofBulkAndBoundaryFields
    (I := I) (omega := omega)
    (selectedPartition := selectedPartition)
    (targetImages := targetImages)
    bulk boundaryPartitionTerm globalBoundaryIntegral
    (boundaryFieldsOfCOV
      (I := I) (omega := omega)
      (selectedPartition := selectedPartition)
      (targetImages := targetImages)
      boundaryPartitionTerm globalBoundaryIntegral cov hactive hpieces)

end M8MeasureLocalizationData

end M8MeasureConstructors

end Stokes

end
