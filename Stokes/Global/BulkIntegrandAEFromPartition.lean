import Stokes.Global.ExtDerivToBulkMeasure
import Stokes.Global.LocalizedInteriorConstructors

/-!
# Bulk a.e. integrand packages from selected partitions

This file is a constructor layer for the bulk-measure side of the global
Stokes pipeline.

The existing APIs already know how to turn exterior-derivative reconstruction
data into `BulkIntegrandAEData`, and how to turn that into the
`BulkIntegrandAELocalFields` consumed by bulk measure localization.  Callers
coming from a selected partition, however, usually have a more geometric input:

* a selected finite partition and localized interior package;
* a boundary-piece family indexed by boundary charts;
* partition-local eventual equality on a controlled chart support;
* a.e. containment of the chosen chartwise measures in that support.

The constructors below package that route.  They do not prove the genuine
analytic facts, such as the chartwise equality
`d(sum rho_i omega) = d omega` or the measure-support statement; those remain
explicit fields.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section PartitionLocalizedAESupport

universe u w c i b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

namespace BulkIntegrandAEData

/--
Build chartwise a.e. bulk-integrand data from partition-local eventual equality,
using only a.e. containment in the controlled chart support.

This is the support-a.e. analogue of
`BulkIntegrandAEData.ofPartitionLocalizedEventuallyFields`, which requires the
chart support to cover every model-space point.
-/
def ofPartitionLocalizedEventuallyOnSupport
    (L : PartitionLocalizedEventuallyFields I ω Chart)
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (hactive : L.activeCharts = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ L.chartSupport x0 x1) :
    BulkIntegrandAEData I ω Chart :=
  ofExtDerivOnSupportData
    (L.toExtDerivOnSupportData R hactive) measure
    (by
      intro x0 x1
      simpa [PartitionLocalizedEventuallyFields.toExtDerivOnSupportData]
        using hmeasureSupport x0 x1)

/-- Projection theorem for the support-a.e. partition-local constructor. -/
theorem ofPartitionLocalizedEventuallyOnSupport_ae_eq_global
    (L : PartitionLocalizedEventuallyFields I ω Chart)
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (hactive : L.activeCharts = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ L.chartSupport x0 x1)
    (x0 x1 : M) :
    bulkIntegrand I x0 x1
        (localizedFormSum I R.activeCharts L.coefficient ω) =ᵐ[measure x0 x1]
      bulkIntegrand I x0 x1 ω := by
  simpa [ofPartitionLocalizedEventuallyOnSupport,
    PartitionLocalizedEventuallyFields.toExtDerivOnSupportData] using
    (ofPartitionLocalizedEventuallyOnSupport
      (I := I) (ω := ω) L R hactive measure hmeasureSupport).ae_eq_global x0 x1

@[simp]
theorem ofPartitionLocalizedEventuallyOnSupport_activeCharts
    (L : PartitionLocalizedEventuallyFields I ω Chart)
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (hactive : L.activeCharts = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ L.chartSupport x0 x1) :
    (ofPartitionLocalizedEventuallyOnSupport
      (I := I) (ω := ω) L R hactive measure hmeasureSupport).activeCharts =
      R.activeCharts := by
  rfl

end BulkIntegrandAEData

end PartitionLocalizedAESupport

section PartitionLocalizedAELocalFields

universe u w ιu cb pb ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type ιu}
variable {BoundaryChart : Type cb} {BoundaryPiece : Type pb}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {measureTerms : BulkMeasureLocalizationTermFields interior boundary}

namespace BulkIntegrandAELocalFields

/--
Build the local a.e. replacement fields from partition-local eventual equality.

The remaining equalities identifying measure-local terms with integrand-local
terms are still explicit: they are the analytic local integral comparison, not
formal bookkeeping.
-/
def ofPartitionLocalizedEventuallyOnSupport
    (L : PartitionLocalizedEventuallyFields I ω (ι ⊕ BoundaryChart))
    (R :
      PartitionReconstructionData I ω (ι ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hLR : L.activeCharts = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ L.chartSupport x0 x1)
    (hactive : R.activeCharts = interior.active.disjSum boundary.activeCharts)
    (interiorIntegrandTerm : ι → Real)
    (boundaryIntegrandTerm : BoundaryChart → BoundaryPiece → Real)
    (hinterior :
      ∀ i, i ∈ interior.active →
        measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i)
    (hboundary :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          measureTerms.boundaryMeasureTerm x q =
            boundaryIntegrandTerm x q) :
    BulkIntegrandAELocalFields measureTerms :=
  ofExtDerivOnSupportData
    (measureTerms := measureTerms)
    (L.toExtDerivOnSupportData R hLR) measure
    (by
      intro x0 x1
      simpa [PartitionLocalizedEventuallyFields.toExtDerivOnSupportData]
        using hmeasureSupport x0 x1)
    (by
      simpa [PartitionLocalizedEventuallyFields.toExtDerivOnSupportData]
        using hactive)
    interiorIntegrandTerm boundaryIntegrandTerm hinterior hboundary

@[simp]
theorem ofPartitionLocalizedEventuallyOnSupport_aeData
    (L : PartitionLocalizedEventuallyFields I ω (ι ⊕ BoundaryChart))
    (R :
      PartitionReconstructionData I ω (ι ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hLR : L.activeCharts = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ L.chartSupport x0 x1)
    (hactive : R.activeCharts = interior.active.disjSum boundary.activeCharts)
    (interiorIntegrandTerm : ι → Real)
    (boundaryIntegrandTerm : BoundaryChart → BoundaryPiece → Real)
    (hinterior :
      ∀ i, i ∈ interior.active →
        measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i)
    (hboundary :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          measureTerms.boundaryMeasureTerm x q =
            boundaryIntegrandTerm x q) :
    (ofPartitionLocalizedEventuallyOnSupport
      (measureTerms := measureTerms)
      L R hLR measure hmeasureSupport hactive interiorIntegrandTerm
      boundaryIntegrandTerm hinterior hboundary).aeData =
      BulkIntegrandAEData.ofPartitionLocalizedEventuallyOnSupport
        (I := I) (ω := ω) L R hLR measure hmeasureSupport := by
  rfl

theorem ofPartitionLocalizedEventuallyOnSupport_ae_eq_global
    (L : PartitionLocalizedEventuallyFields I ω (ι ⊕ BoundaryChart))
    (R :
      PartitionReconstructionData I ω (ι ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (hLR : L.activeCharts = R.activeCharts)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ L.chartSupport x0 x1)
    (hactive : R.activeCharts = interior.active.disjSum boundary.activeCharts)
    (interiorIntegrandTerm : ι → Real)
    (boundaryIntegrandTerm : BoundaryChart → BoundaryPiece → Real)
    (hinterior :
      ∀ i, i ∈ interior.active →
        measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i)
    (hboundary :
      ∀ x, x ∈ boundary.activeCharts →
        ∀ q, q ∈ boundary.boundaryPieces x →
          measureTerms.boundaryMeasureTerm x q =
            boundaryIntegrandTerm x q)
    (x0 x1 : M) :
    bulkIntegrand I x0 x1
        (localizedFormSum I R.activeCharts L.coefficient ω) =ᵐ[measure x0 x1]
      bulkIntegrand I x0 x1 ω :=
  ((ofPartitionLocalizedEventuallyOnSupport
      (measureTerms := measureTerms)
      L R hLR measure hmeasureSupport hactive interiorIntegrandTerm
      boundaryIntegrandTerm hinterior hboundary).aeData).ae_eq_global x0 x1

end BulkIntegrandAELocalFields

end PartitionLocalizedAELocalFields

section SelectedPartitionBulkIntegrandAE

universe u w cb pb ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryChart : Type cb} {BoundaryPiece : Type pb}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- Combined chart labels for a selected interior partition and boundary family. -/
def selectedPartitionBulkActive
    (P : SelectedBoxPartitionOfUnity I ω)
    (boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece) :
    Finset (M ⊕ BoundaryChart) :=
  P.active.disjSum boundary.activeCharts

/--
The partition coefficient on combined chart labels.

Interior labels use the selected partition coefficient.  Boundary labels are
given coefficient zero: boundary bulk terms are integration pieces, not extra
partition-of-unity summands.
-/
def selectedPartitionBulkCoefficient
    (P : SelectedBoxPartitionOfUnity I ω) :
    M ⊕ BoundaryChart → M → Real
  | Sum.inl i => fun x => P.partition i x
  | Sum.inr _ => fun _ => 0

@[simp]
theorem selectedPartitionBulkActive_eq
    (P : SelectedBoxPartitionOfUnity I ω)
    (boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece) :
    selectedPartitionBulkActive P boundary =
      P.active.disjSum boundary.activeCharts :=
  rfl

@[simp]
theorem selectedPartitionBulkCoefficient_inl
    (P : SelectedBoxPartitionOfUnity I ω) (i : M) :
    selectedPartitionBulkCoefficient
        (BoundaryChart := BoundaryChart) P
        (Sum.inl i) =
      fun x => P.partition i x :=
  rfl

@[simp]
theorem selectedPartitionBulkCoefficient_inr
    (P : SelectedBoxPartitionOfUnity I ω) (x : BoundaryChart) :
    selectedPartitionBulkCoefficient
        (BoundaryChart := BoundaryChart) P
        (Sum.inr x) =
      fun _ : M => 0 :=
  rfl

/--
Selected-partition-facing input for the bulk a.e. integrand package.

The record keeps the real analytic work as fields: partition-local eventual
equality, a.e. measure support, and local measure/integrand identifications.
Its projections produce the `BulkIntegrandAELocalFields` required by the bulk
measure-localization constructor.
-/
structure BulkIntegrandAEFromPartitionData
    (P : SelectedBoxPartitionOfUnity I ω)
    (boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece)
    (localized : LocalizedInteriorM8Fields I ω P)
    (measureTerms :
      BulkMeasureLocalizationTermFields localized.localizedInterior boundary) where
  /-- Partition-local equality package on the combined interior/boundary labels. -/
  localizedEventually :
    PartitionLocalizedEventuallyFields I ω (M ⊕ BoundaryChart)
  /-- Reconstruction fields with the same combined chart labels. -/
  reconstruction :
    PartitionReconstructionData I ω (M ⊕ BoundaryChart)
      ExtInteriorPiece ExtBoundaryPiece
  /-- The eventual-equality package uses the selected combined active labels. -/
  localizedEventually_active :
    localizedEventually.activeCharts = selectedPartitionBulkActive P boundary
  /-- The eventual-equality package uses the selected combined coefficients. -/
    localizedEventually_coefficient :
    localizedEventually.coefficient =
      selectedPartitionBulkCoefficient
        (BoundaryChart := BoundaryChart) P
  /-- The eventual-equality and reconstruction packages use the same active labels. -/
  localizedEventually_active_eq_reconstruction :
    localizedEventually.activeCharts = reconstruction.activeCharts
  /-- Chartwise measure used for the scalar bulk integrand comparison. -/
  measure : M → M → Measure (Fin (n + 1) → Real)
  /-- The chosen measures are a.e. supported where the local equality is known. -/
  hmeasureSupport :
    ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1),
      y ∈ localizedEventually.chartSupport x0 x1
  /-- Integrand-local term for one selected interior chart. -/
  interiorIntegrandTerm : M → Real
  /-- Integrand-local term for one selected boundary piece. -/
  boundaryIntegrandTerm : BoundaryChart → BoundaryPiece → Real
  /-- Active measure-local interior terms equal the chosen integrand terms. -/
  interiorMeasureTerm_eq_integrandTerm :
    ∀ i, i ∈ localized.localizedInterior.active →
      measureTerms.interiorMeasureTerm i = interiorIntegrandTerm i
  /-- Active measure-local boundary terms equal the chosen integrand terms. -/
  boundaryMeasureTerm_eq_integrandTerm :
    ∀ x, x ∈ boundary.activeCharts →
      ∀ q, q ∈ boundary.boundaryPieces x →
        measureTerms.boundaryMeasureTerm x q =
          boundaryIntegrandTerm x q

namespace BulkIntegrandAEFromPartitionData

variable {P : SelectedBoxPartitionOfUnity I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {localized : LocalizedInteriorM8Fields I ω P}
variable {measureTerms :
  BulkMeasureLocalizationTermFields localized.localizedInterior boundary}

/-- The reconstruction package is active on the localized interior plus boundary labels. -/
theorem reconstruction_active_eq_localized_disjSum
    (D :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms) :
    D.reconstruction.activeCharts =
      localized.localizedInterior.active.disjSum boundary.activeCharts := by
  calc
    D.reconstruction.activeCharts = D.localizedEventually.activeCharts :=
      D.localizedEventually_active_eq_reconstruction.symm
    _ = selectedPartitionBulkActive P boundary :=
    D.localizedEventually_active
    _ = localized.localizedInterior.active.disjSum boundary.activeCharts := by
      simp [selectedPartitionBulkActive]

/-- Forget the selected-partition wrapper and expose the raw a.e. package. -/
def toBulkIntegrandAEData
    (D :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms) :
    BulkIntegrandAEData I ω (M ⊕ BoundaryChart) :=
  BulkIntegrandAEData.ofPartitionLocalizedEventuallyOnSupport
    D.localizedEventually D.reconstruction
    D.localizedEventually_active_eq_reconstruction
    D.measure D.hmeasureSupport

@[simp]
theorem toBulkIntegrandAEData_activeCharts
    (D :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms) :
    D.toBulkIntegrandAEData.activeCharts =
      localized.localizedInterior.active.disjSum boundary.activeCharts := by
  simpa [toBulkIntegrandAEData,
    BulkIntegrandAEData.ofPartitionLocalizedEventuallyOnSupport,
    PartitionLocalizedEventuallyFields.toExtDerivOnSupportData] using
    D.reconstruction_active_eq_localized_disjSum

/-- The selected-partition package fills the bulk measure a.e. local fields. -/
def toBulkIntegrandAELocalFields
    (D :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms) :
    BulkIntegrandAELocalFields measureTerms :=
  BulkIntegrandAELocalFields.ofPartitionLocalizedEventuallyOnSupport
    (measureTerms := measureTerms)
    D.localizedEventually D.reconstruction
    D.localizedEventually_active_eq_reconstruction
    D.measure D.hmeasureSupport
    D.reconstruction_active_eq_localized_disjSum
    D.interiorIntegrandTerm D.boundaryIntegrandTerm
    D.interiorMeasureTerm_eq_integrandTerm
    D.boundaryMeasureTerm_eq_integrandTerm

@[simp]
theorem toBulkIntegrandAELocalFields_aeData
    (D :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms) :
    D.toBulkIntegrandAELocalFields.aeData = D.toBulkIntegrandAEData := by
  rfl

theorem ae_eq_global
    (D :
      BulkIntegrandAEFromPartitionData
        (ExtInteriorPiece := ExtInteriorPiece)
        (ExtBoundaryPiece := ExtBoundaryPiece)
        P boundary localized measureTerms)
    (x0 x1 : M) :
    bulkIntegrand I x0 x1
        (localizedFormSum I D.reconstruction.activeCharts
          D.localizedEventually.coefficient ω) =ᵐ[D.measure x0 x1]
      bulkIntegrand I x0 x1 ω :=
  D.toBulkIntegrandAEData.ae_eq_global x0 x1

end BulkIntegrandAEFromPartitionData

end SelectedPartitionBulkIntegrandAE

end Stokes

end
