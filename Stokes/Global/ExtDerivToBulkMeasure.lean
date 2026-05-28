import Stokes.Global.BulkMeasureLocalizationFields

/-!
# Exterior-derivative data to bulk-measure a.e. fields

This file is a thin bridge from the exterior-derivative reconstruction packages
to the bulk measure-localization constructor layer.

The mathematical a.e. comparison of scalar bulk integrands is supplied by
`BulkIntegrandAEData.ofExtDerivOnSupportData` and
`BulkIntegrandAEData.ofExtDerivEventuallyEqData`.  The remaining local
integral consequences are deliberately explicit fields: this file does not
prove that measure-local terms equal integrand-local terms.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ExtDerivToBulkMeasure

universe u w i c p ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type i}
variable {BoundaryChart : Type c} {BoundaryPiece : Type p}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {measureTerms : BulkMeasureLocalizationTermFields interior boundary}

namespace BulkIntegrandAELocalFields

/--
Package an already constructed chartwise a.e. bulk-integrand equality as the
local fields expected by the bulk measure-localization constructor.

The two equality fields identifying measure-local terms with integrand-local
terms remain explicit analytic inputs.
-/
def ofBulkIntegrandAEData
    (aeData : BulkIntegrandAEData I ω (ι ⊕ BoundaryChart))
    (hactive :
      aeData.activeCharts = interior.active.disjSum boundary.activeCharts)
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
    BulkIntegrandAELocalFields measureTerms where
  aeData := aeData
  aeData_active := hactive
  interiorIntegrandTerm := interiorIntegrandTerm
  boundaryIntegrandTerm := boundaryIntegrandTerm
  interiorMeasureTerm_eq_integrandTerm := hinterior
  boundaryMeasureTerm_eq_integrandTerm := hboundary

@[simp]
theorem ofBulkIntegrandAEData_aeData
    (aeData : BulkIntegrandAEData I ω (ι ⊕ BoundaryChart))
    (hactive :
      aeData.activeCharts = interior.active.disjSum boundary.activeCharts)
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
    (ofBulkIntegrandAEData (measureTerms := measureTerms)
      aeData hactive interiorIntegrandTerm boundaryIntegrandTerm
      hinterior hboundary).aeData = aeData :=
  rfl

@[simp]
theorem ofBulkIntegrandAEData_aeData_active
    (aeData : BulkIntegrandAEData I ω (ι ⊕ BoundaryChart))
    (hactive :
      aeData.activeCharts = interior.active.disjSum boundary.activeCharts)
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
    (ofBulkIntegrandAEData (measureTerms := measureTerms)
      aeData hactive interiorIntegrandTerm boundaryIntegrandTerm
      hinterior hboundary).aeData_active = hactive :=
  rfl

@[simp]
theorem ofBulkIntegrandAEData_interiorIntegrandTerm
    (aeData : BulkIntegrandAEData I ω (ι ⊕ BoundaryChart))
    (hactive :
      aeData.activeCharts = interior.active.disjSum boundary.activeCharts)
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
    (ofBulkIntegrandAEData (measureTerms := measureTerms)
      aeData hactive interiorIntegrandTerm boundaryIntegrandTerm
      hinterior hboundary).interiorIntegrandTerm = interiorIntegrandTerm :=
  rfl

@[simp]
theorem ofBulkIntegrandAEData_boundaryIntegrandTerm
    (aeData : BulkIntegrandAEData I ω (ι ⊕ BoundaryChart))
    (hactive :
      aeData.activeCharts = interior.active.disjSum boundary.activeCharts)
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
    (ofBulkIntegrandAEData (measureTerms := measureTerms)
      aeData hactive interiorIntegrandTerm boundaryIntegrandTerm
      hinterior hboundary).boundaryIntegrandTerm = boundaryIntegrandTerm :=
  rfl

/--
Construct the bulk measure-local a.e. fields from support-local exterior
derivative reconstruction.

The hypothesis `hmeasureSupport` is the genuine measure-side input: it says the
chosen chartwise measures are a.e. supported where the exterior-derivative
reconstruction is known.
-/
def ofExtDerivOnSupportData
    (D :
      ExtDerivOnSupportData I ω (ι ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ D.chartSupport x0 x1)
    (hactive :
      D.activeCharts = interior.active.disjSum boundary.activeCharts)
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
  ofBulkIntegrandAEData
    (measureTerms := measureTerms)
    (BulkIntegrandAEData.ofExtDerivOnSupportData
      (I := I) (ω := ω) D measure hmeasureSupport)
    (by simpa [BulkIntegrandAEData.ofExtDerivOnSupportData] using hactive)
    interiorIntegrandTerm boundaryIntegrandTerm hinterior hboundary

@[simp]
theorem ofExtDerivOnSupportData_aeData
    (D :
      ExtDerivOnSupportData I ω (ι ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ D.chartSupport x0 x1)
    (hactive :
      D.activeCharts = interior.active.disjSum boundary.activeCharts)
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
    (ofExtDerivOnSupportData (measureTerms := measureTerms)
      D measure hmeasureSupport hactive interiorIntegrandTerm
      boundaryIntegrandTerm hinterior hboundary).aeData =
      BulkIntegrandAEData.ofExtDerivOnSupportData
        (I := I) (ω := ω) D measure hmeasureSupport :=
  rfl

theorem ofExtDerivOnSupportData_ae_eq_global
    (D :
      ExtDerivOnSupportData I ω (ι ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ D.chartSupport x0 x1)
    (hactive :
      D.activeCharts = interior.active.disjSum boundary.activeCharts)
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
        (localizedFormSum I D.activeCharts D.coefficient ω) =ᵐ[measure x0 x1]
      bulkIntegrand I x0 x1 ω :=
  ((ofExtDerivOnSupportData (measureTerms := measureTerms)
      D measure hmeasureSupport hactive interiorIntegrandTerm
      boundaryIntegrandTerm hinterior hboundary).aeData).ae_eq_global x0 x1

/--
Construct the bulk measure-local a.e. fields from the eventual-equality
exterior-derivative package.
-/
def ofExtDerivEventuallyEqData
    (D :
      ExtDerivEventuallyEqData I ω (ι ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ D.chartSupport x0 x1)
    (hactive :
      D.activeCharts = interior.active.disjSum boundary.activeCharts)
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
  ofBulkIntegrandAEData
    (measureTerms := measureTerms)
    (BulkIntegrandAEData.ofExtDerivEventuallyEqData
      (I := I) (ω := ω) D measure hmeasureSupport)
    (by simpa [BulkIntegrandAEData.ofExtDerivEventuallyEqData,
        ExtDerivEventuallyEqData.toExtDerivOnSupportData] using hactive)
    interiorIntegrandTerm boundaryIntegrandTerm hinterior hboundary

@[simp]
theorem ofExtDerivEventuallyEqData_aeData
    (D :
      ExtDerivEventuallyEqData I ω (ι ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ D.chartSupport x0 x1)
    (hactive :
      D.activeCharts = interior.active.disjSum boundary.activeCharts)
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
    (ofExtDerivEventuallyEqData (measureTerms := measureTerms)
      D measure hmeasureSupport hactive interiorIntegrandTerm
      boundaryIntegrandTerm hinterior hboundary).aeData =
      BulkIntegrandAEData.ofExtDerivEventuallyEqData
        (I := I) (ω := ω) D measure hmeasureSupport :=
  rfl

theorem ofExtDerivEventuallyEqData_ae_eq_global
    (D :
      ExtDerivEventuallyEqData I ω (ι ⊕ BoundaryChart)
        ExtInteriorPiece ExtBoundaryPiece)
    (measure : M → M → Measure (Fin (n + 1) → Real))
    (hmeasureSupport :
      ∀ x0 x1, ∀ᶠ y in ae (measure x0 x1), y ∈ D.chartSupport x0 x1)
    (hactive :
      D.activeCharts = interior.active.disjSum boundary.activeCharts)
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
        (localizedFormSum I D.activeCharts D.coefficient ω) =ᵐ[measure x0 x1]
      bulkIntegrand I x0 x1 ω :=
  ((ofExtDerivEventuallyEqData (measureTerms := measureTerms)
      D measure hmeasureSupport hactive interiorIntegrandTerm
      boundaryIntegrandTerm hinterior hboundary).aeData).ae_eq_global x0 x1

end BulkIntegrandAELocalFields

end ExtDerivToBulkMeasure

end Stokes

end
