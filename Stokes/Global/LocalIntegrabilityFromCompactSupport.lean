import Stokes.Global.BulkCompactSupportIntegrabilityToMeasure
import Stokes.Global.BoundaryMeasureAEReconstruction

/-!
# Local integrability fields from compact support

This module is a thin adapter layer for the final Stokes constructors.  It
turns natural local hypotheses

* `tsupport` contained in a compact localization box, plus continuity on that
  box;
* zero outside a selected box;
* recorded local terms as set integrals

into the measure/integrability fields already used by the bulk and boundary
constructor APIs.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

universe u v w i c p a

section Generic

variable {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
variable [OpensMeasurableSpace X] [T2Space X]
variable {F : Type v} [NormedAddCommGroup F]
variable {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
variable {f : X -> F}

namespace CompactSupportIntegrabilityData

/-- Compact-support data gives `IntegrableOn` on any measurable local set. -/
theorem integrableOn_measurableSet
    (D : CompactSupportIntegrabilityData f) {s : Set X}
    (_hs : MeasurableSet s) :
    IntegrableOn f s μ :=
  D.integrableOn s

/-- Stable spelling for compact-support data from topological support in a box. -/
def ofTSupportSubsetCompactBox
    (box : Set X) (hbox : IsCompact box)
    (hcontinuous : ContinuousOn f box) (htsupport : tsupport f ⊆ box) :
    CompactSupportIntegrabilityData f :=
  CompactSupportIntegrabilityData.ofTSupportSubset box hbox hcontinuous
    htsupport

/-- Topological support in a compact box gives integrability on any local set. -/
theorem integrableOn_of_tsupport_subset_compactBox
    {box s : Set X} (hbox : IsCompact box)
    (hcontinuous : ContinuousOn f box) (htsupport : tsupport f ⊆ box)
    (_hs : MeasurableSet s) :
    IntegrableOn f s μ :=
  (CompactSupportIntegrabilityData.ofTSupportSubsetCompactBox
    (f := f) box hbox hcontinuous htsupport).integrableOn s

end CompactSupportIntegrabilityData

end Generic

section Boundary

variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {Chart : Type c} {Piece : Type p}
variable {activeCharts : Finset Chart}
variable {boundaryPieces : Chart -> Finset Piece}
variable {boundaryPartitionTerm : Chart -> Piece -> Real}

namespace BoundaryCompactMeasureFields

/--
Boundary compact-measure fields from already packaged compact-support data,
where the a.e. indicator reconstruction is generated from a finite
unlocalized piece-sum identity and zero-off-box facts.
-/
def ofCompactSupportPieceSumEq
    (boundaryIntegrand : α -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set α)
    (boundaryPieceIntegrand : Chart -> Piece -> α -> Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x -> MeasurableSet (boundaryPieceSet x q))
    (hcompact :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (hterm :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂μ)
    (hpiece :
      boundaryIntegrand =
        boundaryMeasurePieceSum activeCharts boundaryPieces
          boundaryPieceIntegrand)
    (hzero :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          ∀ y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    BoundaryCompactMeasureFields μ activeCharts boundaryPieces
      boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofCompactSupport
    (μ := μ) (activeCharts := activeCharts)
    (boundaryPieces := boundaryPieces)
    (boundaryPartitionTerm := boundaryPartitionTerm)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hcompact hterm
    (by
      have hpiece_ae :
          boundaryIntegrand =ᵐ[μ]
            boundaryMeasurePieceSum activeCharts boundaryPieces
              boundaryPieceIntegrand :=
        Filter.Eventually.of_forall fun y => congrFun hpiece y
      exact hpiece_ae.trans
        (boundaryMeasurePieceSum_ae_eq_indicatorSum_of_support_subset
          (μ := μ) activeCharts boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand
          (fun x hx q hq =>
            support_subset_of_eq_zero_off (hzero x hx q hq))))

/--
Boundary compact-measure fields from topological support contained in compact
piece boxes.  Measurability and `CompactSupportIntegrabilityData` are derived
from compactness, continuity on the box, and the `tsupport` containment.
-/
def ofTSupportSubsetCompactBox
    (boundaryIntegrand : α -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set α)
    (boundaryPieceIntegrand : Chart -> Piece -> α -> Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hcompactSet :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          IsCompact (boundaryPieceSet x q))
    (hcontinuous :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          ContinuousOn (boundaryPieceIntegrand x q)
            (boundaryPieceSet x q))
    (htsupport :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          tsupport (boundaryPieceIntegrand x q) ⊆ boundaryPieceSet x q)
    (hterm :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum activeCharts boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields μ activeCharts boundaryPieces
      boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofCompactSupport
    (μ := μ) (activeCharts := activeCharts)
    (boundaryPieces := boundaryPieces)
    (boundaryPartitionTerm := boundaryPartitionTerm)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure
    (fun x hx q hq => (hcompactSet x hx q hq).measurableSet)
    (fun x hx q hq =>
      CompactSupportIntegrabilityData.ofTSupportSubsetCompactBox
        (f := boundaryPieceIntegrand x q) (boundaryPieceSet x q)
        (hcompactSet x hx q hq) (hcontinuous x hx q hq)
        (htsupport x hx q hq))
    hterm hboundary

/--
Boundary compact-measure fields from compact boxes and zero-off-box support
control.  This is the common final-input shape: local pieces are continuous on
compact boxes, topologically supported in those boxes, vanish off the selected
box, and the recorded boundary term is the corresponding set integral.
-/
def ofTSupportSubsetCompactBoxPieceSumEq
    (boundaryIntegrand : α -> Real)
    (boundaryPieceSet : Chart -> Piece -> Set α)
    (boundaryPieceIntegrand : Chart -> Piece -> α -> Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hcompactSet :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          IsCompact (boundaryPieceSet x q))
    (hcontinuous :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          ContinuousOn (boundaryPieceIntegrand x q)
            (boundaryPieceSet x q))
    (htsupport :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          tsupport (boundaryPieceIntegrand x q) ⊆ boundaryPieceSet x q)
    (hterm :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂μ)
    (hpiece :
      boundaryIntegrand =
        boundaryMeasurePieceSum activeCharts boundaryPieces
          boundaryPieceIntegrand)
    (hzero :
      ∀ x, x ∈ activeCharts ->
        ∀ q, q ∈ boundaryPieces x ->
          ∀ y, y ∉ boundaryPieceSet x q ->
            boundaryPieceIntegrand x q y = 0) :
    BoundaryCompactMeasureFields μ activeCharts boundaryPieces
      boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofCompactSupportPieceSumEq
    (μ := μ) (activeCharts := activeCharts)
    (boundaryPieces := boundaryPieces)
    (boundaryPartitionTerm := boundaryPartitionTerm)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure
    (fun x hx q hq => (hcompactSet x hx q hq).measurableSet)
    (fun x hx q hq =>
      CompactSupportIntegrabilityData.ofTSupportSubsetCompactBox
        (f := boundaryPieceIntegrand x q) (boundaryPieceSet x q)
        (hcompactSet x hx q hq) (hcontinuous x hx q hq)
        (htsupport x hx q hq))
    hterm hpiece hzero

end BoundaryCompactMeasureFields

end Boundary

section BulkLocalCompactSupport

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type i}
variable {α : Type a} [TopologicalSpace α]
variable {BoundaryChart : Type c} {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {ω : ManifoldForm I M n}
variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {interiorLocalTerm : ι -> α -> Real}
variable {boundaryLocalTerm : BoundaryChart -> BoundaryPiece -> α -> Real}

namespace BulkLocalTermCompactSupportData

/--
Family constructor for local bulk compact-support data from `tsupport`
containment in compact localization boxes.
-/
def ofTSupportSubsetCompactBox
    (interiorBox : ι -> Set α)
    (boundaryBox : BoundaryChart -> BoundaryPiece -> Set α)
    (interior_isCompact :
      ∀ i, i ∈ interior.active -> IsCompact (interiorBox i))
    (boundary_isCompact :
      ∀ x, x ∈ boundary.activeCharts ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          IsCompact (boundaryBox x q))
    (interior_continuousOn :
      ∀ i, i ∈ interior.active ->
        ContinuousOn (interiorLocalTerm i) (interiorBox i))
    (boundary_continuousOn :
      ∀ x, x ∈ boundary.activeCharts ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          ContinuousOn (boundaryLocalTerm x q) (boundaryBox x q))
    (interior_tsupport_subset :
      ∀ i, i ∈ interior.active ->
        tsupport (interiorLocalTerm i) ⊆ interiorBox i)
    (boundary_tsupport_subset :
      ∀ x, x ∈ boundary.activeCharts ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          tsupport (boundaryLocalTerm x q) ⊆ boundaryBox x q) :
    BulkLocalTermCompactSupportData (α := α) interior boundary
      interiorLocalTerm boundaryLocalTerm where
  interiorSupportSet := interiorBox
  boundarySupportSet := boundaryBox
  interior_isCompact := interior_isCompact
  boundary_isCompact := boundary_isCompact
  interior_continuousOn := interior_continuousOn
  boundary_continuousOn := boundary_continuousOn
  interior_support_subset := by
    intro i hi
    exact (subset_tsupport (interiorLocalTerm i)).trans
      (interior_tsupport_subset i hi)
  boundary_support_subset := by
    intro x hx q hq
    exact (subset_tsupport (boundaryLocalTerm x q)).trans
      (boundary_tsupport_subset x hx q hq)

end BulkLocalTermCompactSupportData

end BulkLocalCompactSupport

section PureBulkMeasure

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type i}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {BoundaryChart : Type c} {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {ω : ManifoldForm I M n}
variable {interior : LocalizedInteriorPieces (ι := ι) I ω}
variable {boundary : BoundaryPieceFamilyInput I ω BoundaryChart BoundaryPiece}
variable {globalBulkIntegral : Real}

namespace CompactSupportBulkMeasureData

/--
Pure bulk measure package from compact-support data and zero-off-box facts.
The zero-off facts supply the support-in-box fields required for indicator
localization.
-/
def ofCompactSupportOffBox
    (F : α -> Real)
    (interiorLocalTerm : ι -> α -> Real)
    (boundaryLocalTerm : BoundaryChart -> BoundaryPiece -> α -> Real)
    (interiorBox : ι -> Set α)
    (boundaryBox : BoundaryChart -> BoundaryPiece -> Set α)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, F y ∂μ)
    (interiorBox_measurable :
      ∀ i, i ∈ interior.active -> MeasurableSet (interiorBox i))
    (boundaryBox_measurable :
      ∀ x, x ∈ boundary.activeCharts ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          MeasurableSet (boundaryBox x q))
    (interiorCompactSupport :
      ∀ i, i ∈ interior.active ->
        CompactSupportIntegrabilityData (interiorLocalTerm i))
    (boundaryCompactSupport :
      ∀ x, x ∈ boundary.activeCharts ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryLocalTerm x q))
    (interior_eq_zero_off_box :
      ∀ i, i ∈ interior.active ->
        ∀ y, y ∉ interiorBox i -> interiorLocalTerm i y = 0)
    (boundary_eq_zero_off_box :
      ∀ x, x ∈ boundary.activeCharts ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          ∀ y, y ∉ boundaryBox x q -> boundaryLocalTerm x q y = 0)
    (interiorBulkTerm_eq_integral :
      ∀ i, i ∈ interior.active ->
        interior.bulkTerm i = ∫ y in interiorBox i,
          interiorLocalTerm i y ∂μ)
    (boundaryBulkTerm_eq_integral :
      ∀ x, x ∈ boundary.activeCharts ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (F_ae_eq_unlocalizedSum :
      F =ᵐ[μ]
        bulkMeasureUnlocalizedSum interior.active boundary.activeCharts
          boundary.boundaryPieces interiorLocalTerm boundaryLocalTerm) :
    CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
      globalBulkIntegral where
  F := F
  interiorLocalTerm := interiorLocalTerm
  boundaryLocalTerm := boundaryLocalTerm
  interiorBox := interiorBox
  boundaryBox := boundaryBox
  globalBulkIntegral_eq_integral := globalBulkIntegral_eq_integral
  interiorBox_measurable := interiorBox_measurable
  boundaryBox_measurable := boundaryBox_measurable
  interiorCompactSupport := interiorCompactSupport
  boundaryCompactSupport := boundaryCompactSupport
  interior_support_subset_box := by
    intro i hi
    exact support_subset_of_eq_zero_off (interior_eq_zero_off_box i hi)
  boundary_support_subset_box := by
    intro x hx q hq
    exact support_subset_of_eq_zero_off
      (boundary_eq_zero_off_box x hx q hq)
  interiorBulkTerm_eq_integral := interiorBulkTerm_eq_integral
  boundaryBulkTerm_eq_integral := boundaryBulkTerm_eq_integral
  F_ae_eq_unlocalizedSum := F_ae_eq_unlocalizedSum

/--
Pure bulk measure package from `tsupport` contained in compact localization
boxes.  Measurability, compact-support data, and support-in-box fields are all
derived from the compact boxes.
-/
def ofTSupportSubsetCompactBox
    (F : α -> Real)
    (interiorLocalTerm : ι -> α -> Real)
    (boundaryLocalTerm : BoundaryChart -> BoundaryPiece -> α -> Real)
    (interiorBox : ι -> Set α)
    (boundaryBox : BoundaryChart -> BoundaryPiece -> Set α)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, F y ∂μ)
    (interior_isCompact :
      ∀ i, i ∈ interior.active -> IsCompact (interiorBox i))
    (boundary_isCompact :
      ∀ x, x ∈ boundary.activeCharts ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          IsCompact (boundaryBox x q))
    (interior_continuousOn :
      ∀ i, i ∈ interior.active ->
        ContinuousOn (interiorLocalTerm i) (interiorBox i))
    (boundary_continuousOn :
      ∀ x, x ∈ boundary.activeCharts ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          ContinuousOn (boundaryLocalTerm x q) (boundaryBox x q))
    (interior_tsupport_subset :
      ∀ i, i ∈ interior.active ->
        tsupport (interiorLocalTerm i) ⊆ interiorBox i)
    (boundary_tsupport_subset :
      ∀ x, x ∈ boundary.activeCharts ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          tsupport (boundaryLocalTerm x q) ⊆ boundaryBox x q)
    (interiorBulkTerm_eq_integral :
      ∀ i, i ∈ interior.active ->
        interior.bulkTerm i = ∫ y in interiorBox i,
          interiorLocalTerm i y ∂μ)
    (boundaryBulkTerm_eq_integral :
      ∀ x, x ∈ boundary.activeCharts ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (F_ae_eq_unlocalizedSum :
      F =ᵐ[μ]
        bulkMeasureUnlocalizedSum interior.active boundary.activeCharts
          boundary.boundaryPieces interiorLocalTerm boundaryLocalTerm) :
    CompactSupportBulkMeasureData (α := α) (μ := μ) interior boundary
      globalBulkIntegral where
  F := F
  interiorLocalTerm := interiorLocalTerm
  boundaryLocalTerm := boundaryLocalTerm
  interiorBox := interiorBox
  boundaryBox := boundaryBox
  globalBulkIntegral_eq_integral := globalBulkIntegral_eq_integral
  interiorBox_measurable := fun i hi => (interior_isCompact i hi).measurableSet
  boundaryBox_measurable := fun x hx q hq =>
    (boundary_isCompact x hx q hq).measurableSet
  interiorCompactSupport := fun i hi =>
    CompactSupportIntegrabilityData.ofTSupportSubsetCompactBox
      (f := interiorLocalTerm i) (interiorBox i)
      (interior_isCompact i hi) (interior_continuousOn i hi)
      (interior_tsupport_subset i hi)
  boundaryCompactSupport := fun x hx q hq =>
    CompactSupportIntegrabilityData.ofTSupportSubsetCompactBox
      (f := boundaryLocalTerm x q) (boundaryBox x q)
      (boundary_isCompact x hx q hq)
      (boundary_continuousOn x hx q hq)
      (boundary_tsupport_subset x hx q hq)
  interior_support_subset_box := fun i hi =>
    (subset_tsupport (interiorLocalTerm i)).trans
      (interior_tsupport_subset i hi)
  boundary_support_subset_box := fun x hx q hq =>
    (subset_tsupport (boundaryLocalTerm x q)).trans
      (boundary_tsupport_subset x hx q hq)
  interiorBulkTerm_eq_integral := interiorBulkTerm_eq_integral
  boundaryBulkTerm_eq_integral := boundaryBulkTerm_eq_integral
  F_ae_eq_unlocalizedSum := F_ae_eq_unlocalizedSum

end CompactSupportBulkMeasureData

end PureBulkMeasure

section SelectedBulkMeasure

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {BoundaryPiece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {ω : ManifoldForm I M n}
variable {P : SelectedBoxPartitionOfUnity I ω}
variable {boundary : BoundaryPieceFamilyInput I ω M BoundaryPiece}
variable {globalBulkIntegral : Real}

namespace SelectedBoxPartitionOfUnity

/--
Selected bulk reconstruction from compact boxes carrying the topological
support of every local scalar term.
-/
def bulkMeasureFromPartitionDataOfTSupportSubsetCompactBox
    (localized : LocalizedInteriorM8Fields I ω P)
    (boundary_active : boundary.activeCharts = P.active)
    (F : α -> Real)
    (interiorLocalTerm : M -> α -> Real)
    (boundaryLocalTerm : M -> BoundaryPiece -> α -> Real)
    (interiorBox : M -> Set α)
    (boundaryBox : M -> BoundaryPiece -> Set α)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, F y ∂μ)
    (interior_isCompact :
      ∀ i, i ∈ P.active -> IsCompact (interiorBox i))
    (boundary_isCompact :
      ∀ x, x ∈ P.active ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          IsCompact (boundaryBox x q))
    (interior_continuousOn :
      ∀ i, i ∈ P.active ->
        ContinuousOn (interiorLocalTerm i) (interiorBox i))
    (boundary_continuousOn :
      ∀ x, x ∈ P.active ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          ContinuousOn (boundaryLocalTerm x q) (boundaryBox x q))
    (interior_tsupport_subset :
      ∀ i, i ∈ P.active ->
        tsupport (interiorLocalTerm i) ⊆ interiorBox i)
    (boundary_tsupport_subset :
      ∀ x, x ∈ P.active ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          tsupport (boundaryLocalTerm x q) ⊆ boundaryBox x q)
    (interior_eq_zero_off_box :
      ∀ i, i ∈ P.active ->
        ∀ y, y ∉ interiorBox i -> interiorLocalTerm i y = 0)
    (boundary_eq_zero_off_box :
      ∀ x, x ∈ P.active ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          ∀ y, y ∉ boundaryBox x q -> boundaryLocalTerm x q y = 0)
    (interiorBulkTerm_eq_integral :
      ∀ i, i ∈ P.active ->
        localized.localizedInterior.bulkTerm i =
          ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (boundaryBulkTerm_eq_integral :
      ∀ x, x ∈ P.active ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ)
    (F_eq_partitionUnlocalizedSum :
      ∀ y,
        F y =
          bulkMeasureUnlocalizedSum P.active P.active
            boundary.boundaryPieces interiorLocalTerm boundaryLocalTerm y) :
    BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
      globalBulkIntegral :=
  SelectedBoxPartitionOfUnity.bulkMeasureFromPartitionData
    (P := P) (boundary := boundary)
    (globalBulkIntegral := globalBulkIntegral)
    localized boundary_active F interiorLocalTerm boundaryLocalTerm
    interiorBox boundaryBox globalBulkIntegral_eq_integral
    (fun i hi => (interior_isCompact i hi).measurableSet)
    (fun x hx q hq => (boundary_isCompact x hx q hq).measurableSet)
    (fun i hi =>
      CompactSupportIntegrabilityData.ofTSupportSubsetCompactBox
        (f := interiorLocalTerm i) (interiorBox i)
        (interior_isCompact i hi) (interior_continuousOn i hi)
        (interior_tsupport_subset i hi))
    (fun x hx q hq =>
      CompactSupportIntegrabilityData.ofTSupportSubsetCompactBox
        (f := boundaryLocalTerm x q) (boundaryBox x q)
        (boundary_isCompact x hx q hq)
        (boundary_continuousOn x hx q hq)
        (boundary_tsupport_subset x hx q hq))
    interior_eq_zero_off_box boundary_eq_zero_off_box
    interiorBulkTerm_eq_integral boundaryBulkTerm_eq_integral
    F_eq_partitionUnlocalizedSum

/--
Literal finite-sum specialization of
`bulkMeasureFromPartitionDataOfTSupportSubsetCompactBox`.
-/
def bulkMeasureFromLiteralPartitionSumOfTSupportSubsetCompactBox
    (localized : LocalizedInteriorM8Fields I ω P)
    (boundary_active : boundary.activeCharts = P.active)
    (interiorLocalTerm : M -> α -> Real)
    (boundaryLocalTerm : M -> BoundaryPiece -> α -> Real)
    (interiorBox : M -> Set α)
    (boundaryBox : M -> BoundaryPiece -> Set α)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral =
        ∫ y,
          bulkMeasureUnlocalizedSum P.active P.active
            boundary.boundaryPieces interiorLocalTerm boundaryLocalTerm y ∂μ)
    (interior_isCompact :
      ∀ i, i ∈ P.active -> IsCompact (interiorBox i))
    (boundary_isCompact :
      ∀ x, x ∈ P.active ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          IsCompact (boundaryBox x q))
    (interior_continuousOn :
      ∀ i, i ∈ P.active ->
        ContinuousOn (interiorLocalTerm i) (interiorBox i))
    (boundary_continuousOn :
      ∀ x, x ∈ P.active ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          ContinuousOn (boundaryLocalTerm x q) (boundaryBox x q))
    (interior_tsupport_subset :
      ∀ i, i ∈ P.active ->
        tsupport (interiorLocalTerm i) ⊆ interiorBox i)
    (boundary_tsupport_subset :
      ∀ x, x ∈ P.active ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          tsupport (boundaryLocalTerm x q) ⊆ boundaryBox x q)
    (interior_eq_zero_off_box :
      ∀ i, i ∈ P.active ->
        ∀ y, y ∉ interiorBox i -> interiorLocalTerm i y = 0)
    (boundary_eq_zero_off_box :
      ∀ x, x ∈ P.active ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          ∀ y, y ∉ boundaryBox x q -> boundaryLocalTerm x q y = 0)
    (interiorBulkTerm_eq_integral :
      ∀ i, i ∈ P.active ->
        localized.localizedInterior.bulkTerm i =
          ∫ y in interiorBox i, interiorLocalTerm i y ∂μ)
    (boundaryBulkTerm_eq_integral :
      ∀ x, x ∈ P.active ->
        ∀ q, q ∈ boundary.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBulkTerm boundary x q =
            ∫ y in boundaryBox x q, boundaryLocalTerm x q y ∂μ) :
    BulkMeasureFromPartitionData (α := α) (μ := μ) P boundary
      globalBulkIntegral :=
  SelectedBoxPartitionOfUnity.bulkMeasureFromPartitionDataOfTSupportSubsetCompactBox
    (P := P) (boundary := boundary)
    (globalBulkIntegral := globalBulkIntegral)
    localized boundary_active
    (bulkMeasureUnlocalizedSum P.active P.active boundary.boundaryPieces
      interiorLocalTerm boundaryLocalTerm)
    interiorLocalTerm boundaryLocalTerm interiorBox boundaryBox
    globalBulkIntegral_eq_integral interior_isCompact boundary_isCompact
    interior_continuousOn boundary_continuousOn
    interior_tsupport_subset boundary_tsupport_subset
    interior_eq_zero_off_box boundary_eq_zero_off_box
    interiorBulkTerm_eq_integral boundaryBulkTerm_eq_integral
    (fun _ => rfl)

end SelectedBoxPartitionOfUnity

end SelectedBulkMeasure

end Stokes

end
