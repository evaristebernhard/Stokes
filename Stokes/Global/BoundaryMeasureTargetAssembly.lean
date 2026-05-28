import Stokes.Global.BoundaryMeasureFromPartition
import Stokes.Global.BoundaryMeasureToM8
import Stokes.Global.TargetImageResolvedToM8Input

/-!
# Boundary target-image assembly to measure localization

This file connects the boundary target-image assembly layer with the boundary
measure-localization constructors.

The genuine measure-theoretic content is still explicit: callers provide the
boundary integrand, piece support sets, piece integrands, integrability, and
a.e. indicator reconstruction.  The bookkeeping fields coming from target-image
assembly--active charts, boundary pieces, and boundary partition terms--are
projected from `BoundaryTargetImageToAssemblyInput` and its M8 resolved wrapper.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryMeasureTargetAssembly

universe u w c p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {α : Type a} [MeasurableSpace α]
variable {μ : Measure α}

namespace BoundaryTargetImageToAssemblyInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}

/-- Boundary partition data canonically exposed by a target-image assembly input. -/
def toBoundaryMeasurePartitionData
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    BoundaryMeasurePartitionData Chart Piece where
  activeCharts := D.activeCharts
  boundaryPieces := D.boundaryPieces
  boundaryPartitionTerm := D.boundaryPartitionTerm

@[simp]
theorem toBoundaryMeasurePartitionData_activeCharts
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    D.toBoundaryMeasurePartitionData.activeCharts = D.activeCharts :=
  rfl

@[simp]
theorem toBoundaryMeasurePartitionData_boundaryPieces
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    D.toBoundaryMeasurePartitionData.boundaryPieces = D.boundaryPieces :=
  rfl

@[simp]
theorem toBoundaryMeasurePartitionData_boundaryPartitionTerm
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece) :
    D.toBoundaryMeasurePartitionData.boundaryPartitionTerm =
      D.boundaryPartitionTerm :=
  rfl

/--
The partition term projected to measure-localization data is the same
project-local boundary integral recorded by the target-image assembly input.
-/
theorem toBoundaryMeasurePartitionData_boundaryPartitionTerm_eq_projectLocalBoundaryIntegral
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts)
    {q : Piece} (hq : q ∈ D.boundaryPieces x) :
    D.toBoundaryMeasurePartitionData.boundaryPartitionTerm x q =
      projectLocalBoundaryIntegral I
        (D.boundaryTargetChart x q) (D.partitionTargetChart x q) omega
        (D.partitionLowerCorner x q) (D.partitionUpperCorner x q) :=
  D.boundaryPartitionTerm_eq x hx q hq

/-- Compact/set-integral boundary measure fields indexed by target-image assembly data. -/
def boundaryCompactMeasureFieldsOfIntegrableOn
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → MeasurableSet (boundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          IntegrableOn (boundaryPieceIntegrand x q) (boundaryPieceSet x q) μ)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          D.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields μ D.activeCharts D.boundaryPieces
      D.boundaryPartitionTerm :=
  D.toBoundaryMeasurePartitionData.compactFieldsOfIntegrableOn
    (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable hterm hboundary

/--
Boundary measure localization indexed by target-image assembly data, using
explicit `IntegrableOn` hypotheses for each selected piece.
-/
def boundaryMeasureLocalizationDataOfIntegrableOn
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → MeasurableSet (boundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          IntegrableOn (boundaryPieceIntegrand x q) (boundaryPieceSet x q) μ)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          D.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    BoundaryMeasureLocalizationData μ D.activeCharts D.boundaryPieces
      D.boundaryPartitionTerm :=
  D.toBoundaryMeasurePartitionData.localizationDataOfIntegrableOn
    (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable hterm hboundary

/--
Boundary measure localization indexed by target-image assembly data, when the
caller already has indicator-level integrability and term equalities.
-/
def boundaryMeasureLocalizationDataOfIndicatorIntegrable
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand)
    (hpieceIntegrable :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          Integrable
            (boundaryMeasurePieceIndicator boundaryPieceSet
              boundaryPieceIntegrand x q) μ)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          D.boundaryPartitionTerm x q =
            ∫ y,
              boundaryMeasurePieceIndicator boundaryPieceSet
                boundaryPieceIntegrand x q y ∂μ) :
    BoundaryMeasureLocalizationData μ D.activeCharts D.boundaryPieces
      D.boundaryPartitionTerm :=
  D.toBoundaryMeasurePartitionData.localizationDataOfIndicatorIntegrable
    (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hboundary hpieceIntegrable hterm

section CompactSupport

variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
variable [IsFiniteMeasureOnCompacts μ]

/--
Boundary compact-measure fields from target-image assembly data and
compact-support integrability for each unlocalized active piece integrand.
-/
def boundaryCompactMeasureFieldsOfCompactSupport
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → MeasurableSet (boundaryPieceSet x q))
    (hcompact :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          D.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields μ D.activeCharts D.boundaryPieces
      D.boundaryPartitionTerm :=
  D.toBoundaryMeasurePartitionData.compactFieldsOfCompactSupport
    (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hcompact hterm hboundary

/--
Boundary measure localization from target-image assembly data and compact
support on each selected boundary-piece integrand.
-/
def boundaryMeasureLocalizationDataOfCompactSupport
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : Chart → Piece → Set α)
    (boundaryPieceIntegrand : Chart → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → MeasurableSet (boundaryPieceSet x q))
    (hcompact :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          D.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          boundaryPieceSet boundaryPieceIntegrand) :
    BoundaryMeasureLocalizationData μ D.activeCharts D.boundaryPieces
      D.boundaryPartitionTerm :=
  D.toBoundaryMeasurePartitionData.localizationDataOfCompactSupport
    (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hcompact hterm hboundary

end CompactSupport

end BoundaryTargetImageToAssemblyInput

namespace M8TargetImageInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/--
Selected-partition boundary measure data exposed by an M8 target-image input.
The active set is rewritten from the assembly active set by `active_eq`.
-/
def toSelectedBoundaryMeasurePartitionData
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas Piece) :
    BoundaryMeasurePartitionData M Piece where
  activeCharts := selectedPartition.active
  boundaryPieces := D.targetImages.boundaryPieces
  boundaryPartitionTerm := D.assembly.boundaryPartitionTerm

@[simp]
theorem toSelectedBoundaryMeasurePartitionData_activeCharts
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas Piece) :
    D.toSelectedBoundaryMeasurePartitionData.activeCharts =
      selectedPartition.active :=
  rfl

@[simp]
theorem toSelectedBoundaryMeasurePartitionData_boundaryPieces
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas Piece) :
    D.toSelectedBoundaryMeasurePartitionData.boundaryPieces =
      D.targetImages.boundaryPieces :=
  rfl

@[simp]
theorem toSelectedBoundaryMeasurePartitionData_boundaryPartitionTerm
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas Piece) :
    D.toSelectedBoundaryMeasurePartitionData.boundaryPartitionTerm =
      D.assembly.boundaryPartitionTerm :=
  rfl

/-- Boundary measure localization in the selected M8 shape, from `IntegrableOn` inputs. -/
def boundaryMeasureLocalizationDataOfIntegrableOn
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → Piece → Set α)
    (boundaryPieceIntegrand : M → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          IntegrableOn (boundaryPieceIntegrand x q) (boundaryPieceSet x q) μ)
    (hterm :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          D.assembly.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.targetImages.boundaryPieces boundaryPieceSet boundaryPieceIntegrand) :
    BoundaryMeasureLocalizationData μ selectedPartition.active
      D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm :=
  D.toSelectedBoundaryMeasurePartitionData.localizationDataOfIntegrableOn
    (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable hterm hboundary

/-- M8 boundary-only measure data from target-image assembly and explicit boundary fields. -/
def boundaryMeasureDataOfIntegrableOn
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → Piece → Set α)
    (boundaryPieceIntegrand : M → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          IntegrableOn (boundaryPieceIntegrand x q) (boundaryPieceSet x q) μ)
    (hterm :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          D.assembly.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.targetImages.boundaryPieces boundaryPieceSet boundaryPieceIntegrand)
    (globalBoundaryIntegral : Real)
    (hglobal :
      globalBoundaryIntegral =
        (D.boundaryMeasureLocalizationDataOfIntegrableOn
          (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
          boundaryMeasureIntegral hmeasure hset hintegrable hterm
          hboundary).boundaryMeasureIntegral) :
    M8BoundaryMeasureData I omega selectedPartition D.targetImages :=
  M8BoundaryMeasureData.ofBoundaryMeasureLocalizationData
    (I := I) (omega := omega) (selectedPartition := selectedPartition)
    (targetImages := D.targetImages)
    (D.boundaryMeasureLocalizationDataOfIntegrableOn
      (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
      boundaryMeasureIntegral hmeasure hset hintegrable hterm hboundary)
    globalBoundaryIntegral hglobal

end M8TargetImageInput

namespace M8TargetImageResolvedInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

/-- Boundary measure localization induced by a resolved target-image input. -/
def boundaryMeasureLocalizationDataOfIntegrableOn
    (D :
      M8TargetImageResolvedInput I omega selectedPartition
        orientedBoundaryAtlas Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → Piece → Set α)
    (boundaryPieceIntegrand : M → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.toM8TargetImageInput.targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.toM8TargetImageInput.targetImages.boundaryPieces x →
          IntegrableOn (boundaryPieceIntegrand x q) (boundaryPieceSet x q) μ)
    (hterm :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.toM8TargetImageInput.targetImages.boundaryPieces x →
          D.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.toM8TargetImageInput.targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    BoundaryMeasureLocalizationData μ selectedPartition.active
      D.toM8TargetImageInput.targetImages.boundaryPieces
      D.boundaryPartitionTerm :=
  D.toM8TargetImageInput.boundaryMeasureLocalizationDataOfIntegrableOn
    (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable hterm hboundary

/-- M8 boundary-only measure data induced by a resolved target-image input. -/
def boundaryMeasureDataOfIntegrableOn
    (D :
      M8TargetImageResolvedInput I omega selectedPartition
        orientedBoundaryAtlas Piece)
    (boundaryIntegrand : α → Real)
    (boundaryPieceSet : M → Piece → Set α)
    (boundaryPieceIntegrand : M → Piece → α → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (hset :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.toM8TargetImageInput.targetImages.boundaryPieces x →
          MeasurableSet (boundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.toM8TargetImageInput.targetImages.boundaryPieces x →
          IntegrableOn (boundaryPieceIntegrand x q) (boundaryPieceSet x q) μ)
    (hterm :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.toM8TargetImageInput.targetImages.boundaryPieces x →
          D.boundaryPartitionTerm x q =
            ∫ y in boundaryPieceSet x q, boundaryPieceIntegrand x q y ∂μ)
    (hboundary :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.toM8TargetImageInput.targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand)
    (globalBoundaryIntegral : Real)
    (hglobal :
      globalBoundaryIntegral =
        (D.boundaryMeasureLocalizationDataOfIntegrableOn
          (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
          boundaryMeasureIntegral hmeasure hset hintegrable hterm
          hboundary).boundaryMeasureIntegral) :
    M8BoundaryMeasureData I omega selectedPartition
      D.toM8TargetImageInput.targetImages :=
  D.toM8TargetImageInput.boundaryMeasureDataOfIntegrableOn
    (μ := μ) boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral hmeasure hset hintegrable hterm hboundary
    globalBoundaryIntegral hglobal

end M8TargetImageResolvedInput

end BoundaryMeasureTargetAssembly

end Stokes

end
