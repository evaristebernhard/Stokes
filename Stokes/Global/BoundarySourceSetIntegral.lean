import Stokes.Global.BoundaryMeasureFromTargetCOV
import Stokes.Global.BoundaryMeasureProjectLocal

/-!
# Source boundary project-local set integrals

This file isolates the remaining source-side measure equality used by
`BoundaryMeasureFromTargetCOVInput`.

The genuine measure theorem is still not inferred here.  The main constructor
shows that the needed source equality can be obtained from the existing
`ProjectLocalBoundaryMeasureData` route once its project-local charts, pieces,
and source boxes are aligned with the selected target-image source data.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundarySourceSetIntegral

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace M8TargetImageInput

variable
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)

/-- The source-side project-local boundary integral used before target COV. -/
def sourceProjectLocalBoundaryIntegral (x : M) (q : BoundaryPiece) : Real :=
  projectLocalBoundaryIntegral I
    (D.targetImages.sourceChart x q)
    (D.targetImages.boundarySourceChart x q) omega
    (D.targetImages.sourceLowerCorner x q)
    (D.targetImages.sourceUpperCorner x q)

@[simp]
theorem sourceProjectLocalBoundaryIntegral_eq
    (x : M) (q : BoundaryPiece) :
    D.sourceProjectLocalBoundaryIntegral x q =
      projectLocalBoundaryIntegral I
        (D.targetImages.sourceChart x q)
        (D.targetImages.boundarySourceChart x q) omega
        (D.targetImages.sourceLowerCorner x q)
        (D.targetImages.sourceUpperCorner x q) := by
  rfl

end M8TargetImageInput

/--
Minimal source-side measure input.

This is exactly the analytic field that `BoundaryMeasureFromTargetCOVInput`
needs before the already-proved oriented target COV transports the source
set-integral equality to the selected boundary partition term.
-/
structure BoundarySourceSetIntegralInput
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (μ : Measure α) where
  /-- Selected boundary-piece support set. -/
  boundaryPieceSet : M → BoundaryPiece → Set α
  /-- Selected boundary-piece scalar integrand. -/
  boundaryPieceIntegrand : M → BoundaryPiece → α → Real
  /-- Source project-local boundary integral as a genuine localized set integral. -/
  sourceProjectLocal_eq_setIntegral :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        D.sourceProjectLocalBoundaryIntegral x q =
          ∫ y in boundaryPieceSet x q,
            boundaryPieceIntegrand x q y ∂μ

namespace BoundarySourceSetIntegralInput

variable
    {D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
    (S : BoundarySourceSetIntegralInput (α := α) D μ)

/-- Expanded form of the source set-integral equality expected downstream. -/
theorem sourceProjectLocal_eq_setIntegral_expanded
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    projectLocalBoundaryIntegral I
        (D.targetImages.sourceChart x q)
        (D.targetImages.boundarySourceChart x q) omega
        (D.targetImages.sourceLowerCorner x q)
        (D.targetImages.sourceUpperCorner x q) =
      ∫ y in S.boundaryPieceSet x q,
        S.boundaryPieceIntegrand x q y ∂μ := by
  simpa [M8TargetImageInput.sourceProjectLocalBoundaryIntegral] using
    S.sourceProjectLocal_eq_setIntegral x hx q hq

/-- Fill the source-side field of `BoundaryMeasureFromTargetCOVInput`. -/
theorem toBoundaryMeasureFromTargetCOV_sourceProjectLocal_eq_setIntegral :
    ∀ x, x ∈ selectedPartition.active →
      ∀ q, q ∈ D.targetImages.boundaryPieces x →
        projectLocalBoundaryIntegral I
            (D.targetImages.sourceChart x q)
            (D.targetImages.boundarySourceChart x q) omega
            (D.targetImages.sourceLowerCorner x q)
            (D.targetImages.sourceUpperCorner x q) =
          ∫ y in S.boundaryPieceSet x q,
            S.boundaryPieceIntegrand x q y ∂μ := by
  intro x hx q hq
  exact S.sourceProjectLocal_eq_setIntegral_expanded hx hq

/--
Assemble the full COV-backed boundary-measure input once the source set-integral
package and the remaining independent measure fields are supplied.
-/
def toBoundaryMeasureFromTargetCOVInput
    (boundaryIntegrand : α → Real)
    (boundaryMeasureIntegral : Real)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPieceSet_measurable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          MeasurableSet (S.boundaryPieceSet x q))
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (S.boundaryPieceIntegrand x q))
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.targetImages.boundaryPieces S.boundaryPieceSet
          S.boundaryPieceIntegrand)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral) :
    BoundaryMeasureFromTargetCOVInput (α := α) D μ where
  boundaryIntegrand := boundaryIntegrand
  boundaryPieceSet := S.boundaryPieceSet
  boundaryPieceIntegrand := S.boundaryPieceIntegrand
  boundaryMeasureIntegral := boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral := boundaryMeasureIntegral_eq_integral
  boundaryPieceSet_measurable := boundaryPieceSet_measurable
  boundaryPieceCompact := boundaryPieceCompact
  sourceProjectLocal_eq_setIntegral :=
    S.toBoundaryMeasureFromTargetCOV_sourceProjectLocal_eq_setIntegral
  boundaryIntegrand_ae_eq_indicatorSum := boundaryIntegrand_ae_eq_indicatorSum
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    globalBoundaryIntegral_eq_boundaryMeasureIntegral

@[simp]
theorem toBoundaryMeasureFromTargetCOVInput_boundaryPieceSet
    (boundaryIntegrand : α → Real)
    (boundaryMeasureIntegral : Real)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂μ)
    (boundaryPieceSet_measurable :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          MeasurableSet (S.boundaryPieceSet x q))
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (S.boundaryPieceIntegrand x q))
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.targetImages.boundaryPieces S.boundaryPieceSet
          S.boundaryPieceIntegrand)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral) :
    (S.toBoundaryMeasureFromTargetCOVInput boundaryIntegrand
      boundaryMeasureIntegral boundaryMeasureIntegral_eq_integral
      boundaryPieceSet_measurable boundaryPieceCompact
      boundaryIntegrand_ae_eq_indicatorSum globalBoundaryIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral).boundaryPieceSet =
      S.boundaryPieceSet := by
  rfl

end BoundarySourceSetIntegralInput

/--
Alignment between a project-local boundary-measure package and the source side
of the selected target-image data.

This record is only coordinate bookkeeping: it says the project-local source
chart, target chart, and source box are the same objects as the target-image
source chart, boundary source chart, and source box.
-/
structure BoundarySourceProjectLocalAlignment
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)
    (P : ProjectLocalGlobalStokesData I omega M BoundaryPiece) where
  /-- Active labels agree with the selected partition labels. -/
  activeCharts_eq : P.activeCharts = selectedPartition.active
  /-- Boundary-piece labels agree pointwise. -/
  localPieces_eq : ∀ x, P.localPieces x = D.targetImages.boundaryPieces x
  /-- Project-local source chart is the target-image source chart. -/
  sourceChart_eq : ∀ x q, P.sourceChart x q = D.targetImages.sourceChart x q
  /-- Project-local target chart is the target-image boundary source chart. -/
  targetChart_eq : ∀ x q, P.targetChart x q = D.targetImages.boundarySourceChart x q
  /-- Project-local lower corner is the target-image source lower corner. -/
  lowerCorner_eq : ∀ x q, P.lowerCorner x q = D.targetImages.sourceLowerCorner x q
  /-- Project-local upper corner is the target-image source upper corner. -/
  upperCorner_eq : ∀ x q, P.upperCorner x q = D.targetImages.sourceUpperCorner x q

namespace BoundarySourceProjectLocalAlignment

variable
    {D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
    {P : ProjectLocalGlobalStokesData I omega M BoundaryPiece}

/-- Convert selected active membership to the aligned project-local package. -/
theorem mem_active
    (A : BoundarySourceProjectLocalAlignment D P)
    {x : M} (hx : x ∈ selectedPartition.active) :
    x ∈ P.activeCharts := by
  simpa [A.activeCharts_eq] using hx

/-- Convert selected boundary-piece membership to the aligned project-local package. -/
theorem mem_localPiece
    (A : BoundarySourceProjectLocalAlignment D P)
    {x : M} {q : BoundaryPiece}
    (hq : q ∈ D.targetImages.boundaryPieces x) :
    q ∈ P.localPieces x := by
  simpa [A.localPieces_eq x] using hq

/--
The aligned project-local measure package supplies the source set-integral
input required by the target-COV boundary route.
-/
def toBoundarySourceSetIntegralInput
    (A : BoundarySourceProjectLocalAlignment D P)
    (B : ProjectLocalBoundaryMeasureData (α := α) P μ) :
    BoundarySourceSetIntegralInput (α := α) D μ where
  boundaryPieceSet := B.boundaryPieceSet
  boundaryPieceIntegrand := B.boundaryPieceIntegrand
  sourceProjectLocal_eq_setIntegral := by
    intro x hx q hq
    have hxP : x ∈ P.activeCharts := A.mem_active hx
    have hqP : q ∈ P.localPieces x := A.mem_localPiece hq
    have hpiece :=
      B.projectLocalBoundaryIntegral_eq_setIntegral x hxP q hqP
    simpa [M8TargetImageInput.sourceProjectLocalBoundaryIntegral,
      A.sourceChart_eq x q, A.targetChart_eq x q,
      A.lowerCorner_eq x q, A.upperCorner_eq x q] using hpiece

@[simp]
theorem toBoundarySourceSetIntegralInput_boundaryPieceSet
    (A : BoundarySourceProjectLocalAlignment D P)
    (B : ProjectLocalBoundaryMeasureData (α := α) P μ) :
    (A.toBoundarySourceSetIntegralInput B).boundaryPieceSet =
      B.boundaryPieceSet := by
  rfl

/--
Expanded projection of the source set-integral equality obtained from an
aligned project-local boundary-measure package.
-/
theorem projectLocalBoundaryMeasure_sourceProjectLocal_eq_setIntegral
    (A : BoundarySourceProjectLocalAlignment D P)
    (B : ProjectLocalBoundaryMeasureData (α := α) P μ)
    {x : M} (hx : x ∈ selectedPartition.active)
    {q : BoundaryPiece} (hq : q ∈ D.targetImages.boundaryPieces x) :
    projectLocalBoundaryIntegral I
        (D.targetImages.sourceChart x q)
        (D.targetImages.boundarySourceChart x q) omega
        (D.targetImages.sourceLowerCorner x q)
        (D.targetImages.sourceUpperCorner x q) =
      ∫ y in B.boundaryPieceSet x q,
        B.boundaryPieceIntegrand x q y ∂μ :=
  (A.toBoundarySourceSetIntegralInput B)
    |>.sourceProjectLocal_eq_setIntegral_expanded hx hq

/--
Use aligned project-local measure data to assemble the full target-COV boundary
measure input.  Compact-support and selected AE fields remain explicit because
they are stronger/differently indexed than `ProjectLocalBoundaryMeasureData`.
-/
def toBoundaryMeasureFromTargetCOVInput
    (A : BoundarySourceProjectLocalAlignment D P)
    (B : ProjectLocalBoundaryMeasureData (α := α) P μ)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (B.boundaryPieceIntegrand x q))
    (boundaryIntegrand_ae_eq_indicatorSum :
      B.boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.targetImages.boundaryPieces B.boundaryPieceSet
          B.boundaryPieceIntegrand) :
    BoundaryMeasureFromTargetCOVInput (α := α) D μ :=
  (A.toBoundarySourceSetIntegralInput B).toBoundaryMeasureFromTargetCOVInput
    B.boundaryIntegrand B.boundaryMeasureIntegral
    B.boundaryMeasureIntegral_eq_integral
    (fun x hx q hq =>
      B.boundaryPieceSet_measurable x (A.mem_active hx) q
        (A.mem_localPiece hq))
    boundaryPieceCompact boundaryIntegrand_ae_eq_indicatorSum
    P.globalBoundaryIntegral B.globalBoundaryIntegral_eq_boundaryMeasureIntegral

@[simp]
theorem toBoundaryMeasureFromTargetCOVInput_boundaryMeasureIntegral
    (A : BoundarySourceProjectLocalAlignment D P)
    (B : ProjectLocalBoundaryMeasureData (α := α) P μ)
    (boundaryPieceCompact :
      ∀ x, x ∈ selectedPartition.active →
        ∀ q, q ∈ D.targetImages.boundaryPieces x →
          CompactSupportIntegrabilityData (B.boundaryPieceIntegrand x q))
    (boundaryIntegrand_ae_eq_indicatorSum :
      B.boundaryIntegrand =ᵐ[μ]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.targetImages.boundaryPieces B.boundaryPieceSet
          B.boundaryPieceIntegrand) :
    (A.toBoundaryMeasureFromTargetCOVInput B boundaryPieceCompact
      boundaryIntegrand_ae_eq_indicatorSum).boundaryMeasureIntegral =
      B.boundaryMeasureIntegral := by
  rfl

end BoundarySourceProjectLocalAlignment

end BoundarySourceSetIntegral

end Stokes

end
