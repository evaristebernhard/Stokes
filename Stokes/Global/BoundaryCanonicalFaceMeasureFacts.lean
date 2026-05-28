import Stokes.Global.ProjectLocalBoundaryMeasureConstructor
import Stokes.Global.BoundaryIntegrabilityCompactSupport
import Stokes.Global.MeasureBoxAPI

/-!
# Canonical lower-face measure facts for project-local boundary pieces

This module isolates the local measure facts for the canonical source
lower-zero-face representative used by
`ProjectLocalBoundaryMeasureConstructorInput`.

The set measurability is automatic from the lower-zero-face box API.  The
integrability helpers keep the remaining analytic hypotheses explicit, with a
small continuity-data record for the common case where the ambient transition
pullback is continuous on each compact source box.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryCanonicalFaceMeasureFacts

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- Multiplying a real-valued function by a constant preserves set integrability. -/
theorem integrableOn_const_mul_real {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → Real}
    (hf : IntegrableOn f s μ) (c : Real) :
    IntegrableOn (fun x => c * f x) s μ := by
  rw [IntegrableOn] at hf ⊢
  exact hf.const_mul c

namespace ProjectLocalGlobalStokesData

variable (D : ProjectLocalGlobalStokesData I ω Chart Piece)

@[simp]
theorem projectLocalBoundaryPieceSet_eq_lowerZeroFaceDomain
    (x : Chart) (q : Piece) :
    D.projectLocalBoundaryPieceSet x q =
      lowerZeroFaceDomain (D.lowerCorner x q) (D.upperCorner x q) :=
  rfl

/-- The canonical project-local boundary piece set is always measurable. -/
theorem projectLocalBoundaryPieceSet_measurable
    (x : Chart) (q : Piece) :
    MeasurableSet (D.projectLocalBoundaryPieceSet x q) := by
  simpa [projectLocalBoundaryPieceSet] using
    measurableSet_lowerZeroFaceDomain (D.lowerCorner x q) (D.upperCorner x q)

/-- Constructor-field shape for active canonical boundary-piece measurability. -/
theorem boundaryPieceSet_measurable
    (x : Chart) (_hx : x ∈ D.activeCharts)
    (q : Piece) (_hq : q ∈ D.localPieces x) :
    MeasurableSet (D.projectLocalBoundaryPieceSet x q) :=
  D.projectLocalBoundaryPieceSet_measurable x q

/-- The canonical signed integrand is a constant multiple of the transition-pullback scalar. -/
theorem projectLocalBoundaryPieceIntegrand_eq_signed_transition
    (x : Chart) (q : Piece) :
    D.projectLocalBoundaryPieceIntegrand x q =
      fun y : Fin n → Real =>
        outwardFirstBoundaryOrientationSign n *
          boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
            (D.targetChart x q) ω y :=
  rfl

/-- Integrability of the unsigned transition-pullback scalar gives integrability of the
canonical signed boundary-piece integrand. -/
theorem projectLocalBoundaryPieceIntegrand_integrableOn_of_transition_integrableOn
    {x : Chart} {q : Piece}
    (h :
      IntegrableOn
        (boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
          (D.targetChart x q) ω)
        (D.projectLocalBoundaryPieceSet x q) volume) :
    IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
      (D.projectLocalBoundaryPieceSet x q) volume := by
  change
    IntegrableOn
      (fun y : Fin n → Real =>
        outwardFirstBoundaryOrientationSign n *
          boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
            (D.targetChart x q) ω y)
      (D.projectLocalBoundaryPieceSet x q) volume
  exact
    integrableOn_const_mul_real
      (μ := (volume : Measure (Fin n → Real)))
      (s := D.projectLocalBoundaryPieceSet x q)
      (f := boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
        (D.targetChart x q) ω)
      h (outwardFirstBoundaryOrientationSign n)

/-- Ambient-box continuity of the transition-pullback form gives continuity of the
canonical signed boundary-piece integrand on the lower-zero face. -/
theorem projectLocalBoundaryPieceIntegrand_continuousOn_of_transition_continuousOn
    {x : Chart} {q : Piece}
    (ha0 : D.lowerCorner x q (0 : Fin (n + 1)) = 0)
    (hle : D.lowerCorner x q ≤ D.upperCorner x q)
    (hω :
      ContinuousOn
        (ManifoldForm.transitionPullbackInChart I (D.sourceChart x q)
          (D.targetChart x q) ω)
        (Icc (D.lowerCorner x q) (D.upperCorner x q))) :
    ContinuousOn (D.projectLocalBoundaryPieceIntegrand x q)
      (D.projectLocalBoundaryPieceSet x q) := by
  have hunsigned :
      ContinuousOn
        (boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
          (D.targetChart x q) ω)
        (lowerZeroFaceDomain (D.lowerCorner x q) (D.upperCorner x q)) :=
    boundaryChartTransitionPullbackIntegrand_continuousOn_lowerZeroFaceDomain
      I (D.sourceChart x q) (D.targetChart x q) ω ha0 hle hω
  have hsigned :
      ContinuousOn
        (fun y : Fin n → Real =>
          outwardFirstBoundaryOrientationSign n *
            boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
              (D.targetChart x q) ω y)
        (lowerZeroFaceDomain (D.lowerCorner x q) (D.upperCorner x q)) :=
    hunsigned.const_mul (outwardFirstBoundaryOrientationSign n)
  change
    ContinuousOn
      (fun y : Fin n → Real =>
        outwardFirstBoundaryOrientationSign n *
          boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
            (D.targetChart x q) ω y)
      (lowerZeroFaceDomain (D.lowerCorner x q) (D.upperCorner x q))
  exact hsigned

/-- Continuity of the canonical signed integrand on its compact lower-zero face gives
`IntegrableOn`. -/
theorem projectLocalBoundaryPieceIntegrand_integrableOn_of_continuousOn
    {x : Chart} {q : Piece}
    (hf :
      ContinuousOn (D.projectLocalBoundaryPieceIntegrand x q)
        (D.projectLocalBoundaryPieceSet x q)) :
    IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
      (D.projectLocalBoundaryPieceSet x q) volume := by
  have hf' :
      ContinuousOn (D.projectLocalBoundaryPieceIntegrand x q)
        (lowerZeroFaceDomain (D.lowerCorner x q) (D.upperCorner x q)) := by
    simpa [projectLocalBoundaryPieceSet] using hf
  simpa [projectLocalBoundaryPieceSet] using
    (integrableOn_lowerZeroFaceDomain_of_continuousOn
      (a := D.lowerCorner x q) (b := D.upperCorner x q) hf')

/-- Ambient-box continuity of the transition-pullback form gives `IntegrableOn` for the
canonical signed boundary-piece integrand. -/
theorem projectLocalBoundaryPieceIntegrand_integrableOn_of_transition_continuousOn
    {x : Chart} {q : Piece}
    (ha0 : D.lowerCorner x q (0 : Fin (n + 1)) = 0)
    (hle : D.lowerCorner x q ≤ D.upperCorner x q)
    (hω :
      ContinuousOn
        (ManifoldForm.transitionPullbackInChart I (D.sourceChart x q)
          (D.targetChart x q) ω)
        (Icc (D.lowerCorner x q) (D.upperCorner x q))) :
    IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
      (D.projectLocalBoundaryPieceSet x q) volume := by
  exact D.projectLocalBoundaryPieceIntegrand_integrableOn_of_continuousOn
    (D.projectLocalBoundaryPieceIntegrand_continuousOn_of_transition_continuousOn
      ha0 hle hω)

/-- A continuous compactly supported canonical signed integrand is integrable on its
canonical face. -/
theorem projectLocalBoundaryPieceIntegrand_integrableOn_of_continuous_hasCompactSupport
    {x : Chart} {q : Piece}
    (hf : Continuous (D.projectLocalBoundaryPieceIntegrand x q))
    (hcf : HasCompactSupport (D.projectLocalBoundaryPieceIntegrand x q)) :
    IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
      (D.projectLocalBoundaryPieceSet x q) volume := by
  simpa [projectLocalBoundaryPieceSet] using
    (integrableOn_lowerZeroFaceDomain_of_continuous_hasCompactSupport
      (a := D.lowerCorner x q) (b := D.upperCorner x q)
      (hf := hf) (hcf := hcf))

/-- Compact support for the unsigned transition-pullback scalar gives integrability of the
canonical signed boundary-piece integrand. -/
theorem projectLocalBoundaryPieceIntegrand_integrableOn_of_transition_compactSupport
    {x : Chart} {q : Piece}
    (hf :
      Continuous
        (boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
          (D.targetChart x q) ω))
    (hcf :
      HasCompactSupport
        (boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
          (D.targetChart x q) ω)) :
    IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
      (D.projectLocalBoundaryPieceSet x q) volume := by
  have hunsigned :
      IntegrableOn
        (boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
          (D.targetChart x q) ω)
        (D.projectLocalBoundaryPieceSet x q) volume := by
    simpa [projectLocalBoundaryPieceSet] using
      (boundaryChartTransitionPullbackIntegrand_integrableOn_of_compactSupport
        I (D.sourceChart x q) (D.targetChart x q) ω
        (a := D.lowerCorner x q) (b := D.upperCorner x q) hf hcf)
  exact
    D.projectLocalBoundaryPieceIntegrand_integrableOn_of_transition_integrableOn
      hunsigned

/-- An extended boundary source box supplies the canonical signed boundary-piece
integrability field. -/
theorem projectLocalBoundaryPieceIntegrand_integrableOn_of_extendedBox
    {x : Chart} {q : Piece}
    (hbox :
      boundaryChartExtendedBox I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q)) :
    IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
      (D.projectLocalBoundaryPieceSet x q) volume := by
  have hunsigned :
      IntegrableOn
        (boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
          (D.targetChart x q) ω)
        (D.projectLocalBoundaryPieceSet x q) volume := by
    simpa [projectLocalBoundaryPieceSet] using
      (boundaryChartTransitionPullbackIntegrand_integrableOn_of_extendedBox
        (I := I) (x0 := D.sourceChart x q) (x1 := D.targetChart x q)
        (ω := ω) (a := D.lowerCorner x q) (b := D.upperCorner x q) hbox)
  exact
    D.projectLocalBoundaryPieceIntegrand_integrableOn_of_transition_integrableOn
      hunsigned

/-- Constructor-field shape: active canonical integrability from active ambient-box
continuity hypotheses. -/
theorem boundaryPieceIntegrableOn_of_transition_continuousOn
    (ha0 :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          D.lowerCorner x q (0 : Fin (n + 1)) = 0)
    (hle :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          D.lowerCorner x q ≤ D.upperCorner x q)
    (hω :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          ContinuousOn
            (ManifoldForm.transitionPullbackInChart I (D.sourceChart x q)
              (D.targetChart x q) ω)
            (Icc (D.lowerCorner x q) (D.upperCorner x q))) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
          (D.projectLocalBoundaryPieceSet x q) volume := by
  intro x hx q hq
  exact
    D.projectLocalBoundaryPieceIntegrand_integrableOn_of_transition_continuousOn
      (ha0 x hx q hq) (hle x hx q hq) (hω x hx q hq)

/-- Constructor-field shape: active canonical integrability from active extended source boxes. -/
theorem boundaryPieceIntegrableOn_of_extendedBox
    (hbox :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          boundaryChartExtendedBox I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q)) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
          (D.projectLocalBoundaryPieceSet x q) volume := by
  intro x hx q hq
  exact D.projectLocalBoundaryPieceIntegrand_integrableOn_of_extendedBox
    (hbox x hx q hq)

end ProjectLocalGlobalStokesData

/--
Local continuity facts that discharge the canonical boundary-piece
measurability and integrability fields for active project-local pieces.

The remaining global measure identity, set-integral reconstruction, and
boundary partition alignment are intentionally left outside this record.
-/
structure ProjectLocalBoundaryCanonicalFaceContinuityData
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) where
  /-- Each active source box has its lower `0` coordinate on the half-space boundary. -/
  lowerCorner_zero :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        D.lowerCorner x q (0 : Fin (n + 1)) = 0
  /-- Each active source corner pair is ordered. -/
  lowerCorner_le_upper :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        D.lowerCorner x q ≤ D.upperCorner x q
  /-- The ambient transition-pullback representative is continuous on each active source box. -/
  transitionPullback_continuousOn :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        ContinuousOn
          (ManifoldForm.transitionPullbackInChart I (D.sourceChart x q)
            (D.targetChart x q) ω)
          (Icc (D.lowerCorner x q) (D.upperCorner x q))

namespace ProjectLocalBoundaryCanonicalFaceContinuityData

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}

/-- Build canonical face continuity data from active extended source boxes. -/
def ofExtendedBox
    (hbox :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          boundaryChartExtendedBox I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q)) :
    ProjectLocalBoundaryCanonicalFaceContinuityData D where
  lowerCorner_zero := by
    intro x hx q hq
    exact (hbox x hx q hq).selectedBox.ha0
  lowerCorner_le_upper := by
    intro x hx q hq
    exact (hbox x hx q hq).selectedBox.le
  transitionPullback_continuousOn := by
    intro x hx q hq
    rcases (hbox x hx q hq).exists_smooth_nhds with
      ⟨U, _hU, hUbox, hωU⟩
    exact hωU.continuousOn.mono hUbox

/-- Active canonical boundary-piece set measurability supplied by the face API. -/
theorem boundaryPieceSet_measurable
    (_F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (x : Chart) (hx : x ∈ D.activeCharts)
    (q : Piece) (hq : q ∈ D.localPieces x) :
    MeasurableSet (D.projectLocalBoundaryPieceSet x q) :=
  D.boundaryPieceSet_measurable x hx q hq

/-- Active canonical boundary-piece integrability supplied by the recorded continuity facts. -/
theorem boundaryPieceIntegrableOn
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (x : Chart) (hx : x ∈ D.activeCharts)
    (q : Piece) (hq : q ∈ D.localPieces x) :
    IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
      (D.projectLocalBoundaryPieceSet x q) volume :=
  D.projectLocalBoundaryPieceIntegrand_integrableOn_of_transition_continuousOn
    (F.lowerCorner_zero x hx q hq)
    (F.lowerCorner_le_upper x hx q hq)
    (F.transitionPullback_continuousOn x hx q hq)

/--
Construct the project-local boundary measure constructor input using canonical
face local facts.  This fills the two local fields
`boundaryPieceSet_measurable` and `boundaryPieceIntegrableOn`.
-/
def toProjectLocalBoundaryMeasureConstructorInput
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hglobal : D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          D.boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
              (D.lowerCorner x q) (D.upperCorner x q))
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.localPieces
          D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand) :
    ProjectLocalBoundaryMeasureConstructorInput D where
  boundaryIntegrand := boundaryIntegrand
  boundaryMeasureIntegral := boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hglobal
  boundaryMeasureIntegral_eq_integral := hmeasure
  boundaryPieceSet_measurable := F.boundaryPieceSet_measurable
  boundaryPieceIntegrableOn := F.boundaryPieceIntegrableOn
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral := hterm
  boundaryIntegrand_ae_eq_indicatorSum := hboundary

end ProjectLocalBoundaryCanonicalFaceContinuityData

namespace ProjectLocalBoundaryMeasureConstructorInput

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}

/--
Selected-target chart-change data plus canonical face continuity facts build
the project-local boundary constructor input without separate measurability or
integrability arguments.
-/
def ofSelectedBoundaryChartChangeFamilyCanonicalFace
    [IsManifold I 1 M]
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hglobal : D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.localPieces
          D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand)
    (S : BoundaryChartChangeSelectedFamilyData D) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  ofSelectedBoundaryChartChangeFamily boundaryIntegrand boundaryMeasureIntegral
    hmeasure hglobal F.boundaryPieceSet_measurable F.boundaryPieceIntegrableOn
    hboundary S

/--
Extended-target chart-change data plus canonical face continuity facts build
the project-local boundary constructor input without separate measurability or
integrability arguments.
-/
def ofExtendedBoundaryChartChangeFamilyCanonicalFace
    [IsManifold I 1 M]
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hglobal : D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.localPieces
          D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand)
    (S : BoundaryChartChangeExtendedFamilyData D) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  ofExtendedBoundaryChartChangeFamily boundaryIntegrand boundaryMeasureIntegral
    hmeasure hglobal F.boundaryPieceSet_measurable F.boundaryPieceIntegrableOn
    hboundary S

/--
Pure COV family compatibility plus canonical face continuity facts build the
project-local boundary constructor input without separate measurability or
integrability arguments.
-/
def ofCOVFamilyCompatibilityCanonicalFace
    [IsManifold I 1 M]
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hglobal : D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.localPieces
          D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand)
    (S : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (A : BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility S D) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  ofCOVFamilyCompatibility boundaryIntegrand boundaryMeasureIntegral
    hmeasure hglobal F.boundaryPieceSet_measurable F.boundaryPieceIntegrableOn
    hboundary S A

end ProjectLocalBoundaryMeasureConstructorInput

end BoundaryCanonicalFaceMeasureFacts

end Stokes

end
