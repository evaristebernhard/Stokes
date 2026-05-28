import Stokes.Global.BoundarySourceSetIntegral
import Stokes.Global.BoundaryCOVMeasureConstructor

/-!
# Constructors for project-local boundary measure data

This file isolates the source-side project-local boundary set-integral
constructor.  The key point is that the source project-local boundary integral
has a canonical lower-zero-face measure representative by definition.  The
remaining global boundary-measure facts, such as finite partition
reconstruction and a.e. reconstruction, stay explicit.
-/

noncomputable section

set_option linter.style.longLine false

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section ProjectLocalBoundaryMeasureConstructor

universe u w c p a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {α : Type a} [MeasurableSpace α]
variable {μ : Measure α}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

namespace ProjectLocalGlobalStokesData

variable (D : ProjectLocalGlobalStokesData I ω Chart Piece)

/-- The canonical lower-zero-face set for one project-local boundary piece. -/
def projectLocalBoundaryPieceSet (x : Chart) (q : Piece) :
    Set (Fin n → Real) :=
  lowerZeroFaceDomain (D.lowerCorner x q) (D.upperCorner x q)

/--
The canonical scalar integrand whose set integral is the project-local
outward-first boundary integral.
-/
def projectLocalBoundaryPieceIntegrand (x : Chart) (q : Piece)
    (y : Fin n → Real) : Real :=
  outwardFirstBoundaryOrientationSign n *
    ManifoldForm.transitionPullbackInChart I (D.sourceChart x q)
      (D.targetChart x q) ω (boundaryInclusion n y) (boundaryTangent n)

/--
The project-local boundary integral is definitionally the set integral of the
canonical lower-zero-face scalar representative.
-/
theorem projectLocalBoundaryIntegral_eq_projectLocalBoundarySetIntegral
    (x : Chart) (q : Piece) :
    projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q) =
      ∫ y in D.projectLocalBoundaryPieceSet x q,
        D.projectLocalBoundaryPieceIntegrand x q y ∂volume := by
  simp [projectLocalBoundaryPieceSet, projectLocalBoundaryPieceIntegrand,
    projectLocalBoundaryIntegral, outwardFirstBoundaryChartIntegral,
    halfSpaceBoundaryTransitionFormIntegral, halfSpaceBoundaryFormIntegral,
    ← integral_neg]

end ProjectLocalGlobalStokesData

/--
Minimal constructor input for project-local boundary measure data using the
canonical lower-zero-face representative of each project-local boundary
integral.

This record no longer asks for the source set-integral equality as a field:
that equality is supplied by
`ProjectLocalGlobalStokesData.projectLocalBoundaryIntegral_eq_projectLocalBoundarySetIntegral`.
The remaining assumptions are the genuine global measure and localization
facts that cannot be inferred from the definition of the local integral alone.
-/
structure ProjectLocalBoundaryMeasureConstructorInput
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) where
  /-- Boundary-side integrand represented by the global boundary measure. -/
  boundaryIntegrand : (Fin n → Real) → Real
  /-- The genuine boundary measure integral. -/
  boundaryMeasureIntegral : Real
  /-- The represented project-local global boundary integral is this measure integral. -/
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    D.globalBoundaryIntegral = boundaryMeasureIntegral
  /-- The boundary measure integral is the integral of the global boundary integrand. -/
  boundaryMeasureIntegral_eq_integral :
    boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume
  /-- Active canonical lower-zero-face sets are measurable. -/
  boundaryPieceSet_measurable :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        MeasurableSet (D.projectLocalBoundaryPieceSet x q)
  /-- Active canonical scalar representatives are integrable on their face domains. -/
  boundaryPieceIntegrableOn :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
          (D.projectLocalBoundaryPieceSet x q) volume
  /-- The selected boundary partition term is the project-local boundary integral. -/
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        D.boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q)
  /-- A.e. reconstruction by the canonical lower-zero-face indicator pieces. -/
  boundaryIntegrand_ae_eq_indicatorSum :
    boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
      boundaryMeasureIndicatorSum D.activeCharts D.localPieces
        D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand

namespace ProjectLocalBoundaryMeasureConstructorInput

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}
variable (C : ProjectLocalBoundaryMeasureConstructorInput D)

/-- The canonical project-local set-integral equality exposed by the constructor. -/
theorem projectLocalBoundaryIntegral_eq_setIntegral
    (_C : ProjectLocalBoundaryMeasureConstructorInput D)
    {x : Chart} (_hx : x ∈ D.activeCharts)
    {q : Piece} (_hq : q ∈ D.localPieces x) :
    projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q) =
      ∫ y in D.projectLocalBoundaryPieceSet x q,
        D.projectLocalBoundaryPieceIntegrand x q y ∂volume :=
  D.projectLocalBoundaryIntegral_eq_projectLocalBoundarySetIntegral x q

/-- The selected boundary partition term is the canonical set integral. -/
theorem boundaryPartitionTerm_eq_setIntegral
    (C : ProjectLocalBoundaryMeasureConstructorInput D)
    {x : Chart} (hx : x ∈ D.activeCharts)
    {q : Piece} (hq : q ∈ D.localPieces x) :
    D.boundaryPartitionTerm x q =
      ∫ y in D.projectLocalBoundaryPieceSet x q,
        D.projectLocalBoundaryPieceIntegrand x q y ∂volume :=
  (ProjectLocalBoundaryMeasureConstructorInput.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral
      C x hx q hq).trans
    (ProjectLocalBoundaryMeasureConstructorInput.projectLocalBoundaryIntegral_eq_setIntegral
      C hx hq)

/-- Build `ProjectLocalBoundaryMeasureData` from the canonical local pieces. -/
def toProjectLocalBoundaryMeasureData
    (C : ProjectLocalBoundaryMeasureConstructorInput D) :
    ProjectLocalBoundaryMeasureData
      (α := Fin n → Real) D (volume : Measure (Fin n → Real)) where
  boundaryIntegrand := C.boundaryIntegrand
  boundaryPieceSet := D.projectLocalBoundaryPieceSet
  boundaryPieceIntegrand := D.projectLocalBoundaryPieceIntegrand
  boundaryMeasureIntegral := C.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    C.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral :=
    C.boundaryMeasureIntegral_eq_integral
  boundaryPieceSet_measurable := C.boundaryPieceSet_measurable
  boundaryPieceIntegrableOn := C.boundaryPieceIntegrableOn
  projectLocalBoundaryIntegral_eq_setIntegral := by
    intro x hx q hq
    exact ProjectLocalBoundaryMeasureConstructorInput.projectLocalBoundaryIntegral_eq_setIntegral
      C hx hq
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral :=
    ProjectLocalBoundaryMeasureConstructorInput.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral C
  boundaryIntegrand_ae_eq_indicatorSum :=
    C.boundaryIntegrand_ae_eq_indicatorSum

@[simp]
theorem toProjectLocalBoundaryMeasureData_boundaryPieceSet :
    C.toProjectLocalBoundaryMeasureData.boundaryPieceSet =
      D.projectLocalBoundaryPieceSet :=
  rfl

@[simp]
theorem toProjectLocalBoundaryMeasureData_boundaryPieceIntegrand :
    C.toProjectLocalBoundaryMeasureData.boundaryPieceIntegrand =
      D.projectLocalBoundaryPieceIntegrand :=
  rfl

@[simp]
theorem toProjectLocalBoundaryMeasureData_boundaryMeasureIntegral :
    C.toProjectLocalBoundaryMeasureData.boundaryMeasureIntegral =
      C.boundaryMeasureIntegral :=
  rfl

/--
Selected-target boundary chart-change data supplies the pointwise
partition-term/project-local-integral alignment needed by the constructor.
-/
def ofSelectedBoundaryChartChangeFamily [IsManifold I 1 M]
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hglobal : D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hset :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          MeasurableSet (D.projectLocalBoundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
            (D.projectLocalBoundaryPieceSet x q) volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.localPieces
          D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand)
    (F : BoundaryChartChangeSelectedFamilyData D) :
    ProjectLocalBoundaryMeasureConstructorInput D where
  boundaryIntegrand := boundaryIntegrand
  boundaryMeasureIntegral := boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hglobal
  boundaryMeasureIntegral_eq_integral := hmeasure
  boundaryPieceSet_measurable := hset
  boundaryPieceIntegrableOn := hintegrable
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral := by
    intro x hx q hq
    exact (F.pointwise_eq_boundaryPartition_selected x hx q hq).symm
  boundaryIntegrand_ae_eq_indicatorSum := hboundary

/--
Extended-target boundary chart-change data supplies the same pointwise
alignment after forgetting the extra target-box strength.
-/
def ofExtendedBoundaryChartChangeFamily [IsManifold I 1 M]
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hglobal : D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hset :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          MeasurableSet (D.projectLocalBoundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
            (D.projectLocalBoundaryPieceSet x q) volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.localPieces
          D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand)
    (F : BoundaryChartChangeExtendedFamilyData D) :
    ProjectLocalBoundaryMeasureConstructorInput D where
  boundaryIntegrand := boundaryIntegrand
  boundaryMeasureIntegral := boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hglobal
  boundaryMeasureIntegral_eq_integral := hmeasure
  boundaryPieceSet_measurable := hset
  boundaryPieceIntegrableOn := hintegrable
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral := by
    intro x hx q hq
    exact (F.pointwise_eq_boundaryPartition_extended x hx q hq).symm
  boundaryIntegrand_ae_eq_indicatorSum := hboundary

/--
Pure boundary COV family compatibility also supplies the pointwise alignment,
through the selected-target chart-change adapter.
-/
def ofCOVFamilyCompatibility [IsManifold I 1 M]
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hglobal : D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hset :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          MeasurableSet (D.projectLocalBoundaryPieceSet x q))
    (hintegrable :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          IntegrableOn (D.projectLocalBoundaryPieceIntegrand x q)
            (D.projectLocalBoundaryPieceSet x q) volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.localPieces
          D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand)
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (A : BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility F D) :
    ProjectLocalBoundaryMeasureConstructorInput D :=
  ofSelectedBoundaryChartChangeFamily boundaryIntegrand boundaryMeasureIntegral
    hmeasure hglobal hset hintegrable hboundary
    (F.toBoundaryChartChangeSelectedFamilyData A)

end ProjectLocalBoundaryMeasureConstructorInput

/--
General compact-field constructor.  This is useful when another measure space
has already supplied compact/set-integral boundary fields for the chosen
partition term.  The only extra local fact required is the existing
chart-change equality between the partition term and project-local boundary
integral.
-/
structure ProjectLocalBoundaryMeasureCompactConstructorInput
    (D : ProjectLocalGlobalStokesData I ω Chart Piece)
    (μ : Measure α) where
  compactFields :
    BoundaryCompactMeasureFields μ D.activeCharts D.localPieces
      D.boundaryPartitionTerm
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :
    D.globalBoundaryIntegral = compactFields.boundaryMeasureIntegral
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        D.boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q)

namespace ProjectLocalBoundaryMeasureCompactConstructorInput

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}
variable (C : ProjectLocalBoundaryMeasureCompactConstructorInput D μ)

/-- Compact fields plus chart-change alignment give the project-local set-integral equality. -/
theorem projectLocalBoundaryIntegral_eq_setIntegral
    {x : Chart} (hx : x ∈ D.activeCharts)
    {q : Piece} (hq : q ∈ D.localPieces x) :
    projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q) =
      ∫ y in C.compactFields.boundaryPieceSet x q,
        C.compactFields.boundaryPieceIntegrand x q y ∂μ :=
  (C.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral x hx q hq).symm.trans
    (C.compactFields.boundaryPartitionTerm_eq_setIntegral x hx q hq)

/-- Build project-local boundary measure data from compact/set-integral fields. -/
def toProjectLocalBoundaryMeasureData :
    ProjectLocalBoundaryMeasureData (α := α) D μ where
  boundaryIntegrand := C.compactFields.boundaryIntegrand
  boundaryPieceSet := C.compactFields.boundaryPieceSet
  boundaryPieceIntegrand := C.compactFields.boundaryPieceIntegrand
  boundaryMeasureIntegral := C.compactFields.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    C.globalBoundaryIntegral_eq_boundaryMeasureIntegral
  boundaryMeasureIntegral_eq_integral :=
    C.compactFields.boundaryMeasureIntegral_eq_integral
  boundaryPieceSet_measurable := C.compactFields.boundaryPieceSet_measurable
  boundaryPieceIntegrableOn := C.compactFields.boundaryPieceIntegrableOn
  projectLocalBoundaryIntegral_eq_setIntegral := by
    intro x hx q hq
    exact C.projectLocalBoundaryIntegral_eq_setIntegral hx hq
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral :=
    C.boundaryPartitionTerm_eq_projectLocalBoundaryIntegral
  boundaryIntegrand_ae_eq_indicatorSum :=
    C.compactFields.boundaryIntegrand_ae_eq_indicatorSum

@[simp]
theorem toProjectLocalBoundaryMeasureData_boundaryMeasureIntegral :
    C.toProjectLocalBoundaryMeasureData.boundaryMeasureIntegral =
      C.compactFields.boundaryMeasureIntegral :=
  rfl

/-- Constructor from selected-target boundary chart-change data. -/
def ofSelectedBoundaryChartChangeFamily [IsManifold I 1 M]
    (compactFields :
      BoundaryCompactMeasureFields μ D.activeCharts D.localPieces
        D.boundaryPartitionTerm)
    (hglobal :
      D.globalBoundaryIntegral = compactFields.boundaryMeasureIntegral)
    (F : BoundaryChartChangeSelectedFamilyData D) :
    ProjectLocalBoundaryMeasureCompactConstructorInput D μ where
  compactFields := compactFields
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hglobal
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral := by
    intro x hx q hq
    exact (F.pointwise_eq_boundaryPartition_selected x hx q hq).symm

/-- Constructor from extended-target boundary chart-change data. -/
def ofExtendedBoundaryChartChangeFamily [IsManifold I 1 M]
    (compactFields :
      BoundaryCompactMeasureFields μ D.activeCharts D.localPieces
        D.boundaryPartitionTerm)
    (hglobal :
      D.globalBoundaryIntegral = compactFields.boundaryMeasureIntegral)
    (F : BoundaryChartChangeExtendedFamilyData D) :
    ProjectLocalBoundaryMeasureCompactConstructorInput D μ where
  compactFields := compactFields
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hglobal
  boundaryPartitionTerm_eq_projectLocalBoundaryIntegral := by
    intro x hx q hq
    exact (F.pointwise_eq_boundaryPartition_extended x hx q hq).symm

/-- Constructor from pure boundary COV family compatibility. -/
def ofCOVFamilyCompatibility [IsManifold I 1 M]
    (compactFields :
      BoundaryCompactMeasureFields μ D.activeCharts D.localPieces
        D.boundaryPartitionTerm)
    (hglobal :
      D.globalBoundaryIntegral = compactFields.boundaryMeasureIntegral)
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (A : BoundaryChartChangeOfVariablesFamily.ProjectLocalChartChangeCompatibility F D) :
    ProjectLocalBoundaryMeasureCompactConstructorInput D μ :=
  ofSelectedBoundaryChartChangeFamily compactFields hglobal
    (F.toBoundaryChartChangeSelectedFamilyData A)

end ProjectLocalBoundaryMeasureCompactConstructorInput

section M8SourceInput

variable {BoundaryPiece : Type p}
variable {selectedPartition : SelectedBoxPartitionOfUnity I ω}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace M8TargetImageInput

variable
    (D :
      M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas
        BoundaryPiece)

/-- The canonical source lower-zero-face set for one selected target-image piece. -/
def sourceProjectLocalBoundaryPieceSet (x : M) (q : BoundaryPiece) :
    Set (Fin n → Real) :=
  lowerZeroFaceDomain (D.targetImages.sourceLowerCorner x q)
    (D.targetImages.sourceUpperCorner x q)

/-- The canonical source scalar representative for one selected target-image piece. -/
def sourceProjectLocalBoundaryPieceIntegrand (x : M) (q : BoundaryPiece)
    (y : Fin n → Real) : Real :=
  outwardFirstBoundaryOrientationSign n *
    ManifoldForm.transitionPullbackInChart I (D.targetImages.sourceChart x q)
      (D.targetImages.boundarySourceChart x q) ω
      (boundaryInclusion n y) (boundaryTangent n)

/-- Source target-image project-local boundary integrals are canonical set integrals. -/
theorem sourceProjectLocalBoundaryIntegral_eq_sourceSetIntegral
    (x : M) (q : BoundaryPiece) :
    D.sourceProjectLocalBoundaryIntegral x q =
      ∫ y in D.sourceProjectLocalBoundaryPieceSet x q,
        D.sourceProjectLocalBoundaryPieceIntegrand x q y ∂volume := by
  simp [M8TargetImageInput.sourceProjectLocalBoundaryIntegral,
    sourceProjectLocalBoundaryPieceSet, sourceProjectLocalBoundaryPieceIntegrand,
    projectLocalBoundaryIntegral, outwardFirstBoundaryChartIntegral,
    halfSpaceBoundaryTransitionFormIntegral, halfSpaceBoundaryFormIntegral,
    ← integral_neg]

/--
The source-side input consumed by target COV, using the canonical source
lower-zero-face representative.
-/
def canonicalBoundarySourceSetIntegralInput :
    BoundarySourceSetIntegralInput
      (α := Fin n → Real) D (volume : Measure (Fin n → Real)) where
  boundaryPieceSet := D.sourceProjectLocalBoundaryPieceSet
  boundaryPieceIntegrand := D.sourceProjectLocalBoundaryPieceIntegrand
  sourceProjectLocal_eq_setIntegral := by
    intro x _hx q _hq
    exact D.sourceProjectLocalBoundaryIntegral_eq_sourceSetIntegral x q

@[simp]
theorem canonicalBoundarySourceSetIntegralInput_boundaryPieceSet :
    D.canonicalBoundarySourceSetIntegralInput.boundaryPieceSet =
      D.sourceProjectLocalBoundaryPieceSet :=
  rfl

@[simp]
theorem canonicalBoundarySourceSetIntegralInput_boundaryPieceIntegrand :
    D.canonicalBoundarySourceSetIntegralInput.boundaryPieceIntegrand =
      D.sourceProjectLocalBoundaryPieceIntegrand :=
  rfl

end M8TargetImageInput

namespace ProjectLocalBoundaryMeasureConstructorInput

variable {T :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas BoundaryPiece}
variable {P : ProjectLocalGlobalStokesData I ω M BoundaryPiece}

/--
Aligned project-local constructor data supplies the source set-integral input
needed by the target-COV boundary route.
-/
def toBoundarySourceSetIntegralInput
    (C : ProjectLocalBoundaryMeasureConstructorInput P)
    (A : BoundarySourceProjectLocalAlignment T P) :
    BoundarySourceSetIntegralInput
      (α := Fin n → Real) T (volume : Measure (Fin n → Real)) :=
  A.toBoundarySourceSetIntegralInput C.toProjectLocalBoundaryMeasureData

end ProjectLocalBoundaryMeasureConstructorInput

namespace ProjectLocalBoundaryMeasureCompactConstructorInput

variable {T :
    M8TargetImageInput I ω selectedPartition orientedBoundaryAtlas BoundaryPiece}
variable {P : ProjectLocalGlobalStokesData I ω M BoundaryPiece}
variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
variable [IsFiniteMeasureOnCompacts μ]

/--
Aligned compact-field project-local constructor data supplies the source
set-integral input needed by the target-COV boundary route.
-/
def toBoundarySourceSetIntegralInput
    (C : ProjectLocalBoundaryMeasureCompactConstructorInput (α := α) P μ)
    (A : BoundarySourceProjectLocalAlignment T P) :
    BoundarySourceSetIntegralInput (α := α) T μ :=
  A.toBoundarySourceSetIntegralInput C.toProjectLocalBoundaryMeasureData

end ProjectLocalBoundaryMeasureCompactConstructorInput

end M8SourceInput

end ProjectLocalBoundaryMeasureConstructor

end Stokes

end
