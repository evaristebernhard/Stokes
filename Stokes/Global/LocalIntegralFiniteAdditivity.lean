import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Stokes.Global.LocalIntegral
import Stokes.Global.Assembly
import Stokes.Global.IntegralReconstruction

/-!
# Finite additivity bookkeeping for local integral sums

The project-local integral names in `Stokes.Global.LocalIntegral` are wrappers
around the boundary-chart half-space API, not a finished manifold measure
integral.  This module therefore proves the finite-sum algebra that is already
available and packages the genuinely analytic finite-additivity statements as
explicit fields.

The main use is to feed bulk and boundary reconstruction fields without
committing to a final implementation of manifold integration.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section ChartPieceSums

universe c p r

variable {Chart : Type c} {Piece : Type p} {R : Type r}

/-- The flattened finite index set of chart-labelled local pieces. -/
def chartPieceIndexSet
    (activeCharts : Finset Chart) (pieces : Chart → Finset Piece) :
    Finset (Σ _ : Chart, Piece) :=
  activeCharts.sigma pieces

@[simp]
theorem mem_chartPieceIndexSet
    {activeCharts : Finset Chart} {pieces : Chart → Finset Piece}
    {qp : Σ _ : Chart, Piece} :
    qp ∈ chartPieceIndexSet activeCharts pieces ↔
      qp.1 ∈ activeCharts ∧ qp.2 ∈ pieces qp.1 := by
  simp [chartPieceIndexSet]

/-- Nested chart/piece finite sum. -/
def chartPieceSum [AddCommMonoid R]
    (activeCharts : Finset Chart) (pieces : Chart → Finset Piece)
    (term : Chart → Piece → R) : R :=
  Finset.sum activeCharts fun x =>
    Finset.sum (pieces x) fun q => term x q

@[simp]
theorem chartPieceSum_empty [AddCommMonoid R]
    (pieces : Chart → Finset Piece) (term : Chart → Piece → R) :
    chartPieceSum (∅ : Finset Chart) pieces term = 0 := by
  simp [chartPieceSum]

@[simp]
theorem chartPieceSum_empty_pieces [AddCommMonoid R]
    (activeCharts : Finset Chart) (term : Chart → Piece → R) :
    chartPieceSum activeCharts (fun _ => (∅ : Finset Piece)) term = 0 := by
  simp [chartPieceSum]

/-- Unfold a chart/piece sum to its nested `Finset.sum` form. -/
theorem chartPieceSum_eq_nested [AddCommMonoid R]
    (activeCharts : Finset Chart) (pieces : Chart → Finset Piece)
    (term : Chart → Piece → R) :
    chartPieceSum activeCharts pieces term =
      Finset.sum activeCharts fun x =>
        Finset.sum (pieces x) fun q => term x q :=
  rfl

/-- Rewrite a nested chart/piece sum as a sum over the flattened sigma index. -/
theorem chartPieceSum_eq_indexSet_sum [AddCommMonoid R]
    (activeCharts : Finset Chart) (pieces : Chart → Finset Piece)
    (term : Chart → Piece → R) :
    chartPieceSum activeCharts pieces term =
      Finset.sum (chartPieceIndexSet activeCharts pieces) fun qp =>
        term qp.1 qp.2 := by
  simpa [chartPieceSum, chartPieceIndexSet] using
    (Finset.sum_sigma' activeCharts pieces fun x q => term x q)

/-- Pointwise equality on active pieces transports a chart/piece finite sum. -/
theorem chartPieceSum_congr [AddCommMonoid R]
    (activeCharts : Finset Chart) (pieces : Chart → Finset Piece)
    (oldTerm newTerm : Chart → Piece → R)
    (hterm :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ pieces x →
          oldTerm x q = newTerm x q) :
    chartPieceSum activeCharts pieces oldTerm =
      chartPieceSum activeCharts pieces newTerm := by
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro q hq
  exact hterm x hx q hq

/-- Alias for `chartPieceSum_congr`, named for chart-change transport uses. -/
theorem chartPieceSum_transport [AddCommMonoid R]
    (activeCharts : Finset Chart) (pieces : Chart → Finset Piece)
    (sourceTerm targetTerm : Chart → Piece → R)
    (htransport :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ pieces x →
          sourceTerm x q = targetTerm x q) :
    chartPieceSum activeCharts pieces sourceTerm =
      chartPieceSum activeCharts pieces targetTerm :=
  chartPieceSum_congr activeCharts pieces sourceTerm targetTerm htransport

/-- If all active local terms vanish, then the whole chart/piece sum vanishes. -/
theorem chartPieceSum_eq_zero_of_forall_eq_zero [AddCommMonoid R]
    (activeCharts : Finset Chart) (pieces : Chart → Finset Piece)
    (term : Chart → Piece → R)
    (hzero :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ pieces x →
          term x q = 0) :
    chartPieceSum activeCharts pieces term = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro q hq
  exact hzero x hx q hq

/-- A chart/piece sum distributes over pointwise addition of local terms. -/
theorem chartPieceSum_add [AddCommMonoid R]
    (activeCharts : Finset Chart) (pieces : Chart → Finset Piece)
    (f g : Chart → Piece → R) :
    chartPieceSum activeCharts pieces (fun x q => f x q + g x q) =
      chartPieceSum activeCharts pieces f +
        chartPieceSum activeCharts pieces g := by
  simp [chartPieceSum, Finset.sum_add_distrib]

/-- A chart/piece sum commutes with pointwise negation. -/
theorem chartPieceSum_neg [AddCommGroup R]
    (activeCharts : Finset Chart) (pieces : Chart → Finset Piece)
    (f : Chart → Piece → R) :
    chartPieceSum activeCharts pieces (fun x q => - f x q) =
      - chartPieceSum activeCharts pieces f := by
  simp [chartPieceSum]

/-- A chart/piece sum distributes over pointwise subtraction of local terms. -/
theorem chartPieceSum_sub [AddCommGroup R]
    (activeCharts : Finset Chart) (pieces : Chart → Finset Piece)
    (f g : Chart → Piece → R) :
    chartPieceSum activeCharts pieces (fun x q => f x q - g x q) =
      chartPieceSum activeCharts pieces f -
        chartPieceSum activeCharts pieces g := by
  simp [sub_eq_add_neg, chartPieceSum_add, chartPieceSum_neg]

end ChartPieceSums

section BulkBoundarySums

universe c i b

variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/-- Total local bulk sum split into interior and boundary-chart local pieces. -/
def bulkBoundaryLocalSum
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (boundaryPieces : Chart → Finset BoundaryPiece)
    (interiorBulkTerm : Chart → InteriorPiece → Real)
    (boundaryBulkTerm : Chart → BoundaryPiece → Real) : Real :=
  chartPieceSum activeCharts interiorPieces interiorBulkTerm +
    chartPieceSum activeCharts boundaryPieces boundaryBulkTerm

/-- Boundary partition sum for selected boundary pieces. -/
def boundaryPartitionLocalSum
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset BoundaryPiece)
    (boundaryPartitionTerm : Chart → BoundaryPiece → Real) : Real :=
  chartPieceSum activeCharts boundaryPieces boundaryPartitionTerm

theorem bulkBoundaryLocalSum_eq_expanded
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (boundaryPieces : Chart → Finset BoundaryPiece)
    (interiorBulkTerm : Chart → InteriorPiece → Real)
    (boundaryBulkTerm : Chart → BoundaryPiece → Real) :
    bulkBoundaryLocalSum activeCharts interiorPieces boundaryPieces
        interiorBulkTerm boundaryBulkTerm =
      (Finset.sum activeCharts fun x =>
          Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q :=
  rfl

theorem boundaryPartitionLocalSum_eq_expanded
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset BoundaryPiece)
    (boundaryPartitionTerm : Chart → BoundaryPiece → Real) :
    boundaryPartitionLocalSum activeCharts boundaryPieces boundaryPartitionTerm =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q :=
  rfl

/-- Transport both interior and boundary terms in the split local bulk sum. -/
theorem bulkBoundaryLocalSum_congr
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset InteriorPiece)
    (boundaryPieces : Chart → Finset BoundaryPiece)
    (interiorOld interiorNew : Chart → InteriorPiece → Real)
    (boundaryOld boundaryNew : Chart → BoundaryPiece → Real)
    (hinterior :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ interiorPieces x →
          interiorOld x q = interiorNew x q)
    (hboundary :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          boundaryOld x q = boundaryNew x q) :
    bulkBoundaryLocalSum activeCharts interiorPieces boundaryPieces
        interiorOld boundaryOld =
      bulkBoundaryLocalSum activeCharts interiorPieces boundaryPieces
        interiorNew boundaryNew := by
  rw [bulkBoundaryLocalSum, bulkBoundaryLocalSum]
  rw [chartPieceSum_congr activeCharts interiorPieces interiorOld interiorNew
      hinterior,
    chartPieceSum_congr activeCharts boundaryPieces boundaryOld boundaryNew
      hboundary]

/-- Transport the boundary partition local sum. -/
theorem boundaryPartitionLocalSum_congr
    (activeCharts : Finset Chart)
    (boundaryPieces : Chart → Finset BoundaryPiece)
    (oldTerm newTerm : Chart → BoundaryPiece → Real)
    (hterm :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          oldTerm x q = newTerm x q) :
    boundaryPartitionLocalSum activeCharts boundaryPieces oldTerm =
      boundaryPartitionLocalSum activeCharts boundaryPieces newTerm :=
  chartPieceSum_congr activeCharts boundaryPieces oldTerm newTerm hterm

end BulkBoundarySums

section FiniteAdditivityPackages

universe c p i b

/--
Field package for the analytic finite-additivity statement of one local
integral family.

When the genuine integral is available, the field should be filled by the
theorem saying that the represented integral equals the finite sum of the
selected local pieces.
-/
structure LocalIntegralFiniteAdditivityData
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the local decomposition. -/
  activeCharts : Finset Chart
  /-- Local pieces assigned to each active chart. -/
  localPieces : Chart → Finset Piece
  /-- Integral contribution of one selected local piece. -/
  localIntegralTerm : Chart → Piece → Real
  /-- The represented global integral. -/
  globalIntegral : Real
  /-- Analytic finite-additivity/reconstruction equality. -/
  globalIntegral_eq_localSum :
    globalIntegral =
      chartPieceSum activeCharts localPieces localIntegralTerm

namespace LocalIntegralFiniteAdditivityData

variable {Chart : Type c} {Piece : Type p}

/-- Build finite-additivity data from an already-proved reconstruction equality. -/
def ofEq
    (activeCharts : Finset Chart)
    (localPieces : Chart → Finset Piece)
    (localIntegralTerm : Chart → Piece → Real)
    (globalIntegral : Real)
    (h :
      globalIntegral =
        chartPieceSum activeCharts localPieces localIntegralTerm) :
    LocalIntegralFiniteAdditivityData Chart Piece where
  activeCharts := activeCharts
  localPieces := localPieces
  localIntegralTerm := localIntegralTerm
  globalIntegral := globalIntegral
  globalIntegral_eq_localSum := h

/-- Tautological finite-additivity data whose global integral is defined as the sum. -/
def ofLocalSum
    (activeCharts : Finset Chart)
    (localPieces : Chart → Finset Piece)
    (localIntegralTerm : Chart → Piece → Real) :
    LocalIntegralFiniteAdditivityData Chart Piece where
  activeCharts := activeCharts
  localPieces := localPieces
  localIntegralTerm := localIntegralTerm
  globalIntegral :=
    chartPieceSum activeCharts localPieces localIntegralTerm
  globalIntegral_eq_localSum := rfl

/-- Expanded form of the finite-additivity field. -/
theorem globalIntegral_eq_localSum_expanded
    (D : LocalIntegralFiniteAdditivityData Chart Piece) :
    D.globalIntegral =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q => D.localIntegralTerm x q := by
  simpa [chartPieceSum] using D.globalIntegral_eq_localSum

/-- Sigma-indexed form of the finite-additivity field. -/
theorem globalIntegral_eq_indexSet_sum
    (D : LocalIntegralFiniteAdditivityData Chart Piece) :
    D.globalIntegral =
      Finset.sum (chartPieceIndexSet D.activeCharts D.localPieces) fun qp =>
        D.localIntegralTerm qp.1 qp.2 := by
  calc
    D.globalIntegral =
        chartPieceSum D.activeCharts D.localPieces D.localIntegralTerm :=
      D.globalIntegral_eq_localSum
    _ =
        Finset.sum (chartPieceIndexSet D.activeCharts D.localPieces) fun qp =>
          D.localIntegralTerm qp.1 qp.2 :=
      chartPieceSum_eq_indexSet_sum D.activeCharts D.localPieces
        D.localIntegralTerm

/-- Transport the local term representatives in a finite-additivity package. -/
def transportLocalTerm
    (D : LocalIntegralFiniteAdditivityData Chart Piece)
    (newTerm : Chart → Piece → Real)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          D.localIntegralTerm x q = newTerm x q) :
    LocalIntegralFiniteAdditivityData Chart Piece where
  activeCharts := D.activeCharts
  localPieces := D.localPieces
  localIntegralTerm := newTerm
  globalIntegral := D.globalIntegral
  globalIntegral_eq_localSum := by
    calc
      D.globalIntegral =
          chartPieceSum D.activeCharts D.localPieces D.localIntegralTerm :=
        D.globalIntegral_eq_localSum
      _ = chartPieceSum D.activeCharts D.localPieces newTerm :=
        chartPieceSum_transport D.activeCharts D.localPieces
          D.localIntegralTerm newTerm hterm

end LocalIntegralFiniteAdditivityData

/--
Field package for the two reconstruction equalities used by the mixed global
Stokes layer: finite additivity for the bulk integral, and finite additivity
for the boundary partition integral.
-/
structure BulkBoundaryIntegralFiniteAdditivityData
    (Chart : Type c) (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Finite chart labels active in the chosen partition/cover. -/
  activeCharts : Finset Chart
  /-- Localized interior pieces assigned to each chart. -/
  interiorPieces : Chart → Finset InteriorPiece
  /-- Localized boundary-chart pieces assigned to each chart. -/
  boundaryPieces : Chart → Finset BoundaryPiece
  /-- Bulk contribution of an interior local piece. -/
  interiorBulkTerm : Chart → InteriorPiece → Real
  /-- Bulk contribution of a boundary-chart local piece. -/
  boundaryBulkTerm : Chart → BoundaryPiece → Real
  /-- Boundary contribution after chart changes and boundary reconstruction. -/
  boundaryPartitionTerm : Chart → BoundaryPiece → Real
  /-- The represented global bulk integral. -/
  globalBulkIntegral : Real
  /-- The represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- Bulk finite-additivity/reconstruction equality. -/
  globalBulkIntegral_eq_localBulkSum :
    globalBulkIntegral =
      bulkBoundaryLocalSum activeCharts interiorPieces boundaryPieces
        interiorBulkTerm boundaryBulkTerm
  /-- Boundary finite-additivity/reconstruction equality. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      boundaryPartitionLocalSum activeCharts boundaryPieces
        boundaryPartitionTerm

namespace BulkBoundaryIntegralFiniteAdditivityData

variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/-- Sum of all interior bulk terms in the package. -/
def interiorBulkSum
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    Real :=
  chartPieceSum D.activeCharts D.interiorPieces D.interiorBulkTerm

/-- Sum of all boundary-chart bulk terms in the package. -/
def boundaryBulkSum
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    Real :=
  chartPieceSum D.activeCharts D.boundaryPieces D.boundaryBulkTerm

/-- Total local bulk sum recorded in the package. -/
def localBulkSum
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    Real :=
  interiorBulkSum D + boundaryBulkSum D

/-- Boundary partition sum recorded in the package. -/
def boundaryPartitionSum
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    Real :=
  chartPieceSum D.activeCharts D.boundaryPieces D.boundaryPartitionTerm

/-- Bulk reconstruction field using package-local sum names. -/
theorem globalBulkIntegral_eq_localBulkSum'
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    D.globalBulkIntegral = localBulkSum D := by
  rw [localBulkSum, interiorBulkSum, boundaryBulkSum]
  exact D.globalBulkIntegral_eq_localBulkSum

/-- Boundary reconstruction field using package-local sum names. -/
theorem globalBoundaryIntegral_eq_boundaryPartitionSum'
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    D.globalBoundaryIntegral = boundaryPartitionSum D := by
  rw [boundaryPartitionSum]
  exact D.globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Expanded bulk reconstruction field in the shape expected by global data. -/
theorem globalBulkIntegral_eq_localBulkSum_expanded
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    D.globalBulkIntegral =
      (Finset.sum D.activeCharts fun x =>
          Finset.sum (D.interiorPieces x) fun q => D.interiorBulkTerm x q) +
        Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q => D.boundaryBulkTerm x q := by
  simpa [bulkBoundaryLocalSum, chartPieceSum] using
    D.globalBulkIntegral_eq_localBulkSum

/-- Expanded boundary reconstruction field in the shape expected by global data. -/
theorem globalBoundaryIntegral_eq_boundaryPartitionSum_expanded
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    D.globalBoundaryIntegral =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.boundaryPieces x) fun q =>
          D.boundaryPartitionTerm x q := by
  simpa [boundaryPartitionLocalSum, chartPieceSum] using
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

section ManifoldWrappers

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {k : Nat} {I : ModelWithCorners Real E H}
variable {ω : ManifoldForm I M k}

/-- Convert finite-additivity fields to the existing bulk reconstruction package. -/
def toBulkIntegralReconstructionData
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    BulkIntegralReconstructionData I ω Chart InteriorPiece BoundaryPiece where
  activeCharts := D.activeCharts
  interiorPieces := D.interiorPieces
  boundaryPieces := D.boundaryPieces
  interiorBulkTerm := D.interiorBulkTerm
  boundaryBulkTerm := D.boundaryBulkTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBulkIntegral_eq_localBulkSum :=
    D.globalBulkIntegral_eq_localBulkSum_expanded

/--
Convert finite-additivity fields to the existing two-sided partition
reconstruction package.
-/
def toPartitionReconstructionData
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece where
  activeCharts := D.activeCharts
  interiorPieces := D.interiorPieces
  boundaryPieces := D.boundaryPieces
  interiorBulkTerm := D.interiorBulkTerm
  boundaryBulkTerm := D.boundaryBulkTerm
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum :=
    D.globalBulkIntegral_eq_localBulkSum_expanded
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum_expanded

@[simp]
theorem toPartitionReconstructionData_globalBulkIntegral
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    (D.toPartitionReconstructionData (I := I) (ω := ω)).globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem toPartitionReconstructionData_globalBoundaryIntegral
    (D :
      BulkBoundaryIntegralFiniteAdditivityData Chart InteriorPiece BoundaryPiece) :
    (D.toPartitionReconstructionData (I := I) (ω := ω)).globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

end ManifoldWrappers

end BulkBoundaryIntegralFiniteAdditivityData

end FiniteAdditivityPackages

section ProjectLocalFiniteAdditivity

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Finite-additivity fields for project-local bulk and boundary reconstruction.

The local terms are the project wrappers from `LocalIntegral.lean`; the fields
record the still-analytic equalities identifying the global integrals with the
finite sums of these selected local representatives.
-/
structure ProjectLocalIntegralFiniteAdditivityData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the project-local decomposition. -/
  activeCharts : Finset Chart
  /-- Project-local pieces assigned to each active chart. -/
  localPieces : Chart → Finset Piece
  /-- Source chart for the project-local wrapper. -/
  sourceChart : Chart → Piece → M
  /-- Target chart for the project-local wrapper. -/
  targetChart : Chart → Piece → M
  /-- Lower corner of the selected coordinate box. -/
  lowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the selected coordinate box. -/
  upperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Boundary term after chart changes and boundary reconstruction. -/
  boundaryPartitionTerm : Chart → Piece → Real
  /-- The represented global bulk integral. -/
  globalBulkIntegral : Real
  /-- The represented global boundary integral. -/
  globalBoundaryIntegral : Real
  /-- Bulk finite-additivity/reconstruction equality for project-local pieces. -/
  globalBulkIntegral_eq_projectLocalSum :
    globalBulkIntegral =
      chartPieceSum activeCharts localPieces fun x q =>
        projectLocalBulkIntegral I (sourceChart x q) (targetChart x q) ω
          (lowerCorner x q) (upperCorner x q)
  /-- Boundary finite-additivity/reconstruction equality for partition terms. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      chartPieceSum activeCharts localPieces boundaryPartitionTerm

namespace ProjectLocalIntegralFiniteAdditivityData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Bulk term of one recorded project-local piece. -/
def projectLocalBulkTerm
    (D : ProjectLocalIntegralFiniteAdditivityData I ω Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  projectLocalBulkIntegral I (D.sourceChart x q) (D.targetChart x q) ω
    (D.lowerCorner x q) (D.upperCorner x q)

/-- Boundary term of one recorded project-local piece before reconstruction. -/
def projectLocalBoundaryTerm
    (D : ProjectLocalIntegralFiniteAdditivityData I ω Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
    (D.lowerCorner x q) (D.upperCorner x q)

/-- Sum of all recorded project-local bulk terms. -/
def projectLocalBulkSum
    (D : ProjectLocalIntegralFiniteAdditivityData I ω Chart Piece) : Real :=
  chartPieceSum D.activeCharts D.localPieces (projectLocalBulkTerm D)

/-- Sum of all recorded project-local boundary terms before reconstruction. -/
def projectLocalBoundarySum
    (D : ProjectLocalIntegralFiniteAdditivityData I ω Chart Piece) : Real :=
  chartPieceSum D.activeCharts D.localPieces (projectLocalBoundaryTerm D)

/-- Sum of all selected boundary partition terms. -/
def boundaryPartitionSum
    (D : ProjectLocalIntegralFiniteAdditivityData I ω Chart Piece) : Real :=
  chartPieceSum D.activeCharts D.localPieces D.boundaryPartitionTerm

/-- Bulk reconstruction field using package-local sum names. -/
theorem globalBulkIntegral_eq_projectLocalSum'
    (D : ProjectLocalIntegralFiniteAdditivityData I ω Chart Piece) :
    D.globalBulkIntegral = projectLocalBulkSum D := by
  simpa [projectLocalBulkSum, projectLocalBulkTerm] using
    D.globalBulkIntegral_eq_projectLocalSum

/-- Boundary reconstruction field using package-local sum names. -/
theorem globalBoundaryIntegral_eq_boundaryPartitionSum'
    (D : ProjectLocalIntegralFiniteAdditivityData I ω Chart Piece) :
    D.globalBoundaryIntegral = boundaryPartitionSum D := by
  rw [boundaryPartitionSum]
  exact D.globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Expanded bulk reconstruction field expected by `ProjectLocalGlobalStokesData`. -/
theorem globalBulkIntegral_eq_projectLocalSum_expanded
    (D : ProjectLocalIntegralFiniteAdditivityData I ω Chart Piece) :
    D.globalBulkIntegral =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          projectLocalBulkIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q) := by
  simpa [chartPieceSum] using D.globalBulkIntegral_eq_projectLocalSum

/-- Expanded boundary reconstruction field expected by `ProjectLocalGlobalStokesData`. -/
theorem globalBoundaryIntegral_eq_boundaryPartitionSum_expanded
    (D : ProjectLocalIntegralFiniteAdditivityData I ω Chart Piece) :
    D.globalBoundaryIntegral =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          D.boundaryPartitionTerm x q := by
  simpa [chartPieceSum] using
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

/--
Convert project-local finite-additivity fields plus local Stokes and
chart-change compatibility into the final project-local global package.
-/
def toProjectLocalGlobalStokesDataWith
    (D : ProjectLocalIntegralFiniteAdditivityData I ω Chart Piece)
    (localProjectStokes :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          projectLocalBulkTerm D x q = projectLocalBoundaryTerm D x q)
    (chartChangeCancellation :
      projectLocalBoundarySum D = boundaryPartitionSum D) :
    ProjectLocalGlobalStokesData I ω Chart Piece where
  activeCharts := D.activeCharts
  localPieces := D.localPieces
  sourceChart := D.sourceChart
  targetChart := D.targetChart
  lowerCorner := D.lowerCorner
  upperCorner := D.upperCorner
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_projectLocalSum :=
    D.globalBulkIntegral_eq_projectLocalSum_expanded
  localProjectStokes := by
    simpa [projectLocalBulkTerm, projectLocalBoundaryTerm] using
      localProjectStokes
  chartChangeCancellation := by
    simpa [projectLocalBoundarySum, boundaryPartitionSum,
      projectLocalBoundaryTerm, chartPieceSum] using chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum_expanded

/-- Pointwise chart-change equality gives the project-local boundary sum field. -/
theorem chartChangeCancellation_of_pointwise_eq
    (D : ProjectLocalIntegralFiniteAdditivityData I ω Chart Piece)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          projectLocalBoundaryTerm D x q = D.boundaryPartitionTerm x q) :
    projectLocalBoundarySum D = boundaryPartitionSum D :=
  chartPieceSum_transport D.activeCharts D.localPieces
    (projectLocalBoundaryTerm D) D.boundaryPartitionTerm hterm

end ProjectLocalIntegralFiniteAdditivityData

end ProjectLocalFiniteAdditivity

end Stokes

end
