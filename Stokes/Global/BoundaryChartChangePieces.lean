import Stokes.Global.ChartChange

/-!
# Boundary chart-change pieces for project-local cancellation

This file packages the analytic boundary-chart change-of-variables data in the
shape needed by the project-local global Stokes assembly layer.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryChartChangePieces

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
One boundary chart-change piece over a fixed source project-local boundary
term.  The `TargetBox` parameter lets the same structure record either a
selected target box or an extended target box.
-/
structure BoundaryChartChangePieceData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (sourceChart boundarySourceChart : M)
    (sourceLowerCorner sourceUpperCorner : Fin (n + 1) → Real)
    (TargetBox :
      M → M → (Fin (n + 1) → Real) → (Fin (n + 1) → Real) → Prop) where
  /-- Target auxiliary chart used after the boundary chart change. -/
  boundaryTargetChart : M
  /-- Lower corner of the target boundary-coordinate box. -/
  targetLowerCorner : Fin (n + 1) → Real
  /-- Upper corner of the target boundary-coordinate box. -/
  targetUpperCorner : Fin (n + 1) → Real
  /-- Oriented local change-of-variables data from the source box to the target box. -/
  changeOfVariables :
    boundaryChartOrientedChangeOfVariables I sourceChart boundarySourceChart ω
      sourceLowerCorner sourceUpperCorner targetLowerCorner targetUpperCorner
  /-- Target box data, specialized below to selected or extended target boxes. -/
  targetBox :
    TargetBox boundarySourceChart boundaryTargetChart targetLowerCorner targetUpperCorner

/-- Target-box predicate for selected boundary-chart boxes. -/
abbrev boundaryChartSelectedTargetBox {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) :
    M → M → (Fin (n + 1) → Real) → (Fin (n + 1) → Real) → Prop :=
  fun x1 x2 c d => boundaryChartSelectedBox I x1 x2 ω c d

/-- Target-box predicate for extended boundary-chart boxes. -/
abbrev boundaryChartExtendedTargetBox {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n) :
    M → M → (Fin (n + 1) → Real) → (Fin (n + 1) → Real) → Prop :=
  fun x1 x2 c d => boundaryChartExtendedBox I x1 x2 ω c d

/-- One selected-target boundary chart-change piece. -/
abbrev BoundaryChartChangeSelectedPieceData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (sourceChart boundarySourceChart : M)
    (sourceLowerCorner sourceUpperCorner : Fin (n + 1) → Real) :=
  BoundaryChartChangePieceData I ω sourceChart boundarySourceChart
    sourceLowerCorner sourceUpperCorner (boundaryChartSelectedTargetBox I ω)

/-- One extended-target boundary chart-change piece. -/
abbrev BoundaryChartChangeExtendedPieceData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (sourceChart boundarySourceChart : M)
    (sourceLowerCorner sourceUpperCorner : Fin (n + 1) → Real) :=
  BoundaryChartChangePieceData I ω sourceChart boundarySourceChart
    sourceLowerCorner sourceUpperCorner (boundaryChartExtendedTargetBox I ω)

namespace BoundaryChartChangePieceData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable [IsManifold I 1 M]
variable {ω : ManifoldForm I M n}
variable {sourceChart boundarySourceChart : M}
variable {sourceLowerCorner sourceUpperCorner : Fin (n + 1) → Real}

/-- The target boundary term represented by a selected-target piece. -/
def selectedTargetBoundaryTerm
    (P : BoundaryChartChangeSelectedPieceData I ω sourceChart boundarySourceChart
      sourceLowerCorner sourceUpperCorner) : Real :=
  projectLocalBoundaryIntegral I boundarySourceChart P.boundaryTargetChart ω
    P.targetLowerCorner P.targetUpperCorner

/-- The target boundary term represented by an extended-target piece. -/
def extendedTargetBoundaryTerm
    (P : BoundaryChartChangeExtendedPieceData I ω sourceChart boundarySourceChart
      sourceLowerCorner sourceUpperCorner) : Real :=
  projectLocalBoundaryIntegral I boundarySourceChart P.boundaryTargetChart ω
    P.targetLowerCorner P.targetUpperCorner

/-- One selected-target COV piece identifies the source and target boundary terms. -/
theorem boundaryIntegral_eq_selectedTarget
    (P : BoundaryChartChangeSelectedPieceData I ω sourceChart boundarySourceChart
      sourceLowerCorner sourceUpperCorner) :
    projectLocalBoundaryIntegral I sourceChart boundarySourceChart ω
        sourceLowerCorner sourceUpperCorner =
      selectedTargetBoundaryTerm P := by
  exact projectLocalBoundaryIntegral_chartChange_selected
    sourceChart boundarySourceChart P.boundaryTargetChart ω
    sourceLowerCorner sourceUpperCorner P.targetLowerCorner P.targetUpperCorner
    P.changeOfVariables P.targetBox

/-- One extended-target COV piece identifies the source and target boundary terms. -/
theorem boundaryIntegral_eq_extendedTarget
    (P : BoundaryChartChangeExtendedPieceData I ω sourceChart boundarySourceChart
      sourceLowerCorner sourceUpperCorner) :
    projectLocalBoundaryIntegral I sourceChart boundarySourceChart ω
        sourceLowerCorner sourceUpperCorner =
      extendedTargetBoundaryTerm P := by
  exact projectLocalBoundaryIntegral_chartChange_extended
    sourceChart boundarySourceChart P.boundaryTargetChart ω
    sourceLowerCorner sourceUpperCorner P.targetLowerCorner P.targetUpperCorner
    P.changeOfVariables P.targetBox

/-- An extended-target piece also supplies the corresponding selected-target piece. -/
def selectedOfExtended
    (P : BoundaryChartChangeExtendedPieceData I ω sourceChart boundarySourceChart
      sourceLowerCorner sourceUpperCorner) :
    BoundaryChartChangeSelectedPieceData I ω sourceChart boundarySourceChart
      sourceLowerCorner sourceUpperCorner where
  boundaryTargetChart := P.boundaryTargetChart
  targetLowerCorner := P.targetLowerCorner
  targetUpperCorner := P.targetUpperCorner
  changeOfVariables := P.changeOfVariables
  targetBox := P.targetBox.selectedBox

end BoundaryChartChangePieceData

/--
Boundary chart-change data for all active pieces of a
`ProjectLocalGlobalStokesData` package.

The family is relative to `D`: its source chart, boundary source chart, and
source box are the project-local boundary term already recorded in `D`.  For
each active piece it records a target chart/box plus the local oriented COV
package, and it identifies `D.boundaryPartitionTerm` with the transported target
boundary integral.
-/
structure BoundaryChartChangeFamilyData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (D : ProjectLocalGlobalStokesData I ω Chart Piece)
    (TargetBox :
      M → M → (Fin (n + 1) → Real) → (Fin (n + 1) → Real) → Prop) where
  /-- Per-piece chart-change data on every active local boundary piece. -/
  pieceData :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        BoundaryChartChangePieceData I ω (D.sourceChart x q) (D.targetChart x q)
          (D.lowerCorner x q) (D.upperCorner x q) TargetBox
  /--
  The global boundary-partition representative is the transported target
  boundary integral for every active piece.
  -/
  boundaryPartitionTerm_eq :
    ∀ x, (hx : x ∈ D.activeCharts) →
      ∀ q, (hq : q ∈ D.localPieces x) →
        let P := pieceData x hx q hq
        D.boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (D.targetChart x q) P.boundaryTargetChart ω
            P.targetLowerCorner P.targetUpperCorner

/-- Selected-target family data. -/
abbrev BoundaryChartChangeSelectedFamilyData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :=
  BoundaryChartChangeFamilyData D (boundaryChartSelectedTargetBox I ω)

/-- Extended-target family data. -/
abbrev BoundaryChartChangeExtendedFamilyData {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    {Chart : Type c} {Piece : Type p}
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) :=
  BoundaryChartChangeFamilyData D (boundaryChartExtendedTargetBox I ω)

namespace BoundaryChartChangeFamilyData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable [IsManifold I 1 M]
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}
variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}

/-- Target boundary term of an active selected-target family piece. -/
def selectedTargetBoundaryTerm
    (F : BoundaryChartChangeSelectedFamilyData D)
    (x : Chart) (hx : x ∈ D.activeCharts) (q : Piece) (hq : q ∈ D.localPieces x) :
    Real :=
  (F.pieceData x hx q hq).selectedTargetBoundaryTerm

/-- Target boundary term of an active extended-target family piece. -/
def extendedTargetBoundaryTerm
    (F : BoundaryChartChangeExtendedFamilyData D)
    (x : Chart) (hx : x ∈ D.activeCharts) (q : Piece) (hq : q ∈ D.localPieces x) :
    Real :=
  (F.pieceData x hx q hq).extendedTargetBoundaryTerm

/--
Pointwise source-to-partition equality supplied by selected-target boundary COV
data.
-/
theorem pointwise_eq_boundaryPartition_selected
    (F : BoundaryChartChangeSelectedFamilyData D) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q) =
          D.boundaryPartitionTerm x q := by
  intro x hx q hq
  calc
    projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q) =
        selectedTargetBoundaryTerm F x hx q hq := by
          exact (F.pieceData x hx q hq).boundaryIntegral_eq_selectedTarget
    _ = D.boundaryPartitionTerm x q := by
          exact (F.boundaryPartitionTerm_eq x hx q hq).symm

/--
Pointwise source-to-partition equality supplied by extended-target boundary COV
data.
-/
theorem pointwise_eq_boundaryPartition_extended
    (F : BoundaryChartChangeExtendedFamilyData D) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q) =
          D.boundaryPartitionTerm x q := by
  intro x hx q hq
  calc
    projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
        (D.lowerCorner x q) (D.upperCorner x q) =
        extendedTargetBoundaryTerm F x hx q hq := by
          exact (F.pieceData x hx q hq).boundaryIntegral_eq_extendedTarget
    _ = D.boundaryPartitionTerm x q := by
          exact (F.boundaryPartitionTerm_eq x hx q hq).symm

/--
Selected-target boundary chart-change data as pure finite-sum cancellation
data.
-/
def toChartChangeCancellationData_selected
    (F : BoundaryChartChangeSelectedFamilyData D) :
    ChartChangeCancellationData Chart Piece Real :=
  ProjectLocalGlobalStokesData.chartChangeCancellationDataOfPointwiseEq D
    F.pointwise_eq_boundaryPartition_selected

/--
Extended-target boundary chart-change data as pure finite-sum cancellation
data.
-/
def toChartChangeCancellationData_extended
    (F : BoundaryChartChangeExtendedFamilyData D) :
    ChartChangeCancellationData Chart Piece Real :=
  ProjectLocalGlobalStokesData.chartChangeCancellationDataOfPointwiseEq D
    F.pointwise_eq_boundaryPartition_extended

/--
Selected-target data fills the `ProjectLocalGlobalStokesData.chartChangeCancellation`
field.
-/
theorem chartChangeCancellation_selected
    (F : BoundaryChartChangeSelectedFamilyData D) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q)) =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q := by
  exact F.toChartChangeCancellationData_selected.chartChangeCancellation

/--
Extended-target data fills the `ProjectLocalGlobalStokesData.chartChangeCancellation`
field.
-/
theorem chartChangeCancellation_extended
    (F : BoundaryChartChangeExtendedFamilyData D) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q)) =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q := by
  exact F.toChartChangeCancellationData_extended.chartChangeCancellation

end BoundaryChartChangeFamilyData

namespace ProjectLocalGlobalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable [IsManifold I 1 M]
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
Selected-target boundary chart-change family data directly supplies the
project-local chart-change cancellation field.
-/
theorem chartChangeCancellation_of_boundaryChartChange_selected
    (D : ProjectLocalGlobalStokesData I ω Chart Piece)
    (F : BoundaryChartChangeSelectedFamilyData D) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q)) =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q :=
  F.chartChangeCancellation_selected

/--
Extended-target boundary chart-change family data directly supplies the
project-local chart-change cancellation field.
-/
theorem chartChangeCancellation_of_boundaryChartChange_extended
    (D : ProjectLocalGlobalStokesData I ω Chart Piece)
    (F : BoundaryChartChangeExtendedFamilyData D) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q)) =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q :=
  F.chartChangeCancellation_extended

end ProjectLocalGlobalStokesData

end BoundaryChartChangePieces

end Stokes

end
