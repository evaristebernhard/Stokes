import Stokes.Global.Partition
import Stokes.Global.Theorem

/-!
# Boundary project-local pieces

This module instantiates the project-local global Stokes package with
boundary-chart pieces.  It is a bookkeeping layer: local Stokes is discharged
from the existing boundary-chart extended-box theorems, while global
reconstruction and chart-change compatibility remain explicit fields.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryPieces

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Boundary-chart pieces in the exact shape expected by
`ProjectLocalGlobalStokesData`.

Each active piece carries a source/target boundary chart pair, source box
corners, and an extended boundary-chart box.  The extended box proves the local
project Stokes identity.  The remaining global reconstruction and chart-change
terms are recorded as fields for the later global integration layer.
-/
structure BoundaryProjectLocalPieces {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the boundary-piece decomposition. -/
  activeCharts : Finset Chart
  /-- Boundary-local pieces assigned to an active chart. -/
  localPieces : Chart → Finset Piece
  /-- Source chart for the project-local wrapper. -/
  sourceChart : Chart → Piece → M
  /-- Target chart for the project-local wrapper. -/
  targetChart : Chart → Piece → M
  /-- Lower corner of the selected boundary-chart source box. -/
  lowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the selected boundary-chart source box. -/
  upperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Extended boundary-chart boxes for all active local pieces. -/
  extendedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x →
        boundaryChartExtendedBox I (sourceChart x q) (targetChart x q) ω
          (lowerCorner x q) (upperCorner x q)
  /-- Boundary term after chart changes and partition reconstruction. -/
  boundaryPartitionTerm : Chart → Piece → Real
  /-- The global bulk integral represented by this boundary-piece package. -/
  globalBulkIntegral : Real
  /-- The global boundary integral represented by this boundary-piece package. -/
  globalBoundaryIntegral : Real
  /-- Reconstruction of the global bulk integral from project-local bulk terms. -/
  globalBulkIntegral_eq_projectLocalSum :
    globalBulkIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q =>
          projectLocalBulkIntegral I (sourceChart x q) (targetChart x q) ω
            (lowerCorner x q) (upperCorner x q)
  /--
  Compatibility of project-local boundary representatives with the chosen
  boundary partition terms.
  -/
  chartChangeCancellation :
    (Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q =>
          projectLocalBoundaryIntegral I (sourceChart x q) (targetChart x q) ω
            (lowerCorner x q) (upperCorner x q)) =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q => boundaryPartitionTerm x q
  /-- Reconstruction of the global boundary integral from the boundary partition. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q => boundaryPartitionTerm x q

namespace BoundaryProjectLocalPieces

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Bulk term of one recorded project-local boundary piece. -/
def projectLocalBulkTerm
    (D : BoundaryProjectLocalPieces I ω Chart Piece) (x : Chart) (q : Piece) : Real :=
  projectLocalBulkIntegral I (D.sourceChart x q) (D.targetChart x q) ω
    (D.lowerCorner x q) (D.upperCorner x q)

/-- Boundary term of one recorded project-local boundary piece. -/
def projectLocalBoundaryTerm
    (D : BoundaryProjectLocalPieces I ω Chart Piece) (x : Chart) (q : Piece) : Real :=
  projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
    (D.lowerCorner x q) (D.upperCorner x q)

/-- Sum of all recorded project-local boundary-piece bulk terms. -/
def projectLocalBulkSum
    (D : BoundaryProjectLocalPieces I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.localPieces x) fun q => projectLocalBulkTerm D x q

/-- Sum of all recorded project-local boundary-piece boundary terms. -/
def projectLocalBoundarySum
    (D : BoundaryProjectLocalPieces I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.localPieces x) fun q => projectLocalBoundaryTerm D x q

/-- Sum of the selected boundary partition terms. -/
def boundaryPartitionSum
    (D : BoundaryProjectLocalPieces I ω Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q

/-- The selected-box part carried by each active extended box. -/
theorem selectedBox
    (D : BoundaryProjectLocalPieces I ω Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts) {q : Piece} (hq : q ∈ D.localPieces x) :
    boundaryChartSelectedBox I (D.sourceChart x q) (D.targetChart x q) ω
      (D.lowerCorner x q) (D.upperCorner x q) :=
  (D.extendedBox x hx q hq).selectedBox

/-- The lower-zero-face convention for each active boundary source box. -/
theorem lowerCorner_zero
    (D : BoundaryProjectLocalPieces I ω Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts) {q : Piece} (hq : q ∈ D.localPieces x) :
    D.lowerCorner x q 0 = 0 :=
  (D.selectedBox hx hq).ha0

/-- Box-ordering for each active boundary source box. -/
theorem lower_le_upper
    (D : BoundaryProjectLocalPieces I ω Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts) {q : Piece} (hq : q ∈ D.localPieces x) :
    D.lowerCorner x q ≤ D.upperCorner x q :=
  (D.selectedBox hx hq).le

/-- Domain containment for each active boundary source box. -/
theorem Icc_subset_boundaryChartDomain
    (D : BoundaryProjectLocalPieces I ω Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts) {q : Piece} (hq : q ∈ D.localPieces x) :
    Set.Icc (D.lowerCorner x q) (D.upperCorner x q) ⊆
      boundaryChartDomain I (D.sourceChart x q) (D.targetChart x q) :=
  (D.selectedBox hx hq).Icc_subset_domain

/-- Compact-support containment for each active boundary source box. -/
theorem tsupport_subset_halfSpaceSupportBox
    (D : BoundaryProjectLocalPieces I ω Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts) {q : Piece} (hq : q ∈ D.localPieces x) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (D.sourceChart x q) (D.targetChart x q) ω) ⊆
      halfSpaceSupportBox (D.lowerCorner x q) (D.upperCorner x q) :=
  (D.selectedBox hx hq).tsupport_subset

/-- Ambient smooth-extension neighborhood for each active boundary source box. -/
theorem exists_smooth_nhds
    (D : BoundaryProjectLocalPieces I ω Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts) {q : Piece} (hq : q ∈ D.localPieces x) :
    ∃ U : Set (Fin (n + 1) → Real),
      IsOpen U ∧ Set.Icc (D.lowerCorner x q) (D.upperCorner x q) ⊆ U ∧
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (D.sourceChart x q) (D.targetChart x q) ω) U :=
  (D.extendedBox x hx q hq).exists_smooth_nhds

/--
Local project Stokes for every active piece, proved from the recorded extended
boundary-chart box.
-/
theorem localProjectStokes
    (D : BoundaryProjectLocalPieces I ω Chart Piece) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        projectLocalBulkIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q) =
          projectLocalBoundaryIntegral I (D.sourceChart x q) (D.targetChart x q) ω
            (D.lowerCorner x q) (D.upperCorner x q) := by
  intro x hx q hq
  exact projectLocalStokes_of_boundaryChartExtendedBox
    I (D.sourceChart x q) (D.targetChart x q) ω
    (D.lowerCorner x q) (D.upperCorner x q)
    (D.extendedBox x hx q hq)

/-- Summed local project Stokes over all active boundary pieces. -/
theorem projectLocalBulkSum_eq_projectLocalBoundarySum
    (D : BoundaryProjectLocalPieces I ω Chart Piece) :
    projectLocalBulkSum D = projectLocalBoundarySum D := by
  exact GlobalStokesData.sum_localPieces D.activeCharts D.localPieces
    (projectLocalBulkTerm D) (projectLocalBoundaryTerm D) (D.localProjectStokes)

/--
Instantiate the project-local global Stokes package from boundary-chart pieces.
The local Stokes field is supplied by `localProjectStokes`; reconstruction and
chart-change fields are exactly the explicit fields of `D`.
-/
def toProjectLocalGlobalStokesData
    (D : BoundaryProjectLocalPieces I ω Chart Piece) :
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
  globalBulkIntegral_eq_projectLocalSum := D.globalBulkIntegral_eq_projectLocalSum
  localProjectStokes := D.localProjectStokes
  chartChangeCancellation := D.chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Boundary-piece global Stokes via the instantiated project-local package. -/
theorem stokes
    (D : BoundaryProjectLocalPieces I ω Chart Piece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  ProjectLocalGlobalStokesData.stokes D.toProjectLocalGlobalStokesData

/--
The same data can also be viewed as a `GlobalStokesData` package with no
interior pieces.
-/
def toGlobalStokesData
    (D : BoundaryProjectLocalPieces I ω Chart Piece) :
    GlobalStokesData I ω Chart Empty Piece where
  activeCharts := D.activeCharts
  interiorPieces := fun _ => ∅
  boundaryPieces := D.localPieces
  interiorBulkTerm := fun _ q => Empty.elim q
  interiorBoundaryTerm := fun _ q => Empty.elim q
  boundaryBulkTerm := projectLocalBulkTerm D
  boundaryBoundaryTerm := projectLocalBoundaryTerm D
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := by
    simpa [projectLocalBulkTerm] using D.globalBulkIntegral_eq_projectLocalSum
  interiorLocalStokes := by
    intro _ _ q _
    cases q
  boundaryLocalStokes := by
    intro x hx q hq
    exact D.localProjectStokes x hx q hq
  interiorBoundaryCancellation := by
    simp
  chartChangeCancellation := by
    simpa [projectLocalBoundaryTerm] using D.chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

end BoundaryProjectLocalPieces

/--
Boundary-chart pieces whose local Stokes boundary term is transported to a
chosen target boundary chart using oriented image data.

This package is slightly more general than `ProjectLocalGlobalStokesData`: the
bulk term is computed in a source chart pair `(x₀, x₁)`, while the boundary term
is represented in a possibly different target pair `(x₁, x₂)` with its own
selected box.  It therefore instantiates `GlobalStokesData` directly.
-/
structure OrientedBoundaryProjectLocalPieces {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the boundary-piece decomposition. -/
  activeCharts : Finset Chart
  /-- Boundary-local pieces assigned to an active chart. -/
  localPieces : Chart → Finset Piece
  /-- Source chart `x₀` for the bulk transition representative. -/
  sourceChart : Chart → Piece → M
  /-- Shared boundary chart `x₁`: bulk target and boundary source. -/
  boundarySourceChart : Chart → Piece → M
  /-- Target boundary chart `x₂` for the transported boundary representative. -/
  boundaryTargetChart : Chart → Piece → M
  /-- Lower corner of the source boundary-chart box. -/
  sourceLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the source boundary-chart box. -/
  sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Lower corner of the target boundary-chart box. -/
  targetLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the target boundary-chart box. -/
  targetUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Extended source boxes for all active local pieces. -/
  sourceExtendedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x →
        boundaryChartExtendedBox I (sourceChart x q) (boundarySourceChart x q) ω
          (sourceLowerCorner x q) (sourceUpperCorner x q)
  /-- Selected target boxes for all active local pieces. -/
  targetSelectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x →
        boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q) ω
          (targetLowerCorner x q) (targetUpperCorner x q)
  /-- Image data transporting the source boundary face onto the target box. -/
  imageData :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ localPieces x →
        boundaryChartSelectedBoxImageData I (sourceChart x q) (boundarySourceChart x q)
          (sourceLowerCorner x q) (sourceUpperCorner x q)
          (targetLowerCorner x q) (targetUpperCorner x q)
  /-- Boundary term after chart changes and partition reconstruction. -/
  boundaryPartitionTerm : Chart → Piece → Real
  /-- The global bulk integral represented by this oriented boundary-piece package. -/
  globalBulkIntegral : Real
  /-- The global boundary integral represented by this oriented boundary-piece package. -/
  globalBoundaryIntegral : Real
  /-- Reconstruction of the global bulk integral from oriented project-local bulk terms. -/
  globalBulkIntegral_eq_localBulkSum :
    globalBulkIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q =>
          projectLocalBulkIntegral I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q)
  /--
  Compatibility of transported boundary representatives with the chosen
  boundary partition terms.
  -/
  chartChangeCancellation :
    (Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q =>
          projectLocalBoundaryIntegral I
            (boundarySourceChart x q) (boundaryTargetChart x q) ω
            (targetLowerCorner x q) (targetUpperCorner x q)) =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q => boundaryPartitionTerm x q
  /-- Reconstruction of the global boundary integral from the boundary partition. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q => boundaryPartitionTerm x q

namespace OrientedBoundaryProjectLocalPieces

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Bulk term of one oriented boundary piece. -/
def projectLocalBulkTerm
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  projectLocalBulkIntegral I (D.sourceChart x q) (D.boundarySourceChart x q) ω
    (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)

/-- Transported boundary term of one oriented boundary piece. -/
def projectLocalBoundaryTerm
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  projectLocalBoundaryIntegral I
    (D.boundarySourceChart x q) (D.boundaryTargetChart x q) ω
    (D.targetLowerCorner x q) (D.targetUpperCorner x q)

/-- Source selected-box data derived from the recorded source extended box. -/
theorem sourceSelectedBox
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts) {q : Piece} (hq : q ∈ D.localPieces x) :
    boundaryChartSelectedBox I (D.sourceChart x q) (D.boundarySourceChart x q) ω
      (D.sourceLowerCorner x q) (D.sourceUpperCorner x q) :=
  (D.sourceExtendedBox x hx q hq).selectedBox

/--
Local project Stokes for an oriented-atlas boundary piece, with the boundary
term transported to the selected target boundary chart.
-/
theorem localProjectStokes_of_orientedAtlas
    [IsManifold I 1 M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.boundarySourceChart x q ∈ A.charts) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        projectLocalBulkTerm D x q = projectLocalBoundaryTerm D x q := by
  intro x hx q hq
  exact projectLocalStokes_of_orientedAtlas_imageData
    A (hsource x hx q hq) (hboundarySource x hx q hq)
    (D.boundaryTargetChart x q) ω
    (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)
    (D.targetLowerCorner x q) (D.targetUpperCorner x q)
    (D.sourceExtendedBox x hx q hq)
    (D.targetSelectedBox x hx q hq)
    (D.imageData x hx q hq)

/--
Local project Stokes for an oriented boundary-charted manifold, with the
boundary term transported to the selected target boundary chart.
-/
theorem localProjectStokes_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        projectLocalBulkTerm D x q = projectLocalBoundaryTerm D x q := by
  intro x hx q hq
  exact projectLocalStokes_of_orientedManifold_imageData
    (D.sourceChart x q) (D.boundarySourceChart x q) (D.boundaryTargetChart x q) ω
    (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)
    (D.targetLowerCorner x q) (D.targetUpperCorner x q)
    (D.sourceExtendedBox x hx q hq)
    (D.targetSelectedBox x hx q hq)
    (D.imageData x hx q hq)

/--
Instantiate `GlobalStokesData` from oriented-atlas boundary pieces, with no
interior pieces.  The chart-membership hypotheses are exactly the local
orientation inputs needed by the image-data Stokes wrapper.
-/
def toGlobalStokesData_of_orientedAtlas
    [IsManifold I 1 M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.boundarySourceChart x q ∈ A.charts) :
    GlobalStokesData I ω Chart Empty Piece where
  activeCharts := D.activeCharts
  interiorPieces := fun _ => ∅
  boundaryPieces := D.localPieces
  interiorBulkTerm := fun _ q => Empty.elim q
  interiorBoundaryTerm := fun _ q => Empty.elim q
  boundaryBulkTerm := projectLocalBulkTerm D
  boundaryBoundaryTerm := projectLocalBoundaryTerm D
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := by
    simpa [projectLocalBulkTerm] using D.globalBulkIntegral_eq_localBulkSum
  interiorLocalStokes := by
    intro _ _ q _
    cases q
  boundaryLocalStokes :=
    D.localProjectStokes_of_orientedAtlas A hsource hboundarySource
  interiorBoundaryCancellation := by
    simp
  chartChangeCancellation := by
    simpa [projectLocalBoundaryTerm] using D.chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

/--
Instantiate `GlobalStokesData` from oriented-boundary-manifold pieces, with no
interior pieces.
-/
def toGlobalStokesData_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece) :
    GlobalStokesData I ω Chart Empty Piece where
  activeCharts := D.activeCharts
  interiorPieces := fun _ => ∅
  boundaryPieces := D.localPieces
  interiorBulkTerm := fun _ q => Empty.elim q
  interiorBoundaryTerm := fun _ q => Empty.elim q
  boundaryBulkTerm := projectLocalBulkTerm D
  boundaryBoundaryTerm := projectLocalBoundaryTerm D
  boundaryPartitionTerm := D.boundaryPartitionTerm
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := by
    simpa [projectLocalBulkTerm] using D.globalBulkIntegral_eq_localBulkSum
  interiorLocalStokes := by
    intro _ _ q _
    cases q
  boundaryLocalStokes := D.localProjectStokes_of_orientedManifold
  interiorBoundaryCancellation := by
    simp
  chartChangeCancellation := by
    simpa [projectLocalBoundaryTerm] using D.chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    D.globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Global Stokes from oriented-atlas boundary pieces. -/
theorem stokes_of_orientedAtlas
    [IsManifold I 1 M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.boundarySourceChart x q ∈ A.charts) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  GlobalStokesData.stokes
    (D.toGlobalStokesData_of_orientedAtlas A hsource hboundarySource)

/-- Global Stokes from oriented-boundary-manifold boundary pieces. -/
theorem stokes_of_orientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : OrientedBoundaryProjectLocalPieces I ω Chart Piece) :
    D.globalBulkIntegral = D.globalBoundaryIntegral :=
  GlobalStokesData.stokes D.toGlobalStokesData_of_orientedManifold

end OrientedBoundaryProjectLocalPieces

end BoundaryPieces

end Stokes

end
