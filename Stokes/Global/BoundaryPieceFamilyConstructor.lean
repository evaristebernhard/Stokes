import Stokes.Global.MixedGlobalConstructor
import Stokes.Global.BoundaryPieces
import Stokes.Global.BoundaryGlobalConstructor
import Stokes.Global.BoundaryChartChangePieces
import Stokes.BoundaryChart.BoundaryPieceConvenience

/-!
# Boundary piece families for the mixed global constructor

This file packages a finite family of boundary-chart pieces in the local shape
needed by `MixedGlobalStokesData`.  It deliberately carries no global integral
reconstruction, partition-of-unity data, or chart-change-to-boundary-partition
field: the only output is the `MixedBoundaryPackage` local Stokes component and
its finite-sum wrapper.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryPieceFamilyConstructor

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace MixedBoundaryPackage

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}
variable {activeCharts : Finset Chart}
variable {boundaryPieces : Chart → Finset Piece}
variable {boundaryBulkTerm boundaryBoundaryTerm : Chart → Piece → Real}

/-- The boundary local Stokes identities in a mixed package summed over all pieces. -/
theorem boundaryBulkSum_eq_boundaryBoundarySum
    (P :
      MixedBoundaryPackage I omega Chart Piece activeCharts boundaryPieces
        boundaryBulkTerm boundaryBoundaryTerm) :
    (Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q) =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryBoundaryTerm x q := by
  exact GlobalStokesData.sum_localPieces activeCharts boundaryPieces
    boundaryBulkTerm boundaryBoundaryTerm P.localStokes

end MixedBoundaryPackage

/--
Input data for a finite family of oriented boundary-chart pieces.

For each active piece, the source extended boundary box gives the bulk side,
while the target selected boundary box and image data transport the boundary
side to the chart in which later global chart-change/reconstruction data will
compare it.
-/
structure BoundaryPieceFamilyInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (omega : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the boundary-piece decomposition. -/
  activeCharts : Finset Chart
  /-- Boundary-chart pieces assigned to each active chart. -/
  boundaryPieces : Chart → Finset Piece
  /-- Source chart for the bulk transition representative. -/
  sourceChart : Chart → Piece → M
  /-- Shared boundary chart: bulk target and transported-boundary source. -/
  boundarySourceChart : Chart → Piece → M
  /-- Target boundary chart for the transported boundary representative. -/
  boundaryTargetChart : Chart → Piece → M
  /-- Lower corner of the source boundary-chart box. -/
  sourceLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the source boundary-chart box. -/
  sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Lower corner of the target boundary-chart box. -/
  targetLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the target boundary-chart box. -/
  targetUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Extended source boxes for all active boundary pieces. -/
  sourceExtendedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryChartExtendedBox I (sourceChart x q) (boundarySourceChart x q) omega
          (sourceLowerCorner x q) (sourceUpperCorner x q)
  /-- Selected target boxes for all active boundary pieces. -/
  targetSelectedBox :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q) omega
          (targetLowerCorner x q) (targetUpperCorner x q)
  /-- Image data transporting each source boundary face onto its target box. -/
  imageData :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        boundaryChartSelectedBoxImageData I (sourceChart x q) (boundarySourceChart x q)
          (sourceLowerCorner x q) (sourceUpperCorner x q)
          (targetLowerCorner x q) (targetUpperCorner x q)

namespace BoundaryPieceFamilyInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Bulk term of one boundary-chart family piece. -/
def boundaryBulkTerm
    (D : BoundaryPieceFamilyInput I omega Chart Piece) (x : Chart) (q : Piece) :
    Real :=
  projectLocalBulkIntegral I (D.sourceChart x q) (D.boundarySourceChart x q) omega
    (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)

/-- Transported boundary term of one boundary-chart family piece. -/
def boundaryBoundaryTerm
    (D : BoundaryPieceFamilyInput I omega Chart Piece) (x : Chart) (q : Piece) :
    Real :=
  projectLocalBoundaryIntegral I
    (D.boundarySourceChart x q) (D.boundaryTargetChart x q) omega
    (D.targetLowerCorner x q) (D.targetUpperCorner x q)

/-- Sum of all recorded boundary-chart bulk terms. -/
def boundaryBulkSum
    (D : BoundaryPieceFamilyInput I omega Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => boundaryBulkTerm D x q

/-- Sum of all transported boundary terms before global chart-change assembly. -/
def boundaryBoundarySum
    (D : BoundaryPieceFamilyInput I omega Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => boundaryBoundaryTerm D x q

/-- Source selected-box data derived from the recorded source extended box. -/
theorem sourceSelectedBox
    (D : BoundaryPieceFamilyInput I omega Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts) {q : Piece}
    (hq : q ∈ D.boundaryPieces x) :
    boundaryChartSelectedBox I (D.sourceChart x q) (D.boundarySourceChart x q) omega
      (D.sourceLowerCorner x q) (D.sourceUpperCorner x q) :=
  (D.sourceExtendedBox x hx q hq).selectedBox

/--
Local Stokes for an oriented-atlas boundary-piece family, with each boundary
term transported to the selected target boundary chart.
-/
theorem localStokes_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryPieceFamilyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.boundarySourceChart x q ∈ A.charts) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.boundaryPieces x →
        boundaryBulkTerm D x q = boundaryBoundaryTerm D x q := by
  intro x hx q hq
  exact projectLocalStokes_of_orientedAtlas_imageData
    A (hsource x hx q hq) (hboundarySource x hx q hq)
    (D.boundaryTargetChart x q) omega
    (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)
    (D.targetLowerCorner x q) (D.targetUpperCorner x q)
    (D.sourceExtendedBox x hx q hq)
    (D.targetSelectedBox x hx q hq)
    (D.imageData x hx q hq)

/--
Local Stokes for an oriented boundary-charted manifold boundary-piece family,
with each boundary term transported to the selected target boundary chart.
-/
theorem localStokes
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryPieceFamilyInput I omega Chart Piece) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.boundaryPieces x →
        boundaryBulkTerm D x q = boundaryBoundaryTerm D x q := by
  intro x hx q hq
  exact projectLocalStokes_of_orientedManifold_imageData
    (D.sourceChart x q) (D.boundarySourceChart x q) (D.boundaryTargetChart x q) omega
    (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)
    (D.targetLowerCorner x q) (D.targetUpperCorner x q)
    (D.sourceExtendedBox x hx q hq)
    (D.targetSelectedBox x hx q hq)
    (D.imageData x hx q hq)

/--
View an oriented-atlas boundary-piece family as the boundary local-Stokes
package expected by the mixed global constructor.
-/
def toMixedBoundaryPackage_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryPieceFamilyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.boundarySourceChart x q ∈ A.charts) :
    MixedBoundaryPackage I omega Chart Piece
      D.activeCharts D.boundaryPieces (boundaryBulkTerm D) (boundaryBoundaryTerm D) where
  localStokes := D.localStokes_of_orientedAtlas A hsource hboundarySource

/--
View an oriented-boundary-manifold boundary-piece family as the boundary
local-Stokes package expected by the mixed global constructor.
-/
def toMixedBoundaryPackage
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryPieceFamilyInput I omega Chart Piece) :
    MixedBoundaryPackage I omega Chart Piece
      D.activeCharts D.boundaryPieces (boundaryBulkTerm D) (boundaryBoundaryTerm D) where
  localStokes := D.localStokes

/-- The oriented-atlas boundary-piece family local Stokes theorem summed over all pieces. -/
theorem boundaryBulkSum_eq_boundaryBoundarySum_of_orientedAtlas
    [IsManifold I 1 M]
    (D : BoundaryPieceFamilyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.boundarySourceChart x q ∈ A.charts) :
    boundaryBulkSum D = boundaryBoundarySum D := by
  exact MixedBoundaryPackage.boundaryBulkSum_eq_boundaryBoundarySum
    (D.toMixedBoundaryPackage_of_orientedAtlas A hsource hboundarySource)

/-- The oriented-manifold boundary-piece family local Stokes theorem summed over all pieces. -/
theorem boundaryBulkSum_eq_boundaryBoundarySum
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : BoundaryPieceFamilyInput I omega Chart Piece) :
    boundaryBulkSum D = boundaryBoundarySum D := by
  exact D.toMixedBoundaryPackage.boundaryBulkSum_eq_boundaryBoundarySum

end BoundaryPieceFamilyInput

namespace OrientedBoundaryProjectLocalPieces

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
Forget the global reconstruction fields of an oriented boundary-piece package,
keeping only the boundary-chart family data needed for local mixed assembly.
-/
def toBoundaryPieceFamilyInput
    (D : OrientedBoundaryProjectLocalPieces I omega Chart Piece) :
    BoundaryPieceFamilyInput I omega Chart Piece where
  activeCharts := D.activeCharts
  boundaryPieces := D.localPieces
  sourceChart := D.sourceChart
  boundarySourceChart := D.boundarySourceChart
  boundaryTargetChart := D.boundaryTargetChart
  sourceLowerCorner := D.sourceLowerCorner
  sourceUpperCorner := D.sourceUpperCorner
  targetLowerCorner := D.targetLowerCorner
  targetUpperCorner := D.targetUpperCorner
  sourceExtendedBox := D.sourceExtendedBox
  targetSelectedBox := D.targetSelectedBox
  imageData := D.imageData

/-- Oriented-atlas boundary pieces as a mixed boundary local-Stokes package. -/
def toMixedBoundaryPackage_of_orientedAtlas
    [IsManifold I 1 M]
    (D : OrientedBoundaryProjectLocalPieces I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.boundarySourceChart x q ∈ A.charts) :
    MixedBoundaryPackage I omega Chart Piece
      D.activeCharts D.localPieces
      (OrientedBoundaryProjectLocalPieces.projectLocalBulkTerm D)
      (OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm D) := by
  simpa [toBoundaryPieceFamilyInput,
    BoundaryPieceFamilyInput.boundaryBulkTerm,
    BoundaryPieceFamilyInput.boundaryBoundaryTerm] using
    (D.toBoundaryPieceFamilyInput.toMixedBoundaryPackage_of_orientedAtlas
      A hsource hboundarySource)

/-- Oriented-manifold boundary pieces as a mixed boundary local-Stokes package. -/
def toMixedBoundaryPackage
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : OrientedBoundaryProjectLocalPieces I omega Chart Piece) :
    MixedBoundaryPackage I omega Chart Piece
      D.activeCharts D.localPieces
      (OrientedBoundaryProjectLocalPieces.projectLocalBulkTerm D)
      (OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm D) := by
  simpa [toBoundaryPieceFamilyInput,
    BoundaryPieceFamilyInput.boundaryBulkTerm,
    BoundaryPieceFamilyInput.boundaryBoundaryTerm] using
    D.toBoundaryPieceFamilyInput.toMixedBoundaryPackage

/-- The oriented-atlas boundary-piece local Stokes theorem summed over all pieces. -/
theorem projectLocalBulkSum_eq_projectLocalBoundarySum_of_orientedAtlas
    [IsManifold I 1 M]
    (D : OrientedBoundaryProjectLocalPieces I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hsource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x → D.boundarySourceChart x q ∈ A.charts) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          OrientedBoundaryProjectLocalPieces.projectLocalBulkTerm D x q) =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm D x q := by
  exact MixedBoundaryPackage.boundaryBulkSum_eq_boundaryBoundarySum
    (D.toMixedBoundaryPackage_of_orientedAtlas A hsource hboundarySource)

/-- The oriented-manifold boundary-piece local Stokes theorem summed over all pieces. -/
theorem projectLocalBulkSum_eq_projectLocalBoundarySum
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (D : OrientedBoundaryProjectLocalPieces I omega Chart Piece) :
    (Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          OrientedBoundaryProjectLocalPieces.projectLocalBulkTerm D x q) =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q =>
          OrientedBoundaryProjectLocalPieces.projectLocalBoundaryTerm D x q := by
  exact D.toMixedBoundaryPackage.boundaryBulkSum_eq_boundaryBoundarySum

end OrientedBoundaryProjectLocalPieces

end BoundaryPieceFamilyConstructor

end Stokes

end
