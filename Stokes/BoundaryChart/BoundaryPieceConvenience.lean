import Stokes.Global.BoundaryPieces

/-!
# Boundary-piece convenience constructors

This file contains small constructors for the oriented boundary-piece global
package.  They keep the analytic data at the selected-box level and fill the
pure bookkeeping fields by definition.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryPieceConvenience

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace OrientedBoundaryProjectLocalPieces

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/--
Build oriented boundary project-local pieces from per-piece selected-box image
data, choosing the global terms to be the corresponding finite sums.

The only remaining inputs are geometric: source extended boxes, target selected
boxes, and image data transporting each source lower face onto its target box.
-/
def ofSelectedBoxImageData
    {Chart : Type c} {Piece : Type p}
    (activeCharts : Finset Chart) (localPieces : Chart → Finset Piece)
    (sourceChart boundarySourceChart boundaryTargetChart : Chart → Piece → M)
    (sourceLowerCorner sourceUpperCorner targetLowerCorner targetUpperCorner :
      Chart → Piece → Fin (n + 1) → Real)
    (sourceExtendedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartExtendedBox I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q))
    (targetSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q) ω
            (targetLowerCorner x q) (targetUpperCorner x q))
    (imageData :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBoxImageData I (sourceChart x q) (boundarySourceChart x q)
            (sourceLowerCorner x q) (sourceUpperCorner x q)
            (targetLowerCorner x q) (targetUpperCorner x q)) :
    OrientedBoundaryProjectLocalPieces I ω Chart Piece where
  activeCharts := activeCharts
  localPieces := localPieces
  sourceChart := sourceChart
  boundarySourceChart := boundarySourceChart
  boundaryTargetChart := boundaryTargetChart
  sourceLowerCorner := sourceLowerCorner
  sourceUpperCorner := sourceUpperCorner
  targetLowerCorner := targetLowerCorner
  targetUpperCorner := targetUpperCorner
  sourceExtendedBox := sourceExtendedBox
  targetSelectedBox := targetSelectedBox
  imageData := imageData
  boundaryPartitionTerm := fun x q =>
    projectLocalBoundaryIntegral I (boundarySourceChart x q) (boundaryTargetChart x q) ω
      (targetLowerCorner x q) (targetUpperCorner x q)
  globalBulkIntegral :=
    Finset.sum activeCharts fun x =>
      Finset.sum (localPieces x) fun q =>
        projectLocalBulkIntegral I (sourceChart x q) (boundarySourceChart x q) ω
          (sourceLowerCorner x q) (sourceUpperCorner x q)
  globalBoundaryIntegral :=
    Finset.sum activeCharts fun x =>
      Finset.sum (localPieces x) fun q =>
        projectLocalBoundaryIntegral I (boundarySourceChart x q) (boundaryTargetChart x q) ω
          (targetLowerCorner x q) (targetUpperCorner x q)
  globalBulkIntegral_eq_localBulkSum := rfl
  chartChangeCancellation := rfl
  globalBoundaryIntegral_eq_boundaryPartitionSum := rfl

/--
The oriented-atlas-facing version of `ofSelectedBoxImageData`.  The atlas
membership hypotheses are recorded as constructor inputs so callers can pass
exactly the local orientation data used by `stokes_of_orientedAtlas`.
-/
def ofSelectedBoxImageData_orientedAtlas
    {Chart : Type c} {Piece : Type p} [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (activeCharts : Finset Chart) (localPieces : Chart → Finset Piece)
    (sourceChart boundarySourceChart boundaryTargetChart : Chart → Piece → M)
    (sourceLowerCorner sourceUpperCorner targetLowerCorner targetUpperCorner :
      Chart → Piece → Fin (n + 1) → Real)
    (sourceExtendedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartExtendedBox I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q))
    (targetSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q) ω
            (targetLowerCorner x q) (targetUpperCorner x q))
    (imageData :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBoxImageData I (sourceChart x q) (boundarySourceChart x q)
            (sourceLowerCorner x q) (sourceUpperCorner x q)
            (targetLowerCorner x q) (targetUpperCorner x q))
    (_hsource :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x → sourceChart x q ∈ A.charts)
    (_hboundarySource :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x → boundarySourceChart x q ∈ A.charts) :
    OrientedBoundaryProjectLocalPieces I ω Chart Piece :=
  ofSelectedBoxImageData activeCharts localPieces sourceChart boundarySourceChart
    boundaryTargetChart sourceLowerCorner sourceUpperCorner targetLowerCorner
    targetUpperCorner sourceExtendedBox targetSelectedBox imageData

/--
Global Stokes for the finite-sum package created from selected-box image data
and oriented-atlas membership.
-/
theorem stokes_ofSelectedBoxImageData_orientedAtlas
    {Chart : Type c} {Piece : Type p} [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (activeCharts : Finset Chart) (localPieces : Chart → Finset Piece)
    (sourceChart boundarySourceChart boundaryTargetChart : Chart → Piece → M)
    (sourceLowerCorner sourceUpperCorner targetLowerCorner targetUpperCorner :
      Chart → Piece → Fin (n + 1) → Real)
    (sourceExtendedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartExtendedBox I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q))
    (targetSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q) ω
            (targetLowerCorner x q) (targetUpperCorner x q))
    (imageData :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBoxImageData I (sourceChart x q) (boundarySourceChart x q)
            (sourceLowerCorner x q) (sourceUpperCorner x q)
            (targetLowerCorner x q) (targetUpperCorner x q))
    (hsource :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x → sourceChart x q ∈ A.charts)
    (hboundarySource :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x → boundarySourceChart x q ∈ A.charts) :
    (Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q =>
          projectLocalBulkIntegral I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q)) =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q =>
          projectLocalBoundaryIntegral I
            (boundarySourceChart x q) (boundaryTargetChart x q) ω
            (targetLowerCorner x q) (targetUpperCorner x q) := by
  exact
    (ofSelectedBoxImageData activeCharts localPieces sourceChart boundarySourceChart
      boundaryTargetChart sourceLowerCorner sourceUpperCorner targetLowerCorner
      targetUpperCorner sourceExtendedBox targetSelectedBox imageData).stokes_of_orientedAtlas
        A hsource hboundarySource

/--
The oriented-manifold-facing version of `ofSelectedBoxImageData`; the global
orientation is supplied by typeclass inference.
-/
def ofSelectedBoxImageData_orientedManifold
    {Chart : Type c} {Piece : Type p}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (activeCharts : Finset Chart) (localPieces : Chart → Finset Piece)
    (sourceChart boundarySourceChart boundaryTargetChart : Chart → Piece → M)
    (sourceLowerCorner sourceUpperCorner targetLowerCorner targetUpperCorner :
      Chart → Piece → Fin (n + 1) → Real)
    (sourceExtendedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartExtendedBox I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q))
    (targetSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q) ω
            (targetLowerCorner x q) (targetUpperCorner x q))
    (imageData :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBoxImageData I (sourceChart x q) (boundarySourceChart x q)
            (sourceLowerCorner x q) (sourceUpperCorner x q)
            (targetLowerCorner x q) (targetUpperCorner x q)) :
    OrientedBoundaryProjectLocalPieces I ω Chart Piece :=
  ofSelectedBoxImageData activeCharts localPieces sourceChart boundarySourceChart
    boundaryTargetChart sourceLowerCorner sourceUpperCorner targetLowerCorner
    targetUpperCorner sourceExtendedBox targetSelectedBox imageData

/--
Global Stokes for the selected-box image-data constructor on an oriented
boundary-charted manifold.
-/
theorem stokes_ofSelectedBoxImageData_orientedManifold
    {Chart : Type c} {Piece : Type p}
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (activeCharts : Finset Chart) (localPieces : Chart → Finset Piece)
    (sourceChart boundarySourceChart boundaryTargetChart : Chart → Piece → M)
    (sourceLowerCorner sourceUpperCorner targetLowerCorner targetUpperCorner :
      Chart → Piece → Fin (n + 1) → Real)
    (sourceExtendedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartExtendedBox I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q))
    (targetSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q) ω
            (targetLowerCorner x q) (targetUpperCorner x q))
    (imageData :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ localPieces x →
          boundaryChartSelectedBoxImageData I (sourceChart x q) (boundarySourceChart x q)
            (sourceLowerCorner x q) (sourceUpperCorner x q)
            (targetLowerCorner x q) (targetUpperCorner x q)) :
    (Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q =>
          projectLocalBulkIntegral I (sourceChart x q) (boundarySourceChart x q) ω
            (sourceLowerCorner x q) (sourceUpperCorner x q)) =
      Finset.sum activeCharts fun x =>
        Finset.sum (localPieces x) fun q =>
          projectLocalBoundaryIntegral I
            (boundarySourceChart x q) (boundaryTargetChart x q) ω
            (targetLowerCorner x q) (targetUpperCorner x q) := by
  exact
    (ofSelectedBoxImageData activeCharts localPieces sourceChart boundarySourceChart
      boundaryTargetChart sourceLowerCorner sourceUpperCorner targetLowerCorner
      targetUpperCorner sourceExtendedBox targetSelectedBox imageData).stokes_of_orientedManifold

/--
Single-piece selected-box image-data constructor.  The resulting package has one
active chart label and one local piece, so its global terms are the two local
project-local terms.
-/
def ofSelectedBoxImageData_piece
    (x0 x1 x2 : M) (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    OrientedBoundaryProjectLocalPieces I ω Unit Unit where
  activeCharts := {()}
  localPieces := fun _ => {()}
  sourceChart := fun _ _ => x0
  boundarySourceChart := fun _ _ => x1
  boundaryTargetChart := fun _ _ => x2
  sourceLowerCorner := fun _ _ => a
  sourceUpperCorner := fun _ _ => b
  targetLowerCorner := fun _ _ => c
  targetUpperCorner := fun _ _ => d
  sourceExtendedBox := by
    intro x _ q _
    cases x
    cases q
    simpa using hboxSource
  targetSelectedBox := by
    intro x _ q _
    cases x
    cases q
    simpa using hboxTarget
  imageData := by
    intro x _ q _
    cases x
    cases q
    simpa using himage
  boundaryPartitionTerm := fun _ _ =>
    projectLocalBoundaryIntegral I x1 x2 ω c d
  globalBulkIntegral := projectLocalBulkIntegral I x0 x1 ω a b
  globalBoundaryIntegral := projectLocalBoundaryIntegral I x1 x2 ω c d
  globalBulkIntegral_eq_localBulkSum := by
    simp
  chartChangeCancellation := by
    simp
  globalBoundaryIntegral_eq_boundaryPartitionSum := by
    simp

/-- Single-piece constructor with explicit oriented-atlas data. -/
def ofSelectedBoxImageData_orientedAtlas_piece
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (_hx0 : x0 ∈ A.charts) (_hx1 : x1 ∈ A.charts)
    (x2 : M) (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    OrientedBoundaryProjectLocalPieces I ω Unit Unit :=
  ofSelectedBoxImageData_piece x0 x1 x2 a b c d hboxSource hboxTarget himage

/-- Direct single-piece oriented-atlas Stokes projection. -/
theorem stokes_ofSelectedBoxImageData_orientedAtlas_piece
    [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M) {x0 x1 : M}
    (hx0 : x0 ∈ A.charts) (hx1 : x1 ∈ A.charts)
    (x2 : M) (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    projectLocalBulkIntegral I x0 x1 ω a b =
      projectLocalBoundaryIntegral I x1 x2 ω c d := by
  let D :=
    ofSelectedBoxImageData_piece
      (I := I) (ω := ω) x0 x1 x2 a b c d hboxSource hboxTarget himage
  change D.globalBulkIntegral = D.globalBoundaryIntegral
  exact D.stokes_of_orientedAtlas A
    (by
      intro x _ q _
      cases x
      cases q
      simpa using hx0)
    (by
      intro x _ q _
      cases x
      cases q
      simpa using hx1)

/-- Single-piece constructor specialized to an oriented boundary-charted manifold. -/
def ofSelectedBoxImageData_orientedManifold_piece
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    OrientedBoundaryProjectLocalPieces I ω Unit Unit :=
  ofSelectedBoxImageData_piece x0 x1 x2 a b c d hboxSource hboxTarget himage

/-- Direct single-piece oriented-manifold Stokes projection. -/
theorem stokes_ofSelectedBoxImageData_orientedManifold_piece
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (x0 x1 x2 : M) (a b c d : Fin (n + 1) → Real)
    (hboxSource : boundaryChartExtendedBox I x0 x1 ω a b)
    (hboxTarget : boundaryChartSelectedBox I x1 x2 ω c d)
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    projectLocalBulkIntegral I x0 x1 ω a b =
      projectLocalBoundaryIntegral I x1 x2 ω c d := by
  let D :=
    ofSelectedBoxImageData_piece
      (I := I) (ω := ω) x0 x1 x2 a b c d hboxSource hboxTarget himage
  change D.globalBulkIntegral = D.globalBoundaryIntegral
  exact D.stokes_of_orientedManifold

end OrientedBoundaryProjectLocalPieces

end BoundaryPieceConvenience

end Stokes

end
