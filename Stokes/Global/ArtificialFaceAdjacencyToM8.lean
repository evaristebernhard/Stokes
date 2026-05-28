import Stokes.Global.ArtificialFacePairingToM8

/-!
# Adjacent artificial faces for M8

This file gives a slightly more natural M8-facing layer for artificial-face
adjacency data.  The lower files already prove the cancellation theorem from
adjacent/opposite faces.  Here we package the three alignments that M8 needs:

* the adjacent-face active set is the selected active set;
* each selected chart has the singleton `Unit` interior piece;
* the recorded project-local artificial boundary term is the M8 localized
  artificial-boundary term.

The constructions are bookkeeping only.  The geometric input remains explicit
in `AdjacentSelectedFacesData` and `ArtificialFaceOverlapPairingData`.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section ArtificialFaceAdjacencyToM8

universe u w b f d g

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

/--
M8-facing wrapper around adjacent selected-face data.

This is useful when the adjacency package has already been constructed and the
remaining work is only to expose the M8 alignment fields.
-/
structure M8AdjacentSelectedFaceData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages)
    (Face : Type f) (Geometry : Type g) where
  /-- Adjacent artificial faces for the selected chart boxes. -/
  adjacency : AdjacentSelectedFacesData I omega M Unit Face Geometry
  /-- The adjacency package uses exactly the selected active charts. -/
  active_eq : adjacency.activeCharts = selectedPartition.active
  /-- The adjacency package uses one singleton interior piece per chart. -/
  singleton_pieces :
    adjacency.interiorPieces = fun _ : M => ({()} : Finset Unit)
  /--
  The M8 localized artificial-boundary term is the project-local term recorded
  by the selected adjacent-face package.
  -/
  boundaryTerm_eq_project :
    forall x, x ∈ adjacency.activeCharts ->
      forall q, q ∈ adjacency.interiorPieces x ->
        measureLocalization.interiorBoundaryTerm x q =
          projectInteriorBoundaryIntegral I (adjacency.sourceChart x q)
            (adjacency.targetChart x q) omega (adjacency.lowerCorner x q)
            (adjacency.upperCorner x q)

namespace M8AdjacentSelectedFaceData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}
variable {Face : Type f} {Geometry : Type g}

@[simp]
theorem adjacency_active
    (D :
      M8AdjacentSelectedFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face Geometry) :
    D.adjacency.activeCharts = selectedPartition.active :=
  D.active_eq

@[simp]
theorem adjacency_pieces
    (D :
      M8AdjacentSelectedFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face Geometry) :
    D.adjacency.interiorPieces = fun _ : M => ({()} : Finset Unit) :=
  D.singleton_pieces

/-- Boundary-term alignment in the exact shape consumed by the M8 constructor. -/
theorem boundaryTerm_eq_project_on_active
    (D :
      M8AdjacentSelectedFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face Geometry) :
    forall x, x ∈ D.adjacency.activeCharts ->
      forall q, q ∈ D.adjacency.interiorPieces x ->
        measureLocalization.interiorBoundaryTerm x q =
          projectInteriorBoundaryIntegral I (D.adjacency.sourceChart x q)
            (D.adjacency.targetChart x q) omega
            (D.adjacency.lowerCorner x q) (D.adjacency.upperCorner x q) :=
  D.boundaryTerm_eq_project

/-- Convert M8-facing adjacent-face data to the artificial-face field package. -/
def toM8ArtificialFaceFields
    (D :
      M8AdjacentSelectedFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face Geometry) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  M8ArtificialFaceFields.ofAdjacentSelectedFacesDataBoundaryTerm
    D.adjacency D.active_eq D.singleton_pieces D.boundaryTerm_eq_project

@[simp]
theorem toM8ArtificialFaceFields_artificialFaces
    (D :
      M8AdjacentSelectedFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face Geometry) :
    D.toM8ArtificialFaceFields.artificialFaces =
      ArtificialFaceResolvedData.ofAdjacentSelectedFacesBoundaryTerm
        D.adjacency measureLocalization.interiorBoundaryTerm
        D.boundaryTerm_eq_project :=
  rfl

@[simp]
theorem toM8ArtificialFaceFields_active
    (D :
      M8AdjacentSelectedFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face Geometry) :
    D.toM8ArtificialFaceFields.artificialFaces.activeCharts =
      selectedPartition.active :=
  D.toM8ArtificialFaceFields.artificialFaces_active

@[simp]
theorem toM8ArtificialFaceFields_pieces
    (D :
      M8AdjacentSelectedFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face Geometry) :
    D.toM8ArtificialFaceFields.artificialFaces.interiorPieces =
      fun _ : M => ({()} : Finset Unit) :=
  D.toM8ArtificialFaceFields.artificialFaces_pieces

@[simp]
theorem toM8ArtificialFaceFields_term
    (D :
      M8AdjacentSelectedFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face Geometry) :
    D.toM8ArtificialFaceFields.artificialFaces.interiorBoundaryTerm =
      measureLocalization.interiorBoundaryTerm :=
  D.toM8ArtificialFaceFields.artificialFaces_term

end M8AdjacentSelectedFaceData

/--
M8-facing wrapper around overlap-pairing data.

This is parallel to `M8AdjacentSelectedFaceData`, but it starts from the
overlap-pairing package directly.
-/
structure M8OverlapPairingFaceData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (omega : ManifoldForm I M n)
    (BoundaryPiece : Type b)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    (measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages)
    (Face : Type f) (FaceDimension : Type d) (Geometry : Type g) where
  /-- Overlap-pairing artificial-face data. -/
  overlap : ArtificialFaceOverlapPairingData M Unit Face FaceDimension Geometry
  /-- The overlap package uses exactly the selected active charts. -/
  active_eq : overlap.activeCharts = selectedPartition.active
  /-- The overlap package uses one singleton interior piece per chart. -/
  singleton_pieces :
    overlap.interiorPieces = fun _ : M => ({()} : Finset Unit)
  /--
  The M8 localized artificial-boundary term is the overlap package's recorded
  artificial boundary term.
  -/
  boundaryTerm_eq_overlap :
    forall x, x ∈ overlap.activeCharts ->
      forall q, q ∈ overlap.interiorPieces x ->
        measureLocalization.interiorBoundaryTerm x q =
          overlap.toArtificialFacePairingData.interiorBoundaryTerm x q

namespace M8OverlapPairingFaceData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}
variable {Face : Type f} {FaceDimension : Type d} {Geometry : Type g}

@[simp]
theorem overlap_active
    (D :
      M8OverlapPairingFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face FaceDimension Geometry) :
    D.overlap.activeCharts = selectedPartition.active :=
  D.active_eq

@[simp]
theorem overlap_pieces
    (D :
      M8OverlapPairingFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face FaceDimension Geometry) :
    D.overlap.interiorPieces = fun _ : M => ({()} : Finset Unit) :=
  D.singleton_pieces

/-- Boundary-term alignment in the exact shape consumed by the M8 constructor. -/
theorem boundaryTerm_eq_overlap_on_active
    (D :
      M8OverlapPairingFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face FaceDimension Geometry) :
    forall x, x ∈ D.overlap.activeCharts ->
      forall q, q ∈ D.overlap.interiorPieces x ->
        measureLocalization.interiorBoundaryTerm x q =
          D.overlap.toArtificialFacePairingData.interiorBoundaryTerm x q :=
  D.boundaryTerm_eq_overlap

/-- Convert M8-facing overlap-pairing data to the artificial-face field package. -/
def toM8ArtificialFaceFields
    (D :
      M8OverlapPairingFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face FaceDimension Geometry) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  M8ArtificialFaceFields.ofOverlapPairingDataBoundaryTerm
    D.overlap D.active_eq D.singleton_pieces D.boundaryTerm_eq_overlap

@[simp]
theorem toM8ArtificialFaceFields_artificialFaces
    (D :
      M8OverlapPairingFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face FaceDimension Geometry) :
    D.toM8ArtificialFaceFields.artificialFaces =
      ArtificialFaceResolvedData.ofOverlapPairingBoundaryTerm
        D.overlap measureLocalization.interiorBoundaryTerm
        D.boundaryTerm_eq_overlap :=
  rfl

@[simp]
theorem toM8ArtificialFaceFields_active
    (D :
      M8OverlapPairingFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face FaceDimension Geometry) :
    D.toM8ArtificialFaceFields.artificialFaces.activeCharts =
      selectedPartition.active :=
  D.toM8ArtificialFaceFields.artificialFaces_active

@[simp]
theorem toM8ArtificialFaceFields_pieces
    (D :
      M8OverlapPairingFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face FaceDimension Geometry) :
    D.toM8ArtificialFaceFields.artificialFaces.interiorPieces =
      fun _ : M => ({()} : Finset Unit) :=
  D.toM8ArtificialFaceFields.artificialFaces_pieces

@[simp]
theorem toM8ArtificialFaceFields_term
    (D :
      M8OverlapPairingFaceData I omega BoundaryPiece selectedPartition
        targetImages measureLocalization Face FaceDimension Geometry) :
    D.toM8ArtificialFaceFields.artificialFaces.interiorBoundaryTerm =
      measureLocalization.interiorBoundaryTerm :=
  D.toM8ArtificialFaceFields.artificialFaces_term

end M8OverlapPairingFaceData

namespace SelectedBoxPartitionOfUnity

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
variable {measureLocalization :
  M8MeasureLocalizationData I omega selectedPartition targetImages}
variable {Face : Type f} {Geometry : Type g}

/--
Selected-partition adjacent-face data with the M8 singleton `Unit` piece.

The older generic constructor in `ArtificialFaceAdjacency` uses `PUnit`; this
version is definitionaly aligned with M8's `Unit` singleton-piece convention.
-/
def toUnitAdjacentSelectedFacesData
    (P : SelectedBoxPartitionOfUnity I omega)
    (faceIndices : M -> Finset Face)
    (coordinateFace : M -> Face -> ArtificialCoordinateFace n)
    (geometricFace : M -> Face -> Geometry)
    (unsignedFaceTerm : M -> Face -> Real)
    (boundaryTerm_eq_faceSum :
      forall i, i ∈ P.active ->
        projectInteriorBoundaryIntegral I i i omega (P.lower i) (P.upper i) =
          Finset.sum (faceIndices i) fun f =>
            (coordinateFace i f).sign * unsignedFaceTerm i f)
    (pair : ArtificialFaceIndex M Unit Face -> ArtificialFaceIndex M Unit Face)
    (pair_mem :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair r ∈
            artificialFaceIndexSet P.active
              (fun _ : M => ({()} : Finset Unit))
              (fun i _ => faceIndices i))
    (pair_involutive :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair (pair r) = r)
    (paired_coordinateFace_opposite :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          coordinateFace (pair r).1.1 (pair r).2 =
            (coordinateFace r.1.1 r.2).opposite)
    (paired_geometricFace_eq :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          geometricFace r.1.1 r.2 = geometricFace (pair r).1.1 (pair r).2)
    (paired_unsignedFaceTerm_eq :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) r =
            artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) (pair r))
    (fixed_terms_zero :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair r = r ->
            artificialFaceTerm
              (fun i _ f => (coordinateFace i f).sign * unsignedFaceTerm i f) r = 0) :
    AdjacentSelectedFacesData I omega M Unit Face Geometry where
  activeCharts := P.active
  interiorPieces := fun _ => ({()} : Finset Unit)
  sourceChart := fun i _ => i
  targetChart := fun i _ => i
  lowerCorner := fun i _ => P.lower i
  upperCorner := fun i _ => P.upper i
  selectedBox := by
    intro i hi q _hq
    cases q
    exact P.selectedBox hi
  faceIndices := fun i _ => faceIndices i
  coordinateFace := fun i _ f => coordinateFace i f
  geometricFace := fun i _ f => geometricFace i f
  unsignedFaceTerm := fun i _ f => unsignedFaceTerm i f
  boundaryTerm_eq_faceSum := by
    intro i hi q _hq
    cases q
    exact boundaryTerm_eq_faceSum i hi
  pair := pair
  pair_mem := pair_mem
  pair_involutive := pair_involutive
  paired_coordinateFace_opposite := paired_coordinateFace_opposite
  paired_geometricFace_eq := paired_geometricFace_eq
  paired_unsignedFaceTerm_eq := paired_unsignedFaceTerm_eq
  fixed_terms_zero := fixed_terms_zero

@[simp]
theorem toUnitAdjacentSelectedFacesData_activeCharts
    (P : SelectedBoxPartitionOfUnity I omega)
    (faceIndices : M -> Finset Face)
    (coordinateFace : M -> Face -> ArtificialCoordinateFace n)
    (geometricFace : M -> Face -> Geometry)
    (unsignedFaceTerm : M -> Face -> Real)
    (boundaryTerm_eq_faceSum pair pair_mem pair_involutive
      paired_coordinateFace_opposite paired_geometricFace_eq
      paired_unsignedFaceTerm_eq fixed_terms_zero) :
    (P.toUnitAdjacentSelectedFacesData faceIndices coordinateFace geometricFace
      unsignedFaceTerm boundaryTerm_eq_faceSum pair pair_mem pair_involutive
      paired_coordinateFace_opposite paired_geometricFace_eq
      paired_unsignedFaceTerm_eq fixed_terms_zero).activeCharts = P.active :=
  rfl

@[simp]
theorem toUnitAdjacentSelectedFacesData_interiorPieces
    (P : SelectedBoxPartitionOfUnity I omega)
    (faceIndices : M -> Finset Face)
    (coordinateFace : M -> Face -> ArtificialCoordinateFace n)
    (geometricFace : M -> Face -> Geometry)
    (unsignedFaceTerm : M -> Face -> Real)
    (boundaryTerm_eq_faceSum pair pair_mem pair_involutive
      paired_coordinateFace_opposite paired_geometricFace_eq
      paired_unsignedFaceTerm_eq fixed_terms_zero) :
    (P.toUnitAdjacentSelectedFacesData faceIndices coordinateFace geometricFace
      unsignedFaceTerm boundaryTerm_eq_faceSum pair pair_mem pair_involutive
      paired_coordinateFace_opposite paired_geometricFace_eq
      paired_unsignedFaceTerm_eq fixed_terms_zero).interiorPieces =
        fun _ : M => ({()} : Finset Unit) :=
  rfl

/--
The selected Unit-adjacency package records the project-local boundary term of
the selected chart box.
-/
theorem toUnitAdjacentSelectedFacesData_projectBoundaryTerm
    (P : SelectedBoxPartitionOfUnity I omega)
    (faceIndices : M -> Finset Face)
    (coordinateFace : M -> Face -> ArtificialCoordinateFace n)
    (geometricFace : M -> Face -> Geometry)
    (unsignedFaceTerm : M -> Face -> Real)
    (boundaryTerm_eq_faceSum pair pair_mem pair_involutive
      paired_coordinateFace_opposite paired_geometricFace_eq
      paired_unsignedFaceTerm_eq fixed_terms_zero) :
    let D :=
      P.toUnitAdjacentSelectedFacesData faceIndices coordinateFace geometricFace
        unsignedFaceTerm boundaryTerm_eq_faceSum pair pair_mem pair_involutive
        paired_coordinateFace_opposite paired_geometricFace_eq
        paired_unsignedFaceTerm_eq fixed_terms_zero
    (fun x q =>
        projectInteriorBoundaryIntegral I (D.sourceChart x q)
          (D.targetChart x q) omega (D.lowerCorner x q)
          (D.upperCorner x q)) =
      fun x _ =>
        projectInteriorBoundaryIntegral I x x omega (P.lower x) (P.upper x) := by
  funext x q
  cases q
  rfl

/--
Pointwise M8 boundary-term alignment for the selected Unit-adjacency package.
-/
theorem toUnitAdjacentSelectedFacesData_m8BoundaryTerm_eq_project
    (P : SelectedBoxPartitionOfUnity I omega)
    (faceIndices : M -> Finset Face)
    (coordinateFace : M -> Face -> ArtificialCoordinateFace n)
    (geometricFace : M -> Face -> Geometry)
    (unsignedFaceTerm : M -> Face -> Real)
    (boundaryTerm_eq_faceSum pair pair_mem pair_involutive
      paired_coordinateFace_opposite paired_geometricFace_eq
      paired_unsignedFaceTerm_eq fixed_terms_zero)
    (hterm :
      forall x, x ∈ P.active ->
        measureLocalization.interiorBoundaryTerm x () =
          projectInteriorBoundaryIntegral I x x omega (P.lower x) (P.upper x)) :
    let D :=
      P.toUnitAdjacentSelectedFacesData faceIndices coordinateFace geometricFace
        unsignedFaceTerm boundaryTerm_eq_faceSum pair pair_mem pair_involutive
        paired_coordinateFace_opposite paired_geometricFace_eq
        paired_unsignedFaceTerm_eq fixed_terms_zero
    forall x, x ∈ D.activeCharts ->
      forall q, q ∈ D.interiorPieces x ->
        measureLocalization.interiorBoundaryTerm x q =
          projectInteriorBoundaryIntegral I (D.sourceChart x q)
            (D.targetChart x q) omega (D.lowerCorner x q)
            (D.upperCorner x q) := by
  intro D x hx q _hq
  cases q
  exact hterm x hx

/--
Build the generic M8-adjacent wrapper from selected-partition face adjacency
fields.
-/
def toM8AdjacentSelectedFaceData
    (P : SelectedBoxPartitionOfUnity I omega)
    (hactiveP : P.active = selectedPartition.active)
    (faceIndices : M -> Finset Face)
    (coordinateFace : M -> Face -> ArtificialCoordinateFace n)
    (geometricFace : M -> Face -> Geometry)
    (unsignedFaceTerm : M -> Face -> Real)
    (boundaryTerm_eq_faceSum :
      forall i, i ∈ P.active ->
        projectInteriorBoundaryIntegral I i i omega (P.lower i) (P.upper i) =
          Finset.sum (faceIndices i) fun f =>
            (coordinateFace i f).sign * unsignedFaceTerm i f)
    (pair : ArtificialFaceIndex M Unit Face -> ArtificialFaceIndex M Unit Face)
    (pair_mem :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair r ∈
            artificialFaceIndexSet P.active
              (fun _ : M => ({()} : Finset Unit))
              (fun i _ => faceIndices i))
    (pair_involutive :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair (pair r) = r)
    (paired_coordinateFace_opposite :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          coordinateFace (pair r).1.1 (pair r).2 =
            (coordinateFace r.1.1 r.2).opposite)
    (paired_geometricFace_eq :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          geometricFace r.1.1 r.2 = geometricFace (pair r).1.1 (pair r).2)
    (paired_unsignedFaceTerm_eq :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) r =
            artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) (pair r))
    (fixed_terms_zero :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair r = r ->
            artificialFaceTerm
              (fun i _ f => (coordinateFace i f).sign * unsignedFaceTerm i f) r = 0)
    (hterm :
      forall x, x ∈ P.active ->
        measureLocalization.interiorBoundaryTerm x () =
          projectInteriorBoundaryIntegral I x x omega (P.lower x) (P.upper x)) :
    M8AdjacentSelectedFaceData I omega BoundaryPiece selectedPartition
      targetImages measureLocalization Face Geometry where
  adjacency :=
    P.toUnitAdjacentSelectedFacesData faceIndices coordinateFace geometricFace
      unsignedFaceTerm boundaryTerm_eq_faceSum pair pair_mem pair_involutive
      paired_coordinateFace_opposite paired_geometricFace_eq
      paired_unsignedFaceTerm_eq fixed_terms_zero
  active_eq := by
    simpa using hactiveP
  singleton_pieces := rfl
  boundaryTerm_eq_project := by
    intro x hx q _hq
    cases q
    exact hterm x hx

/--
Selected-partition adjacent-face fields as the M8 artificial-face package.
-/
def toM8ArtificialFaceFieldsOfAdjacentFaces
    (P : SelectedBoxPartitionOfUnity I omega)
    (hactiveP : P.active = selectedPartition.active)
    (faceIndices : M -> Finset Face)
    (coordinateFace : M -> Face -> ArtificialCoordinateFace n)
    (geometricFace : M -> Face -> Geometry)
    (unsignedFaceTerm : M -> Face -> Real)
    (boundaryTerm_eq_faceSum :
      forall i, i ∈ P.active ->
        projectInteriorBoundaryIntegral I i i omega (P.lower i) (P.upper i) =
          Finset.sum (faceIndices i) fun f =>
            (coordinateFace i f).sign * unsignedFaceTerm i f)
    (pair : ArtificialFaceIndex M Unit Face -> ArtificialFaceIndex M Unit Face)
    (pair_mem :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair r ∈
            artificialFaceIndexSet P.active
              (fun _ : M => ({()} : Finset Unit))
              (fun i _ => faceIndices i))
    (pair_involutive :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair (pair r) = r)
    (paired_coordinateFace_opposite :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          coordinateFace (pair r).1.1 (pair r).2 =
            (coordinateFace r.1.1 r.2).opposite)
    (paired_geometricFace_eq :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          geometricFace r.1.1 r.2 = geometricFace (pair r).1.1 (pair r).2)
    (paired_unsignedFaceTerm_eq :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) r =
            artificialFaceTerm (fun i _ f => unsignedFaceTerm i f) (pair r))
    (fixed_terms_zero :
      forall r,
        r ∈ artificialFaceIndexSet P.active
            (fun _ : M => ({()} : Finset Unit))
            (fun i _ => faceIndices i) ->
          pair r = r ->
            artificialFaceTerm
              (fun i _ f => (coordinateFace i f).sign * unsignedFaceTerm i f) r = 0)
    (hterm :
      forall x, x ∈ P.active ->
        measureLocalization.interiorBoundaryTerm x () =
          projectInteriorBoundaryIntegral I x x omega (P.lower x) (P.upper x)) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  (P.toM8AdjacentSelectedFaceData (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition) (targetImages := targetImages)
    (measureLocalization := measureLocalization)
    hactiveP faceIndices coordinateFace geometricFace unsignedFaceTerm
    boundaryTerm_eq_faceSum pair pair_mem pair_involutive
    paired_coordinateFace_opposite paired_geometricFace_eq
    paired_unsignedFaceTerm_eq fixed_terms_zero hterm).toM8ArtificialFaceFields

end SelectedBoxPartitionOfUnity

end ArtificialFaceAdjacencyToM8

end Stokes

end
