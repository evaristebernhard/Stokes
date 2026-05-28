import Stokes.Global.CoverIndexedZeroCompactRefinedEndpointAdapter
import Stokes.Global.CoverIndexedZeroCompactRepresentedStokesFromCollar

/-!
# Generated endpoint adapter for collar-indexed refined partitions

This file removes the last artificial endpoint-adapter field from the
collar-facing refined compact-support route when callers accept the canonical
represented integral names:

* represented bulk integral = the refined nested local bulk sum;
* represented boundary integral = the refined nested local boundary sum; and
* boundary partition term = the refined local boundary term.

The generated adapter is intentionally definitional.  A small optional name
bridge is also provided for callers that want to expose external scalar names
while proving they are these generated canonical terms.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CanonicalRefinedEndpoint

universe uH uM uB

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type uB}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece)

/-- Canonical boundary partition term for the generated endpoint adapter. -/
def generatedBoundaryPartitionTerm :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece → Real :=
  D.localBoundaryTerm

/-- Canonical represented bulk integral: the refined nested local bulk sum. -/
def generatedRepresentedBulkIntegral : Real :=
  D.refinedBoundaryNestedSum (I := I) (K := K) D.localBulkTerm

/-- Canonical represented boundary integral: the refined nested local boundary
sum, equivalently the generated boundary-partition sum. -/
def generatedRepresentedBoundaryIntegral : Real :=
  D.refinedBoundaryNestedSum (I := I) (K := K)
    (D.generatedBoundaryPartitionTerm (I := I) (K := K))

/--
Generated refined endpoint adapter for the canonical represented integral
names.  All reconstruction fields are definitional after choosing
`boundaryPartitionTerm := D.localBoundaryTerm`.
-/
def generatedEndpointAdapter :
    D.RefinedEndpointAdapter (I := I) (K := K) where
  boundaryPartitionTerm :=
    D.generatedBoundaryPartitionTerm (I := I) (K := K)
  representedBulkIntegral :=
    D.generatedRepresentedBulkIntegral (I := I) (K := K)
  representedBoundaryIntegral :=
    D.generatedRepresentedBoundaryIntegral (I := I) (K := K)
  representedBulkIntegral_eq_refinedBulkSum := rfl
  localBoundarySum_eq_boundaryPartitionSum := rfl
  representedBoundaryIntegral_eq_boundaryPartitionSum := rfl

@[simp]
theorem generatedEndpointAdapter_boundaryPartitionTerm :
    (D.generatedEndpointAdapter
        (I := I) (K := K)).boundaryPartitionTerm =
      D.generatedBoundaryPartitionTerm (I := I) (K := K) :=
  rfl

@[simp]
theorem generatedEndpointAdapter_representedBulkIntegral :
    (D.generatedEndpointAdapter
        (I := I) (K := K)).representedBulkIntegral =
      D.generatedRepresentedBulkIntegral (I := I) (K := K) :=
  rfl

@[simp]
theorem generatedEndpointAdapter_representedBoundaryIntegral :
    (D.generatedEndpointAdapter
        (I := I) (K := K)).representedBoundaryIntegral =
      D.generatedRepresentedBoundaryIntegral (I := I) (K := K) :=
  rfl

/--
Optional bridge for callers that keep external scalar names but want to use
the generated endpoint adapter.  The only obligations are that those external
names are the generated canonical refined sums.
-/
structure RepresentedIntegralNameBridge where
  externalBulk : Real
  externalBoundary : Real
  externalBulk_eq_generated :
    externalBulk = D.generatedRepresentedBulkIntegral (I := I) (K := K)
  externalBoundary_eq_generated :
    externalBoundary = D.generatedRepresentedBoundaryIntegral (I := I) (K := K)

namespace RepresentedIntegralNameBridge

variable
    {D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece}
    (B : D.RepresentedIntegralNameBridge (I := I) (K := K))

/-- The canonical bridge, using the generated names themselves. -/
def canonical :
    D.RepresentedIntegralNameBridge (I := I) (K := K) where
  externalBulk := D.generatedRepresentedBulkIntegral (I := I) (K := K)
  externalBoundary := D.generatedRepresentedBoundaryIntegral (I := I) (K := K)
  externalBulk_eq_generated := rfl
  externalBoundary_eq_generated := rfl

/-- Convert external names known to be canonical into the refined endpoint
adapter shape consumed by the older theorem. -/
def toEndpointAdapter :
    D.RefinedEndpointAdapter (I := I) (K := K) where
  boundaryPartitionTerm := D.generatedBoundaryPartitionTerm (I := I) (K := K)
  representedBulkIntegral := B.externalBulk
  representedBoundaryIntegral := B.externalBoundary
  representedBulkIntegral_eq_refinedBulkSum := by
    rw [B.externalBulk_eq_generated]
    rfl
  localBoundarySum_eq_boundaryPartitionSum := rfl
  representedBoundaryIntegral_eq_boundaryPartitionSum := by
    rw [B.externalBoundary_eq_generated]
    rfl

@[simp]
theorem toEndpointAdapter_representedBulkIntegral :
    (B.toEndpointAdapter (I := I) (K := K)).representedBulkIntegral =
      B.externalBulk :=
  rfl

@[simp]
theorem toEndpointAdapter_representedBoundaryIntegral :
    (B.toEndpointAdapter (I := I) (K := K)).representedBoundaryIntegral =
      B.externalBoundary :=
  rfl

/-- Local refined Stokes, plus the external-name bridge, proves equality of
the external represented integral names. -/
theorem externalBulk_eq_externalBoundary_of_localSum
    (hlocal :
      (Finset.sum
          (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
          Finset.sum (D.boundaryPieces i) fun q => D.localBulkTerm i q) =
        Finset.sum
          (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
          Finset.sum (D.boundaryPieces i) fun q => D.localBoundaryTerm i q) :
    B.externalBulk = B.externalBoundary := by
  exact
    (B.toEndpointAdapter
      (I := I) (K := K)).representedBulkIntegral_eq_representedBoundaryIntegral_of_localSum
        (I := I) (K := K) hlocal

end RepresentedIntegralNameBridge

end CoverIndexedBoundaryBoxRefinedPartition

end CanonicalRefinedEndpoint

section FromCollarEndpoint

universe uH uM uB uι

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type uB} [DecidableEq BoundaryPiece]
variable {ImageIndex : Type uι} [Fintype ImageIndex]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
Collar-facing refined compact-support represented Stokes input with the
endpoint adapter generated canonically from the refined local sums.

This is the same honest geometric and smoothness package as
`CoverIndexedZeroCompactRepresentedStokesFromCollarInput`, minus the manual
`endpointAdapter` field.
-/
structure CoverIndexedZeroCompactFromCollarEndpointInput where
  /-- Coordinate carrier for each boundary chart index. -/
  coordCarrier :
    CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real)
  /-- Ambient collar/preimage region in the same boundary coordinates. -/
  ambient :
    CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real)
  /-- Compactness of each coordinate carrier. -/
  coordCarrier_isCompact :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C, IsCompact (coordCarrier i)
  /-- The coordinate carriers lie in the closed upper half-space. -/
  coordCarrier_subset_upperHalfSpace :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      coordCarrier i ⊆ upperHalfSpace n
  /-- Collar/prism containment around every carrier point. -/
  collar_prisms :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      ∀ x ∈ coordCarrier i, ∃ eps : Real,
        0 < eps ∧ halfSpaceCollarPrism (n := n) x eps ⊆ ambient i
  /-- Smooth refinement of the original boundary partition into box pieces. -/
  smoothRefinement :
    BoundarySmoothBoxRefinement (I := I) (K := K) C P BoundaryPiece
  /-- The actual box-refined boundary partition consumed by local Stokes. -/
  refinedPartition :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω BoundaryPiece
  /-- Smoothness neighborhood assigned to each refined boundary box. -/
  smoothnessNeighborhood :
    CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece →
      Set (Fin (n + 1) → Real)
  /-- Smoothness fields for refined coefficients and transition-pullback forms. -/
  smoothnessFields :
    CoverIndexedBoundaryBoxRefinedSmoothnessFields
      (I := I) (K := K) refinedPartition smoothnessNeighborhood
  /-- The smoothness neighborhoods are open. -/
  smoothnessNeighborhood_isOpen :
    ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
      ∀ q, q ∈ refinedPartition.boundaryPieces i →
        IsOpen (smoothnessNeighborhood i q)
  /-- Each refined closed source box lies in its smoothness neighborhood. -/
  sourceIcc_subset_smoothnessNeighborhood :
    ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
      ∀ q, q ∈ refinedPartition.boundaryPieces i →
        Icc (refinedPartition.lower i q) (refinedPartition.upper i q) ⊆
          smoothnessNeighborhood i q
  /-- Finite family used to state ambient image control for refined boxes. -/
  imageControlFamily :
    CoverIndexedRefinedBoxImageControlFamily
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      refinedPartition ImageIndex
  /-- Whole-box ambient chart-transition control. -/
  imageControl_mapsTo :
    imageControlFamily.ChartTransitionMapsToField (I := I) (K := K) (C := C)

namespace CoverIndexedZeroCompactFromCollarEndpointInput

variable
    (X :
      CoverIndexedZeroCompactFromCollarEndpointInput
        (I := I) (K := K) (ω := ω) (C := C) (P := P)
        (BoundaryPiece := BoundaryPiece) (ImageIndex := ImageIndex))

/-- Generated endpoint adapter for the packaged refined partition. -/
def endpointAdapter :
    X.refinedPartition.RefinedEndpointAdapter (I := I) (K := K) :=
  X.refinedPartition.generatedEndpointAdapter (I := I) (K := K)

/-- Canonical represented bulk integral selected by this endpoint. -/
def representedBulkIntegral : Real :=
  X.refinedPartition.generatedRepresentedBulkIntegral (I := I) (K := K)

/-- Canonical represented boundary integral selected by this endpoint. -/
def representedBoundaryIntegral : Real :=
  X.refinedPartition.generatedRepresentedBoundaryIntegral (I := I) (K := K)

/-- Reinsert the generated adapter for the older represented from-collar API. -/
def toRepresentedStokesFromCollarInput :
    CoverIndexedZeroCompactRepresentedStokesFromCollarInput
      (I := I) (K := K) (ω := ω) (C := C) (P := P)
      (BoundaryPiece := BoundaryPiece) (ImageIndex := ImageIndex) where
  coordCarrier := X.coordCarrier
  ambient := X.ambient
  coordCarrier_isCompact := X.coordCarrier_isCompact
  coordCarrier_subset_upperHalfSpace := X.coordCarrier_subset_upperHalfSpace
  collar_prisms := X.collar_prisms
  smoothRefinement := X.smoothRefinement
  refinedPartition := X.refinedPartition
  smoothnessNeighborhood := X.smoothnessNeighborhood
  smoothnessFields := X.smoothnessFields
  smoothnessNeighborhood_isOpen := X.smoothnessNeighborhood_isOpen
  sourceIcc_subset_smoothnessNeighborhood :=
    X.sourceIcc_subset_smoothnessNeighborhood
  imageControlFamily := X.imageControlFamily
  imageControl_mapsTo := X.imageControl_mapsTo
  endpointAdapter := X.endpointAdapter (I := I) (K := K)

@[simp]
theorem toRepresentedStokesFromCollarInput_endpointAdapter :
    (X.toRepresentedStokesFromCollarInput
        (I := I) (K := K)).endpointAdapter =
      X.endpointAdapter (I := I) (K := K) :=
  rfl

@[simp]
theorem toRepresentedStokesFromCollarInput_representedBulkIntegral :
    (X.toRepresentedStokesFromCollarInput
        (I := I) (K := K)).representedBulkIntegral (I := I) (K := K) =
      X.representedBulkIntegral (I := I) (K := K) :=
  rfl

@[simp]
theorem toRepresentedStokesFromCollarInput_representedBoundaryIntegral :
    (X.toRepresentedStokesFromCollarInput
        (I := I) (K := K)).representedBoundaryIntegral (I := I) (K := K) =
      X.representedBoundaryIntegral (I := I) (K := K) :=
  rfl

/-- The finite half-space box cover supplied by the collar fields. -/
def finiteHalfSpaceCover :
    CoverIndexedFiniteHalfSpaceBoxCover
      (I := I) (K := K) C X.coordCarrier X.ambient
      (fun _ : CoverIndexedBoundaryIndex (I := I) C => Fin (n + 1) → Real) :=
  (X.toRepresentedStokesFromCollarInput
    (I := I) (K := K)).finiteHalfSpaceCover

/-- Active centers selected by the collar finite cover remain in their carriers. -/
theorem finiteHalfSpaceCover_active_subset
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    ∀ x ∈ (X.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i,
      x ∈ X.coordCarrier i := by
  simpa [finiteHalfSpaceCover] using
    (X.toRepresentedStokesFromCollarInput
      (I := I) (K := K)).finiteHalfSpaceCover_active_subset
        (I := I) (K := K) i

/-- Local refined half-space Stokes for all refined boundary boxes. -/
theorem refinedLocalStokes
    [IsManifold I ⊤ M] :
    (Finset.sum
        (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (X.refinedPartition.boundaryPieces i) fun q =>
          X.refinedPartition.localBulkTerm i q) =
      Finset.sum
        (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (X.refinedPartition.boundaryPieces i) fun q =>
          X.refinedPartition.localBoundaryTerm i q := by
  exact
    (X.toRepresentedStokesFromCollarInput
      (I := I) (K := K)).refinedLocalStokes
        (I := I) (K := K)

/--
Compact-support represented Stokes from collar/refined-box data with canonical
endpoint names.  No manual `RefinedEndpointAdapter` is exposed at this API.
-/
theorem representedStokes
    [IsManifold I ⊤ M] :
    X.representedBulkIntegral (I := I) (K := K) =
      X.representedBoundaryIntegral (I := I) (K := K) := by
  simpa [representedBulkIntegral, representedBoundaryIntegral,
    toRepresentedStokesFromCollarInput, endpointAdapter] using
    (X.toRepresentedStokesFromCollarInput
      (I := I) (K := K)).representedStokes
        (I := I) (K := K)

end CoverIndexedZeroCompactFromCollarEndpointInput

end FromCollarEndpoint

end Stokes

end
