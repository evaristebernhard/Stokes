import Stokes.Global.CoverIndexedZeroCompactBoundaryCarrierRefinement
import Stokes.Global.CoverIndexedZeroCompactFiniteHalfSpaceCover

/-!
# Finite half-space covers from selected boundary boxes

The collar route is useful when the ambient coordinate region is an arbitrary
preimage/shrink.  For the intrinsic pointwise route, however, every selected
boundary active carrier is already contained in its selected half-space chart
box.  This file packages the direct finite-cover constructor that uses those
selected boxes as the ambient closed-box regions.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section SelectedBoundaryBoxFiniteCover

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}

namespace SupportControlledSelectedPartition

variable (P : SupportControlledSelectedPartition C)

/-- The canonical coordinate ambient region for a selected boundary index:
the closed box already stored in the selected chart-box data. -/
def boundaryAssignedIccAmbient
    (_P : SupportControlledSelectedPartition C)
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    Set (Fin (n + 1) → Real) :=
  Icc (C.boundaryLower i.1) (C.boundaryUpper i.1)

/-- The selected boundary active coordinate carrier has pointwise half-space
box data inside the selected closed coordinate box. -/
theorem boundaryActiveCoordCarrier_pointwise_assignedIcc
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (x : Fin (n + 1) → Real)
    (hx : x ∈ P.boundaryActiveCoordCarrier (I := I) i) :
    ∃ a b : Fin (n + 1) → Real,
      a 0 = 0 ∧ a ≤ b ∧ x ∈ halfSpaceSupportBox a b ∧
        Icc a b ⊆ P.boundaryAssignedIccAmbient (I := I) i := by
  refine ⟨C.boundaryLower i.1, C.boundaryUpper i.1, ?_, ?_, ?_, ?_⟩
  · exact C.boundary_lower_zero i.1 i.2
  · exact C.boundary_le i.1 i.2
  · exact P.boundaryActiveCoordCarrier_subset_halfSpaceSupportBox (I := I) i hx
  · intro y hy
    simpa [boundaryAssignedIccAmbient] using hy

/-- A finite half-space cover generated directly from selected boundary boxes.

This constructor removes the need for public `boundaryAmbient` and
`collar_prisms` fields when the refinement is only meant to live inside the
original selected boundary chart boxes.
-/
def finiteHalfSpaceCoverOfSelectedBoundaryBoxes
    (hK : IsCompact K) :
    CoverIndexedFiniteHalfSpaceBoxCover
      (I := I) (K := K) C
      (P.boundaryActiveCoordCarrier (I := I))
      (P.boundaryAssignedIccAmbient (I := I))
      (fun _ : CoverIndexedBoundaryIndex (I := I) C =>
        Fin (n + 1) → Real) :=
  coverIndexedFiniteHalfSpaceBoxCoverOfPointwise
    (I := I) (K := K) (C := C)
    (P.boundaryActiveCoordCarrier (I := I))
    (P.boundaryAssignedIccAmbient (I := I))
    (fun i =>
      P.isCompact_boundaryActiveCoordCarrier (I := I) hK i)
    (fun i =>
      P.boundaryActiveCoordCarrier_subset_upperHalfSpace (I := I) i)
    (fun i x hx =>
      P.boundaryActiveCoordCarrier_pointwise_assignedIcc
        (I := I) i x hx)

/-- Active centers selected by the intrinsic finite cover remain in the
boundary active coordinate carrier. -/
theorem finiteHalfSpaceCoverOfSelectedBoundaryBoxes_active_subset
    (hK : IsCompact K)
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    ∀ x ∈
      ((P.finiteHalfSpaceCoverOfSelectedBoundaryBoxes
        (I := I) hK).cover i).activePieces,
      x ∈ P.boundaryActiveCoordCarrier (I := I) i := by
  simpa [finiteHalfSpaceCoverOfSelectedBoundaryBoxes] using
    coverIndexedFiniteHalfSpaceBoxCoverOfPointwise_active_subset
      (I := I) (K := K) (C := C)
      (P.boundaryActiveCoordCarrier (I := I))
      (P.boundaryAssignedIccAmbient (I := I))
      (fun i =>
        P.isCompact_boundaryActiveCoordCarrier (I := I) hK i)
      (fun i =>
        P.boundaryActiveCoordCarrier_subset_upperHalfSpace (I := I) i)
      (fun i x hx =>
        P.boundaryActiveCoordCarrier_pointwise_assignedIcc
          (I := I) i x hx)
      i

end SupportControlledSelectedPartition

end SelectedBoundaryBoxFiniteCover

end Stokes

end
