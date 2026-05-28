import Stokes.Global.CoverIndexedZeroCompactRepresentedStokesCompact
import Stokes.Global.CoverIndexedBaseSupportFromGlobal
import Stokes.Global.CoverIndexedRelativeLocalStokes
import Stokes.Global.CoverIndexedOpenInteriorLocalStokes

/-!
# Raw compact-support represented Stokes input

This module starts the theorem-facing compression layer below
`CoverIndexedZeroCompactRepresentedStokesCompactInput`.

The main new point is that the selected smooth partition is no longer a public
input: it is chosen from the selected finite chart cover.  We also expose the
self-chart transition identity used by later self-target image-control
constructors.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section SelfTransition

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}

namespace ManifoldForm

/-- On the target of a chart, the self chart transition is the identity. -/
theorem chartTransition_self_eqOn_target (x : M) :
    EqOn (chartTransition I x x) id (extChartAt I x).target := by
  intro y hy
  change (extChartAt I x) ((extChartAt I x).symm y) = y
  exact (extChartAt I x).right_inv hy

/-- Set-valued preimage form of `chartTransition_self_eqOn_target`. -/
theorem chartTransition_self_preimage_Icc_of_subset_target
    (x : M) {a b : Fin (n + 1) → Real}
    {s : Set (Fin (n + 1) → Real)}
    (hs : s ⊆ (extChartAt I x).target) :
    s ⊆ (chartTransition I x x) ⁻¹' Icc a b ↔ s ⊆ Icc a b := by
  constructor
  · intro h y hy
    have hpre := h hy
    have hself : chartTransition I x x y = y :=
      chartTransition_self_eqOn_target (I := I) x (hs hy)
    simpa [hself] using hpre
  · intro h y hy
    have hmem := h hy
    have hself : chartTransition I x x y = y :=
      chartTransition_self_eqOn_target (I := I) x (hs hy)
    simpa [hself] using hmem

end ManifoldForm

end SelfTransition

section GlobalSupportCarrierConstructor

universe uH uM uPiece

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable
  {coordCarrier ambient :
    CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real)}
variable {Piece : CoverIndexedBoundaryIndex (I := I) C → Type uPiece}

namespace BoundarySmoothBoxRefinement

variable [DecidableEq (SigmaBoundaryPiece (I := I) (K := K) C Piece)]
variable
  (S :
    BoundarySmoothBoxRefinement
      (I := I) (K := K) C P
      (SigmaBoundaryPiece (I := I) (K := K) C Piece))
  (F :
    CoverIndexedFiniteHalfSpaceBoxCover
      (I := I) (K := K) C coordCarrier ambient Piece)

/--
Construct a box-refined boundary partition when finite-cover selection and
local-Stokes support use different coordinate carriers.

The finite cover is selected from `coordCarrier`; the local Stokes theorem is
fed the larger/natural `coordSupport`, usually
`chartCoordinateImage I (C.boundaryChart i) K`.  This removes the false
requirement that the base form's chart support lie in the boundary partition
coefficient's active carrier.
-/
def toRefinedPartitionOfFiniteHalfSpaceCoverWithGlobalSupportCarrier
    (targetChart :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C, Piece i → M)
    (coordSupport :
      CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real))
    (boundaryPieces_eq :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        S.boundaryPieces i = F.sigmaBoundaryPieces i)
    (lower_eq :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        S.lower i ⟨i, q⟩ = F.lowerCorner i q)
    (upper_eq :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        S.upper i ⟨i, q⟩ = F.upperCorner i q)
    (base_tsupport_subset_coordSupport :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (S.sourceChart i ⟨i, q⟩) (targetChart i q) ω) ⊆
          coordSupport i)
    (coordSupport_subset_upperHalfSpace :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        coordSupport i ⊆ upperHalfSpace n)
    (isCompact_coordSupport :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        IsCompact (coordSupport i))
    (ambient_subset_boundaryChartDomain :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        ambient i ⊆
          boundaryChartDomain I (S.sourceChart i ⟨i, q⟩) (targetChart i q))
    (coordSupport_mapsTo_K :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        ∀ y ∈ coordSupport i,
          (extChartAt I (S.sourceChart i ⟨i, q⟩)).symm y ∈ K)
    (coordSupport_subset_sourceTarget :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        coordSupport i ⊆ (extChartAt I (S.sourceChart i ⟨i, q⟩)).target)
    (coordSupport_subset_overlap :
      ∀ i (q : Piece i), q ∈ F.activePieces i →
        coordSupport i ⊆
          ManifoldForm.chartOverlap I (S.sourceChart i ⟨i, q⟩) (targetChart i q)) :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω
      (SigmaBoundaryPiece (I := I) (K := K) C Piece) :=
  CoverIndexedBoundaryBoxRefinedPartition.ofManifoldSupportControl
    (I := I) (K := K) (ω := ω) (C := C) (P := P)
    (BoundaryPiece := SigmaBoundaryPiece (I := I) (K := K) C Piece)
    (boundaryPieces := F.sigmaBoundaryPieces)
    (sourceChart := fun _ q => S.sourceChart q.1 q)
    (targetChart := fun _ q => targetChart q.1 q.2)
    (coefficient := fun _ q => S.coefficient q.1 q)
    (coordSupport := fun _ q => coordSupport q.1)
    (lower := fun _ q => F.lowerCorner q.1 q.2)
    (upper := fun _ q => F.upperCorner q.1 q.2)
    (reconstruct_on_K := by
      intro i x hxK
      calc
        (Finset.sum (F.sigmaBoundaryPieces i)
            (fun q => S.coefficient q.1 q x))
            =
            Finset.sum (F.sigmaBoundaryPieces i)
              (fun q => S.coefficient i q x) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              have howner : q.1 = i := (F.mem_sigmaBoundaryPieces.mp hq).1
              cases howner
              rfl
        _ = P.partition (Sum.inr i) x := by
              simpa [boundaryPieces_eq i] using
                S.reconstruct_on_K i (x := x) hxK)
    (base_tsupport_subset_coordSupport := by
      intro i q hq
      exact
        base_tsupport_subset_coordSupport q.1 q.2
          (F.sigmaBoundaryPieces_active hq))
    (coordSupport_subset_upperHalfSpace := by
      intro i q hq
      exact coordSupport_subset_upperHalfSpace q.1)
    (isCompact_coordSupport := by
      intro i q hq
      exact isCompact_coordSupport q.1)
    (lower_zero := by
      intro i q hq
      exact
        (F.cover q.1).lowerCorner_zero q.2
          (by
            simpa [CoverIndexedFiniteHalfSpaceBoxCover.activePieces] using
              F.sigmaBoundaryPieces_active hq))
    (lower_le_upper := by
      intro i q hq
      exact
        (F.cover q.1).lower_le_upper q.2
          (by
            simpa [CoverIndexedFiniteHalfSpaceBoxCover.activePieces] using
              F.sigmaBoundaryPieces_active hq))
    (Icc_subset_boundaryChartDomain := by
      intro i q hq
      have hactive : q.2 ∈ F.activePieces q.1 :=
        F.sigmaBoundaryPieces_active hq
      have hIcc :
          Icc (F.lowerCorner q.1 q.2) (F.upperCorner q.1 q.2) ⊆
            ambient q.1 :=
        F.Icc_subset_ambient q.1 hactive
      exact hIcc.trans
        (ambient_subset_boundaryChartDomain q.1 q.2 hactive))
    (coordSupport_mapsTo_K := by
      intro i q hq
      exact
        coordSupport_mapsTo_K q.1 q.2
          (F.sigmaBoundaryPieces_active hq))
    (coordSupport_subset_sourceTarget := by
      intro i q hq
      exact
        coordSupport_subset_sourceTarget q.1 q.2
          (F.sigmaBoundaryPieces_active hq))
    (coordSupport_subset_overlap := by
      intro i q hq
      exact
        coordSupport_subset_overlap q.1 q.2
          (F.sigmaBoundaryPieces_active hq))
    (coefficient_tsupport_inter_K_subset_sourceBox := by
      intro i q hq
      exact
        S.coefficient_tsupport_inter_K_subset_finiteHalfSpaceCoverBox F
          boundaryPieces_eq lower_eq upper_eq q.1 q.2
          (F.sigmaBoundaryPieces_active hq))

end BoundarySmoothBoxRefinement

end GlobalSupportCarrierConstructor

section RawSelectedCover

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable [FiniteDimensional Real (Fin (n + 1) → Real)]
variable [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]

/--
Raw data attached to a selected finite chart-cover.  The selected
support-controlled partition is generated from `hK` and
`assignedCoverSet_isOpen`.
-/
structure CoverIndexedZeroCompactRepresentedStokesRawBase
    (C : CompactSupportChartCoverSelection I K) where
  /-- Compact global support carrier. -/
  hK : IsCompact K
  /-- The selected chart-box cover is open on the manifold side. -/
  assignedCoverSet_isOpen :
    ∀ j : C.CoverIndex, IsOpen (C.assignedCoverSet j)
  /-- Chartwise smoothness of the base form. -/
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I ω
  /-- Global manifold-side support control for the form. -/
  support_subset_K : ManifoldForm.support I ω ⊆ K
  /-- Coordinate-side ambient collar/preimage region for each boundary index. -/
  ambient :
    CoverIndexedBoundaryIndex (I := I) C → Set (Fin (n + 1) → Real)
  /-- The coordinate ambient region lies in the self boundary chart domain. -/
  ambient_subset_selfDomain :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      ambient i ⊆ boundaryChartDomain I (C.boundaryChart i.1) (C.boundaryChart i.1)
  /-- The compact support lies in each selected boundary source chart. -/
  K_subset_boundary_source :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      K ⊆ (extChartAt I (C.boundaryChart i.1)).source
  /-- Boundary chart images of the compact support lie in the model half-space. -/
  boundary_chartImage_subset_upperHalfSpace :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      chartCoordinateImage I (C.boundaryChart i.1) K ⊆ upperHalfSpace n
  /-- Self transition representatives are supported in the selected chart target. -/
  boundary_transition_support_subset_target :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      Function.support
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1) ω) ⊆
        (extChartAt I (C.boundaryChart i.1)).target

namespace CoverIndexedZeroCompactRepresentedStokesRawBase

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesRawBase
        (I := I) (K := K) (ω := ω) C)

/-- Canonically choose the support-controlled smooth partition subordinate to
the selected chart cover. -/
def canonicalSelectedPartition :
    SupportControlledSelectedPartition C :=
  Classical.choice
    (nonempty_supportControlledSelectedPartition
      (I := I) (K := K) C X.hK X.assignedCoverSet_isOpen)

/-- Boundary base representative support is generated from global support and
the self-chart target-support field. -/
theorem boundary_base_tsupport_subset_chartCoordinateImage
    (X :
      CoverIndexedZeroCompactRepresentedStokesRawBase
        (I := I) (K := K) (ω := ω) C)
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.boundaryChart i.1) (C.boundaryChart i.1) ω) ⊆
      chartCoordinateImage I (C.boundaryChart i.1) K :=
  CoverIndexedBoundaryCarrierSelection.base_tsupport_subset_chartCoordinateImage_of_globalManifoldSupport
    (I := I) (K := K) (C := C) (omega := ω)
    X.hK X.K_subset_boundary_source
    X.boundary_transition_support_subset_target
    X.support_subset_K i

end CoverIndexedZeroCompactRepresentedStokesRawBase

/--
Raw selected-cover input.  The collar-prism condition is stated over the
canonical selected partition generated by `base`.
-/
structure CoverIndexedZeroCompactRepresentedStokesRawInput
    (C : CompactSupportChartCoverSelection I K) where
  /-- The selected-cover raw base data. -/
  base :
    CoverIndexedZeroCompactRepresentedStokesRawBase
      (I := I) (K := K) (ω := ω) C
  /-- Collar/prism containment around every generated boundary active carrier. -/
  collar_prisms :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      ∀ x ∈
        (CoverIndexedZeroCompactRepresentedStokesRawBase.canonicalSelectedPartition
          (I := I) (K := K) (ω := ω) base).boundaryActiveCoordCarrier (I := I) i,
        ∃ eps : Real,
          0 < eps ∧ halfSpaceCollarPrism (n := n) x eps ⊆ base.ambient i

namespace CoverIndexedZeroCompactRepresentedStokesRawInput

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesRawInput
        (I := I) (K := K) (ω := ω) C)

/-- The canonical selected smooth partition generated by the raw input. -/
def selectedPartition : SupportControlledSelectedPartition C :=
  CoverIndexedZeroCompactRepresentedStokesRawBase.canonicalSelectedPartition
    (I := I) (K := K) (ω := ω) X.base

/-- Collar-generated finite-cover data generated from the raw input. -/
def generatedFromRaw :
    CoverIndexedZeroCompactFromCollarGenerated
      (I := I) (K := K) C (X.selectedPartition (I := I) (K := K) (ω := ω)) where
  hK := X.base.hK
  ambient := X.base.ambient
  collar_prisms := X.collar_prisms

@[simp]
theorem generatedFromRaw_ambient :
    (X.generatedFromRaw
      (I := I) (K := K) (ω := ω)).ambient = X.base.ambient := rfl

/-- The generated finite half-space cover selected from the raw collar data. -/
def finiteHalfSpaceCover :
    CoverIndexedFiniteHalfSpaceBoxCover
      (I := I) (K := K) C
      ((X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).coordCarrier (I := I) (K := K))
      X.base.ambient
      (fun _ : CoverIndexedBoundaryIndex (I := I) C => Fin (n + 1) → Real) :=
  (X.generatedFromRaw
    (I := I) (K := K) (ω := ω)).finiteHalfSpaceCover (I := I) (K := K) (C := C)

/-- The self target chart for every raw generated refined box. -/
def selfTargetChart
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (_q : Fin (n + 1) → Real) : M :=
  C.boundaryChart i.1

/-- The raw ambient field gives closed-box containment in the self boundary
chart domain. -/
theorem ambient_subset_selfDomain_of_active
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : Fin (n + 1) → Real)
    (_hq : q ∈ (X.finiteHalfSpaceCover
      (I := I) (K := K) (ω := ω) (C := C)).activePieces i) :
    X.base.ambient i ⊆
      boundaryChartDomain I
        (C.boundaryChart i.1) (C.boundaryChart i.1) :=
  X.base.ambient_subset_selfDomain i

/-- The coordinate support used for local Stokes in the raw route: the whole
compact support written in the selected boundary chart. -/
def globalCoordSupport
    (_X :
      CoverIndexedZeroCompactRepresentedStokesRawInput
        (I := I) (K := K) (ω := ω) C)
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    Set (Fin (n + 1) → Real) :=
  chartCoordinateImage I (C.boundaryChart i.1) K

/-- Compactness of the raw global coordinate support. -/
theorem isCompact_globalCoordSupport
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    IsCompact (X.globalCoordSupport (I := I) (K := K) (ω := ω) i) := by
  simpa [globalCoordSupport] using
    isCompact_chartCoordinateImage_of_subset_source
      (I := I) (x := C.boundaryChart i.1)
      X.base.hK (X.base.K_subset_boundary_source i)

/-- The raw global coordinate support lies in the closed model half-space. -/
theorem globalCoordSupport_subset_upperHalfSpace
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    X.globalCoordSupport (I := I) (K := K) (ω := ω) i ⊆ upperHalfSpace n := by
  simpa [globalCoordSupport] using
    X.base.boundary_chartImage_subset_upperHalfSpace i

/-- Inverse-chart points of the raw global coordinate support lie back in `K`. -/
theorem globalCoordSupport_mapsTo_K
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    ∀ y ∈ X.globalCoordSupport (I := I) (K := K) (ω := ω) i,
      (extChartAt I (C.boundaryChart i.1)).symm y ∈ K := by
  rintro y ⟨p, hpK, rfl⟩
  rw [(extChartAt I (C.boundaryChart i.1)).left_inv
    (X.base.K_subset_boundary_source i hpK)]
  exact hpK

/-- The raw global coordinate support lies in the source chart target. -/
theorem globalCoordSupport_subset_sourceTarget
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    X.globalCoordSupport (I := I) (K := K) (ω := ω) i ⊆
      (extChartAt I (C.boundaryChart i.1)).target := by
  simpa [globalCoordSupport] using
    chartCoordinateImage_subset_target
      (I := I) (x := C.boundaryChart i.1)
      (K := K) (X.base.K_subset_boundary_source i)

/-- The raw global coordinate support lies in the self chart overlap. -/
theorem globalCoordSupport_subset_selfOverlap
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    X.globalCoordSupport (I := I) (K := K) (ω := ω) i ⊆
      ManifoldForm.chartOverlap I (C.boundaryChart i.1) (C.boundaryChart i.1) :=
  ManifoldForm.subset_chartOverlap_self_of_subset_target
    (I := I) (x := C.boundaryChart i.1)
    (X.globalCoordSupport_subset_sourceTarget (I := I) (K := K) (ω := ω) i)

/-- Smooth box refinement generated from a manifold-side open lift of the raw
finite half-space cover. -/
def smoothRefinementFromAmbientOpenData
    (A :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
          (I := I) (K := K) (C := C)
          (P := X.selectedPartition (I := I) (K := K) (ω := ω))) :
    BoundarySmoothBoxRefinement
      (I := I) (K := K) C
      (X.selectedPartition (I := I) (K := K) (ω := ω))
      ((X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).BoundaryPiece (I := I) (K := K)) :=
  (X.generatedFromRaw
    (I := I) (K := K) (ω := ω)).smoothRefinementOfFiniteOpenCover
      (I := I) (K := K) A

/--
Raw refined partition generated from a manifold-side open lift, using
`chartCoordinateImage K` as the local-Stokes coordinate support.
-/
def refinedPartitionWithGlobalSupportCarrier
    (A :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
          (I := I) (K := K) (C := C)
          (P := X.selectedPartition (I := I) (K := K) (ω := ω))) :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C
      (X.selectedPartition (I := I) (K := K) (ω := ω)) ω
      ((X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).BoundaryPiece (I := I) (K := K)) := by
  classical
  let G := X.generatedFromRaw (I := I) (K := K) (ω := ω)
  letI : DecidableEq (G.BoundaryPiece (I := I) (K := K)) :=
    G.instDecidableEqBoundaryPiece (I := I) (K := K)
  let S := X.smoothRefinementFromAmbientOpenData
    (I := I) (K := K) (ω := ω) A
  let F := G.finiteHalfSpaceCover (I := I) (K := K) (C := C)
  exact
    S.toRefinedPartitionOfFiniteHalfSpaceCoverWithGlobalSupportCarrier
      (I := I) (K := K) (ω := ω)
      F
      (fun i _q => C.boundaryChart i.1)
      (fun i => X.globalCoordSupport (I := I) (K := K) (ω := ω) i)
      (by intro i; rfl)
      (by intro i q hq; rfl)
      (by intro i q hq; rfl)
      (by
        intro i q hq
        simpa [G, S, CoverIndexedZeroCompactFromCollarGenerated.sourceChart]
          using
            CoverIndexedZeroCompactRepresentedStokesRawBase.boundary_base_tsupport_subset_chartCoordinateImage
              (I := I) (K := K) (ω := ω) (C := C) X.base i)
      (by
        intro i
        exact X.globalCoordSupport_subset_upperHalfSpace
          (I := I) (K := K) (ω := ω) i)
      (by
        intro i
        exact X.isCompact_globalCoordSupport
          (I := I) (K := K) (ω := ω) i)
      (by
        intro i q hq
        simpa [G, S, CoverIndexedZeroCompactFromCollarGenerated.sourceChart]
          using X.base.ambient_subset_selfDomain i)
      (by
        intro i q hq
        simpa [G, S, CoverIndexedZeroCompactFromCollarGenerated.sourceChart]
          using X.globalCoordSupport_mapsTo_K
            (I := I) (K := K) (ω := ω) i)
      (by
        intro i q hq
        simpa [G, S, CoverIndexedZeroCompactFromCollarGenerated.sourceChart]
          using X.globalCoordSupport_subset_sourceTarget
            (I := I) (K := K) (ω := ω) i)
      (by
        intro i q hq
        simpa [G, S, CoverIndexedZeroCompactFromCollarGenerated.sourceChart]
          using X.globalCoordSupport_subset_selfOverlap
            (I := I) (K := K) (ω := ω) i)

@[simp]
theorem refinedPartitionWithGlobalSupportCarrier_boundaryPieces
    (A :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
          (I := I) (K := K) (C := C)
          (P := X.selectedPartition (I := I) (K := K) (ω := ω)))
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    (X.refinedPartitionWithGlobalSupportCarrier
      (I := I) (K := K) (ω := ω) A).boundaryPieces i =
      ((X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).finiteHalfSpaceCover
          (I := I) (K := K) (C := C)).sigmaBoundaryPieces i := by
  rfl

/-- Canonical represented bulk integral for the raw generated partition. -/
def representedBulkIntegral
    (A :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
          (I := I) (K := K) (C := C)
          (P := X.selectedPartition (I := I) (K := K) (ω := ω))) :
    Real :=
  (X.refinedPartitionWithGlobalSupportCarrier
    (I := I) (K := K) (ω := ω) A).generatedRepresentedBulkIntegral
      (I := I) (K := K)

/-- Canonical represented boundary integral for the raw generated partition. -/
def representedBoundaryIntegral
    (A :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
          (I := I) (K := K) (C := C)
          (P := X.selectedPartition (I := I) (K := K) (ω := ω))) :
    Real :=
  (X.refinedPartitionWithGlobalSupportCarrier
    (I := I) (K := K) (ω := ω) A).generatedRepresentedBoundaryIntegral
      (I := I) (K := K)

/--
Raw represented Stokes after supplying the remaining genuine open-neighborhood
lift.

This theorem already generates the selected partition, collar finite cover,
smooth refinement, refined partition, global-support carrier bridge, and
canonical endpoint internally.  The explicit `A` and `U` parameters are the
current honest boundary obstruction: in a manifold-with-boundary chart, the
extended chart target is generally only relatively open, so an ambient-open
smoothness neighborhood cannot be manufactured from the target alone.
-/
theorem representedStokes
    (A :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
          (I := I) (K := K) (C := C)
          (P := X.selectedPartition (I := I) (K := K) (ω := ω)))
    (U :
      CoverIndexedBoundaryIndex (I := I) C →
        (X.generatedFromRaw
          (I := I) (K := K) (ω := ω)).BoundaryPiece (I := I) (K := K) →
          Set (Fin (n + 1) → Real))
    (hUopen :
      ∀ i,
        i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
          ∀ q,
            q ∈ (X.refinedPartitionWithGlobalSupportCarrier
              (I := I) (K := K) (ω := ω) A).boundaryPieces i →
              IsOpen (U i q))
    (hUbox :
      ∀ i,
        i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
          ∀ q,
            q ∈ (X.refinedPartitionWithGlobalSupportCarrier
              (I := I) (K := K) (ω := ω) A).boundaryPieces i →
              Icc
                  ((X.refinedPartitionWithGlobalSupportCarrier
                    (I := I) (K := K) (ω := ω) A).lower i q)
                  ((X.refinedPartitionWithGlobalSupportCarrier
                    (I := I) (K := K) (ω := ω) A).upper i q) ⊆
                U i q)
    (hUtarget :
      ∀ i q,
        q ∈ (X.refinedPartitionWithGlobalSupportCarrier
          (I := I) (K := K) (ω := ω) A).boundaryPieces i →
          U i q ⊆
            (extChartAt I
              ((X.refinedPartitionWithGlobalSupportCarrier
                (I := I) (K := K) (ω := ω) A).sourceChart i q)).target) :
    X.representedBulkIntegral (I := I) (K := K) (ω := ω) A =
      X.representedBoundaryIntegral (I := I) (K := K) (ω := ω) A := by
  classical
  let D := X.refinedPartitionWithGlobalSupportCarrier
    (I := I) (K := K) (ω := ω) A
  let S := X.smoothRefinementFromAmbientOpenData
    (I := I) (K := K) (ω := ω) A
  have hlocal :
      (Finset.sum
          (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
          Finset.sum (D.boundaryPieces i) fun q => D.localBulkTerm i q) =
        Finset.sum
          (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
          Finset.sum (D.boundaryPieces i) fun q => D.localBoundaryTerm i q := by
    refine
      D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_contDiffOn_infty
        (I := I) (K := K) (ω := ω) (U := U)
        ?_ ?_ ?_ ?_
    · simpa [D] using hUopen
    · simpa [D] using hUbox
    · intro i hi q hq
      have hqS : q ∈ S.boundaryPieces i := by
        simpa [D, S, refinedPartitionWithGlobalSupportCarrier]
          using hq
      have howner : q ∈ S.boundaryPieces q.1 := by
        let F := (X.generatedFromRaw
          (I := I) (K := K) (ω := ω)).finiteHalfSpaceCover
            (I := I) (K := K) (C := C)
        have hqF : q ∈ F.sigmaBoundaryPieces i := by
          simpa [D, F]
            using hq
        have hiq : q.1 = i := (F.mem_sigmaBoundaryPieces.mp hqF).1
        simpa [hiq] using hqS
      have hcoeff :
          ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
            (ManifoldForm.coefficientInChart I (D.sourceChart i q)
              (S.coefficient q.1 q)) (U i q) := by
        exact
          S.contDiffOn_infty_coefficientInChart
            (I := I) q.1 howner (D.sourceChart i q)
            (by
              simpa [D] using hUtarget i q hq)
      have hcoeffD :
          ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
            (ManifoldForm.coefficientInChart I (D.sourceChart i q)
              (D.coefficient i q)) (U i q) := by
        simpa [D, refinedPartitionWithGlobalSupportCarrier] using hcoeff
      exact
        ManifoldForm.contDiffOn_infty_transitionCoefficientInChart_of_coefficientInChart
          (I := I) hcoeffD
          (ManifoldForm.subset_chartOverlap_self_of_subset_target
            (I := I) (x := D.sourceChart i q)
            (by simpa [D] using hUtarget i q hq))
    · intro i hi q hq
      exact
        ManifoldForm.contDiffOn_infty_transitionPullbackInChart_of_chartwiseSmooth_refined
          (I := I) (ω := ω)
          X.base.chartwiseSmooth
          (by simpa [D] using hUtarget i q hq)
          (ManifoldForm.subset_chartOverlap_self_of_subset_target
            (I := I) (x := D.sourceChart i q)
            (by simpa [D] using hUtarget i q hq))
  simpa [representedBulkIntegral, representedBoundaryIntegral, D,
    CoverIndexedBoundaryBoxRefinedPartition.generatedRepresentedBulkIntegral,
    CoverIndexedBoundaryBoxRefinedPartition.generatedRepresentedBoundaryIntegral,
    CoverIndexedBoundaryBoxRefinedPartition.generatedBoundaryPartitionTerm]
    using hlocal

/--
Raw represented Stokes from per-box interior Stokes fields.

This is the boundary-compatible entry point for the raw generated theorem: it
does not ask for an ambient-open smoothness neighborhood `U`, nor for
`U ⊆ (extChartAt I _).target`.  The remaining analytic input is the exact
interior-box certificate for each generated localized representative.
-/
theorem representedStokes_relative
    (A :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
          (I := I) (K := K) (C := C)
          (P := X.selectedPartition (I := I) (K := K) (ω := ω)))
    (hfields :
      let D := X.refinedPartitionWithGlobalSupportCarrier
        (I := I) (K := K) (ω := ω) A
      ∀ i,
        i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
          ∀ q,
            q ∈ D.boundaryPieces i →
              HalfSpaceBoxInteriorStokesFields
                (ManifoldForm.transitionPullbackInChart I
                  (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
                (D.lower i q) (D.upper i q)) :
    X.representedBulkIntegral (I := I) (K := K) (ω := ω) A =
      X.representedBoundaryIntegral (I := I) (K := K) (ω := ω) A := by
  classical
  let D := X.refinedPartitionWithGlobalSupportCarrier
    (I := I) (K := K) (ω := ω) A
  have hfieldsD :
      ∀ i,
        i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
          ∀ q,
            q ∈ D.boundaryPieces i →
              HalfSpaceBoxInteriorStokesFields
                (ManifoldForm.transitionPullbackInChart I
                  (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
                (D.lower i q) (D.upper i q) := by
    simpa [D] using hfields
  have hlocal :
      (Finset.sum
          (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
          Finset.sum (D.boundaryPieces i) fun q => D.localBulkTerm i q) =
        Finset.sum
          (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
          Finset.sum (D.boundaryPieces i) fun q => D.localBoundaryTerm i q :=
    D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_interiorFields hfieldsD
  simpa [representedBulkIntegral, representedBoundaryIntegral, D,
    CoverIndexedBoundaryBoxRefinedPartition.generatedRepresentedBulkIntegral,
    CoverIndexedBoundaryBoxRefinedPartition.generatedRepresentedBoundaryIntegral,
    CoverIndexedBoundaryBoxRefinedPartition.generatedBoundaryPartitionTerm]
    using hlocal

/--
Raw represented Stokes from per-box open-interior smoothness packages.

Compared with `representedStokes_relative`, callers no longer provide the
bottom-level Euclidean `HalfSpaceBoxInteriorStokesFields`.  Each refined box is
allowed to prove smoothness only on an ambient-open neighborhood of its
coordinate open box; closed-box continuity and divergence integrability remain
the honest analytic fields of `HalfSpaceBoxOpenInteriorSmoothnessFields`.
-/
theorem representedStokes_openInteriorSmoothness
    (A :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
          (I := I) (K := K) (C := C)
          (P := X.selectedPartition (I := I) (K := K) (ω := ω)))
    (hfields :
      let D := X.refinedPartitionWithGlobalSupportCarrier
        (I := I) (K := K) (ω := ω) A
      ∀ i,
        i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
          ∀ q,
            q ∈ D.boundaryPieces i →
              HalfSpaceBoxOpenInteriorSmoothnessFields
                (ManifoldForm.transitionPullbackInChart I
                  (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
                (D.lower i q) (D.upper i q)) :
    X.representedBulkIntegral (I := I) (K := K) (ω := ω) A =
      X.representedBoundaryIntegral (I := I) (K := K) (ω := ω) A := by
  classical
  let D := X.refinedPartitionWithGlobalSupportCarrier
    (I := I) (K := K) (ω := ω) A
  have hfieldsD :
      ∀ i,
        i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
          ∀ q,
            q ∈ D.boundaryPieces i →
              HalfSpaceBoxOpenInteriorSmoothnessFields
                (ManifoldForm.transitionPullbackInChart I
                  (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
                (D.lower i q) (D.upper i q) := by
    simpa [D] using hfields
  have hlocal :
      (Finset.sum
          (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
          Finset.sum (D.boundaryPieces i) fun q => D.localBulkTerm i q) =
        Finset.sum
          (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
          Finset.sum (D.boundaryPieces i) fun q => D.localBoundaryTerm i q :=
    D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_openInteriorSmoothness hfieldsD
  simpa [representedBulkIntegral, representedBoundaryIntegral, D,
    CoverIndexedBoundaryBoxRefinedPartition.generatedRepresentedBulkIntegral,
    CoverIndexedBoundaryBoxRefinedPartition.generatedRepresentedBoundaryIntegral,
    CoverIndexedBoundaryBoxRefinedPartition.generatedBoundaryPartitionTerm]
    using hlocal

end CoverIndexedZeroCompactRepresentedStokesRawInput

end RawSelectedCover

end Stokes

end
