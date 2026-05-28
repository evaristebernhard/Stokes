import Stokes.Global.BulkMeasureCanonicalLocalFacts

/-!
# Compact-support constructor for canonical bulk local terms

`BulkMeasureCanonicalLocalFacts` used to receive
`BulkLocalTermCompactSupportData` as an input.  This file constructs that data
for the canonical scalar bulk terms from the support and smooth-neighborhood
fields already carried by localized interior pieces and boundary source boxes.

The boundary support carrier is the closed source `Icc`, not
`halfSpaceSupportBox`: the latter has strict inequalities in artificial face
directions, so it is not the compact carrier we need for integrability.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section ModelBulkContinuity

/-- The coordinate exterior-derivative scalar is continuous on any subset of an
open set where the model form is smooth. -/
theorem extDerivCoord_continuousOn_of_contDiffOn_isOpen {n : Nat}
    {ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real}
    {U s : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hs : s ⊆ U)
    (hω : ContDiffOn Real ⊤ ω U) :
    ContinuousOn (CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω)) s := by
  change ContinuousOn
    (fun x =>
      ∑ i : Fin (n + 1),
        (-1 : Real) ^ (i : Nat) *
          fderiv Real (CubeStokes.toCoordNForm ω i) x (Pi.single i 1)) s
  apply continuousOn_finset_sum
  intro i _hi
  have hcoeff : ContDiffOn Real ⊤ (CubeStokes.toCoordNForm ω i) U :=
    toCoordNForm_contDiffOn ω hω i
  have hfderiv :
      ContinuousOn (fderiv Real (CubeStokes.toCoordNForm ω i)) U :=
    hcoeff.continuousOn_fderiv_of_isOpen hU (by simp)
  have happly :
      ContinuousOn
        (fun x =>
          fderiv Real (CubeStokes.toCoordNForm ω i) x (Pi.single i 1)) U :=
    (ContinuousLinearMap.apply Real Real (Pi.single i 1)).continuous.comp_continuousOn
      hfderiv
  exact ((continuousOn_const.mul happly).mono hs : _)

/-- The top-degree `extDeriv` scalar is continuous on any subset of an open set
where the model form is smooth. -/
theorem modelBulkIntegrand_continuousOn_of_contDiffOn_isOpen {n : Nat}
    {ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real}
    {U s : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hs : s ⊆ U)
    (hω : ContDiffOn Real ⊤ ω U) :
    ContinuousOn (fun y => extDeriv ω y (standardTopFrame n)) s := by
  have hcoord :
      ContinuousOn (CubeStokes.extDerivCoord (CubeStokes.toCoordNForm ω)) s :=
    extDerivCoord_continuousOn_of_contDiffOn_isOpen hU hs hω
  exact hcoord.congr fun y hy => by
    have hyU : y ∈ U := hs hy
    have hdiff : DifferentiableAt Real ω y :=
      (hω.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
    simpa [standardTopFrame] using
      CubeStokes.extDeriv_topCoeff_eq_extDerivCoord ω y hdiff

universe u w

/-- Manifold-facing continuity of the canonical scalar bulk integrand. -/
theorem bulkIntegrand_continuousOn_of_contDiffOn_isOpen
    {H : Type u} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {U s : Set (Fin (n + 1) → Real)}
    (hU : IsOpen U) (hs : s ⊆ U)
    (hω :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) U) :
    ContinuousOn (bulkIntegrand I x0 x1 ω) s := by
  simpa [bulkIntegrand] using
    modelBulkIntegrand_continuousOn_of_contDiffOn_isOpen
      (ω := ManifoldForm.transitionPullbackInChart I x0 x1 ω) hU hs hω

end ModelBulkContinuity

section SupportCarriers

/-- The half-space support box is contained in its ambient closed coordinate box. -/
theorem halfSpaceSupportBox_subset_Icc {n : Nat}
    (a b : Fin (n + 1) → Real) :
    halfSpaceSupportBox a b ⊆ Set.Icc a b := by
  intro y hy
  rcases hy with ⟨h0lo, h0hi, htan⟩
  constructor
  · intro i
    refine Fin.cases ?_ ?_ i
    · exact h0lo
    · intro j
      exact (htan j).1.le
  · intro i
    refine Fin.cases ?_ ?_ i
    · exact h0hi.le
    · intro j
      exact (htan j).2.le

end SupportCarriers

section CanonicalCompactSupport

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}

namespace LocalizedInteriorPiece

variable {ρ : M → M → Real} {i : M}

/-- The canonical scalar bulk term of a localized interior piece is supported in
its selected closed coordinate box. -/
theorem bulkIntegrand_support_subset_Icc
    (D : LocalizedInteriorPiece I omega ρ i) :
    Function.support (bulkIntegrand I D.sourceChart D.targetChart D.localizedForm) ⊆
      Set.Icc D.lowerCorner D.upperCorner :=
  (bulkIntegrand_support_subset_tsupport
    (I := I) D.sourceChart D.targetChart D.localizedForm).trans
    (by
      simpa [LocalizedInteriorPiece.localizedForm] using
        D.supportControl.localized_tsupport_subset)

/-- Smooth-neighborhood data carried by a localized interior piece makes its
canonical scalar bulk term continuous on the selected closed box. -/
theorem bulkIntegrand_continuousOn_Icc
    (D : LocalizedInteriorPiece I omega ρ i) :
    ContinuousOn (bulkIntegrand I D.sourceChart D.targetChart D.localizedForm)
      (Set.Icc D.lowerCorner D.upperCorner) := by
  rcases D.smoothNeighborhood with ⟨U, hU, hbox, hωU⟩
  exact bulkIntegrand_continuousOn_of_contDiffOn_isOpen
    (I := I) (x0 := D.sourceChart) (x1 := D.targetChart)
    (ω := D.localizedForm) hU hbox hωU

/-- Compact-support integrability data for one localized interior canonical
bulk scalar term. -/
def bulkIntegrandCompactSupportData
    (D : LocalizedInteriorPiece I omega ρ i) :
    CompactSupportIntegrabilityData
      (bulkIntegrand I D.sourceChart D.targetChart D.localizedForm) :=
  CompactSupportIntegrabilityData.of (Set.Icc D.lowerCorner D.upperCorner)
    isCompact_Icc D.bulkIntegrand_continuousOn_Icc
    D.bulkIntegrand_support_subset_Icc

end LocalizedInteriorPiece

namespace BoundaryPieceFamilyInput

/-- The canonical scalar bulk term of a boundary source piece is supported in
the source closed coordinate box. -/
theorem boundaryBulkIntegrand_support_subset_sourceIcc
    (D : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    {x : M} (hx : x ∈ D.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ D.boundaryPieces x) :
    Function.support
        (bulkIntegrand I (D.sourceChart x q) (D.boundarySourceChart x q) omega) ⊆
      Set.Icc (D.sourceLowerCorner x q) (D.sourceUpperCorner x q) :=
  (bulkIntegrand_support_subset_tsupport
    (I := I) (x0 := D.sourceChart x q)
    (x1 := D.boundarySourceChart x q) (ω := omega)).trans
    ((D.sourceSelectedBox hx hq).tsupport_subset.trans
      (halfSpaceSupportBox_subset_Icc
        (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)))

/-- The source extended box makes a boundary source canonical scalar bulk term
continuous on its source closed coordinate box. -/
theorem boundaryBulkIntegrand_continuousOn_sourceIcc
    (D : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    {x : M} (hx : x ∈ D.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ D.boundaryPieces x) :
    ContinuousOn
      (bulkIntegrand I (D.sourceChart x q) (D.boundarySourceChart x q) omega)
      (Set.Icc (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)) := by
  rcases (D.sourceExtendedBox x hx q hq).exists_smooth_nhds with
    ⟨U, hU, hbox, hωU⟩
  exact bulkIntegrand_continuousOn_of_contDiffOn_isOpen
    (I := I) (x0 := D.sourceChart x q)
    (x1 := D.boundarySourceChart x q) (ω := omega) hU hbox hωU

/-- Compact-support integrability data for one boundary source canonical bulk
scalar term. -/
def boundaryBulkIntegrandCompactSupportData
    (D : BoundaryPieceFamilyInput I omega M BoundaryPiece)
    {x : M} (hx : x ∈ D.activeCharts)
    {q : BoundaryPiece} (hq : q ∈ D.boundaryPieces x) :
    CompactSupportIntegrabilityData
      (bulkIntegrand I (D.sourceChart x q) (D.boundarySourceChart x q) omega) :=
  CompactSupportIntegrabilityData.of
    (Set.Icc (D.sourceLowerCorner x q) (D.sourceUpperCorner x q))
    isCompact_Icc (D.boundaryBulkIntegrand_continuousOn_sourceIcc hx hq)
    (D.boundaryBulkIntegrand_support_subset_sourceIcc hx hq)

end BoundaryPieceFamilyInput

variable {P : SelectedBoxPartitionOfUnity I omega}
variable {boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/-- Canonical construction of local compact-support data for selected bulk
measure pieces. -/
def canonicalBulkLocalTermCompactSupportData
    (localized : LocalizedInteriorM8Fields I omega P)
    (boundary : BoundaryPieceFamilyInput I omega M BoundaryPiece) :
    BulkLocalTermCompactSupportData
      (α := Fin (n + 1) → Real)
      localized.localizedInterior boundary
      (selectedPartitionInteriorBulkScalarTerm localized)
      (selectedPartitionBoundaryBulkScalarTerm boundary) where
  interiorSupportSet := fun i =>
    Set.Icc (localized.localizedInterior.piece i).lowerCorner
      (localized.localizedInterior.piece i).upperCorner
  boundarySupportSet := fun x q =>
    Set.Icc (boundary.sourceLowerCorner x q) (boundary.sourceUpperCorner x q)
  interior_isCompact := by
    intro _i _hi
    exact isCompact_Icc
  boundary_isCompact := by
    intro _x _hx _q _hq
    exact isCompact_Icc
  interior_continuousOn := by
    intro i _hi
    simpa [selectedPartitionInteriorBulkScalarTerm] using
      (localized.localizedInterior.piece i).bulkIntegrand_continuousOn_Icc
  boundary_continuousOn := by
    intro x hx q hq
    simpa [selectedPartitionBoundaryBulkScalarTerm] using
      boundary.boundaryBulkIntegrand_continuousOn_sourceIcc hx hq
  interior_support_subset := by
    intro i _hi
    simpa [selectedPartitionInteriorBulkScalarTerm] using
      (localized.localizedInterior.piece i).bulkIntegrand_support_subset_Icc
  boundary_support_subset := by
    intro x hx q hq
    simpa [selectedPartitionBoundaryBulkScalarTerm] using
      boundary.boundaryBulkIntegrand_support_subset_sourceIcc hx hq

namespace SelectedPartitionBulkCanonicalLocalFacts

/-- Constructor of canonical local facts once the boundary active set is aligned
with the selected partition. -/
def ofCanonicalCompactSupport
    (localized : LocalizedInteriorM8Fields I omega P)
    (boundary_active : boundary.activeCharts = P.active) :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := P) (boundary := boundary) localized where
  boundary_active := boundary_active
  compactSupport :=
    canonicalBulkLocalTermCompactSupportData
      (P := P) (localized := localized) boundary

@[simp]
theorem ofCanonicalCompactSupport_boundary_active
    (localized : LocalizedInteriorM8Fields I omega P)
    (boundary_active : boundary.activeCharts = P.active) :
    (ofCanonicalCompactSupport
      (P := P) (boundary := boundary) localized boundary_active).boundary_active =
      boundary_active :=
  rfl

end SelectedPartitionBulkCanonicalLocalFacts

end CanonicalCompactSupport

end Stokes

end
