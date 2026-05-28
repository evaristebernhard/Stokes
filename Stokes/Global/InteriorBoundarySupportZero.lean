import Stokes.BoundaryChart.BoundaryBoxSelection
import Stokes.Global.ArtificialFaceSelection
import Stokes.Global.CoefficientBoxSupport

/-!
# Interior boundary support-zero wrappers

This file packages the compact-support situation where an interior chart
representative is supported strictly inside its auxiliary coordinate box.  In
that case every box face is artificial, so the project-local boundary term is
zero.  For boundary charts, the analogous non-true-face statement is already
proved by the half-space support-box API; this file exposes the matching global
wrappers without changing the existing boundary layer.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section InteriorSupportBox

/--
The strict interior of an auxiliary coordinate box.

An interior chart piece has no true boundary face.  Support contained in this
set is separated from every coordinate face of the selected box.
-/
def boxInteriorSupportBox {n : Nat} (a b : Fin (n + 1) → Real) :
    Set (Fin (n + 1) → Real) :=
  {y | ∀ i : Fin (n + 1), a i < y i ∧ y i < b i}

/--
All coordinate face coefficients of a form have topological support strictly
inside the selected coordinate box.
-/
def boxFaceCoeffTSupportInInteriorBox {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) : Prop :=
  ∀ i : Fin (n + 1), tsupport (boxFormFaceCoeff ω i) ⊆ boxInteriorSupportBox a b

/--
Evaluating on coordinate face frames preserves strict interior support.
-/
theorem boxFaceCoeffTSupportInInteriorBox_of_tsupport_subset {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hsupp : tsupport ω ⊆ boxInteriorSupportBox a b) :
    boxFaceCoeffTSupportInInteriorBox ω a b := by
  intro i
  exact (boxFormFaceCoeff_tsupport_subset ω i).trans hsupp

/-- Upper face integrals vanish from topological-support disjointness. -/
theorem boxUpperFormFaceIntegral_eq_zero_of_tsupport_disjoint {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real)
    (h : Disjoint (boxUpperFaceSet i a b) (tsupport (boxFormFaceCoeff ω i))) :
    boxUpperFormFaceIntegral ω i a b = 0 :=
  boxUpperFormFaceIntegral_eq_zero_of_support_disjoint ω i a b
    (h.mono_right (subset_tsupport (boxFormFaceCoeff ω i)))

/-- Lower face integrals vanish from topological-support disjointness. -/
theorem boxLowerFormFaceIntegral_eq_zero_of_tsupport_disjoint {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (i : Fin (n + 1)) (a b : Fin (n + 1) → Real)
    (h : Disjoint (boxLowerFaceSet i a b) (tsupport (boxFormFaceCoeff ω i))) :
    boxLowerFormFaceIntegral ω i a b = 0 :=
  boxLowerFormFaceIntegral_eq_zero_of_support_disjoint ω i a b
    (h.mono_right (subset_tsupport (boxFormFaceCoeff ω i)))

/--
Strict interior support is disjoint from every upper and lower coordinate face.
-/
theorem boxBoundaryFaces_tsupport_disjoint_of_subset_interiorBox {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hsupp : boxFaceCoeffTSupportInInteriorBox ω a b) :
    ∀ i : Fin (n + 1),
      Disjoint (boxUpperFaceSet i a b) (tsupport (boxFormFaceCoeff ω i)) ∧
        Disjoint (boxLowerFaceSet i a b) (tsupport (boxFormFaceCoeff ω i)) := by
  intro i
  constructor
  · rw [disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    have hlt : (boxFaceMap i (b i) x) i < b i := ((hsupp i) hy i).2
    unfold boxFaceMap at hlt
    rw [Fin.insertNth_apply_same] at hlt
    exact (lt_irrefl (b i)) hlt
  · rw [disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    have hlt : a i < (boxFaceMap i (a i) x) i := ((hsupp i) hy i).1
    unfold boxFaceMap at hlt
    rw [Fin.insertNth_apply_same] at hlt
    exact (lt_irrefl (a i)) hlt

/--
Data package for the common support-separation proof that every face term of
an interior chart box is zero.
-/
structure FaceTermZeroOnSupportData {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real) where
  /-- Every face coefficient is supported strictly inside the box. -/
  faceCoeff_tsupport_subset : boxFaceCoeffTSupportInInteriorBox ω a b

namespace FaceTermZeroOnSupportData

variable {n : Nat}
variable {ω : (Fin (n + 1) → Real) →
  (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real}
variable {a b : Fin (n + 1) → Real}

/-- Constructor from a support bound for the whole form. -/
def of_tsupport_subset (hsupp : tsupport ω ⊆ boxInteriorSupportBox a b) :
    FaceTermZeroOnSupportData ω a b where
  faceCoeff_tsupport_subset :=
    boxFaceCoeffTSupportInInteriorBox_of_tsupport_subset ω a b hsupp

/-- The recorded support predicate. -/
theorem faceCoeffTSupportInInteriorBox (D : FaceTermZeroOnSupportData ω a b) :
    boxFaceCoeffTSupportInInteriorBox ω a b :=
  D.faceCoeff_tsupport_subset

/-- Every upper and lower box face is disjoint from the relevant coefficient support. -/
theorem boundaryFaces_tsupport_disjoint (D : FaceTermZeroOnSupportData ω a b) :
    ∀ i : Fin (n + 1),
      Disjoint (boxUpperFaceSet i a b) (tsupport (boxFormFaceCoeff ω i)) ∧
        Disjoint (boxLowerFaceSet i a b) (tsupport (boxFormFaceCoeff ω i)) :=
  boxBoundaryFaces_tsupport_disjoint_of_subset_interiorBox ω a b
    D.faceCoeff_tsupport_subset

/-- The upper face integral in any coordinate direction is zero. -/
theorem upperFormFaceIntegral_eq_zero
    (D : FaceTermZeroOnSupportData ω a b) (i : Fin (n + 1)) :
    boxUpperFormFaceIntegral ω i a b = 0 :=
  boxUpperFormFaceIntegral_eq_zero_of_tsupport_disjoint ω i a b
    (D.boundaryFaces_tsupport_disjoint i).1

/-- The lower face integral in any coordinate direction is zero. -/
theorem lowerFormFaceIntegral_eq_zero
    (D : FaceTermZeroOnSupportData ω a b) (i : Fin (n + 1)) :
    boxLowerFormFaceIntegral ω i a b = 0 :=
  boxLowerFormFaceIntegral_eq_zero_of_tsupport_disjoint ω i a b
    (D.boundaryFaces_tsupport_disjoint i).2

/-- The half-space-style remainder vanishes as a special case. -/
theorem boxRemainingFormFaceTerms_eq_zero
    (D : FaceTermZeroOnSupportData ω a b) :
    boxRemainingFormFaceTerms ω a b = 0 := by
  refine boxRemainingFormFaceTerms_eq_zero_of_tsupport_disjoint ω a b ?_ ?_
  · exact (D.boundaryFaces_tsupport_disjoint (0 : Fin (n + 1))).1
  · intro i
    exact ⟨(D.boundaryFaces_tsupport_disjoint i.succ).1,
      (D.boundaryFaces_tsupport_disjoint i.succ).2⟩

/-- The lower zero coordinate face term also vanishes for an interior box. -/
theorem boxLowerZeroCoordFaceTerm_toCoordNForm_eq_zero
    (D : FaceTermZeroOnSupportData ω a b) :
    boxLowerZeroCoordFaceTerm (CubeStokes.toCoordNForm ω) a b = 0 := by
  unfold boxLowerZeroCoordFaceTerm
  rw [boxLowerCoordFaceTerm_toCoordNForm]
  rw [D.lowerFormFaceIntegral_eq_zero (0 : Fin (n + 1))]
  simp

/-- The coordinate remainder vanishes for the corresponding coordinate form. -/
theorem boxRemainingCoordFaceTerms_toCoordNForm_eq_zero
    (D : FaceTermZeroOnSupportData ω a b) :
    boxRemainingCoordFaceTerms (CubeStokes.toCoordNForm ω) a b = 0 := by
  rw [boxRemainingCoordFaceTerms_toCoordNForm]
  exact D.boxRemainingFormFaceTerms_eq_zero

/-- The full coordinate box boundary integral vanishes. -/
theorem bdryIntegral_toCoordNForm_eq_zero
    (D : FaceTermZeroOnSupportData ω a b) :
    CubeStokes.bdryIntegral (CubeStokes.toCoordNForm ω) a b = 0 := by
  rw [bdryIntegral_eq_lowerZero_add_remaining]
  rw [D.boxLowerZeroCoordFaceTerm_toCoordNForm_eq_zero,
    D.boxRemainingCoordFaceTerms_toCoordNForm_eq_zero]
  simp

end FaceTermZeroOnSupportData

/-- The full coordinate boundary integral vanishes from strict interior support. -/
theorem bdryIntegral_toCoordNForm_eq_zero_of_tsupport_subset_interiorBox {n : Nat}
    (ω : (Fin (n + 1) → Real) →
      (Fin (n + 1) → Real) [⋀^Fin n]→L[Real] Real)
    (a b : Fin (n + 1) → Real)
    (hsupp : tsupport ω ⊆ boxInteriorSupportBox a b) :
    CubeStokes.bdryIntegral (CubeStokes.toCoordNForm ω) a b = 0 :=
  (FaceTermZeroOnSupportData.of_tsupport_subset
    (ω := ω) (a := a) (b := b) hsupp).bdryIntegral_toCoordNForm_eq_zero

/-!
The next lemmas are the compact-support source of strict interior boxes.  They
are deliberately pure coordinate facts: chart-domain containment and local
smoothness neighborhoods remain separate hypotheses in later local Stokes
wrappers.
-/

/-- Every compact coordinate set fits in the strict interior of some box. -/
theorem exists_boxInteriorSupportBox_of_isCompact {n : Nat}
    {K : Set (Fin (n + 1) → Real)} (hK : IsCompact K) :
    ∃ a b : Fin (n + 1) → Real, a ≤ b ∧ K ⊆ boxInteriorSupportBox a b := by
  obtain ⟨R, _hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  let a : Fin (n + 1) → Real := fun _ => -(R + 1)
  let b : Fin (n + 1) → Real := fun _ => R + 1
  refine ⟨a, b, ?_, ?_⟩
  · intro i
    dsimp [a, b]
    linarith
  · intro x hx i
    have hxnorm : ‖x‖ ≤ R := hR x hx
    have hcoord_abs : |x i| ≤ R := by
      simpa [Real.norm_eq_abs] using
        (piReal_coord_norm_le_norm x i).trans hxnorm
    have hcoord_le : x i ≤ R := (le_abs_self (x i)).trans hcoord_abs
    have hcoord_ge : -R ≤ x i := (neg_le_neg hcoord_abs).trans (neg_abs_le (x i))
    constructor
    · dsimp [a]
      linarith
    · dsimp [b]
      linarith

/-- A compact topological support fits in the strict interior of some box. -/
theorem exists_boxInteriorSupportBox_of_compact_tsupport {n : Nat}
    {β : Type*} [Zero β]
    (ω : (Fin (n + 1) → Real) → β)
    (hω : IsCompact (tsupport ω)) :
    ∃ a b : Fin (n + 1) → Real,
      a ≤ b ∧ tsupport ω ⊆ boxInteriorSupportBox a b :=
  exists_boxInteriorSupportBox_of_isCompact hω

/--
If the topological support is contained in a compact coordinate set, then it
fits in the strict interior of some box.
-/
theorem exists_boxInteriorSupportBox_of_tsupport_subset_compact {n : Nat}
    {β : Type*} [Zero β]
    (ω : (Fin (n + 1) → Real) → β)
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K) (hsupp : tsupport ω ⊆ K) :
    ∃ a b : Fin (n + 1) → Real,
      a ≤ b ∧ tsupport ω ⊆ boxInteriorSupportBox a b := by
  obtain ⟨a, b, hle, hKbox⟩ := exists_boxInteriorSupportBox_of_isCompact hK
  exact ⟨a, b, hle, hsupp.trans hKbox⟩

end InteriorSupportBox

section InteriorChartWrappers

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- Face coefficient support predicate for an interior transition-pullback representative. -/
def interiorTransitionFaceCoeffTSupportInInteriorBox {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real) : Prop :=
  boxFaceCoeffTSupportInInteriorBox
    (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b

/--
Strict support of the transition-pullback representative inside the box gives
strict support for all face coefficients.
-/
theorem interiorTransitionFaceCoeffTSupportInInteriorBox_of_tsupport_subset {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      boxInteriorSupportBox a b) :
    interiorTransitionFaceCoeffTSupportInInteriorBox I x0 x1 ω a b :=
  boxFaceCoeffTSupportInInteriorBox_of_tsupport_subset
    (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b hsupp

/-- Support-zero data for an interior transition-pullback representative. -/
def interiorFaceTermZeroOnSupportData_of_tsupport_subset {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      boxInteriorSupportBox a b) :
    FaceTermZeroOnSupportData
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b :=
  FaceTermZeroOnSupportData.of_tsupport_subset hsupp

/--
If an interior chart representative is supported strictly inside its auxiliary
box, its project-local artificial boundary term is zero.
-/
theorem projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
    {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      boxInteriorSupportBox a b) :
    projectInteriorBoundaryIntegral I x0 x1 ω a b = 0 := by
  simpa [projectInteriorBoundaryIntegral] using
    bdryIntegral_toCoordNForm_eq_zero_of_tsupport_subset_interiorBox
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) a b hsupp

/--
If an interior chart representative is supported strictly inside an extended
coordinate box, then its project-local bulk integral also vanishes.
-/
theorem projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox
    {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (a b : Fin (n + 1) → Real)
    (hbox : interiorChartExtendedBox I x0 x1 ω a b)
    (hsupp : tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
      boxInteriorSupportBox a b) :
    projectInteriorBulkIntegral I x0 x1 ω a b = 0 := by
  calc
    projectInteriorBulkIntegral I x0 x1 ω a b =
        projectInteriorBoundaryIntegral I x0 x1 ω a b :=
      projectInteriorLocalStokes_of_extendedBox I x0 x1 ω a b hbox
    _ = 0 :=
      projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
        I x0 x1 ω a b hsupp

/--
Compact support of an interior transition-pullback representative automatically
selects a strict interior box whose project-local boundary integral vanishes.
-/
theorem exists_projectInteriorBoundaryIntegral_eq_zero_of_compact_tsupport
    {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (hcompact :
      IsCompact (tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω))) :
    ∃ a b : Fin (n + 1) → Real,
      a ≤ b ∧
        tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
          boxInteriorSupportBox a b ∧
        projectInteriorBoundaryIntegral I x0 x1 ω a b = 0 := by
  obtain ⟨a, b, hle, hsupp⟩ :=
    exists_boxInteriorSupportBox_of_compact_tsupport
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) hcompact
  exact ⟨a, b, hle, hsupp,
    projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
      I x0 x1 ω a b hsupp⟩

/--
Compact support selects a strict interior box, and any supplied extended-box
geometry for that selected box turns local Stokes into a zero bulk integral.
-/
theorem exists_projectInteriorBulkIntegral_eq_zero_of_compact_tsupport
    {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    (hcompact :
      IsCompact (tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω)))
    (hbox :
      ∀ a b : Fin (n + 1) → Real,
        a ≤ b →
          tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
            boxInteriorSupportBox a b →
          interiorChartExtendedBox I x0 x1 ω a b) :
    ∃ a b : Fin (n + 1) → Real,
      a ≤ b ∧
        tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
          boxInteriorSupportBox a b ∧
        interiorChartExtendedBox I x0 x1 ω a b ∧
        projectInteriorBoundaryIntegral I x0 x1 ω a b = 0 ∧
        projectInteriorBulkIntegral I x0 x1 ω a b = 0 := by
  obtain ⟨a, b, hle, hsupp, hboundary⟩ :=
    exists_projectInteriorBoundaryIntegral_eq_zero_of_compact_tsupport
      I x0 x1 ω hcompact
  have hbox' : interiorChartExtendedBox I x0 x1 ω a b :=
    hbox a b hle hsupp
  have hbulk : projectInteriorBulkIntegral I x0 x1 ω a b = 0 := by
    calc
      projectInteriorBulkIntegral I x0 x1 ω a b =
          projectInteriorBoundaryIntegral I x0 x1 ω a b :=
        projectInteriorLocalStokes_of_extendedBox I x0 x1 ω a b hbox'
      _ = 0 := hboundary
  exact ⟨a, b, hle, hsupp, hbox', hboundary, hbulk⟩

/--
If the transition-pullback representative has support contained in a compact
coordinate set, then some strict interior box kills its project-local boundary
integral.
-/
theorem exists_projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_compact
    {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K)
    (hsuppK :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K) :
    ∃ a b : Fin (n + 1) → Real,
      a ≤ b ∧
        tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
          boxInteriorSupportBox a b ∧
        projectInteriorBoundaryIntegral I x0 x1 ω a b = 0 := by
  obtain ⟨a, b, hle, hsupp⟩ :=
    exists_boxInteriorSupportBox_of_tsupport_subset_compact
      (ManifoldForm.transitionPullbackInChart I x0 x1 ω) hK hsuppK
  exact ⟨a, b, hle, hsupp,
    projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
      I x0 x1 ω a b hsupp⟩

/--
Support contained in a compact coordinate set selects a strict interior box;
with supplied extended-box geometry, the associated project-local bulk integral
is zero.
-/
theorem exists_projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_compact
    {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (x0 x1 : M) (ω : ManifoldForm I M n)
    {K : Set (Fin (n + 1) → Real)}
    (hK : IsCompact K)
    (hsuppK :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆ K)
    (hbox :
      ∀ a b : Fin (n + 1) → Real,
        a ≤ b →
          tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
            boxInteriorSupportBox a b →
          interiorChartExtendedBox I x0 x1 ω a b) :
    ∃ a b : Fin (n + 1) → Real,
      a ≤ b ∧
        tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
          boxInteriorSupportBox a b ∧
        interiorChartExtendedBox I x0 x1 ω a b ∧
        projectInteriorBoundaryIntegral I x0 x1 ω a b = 0 ∧
        projectInteriorBulkIntegral I x0 x1 ω a b = 0 := by
  obtain ⟨a, b, hle, hsupp, hboundary⟩ :=
    exists_projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_compact
      I x0 x1 ω hK hsuppK
  have hbox' : interiorChartExtendedBox I x0 x1 ω a b :=
    hbox a b hle hsupp
  have hbulk : projectInteriorBulkIntegral I x0 x1 ω a b = 0 := by
    calc
      projectInteriorBulkIntegral I x0 x1 ω a b =
          projectInteriorBoundaryIntegral I x0 x1 ω a b :=
        projectInteriorLocalStokes_of_extendedBox I x0 x1 ω a b hbox'
      _ = 0 := hboundary
  exact ⟨a, b, hle, hsupp, hbox', hboundary, hbulk⟩

namespace InteriorLocalStokesData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

/-- The artificial boundary term recorded by local Stokes data is zero under strict support. -/
theorem artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
    (D : InteriorLocalStokesData I ω)
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart ω) ⊆
        boxInteriorSupportBox D.lowerCorner D.upperCorner) :
    D.artificialBoundaryTerm = 0 := by
  calc
    D.artificialBoundaryTerm =
        projectInteriorBoundaryIntegral I D.sourceChart D.targetChart ω
          D.lowerCorner D.upperCorner := D.artificialBoundaryTerm_eq_project
    _ = 0 :=
        projectInteriorBoundaryIntegral_eq_zero_of_tsupport_subset_interiorBox
          I D.sourceChart D.targetChart ω D.lowerCorner D.upperCorner hsupp

/-- The recorded bulk term is zero under strict support inside the selected box. -/
theorem bulkTerm_eq_zero_of_tsupport_subset_interiorBox
    (D : InteriorLocalStokesData I ω)
    (hsupp :
      tsupport
          (ManifoldForm.transitionPullbackInChart I D.sourceChart D.targetChart ω) ⊆
        boxInteriorSupportBox D.lowerCorner D.upperCorner) :
    D.bulkTerm = 0 := by
  calc
    D.bulkTerm =
        projectInteriorBulkIntegral I D.sourceChart D.targetChart ω
          D.lowerCorner D.upperCorner := D.bulkTerm_eq_project
    _ = 0 :=
        projectInteriorBulkIntegral_eq_zero_of_tsupport_subset_interiorBox
          I D.sourceChart D.targetChart ω D.lowerCorner D.upperCorner
          D.extendedBox hsupp

end InteriorLocalStokesData

/--
Pointwise-zero cancellation package for interior local Stokes data whose
transition-pullback representatives are all strictly supported inside their
auxiliary boxes.
-/
def artificialBoundaryCancellationData_of_interiorSupportZero
    {Chart Piece : Type*} {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset Piece)
    (localStokesData : Chart → Piece → InteriorLocalStokesData I ω)
    (hsupp :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ interiorPieces x →
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (localStokesData x q).sourceChart
                (localStokesData x q).targetChart ω) ⊆
            boxInteriorSupportBox
              (localStokesData x q).lowerCorner
              (localStokesData x q).upperCorner) :
    ArtificialBoundaryCancellationData Chart Piece :=
  ArtificialBoundaryCancellationData.of_forall_eq_zero activeCharts interiorPieces
    (fun x q => (localStokesData x q).artificialBoundaryTerm)
    (fun x hx q hq =>
      (localStokesData x q).artificialBoundaryTerm_eq_zero_of_tsupport_subset_interiorBox
        (hsupp x hx q hq))

namespace GlobalStokesData

/-- Global cancellation wrapper from pointwise strict-support zero of interior local data. -/
theorem interiorBoundaryCancellation_of_interiorSupportZero
    {Chart Piece : Type*} {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset Piece)
    (localStokesData : Chart → Piece → InteriorLocalStokesData I ω)
    (hsupp :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ interiorPieces x →
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (localStokesData x q).sourceChart
                (localStokesData x q).targetChart ω) ⊆
            boxInteriorSupportBox
              (localStokesData x q).lowerCorner
              (localStokesData x q).upperCorner) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun q =>
        (localStokesData x q).artificialBoundaryTerm) = 0 :=
  (artificialBoundaryCancellationData_of_interiorSupportZero
    activeCharts interiorPieces localStokesData hsupp).cancellation

end GlobalStokesData

namespace GlobalStokesAssemblyData

variable {BoundaryPiece : Type*}

/--
Assembly-layer cancellation wrapper from pointwise strict-support zero of
interior local data.
-/
theorem interiorBoundaryCancellation_of_interiorSupportZero
    {Chart Piece : Type*} {n : Nat}
    {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {ω : ManifoldForm I M n}
    (activeCharts : Finset Chart)
    (interiorPieces : Chart → Finset Piece)
    (localStokesData : Chart → Piece → InteriorLocalStokesData I ω)
    (hsupp :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ interiorPieces x →
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (localStokesData x q).sourceChart
                (localStokesData x q).targetChart ω) ⊆
            boxInteriorSupportBox
              (localStokesData x q).lowerCorner
              (localStokesData x q).upperCorner) :
    (Finset.sum activeCharts fun x =>
      Finset.sum (interiorPieces x) fun q =>
        (localStokesData x q).artificialBoundaryTerm) = 0 :=
  (artificialBoundaryCancellationData_of_interiorSupportZero
    activeCharts interiorPieces localStokesData hsupp).cancellation

end GlobalStokesAssemblyData

end InteriorChartWrappers

section BoundaryChartWrappers

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryCompactBoxSelectionData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}

/--
Boundary-chart wrapper: compact support in the half-space support box kills
exactly the non-true auxiliary faces.
-/
theorem nontrueFaceTerms_eq_zero
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    boxRemainingFormFaceTerms
        (ManifoldForm.transitionPullbackInChart I x0 x1 ω) D.a D.b = 0 :=
  D.boxRemainingFormFaceTerms_eq_zero

/--
Boundary-chart wrapper exposing the disjointness of non-true faces from the
transition-pullback face-coefficient supports.
-/
theorem nontrueFaces_tsupport_disjoint
    (D : BoundaryCompactBoxSelectionData I x0 x1 ω) :
    Disjoint (boxUpperFaceSet (0 : Fin (n + 1)) D.a D.b)
        (tsupport
          (boxFormFaceCoeff
            (ManifoldForm.transitionPullbackInChart I x0 x1 ω) (0 : Fin (n + 1)))) ∧
      ∀ i : Fin n,
        Disjoint (boxUpperFaceSet i.succ D.a D.b)
            (tsupport
              (boxFormFaceCoeff
                (ManifoldForm.transitionPullbackInChart I x0 x1 ω) i.succ)) ∧
        Disjoint (boxLowerFaceSet i.succ D.a D.b)
            (tsupport
              (boxFormFaceCoeff
                (ManifoldForm.transitionPullbackInChart I x0 x1 ω) i.succ)) :=
  D.artificialFaces_tsupport_disjoint

end BoundaryCompactBoxSelectionData

end BoundaryChartWrappers

end Stokes

end
