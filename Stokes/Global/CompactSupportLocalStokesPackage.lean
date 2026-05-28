import Stokes.Global.InteriorAssignedBoxSupport
import Stokes.BoundaryChart.BoundaryAssignedBoxSupport
import Stokes.Global.MixedGlobalConstructor

/-!
# Compact-support local Stokes package

This file packages the local compact-support conclusions used by the selected
partition route.  The inputs stay deliberately local: assigned-box support for
the localized pieces, selected local boxes, and local smoothness on the chosen
box neighborhoods.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CompactSupportLocalStokesPackage

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-- The selected interior fiber is a singleton over every active chart. -/
def selectedInteriorLocalPieces
    (_P : SelectedBoxPartitionOfUnity I omega) : M -> Finset Unit :=
  fun _ => ({()} : Finset Unit)

/-- Localized interior bulk term attached to a selected active chart. -/
def selectedInteriorLocalBulkTerm
    (P : SelectedBoxPartitionOfUnity I omega) : M -> Unit -> Real :=
  fun x _ =>
    projectInteriorBulkIntegral I x x
      (ManifoldForm.localizedForm I (P.partition x) omega)
      (P.lower x) (P.upper x)

/-- Artificial coordinate-box boundary term attached to a selected active chart. -/
def selectedInteriorArtificialBoundaryTerm
    (P : SelectedBoxPartitionOfUnity I omega) : M -> Unit -> Real :=
  fun x _ =>
    projectInteriorBoundaryIntegral I x x
      (ManifoldForm.localizedForm I (P.partition x) omega)
      (P.lower x) (P.upper x)

/-- Boundary-chart localized bulk term for an assigned boundary box family. -/
def assignedBoundaryLocalBulkTerm
    (sourceChart targetChart : M -> BoundaryPiece -> M)
    (rho : M -> BoundaryPiece -> M -> Real)
    (lower upper : M -> BoundaryPiece -> Fin (n + 1) -> Real) :
    M -> BoundaryPiece -> Real :=
  fun x q =>
    projectLocalBulkIntegral I (sourceChart x q) (targetChart x q)
      (ManifoldForm.localizedForm I (rho x q) omega)
      (lower x q) (upper x q)

/-- True outward-first boundary term for an assigned boundary box family. -/
def assignedBoundaryTrueLocalTerm
    (sourceChart targetChart : M -> BoundaryPiece -> M)
    (rho : M -> BoundaryPiece -> M -> Real)
    (lower upper : M -> BoundaryPiece -> Fin (n + 1) -> Real) :
    M -> BoundaryPiece -> Real :=
  fun x q =>
    projectLocalBoundaryIntegral I (sourceChart x q) (targetChart x q)
      (ManifoldForm.localizedForm I (rho x q) omega)
      (lower x q) (upper x q)

/-- Selected interior active pieces as a mixed local-Stokes field package. -/
def interiorAssignedBoxLocalStokesFields
    (P : SelectedBoxPartitionOfUnity I omega)
    (hbox :
      forall x, x ∈ P.active ->
        interiorChartExtendedBox I x x
          (ManifoldForm.localizedForm I (P.partition x) omega)
          (P.lower x) (P.upper x)) :
    MixedInteriorPackage I omega M Unit P.active
      (selectedInteriorLocalPieces P)
      (selectedInteriorLocalBulkTerm P)
      (selectedInteriorArtificialBoundaryTerm P) where
  localStokes := by
    intro x hx q _hq
    cases q
    exact
      projectInteriorLocalStokes_of_extendedBox I x x
        (ManifoldForm.localizedForm I (P.partition x) omega)
        (P.lower x) (P.upper x) (hbox x hx)

/-- Assigned-box support kills every selected interior artificial boundary term. -/
theorem selectedInteriorArtificialBoundaryTerm_eq_zero_of_assignedBox
    (P : SelectedBoxPartitionOfUnity I omega)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall x, x ∈ P.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (hcoeff :
      forall x, x ∈ P.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (P.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox (P.lower x) (P.upper x)) :
    forall x, x ∈ P.active ->
      forall q, q ∈ selectedInteriorLocalPieces P x ->
        selectedInteriorArtificialBoundaryTerm P x q = 0 := by
  intro x hx q _hq
  cases q
  exact
    P.localized_projectInteriorBoundaryIntegral_eq_zero_of_assignedBox
      (omega := omega) hbase hcoeff hx

/-- Assigned-box support kills every selected interior bulk term once local Stokes is available. -/
theorem selectedInteriorLocalBulkTerm_eq_zero_of_assignedBox
    (P : SelectedBoxPartitionOfUnity I omega)
    (hbox :
      forall x, x ∈ P.active ->
        interiorChartExtendedBox I x x
          (ManifoldForm.localizedForm I (P.partition x) omega)
          (P.lower x) (P.upper x))
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall x, x ∈ P.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (hcoeff :
      forall x, x ∈ P.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (P.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox (P.lower x) (P.upper x)) :
    forall x, x ∈ P.active ->
      forall q, q ∈ selectedInteriorLocalPieces P x ->
        selectedInteriorLocalBulkTerm P x q = 0 := by
  intro x hx q _hq
  cases q
  exact
    P.localized_projectInteriorBulkIntegral_eq_zero_of_assignedBox
      (omega := omega) hbox hbase hcoeff hx

/-- The selected interior artificial-boundary finite sum vanishes. -/
theorem selectedInteriorArtificialBoundarySum_eq_zero_of_assignedBox
    (P : SelectedBoxPartitionOfUnity I omega)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall x, x ∈ P.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (hcoeff :
      forall x, x ∈ P.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (P.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox (P.lower x) (P.upper x)) :
    (Finset.sum P.active fun x =>
      Finset.sum (selectedInteriorLocalPieces P x) fun q =>
        selectedInteriorArtificialBoundaryTerm P x q) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro x hx
  refine Finset.sum_eq_zero ?_
  intro q hq
  exact
    selectedInteriorArtificialBoundaryTerm_eq_zero_of_assignedBox
      (P := P) (omega := omega) hbase hcoeff x hx q hq

/-- The selected interior bulk finite sum vanishes under assigned-box support. -/
theorem selectedInteriorLocalBulkSum_eq_zero_of_assignedBox
    (P : SelectedBoxPartitionOfUnity I omega)
    (hbox :
      forall x, x ∈ P.active ->
        interiorChartExtendedBox I x x
          (ManifoldForm.localizedForm I (P.partition x) omega)
          (P.lower x) (P.upper x))
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall x, x ∈ P.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (hcoeff :
      forall x, x ∈ P.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (P.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox (P.lower x) (P.upper x)) :
    (Finset.sum P.active fun x =>
      Finset.sum (selectedInteriorLocalPieces P x) fun q =>
        selectedInteriorLocalBulkTerm P x q) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro x hx
  refine Finset.sum_eq_zero ?_
  intro q hq
  exact
    selectedInteriorLocalBulkTerm_eq_zero_of_assignedBox
      (P := P) (omega := omega) hbox hbase hcoeff x hx q hq

/--
One assigned boundary box gives local Stokes with the artificial half-space
faces already removed, stated in project-local wrapper names.
-/
theorem boundaryAssignedBox_projectLocalStokes_of_coordSupport
    {x0 x1 : M} {rho : M -> Real}
    {K : Set (Fin (n + 1) -> Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 omega) ⊆ K)
    {a b : Fin (n + 1) -> Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 rho) ∩ K ⊆
        halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) -> Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hlocalizedU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I rho omega)) U) :
    projectLocalBulkIntegral I x0 x1
        (ManifoldForm.localizedForm I rho omega) a b =
      projectLocalBoundaryIntegral I x0 x1
        (ManifoldForm.localizedForm I rho omega) a b := by
  rcases
    exists_boundaryAssignedBoxData_localStokes_of_coordSupport
      (I := I) (x0 := x0) (x1 := x1) (ρ := rho) (ω := omega)
      hK hhalf hbase ha0 hle hcoeff hdomain hU hUbox hlocalizedU with
    ⟨_hsupp, D, _hDK, hDa, hDb, hstokes⟩
  simpa [projectLocalBulkIntegral, projectLocalBoundaryIntegral, hDa, hDb] using hstokes

/--
`C^\infty` version of `boundaryAssignedBox_projectLocalStokes_of_coordSupport`.
-/
theorem boundaryAssignedBox_projectLocalStokes_of_coordSupport_infty
    {x0 x1 : M} {rho : M -> Real}
    {K : Set (Fin (n + 1) -> Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 omega) ⊆ K)
    {a b : Fin (n + 1) -> Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 rho) ∩ K ⊆
        halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) -> Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hlocalizedU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I rho omega)) U) :
    projectLocalBulkIntegral I x0 x1
        (ManifoldForm.localizedForm I rho omega) a b =
      projectLocalBoundaryIntegral I x0 x1
        (ManifoldForm.localizedForm I rho omega) a b := by
  rcases
    exists_boundaryAssignedBoxData_localStokes_of_coordSupport_infty
      (I := I) (x0 := x0) (x1 := x1) (ρ := rho) (ω := omega)
      hK hhalf hbase ha0 hle hcoeff hdomain hU hUbox hlocalizedU with
    ⟨_hsupp, D, _hDK, hDa, hDb, hstokes⟩
  simpa [projectLocalBulkIntegral, projectLocalBoundaryIntegral, hDa, hDb] using hstokes

/--
One assigned boundary box gives local Stokes, deriving localized smoothness from
coefficient and base representative smoothness on the same open neighborhood.
-/
theorem boundaryAssignedBox_projectLocalStokes_of_contDiffOn
    {x0 x1 : M} {rho : M -> Real}
    {K : Set (Fin (n + 1) -> Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 omega) ⊆ K)
    {a b : Fin (n + 1) -> Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 rho) ∩ K ⊆
        halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) -> Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hrhoU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I x0 x1 rho) U)
    (homegaU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionPullbackInChart I x0 x1 omega) U) :
    projectLocalBulkIntegral I x0 x1
        (ManifoldForm.localizedForm I rho omega) a b =
      projectLocalBoundaryIntegral I x0 x1
        (ManifoldForm.localizedForm I rho omega) a b := by
  exact
    boundaryAssignedBox_projectLocalStokes_of_coordSupport
      (I := I) (omega := omega) (x0 := x0) (x1 := x1) (rho := rho)
      hK hhalf hbase ha0 hle hcoeff hdomain hU hUbox
      (ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
        (I := I) hrhoU homegaU)

/--
One assigned boundary box gives local Stokes from `C^\infty` coefficient and
base representative smoothness.
-/
theorem boundaryAssignedBox_projectLocalStokes_of_contDiffOn_infty
    {x0 x1 : M} {rho : M -> Real}
    {K : Set (Fin (n + 1) -> Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 omega) ⊆ K)
    {a b : Fin (n + 1) -> Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 rho) ∩ K ⊆
        halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) -> Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hrhoU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionCoefficientInChart I x0 x1 rho) U)
    (homegaU :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.transitionPullbackInChart I x0 x1 omega) U) :
    projectLocalBulkIntegral I x0 x1
        (ManifoldForm.localizedForm I rho omega) a b =
      projectLocalBoundaryIntegral I x0 x1
        (ManifoldForm.localizedForm I rho omega) a b := by
  exact
    boundaryAssignedBox_projectLocalStokes_of_coordSupport_infty
      (I := I) (omega := omega) (x0 := x0) (x1 := x1) (rho := rho)
      hK hhalf hbase ha0 hle hcoeff hdomain hU hUbox
      (ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
        (I := I) hrhoU homegaU)

/--
One assigned boundary box gives local Stokes, deriving base smoothness from
chartwise smoothness of the form.
-/
theorem boundaryAssignedBox_projectLocalStokes_of_chartwiseSmooth
    [IsManifold I ⊤ M]
    {x0 x1 : M} {rho : M -> Real}
    {K : Set (Fin (n + 1) -> Real)}
    (hK : IsCompact K) (hhalf : K ⊆ upperHalfSpace n)
    (hbase :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 omega) ⊆ K)
    {a b : Fin (n + 1) -> Real}
    (ha0 : a 0 = 0) (hle : a ≤ b)
    (hcoeff :
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 rho) ∩ K ⊆
        halfSpaceSupportBox a b)
    (hdomain : Set.Icc a b ⊆ boundaryChartDomain I x0 x1)
    {U : Set (Fin (n + 1) -> Real)} (hU : IsOpen U)
    (hUbox : Set.Icc a b ⊆ U)
    (hrhoU :
      ContDiffOn Real ⊤
        (ManifoldForm.transitionCoefficientInChart I x0 x1 rho) U)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ ManifoldForm.chartOverlap I x0 x1) :
    projectLocalBulkIntegral I x0 x1
        (ManifoldForm.localizedForm I rho omega) a b =
      projectLocalBoundaryIntegral I x0 x1
        (ManifoldForm.localizedForm I rho omega) a b := by
  exact
    boundaryAssignedBox_projectLocalStokes_of_contDiffOn
      (I := I) (omega := omega) (x0 := x0) (x1 := x1) (rho := rho)
      hK hhalf hbase ha0 hle hcoeff hdomain hU hUbox hrhoU
      (homega.contDiffOn_transitionPullbackInChart_of_chartAPI
        (I := I) x0 x1 hUtarget hUoverlap)

/-- Boundary active pieces as a mixed local-Stokes field package. -/
def boundaryAssignedBoxLocalStokesFields_of_contDiffOn
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundaryPieces : M -> Finset BoundaryPiece)
    (sourceChart targetChart : M -> BoundaryPiece -> M)
    (rho : M -> BoundaryPiece -> M -> Real)
    (K : M -> BoundaryPiece -> Set (Fin (n + 1) -> Real))
    (lower upper : M -> BoundaryPiece -> Fin (n + 1) -> Real)
    (U : M -> BoundaryPiece -> Set (Fin (n + 1) -> Real))
    (hK :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> IsCompact (K x q))
    (hhalf :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> K x q ⊆ upperHalfSpace n)
    (hbase :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (sourceChart x q) (targetChart x q) omega) ⊆
            K x q)
    (ha0 :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> lower x q 0 = 0)
    (hle :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> lower x q ≤ upper x q)
    (hcoeff :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          tsupport
              (ManifoldForm.transitionCoefficientInChart I
                (sourceChart x q) (targetChart x q) (rho x q)) ∩ K x q ⊆
            halfSpaceSupportBox (lower x q) (upper x q))
    (hdomain :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          Set.Icc (lower x q) (upper x q) ⊆
            boundaryChartDomain I (sourceChart x q) (targetChart x q))
    (hU :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> IsOpen (U x q))
    (hUbox :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          Set.Icc (lower x q) (upper x q) ⊆ U x q)
    (hrhoU :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          ContDiffOn Real ⊤
            (ManifoldForm.transitionCoefficientInChart I
              (sourceChart x q) (targetChart x q) (rho x q)) (U x q))
    (homegaU :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          ContDiffOn Real ⊤
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart x q) (targetChart x q) omega) (U x q)) :
    MixedBoundaryPackage I omega M BoundaryPiece P.active boundaryPieces
      (assignedBoundaryLocalBulkTerm (I := I) (omega := omega)
        sourceChart targetChart rho lower upper)
      (assignedBoundaryTrueLocalTerm (I := I) (omega := omega)
        sourceChart targetChart rho lower upper) where
  localStokes := by
    intro x hx q hq
    exact
      boundaryAssignedBox_projectLocalStokes_of_contDiffOn
        (I := I) (omega := omega)
        (x0 := sourceChart x q) (x1 := targetChart x q)
        (rho := rho x q)
        (hK x hx q hq) (hhalf x hx q hq) (hbase x hx q hq)
        (ha0 x hx q hq) (hle x hx q hq) (hcoeff x hx q hq)
        (hdomain x hx q hq) (hU x hx q hq) (hUbox x hx q hq)
        (hrhoU x hx q hq) (homegaU x hx q hq)

/--
Output package containing both local field constructors and the selected
interior zero facts needed to erase artificial boundaries from finite sums.
-/
structure CompactSupportLocalStokesPackage
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundaryPieces : M -> Finset BoundaryPiece)
    (sourceChart targetChart : M -> BoundaryPiece -> M)
    (rho : M -> BoundaryPiece -> M -> Real)
    (lower upper : M -> BoundaryPiece -> Fin (n + 1) -> Real) where
  /-- Interior selected active pieces satisfy local Stokes. -/
  interiorFields :
    MixedInteriorPackage I omega M Unit P.active
      (selectedInteriorLocalPieces P)
      (selectedInteriorLocalBulkTerm P)
      (selectedInteriorArtificialBoundaryTerm P)
  /-- Boundary active pieces satisfy outward-first local Stokes. -/
  boundaryFields :
    MixedBoundaryPackage I omega M BoundaryPiece P.active boundaryPieces
      (assignedBoundaryLocalBulkTerm (I := I) (omega := omega)
        sourceChart targetChart rho lower upper)
      (assignedBoundaryTrueLocalTerm (I := I) (omega := omega)
        sourceChart targetChart rho lower upper)
  /-- Assigned interior boxes erase every artificial coordinate-box boundary term. -/
  interiorArtificialBoundaryZero :
    forall x, x ∈ P.active ->
      forall q, q ∈ selectedInteriorLocalPieces P x ->
        selectedInteriorArtificialBoundaryTerm P x q = 0
  /-- The same assigned support also erases every selected interior bulk term. -/
  interiorBulkZero :
    forall x, x ∈ P.active ->
      forall q, q ∈ selectedInteriorLocalPieces P x ->
        selectedInteriorLocalBulkTerm P x q = 0

namespace CompactSupportLocalStokesPackage

variable {P : SelectedBoxPartitionOfUnity I omega}
variable {boundaryPieces : M -> Finset BoundaryPiece}
variable {sourceChart targetChart : M -> BoundaryPiece -> M}
variable {rho : M -> BoundaryPiece -> M -> Real}
variable {lower upper : M -> BoundaryPiece -> Fin (n + 1) -> Real}

/-- Sum of selected interior local bulk terms. -/
def interiorBulkSum
    (_D :
      CompactSupportLocalStokesPackage (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho lower upper) : Real :=
  Finset.sum P.active fun x =>
    Finset.sum (selectedInteriorLocalPieces P x) fun q =>
      selectedInteriorLocalBulkTerm P x q

/-- Sum of selected interior artificial-boundary terms. -/
def interiorArtificialBoundarySum
    (_D :
      CompactSupportLocalStokesPackage (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho lower upper) : Real :=
  Finset.sum P.active fun x =>
    Finset.sum (selectedInteriorLocalPieces P x) fun q =>
      selectedInteriorArtificialBoundaryTerm P x q

/-- Sum of boundary-piece local bulk terms. -/
def boundaryBulkSum
    (_D :
      CompactSupportLocalStokesPackage (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho lower upper) : Real :=
  Finset.sum P.active fun x =>
    Finset.sum (boundaryPieces x) fun q =>
      assignedBoundaryLocalBulkTerm (I := I) (omega := omega)
        sourceChart targetChart rho lower upper x q

/-- Sum of true outward-first boundary-piece terms. -/
def trueBoundarySum
    (_D :
      CompactSupportLocalStokesPackage (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho lower upper) : Real :=
  Finset.sum P.active fun x =>
    Finset.sum (boundaryPieces x) fun q =>
      assignedBoundaryTrueLocalTerm (I := I) (omega := omega)
        sourceChart targetChart rho lower upper x q

/-- Interior artificial-boundary terms vanish in the packaged finite sum. -/
theorem interiorArtificialBoundarySum_eq_zero
    (D :
      CompactSupportLocalStokesPackage (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho lower upper) :
    D.interiorArtificialBoundarySum = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro x hx
  refine Finset.sum_eq_zero ?_
  intro q hq
  exact D.interiorArtificialBoundaryZero x hx q hq

/-- Interior bulk terms vanish in the packaged finite sum. -/
theorem interiorBulkSum_eq_zero
    (D :
      CompactSupportLocalStokesPackage (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho lower upper) :
    D.interiorBulkSum = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro x hx
  refine Finset.sum_eq_zero ?_
  intro q hq
  exact D.interiorBulkZero x hx q hq

/-- Boundary local Stokes identities summed over all selected active pieces. -/
theorem boundaryBulkSum_eq_trueBoundarySum
    (D :
      CompactSupportLocalStokesPackage (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho lower upper) :
    D.boundaryBulkSum = D.trueBoundarySum := by
  exact
    GlobalStokesData.sum_localPieces P.active boundaryPieces
      (assignedBoundaryLocalBulkTerm (I := I) (omega := omega)
        sourceChart targetChart rho lower upper)
      (assignedBoundaryTrueLocalTerm (I := I) (omega := omega)
        sourceChart targetChart rho lower upper)
      D.boundaryFields.localStokes

/--
After assigned-box support erases interior artificial terms, the full local
bulk finite sum is exactly the finite sum of the true boundary local terms.
-/
theorem localBulkSum_eq_trueBoundarySum
    (D :
      CompactSupportLocalStokesPackage (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho lower upper) :
    D.interiorBulkSum + D.boundaryBulkSum = D.trueBoundarySum := by
  rw [D.interiorBulkSum_eq_zero, zero_add]
  exact D.boundaryBulkSum_eq_trueBoundarySum

/--
The local boundary side also reduces to the true boundary sum: the interior
side of local Stokes is artificial and vanishes by assigned-box support.
-/
theorem localBoundarySideSum_eq_trueBoundarySum
    (D :
      CompactSupportLocalStokesPackage (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho lower upper) :
    D.interiorArtificialBoundarySum + D.trueBoundarySum = D.trueBoundarySum := by
  rw [D.interiorArtificialBoundarySum_eq_zero, zero_add]

end CompactSupportLocalStokesPackage

/-- Constructor for the compact-support local Stokes package from assigned boxes. -/
def compactSupportLocalStokesPackage_of_assignedBoxes
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundaryPieces : M -> Finset BoundaryPiece)
    (sourceChart targetChart : M -> BoundaryPiece -> M)
    (rho : M -> BoundaryPiece -> M -> Real)
    (K : M -> BoundaryPiece -> Set (Fin (n + 1) -> Real))
    (lower upper : M -> BoundaryPiece -> Fin (n + 1) -> Real)
    (U : M -> BoundaryPiece -> Set (Fin (n + 1) -> Real))
    (interiorBox :
      forall x, x ∈ P.active ->
        interiorChartExtendedBox I x x
          (ManifoldForm.localizedForm I (P.partition x) omega)
          (P.lower x) (P.upper x))
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (interiorBaseSupport :
      forall x, x ∈ P.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (interiorCoeffSupport :
      forall x, x ∈ P.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (P.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox (P.lower x) (P.upper x))
    (boundaryK :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> IsCompact (K x q))
    (boundaryHalf :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> K x q ⊆ upperHalfSpace n)
    (boundaryBaseSupport :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (sourceChart x q) (targetChart x q) omega) ⊆
            K x q)
    (boundaryLowerZero :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> lower x q 0 = 0)
    (boundaryLe :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> lower x q ≤ upper x q)
    (boundaryCoeffSupport :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          tsupport
              (ManifoldForm.transitionCoefficientInChart I
                (sourceChart x q) (targetChart x q) (rho x q)) ∩ K x q ⊆
            halfSpaceSupportBox (lower x q) (upper x q))
    (boundaryDomain :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          Set.Icc (lower x q) (upper x q) ⊆
            boundaryChartDomain I (sourceChart x q) (targetChart x q))
    (boundaryUOpen :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> IsOpen (U x q))
    (boundaryUBox :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          Set.Icc (lower x q) (upper x q) ⊆ U x q)
    (boundaryCoeffSmooth :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          ContDiffOn Real ⊤
            (ManifoldForm.transitionCoefficientInChart I
              (sourceChart x q) (targetChart x q) (rho x q)) (U x q))
    (boundaryFormSmooth :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          ContDiffOn Real ⊤
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart x q) (targetChart x q) omega) (U x q)) :
    CompactSupportLocalStokesPackage (I := I) (omega := omega)
      P boundaryPieces sourceChart targetChart rho lower upper where
  interiorFields := interiorAssignedBoxLocalStokesFields P interiorBox
  boundaryFields :=
    boundaryAssignedBoxLocalStokesFields_of_contDiffOn
      (P := P) (omega := omega)
      boundaryPieces sourceChart targetChart rho K lower upper U
      boundaryK boundaryHalf boundaryBaseSupport boundaryLowerZero boundaryLe
      boundaryCoeffSupport boundaryDomain boundaryUOpen boundaryUBox
      boundaryCoeffSmooth boundaryFormSmooth
  interiorArtificialBoundaryZero :=
    selectedInteriorArtificialBoundaryTerm_eq_zero_of_assignedBox
      (P := P) (omega := omega) interiorBaseSupport interiorCoeffSupport
  interiorBulkZero :=
    selectedInteriorLocalBulkTerm_eq_zero_of_assignedBox
      (P := P) (omega := omega) interiorBox interiorBaseSupport
      interiorCoeffSupport

/--
Finite-sum constructor theorem: assigned-box support plus local smoothness gives
the local compact-support Stokes sum with artificial interior terms removed.
-/
theorem sum_localBulk_eq_trueBoundarySum_of_assignedBoxes
    (P : SelectedBoxPartitionOfUnity I omega)
    (boundaryPieces : M -> Finset BoundaryPiece)
    (sourceChart targetChart : M -> BoundaryPiece -> M)
    (rho : M -> BoundaryPiece -> M -> Real)
    (K : M -> BoundaryPiece -> Set (Fin (n + 1) -> Real))
    (lower upper : M -> BoundaryPiece -> Fin (n + 1) -> Real)
    (U : M -> BoundaryPiece -> Set (Fin (n + 1) -> Real))
    (interiorBox :
      forall x, x ∈ P.active ->
        interiorChartExtendedBox I x x
          (ManifoldForm.localizedForm I (P.partition x) omega)
          (P.lower x) (P.upper x))
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (interiorBaseSupport :
      forall x, x ∈ P.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (interiorCoeffSupport :
      forall x, x ∈ P.active ->
        tsupport
            (ManifoldForm.transitionCoefficientInChart I x x
              (P.partition x)) ∩ coordSupport x ⊆
          boxInteriorSupportBox (P.lower x) (P.upper x))
    (boundaryK :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> IsCompact (K x q))
    (boundaryHalf :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> K x q ⊆ upperHalfSpace n)
    (boundaryBaseSupport :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (sourceChart x q) (targetChart x q) omega) ⊆
            K x q)
    (boundaryLowerZero :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> lower x q 0 = 0)
    (boundaryLe :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> lower x q ≤ upper x q)
    (boundaryCoeffSupport :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          tsupport
              (ManifoldForm.transitionCoefficientInChart I
                (sourceChart x q) (targetChart x q) (rho x q)) ∩ K x q ⊆
            halfSpaceSupportBox (lower x q) (upper x q))
    (boundaryDomain :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          Set.Icc (lower x q) (upper x q) ⊆
            boundaryChartDomain I (sourceChart x q) (targetChart x q))
    (boundaryUOpen :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x -> IsOpen (U x q))
    (boundaryUBox :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          Set.Icc (lower x q) (upper x q) ⊆ U x q)
    (boundaryCoeffSmooth :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          ContDiffOn Real ⊤
            (ManifoldForm.transitionCoefficientInChart I
              (sourceChart x q) (targetChart x q) (rho x q)) (U x q))
    (boundaryFormSmooth :
      forall x, x ∈ P.active ->
        forall q, q ∈ boundaryPieces x ->
          ContDiffOn Real ⊤
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart x q) (targetChart x q) omega) (U x q)) :
    let D :=
      compactSupportLocalStokesPackage_of_assignedBoxes
        (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho K lower upper U
        interiorBox interiorBaseSupport interiorCoeffSupport
        boundaryK boundaryHalf boundaryBaseSupport boundaryLowerZero boundaryLe
        boundaryCoeffSupport boundaryDomain boundaryUOpen boundaryUBox
        boundaryCoeffSmooth boundaryFormSmooth
    D.interiorBulkSum + D.boundaryBulkSum = D.trueBoundarySum := by
  intro D
  exact D.localBulkSum_eq_trueBoundarySum

end CompactSupportLocalStokesPackage

end Stokes

end
