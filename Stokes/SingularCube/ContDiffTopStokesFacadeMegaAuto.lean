import Stokes.SingularCube.ContDiffTopUpgradeMegaAuto
import Stokes.SingularCube.SmoothBridgeFacade
import Stokes.SingularCube.IntegralCongruence

/-!
# Public top-smoothness facade for the singular-cube Stokes route

`ContDiffTopUpgradeMegaAuto` isolates the honest analytic gap in the current
smooth-singular-cube route: the generated cutoff extension is constructed as a
`C∞` Euclidean form, but the existing singular-cube Stokes theorem still asks
for `ContDiff Real ⊤`.  Mathlib's monotonicity API gives the downgrade
`⊤ -> ∞`; it does not provide an automatic upgrade `∞ -> ⊤`.

This file is a theorem-facing public facade around that fact.  The input
contains the already constructed cutoff-extension data, and the only additional
smoothness field is

```
ContDiff Real ⊤ generatedExtension
```

Everything else is projected from existing modules: cutoff construction,
carrier containment, local agreement, congruence to the chart representative,
and the boundary/chain Stokes theorem wrappers.
-/

noncomputable section

open Set Function Filter
open scoped Manifold Topology ContDiff

namespace Stokes
namespace SingularCubeSmoothExtensionAudit
namespace SingularCubeTopStokesFacade

section PublicInput

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n m : Nat}
variable {I : ModelWithCorners Real (Fin m → Real) H}
variable {omega : ManifoldForm I M n}
variable {chart : M} {cube : SmoothSingularCube (n + 1) m}

/-- The top-smoothness requirement for the generated cutoff extension.

The generated extension is already `C∞`; this proposition names the single
extra field that the current singular-cube Stokes theorem still requires. -/
def GeneratedExtensionTopSmoothness
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube) : Prop :=
  ContDiff Real ⊤ E.euclideanPackage.omegaExt

/-- Public theorem input for the singular-cube Stokes route with cutoff
extension.

The `base` field contains all geometric and cutoff-construction data.  The
only additional analytic field is top smoothness of the generated extension;
there is deliberately no theorem pretending that the existing `C∞` proof can
be upgraded to `⊤`. -/
structure ChartwiseSingularCubeTopStokesPublicInput
    (omega : ManifoldForm I M n)
    (chart : M) (cube : SmoothSingularCube (n + 1) m) where
  /-- The already constructed chartwise cutoff extension. -/
  base : ChartwiseSingularCubeCutoffExtensionInput omega chart cube
  /-- The single remaining top-smoothness field for the generated extension. -/
  contDiff_top_generatedExtension :
    ContDiff Real ⊤ base.euclideanPackage.omegaExt

namespace ChartwiseSingularCubeTopStokesPublicInput

variable (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube)

/-- The local chart representative used by the singular-cube theorem. -/
abbrev localForm
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    EuclideanForm m n :=
  let _anchor := P
  chartLocalForm I chart omega

/-- The Euclidean cutoff extension generated from the public input. -/
abbrev generatedExtension
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    EuclideanForm m n :=
  P.base.euclideanPackage.omegaExt

/-- The chart-local smoothness neighborhood. -/
abbrev smoothSet
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    Set (Fin m → Real) :=
  P.base.smoothSet

/-- The open neighborhood on which the extension agrees with the local form. -/
abbrev extensionSet
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    Set (Fin m → Real) :=
  P.base.cutoffShrink.inner

/-- The support buffer for the scalar cutoff. -/
abbrev supportBuffer
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    Set (Fin m → Real) :=
  P.base.cutoffShrink.supportSet

/-- The compact carrier containing the cube and all faces. -/
abbrev compactCarrier
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    CubeAndFacesCompactData cube :=
  P.base.compactCarrier

/-- The nested cutoff shrink used by the generated extension. -/
abbrev cutoffShrink
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    CompactCarrierCutoffShrink (m := m) P.compactCarrier.carrier P.smoothSet :=
  P.base.cutoffShrink

/-- The scalar cutoff data used in the generated extension. -/
abbrev cutoffData
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    EuclideanCutoffFunctionData P.cutoffShrink :=
  P.base.euclideanPackage.cutoffData

/-- The scalar cutoff function used in the generated extension. -/
abbrev scalarCutoff
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    (Fin m → Real) → Real :=
  P.cutoffData.cutoff

/-- The cutoff package behind the generated extension. -/
abbrev euclideanPackage
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    EuclideanFormCutoffSmoothPackage P.localForm P.cutoffShrink :=
  P.base.euclideanPackage

/-- The open-extension input obtained from the public facade. -/
def toCutoffTopExtensionInput :
    ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube where
  base := P.base
  contDiff_top_omegaExt := P.contDiff_top_generatedExtension

/-- The compact-extension input obtained from the public facade. -/
def toCompactExtensionInput :
    ChartwiseSingularCubeCompactExtensionInput omega chart cube :=
  P.toCutoffTopExtensionInput.toCompactExtensionInput

/-- The core extension input obtained from the public facade. -/
def toCoreExtensionInput :
    ChartwiseSingularCubeCoreExtensionInput omega chart cube :=
  P.toCutoffTopExtensionInput.toCoreExtensionInput

/-- The open-neighborhood extension input obtained from the public facade. -/
def toOpenExtensionInput :
    ChartwiseSingularCubeOpenExtensionInput omega chart cube :=
  P.toCutoffTopExtensionInput.toOpenExtensionInput

/-- The compressed top-upgrade bridge already provided by the audit layer. -/
def toTopUpgradeBridge :
    ChartwiseSingularCubeCutoffTopUpgradeBridge P.base :=
  ChartwiseSingularCubeCutoffTopUpgradeBridge.ofTop
    P.contDiff_top_generatedExtension

/-- The local data attached to the open-extension input. -/
abbrev localData
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    ChartSingularCubeLocalData (d := n + 1) I omega :=
  P.toOpenExtensionInput.localData

/-- The local extension input used by the congruence layer. -/
def toLocalExtensionInput :
    ChartSingularCubeLocalExtensionInput P.localData :=
  P.toOpenExtensionInput.toLocalExtensionInput

/-- Constructor from the already generated cutoff extension plus the top field. -/
def ofBase
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : GeneratedExtensionTopSmoothness E) :
    ChartwiseSingularCubeTopStokesPublicInput omega chart cube where
  base := E
  contDiff_top_generatedExtension := htop

/-- Constructor from the lower-level compressed top-upgrade bridge. -/
def ofTopUpgradeBridge
    {E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube}
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ChartwiseSingularCubeTopStokesPublicInput omega chart cube where
  base := E
  contDiff_top_generatedExtension := B.contDiff_top_omegaExt

/-- Forget the public facade back to the lower-level compressed bridge. -/
def toExistingTopUpgradeBridge :
    ChartwiseSingularCubeCutoffTopUpgradeBridge P.base :=
  P.toTopUpgradeBridge

/-- Forget the public facade to the older top-extension input. -/
def toExistingCutoffTopExtensionInput :
    ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube :=
  P.toCutoffTopExtensionInput

@[simp]
theorem ofBase_base
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : GeneratedExtensionTopSmoothness E) :
    (ofBase (I := I) E htop).base = E :=
  rfl

@[simp]
theorem ofBase_contDiff_top_generatedExtension
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : GeneratedExtensionTopSmoothness E) :
    (ofBase (I := I) E htop).contDiff_top_generatedExtension = htop :=
  rfl

@[simp]
theorem ofTopUpgradeBridge_base
    {E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube}
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    (ofTopUpgradeBridge (I := I) B).base = E :=
  rfl

@[simp]
theorem ofTopUpgradeBridge_contDiff_top_generatedExtension
    {E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube}
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    (ofTopUpgradeBridge (I := I) B).contDiff_top_generatedExtension =
      B.contDiff_top_omegaExt :=
  rfl

@[simp]
theorem generatedExtension_eq :
    P.generatedExtension = P.base.euclideanPackage.omegaExt :=
  rfl

@[simp]
theorem localForm_eq :
    P.localForm = chartLocalForm I chart omega :=
  rfl

@[simp]
theorem smoothSet_eq :
    P.smoothSet = P.base.smoothSet :=
  rfl

@[simp]
theorem extensionSet_eq :
    P.extensionSet = P.base.cutoffShrink.inner :=
  rfl

@[simp]
theorem supportBuffer_eq :
    P.supportBuffer = P.base.cutoffShrink.supportSet :=
  rfl

@[simp]
theorem compactCarrier_eq :
    P.compactCarrier = P.base.compactCarrier :=
  rfl

@[simp]
theorem cutoffShrink_eq :
    P.cutoffShrink = P.base.cutoffShrink :=
  rfl

@[simp]
theorem cutoffData_eq :
    P.cutoffData = P.base.euclideanPackage.cutoffData :=
  rfl

@[simp]
theorem scalarCutoff_eq :
    P.scalarCutoff = P.base.euclideanPackage.cutoffData.cutoff :=
  rfl

@[simp]
theorem euclideanPackage_eq :
    P.euclideanPackage = P.base.euclideanPackage :=
  rfl

@[simp]
theorem toCutoffTopExtensionInput_base :
    P.toCutoffTopExtensionInput.base = P.base :=
  rfl

@[simp]
theorem toCutoffTopExtensionInput_contDiff_top :
    P.toCutoffTopExtensionInput.contDiff_top_omegaExt =
      P.contDiff_top_generatedExtension :=
  rfl

@[simp]
theorem toTopUpgradeBridge_contDiff_top :
    P.toTopUpgradeBridge.contDiff_top_omegaExt =
      P.contDiff_top_generatedExtension :=
  rfl

@[simp]
theorem toTopUpgradeBridge_base :
    P.toTopUpgradeBridge.base = P.base :=
  rfl

@[simp]
theorem toCompactExtensionInput_omegaExt :
    P.toCompactExtensionInput.omegaExt = P.generatedExtension :=
  rfl

@[simp]
theorem toCompactExtensionInput_extensionSet :
    P.toCompactExtensionInput.extensionSet = P.extensionSet :=
  rfl

@[simp]
theorem toCompactExtensionInput_compactCarrier :
    P.toCompactExtensionInput.compactCarrier = P.compactCarrier :=
  rfl

@[simp]
theorem toCompactExtensionInput_chartwiseSmooth :
    P.toCompactExtensionInput.chartwiseSmooth = P.base.chartwiseSmooth :=
  rfl

@[simp]
theorem toOpenExtensionInput_omegaExt :
    P.toOpenExtensionInput.omegaExt = P.generatedExtension :=
  rfl

@[simp]
theorem toOpenExtensionInput_extensionSet :
    P.toOpenExtensionInput.extensionSet = P.extensionSet :=
  rfl

@[simp]
theorem toCoreExtensionInput_omegaExt :
    P.toCoreExtensionInput.omegaExt = P.generatedExtension :=
  rfl

@[simp]
theorem toExistingTopUpgradeBridge_eq :
    P.toExistingTopUpgradeBridge = P.toTopUpgradeBridge :=
  rfl

@[simp]
theorem toExistingCutoffTopExtensionInput_eq :
    P.toExistingCutoffTopExtensionInput = P.toCutoffTopExtensionInput :=
  rfl

/-- The required top smoothness of the generated extension. -/
theorem contDiff_top_generatedExtension' :
    ContDiff Real ⊤ P.generatedExtension :=
  P.contDiff_top_generatedExtension

/-- The generated extension is `C∞` from the original cutoff construction. -/
theorem contDiff_infty_generatedExtension_from_cutoff :
    ContDiff Real ∞ P.generatedExtension :=
  P.base.contDiff_infty_omegaExt

/-- The generated extension is `C∞` by downgrading the explicit top field. -/
theorem contDiff_infty_generatedExtension_from_top :
    ContDiff Real ∞ P.generatedExtension :=
  contDiff_infty_of_contDiff_top P.contDiff_top_generatedExtension

/-- Top smoothness at every point. -/
theorem contDiffAt_top_generatedExtension (x : Fin m → Real) :
    ContDiffAt Real ⊤ P.generatedExtension x :=
  P.contDiff_top_generatedExtension.contDiffAt

/-- `C∞` smoothness at every point from the cutoff construction. -/
theorem contDiffAt_infty_generatedExtension (x : Fin m → Real) :
    ContDiffAt Real ∞ P.generatedExtension x :=
  P.contDiff_infty_generatedExtension_from_cutoff.contDiffAt

/-- Top smoothness on any set. -/
theorem contDiffOn_top_generatedExtension (s : Set (Fin m → Real)) :
    ContDiffOn Real ⊤ P.generatedExtension s :=
  P.contDiff_top_generatedExtension.contDiffOn

/-- `C∞` smoothness on any set from the cutoff construction. -/
theorem contDiffOn_infty_generatedExtension (s : Set (Fin m → Real)) :
    ContDiffOn Real ∞ P.generatedExtension s :=
  P.contDiff_infty_generatedExtension_from_cutoff.contDiffOn

/-- The generated extension is continuous. -/
theorem continuous_generatedExtension :
    Continuous P.generatedExtension :=
  P.contDiff_top_generatedExtension.continuous

/-- The local chart form is smooth on the chosen smoothness set. -/
theorem contDiffOn_localForm_smoothSet :
    ContDiffOn Real ⊤ P.localForm P.smoothSet :=
  P.base.contDiffOn_localForm_smoothSet

/-- The local chart form is `C∞` on the chosen smoothness set. -/
theorem contDiffOn_localForm_smoothSet_infty :
    ContDiffOn Real ∞ P.localForm P.smoothSet :=
  P.base.contDiffOn_localForm_smoothSet_infty

/-- The smoothness set is open. -/
theorem isOpen_smoothSet :
    IsOpen P.smoothSet :=
  P.base.isOpen_smoothSet

/-- The extension set is open. -/
theorem isOpen_extensionSet :
    IsOpen P.extensionSet :=
  P.base.cutoffShrink.isOpen_inner

/-- The support buffer is open. -/
theorem isOpen_supportBuffer :
    IsOpen P.supportBuffer :=
  P.base.cutoffShrink.isOpen_supportSet

/-- The cube image lands in the chart-local smoothness set. -/
theorem cube_mapsTo_smoothSet :
    MapsTo cube.toFun (singularParameterCube (n + 1)) P.smoothSet :=
  P.base.cube_mem_smoothSet

/-- The smoothness set lies in the selected chart target. -/
theorem smoothSet_subset_chartTarget :
    P.smoothSet ⊆ (extChartAt I chart).target :=
  P.base.smoothSet_subset_chartTarget

/-- The extension set lies in the local smoothness set. -/
theorem extensionSet_subset_smoothSet :
    P.extensionSet ⊆ P.smoothSet :=
  P.base.cutoffShrink.inner_subset_outer

/-- The support buffer lies in the local smoothness set. -/
theorem supportBuffer_subset_smoothSet :
    P.supportBuffer ⊆ P.smoothSet :=
  P.base.cutoffShrink.supportSet_subset_outer

/-- The compact carrier lies in the extension set. -/
theorem carrier_subset_extensionSet :
    P.compactCarrier.carrier ⊆ P.extensionSet :=
  P.base.cutoffShrink.carrier_subset_inner

/-- The compact carrier lies in the support buffer. -/
theorem carrier_subset_supportBuffer :
    P.compactCarrier.carrier ⊆ P.supportBuffer :=
  P.base.cutoffShrink.carrier_subset_supportSet

/-- The compact carrier lies in the local smoothness set. -/
theorem carrier_subset_smoothSet :
    P.compactCarrier.carrier ⊆ P.smoothSet :=
  P.base.cutoffShrink.carrier_subset_outer

/-- The extension set is a set-neighborhood of the compact carrier. -/
theorem extensionSet_mem_nhdsSet :
    P.extensionSet ∈ 𝓝ˢ P.compactCarrier.carrier :=
  P.base.cutoffShrink.inner_mem_nhdsSet

/-- The support buffer is a set-neighborhood of the compact carrier. -/
theorem supportBuffer_mem_nhdsSet :
    P.supportBuffer ∈ 𝓝ˢ P.compactCarrier.carrier :=
  P.base.cutoffShrink.supportSet_mem_nhdsSet

/-- The compact carrier is compact. -/
theorem isCompact_carrier :
    IsCompact P.compactCarrier.carrier :=
  P.compactCarrier.isCompact_carrier

/-- The full cube image lies in the extension set. -/
theorem cube_mem_extensionSet
    {x : Fin (n + 1) → Real} (hx : x ∈ singularParameterCube (n + 1)) :
    cube.toFun x ∈ P.extensionSet :=
  P.base.cube_mem_extensionSet hx

/-- High-face images lie in the extension set. -/
theorem highFace_mem_extensionSet
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 1).toFun x ∈ P.extensionSet :=
  P.base.highFace_mem_extensionSet i hx

/-- Low-face images lie in the extension set. -/
theorem lowFace_mem_extensionSet
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 0).toFun x ∈ P.extensionSet :=
  P.base.lowFace_mem_extensionSet i hx

/-- The generated extension agrees with the chart local form on the extension set. -/
theorem generatedExtension_agreesOn_extensionSet :
    EqOn P.generatedExtension P.localForm P.extensionSet :=
  P.base.omegaExt_agreesOn_inner

/-- The generated extension agrees with the chart local form on the compact carrier. -/
theorem generatedExtension_agreesOn_carrier :
    EqOn P.generatedExtension P.localForm P.compactCarrier.carrier :=
  P.base.omegaExt_agreesOn_carrier

/-- Pointwise agreement on the extension set. -/
theorem generatedExtension_eq_localForm_of_mem_extensionSet
    {x : Fin m → Real} (hx : x ∈ P.extensionSet) :
    P.generatedExtension x = P.localForm x :=
  P.generatedExtension_agreesOn_extensionSet hx

/-- Pointwise agreement on the compact carrier. -/
theorem generatedExtension_eq_localForm_of_mem_carrier
    {x : Fin m → Real} (hx : x ∈ P.compactCarrier.carrier) :
    P.generatedExtension x = P.localForm x :=
  P.generatedExtension_agreesOn_carrier hx

/-- The generated extension is explicitly the scalar cutoff times the local form. -/
theorem generatedExtension_apply (x : Fin m → Real) :
    P.generatedExtension x = P.scalarCutoff x • P.localForm x :=
  P.base.euclideanPackage.omegaExt_apply x

/-- The scalar cutoff is `C∞`. -/
theorem contDiff_infty_scalarCutoff :
    ContDiff Real ∞ P.scalarCutoff :=
  P.cutoffData.contDiff_cutoff

/-- The scalar cutoff is one on the extension set. -/
theorem scalarCutoff_eq_one_of_mem_extensionSet
    {x : Fin m → Real} (hx : x ∈ P.extensionSet) :
    P.scalarCutoff x = 1 :=
  P.cutoffData.cutoff_eq_one_of_mem_inner hx

/-- The scalar cutoff is one on the compact carrier. -/
theorem scalarCutoff_eq_one_of_mem_carrier
    {x : Fin m → Real} (hx : x ∈ P.compactCarrier.carrier) :
    P.scalarCutoff x = 1 :=
  P.cutoffData.cutoff_eq_one_of_mem_carrier hx

/-- The scalar cutoff vanishes outside the local smoothness set. -/
theorem scalarCutoff_eq_zero_of_not_mem_smoothSet
    {x : Fin m → Real} (hx : x ∉ P.smoothSet) :
    P.scalarCutoff x = 0 :=
  P.cutoffData.cutoff_eq_zero_of_not_mem_outer hx

/-- The scalar cutoff has support contained in the local smoothness set. -/
theorem scalarCutoff_support_subset_smoothSet :
    support P.scalarCutoff ⊆ P.smoothSet :=
  P.cutoffData.support_subset_outer

/-- The scalar cutoff has topological support contained in the local smoothness set. -/
theorem scalarCutoff_tsupport_subset_smoothSet :
    tsupport P.scalarCutoff ⊆ P.smoothSet :=
  P.cutoffData.tsupport_subset_outer

/-- Boundary Stokes from the public top-smoothness facade. -/
theorem boundary_stokes :
    SingularCubeStokes.bdryIntegral_singular cube P.localForm =
      integrateForm cube (fun y => extDeriv P.localForm y) :=
  P.toTopUpgradeBridge.boundary_stokes

/-- Chain Stokes from the public top-smoothness facade. -/
theorem chain_stokes :
    integrateChain (singularBoundarySingle cube) P.localForm =
      integrateForm cube (fun y => extDeriv P.localForm y) :=
  P.toTopUpgradeBridge.chain_stokes

/-- Boundary Stokes through the older cutoff-top input. -/
theorem boundary_stokes_via_cutoffTopExtensionInput :
    SingularCubeStokes.bdryIntegral_singular cube P.localForm =
      integrateForm cube (fun y => extDeriv P.localForm y) :=
  P.toCutoffTopExtensionInput.boundary_stokes

/-- Chain Stokes through the older cutoff-top input. -/
theorem chain_stokes_via_cutoffTopExtensionInput :
    integrateChain (singularBoundarySingle cube) P.localForm =
      integrateForm cube (fun y => extDeriv P.localForm y) :=
  P.toCutoffTopExtensionInput.chain_stokes

/-- Boundary Stokes through the compact-extension input. -/
theorem boundary_stokes_via_compactExtensionInput :
    SingularCubeStokes.bdryIntegral_singular cube P.localForm =
      integrateForm cube (fun y => extDeriv P.localForm y) :=
  P.toCompactExtensionInput.boundary_stokes

/-- Chain Stokes through the compact-extension input. -/
theorem chain_stokes_via_compactExtensionInput :
    integrateChain (singularBoundarySingle cube) P.localForm =
      integrateForm cube (fun y => extDeriv P.localForm y) :=
  P.toCompactExtensionInput.chain_stokes

/-- Boundary Stokes through the open-extension input. -/
theorem boundary_stokes_via_openExtensionInput :
    SingularCubeStokes.bdryIntegral_singular cube P.localForm =
      integrateForm cube (fun y => extDeriv P.localForm y) :=
  P.toOpenExtensionInput.boundary_stokes

/-- Chain Stokes through the open-extension input. -/
theorem chain_stokes_via_openExtensionInput :
    integrateChain (singularBoundarySingle cube) P.localForm =
      integrateForm cube (fun y => extDeriv P.localForm y) :=
  P.toOpenExtensionInput.chain_stokes

/-- Boundary Stokes in the local-data statement shape used by the congruence layer. -/
theorem local_boundary_stokes_via_integralCongruence :
    SingularCubeStokes.bdryIntegral_singular P.localData.cube P.localData.localForm =
      integrateForm P.localData.cube (fun y => extDeriv P.localData.localForm y) :=
  P.toLocalExtensionInput.singular_boundary_stokes_local

/-- Chain Stokes in the local-data statement shape used by the congruence layer. -/
theorem local_chain_stokes_via_integralCongruence :
    integrateChain (singularBoundarySingle P.localData.cube) P.localData.localForm =
      integrateForm P.localData.cube (fun y => extDeriv P.localData.localForm y) :=
  P.toLocalExtensionInput.singular_chain_stokes_local

/-- Compatibility wrapper with the older global-local-form facade. -/
theorem boundary_stokes_if_chartLocalForm_globalTop
    (hglobal : ContDiff Real ⊤ P.localForm) :
    SingularCubeStokes.bdryIntegral_singular cube P.localForm =
      integrateForm cube (fun y => extDeriv P.localForm y) :=
  chartwise_singular_boundary_stokes_of_globalSmooth
    (I := I) (omega := omega) chart cube
    P.isOpen_smoothSet P.cube_mapsTo_smoothSet
    P.smoothSet_subset_chartTarget P.base.chartwiseSmooth hglobal

/-- Chain-level compatibility wrapper with the older global-local-form facade. -/
theorem chain_stokes_if_chartLocalForm_globalTop
    (hglobal : ContDiff Real ⊤ P.localForm) :
    integrateChain (singularBoundarySingle cube) P.localForm =
      integrateForm cube (fun y => extDeriv P.localForm y) :=
  chartwise_singular_chain_stokes_of_globalSmooth
    (I := I) (omega := omega) chart cube
    P.isOpen_smoothSet P.cube_mapsTo_smoothSet
    P.smoothSet_subset_chartTarget P.base.chartwiseSmooth hglobal

/-- Existing top-upgrade existential output. -/
theorem exists_topUpgradeBridge
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    ExistsChartwiseSingularCubeCutoffTopUpgradeBridge
      (I := I) omega chart cube :=
  ⟨P.base, P.toTopUpgradeBridge, trivial⟩

/-- Existing cutoff-top existential output. -/
theorem exists_cutoffTopExtensionInput
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    ExistsChartwiseSingularCubeCutoffTopExtensionInput omega chart cube :=
  P.toTopUpgradeBridge.exists_cutoffTopExtensionInput

/-- Existing compact-extension existential output. -/
theorem exists_compactExtensionInput
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    ExistsChartwiseSingularCubeCompactExtensionInput omega chart cube :=
  P.toTopUpgradeBridge.exists_compactExtensionInput

/-- Existing open-extension existential output. -/
theorem exists_openExtensionInput
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    ExistsChartwiseSingularCubeOpenExtensionInput omega chart cube :=
  ⟨P.toOpenExtensionInput, trivial⟩

end ChartwiseSingularCubeTopStokesPublicInput

/-- Existential output shape for the public singular-cube top-smoothness facade. -/
def ExistsChartwiseSingularCubeTopStokesPublicInput
    (omega : ManifoldForm I M n)
    (chart : M) (cube : SmoothSingularCube (n + 1) m) : Prop :=
  ∃ _P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube, True

/-- Convert the public existential to the existing top-upgrade bridge existential. -/
theorem exists_topUpgradeBridge_of_publicInput
    (hP :
      ExistsChartwiseSingularCubeTopStokesPublicInput
        (I := I) omega chart cube) :
    ExistsChartwiseSingularCubeCutoffTopUpgradeBridge
      (I := I) omega chart cube := by
  rcases hP with ⟨P, _⟩
  exact P.exists_topUpgradeBridge

/-- Convert the public existential to the older cutoff-top existential. -/
theorem exists_cutoffTopExtensionInput_of_publicInput
    (hP :
      ExistsChartwiseSingularCubeTopStokesPublicInput
        (I := I) omega chart cube) :
    ExistsChartwiseSingularCubeCutoffTopExtensionInput omega chart cube := by
  rcases hP with ⟨P, _⟩
  exact P.exists_cutoffTopExtensionInput

/-- Convert the public existential to the compact-extension existential. -/
theorem exists_compactExtensionInput_of_publicInput
    (hP :
      ExistsChartwiseSingularCubeTopStokesPublicInput
        (I := I) omega chart cube) :
    ExistsChartwiseSingularCubeCompactExtensionInput omega chart cube := by
  rcases hP with ⟨P, _⟩
  exact P.exists_compactExtensionInput

/-- Convert the public existential to the open-extension existential. -/
theorem exists_openExtensionInput_of_publicInput
    (hP :
      ExistsChartwiseSingularCubeTopStokesPublicInput
        (I := I) omega chart cube) :
    ExistsChartwiseSingularCubeOpenExtensionInput omega chart cube := by
  rcases hP with ⟨P, _⟩
  exact P.exists_openExtensionInput

/-- Boundary Stokes from the public top-smoothness facade. -/
theorem chartwise_singular_boundary_stokes_of_topStokesPublicInput
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  P.boundary_stokes

/-- Chain Stokes from the public top-smoothness facade. -/
theorem chartwise_singular_chain_stokes_of_topStokesPublicInput
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (P : ChartwiseSingularCubeTopStokesPublicInput omega chart cube) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  P.chain_stokes

/-- Boundary Stokes from the public existential output shape. -/
theorem chartwise_singular_boundary_stokes_of_exists_topStokesPublicInput
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (hP :
      ExistsChartwiseSingularCubeTopStokesPublicInput
        (I := I) omega chart cube) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  rcases hP with ⟨P, _⟩
  exact chartwise_singular_boundary_stokes_of_topStokesPublicInput chart cube P

/-- Chain Stokes from the public existential output shape. -/
theorem chartwise_singular_chain_stokes_of_exists_topStokesPublicInput
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (hP :
      ExistsChartwiseSingularCubeTopStokesPublicInput
        (I := I) omega chart cube) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  rcases hP with ⟨P, _⟩
  exact chartwise_singular_chain_stokes_of_topStokesPublicInput chart cube P

/-- Build the public input directly from a cutoff-extension input and the single
top-smoothness proof, then invoke boundary Stokes. -/
theorem chartwise_singular_boundary_stokes_of_base_top
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : GeneratedExtensionTopSmoothness E) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  (ChartwiseSingularCubeTopStokesPublicInput.ofBase
    (I := I) E htop).boundary_stokes

/-- Build the public input directly from a cutoff-extension input and the single
top-smoothness proof, then invoke chain Stokes. -/
theorem chartwise_singular_chain_stokes_of_base_top
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : GeneratedExtensionTopSmoothness E) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  (ChartwiseSingularCubeTopStokesPublicInput.ofBase
    (I := I) E htop).chain_stokes

/-- Public boundary-Stokes wrapper from the existing compressed top bridge. -/
theorem chartwise_singular_boundary_stokes_of_existing_topUpgradeBridge
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube}
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  (ChartwiseSingularCubeTopStokesPublicInput.ofTopUpgradeBridge
    (I := I) B).boundary_stokes

/-- Public chain-Stokes wrapper from the existing compressed top bridge. -/
theorem chartwise_singular_chain_stokes_of_existing_topUpgradeBridge
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube}
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  (ChartwiseSingularCubeTopStokesPublicInput.ofTopUpgradeBridge
    (I := I) B).chain_stokes

end PublicInput

end SingularCubeTopStokesFacade
end SingularCubeSmoothExtensionAudit
end Stokes

end
