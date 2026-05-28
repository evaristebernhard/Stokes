import Stokes.SingularCube.CutoffExtensionMegaAuto
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# ContDiff top-upgrade bridge for singular-cube cutoff extension

`CutoffExtensionMegaAuto` constructs a genuine cutoff extension and proves that
the generated Euclidean form is `C∞`, i.e. `ContDiff Real ∞`.  The current
smooth-singular Stokes engine still asks for `ContDiff Real ⊤`, the analytic/top
level in mathlib's `ContDiff` hierarchy.  There is no sound bridge from `∞` to
`⊤`; the monotonicity theorem goes in the opposite direction.

This module therefore compresses the remaining obligation to a single explicit
field:

```
ContDiff Real ⊤ generatedExtension
```

All cutoff construction data, carrier containment, agreement on the carrier, and
boundary/chain Stokes wrappers are then generated automatically from that one
field.  This keeps the analytic gap honest while removing the surrounding
bookkeeping from downstream singular-cube code.
-/

noncomputable section

open Set Function Filter
open scoped Manifold Topology ContDiff

namespace Stokes
namespace SingularCubeSmoothExtensionAudit

section GeneralContDiffBridge

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace Real E]
variable [NormedAddCommGroup F] [NormedSpace Real F]
variable {f : E → F} {s : Set E} {x : E}

/-- A `ContDiff Real ⊤` function is `C∞`.  This is the usable direction of the
mathlib monotonicity API for the current cutoff-extension gap. -/
theorem contDiff_infty_of_contDiff_top
    (h : ContDiff Real ⊤ f) :
    ContDiff Real ∞ f :=
  h.of_le le_top

/-- Pointwise version of `contDiff_infty_of_contDiff_top`. -/
theorem contDiffAt_infty_of_contDiffAt_top
    (h : ContDiffAt Real ⊤ f x) :
    ContDiffAt Real ∞ f x :=
  h.of_le le_top

/-- Within-at version of `contDiff_infty_of_contDiff_top`. -/
theorem contDiffWithinAt_infty_of_contDiffWithinAt_top
    (h : ContDiffWithinAt Real ⊤ f s x) :
    ContDiffWithinAt Real ∞ f s x :=
  h.of_le le_top

/-- On-set version of `contDiff_infty_of_contDiff_top`. -/
theorem contDiffOn_infty_of_contDiffOn_top
    (h : ContDiffOn Real ⊤ f s) :
    ContDiffOn Real ∞ f s :=
  h.of_le le_top

/-- A theorem-facing record for the only sound bridge currently available:
`⊤`-smoothness, together with its automatic `∞` downgrade. -/
structure ContDiffTopBridge (f : E → F) where
  contDiff_top : ContDiff Real ⊤ f

namespace ContDiffTopBridge

variable {f : E → F}

/-- Build the bridge from the actual top-smoothness proof. -/
def ofTop (h : ContDiff Real ⊤ f) : ContDiffTopBridge f where
  contDiff_top := h

/-- The automatic `C∞` consequence of a top bridge. -/
theorem contDiff_infty (B : ContDiffTopBridge f) :
    ContDiff Real ∞ f :=
  contDiff_infty_of_contDiff_top B.contDiff_top

/-- Top smoothness at every point. -/
theorem contDiffAt_top (B : ContDiffTopBridge f) (x : E) :
    ContDiffAt Real ⊤ f x :=
  B.contDiff_top.contDiffAt

/-- `C∞` smoothness at every point. -/
theorem contDiffAt_infty (B : ContDiffTopBridge f) (x : E) :
    ContDiffAt Real ∞ f x :=
  B.contDiff_infty.contDiffAt

/-- Top smoothness on any set. -/
theorem contDiffOn_top (B : ContDiffTopBridge f) (s : Set E) :
    ContDiffOn Real ⊤ f s :=
  B.contDiff_top.contDiffOn

/-- `C∞` smoothness on any set. -/
theorem contDiffOn_infty (B : ContDiffTopBridge f) (s : Set E) :
    ContDiffOn Real ∞ f s :=
  B.contDiff_infty.contDiffOn

/-- Continuous consequence of the top bridge. -/
theorem continuous (B : ContDiffTopBridge f) :
    Continuous f :=
  B.contDiff_top.continuous

@[simp]
theorem ofTop_contDiff_top (h : ContDiff Real ⊤ f) :
    (ofTop h).contDiff_top = h :=
  rfl

end ContDiffTopBridge

/-- A paired view of the cutoff-extension gap: the `C∞` fact is already known,
and `contDiff_top` is the single remaining extra field. -/
structure ContDiffTopUpgradeFromInfty (f : E → F) where
  contDiff_infty : ContDiff Real ∞ f
  contDiff_top : ContDiff Real ⊤ f

namespace ContDiffTopUpgradeFromInfty

variable {f : E → F}

/-- If a top proof is available, the `C∞` component is automatic. -/
def ofTop (h : ContDiff Real ⊤ f) :
    ContDiffTopUpgradeFromInfty f where
  contDiff_infty := contDiff_infty_of_contDiff_top h
  contDiff_top := h

/-- Attach a top proof to an already constructed `C∞` proof. -/
def ofInftyAndTop
    (hinfty : ContDiff Real ∞ f) (htop : ContDiff Real ⊤ f) :
    ContDiffTopUpgradeFromInfty f where
  contDiff_infty := hinfty
  contDiff_top := htop

/-- Forget the stored `C∞` proof and keep the actual bridge. -/
def toTopBridge (U : ContDiffTopUpgradeFromInfty f) :
    ContDiffTopBridge f :=
  ContDiffTopBridge.ofTop U.contDiff_top

/-- Pointwise top smoothness from an upgrade package. -/
theorem contDiffAt_top (U : ContDiffTopUpgradeFromInfty f) (x : E) :
    ContDiffAt Real ⊤ f x :=
  U.contDiff_top.contDiffAt

/-- Pointwise `C∞` smoothness from an upgrade package. -/
theorem contDiffAt_infty (U : ContDiffTopUpgradeFromInfty f) (x : E) :
    ContDiffAt Real ∞ f x :=
  U.contDiff_infty.contDiffAt

/-- On-set top smoothness from an upgrade package. -/
theorem contDiffOn_top (U : ContDiffTopUpgradeFromInfty f) (s : Set E) :
    ContDiffOn Real ⊤ f s :=
  U.contDiff_top.contDiffOn

/-- On-set `C∞` smoothness from an upgrade package. -/
theorem contDiffOn_infty (U : ContDiffTopUpgradeFromInfty f) (s : Set E) :
    ContDiffOn Real ∞ f s :=
  U.contDiff_infty.contDiffOn

/-- The stored `C∞` proof agrees propositionally with the downgrade produced by
the top proof.  This theorem is intentionally phrased as a theorem, not a simp
rule, because proofs of propositions should rarely be normalized by `simp`. -/
theorem has_automatic_infty (U : ContDiffTopUpgradeFromInfty f) :
    ContDiff Real ∞ f :=
  contDiff_infty_of_contDiff_top U.contDiff_top

@[simp]
theorem ofTop_contDiff_top (h : ContDiff Real ⊤ f) :
    (ofTop h).contDiff_top = h :=
  rfl

@[simp]
theorem ofTop_toTopBridge (h : ContDiff Real ⊤ f) :
    (ofTop h).toTopBridge = ContDiffTopBridge.ofTop h :=
  rfl

end ContDiffTopUpgradeFromInfty

end GeneralContDiffBridge

section EuclideanCutoffTopBridge

variable {m n : Nat}
variable {K outer : Set (Fin m → Real)}
variable {S : CompactCarrierCutoffShrink (m := m) K outer}
variable {omega : EuclideanForm m n}

/-- Top-smoothness bridge for a scalar cutoff.  The generated cutoff in
`CutoffExtensionMegaAuto` supplies `ContDiff Real ∞`; this record is useful only
when a caller has a stronger `ContDiff Real ⊤` proof for the same cutoff. -/
structure EuclideanCutoffFunctionTopBridge
    {K outer : Set (Fin m → Real)}
    {S : CompactCarrierCutoffShrink (m := m) K outer}
    (C : EuclideanCutoffFunctionData S) where
  contDiff_top_cutoff : ContDiff Real ⊤ C.cutoff

namespace EuclideanCutoffFunctionTopBridge

variable {C : EuclideanCutoffFunctionData S}

/-- Constructor from the explicit top-smoothness field. -/
def ofTop (h : ContDiff Real ⊤ C.cutoff) :
    EuclideanCutoffFunctionTopBridge C where
  contDiff_top_cutoff := h

/-- The top bridge downgrades to the `C∞` smoothness stored in the cutoff data
shape expected by mathlib's cutoff API. -/
theorem contDiff_infty_cutoff
    (B : EuclideanCutoffFunctionTopBridge C) :
    ContDiff Real ∞ C.cutoff :=
  contDiff_infty_of_contDiff_top B.contDiff_top_cutoff

/-- Top smoothness at a point. -/
theorem contDiffAt_top_cutoff
    (B : EuclideanCutoffFunctionTopBridge C) (x : Fin m → Real) :
    ContDiffAt Real ⊤ C.cutoff x :=
  B.contDiff_top_cutoff.contDiffAt

/-- `C∞` smoothness at a point. -/
theorem contDiffAt_infty_cutoff
    (B : EuclideanCutoffFunctionTopBridge C) (x : Fin m → Real) :
    ContDiffAt Real ∞ C.cutoff x :=
  B.contDiff_infty_cutoff.contDiffAt

@[simp]
theorem ofTop_contDiff_top_cutoff
    (h : ContDiff Real ⊤ C.cutoff) :
    (ofTop h).contDiff_top_cutoff = h :=
  rfl

end EuclideanCutoffFunctionTopBridge

/-- The Euclidean cutoff-extension package with the top-smoothness upgrade
isolated as a single field. -/
structure EuclideanFormCutoffTopUpgradePackage
    (omega : EuclideanForm m n)
    {K outer : Set (Fin m → Real)}
    (S : CompactCarrierCutoffShrink (m := m) K outer) where
  base : EuclideanFormCutoffSmoothPackage omega S
  contDiff_top_omegaExt : ContDiff Real ⊤ base.omegaExt

namespace EuclideanFormCutoffTopUpgradePackage

variable {S : CompactCarrierCutoffShrink (m := m) K outer}
variable {omega : EuclideanForm m n}

/-- Constructor from an already generated smooth package and the single top
smoothness field still needed by the singular-cube engine. -/
def ofSmoothPackage
    (P : EuclideanFormCutoffSmoothPackage omega S)
    (htop : ContDiff Real ⊤ P.omegaExt) :
    EuclideanFormCutoffTopUpgradePackage omega S where
  base := P
  contDiff_top_omegaExt := htop

/-- Constructor from raw cutoff data, local smoothness, and the explicit top
proof for the generated cutoff-smul form. -/
def ofCutoffData
    (houter : IsOpen outer)
    (homega : ContDiffOn Real ∞ omega outer)
    (C : EuclideanCutoffFunctionData S)
    (htop : ContDiff Real ⊤ (cutoffSmulForm C omega)) :
    EuclideanFormCutoffTopUpgradePackage omega S :=
  ofSmoothPackage
    (EuclideanFormCutoffSmoothPackage.ofCutoffData houter homega C)
    (by simpa using htop)

/-- Constructor using the noncomputable cutoff generated by mathlib, plus the
one remaining top-smoothness proof for the generated extension. -/
def ofContDiffOn
    (houter : IsOpen outer)
    (homega : ContDiffOn Real ∞ omega outer)
    (htop :
      ContDiff Real ⊤
        (cutoffSmulForm (euclideanCutoffFunctionData S) omega)) :
    EuclideanFormCutoffTopUpgradePackage omega S :=
  ofCutoffData houter homega (euclideanCutoffFunctionData S) htop

/-- The generated extension. -/
abbrev omegaExt
    (P : EuclideanFormCutoffTopUpgradePackage omega S) :
    EuclideanForm m n :=
  P.base.omegaExt

/-- The scalar cutoff used by the generated extension. -/
abbrev cutoffData
    (P : EuclideanFormCutoffTopUpgradePackage omega S) :
    EuclideanCutoffFunctionData S :=
  P.base.cutoffData

/-- The stored `C∞` smoothness of the generated extension. -/
theorem contDiff_infty_omegaExt
    (P : EuclideanFormCutoffTopUpgradePackage omega S) :
    ContDiff Real ∞ P.omegaExt :=
  P.base.contDiff_omegaExt

/-- The top bridge for the generated extension. -/
def topBridge
    (P : EuclideanFormCutoffTopUpgradePackage omega S) :
    ContDiffTopBridge P.omegaExt :=
  ContDiffTopBridge.ofTop P.contDiff_top_omegaExt

/-- The paired `C∞`/top view of the generated extension. -/
def topUpgrade
    (P : EuclideanFormCutoffTopUpgradePackage omega S) :
    ContDiffTopUpgradeFromInfty P.omegaExt :=
  ContDiffTopUpgradeFromInfty.ofInftyAndTop
    P.contDiff_infty_omegaExt P.contDiff_top_omegaExt

/-- The top bridge downgrades to a `C∞` proof without using the stored one. -/
theorem contDiff_infty_omegaExt_of_top
    (P : EuclideanFormCutoffTopUpgradePackage omega S) :
    ContDiff Real ∞ P.omegaExt :=
  contDiff_infty_of_contDiff_top P.contDiff_top_omegaExt

/-- The generated extension agrees with the original form on the inner set. -/
theorem agreesOn_inner
    (P : EuclideanFormCutoffTopUpgradePackage omega S) :
    EqOn P.omegaExt omega S.inner :=
  P.base.agreesOn_inner

/-- The generated extension agrees with the original form on the compact
carrier. -/
theorem agreesOn_carrier
    (P : EuclideanFormCutoffTopUpgradePackage omega S) :
    EqOn P.omegaExt omega K :=
  P.base.agreesOn_carrier

/-- Pointwise agreement on the inner set. -/
theorem omegaExt_eq_of_mem_inner
    (P : EuclideanFormCutoffTopUpgradePackage omega S)
    {x : Fin m → Real} (hx : x ∈ S.inner) :
    P.omegaExt x = omega x :=
  P.base.omegaExt_eq_of_mem_inner hx

/-- Pointwise agreement on the carrier. -/
theorem omegaExt_eq_of_mem_carrier
    (P : EuclideanFormCutoffTopUpgradePackage omega S)
    {x : Fin m → Real} (hx : x ∈ K) :
    P.omegaExt x = omega x :=
  P.base.omegaExt_eq_of_mem_carrier hx

/-- Explicit formula for the generated extension. -/
theorem omegaExt_apply
    (P : EuclideanFormCutoffTopUpgradePackage omega S)
    (x : Fin m → Real) :
    P.omegaExt x = P.cutoffData.cutoff x • omega x :=
  P.base.omegaExt_apply x

/-- The original local smoothness on the outer set. -/
theorem contDiffOn_omega_outer
    (P : EuclideanFormCutoffTopUpgradePackage omega S) :
    ContDiffOn Real ∞ omega outer :=
  P.base.contDiffOn_omega_outer

/-- The outer set is open. -/
theorem isOpen_outer
    (P : EuclideanFormCutoffTopUpgradePackage omega S) :
    IsOpen outer :=
  P.base.isOpen_outer

@[simp]
theorem ofSmoothPackage_base
    (P : EuclideanFormCutoffSmoothPackage omega S)
    (htop : ContDiff Real ⊤ P.omegaExt) :
    (ofSmoothPackage P htop).base = P :=
  rfl

@[simp]
theorem ofSmoothPackage_contDiff_top
    (P : EuclideanFormCutoffSmoothPackage omega S)
    (htop : ContDiff Real ⊤ P.omegaExt) :
    (ofSmoothPackage P htop).contDiff_top_omegaExt = htop :=
  rfl

@[simp]
theorem ofCutoffData_base_omegaExt
    (houter : IsOpen outer)
    (homega : ContDiffOn Real ∞ omega outer)
    (C : EuclideanCutoffFunctionData S)
    (htop : ContDiff Real ⊤ (cutoffSmulForm C omega)) :
    (ofCutoffData (S := S) houter homega C htop).base.omegaExt =
      cutoffSmulForm C omega :=
  rfl

@[simp]
theorem ofContDiffOn_cutoffData
    (houter : IsOpen outer)
    (homega : ContDiffOn Real ∞ omega outer)
    (htop :
      ContDiff Real ⊤
        (cutoffSmulForm (euclideanCutoffFunctionData S) omega)) :
    (ofContDiffOn (S := S) houter homega htop).cutoffData =
      euclideanCutoffFunctionData S :=
  rfl

end EuclideanFormCutoffTopUpgradePackage

end EuclideanCutoffTopBridge

section ChartwiseCutoffTopBridge

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n m : Nat}
variable {I : ModelWithCorners Real (Fin m → Real) H}
variable {omega : ManifoldForm I M n}
variable {chart : M} {cube : SmoothSingularCube (n + 1) m}

namespace ChartwiseSingularCubeCutoffExtensionInput

/-- The generated cutoff extension is already known to be `C∞`. -/
theorem contDiff_infty_omegaExt
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube) :
    ContDiff Real ∞ E.euclideanPackage.omegaExt :=
  E.euclideanPackage.contDiff_omegaExt

/-- The minimal extra proposition needed to feed the current singular-cube
Stokes engine. -/
def TopUpgradeRequirement
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube) : Prop :=
  ContDiff Real ⊤ E.euclideanPackage.omegaExt

/-- Convert a cutoff-extension input and the minimal top-upgrade proof to the
existing top-extension input. -/
def toCutoffTopExtensionInput
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube where
  base := E
  contDiff_top_omegaExt := htop

/-- Convert a cutoff-extension input and the minimal top-upgrade proof directly
to compact-carrier extension input. -/
def toCompactExtensionInputOfTopUpgrade
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    ChartwiseSingularCubeCompactExtensionInput omega chart cube :=
  (E.toCutoffTopExtensionInput htop).toCompactExtensionInput

/-- Convert a cutoff-extension input and the minimal top-upgrade proof directly
to core extension input. -/
def toCoreExtensionInputOfTopUpgrade
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    ChartwiseSingularCubeCoreExtensionInput omega chart cube :=
  (E.toCutoffTopExtensionInput htop).toCoreExtensionInput

/-- Convert a cutoff-extension input and the minimal top-upgrade proof directly
to open extension input. -/
def toOpenExtensionInputOfTopUpgrade
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    ChartwiseSingularCubeOpenExtensionInput omega chart cube :=
  (E.toCutoffTopExtensionInput htop).toOpenExtensionInput

/-- Boundary Stokes from a cutoff-extension input plus the single top-upgrade
field. -/
theorem boundary_stokes_of_topUpgrade
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  (E.toCutoffTopExtensionInput htop).boundary_stokes

/-- Chain Stokes from a cutoff-extension input plus the single top-upgrade
field. -/
theorem chain_stokes_of_topUpgrade
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  (E.toCutoffTopExtensionInput htop).chain_stokes

/-- The top-upgrade field also supplies a second `C∞` proof by downgrade. -/
theorem contDiff_infty_omegaExt_of_topUpgrade
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    ContDiff Real ∞ E.euclideanPackage.omegaExt :=
  contDiff_infty_of_contDiff_top htop

/-- Existential top-extension output from the minimal top-upgrade field. -/
theorem exists_cutoffTopExtensionInput_of_topUpgrade
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    ExistsChartwiseSingularCubeCutoffTopExtensionInput omega chart cube :=
  ⟨E.toCutoffTopExtensionInput htop, trivial⟩

@[simp]
theorem toCutoffTopExtensionInput_base
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    (E.toCutoffTopExtensionInput htop).base = E :=
  rfl

@[simp]
theorem toCutoffTopExtensionInput_contDiff_top
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    (E.toCutoffTopExtensionInput htop).contDiff_top_omegaExt = htop :=
  rfl

@[simp]
theorem toCompactExtensionInputOfTopUpgrade_omegaExt
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    (E.toCompactExtensionInputOfTopUpgrade htop).omegaExt =
      E.euclideanPackage.omegaExt :=
  rfl

@[simp]
theorem toCompactExtensionInputOfTopUpgrade_extensionSet
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    (E.toCompactExtensionInputOfTopUpgrade htop).extensionSet =
      E.cutoffShrink.inner :=
  rfl

@[simp]
theorem toCompactExtensionInputOfTopUpgrade_compactCarrier
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    (E.toCompactExtensionInputOfTopUpgrade htop).compactCarrier =
      E.compactCarrier :=
  rfl

@[simp]
theorem toOpenExtensionInputOfTopUpgrade_extensionSet
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube)
    (htop : E.TopUpgradeRequirement) :
    (E.toOpenExtensionInputOfTopUpgrade htop).extensionSet =
      E.cutoffShrink.inner :=
  rfl

end ChartwiseSingularCubeCutoffExtensionInput

/-- Minimal bridge package for the current cutoff-extension analytic gap.  It is
parameterized by the already constructed `C∞` cutoff input, so the only new
field is exactly the top smoothness proof required by the current Stokes
engine. -/
structure ChartwiseSingularCubeCutoffTopUpgradeBridge
    (E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube) where
  contDiff_top_omegaExt : E.TopUpgradeRequirement

namespace ChartwiseSingularCubeCutoffTopUpgradeBridge

variable {E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube}

/-- Constructor from the single remaining field. -/
def ofTop
    (htop : E.TopUpgradeRequirement) :
    ChartwiseSingularCubeCutoffTopUpgradeBridge E where
  contDiff_top_omegaExt := htop

/-- The original cutoff-extension input. -/
abbrev base
    (_B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ChartwiseSingularCubeCutoffExtensionInput omega chart cube :=
  E

/-- The generated Euclidean top bridge. -/
def topBridge
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ContDiffTopBridge E.euclideanPackage.omegaExt :=
  ContDiffTopBridge.ofTop B.contDiff_top_omegaExt

/-- The paired `C∞`/top upgrade for the generated Euclidean extension. -/
def topUpgrade
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ContDiffTopUpgradeFromInfty E.euclideanPackage.omegaExt :=
  ContDiffTopUpgradeFromInfty.ofInftyAndTop
    E.contDiff_infty_omegaExt B.contDiff_top_omegaExt

/-- Convert the bridge to the existing top-extension input. -/
def toCutoffTopExtensionInput
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ChartwiseSingularCubeCutoffTopExtensionInput omega chart cube :=
  E.toCutoffTopExtensionInput B.contDiff_top_omegaExt

/-- Convert the bridge to compact-carrier extension input. -/
def toCompactExtensionInput
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ChartwiseSingularCubeCompactExtensionInput omega chart cube :=
  B.toCutoffTopExtensionInput.toCompactExtensionInput

/-- Convert the bridge to core extension input. -/
def toCoreExtensionInput
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ChartwiseSingularCubeCoreExtensionInput omega chart cube :=
  B.toCutoffTopExtensionInput.toCoreExtensionInput

/-- Convert the bridge to open extension input. -/
def toOpenExtensionInput
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ChartwiseSingularCubeOpenExtensionInput omega chart cube :=
  B.toCutoffTopExtensionInput.toOpenExtensionInput

/-- The original `C∞` result produced by the cutoff construction. -/
theorem contDiff_infty_omegaExt
    (_B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ContDiff Real ∞ E.euclideanPackage.omegaExt :=
  E.contDiff_infty_omegaExt

/-- The `C∞` result obtained by downgrading the top field. -/
theorem contDiff_infty_omegaExt_of_top
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ContDiff Real ∞ E.euclideanPackage.omegaExt :=
  contDiff_infty_of_contDiff_top B.contDiff_top_omegaExt

/-- Agreement of the generated extension on the cutoff inner set. -/
theorem agreesOn_inner
    (_B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    EqOn E.euclideanPackage.omegaExt
      (chartLocalForm I chart omega) E.cutoffShrink.inner :=
  E.omegaExt_agreesOn_inner

/-- Agreement of the generated extension on the compact carrier. -/
theorem agreesOn_carrier
    (_B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    EqOn E.euclideanPackage.omegaExt
      (chartLocalForm I chart omega) E.compactCarrier.carrier :=
  E.omegaExt_agreesOn_carrier

/-- The full cube image lands in the extension set. -/
theorem cube_mem_extensionSet
    (_B : ChartwiseSingularCubeCutoffTopUpgradeBridge E)
    {x : Fin (n + 1) → Real}
    (hx : x ∈ singularParameterCube (n + 1)) :
    cube.toFun x ∈ E.cutoffShrink.inner :=
  E.cube_mem_extensionSet hx

/-- A high face lands in the extension set. -/
theorem highFace_mem_extensionSet
    (_B : ChartwiseSingularCubeCutoffTopUpgradeBridge E)
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 1).toFun x ∈ E.cutoffShrink.inner :=
  E.highFace_mem_extensionSet i hx

/-- A low face lands in the extension set. -/
theorem lowFace_mem_extensionSet
    (_B : ChartwiseSingularCubeCutoffTopUpgradeBridge E)
    (i : Fin (n + 1)) {x : Fin n → Real}
    (hx : x ∈ singularParameterCube n) :
    (singularFace cube i 0).toFun x ∈ E.cutoffShrink.inner :=
  E.lowFace_mem_extensionSet i hx

/-- Boundary Stokes from the minimal bridge. -/
theorem boundary_stokes
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  B.toCutoffTopExtensionInput.boundary_stokes

/-- Chain Stokes from the minimal bridge. -/
theorem chain_stokes
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  B.toCutoffTopExtensionInput.chain_stokes

/-- Existential top-extension output from the minimal bridge. -/
theorem exists_cutoffTopExtensionInput
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ExistsChartwiseSingularCubeCutoffTopExtensionInput omega chart cube :=
  ⟨B.toCutoffTopExtensionInput, trivial⟩

/-- Existential compact-extension output from the minimal bridge. -/
theorem exists_compactExtensionInput
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    ExistsChartwiseSingularCubeCompactExtensionInput omega chart cube :=
  ⟨B.toCompactExtensionInput, trivial⟩

@[simp]
theorem ofTop_contDiff_top
    (htop : E.TopUpgradeRequirement) :
    (ofTop (E := E) htop).contDiff_top_omegaExt = htop :=
  rfl

@[simp]
theorem toCutoffTopExtensionInput_base
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    B.toCutoffTopExtensionInput.base = E :=
  rfl

@[simp]
theorem toCutoffTopExtensionInput_contDiff_top
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    B.toCutoffTopExtensionInput.contDiff_top_omegaExt =
      B.contDiff_top_omegaExt :=
  rfl

@[simp]
theorem toCompactExtensionInput_omegaExt
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    B.toCompactExtensionInput.omegaExt = E.euclideanPackage.omegaExt :=
  rfl

@[simp]
theorem toCompactExtensionInput_extensionSet
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    B.toCompactExtensionInput.extensionSet = E.cutoffShrink.inner :=
  rfl

@[simp]
theorem toCompactExtensionInput_compactCarrier
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    B.toCompactExtensionInput.compactCarrier = E.compactCarrier :=
  rfl

@[simp]
theorem toCoreExtensionInput_omegaExt
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    B.toCoreExtensionInput.omegaExt = E.euclideanPackage.omegaExt :=
  rfl

@[simp]
theorem toOpenExtensionInput_extensionSet
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    B.toOpenExtensionInput.extensionSet = E.cutoffShrink.inner :=
  rfl

end ChartwiseSingularCubeCutoffTopUpgradeBridge

/-- Existential shape for the compressed top-upgrade bridge. -/
def ExistsChartwiseSingularCubeCutoffTopUpgradeBridge
    (omega : ManifoldForm I M n)
    (chart : M) (cube : SmoothSingularCube (n + 1) m) : Prop :=
  ∃ E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube,
    ∃ _B : ChartwiseSingularCubeCutoffTopUpgradeBridge E, True

/-- Convert the compressed bridge existential to the older top-extension
existential shape. -/
theorem exists_cutoffTopExtensionInput_of_exists_topUpgradeBridge
    (h :
      ExistsChartwiseSingularCubeCutoffTopUpgradeBridge
        (I := I) omega chart cube) :
    ExistsChartwiseSingularCubeCutoffTopExtensionInput omega chart cube := by
  rcases h with ⟨E, B, _⟩
  exact B.exists_cutoffTopExtensionInput

/-- Convert the compressed bridge existential to compact-extension existential
shape. -/
theorem exists_compactExtensionInput_of_exists_topUpgradeBridge
    (h :
      ExistsChartwiseSingularCubeCutoffTopUpgradeBridge
        (I := I) omega chart cube) :
    ExistsChartwiseSingularCubeCompactExtensionInput omega chart cube := by
  rcases h with ⟨E, B, _⟩
  exact B.exists_compactExtensionInput

/-- Boundary Stokes from the compressed top-upgrade bridge. -/
theorem chartwise_singular_boundary_stokes_of_topUpgradeBridge
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube}
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  B.boundary_stokes

/-- Chain Stokes from the compressed top-upgrade bridge. -/
theorem chartwise_singular_chain_stokes_of_topUpgradeBridge
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    {E : ChartwiseSingularCubeCutoffExtensionInput omega chart cube}
    (B : ChartwiseSingularCubeCutoffTopUpgradeBridge E) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) :=
  B.chain_stokes

/-- Boundary Stokes from an existential compressed bridge. -/
theorem chartwise_singular_boundary_stokes_of_exists_topUpgradeBridge
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (h :
      ExistsChartwiseSingularCubeCutoffTopUpgradeBridge
        (I := I) omega chart cube) :
    SingularCubeStokes.bdryIntegral_singular cube (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  rcases h with ⟨E, B, _⟩
  exact chartwise_singular_boundary_stokes_of_topUpgradeBridge chart cube B

/-- Chain Stokes from an existential compressed bridge. -/
theorem chartwise_singular_chain_stokes_of_exists_topUpgradeBridge
    (chart : M) (cube : SmoothSingularCube (n + 1) m)
    (h :
      ExistsChartwiseSingularCubeCutoffTopUpgradeBridge
        (I := I) omega chart cube) :
    integrateChain (singularBoundarySingle cube) (chartLocalForm I chart omega) =
      integrateForm cube (fun y => extDeriv (chartLocalForm I chart omega) y) := by
  rcases h with ⟨E, B, _⟩
  exact chartwise_singular_chain_stokes_of_topUpgradeBridge chart cube B

end ChartwiseCutoffTopBridge

end SingularCubeSmoothExtensionAudit
end Stokes

end
