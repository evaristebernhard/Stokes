import Stokes.BoundaryChart.ConstrainedTargetBoxSelectionAuto
import Stokes.BoundaryChart.TargetBoxSourceShrinkIFT

/-!
# Controlled target boxes from local-inverse data

`ConstrainedTargetBoxSelectionAuto` fixed the right downstream API for boundary
chart-change target boxes: instead of quantifying over every later target, pick
one controlled target box and remember the compact-image/local-inverse data on
that exact box.

This file supplies constructor-facing bridges from the existing local-inverse
and source-shrink APIs to that controlled target record.  No change-of-variables
proofs are reproved here; the goal is only to materialize the target corners,
membership/neighborhood fields, set containment, and the image-data halves in a
single reusable package.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartTargetBoxSelection

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b selectedLower selectedUpper : Fin (n + 1) → Real}
variable {y : Fin n → Real} {U : Set (Fin n → Real)}

/--
Turn a selected target-box record into controlled target data, with the
containing-box inequalities supplied explicitly.
-/
def toControlledTargetBoxSelection
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hy : y ∈ lowerZeroFaceDomain target.lowerCorner target.upperCorner)
    (hnhds : lowerZeroFaceDomain target.lowerCorner target.upperCorner ∈ 𝓝 y)
    (hsubset : lowerZeroFaceDomain target.lowerCorner target.upperCorner ⊆ U)
    (hlower : ∀ i : Fin n, target.lowerCorner i.succ ≤ selectedLower i.succ)
    (hupper : ∀ i : Fin n, selectedUpper i.succ ≤ target.upperCorner i.succ) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b selectedLower selectedUpper y U :=
  BoundaryChartControlledTargetBoxSelectionData.ofTargetBoxSelection
    target hy hnhds hsubset hlower hupper

/--
Use a target-box selection as the controlled box itself.  This is the common
local-inverse route: the selected target and the controlled later target have
the same corners.
-/
def toControlledTargetBoxSelectionSelf
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b)
    (hy : y ∈ lowerZeroFaceDomain target.lowerCorner target.upperCorner)
    (hnhds : lowerZeroFaceDomain target.lowerCorner target.upperCorner ∈ 𝓝 y)
    (hsubset : lowerZeroFaceDomain target.lowerCorner target.upperCorner ⊆ U) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 a b target.lowerCorner target.upperCorner y U :=
  target.toControlledTargetBoxSelection hy hnhds hsubset
    (fun _ => le_rfl) (fun _ => le_rfl)

end BoundaryChartTargetBoxSelection

/--
Local openness plus compact-image control produces a controlled target box
inside any prescribed target-side neighborhood `U`.

The selected target corners in the output are the corners chosen by the
lower-zero neighborhood basis; hence the controlled target contains the
selected target by reflexivity.
-/
theorem exists_controlledTargetBoxSelection_of_localOpenness_compactImage_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    {y : Fin n → Real} {U : Set (Fin n → Real)}
    (hU : U ∈ 𝓝 y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hcompact :
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d y U,
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d := by
  have hinter :
      (U ∩ (boundaryChartTransition I x0 x1) ''
          lowerZeroFaceDomain a b) ∈ 𝓝 y :=
    inter_mem hU himage
  rcases exists_lowerZeroFaceDomain_mem_nhds_subset_of_mem_nhds hinter with
    ⟨c, d, hc0, hle, hy, hnhds, hsubset_inter⟩
  have hsubset_U : lowerZeroFaceDomain c d ⊆ U := by
    intro z hz
    exact (hsubset_inter hz).1
  have hsubset_image :
      lowerZeroFaceDomain c d ⊆
        (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b := by
    intro z hz
    exact (hsubset_inter hz).2
  have hlocal : boundaryChartLocalInverseData I x0 x1 a b c d :=
    boundaryChartLocalInverseData.of_inverseImageBoxSelection hsubset_image
  let target : BoundaryChartTargetBoxSelection I x0 x1 a b :=
    BoundaryChartTargetBoxSelection.mkOfCompactCoordinateImageBoxSelection
      c d hc0 hle (hcompact c d hc0 hle hy hlocal) hlocal
  refine ⟨c, d, target.toControlledTargetBoxSelectionSelf hy hnhds hsubset_U, ?_, ?_⟩
  · rfl
  · rfl

/--
Local-openness version where the ambient set is the image neighborhood itself.
-/
theorem exists_controlledTargetBoxSelection_of_localOpenness_compactImage
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real} {y : Fin n → Real}
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hcompact :
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a b y) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d y
            ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b),
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_compactImage_subset
    (U := (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b)
    himage himage hcompact

namespace BoundaryChartContinuousLocalInverseData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b c d a' b' : Fin (n + 1) → Real}
variable {y : Fin n → Real}

/--
A named continuous local inverse can shrink the target box and, after compact
image control for that selected target, produce controlled target data inside
the original target box.
-/
theorem exists_controlledTargetBoxSelection
    (G : BoundaryChartContinuousLocalInverseData I x0 x1 a b c d y)
    (hsource : lowerZeroFaceDomain a' b' ∈ 𝓝 (G.invFun y))
    (htarget : lowerZeroFaceDomain c d ∈ 𝓝 y)
    (hcompact :
      boundaryChartCompactCoordinateImageForLocalInverseTargets I x0 x1 a' b' y) :
    ∃ e f : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a' b' e f y (lowerZeroFaceDomain c d),
        D.laterLowerCorner = e ∧ D.laterUpperCorner = f := by
  rcases G.exists_targetShrinkLocalInverseData hsource htarget with
    ⟨e, f, he0, hle, hy, hnhds, hsubset, hlocal⟩
  let target : BoundaryChartTargetBoxSelection I x0 x1 a' b' :=
    BoundaryChartTargetBoxSelection.mkOfCompactCoordinateImageBoxSelection
      e f he0 hle (hcompact e f he0 hle hy hlocal) hlocal
  refine ⟨e, f, target.toControlledTargetBoxSelectionSelf hy hnhds hsubset, ?_, ?_⟩
  · rfl
  · rfl

end BoundaryChartContinuousLocalInverseData

namespace BoundaryChartSourceShrinkInverseTargetBoxData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b c d e f selectedLower selectedUpper : Fin (n + 1) → Real}
variable {u y : Fin n → Real} {U : Set (Fin n → Real)}

/--
Completed source-shrink inverse-target data gives a controlled target as soon
as the caller supplies the target-neighborhood audit field and the containing
target-side set.
-/
def toControlledTargetBoxSelection
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hnhds : lowerZeroFaceDomain e f ∈ 𝓝 y)
    (hsubset : lowerZeroFaceDomain e f ⊆ U)
    (hlower : ∀ i : Fin n, e i.succ ≤ selectedLower i.succ)
    (hupper : ∀ i : Fin n, selectedUpper i.succ ≤ f i.succ) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 D.sourceLowerCorner D.sourceUpperCorner
        selectedLower selectedUpper y U :=
  D.targetBoxSelection.toControlledTargetBoxSelection
    D.targetPoint_mem hnhds hsubset hlower hupper

/--
Use the source-shrink selected target itself as the controlled target.
-/
def toControlledTargetBoxSelectionSelf
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hnhds : lowerZeroFaceDomain e f ∈ 𝓝 y)
    (hsubset : lowerZeroFaceDomain e f ⊆ U) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 D.sourceLowerCorner D.sourceUpperCorner e f y U :=
  D.targetBoxSelection.toControlledTargetBoxSelectionSelf
    D.targetPoint_mem hnhds hsubset

/--
Source-shrink inverse-target data controlled inside its ambient target box.
-/
def toControlledTargetBoxSelectionInAmbient
    (D : BoundaryChartSourceShrinkInverseTargetBoxData I x0 x1 a b c d e f u y)
    (hnhds : lowerZeroFaceDomain e f ∈ 𝓝 y) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 D.sourceLowerCorner D.sourceUpperCorner e f y
        (lowerZeroFaceDomain c d) :=
  D.toControlledTargetBoxSelectionSelf hnhds D.targetSubset_original

end BoundaryChartSourceShrinkInverseTargetBoxData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b c d selectedLower selectedUpper : Fin (n + 1) → Real}
variable {u y : Fin n → Real} {U : Set (Fin n → Real)}

/--
Open-partial-homeomorphism source-shrink data already stores the target
membership and target-neighborhood fields, so only the chosen ambient set and
containing bounds remain.
-/
def toControlledTargetBoxSelection
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hsubset :
      lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ⊆ U)
    (hlower :
      ∀ i : Fin n, D.targetLowerCorner i.succ ≤ selectedLower i.succ)
    (hupper :
      ∀ i : Fin n, selectedUpper i.succ ≤ D.targetUpperCorner i.succ) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 D.sourceLowerCorner D.sourceUpperCorner
        selectedLower selectedUpper y U :=
  D.targetBoxSelection.toControlledTargetBoxSelection
    D.targetPoint_mem D.target_mem_nhds hsubset hlower hupper

/--
Use the open-partial-homeomorphism selected target itself as the controlled
target.
-/
def toControlledTargetBoxSelectionSelf
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y)
    (hsubset :
      lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner ⊆ U) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 D.sourceLowerCorner D.sourceUpperCorner
        D.targetLowerCorner D.targetUpperCorner y U :=
  D.targetBoxSelection.toControlledTargetBoxSelectionSelf
    D.targetPoint_mem D.target_mem_nhds hsubset

/--
Open-partial-homeomorphism source-shrink data controlled inside its ambient
target box, with no extra neighborhood or subset arguments.
-/
def toControlledTargetBoxSelectionInAmbient
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    BoundaryChartControlledTargetBoxSelectionData
      I x0 x1 D.sourceLowerCorner D.sourceUpperCorner
        D.targetLowerCorner D.targetUpperCorner y (lowerZeroFaceDomain c d) :=
  D.toControlledTargetBoxSelectionSelf D.targetSubset_original

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
