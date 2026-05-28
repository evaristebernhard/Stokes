import Stokes.Global.BoundaryChartChangeFromCOVAuto
import Stokes.Global.BoundarySourceAlignmentUnified

/-!
# Boundary partition terms from resolved target-image data

This module removes the pointwise `boundaryPartitionTerm_eq` proof obligation
from the resolved target-image/project-local compatibility path in the
source-shrink/M8 route.

The key observation is that the M8 resolved fields already build the selected
boundary assembly.  Its existing pointwise chart-change theorem identifies the
transported local boundary term with the selected boundary partition term.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryPartitionTermFromResolvedTarget

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.M8ResolvedFields

variable
    {F :
      BoundaryChartSourceShrinkOpenPartialHomeomorphFamily I omega M
        BoundaryPiece}

/--
The M8 resolved fields identify their selected boundary partition term with
the transported target-image boundary integral.

This is the pointwise form needed by
`BoundaryChartTargetImageResolvedFamily.ProjectLocalCompatibility`: it follows
from the selected boundary assembly's chart-change theorem, using the oriented
atlas membership fields already packaged in `M8ResolvedFields`.
-/
theorem boundaryPartitionTerm_eq_targetIntegral_of_orientedAtlas
    [IsManifold I 1 M]
    (D :
      M8ResolvedFields F selectedPartition orientedBoundaryAtlas)
    (x : M) (hx : x ∈ F.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ F.localPieces x) :
    D.boundaryPartitionTerm x q =
      projectLocalBoundaryIntegral I
        (F.boundarySourceChart x q) (F.boundaryTargetChart x q) omega
        (F.targetLowerCorner x q) (F.targetUpperCorner x q) := by
  let A := D.toM8ResolvedInput.toAssemblyInput
  let S :=
    A.toSelectedBoundaryAssemblyData_of_orientedAtlas orientedBoundaryAtlas
      (by
        intro y hy r hr
        exact D.boundarySource_mem y hy r hr)
      (by
        intro y hy r hr
        exact D.boundaryTarget_mem y hy r hr)
  have hpoint :
      SelectedBoundaryAssemblyData.boundaryBoundaryTerm S x q =
        S.boundaryPartitionTerm x q :=
    S.pointwise_chartChange x (by simpa [S, A] using hx) q
      (by simpa [S, A] using hq)
  simpa [S, A, SelectedBoundaryAssemblyData.boundaryBoundaryTerm,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetLowerCorner,
    BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetUpperCorner] using
    hpoint.symm

end BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.M8ResolvedFields

namespace BoundarySourceAlignmentUnifiedData

variable
    (U :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece))

/--
Resolved target-image/project-local compatibility generated from unified
source-shrink/M8 data.

All source fields are definitional projections from `U.family`.  The boundary
partition term field is derived from the M8 resolved assembly chart-change
theorem above, so callers no longer have to prove this pointwise equality by
hand.
-/
def toResolvedProjectLocalCompatibilityOfOrientedAtlas
    [IsManifold I 1 M] :
    U.family.toTargetImageResolvedFamily.ProjectLocalCompatibility
      U.toProjectLocalGlobalStokesData where
  activeCharts_eq := rfl
  localPieces_eq := fun _ => rfl
  sourceChart_eq := fun _ _ => rfl
  targetChart_eq := fun _ _ => rfl
  lowerCorner_eq := fun _ _ => rfl
  upperCorner_eq := fun _ _ => rfl
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    simpa [BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.toTargetImageResolvedFamily,
      BoundaryChartTargetImageResolvedFamily.targetLowerCorner,
      BoundaryChartTargetImageResolvedFamily.targetUpperCorner,
      BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetBoxSelection,
      BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetLowerCorner,
      BoundaryChartSourceShrinkOpenPartialHomeomorphFamily.targetUpperCorner] using
      U.m8Fields.boundaryPartitionTerm_eq_targetIntegral_of_orientedAtlas
        x hx q hq

@[simp]
theorem toResolvedProjectLocalCompatibilityOfOrientedAtlas_boundaryPartitionTerm_eq
    [IsManifold I 1 M]
    (x : M) (hx : x ∈ U.family.activeCharts)
    (q : BoundaryPiece) (hq : q ∈ U.family.localPieces x) :
    (U.toResolvedProjectLocalCompatibilityOfOrientedAtlas
      (I := I) (omega := omega)).boundaryPartitionTerm_eq x hx q hq =
      U.m8Fields.boundaryPartitionTerm_eq_targetIntegral_of_orientedAtlas
        x hx q hq := by
  rfl

end BoundarySourceAlignmentUnifiedData

end BoundaryPartitionTermFromResolvedTarget

end Stokes

end
