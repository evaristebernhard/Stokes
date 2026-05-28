import Stokes.Global.CoverIndexedZeroCompactRepresentedStokesNatural

/-!
# Compact-support represented Stokes with a smaller public input

This module is a theorem-facing compression layer above
`CoverIndexedZeroCompactRepresentedStokesNatural`.  It keeps the remaining
geometric hypotheses honest, but removes two more internal packages from the
public theorem input:

* ambient-open data is built by a named constructor;
* the three coordinate-carrier chart-compatibility fields are derived from the
  generated active coordinate carrier plus an ambient-domain hypothesis; and
* image-control is supplied as explicit whole-box closed-preimage control,
  rather than as an `imageData` package.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section AmbientOpenData

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedZeroCompactFromCollarGenerated

variable
    (D :
      CoverIndexedZeroCompactFromCollarGenerated
        (I := I) (K := K) C P)

/--
Build the manifold-side ambient-open lift used by the smooth box refinement.

This constructor deliberately exposes only the genuine open-cover fields,
rather than asking callers to assemble `FiniteCoverAmbientOpenData` directly.
-/
def ambientOpenDataOfBoundaryChartBoxes
    (ambientOpen :
      CoverIndexedBoundaryIndex (I := I) C →
        D.BoundaryPiece (I := I) (K := K) → Set M)
    (ambientOpen_isOpen :
      ∀ i q, q ∈ D.boundaryPieces (I := I) (K := K) i →
        IsOpen (ambientOpen i q))
    (activeCarrier_subset_iUnion_ambientOpen :
      ∀ i : CoverIndexedBoundaryIndex (I := I) C,
        D.activeCarrier (I := I) (K := K) i ⊆
          ⋃ q ∈ D.boundaryPieces (I := I) (K := K) i, ambientOpen i q)
    (ambientOpen_subset_boundaryChartBox :
      ∀ i q, q ∈ D.boundaryPieces (I := I) (K := K) i →
        ambientOpen i q ⊆
          boundaryChartBoxNeighborhood I
            (D.sourceChart (I := I) (K := K) i q)
            (D.lower (I := I) (K := K) i q)
            (D.upper (I := I) (K := K) i q)) :
    D.FiniteCoverAmbientOpenData (I := I) (K := K) (C := C) (P := P) where
  ambientOpen := ambientOpen
  ambientOpen_isOpen := ambientOpen_isOpen
  activeCarrier_subset_iUnion_ambientOpen :=
    activeCarrier_subset_iUnion_ambientOpen
  ambientOpen_subset_boundaryChartBox :=
    ambientOpen_subset_boundaryChartBox

/-- The generated coordinate carrier lies in its coordinate-side ambient set. -/
theorem coordCarrier_subset_ambient
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    D.coordCarrier (I := I) (K := K) i ⊆ D.ambient i := by
  intro y hy
  let F := D.finiteHalfSpaceCover (I := I) (K := K) (C := C)
  have hcover :
      y ∈ ⋃ q : {q // q ∈ F.activePieces i},
        halfSpaceSupportBox (F.lowerCorner i q.1) (F.upperCorner i q.1) :=
    F.carrier_subset_iUnion i hy
  rcases mem_iUnion.mp hcover with ⟨q, hyq⟩
  exact F.sourceBox_subset_ambient i q.2 hyq

/--
Generated coordinate carriers map back into the compact support through their
selected source boundary chart.
-/
theorem coordCarrier_mapsTo_K_of_boundaryActiveCoordCarrier
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : Fin (n + 1) → Real)
    (_hq :
      q ∈ (D.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i) :
    ∀ y ∈ D.coordCarrier (I := I) (K := K) i,
      (extChartAt I
        (D.sourceChart (I := I) (K := K) i ⟨i, q⟩)).symm y ∈ K := by
  intro y hy
  have hy' :
      y ∈ chartCoordinateImage I (C.boundaryChart i.1)
        (P.boundaryActiveCarrier (I := I) i) := by
    simpa [coordCarrier, SupportControlledSelectedPartition.boundaryActiveCoordCarrier]
      using hy
  rcases hy' with ⟨x, hx, rfl⟩
  have hsource :
      x ∈ (extChartAt I (C.boundaryChart i.1)).source :=
    P.boundaryActiveCarrier_subset_chart_source (I := I) i hx
  have hsymm :
      (extChartAt I (C.boundaryChart i.1)).symm
          ((extChartAt I (C.boundaryChart i.1)) x) = x :=
    (extChartAt I (C.boundaryChart i.1)).left_inv hsource
  change
    (extChartAt I (C.boundaryChart i.1)).symm
        ((extChartAt I (C.boundaryChart i.1)) x) ∈ K
  exact hsymm.symm ▸ hx.2

/-- Generated coordinate carriers lie in the selected source chart target. -/
theorem coordCarrier_subset_sourceTarget_of_boundaryActiveCoordCarrier
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : Fin (n + 1) → Real)
    (_hq :
      q ∈ (D.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i) :
    D.coordCarrier (I := I) (K := K) i ⊆
      (extChartAt I
        (D.sourceChart (I := I) (K := K) i ⟨i, q⟩)).target := by
  simpa [sourceChart, coordCarrier,
    SupportControlledSelectedPartition.boundaryActiveCoordCarrier] using
    (chartCoordinateImage_subset_target
      (I := I) (x := C.boundaryChart i.1)
      (K := P.boundaryActiveCarrier (I := I) i)
      (P.boundaryActiveCarrier_subset_chart_source (I := I) i))

/-- If the ambient region lies in a boundary chart-transition domain, then the
generated coordinate carrier lies in the source/target overlap. -/
theorem coordCarrier_subset_overlap_of_ambientDomain
    (targetChart :
      CoverIndexedBoundaryIndex (I := I) C →
        (Fin (n + 1) → Real) → M)
    (ambient_subset_boundaryChartDomain :
      ∀ i q,
        q ∈ (D.finiteHalfSpaceCover
          (I := I) (K := K) (C := C)).activePieces i →
          D.ambient i ⊆
            boundaryChartDomain I
              (D.sourceChart (I := I) (K := K) i ⟨i, q⟩)
              (targetChart i q))
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : Fin (n + 1) → Real)
    (hq :
      q ∈ (D.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i) :
    D.coordCarrier (I := I) (K := K) i ⊆
      ManifoldForm.chartOverlap I
        (D.sourceChart (I := I) (K := K) i ⟨i, q⟩)
        (targetChart i q) := by
  intro y hy
  exact
    (boundaryChartDomain_subset_overlap I
      (D.sourceChart (I := I) (K := K) i ⟨i, q⟩)
      (targetChart i q))
      (ambient_subset_boundaryChartDomain i q hq
        (D.coordCarrier_subset_ambient (I := I) (K := K) i hy))

end CoverIndexedZeroCompactFromCollarGenerated

end AmbientOpenData

section ChartCompatibility

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
The remaining chart-transition compatibility data for the generated collar
cover.

The three older coordinate-carrier fields are not stored here: they are
generated from the active coordinate carrier and `ambient_subset_boundaryChartDomain`.
-/
structure CoverIndexedZeroCompactGeneratedChartCompatibility
    (D : CoverIndexedZeroCompactFromCollarGenerated (I := I) (K := K) C P) where
  /-- Target chart attached to each generated finite half-space box. -/
  targetChart :
    CoverIndexedBoundaryIndex (I := I) C →
      (Fin (n + 1) → Real) → M
  /-- Base transition-pullback support lies in the generated coordinate carrier. -/
  base_tsupport_subset_coordCarrier :
    ∀ i q,
      q ∈ (D.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (D.sourceChart (I := I) (K := K) i ⟨i, q⟩)
              (targetChart i q) ω) ⊆
          D.coordCarrier (I := I) (K := K) i
  /-- Ambient regions lie in the boundary chart-transition domain. -/
  ambient_subset_boundaryChartDomain :
    ∀ i q,
      q ∈ (D.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i →
        D.ambient i ⊆
          boundaryChartDomain I
            (D.sourceChart (I := I) (K := K) i ⟨i, q⟩)
            (targetChart i q)

namespace CoverIndexedZeroCompactGeneratedChartCompatibility

variable
    {D : CoverIndexedZeroCompactFromCollarGenerated (I := I) (K := K) C P}
    (G : CoverIndexedZeroCompactGeneratedChartCompatibility
      (I := I) (K := K) (ω := ω) (C := C) (P := P) D)

/-- Generated inverse-chart membership in the compact support. -/
theorem coordCarrier_mapsTo_K
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : Fin (n + 1) → Real)
    (hq :
      q ∈ (D.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i) :
    ∀ y ∈ D.coordCarrier (I := I) (K := K) i,
      (extChartAt I
        (D.sourceChart (I := I) (K := K) i ⟨i, q⟩)).symm y ∈ K :=
  D.coordCarrier_mapsTo_K_of_boundaryActiveCoordCarrier
    (I := I) (K := K) i q hq

/-- Generated source-target containment. -/
theorem coordCarrier_subset_sourceTarget
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : Fin (n + 1) → Real)
    (hq :
      q ∈ (D.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i) :
    D.coordCarrier (I := I) (K := K) i ⊆
      (extChartAt I
        (D.sourceChart (I := I) (K := K) i ⟨i, q⟩)).target :=
  D.coordCarrier_subset_sourceTarget_of_boundaryActiveCoordCarrier
    (I := I) (K := K) i q hq

/-- Generated source/target overlap containment. -/
theorem coordCarrier_subset_overlap
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : Fin (n + 1) → Real)
    (hq :
      q ∈ (D.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i) :
    D.coordCarrier (I := I) (K := K) i ⊆
      ManifoldForm.chartOverlap I
        (D.sourceChart (I := I) (K := K) i ⟨i, q⟩)
        (G.targetChart i q) :=
  D.coordCarrier_subset_overlap_of_ambientDomain
    (I := I) (K := K) G.targetChart
    G.ambient_subset_boundaryChartDomain i q hq

/-- Build the natural core from generated collar data, ambient-open data, and
the compressed chart-compatibility package. -/
def toNaturalCore
    (ambientOpenData :
      D.FiniteCoverAmbientOpenData (I := I) (K := K) (C := C) (P := P)) :
    CoverIndexedZeroCompactRepresentedStokesNaturalCore
      (I := I) (K := K) (ω := ω) (C := C) (P := P) where
  generated := D
  ambientOpenData := ambientOpenData
  targetChart := G.targetChart
  base_tsupport_subset_coordCarrier :=
    G.base_tsupport_subset_coordCarrier
  ambient_subset_boundaryChartDomain :=
    G.ambient_subset_boundaryChartDomain
  coordCarrier_mapsTo_K :=
    D.coordCarrier_mapsTo_K_of_boundaryActiveCoordCarrier (I := I) (K := K)
  coordCarrier_subset_sourceTarget :=
    D.coordCarrier_subset_sourceTarget_of_boundaryActiveCoordCarrier
      (I := I) (K := K)
  coordCarrier_subset_overlap :=
    G.coordCarrier_subset_overlap

end CoverIndexedZeroCompactGeneratedChartCompatibility

end ChartCompatibility

section CInftyLocalStokes

universe uH uM uι uB

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type uι} {BoundaryPiece : Type uB}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace ManifoldForm

/-- `C^\infty` source-chart coefficient smoothness transports to transition
coordinates on a chart-overlap neighborhood. -/
theorem contDiffOn_infty_transitionCoefficientInChart_of_coefficientInChart
    {x0 x1 : M} {ρ : M → Real} {U : Set (Fin (n + 1) → Real)}
    (hρ :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (coefficientInChart I x0 ρ) U)
    (hUoverlap : U ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (transitionCoefficientInChart I x0 x1 ρ) U := by
  exact hρ.congr fun y hy =>
    transitionCoefficientInChart_eq_coefficientInChart_of_mem_overlap
      (I := I) (ρ := ρ) (y := y) (hUoverlap hy)

/-- Chartwise smoothness supplies `C^\infty` transition-pullback smoothness on
refined neighborhoods. -/
theorem contDiffOn_infty_transitionPullbackInChart_of_chartwiseSmooth_refined
    [IsManifold I ⊤ M]
    {x0 x1 : M} {U : Set (Fin (n + 1) → Real)}
    (hω : ChartwiseSmooth I ω)
    (hUtarget : U ⊆ (extChartAt I x0).target)
    (hUoverlap : U ⊆ chartOverlap I x0 x1) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (transitionPullbackInChart I x0 x1 ω) U :=
  (hω.contDiffOn_transitionPullbackInChart_of_chartAPI
    (I := I) x0 x1 hUtarget hUoverlap).of_le le_top

end ManifoldForm

/-- `C^\infty` cover-indexed boundary half-space local Stokes, deriving
localized smoothness from coefficient and base representative smoothness. -/
theorem coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_contDiffOn_infty
    (active : Finset ι)
    (boundaryPieces : ι → Finset BoundaryPiece)
    (sourceChart targetChart : ι → BoundaryPiece → M)
    (rho : ι → BoundaryPiece → M → Real)
    (coordSupport : ι → BoundaryPiece → Set (Fin (n + 1) → Real))
    (lower upper : ι → BoundaryPiece → Fin (n + 1) → Real)
    (U : ι → BoundaryPiece → Set (Fin (n + 1) → Real))
    (hK :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i → IsCompact (coordSupport i q))
    (hhalf :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i → coordSupport i q ⊆ upperHalfSpace n)
    (hbase :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i →
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (sourceChart i q) (targetChart i q) ω) ⊆
            coordSupport i q)
    (ha0 :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i → lower i q 0 = 0)
    (hle :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i → lower i q ≤ upper i q)
    (hcoeff :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i →
          tsupport
              (ManifoldForm.transitionCoefficientInChart I
                (sourceChart i q) (targetChart i q) (rho i q)) ∩
              coordSupport i q ⊆
            halfSpaceSupportBox (lower i q) (upper i q))
    (hdomain :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i →
          Icc (lower i q) (upper i q) ⊆
            boundaryChartDomain I (sourceChart i q) (targetChart i q))
    (hU :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i → IsOpen (U i q))
    (hUbox :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i →
          Icc (lower i q) (upper i q) ⊆ U i q)
    (hrhoU :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i →
          ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
            (ManifoldForm.transitionCoefficientInChart I
              (sourceChart i q) (targetChart i q) (rho i q)) (U i q))
    (homegaU :
      ∀ i, i ∈ active →
        ∀ q, q ∈ boundaryPieces i →
          ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart i q) (targetChart i q) ω) (U i q)) :
    (Finset.sum active fun i =>
        Finset.sum (boundaryPieces i) fun q =>
          projectLocalBulkIntegral I (sourceChart i q) (targetChart i q)
            (ManifoldForm.localizedForm I (rho i q) ω)
            (lower i q) (upper i q)) =
      Finset.sum active fun i =>
        Finset.sum (boundaryPieces i) fun q =>
          projectLocalBoundaryIntegral I (sourceChart i q) (targetChart i q)
            (ManifoldForm.localizedForm I (rho i q) ω)
            (lower i q) (upper i q) := by
  exact
    coverIndexed_boundaryBulkSum_eq_trueBoundarySum active boundaryPieces
      (fun i q =>
        projectLocalBulkIntegral I (sourceChart i q) (targetChart i q)
          (ManifoldForm.localizedForm I (rho i q) ω)
          (lower i q) (upper i q))
      (fun i q =>
        projectLocalBoundaryIntegral I (sourceChart i q) (targetChart i q)
          (ManifoldForm.localizedForm I (rho i q) ω)
          (lower i q) (upper i q))
      (by
        intro i hi q hq
        exact
          boundaryAssignedBox_projectLocalStokes_of_contDiffOn_infty
            (I := I) (omega := ω)
            (x0 := sourceChart i q) (x1 := targetChart i q)
            (rho := rho i q)
            (hK i hi q hq) (hhalf i hi q hq) (hbase i hi q hq)
            (ha0 i hi q hq) (hle i hi q hq) (hcoeff i hi q hq)
            (hdomain i hi q hq) (hU i hi q hq) (hUbox i hi q hq)
            (hrhoU i hi q hq) (homegaU i hi q hq))

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece)
    {U :
      CoverIndexedBoundaryIndex (I := I) C → BoundaryPiece →
        Set (Fin (n + 1) → Real)}

/-- Refined boundary half-space Stokes from `C^\infty` local smoothness. -/
theorem boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_contDiffOn_infty
    (hU :
      ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q, q ∈ D.boundaryPieces i → IsOpen (U i q))
    (hUbox :
      ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q, q ∈ D.boundaryPieces i →
          Icc (D.lower i q) (D.upper i q) ⊆ U i q)
    (hrhoU :
      ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q, q ∈ D.boundaryPieces i →
          ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
            (ManifoldForm.transitionCoefficientInChart I
              (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
            (U i q))
    (homegaU :
      ∀ i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q, q ∈ D.boundaryPieces i →
          ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
            (ManifoldForm.transitionPullbackInChart I
              (D.sourceChart i q) (D.targetChart i q) ω)
            (U i q)) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBoundaryTerm i q := by
  classical
  exact
    coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_contDiffOn_infty
      (I := I) (ω := ω)
      (active := (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)))
      (boundaryPieces := D.boundaryPieces)
      (sourceChart := D.sourceChart) (targetChart := D.targetChart)
      (rho := D.coefficient) (coordSupport := D.coordSupport)
      (lower := D.lower) (upper := D.upper) (U := U)
      (fun i _hi q hq => D.isCompact_coordSupport i q hq)
      (fun i _hi q hq => D.coordSupport_subset_upperHalfSpace i q hq)
      (fun i _hi q hq => D.base_tsupport_subset_coordSupport i q hq)
      (fun i _hi q hq => D.lower_zero i q hq)
      (fun i _hi q hq => D.lower_le_upper i q hq)
      (fun i _hi q hq =>
        D.coefficient_tsupport_inter_coordSupport_subset_halfSpaceSupportBox i q hq)
      (fun i _hi q hq => D.Icc_subset_boundaryChartDomain i q hq)
      hU hUbox hrhoU homegaU

end CoverIndexedBoundaryBoxRefinedPartition

end CInftyLocalStokes

section CompactInput

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable [FiniteDimensional Real (Fin (n + 1) → Real)]
variable [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]

/--
A smaller compact-support represented Stokes input.

It still exposes the honest collar, ambient-open, smoothness-neighborhood, and
whole-box image-shrink hypotheses, but it no longer asks callers to build the
natural theorem's image-data package or coefficient smoothness field.
-/
structure CoverIndexedZeroCompactRepresentedStokesCompactInput where
  /-- Collar-generated finite-cover data. -/
  generated :
    CoverIndexedZeroCompactFromCollarGenerated (I := I) (K := K) C P
  /-- Manifold-side open neighborhoods for generated refined boxes. -/
  ambientOpen :
    CoverIndexedBoundaryIndex (I := I) C →
      generated.BoundaryPiece (I := I) (K := K) → Set M
  /-- The assigned manifold-side neighborhoods are open. -/
  ambientOpen_isOpen :
    ∀ i q, q ∈ generated.boundaryPieces (I := I) (K := K) i →
      IsOpen (ambientOpen i q)
  /-- The natural active carrier is covered by the assigned neighborhoods. -/
  activeCarrier_subset_iUnion_ambientOpen :
    ∀ i : CoverIndexedBoundaryIndex (I := I) C,
      generated.activeCarrier (I := I) (K := K) i ⊆
        ⋃ q ∈ generated.boundaryPieces (I := I) (K := K) i, ambientOpen i q
  /-- Each assigned neighborhood lies in the generated boundary chart box. -/
  ambientOpen_subset_boundaryChartBox :
    ∀ i q, q ∈ generated.boundaryPieces (I := I) (K := K) i →
      ambientOpen i q ⊆
        boundaryChartBoxNeighborhood I
          (generated.sourceChart (I := I) (K := K) i q)
          (generated.lower (I := I) (K := K) i q)
          (generated.upper (I := I) (K := K) i q)
  /-- Compressed chart-transition compatibility. -/
  chartCompatibility :
    CoverIndexedZeroCompactGeneratedChartCompatibility
      (I := I) (K := K) (ω := ω) (C := C) (P := P) generated
  /-- Chartwise smoothness of the base form. -/
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I ω
  /-- Smoothness neighborhood for each generated refined box. -/
  smoothnessNeighborhood :
    CoverIndexedBoundaryIndex (I := I) C →
      generated.BoundaryPiece (I := I) (K := K) →
        Set (Fin (n + 1) → Real)
  /-- Smoothness neighborhoods are open. -/
  smoothnessNeighborhood_isOpen :
    ∀ i,
      i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q,
          q ∈ ((chartCompatibility.toNaturalCore
              (generated.ambientOpenDataOfBoundaryChartBoxes
                (I := I) (K := K)
                ambientOpen ambientOpen_isOpen
                activeCarrier_subset_iUnion_ambientOpen
                ambientOpen_subset_boundaryChartBox)).refinedPartition
            (I := I) (K := K) (ω := ω)).boundaryPieces i →
            IsOpen (smoothnessNeighborhood i q)
  /-- Each generated closed source box lies in its smoothness neighborhood. -/
  sourceIcc_subset_smoothnessNeighborhood :
    ∀ i,
      i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q,
          q ∈ ((chartCompatibility.toNaturalCore
              (generated.ambientOpenDataOfBoundaryChartBoxes
                (I := I) (K := K)
                ambientOpen ambientOpen_isOpen
                activeCarrier_subset_iUnion_ambientOpen
                ambientOpen_subset_boundaryChartBox)).refinedPartition
            (I := I) (K := K) (ω := ω)).boundaryPieces i →
            Icc
                (((chartCompatibility.toNaturalCore
                  (generated.ambientOpenDataOfBoundaryChartBoxes
                    (I := I) (K := K)
                    ambientOpen ambientOpen_isOpen
                    activeCarrier_subset_iUnion_ambientOpen
                    ambientOpen_subset_boundaryChartBox)).refinedPartition
                  (I := I) (K := K) (ω := ω)).lower i q)
                (((chartCompatibility.toNaturalCore
                  (generated.ambientOpenDataOfBoundaryChartBoxes
                    (I := I) (K := K)
                    ambientOpen ambientOpen_isOpen
                    activeCarrier_subset_iUnion_ambientOpen
                    ambientOpen_subset_boundaryChartBox)).refinedPartition
                  (I := I) (K := K) (ω := ω)).upper i q) ⊆
              smoothnessNeighborhood i q
  /-- Smoothness neighborhoods lie in the source chart target. -/
  smoothnessNeighborhood_subset_target :
    ∀ i q,
      q ∈ ((chartCompatibility.toNaturalCore
          (generated.ambientOpenDataOfBoundaryChartBoxes
            (I := I) (K := K)
            ambientOpen ambientOpen_isOpen
            activeCarrier_subset_iUnion_ambientOpen
            ambientOpen_subset_boundaryChartBox)).refinedPartition
        (I := I) (K := K) (ω := ω)).boundaryPieces i →
        smoothnessNeighborhood i q ⊆
          (extChartAt I
            (((chartCompatibility.toNaturalCore
              (generated.ambientOpenDataOfBoundaryChartBoxes
                (I := I) (K := K)
                ambientOpen ambientOpen_isOpen
                activeCarrier_subset_iUnion_ambientOpen
                ambientOpen_subset_boundaryChartBox)).refinedPartition
              (I := I) (K := K) (ω := ω)).sourceChart i q)).target
  /-- Smoothness neighborhoods lie in the source/target chart overlap. -/
  smoothnessNeighborhood_subset_overlap :
    ∀ i q,
      q ∈ ((chartCompatibility.toNaturalCore
          (generated.ambientOpenDataOfBoundaryChartBoxes
            (I := I) (K := K)
            ambientOpen ambientOpen_isOpen
            activeCarrier_subset_iUnion_ambientOpen
            ambientOpen_subset_boundaryChartBox)).refinedPartition
        (I := I) (K := K) (ω := ω)).boundaryPieces i →
        smoothnessNeighborhood i q ⊆
          ManifoldForm.chartOverlap I
            (((chartCompatibility.toNaturalCore
              (generated.ambientOpenDataOfBoundaryChartBoxes
                (I := I) (K := K)
                ambientOpen ambientOpen_isOpen
                activeCarrier_subset_iUnion_ambientOpen
                ambientOpen_subset_boundaryChartBox)).refinedPartition
              (I := I) (K := K) (ω := ω)).sourceChart i q)
            (((chartCompatibility.toNaturalCore
              (generated.ambientOpenDataOfBoundaryChartBoxes
                (I := I) (K := K)
                ambientOpen ambientOpen_isOpen
                activeCarrier_subset_iUnion_ambientOpen
                ambientOpen_subset_boundaryChartBox)).refinedPartition
              (I := I) (K := K) (ω := ω)).targetChart i q)
  /-- Refined source charts agree with the selected boundary charts. -/
  sourceChart_eq_boundaryChart :
    ∀ r :
      ((chartCompatibility.toNaturalCore
          (generated.ambientOpenDataOfBoundaryChartBoxes
            (I := I) (K := K)
            ambientOpen ambientOpen_isOpen
            activeCarrier_subset_iUnion_ambientOpen
            ambientOpen_subset_boundaryChartBox)).refinedPartition
        (I := I) (K := K) (ω := ω)).RefinedBoxIndex,
        ((chartCompatibility.toNaturalCore
            (generated.ambientOpenDataOfBoundaryChartBoxes
              (I := I) (K := K)
              ambientOpen ambientOpen_isOpen
              activeCarrier_subset_iUnion_ambientOpen
              ambientOpen_subset_boundaryChartBox)).refinedPartition
          (I := I) (K := K) (ω := ω)).sourceChart r.1 r.2.1 =
            C.boundaryChart r.1.1
  /-- Lower corner of the target box for each refined box. -/
  targetLower :
    ((chartCompatibility.toNaturalCore
        (generated.ambientOpenDataOfBoundaryChartBoxes
          (I := I) (K := K)
          ambientOpen ambientOpen_isOpen
          activeCarrier_subset_iUnion_ambientOpen
          ambientOpen_subset_boundaryChartBox)).refinedPartition
      (I := I) (K := K) (ω := ω)).RefinedBoxIndex →
        Fin (n + 1) → Real
  /-- Upper corner of the target box for each refined box. -/
  targetUpper :
    ((chartCompatibility.toNaturalCore
        (generated.ambientOpenDataOfBoundaryChartBoxes
          (I := I) (K := K)
          ambientOpen ambientOpen_isOpen
          activeCarrier_subset_iUnion_ambientOpen
          ambientOpen_subset_boundaryChartBox)).refinedPartition
      (I := I) (K := K) (ω := ω)).RefinedBoxIndex →
        Fin (n + 1) → Real
  /-- Explicit whole-box closed-preimage shrink for each refined box. -/
  closedPreimageShrink :
    ∀ r :
      ((chartCompatibility.toNaturalCore
          (generated.ambientOpenDataOfBoundaryChartBoxes
            (I := I) (K := K)
            ambientOpen ambientOpen_isOpen
            activeCarrier_subset_iUnion_ambientOpen
            ambientOpen_subset_boundaryChartBox)).refinedPartition
        (I := I) (K := K) (ω := ω)).RefinedBoxIndex,
        Icc
          (((chartCompatibility.toNaturalCore
            (generated.ambientOpenDataOfBoundaryChartBoxes
              (I := I) (K := K)
              ambientOpen ambientOpen_isOpen
              activeCarrier_subset_iUnion_ambientOpen
              ambientOpen_subset_boundaryChartBox)).refinedPartition
            (I := I) (K := K) (ω := ω)).lower r.1 r.2.1)
          (((chartCompatibility.toNaturalCore
            (generated.ambientOpenDataOfBoundaryChartBoxes
              (I := I) (K := K)
              ambientOpen ambientOpen_isOpen
              activeCarrier_subset_iUnion_ambientOpen
              ambientOpen_subset_boundaryChartBox)).refinedPartition
            (I := I) (K := K) (ω := ω)).upper r.1 r.2.1) ⊆
          (ManifoldForm.chartTransition I
            (C.boundaryChart r.1.1)
            (((chartCompatibility.toNaturalCore
              (generated.ambientOpenDataOfBoundaryChartBoxes
                (I := I) (K := K)
                ambientOpen ambientOpen_isOpen
                activeCarrier_subset_iUnion_ambientOpen
                ambientOpen_subset_boundaryChartBox)).refinedPartition
              (I := I) (K := K) (ω := ω)).targetChart r.1 r.2.1)) ⁻¹'
            Icc (targetLower r) (targetUpper r)

namespace CoverIndexedZeroCompactRepresentedStokesCompactInput

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesCompactInput
        (I := I) (K := K) (ω := ω) (C := C) (P := P))

/-- Ambient-open data generated from the public compact input. -/
def ambientOpenData :
    X.generated.FiniteCoverAmbientOpenData
      (I := I) (K := K) (C := C) (P := P) :=
  X.generated.ambientOpenDataOfBoundaryChartBoxes
    (I := I) (K := K)
    X.ambientOpen
    X.ambientOpen_isOpen
    X.activeCarrier_subset_iUnion_ambientOpen
    X.ambientOpen_subset_boundaryChartBox

/-- Natural core generated from collar, ambient-open, and chart-compatibility data. -/
def naturalCore :
    CoverIndexedZeroCompactRepresentedStokesNaturalCore
      (I := I) (K := K) (ω := ω) (C := C) (P := P) :=
  X.chartCompatibility.toNaturalCore
    (I := I) (K := K) (ω := ω) (C := C) (P := P)
    X.ambientOpenData

/-- Generated refined partition. -/
def refinedPartition :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω
      (X.generated.BoundaryPiece (I := I) (K := K)) :=
  X.naturalCore.refinedPartition (I := I) (K := K) (ω := ω)

/-- `C^\infty` source-chart smoothness of generated refined coefficients. -/
theorem coefficientInChart_contDiffOn_infty
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : X.generated.BoundaryPiece (I := I) (K := K))
    (hq : q ∈ (X.refinedPartition
        (I := I) (K := K) (ω := ω)).boundaryPieces i) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.coefficientInChart I
        ((X.refinedPartition
          (I := I) (K := K) (ω := ω)).sourceChart i q)
        ((X.refinedPartition
          (I := I) (K := K) (ω := ω)).coefficient i q))
      (X.smoothnessNeighborhood i q) := by
  classical
  let S := X.naturalCore.smoothRefinement (I := I) (K := K) (ω := ω)
  have hqS : q ∈ S.boundaryPieces i := by
    simpa [refinedPartition, naturalCore, CoverIndexedZeroCompactGeneratedChartCompatibility.toNaturalCore,
      CoverIndexedZeroCompactRepresentedStokesNaturalCore.refinedPartition, S]
      using hq
  have hqS_owner : q ∈ S.boundaryPieces q.1 := by
    let F :=
      X.generated.finiteHalfSpaceCover (I := I) (K := K) (C := C)
    have hqGenerated :
        q ∈ X.generated.boundaryPieces (I := I) (K := K) i := by
      simpa [S, CoverIndexedZeroCompactRepresentedStokesNaturalCore.smoothRefinement]
        using hqS
    have hqF :
        q ∈ F.sigmaBoundaryPieces i := by
      simpa [CoverIndexedZeroCompactFromCollarGenerated.boundaryPieces, F]
        using hqGenerated
    have howner : q.1 = i := (F.mem_sigmaBoundaryPieces.mp hqF).1
    simpa [howner] using hqS
  have hsmooth :
      ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
        (ManifoldForm.coefficientInChart I
          ((X.refinedPartition
            (I := I) (K := K) (ω := ω)).sourceChart i q)
          (S.coefficient q.1 q))
        (X.smoothnessNeighborhood i q) := by
    exact
      S.contDiffOn_infty_coefficientInChart
        (I := I) q.1 hqS_owner
        ((X.refinedPartition
          (I := I) (K := K) (ω := ω)).sourceChart i q)
        (X.smoothnessNeighborhood_subset_target i q hq)
  change
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.coefficientInChart I
        ((X.refinedPartition
          (I := I) (K := K) (ω := ω)).sourceChart i q)
        (S.coefficient q.1 q))
      (X.smoothnessNeighborhood i q)
  exact hsmooth

/-- `C^\infty` transition-coordinate smoothness of generated refined
coefficients. -/
theorem transitionCoefficientInChart_contDiffOn_infty
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : X.generated.BoundaryPiece (I := I) (K := K))
    (hq : q ∈ (X.refinedPartition
        (I := I) (K := K) (ω := ω)).boundaryPieces i) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionCoefficientInChart I
        ((X.refinedPartition
          (I := I) (K := K) (ω := ω)).sourceChart i q)
        ((X.refinedPartition
          (I := I) (K := K) (ω := ω)).targetChart i q)
        ((X.refinedPartition
          (I := I) (K := K) (ω := ω)).coefficient i q))
      (X.smoothnessNeighborhood i q) :=
  ManifoldForm.contDiffOn_infty_transitionCoefficientInChart_of_coefficientInChart
    (I := I)
    (X.coefficientInChart_contDiffOn_infty
      (I := I) (K := K) (ω := ω) i q hq)
    (X.smoothnessNeighborhood_subset_overlap i q hq)

/-- `C^\infty` transition-pullback smoothness of the base form on generated
refined neighborhoods. -/
theorem transitionPullbackInChart_contDiffOn_infty
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q : X.generated.BoundaryPiece (I := I) (K := K))
    (hq : q ∈ (X.refinedPartition
        (I := I) (K := K) (ω := ω)).boundaryPieces i) :
    ContDiffOn Real ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ManifoldForm.transitionPullbackInChart I
        ((X.refinedPartition
          (I := I) (K := K) (ω := ω)).sourceChart i q)
        ((X.refinedPartition
          (I := I) (K := K) (ω := ω)).targetChart i q)
        ω)
      (X.smoothnessNeighborhood i q) :=
  ManifoldForm.contDiffOn_infty_transitionPullbackInChart_of_chartwiseSmooth_refined
    (I := I) (ω := ω)
    X.chartwiseSmooth
    (X.smoothnessNeighborhood_subset_target i q hq)
    (X.smoothnessNeighborhood_subset_overlap i q hq)

/-- Local refined half-space Stokes using the generated `C^\infty`
smooth-partition coefficients. -/
theorem refinedLocalStokes :
    (Finset.sum
        (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum ((X.refinedPartition
          (I := I) (K := K) (ω := ω)).boundaryPieces i) fun q =>
          (X.refinedPartition
            (I := I) (K := K) (ω := ω)).localBulkTerm i q) =
      Finset.sum
        (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum ((X.refinedPartition
          (I := I) (K := K) (ω := ω)).boundaryPieces i) fun q =>
          (X.refinedPartition
            (I := I) (K := K) (ω := ω)).localBoundaryTerm i q := by
  exact
    (X.refinedPartition
      (I := I) (K := K) (ω := ω))
      |>.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_contDiffOn_infty
        (I := I) (K := K) (ω := ω)
        X.smoothnessNeighborhood_isOpen
        X.sourceIcc_subset_smoothnessNeighborhood
        (by
          intro i hi q hq
          exact
            X.transitionCoefficientInChart_contDiffOn_infty
              (I := I) (K := K) (ω := ω) i q hq)
        (by
          intro i hi q hq
          exact
            X.transitionPullbackInChart_contDiffOn_infty
              (I := I) (K := K) (ω := ω) i q hq)

/-- Canonical represented bulk integral generated by the compact input. -/
def representedBulkIntegral : Real :=
  (X.refinedPartition
    (I := I) (K := K) (ω := ω)).generatedRepresentedBulkIntegral
      (I := I) (K := K)

/-- Canonical represented boundary integral generated by the compact input. -/
def representedBoundaryIntegral : Real :=
  (X.refinedPartition
    (I := I) (K := K) (ω := ω)).generatedRepresentedBoundaryIntegral
      (I := I) (K := K)

/-- Compact-support represented Stokes from the smaller compact input. -/
theorem representedStokes :
    X.representedBulkIntegral (I := I) (K := K) (ω := ω) =
      X.representedBoundaryIntegral (I := I) (K := K) (ω := ω) := by
  simpa [representedBulkIntegral, representedBoundaryIntegral,
    CoverIndexedBoundaryBoxRefinedPartition.generatedRepresentedBulkIntegral,
    CoverIndexedBoundaryBoxRefinedPartition.generatedRepresentedBoundaryIntegral,
    CoverIndexedBoundaryBoxRefinedPartition.generatedBoundaryPartitionTerm]
    using X.refinedLocalStokes (I := I) (K := K) (ω := ω)

end CoverIndexedZeroCompactRepresentedStokesCompactInput

end CompactInput

end Stokes

end
