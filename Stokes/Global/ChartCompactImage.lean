import Stokes.Global.CompactActiveBoxes
import Stokes.Global.LocalizedSupport

/-!
# Compact coordinate images of chart-source supports

This module packages the point-set step used before selecting coordinate boxes:
a compact support set in a chart source has compact image under the extended
chart map.  In finite real coordinate spaces, the compact image then supplies
the coordinate support and selected box fields required by
`CompactActiveBoxData`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false

section TSupportCompact

universe u v

variable {X : Type u} [TopologicalSpace X]
variable {A : Type v} [Zero A]

/--
If the topological support of a function is contained in a compact set, then
the topological support itself is compact.

This is the basic compact-support bridge used below for chart representatives:
after a local representative has been shown to live in a compact coordinate
set, its own `tsupport` can be used as a compact set for later box selection.
-/
theorem isCompact_tsupport_of_subset_isCompact {f : X → A} {K : Set X}
    (hK : IsCompact K) (hsupp : tsupport f ⊆ K) :
    IsCompact (tsupport f) :=
  hK.of_isClosed_subset (isClosed_tsupport f) hsupp

end TSupportCompact

section ChartCompactImage

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- The image of a manifold support set in the coordinates of an extended chart. -/
def chartCoordinateImage
    (I : ModelWithCorners Real E H) (x : M) (K : Set M) : Set E :=
  (extChartAt I x) '' K

/--
A compact manifold support set together with continuity of a chosen chart map
on that set.  Its coordinate image is compact and can later be boxed.
-/
structure ChartCompactImage
    (I : ModelWithCorners Real E H) (x : M) where
  /-- The manifold-side compact support set. -/
  K : Set M
  /-- Compactness of the manifold-side support set. -/
  isCompact_K : IsCompact K
  /-- Continuity of the extended chart map on the support set. -/
  continuousOn_chart : ContinuousOn (extChartAt I x) K

namespace ChartCompactImage

variable {I : ModelWithCorners Real E H} {x : M}

/-- Constructor from the explicit compactness and chart-continuity hypotheses. -/
def of (K : Set M) (hK : IsCompact K)
    (hcont : ContinuousOn (extChartAt I x) K) :
    ChartCompactImage I x where
  K := K
  isCompact_K := hK
  continuousOn_chart := hcont

/-- The coordinate support attached to a compact chart-image package. -/
def coordSupport (C : ChartCompactImage I x) : Set E :=
  chartCoordinateImage I x C.K

@[simp]
theorem coordSupport_eq (C : ChartCompactImage I x) :
    C.coordSupport = chartCoordinateImage I x C.K :=
  rfl

/-- The coordinate support is compact. -/
theorem isCompact_coordSupport (C : ChartCompactImage I x) :
    IsCompact C.coordSupport :=
  C.isCompact_K.image_of_continuousOn C.continuousOn_chart

/-- Membership in the manifold-side support maps into the coordinate support. -/
theorem mem_coordSupport (C : ChartCompactImage I x) {p : M} (hp : p ∈ C.K) :
    (extChartAt I x) p ∈ C.coordSupport :=
  ⟨p, hp, rfl⟩

/--
Any local representative whose topological support is contained in the compact
coordinate image carried by `C` has compact topological support.
-/
theorem isCompact_tsupport_of_subset_coordSupport
    (C : ChartCompactImage I x) {A : Type*} [Zero A] {f : E → A}
    (hsupp : tsupport f ⊆ C.coordSupport) :
    IsCompact (tsupport f) :=
  Stokes.isCompact_tsupport_of_subset_isCompact C.isCompact_coordSupport hsupp

/--
Specialization to a transition-pullback chart representative: compact
coordinate-image containment gives compact `tsupport` for the local
representative itself.
-/
theorem isCompact_transitionPullbackInChart_tsupport_of_subset_coordSupport
    (C : ChartCompactImage I x) {x1 : M} {ω : ManifoldForm I M k}
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x x1 ω) ⊆
        C.coordSupport) :
    IsCompact
      (tsupport (ManifoldForm.transitionPullbackInChart I x x1 ω)) :=
  C.isCompact_tsupport_of_subset_coordSupport hsupp

/--
For a single chart compact-image package, coefficient localization cannot push
the transition-pullback support outside a compact coordinate support that
already controls the base representative.
-/
theorem localized_transitionPullback_tsupport_subset_coordSupport_of_base
    (C : ChartCompactImage I x) {x1 : M} {ρ : M → Real}
    {ω : ManifoldForm I M k}
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x x1 ω) ⊆
        C.coordSupport) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x x1
          (ManifoldForm.localizedForm I ρ ω)) ⊆
      C.coordSupport :=
  (ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_form
    (I := I) x x1 ρ ω).trans hsupp

/--
Single-chart compactness version for localized representatives.
-/
theorem isCompact_localized_transitionPullbackInChart_tsupport_of_base
    (C : ChartCompactImage I x) {x1 : M} {ρ : M → Real}
    {ω : ManifoldForm I M k}
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x x1 ω) ⊆
        C.coordSupport) :
    IsCompact
      (tsupport
        (ManifoldForm.transitionPullbackInChart I x x1
          (ManifoldForm.localizedForm I ρ ω))) :=
  C.isCompact_tsupport_of_subset_coordSupport
    (C.localized_transitionPullback_tsupport_subset_coordSupport_of_base hsupp)

end ChartCompactImage

/-- Extended charts are continuous on any subset of their source. -/
theorem continuousOn_extChartAt_of_subset_source
    {I : ModelWithCorners Real E H} {x : M} {K : Set M}
    (hsource : K ⊆ (extChartAt I x).source) :
    ContinuousOn (extChartAt I x) K :=
  (continuousOn_extChartAt (I := I) x).mono hsource

/-- A compact set in a chart source has compact coordinate image. -/
theorem isCompact_chartCoordinateImage_of_continuousOn
    {I : ModelWithCorners Real E H} {x : M} {K : Set M}
    (hK : IsCompact K) (hcont : ContinuousOn (extChartAt I x) K) :
    IsCompact (chartCoordinateImage I x K) :=
  hK.image_of_continuousOn hcont

/-- Source-contained compact sets have compact coordinate image. -/
theorem isCompact_chartCoordinateImage_of_subset_source
    {I : ModelWithCorners Real E H} {x : M} {K : Set M}
    (hK : IsCompact K) (hsource : K ⊆ (extChartAt I x).source) :
    IsCompact (chartCoordinateImage I x K) :=
  isCompact_chartCoordinateImage_of_continuousOn hK
    (continuousOn_extChartAt_of_subset_source hsource)

/-- The coordinate image of a set contained in the chart source lies in the chart target. -/
theorem chartCoordinateImage_subset_target
    {I : ModelWithCorners Real E H} {x : M} {K : Set M}
    (hsource : K ⊆ (extChartAt I x).source) :
    chartCoordinateImage I x K ⊆ (extChartAt I x).target := by
  rintro y ⟨p, hp, rfl⟩
  exact (extChartAt I x).map_source (hsource hp)

/-- Coordinate images are monotone in the manifold-side source set. -/
theorem chartCoordinateImage_mono
    {I : ModelWithCorners Real E H} {x : M} {K L : Set M}
    (hKL : K ⊆ L) :
    chartCoordinateImage I x K ⊆ chartCoordinateImage I x L := by
  rintro y ⟨p, hp, rfl⟩
  exact ⟨p, hKL hp, rfl⟩

/--
If a local model-space representative is supported in the coordinate image of
a compact manifold-side set, then that representative has compact
topological support.
-/
theorem isCompact_tsupport_of_subset_chartCoordinateImage
    {I : ModelWithCorners Real E H} {x : M} {K : Set M}
    {A : Type*} [Zero A] {f : E → A}
    (hK : IsCompact K) (hcont : ContinuousOn (extChartAt I x) K)
    (hsupp : tsupport f ⊆ chartCoordinateImage I x K) :
    IsCompact (tsupport f) :=
  isCompact_tsupport_of_subset_isCompact
    (isCompact_chartCoordinateImage_of_continuousOn hK hcont) hsupp

/--
Source-contained compact manifold-side sets give compact topological support
for any local representative supported in their coordinate image.
-/
theorem isCompact_tsupport_of_subset_chartCoordinateImage_of_subset_source
    {I : ModelWithCorners Real E H} {x : M} {K : Set M}
    {A : Type*} [Zero A] {f : E → A}
    (hK : IsCompact K) (hsource : K ⊆ (extChartAt I x).source)
    (hsupp : tsupport f ⊆ chartCoordinateImage I x K) :
    IsCompact (tsupport f) :=
  isCompact_tsupport_of_subset_chartCoordinateImage hK
    (continuousOn_extChartAt_of_subset_source hsource) hsupp

/--
Transition-pullback version of compactness from a compact chart-coordinate
image.  The support containment is the analytic input; the compactness is now
automatic.
-/
theorem isCompact_transitionPullbackInChart_tsupport_of_subset_chartCoordinateImage
    {I : ModelWithCorners Real E H} {x0 x1 : M} {K : Set M}
    {ω : ManifoldForm I M k}
    (hK : IsCompact K) (hcont : ContinuousOn (extChartAt I x0) K)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        chartCoordinateImage I x0 K) :
    IsCompact
      (tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω)) :=
  isCompact_tsupport_of_subset_chartCoordinateImage hK hcont hsupp

/--
Source-contained version for transition-pullback representatives.
-/
theorem isCompact_transitionPullbackInChart_tsupport_of_subset_chartCoordinateImage_of_subset_source
    {I : ModelWithCorners Real E H} {x0 x1 : M} {K : Set M}
    {ω : ManifoldForm I M k}
    (hK : IsCompact K) (hsource : K ⊆ (extChartAt I x0).source)
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) ⊆
        chartCoordinateImage I x0 K) :
    IsCompact
      (tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω)) :=
  isCompact_transitionPullbackInChart_tsupport_of_subset_chartCoordinateImage hK
    (continuousOn_extChartAt_of_subset_source hsource) hsupp

end ChartCompactImage

section PiRealChartCompactImage

universe u v w

variable {ι : Type u} [Fintype ι]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real (ι → Real) H}

/--
In finite real coordinates, a compact coordinate chart image has a selected
coordinate box.
-/
theorem exists_compactCoordinateBoxSelection_chartCoordinateImage_of_continuousOn
    {x : M} {K : Set M} (hK : IsCompact K)
    (hcont : ContinuousOn (extChartAt I x) K) :
    ∃ B : CompactCoordinateBoxSelection (ι → Real),
      B.K = chartCoordinateImage I x K :=
  exists_compactCoordinateBoxSelection_piReal
    (isCompact_chartCoordinateImage_of_continuousOn hK hcont)

/--
Source-contained compact sets in finite real coordinates have selected
coordinate boxes.
-/
theorem exists_compactCoordinateBoxSelection_chartCoordinateImage_of_subset_source
    {x : M} {K : Set M} (hK : IsCompact K)
    (hsource : K ⊆ (extChartAt I x).source) :
    ∃ B : CompactCoordinateBoxSelection (ι → Real),
      B.K = chartCoordinateImage I x K :=
  exists_compactCoordinateBoxSelection_chartCoordinateImage_of_continuousOn
    hK (continuousOn_extChartAt_of_subset_source hsource)

namespace ChartCompactImage

variable {x : M}

/-- The selected box associated to a finite-dimensional chart compact image. -/
def box (C : ChartCompactImage I x) :
    CompactCoordinateBoxSelection (ι → Real) :=
  Classical.choose (exists_compactCoordinateBoxSelection_piReal C.isCompact_coordSupport)

@[simp]
theorem box_K_eq_coordSupport (C : ChartCompactImage I x) :
    C.box.K = C.coordSupport :=
  Classical.choose_spec (exists_compactCoordinateBoxSelection_piReal C.isCompact_coordSupport)

theorem coordSupport_subset_box (C : ChartCompactImage I x) :
    C.coordSupport ⊆ Set.Icc C.box.a C.box.b := by
  intro y hy
  exact C.box.subset_Icc (by simpa [C.box_K_eq_coordSupport] using hy)

end ChartCompactImage

end PiRealChartCompactImage

section ActiveChartCompactImages

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H}

/--
For each active chart index, a compact manifold-side support set whose image
under that chart is the coordinate support to be boxed.
-/
structure ActiveChartCompactImages
    (P : FiniteActiveOnCompact (M := M) I) where
  /-- Manifold-side compact support set used for each active chart. -/
  sourceSupport : M → Set M
  /-- Compactness of each active manifold-side support set. -/
  isCompact_sourceSupport :
    ∀ i ∈ P.active, IsCompact (sourceSupport i)
  /-- Continuity of each active chart map on its manifold-side support. -/
  continuousOn_chart :
    ∀ i ∈ P.active, ContinuousOn (extChartAt I i) (sourceSupport i)

namespace ActiveChartCompactImages

variable {P : FiniteActiveOnCompact (M := M) I}

/-- Constructor when every active support set is contained in its chart source. -/
def ofSubsetSource
    (sourceSupport : M → Set M)
    (hcompact : ∀ i ∈ P.active, IsCompact (sourceSupport i))
    (hsource : ∀ i ∈ P.active, sourceSupport i ⊆ (extChartAt I i).source) :
    ActiveChartCompactImages (I := I) P where
  sourceSupport := sourceSupport
  isCompact_sourceSupport := hcompact
  continuousOn_chart := fun i hi =>
    continuousOn_extChartAt_of_subset_source (hsource i hi)

/--
Use the global compact support set `P.K` as the manifold-side compact support
for every active chart.  The only local geometric input is that this compact
set lies in the source of each active extended chart.
-/
def ofFiniteActiveK
    (hsource : ∀ i ∈ P.active, P.K ⊆ (extChartAt I i).source) :
    ActiveChartCompactImages (I := I) P :=
  ofSubsetSource (I := I) (P := P) (fun _ => P.K)
    (fun _ _ => P.isCompact) hsource

@[simp]
theorem ofFiniteActiveK_sourceSupport
    (hsource : ∀ i ∈ P.active, P.K ⊆ (extChartAt I i).source)
    (i : M) :
    (ofFiniteActiveK (I := I) (P := P) hsource).sourceSupport i = P.K :=
  rfl

/-- Coordinate support for each active chart. -/
def coordSupport (C : ActiveChartCompactImages (I := I) P) :
    M → Set E :=
  fun i => chartCoordinateImage I i (C.sourceSupport i)

@[simp]
theorem ofFiniteActiveK_coordSupport
    (hsource : ∀ i ∈ P.active, P.K ⊆ (extChartAt I i).source)
    (i : M) :
    (ofFiniteActiveK (I := I) (P := P) hsource).coordSupport i =
      chartCoordinateImage I i P.K :=
  rfl

/-- The single-chart package associated to an active index. -/
def chartImage (C : ActiveChartCompactImages (I := I) P)
    (i : M) (hi : i ∈ P.active) : ChartCompactImage I i :=
  ChartCompactImage.of (C.sourceSupport i)
    (C.isCompact_sourceSupport i hi) (C.continuousOn_chart i hi)

@[simp]
theorem chartImage_K (C : ActiveChartCompactImages (I := I) P)
    {i : M} (hi : i ∈ P.active) :
    (C.chartImage i hi).K = C.sourceSupport i :=
  rfl

@[simp]
theorem chartImage_coordSupport (C : ActiveChartCompactImages (I := I) P)
    {i : M} (hi : i ∈ P.active) :
    (C.chartImage i hi).coordSupport = C.coordSupport i :=
  rfl

/-- Each active coordinate support is compact. -/
theorem isCompact_coordSupport (C : ActiveChartCompactImages (I := I) P)
    {i : M} (hi : i ∈ P.active) :
    IsCompact (C.coordSupport i) :=
  isCompact_chartCoordinateImage_of_continuousOn
    (C.isCompact_sourceSupport i hi) (C.continuousOn_chart i hi)

/-- Source-contained active supports have coordinate images inside chart targets. -/
theorem coordSupport_subset_target
    (C : ActiveChartCompactImages (I := I) P)
    (hsource : ∀ i ∈ P.active, C.sourceSupport i ⊆ (extChartAt I i).source)
    {i : M} (hi : i ∈ P.active) :
    C.coordSupport i ⊆ (extChartAt I i).target :=
  chartCoordinateImage_subset_target (hsource i hi)

/--
If an active base chart representative is supported in its generated compact
coordinate image, then that representative has compact topological support.
-/
theorem isCompact_transitionPullbackInChart_tsupport_of_subset_coordSupport
    (C : ActiveChartCompactImages (I := I) P)
    (ω : ManifoldForm I M k)
    (hsupp :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          C.coordSupport i)
    {i : M} (hi : i ∈ P.active) :
    IsCompact
      (tsupport (ManifoldForm.transitionPullbackInChart I i i ω)) :=
  Stokes.isCompact_tsupport_of_subset_isCompact
    (C.isCompact_coordSupport hi) (hsupp i hi)

/--
Localized partition terms inherit coordinate-image support from the base
representative, because localization by a scalar coefficient cannot enlarge
the transition-pullback `tsupport`.
-/
theorem localized_transitionPullback_tsupport_subset_coordSupport_of_base
    (C : ActiveChartCompactImages (I := I) P)
    (ω : ManifoldForm I M k)
    (hsupp :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          C.coordSupport i)
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      C.coordSupport i :=
  (ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_form
    (I := I) i i (P.partition i) ω).trans (hsupp i hi)

/--
Consequently, every active localized chart representative controlled by the
generated compact coordinate image has compact topological support.
-/
theorem isCompact_localized_transitionPullbackInChart_tsupport_of_base
    (C : ActiveChartCompactImages (I := I) P)
    (ω : ManifoldForm I M k)
    (hsupp :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          C.coordSupport i)
    {i : M} (hi : i ∈ P.active) :
    IsCompact
      (tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω))) :=
  Stokes.isCompact_tsupport_of_subset_isCompact
    (C.isCompact_coordSupport hi)
    (C.localized_transitionPullback_tsupport_subset_coordSupport_of_base
      ω hsupp hi)

/--
Compactness wrapper specialized to `ofFiniteActiveK`: if the base chart
representative over every active chart is supported in the coordinate image of
the global compact set `P.K`, then the partition-localized representative has
compact topological support.
-/
theorem isCompact_localized_transitionPullbackInChart_tsupport_ofFiniteActiveK
    (hsource : ∀ i ∈ P.active, P.K ⊆ (extChartAt I i).source)
    (ω : ManifoldForm I M k)
    (hsupp :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          chartCoordinateImage I i P.K)
    {i : M} (hi : i ∈ P.active) :
    IsCompact
      (tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω))) := by
  let C : ActiveChartCompactImages (I := I) P :=
    ofFiniteActiveK (I := I) (P := P) hsource
  refine C.isCompact_localized_transitionPullbackInChart_tsupport_of_base ω ?_ hi
  intro j hj
  simpa using hsupp j hj

end ActiveChartCompactImages

end ActiveChartCompactImages

section PiRealActiveChartCompactImages

universe u v w

variable {ι : Type u} [Fintype ι]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real (ι → Real) H}
variable {P : FiniteActiveOnCompact (M := M) I}

namespace ActiveChartCompactImages

/--
Simultaneous selected boxes for all active compact chart-coordinate images.
Inactive indices receive the fallback box chosen by
`exists_activeCompactCoordinateBoxSelections_piReal`.
-/
def box (C : ActiveChartCompactImages (I := I) P) :
    M → CompactCoordinateBoxSelection (ι → Real) :=
  Classical.choose
    (exists_activeCompactCoordinateBoxSelections_piReal (I := I) P C.coordSupport
      (fun _ hi => C.isCompact_coordSupport hi))

@[simp]
theorem box_K_eq_coordSupport (C : ActiveChartCompactImages (I := I) P)
    {i : M} (hi : i ∈ P.active) :
    (C.box i).K = C.coordSupport i :=
  Classical.choose_spec
    (exists_activeCompactCoordinateBoxSelections_piReal (I := I) P C.coordSupport
      (fun _ hi => C.isCompact_coordSupport hi)) i hi

theorem coordSupport_subset_box (C : ActiveChartCompactImages (I := I) P)
    {i : M} (hi : i ∈ P.active) :
    C.coordSupport i ⊆ Set.Icc (C.box i).a (C.box i).b := by
  intro y hy
  exact (C.box i).subset_Icc (by simpa [C.box_K_eq_coordSupport hi] using hy)

/--
Build `CompactActiveBoxData` from active chart compact images.  The coordinate
support and selected boxes are generated here; the support and domain
containments remain explicit local-geometric inputs.
-/
def toCompactActiveBoxData
    (C : ActiveChartCompactImages (I := I) P)
    (ω : ManifoldForm I M k)
    (htsupport :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          C.coordSupport i)
    (htarget :
      ∀ i ∈ P.active,
        Set.Icc (C.box i).a (C.box i).b ⊆ (extChartAt I i).target)
    (hoverlap :
      ∀ i ∈ P.active,
        Set.Icc (C.box i).a (C.box i).b ⊆ ManifoldForm.chartOverlap I i i) :
    CompactActiveBoxData I ω where
  finiteActive := P
  coordSupport := C.coordSupport
  isCompact_coordSupport := fun _ hi => C.isCompact_coordSupport hi
  box := C.box
  box_K_eq_coordSupport := fun _ hi => C.box_K_eq_coordSupport hi
  tsupport_subset_coordSupport := htsupport
  Icc_subset_target := htarget
  Icc_subset_overlap := hoverlap

@[simp]
theorem toCompactActiveBoxData_finiteActive
    (C : ActiveChartCompactImages (I := I) P)
    (ω : ManifoldForm I M k)
    (htsupport :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          C.coordSupport i)
    (htarget :
      ∀ i ∈ P.active,
        Set.Icc (C.box i).a (C.box i).b ⊆ (extChartAt I i).target)
    (hoverlap :
      ∀ i ∈ P.active,
        Set.Icc (C.box i).a (C.box i).b ⊆ ManifoldForm.chartOverlap I i i) :
    (C.toCompactActiveBoxData ω htsupport htarget hoverlap).finiteActive = P :=
  rfl

@[simp]
theorem toCompactActiveBoxData_coordSupport
    (C : ActiveChartCompactImages (I := I) P)
    (ω : ManifoldForm I M k)
    (htsupport :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          C.coordSupport i)
    (htarget :
      ∀ i ∈ P.active,
        Set.Icc (C.box i).a (C.box i).b ⊆ (extChartAt I i).target)
    (hoverlap :
      ∀ i ∈ P.active,
        Set.Icc (C.box i).a (C.box i).b ⊆ ManifoldForm.chartOverlap I i i) :
    (C.toCompactActiveBoxData ω htsupport htarget hoverlap).coordSupport =
      C.coordSupport :=
  rfl

@[simp]
theorem toCompactActiveBoxData_box
    (C : ActiveChartCompactImages (I := I) P)
    (ω : ManifoldForm I M k)
    (htsupport :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          C.coordSupport i)
    (htarget :
      ∀ i ∈ P.active,
        Set.Icc (C.box i).a (C.box i).b ⊆ (extChartAt I i).target)
    (hoverlap :
      ∀ i ∈ P.active,
        Set.Icc (C.box i).a (C.box i).b ⊆ ManifoldForm.chartOverlap I i i) :
    (C.toCompactActiveBoxData ω htsupport htarget hoverlap).box = C.box :=
  rfl

end ActiveChartCompactImages

end PiRealActiveChartCompactImages

end Stokes

end
