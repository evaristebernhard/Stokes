# Lean 4 Stokes Formalization Roadmap

Status date: 2026-05-25.

## Current Repository Status

M0, M1, and M2 are complete as thin, buildable wrappers over the LeanStokes
prior artifact.

- Root Lean package: `Stokes`.
- Lean toolchain: `leanprover/lean4:v4.29.1`.
- Pinned dependency: `d0d1/lean-stokes-theorem` at
  `adffb99be9fd00a42369561068c9d11475cbedb8`.
- Inherited mathlib pin: `v4.29.1`, manifest revision
  `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
- Baseline modules:
  - `Stokes.Box`;
  - `Stokes.SingularCube`;
  - `Stokes.ManifoldForm`;
  - `Stokes.HalfSpace`.
- Baseline theorems:
  - `Stokes.box_stokes_on_box`;
  - `Stokes.box_stokes_extDeriv_smooth`;
  - `Stokes.singular_pullback_extDeriv`;
  - `Stokes.singular_cube_stokes`;
  - `Stokes.singular_cube_boundary_stokes`;
  - `Stokes.singular_cube_chain_stokes`;
  - `Stokes.singular_chain_stokes`;
  - `Stokes.singular_boundary_boundary_zero`;
  - `Stokes.singular_boundary_boundary_zero_general`.

Verification performed:

```text
lake build
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

`lake build` completed successfully. The placeholder scan produced no matches.

## Goal

Formalize Stokes' theorem in Lean 4, starting with Euclidean box and smooth
singular cube statements, then building the missing infrastructure needed for
smooth manifolds with boundary.

The intended final shape is a theorem of the form:

```text
For an oriented compact smooth n-manifold M with boundary and a smooth
compactly supported (n-1)-form omega,
  integral_M d omega = integral_boundary_M omega
```

The exact first global statement may use compact support, compact manifolds, or
a finite-chart formulation depending on which path fits mathlib best.

## Active Execution Goal

Run the Stokes formalization as a controlled parallel-first long run:

- whenever a bottleneck splits into independent proof/API tasks, start a
  worker wave instead of single-threaded exploration;
- each wave may spawn multiple workers for disjoint Lean modules;
- workers must not spawn further workers;
- the main thread keeps one critical-path task locally and owns imports,
  integration, and final verification;
- every integrated wave must return to:

```text
lake build
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

Current wave completed:

- `Stokes.Global.BulkBoundaryIccHalfSpaceTransfer` proves the boundary bulk
  `Icc` to `halfSpaceSupportBox` integral transfer from support containment.
- `Stokes.Global.NaturalCompactSupportBulkAuto` removes the three explicit
  bulk integral-identification fields from the collapsed compact-support
  endpoint when the selected measure is volume and `MeasureLocalBoxTermAPI` is
  available.
- `Stokes.Global.BoundaryCanonicalFaceMeasureFacts` packages canonical
  lower-face measurability and integrability constructors.
- `Stokes.Global.BoundaryCanonicalFiniteReconstruction` connects
  project-local boundary measure data to support-finite target-COV input.
- `Stokes.Global.BoundaryIndicatorCompactSupport` proves compact-support data
  for the indicator-localized canonical boundary face pieces.
- `Stokes.Global.BoundaryCanonicalRouteFromContinuity` combines canonical face
  continuity, project-local boundary measure reconstruction, source alignment,
  and support-finite target-COV input; canonical-face constructors now fill the
  indicator compact-support field automatically.
- `Stokes.BoundaryChart.TargetBoxSourceShrinkInverse` packages the inverse
  half of source-shrink target-box selection.
- `Stokes.BoundaryChart.TargetBoxSourceShrinkIFT` exposes the local
  homeomorphism / IFT-facing constructor for completed source-shrink target-box
  image data.
- `Stokes.BoundaryChart.BoundaryChartPositiveJacobianFromAtlas` adds selected
  box orientation/COV convenience routes from oriented atlas data.
- `Stokes.Global.NaturalCompactSupportInputCollapse` removes the external
  `K/hK/supportSet_eq` bookkeeping from the current compact-support endpoint.
- `Stokes.SingularCube.ManifoldBridge` exposes the chart-local bridge from
  manifold forms to smooth singular cube APIs.
- `Stokes.Global.NaturalCompactSupportSeparatedMeasures` separates the bulk
  and boundary measure spaces, allowing bulk data over `Fin (n + 1) -> Real`
  and boundary data over `Fin n -> Real` before recombining at the M8
  real-valued localization layer.
- `Stokes.Global.MeasureLocalBoxTermAuto` makes the canonical project-local
  box-term choice provide `MeasureLocalBoxTermAPI` by definition, removing the
  manual `measureTerms` and `measureBox` fields from the bulk-auto collapsed
  route.
- `Stokes.BoundaryChart.TargetBoxToM8Glue` connects source-shrink local
  homeomorphism / target-box data to the selected-box target-image builder and
  M8 resolved target-image inputs.
- `Stokes.Global.BoundaryCanonicalRouteFromContinuity` now also exposes a
  compact three-field boundary route input:
  canonical face continuity, project-local boundary measure constructor data,
  and source alignment.
- `Stokes.Global.NaturalCompactSupportCombinedEndpoint` combines the latest
  reduced inputs into one theorem-facing compact-support endpoint: canonical
  project-local bulk measure terms over `Fin (n + 1) -> Real`, canonical
  boundary lower-face measure data over `Fin n -> Real`, separated M8 measure
  localization, and artificial-face cancellation.
- `Stokes.Global.ProjectLocalBoundaryMeasureAuto` packages the remaining
  global boundary measure reconstruction assumptions as
  `ProjectLocalBoundaryGlobalMeasureFacts`, and adds a support-finite route
  that derives the selected a.e. indicator reconstruction from support
  containment.
- `Stokes.Global.BulkExtDerivProjectLocalAuto` packages the canonical
  project-local bulk a.e. input, so callers no longer provide the local
  integrand terms or their measure-term equalities by hand.
- `Stokes.Global.BoundarySourceAlignmentAuto` packages source/project-local
  alignment against selected target-image data and source-shrink M8 resolved
  fields.
- `Stokes.Global.BoundaryCanonicalSupportContainmentAuto` makes the support
  issue precise: indicator-localized canonical lower-face pieces have automatic
  support containment, while raw lower-face scalar representatives need an
  explicit zero-off hypothesis.
- `Stokes.Global.BoundaryGlobalMeasureFactsAuto` switches the boundary global
  measure route to the canonical indicator sum, so the integral representation
  and a.e. reconstruction fields are tautological once the remaining
  partition-term/project-local alignment is supplied.
- `Stokes.Global.BoundarySourceAlignmentConstructors` adds constructors from
  source-shrink/M8 resolved target-image data and project-local constructor
  data to `BoundarySourceTargetImageAlignmentFields`.
- `Stokes.Global.BulkExtDerivProjectLocalConstructors` builds
  `BulkIntegrandAEProjectLocalAutoInput` from localized-form eventual equality
  and selected-partition reconstruction data, with chart support set to `univ`
  so the measure-support field is automatic.
- `Stokes.Global.NaturalCompactSupportEndpointAdapters` groups the current
  compact-support endpoint inputs by construction source and exposes a direct
  audited route to the combined separated-measure endpoint.
- `Stokes.Global.BoundaryPartitionTermAlignmentAuto` feeds selected/extended
  chart-change and COV-family alignment into the canonical indicator boundary
  measure route, so callers no longer need to separately prove the
  `ProjectLocalBoundaryGlobalMeasureFacts` reconstruction once face continuity
  and chart-change alignment are available.
- `Stokes.Global.BoundarySourceAlignmentUnified` packages source-shrink/M8
  target-image data and project-local constructor data from one family, making
  the six source-alignment equalities definitional.
- `Stokes.Global.NaturalCompactSupportEndpointUnified` is the preferred
  boundary-facing endpoint source: it removes `boundaryGlobalMeasure`,
  `boundaryProjectLocal`, `targetImageInput`, and the six source-alignment
  equalities as independent inputs, deriving them from unified boundary data,
  face continuity, and selected chart-change alignment.
- `Stokes.Global.BulkExtDerivFromExtDerivConstructor` constructs the canonical
  bulk `BulkIntegrandAEProjectLocalAutoInput` from
  `PartitionExtDerivConstructorData` or `ExtDerivOnSupportData`, removing
  hand-passed `PartitionReconstructionData` and a.e. measure-support fields
  from this route.
- `Stokes.Global.NaturalEndpointArtificialAuto` builds endpoint
  `M8ArtificialFaceFields` from strict-support buffers, support-zero geometry,
  adjacent selected faces, or overlap-pairing cancellation data, so endpoint
  callers no longer hand-assemble artificial-face cancellation.
- `Stokes.BoundaryChart.SelectedBoxCOVFromOrientationAuto` produces
  `boundaryChartOrientedChangeOfVariables` from selected boxes plus oriented
  atlas/manifold and local-inverse/source-shrink data through the existing
  mathlib change-of-variables route.
- `Stokes.Global.BoundaryChartChangeFromCOVAuto` constructs selected
  boundary chart-change family data from resolved target-image/local-inverse
  COV data and oriented-atlas/oriented-manifold input, reducing the endpoint's
  manual chart-change field.
- `Stokes.Global.BulkExtDerivSelectedAlignmentAuto` constructs the bulk
  exterior-derivative input from selected-partition reconstruction data, making
  the selected active/coefficient alignment automatic when the reconstruction
  genuinely comes from the selected partition.
- `Stokes.Global.BoundaryPartitionTermFromResolvedTarget` proves the resolved
  target-image boundary partition term equals the transported target boundary
  integral using the selected boundary assembly theorem, removing the hand
  proof of `ProjectLocalCompatibility.boundaryPartitionTerm_eq` for the
  unified source-shrink/M8 route.
- `Stokes.Global.BoundaryAtlasMembershipAuto` derives resolved-family source
  and boundary-source atlas membership from target-image/M8 membership plus
  source/project-local alignment, removing manual `hsource` and
  `hboundarySource` from the oriented-atlas COV endpoint path.
- `Stokes.BoundaryChart.CompactImageFromIFTAuto` derives the compact-image
  local-inverse target predicate from actual source-image containment or from
  compact image boxes plus containment, and connects this to local openness and
  IFT target-box selection.  It now also derives compactness of boundary chart
  transition images directly from `boundaryChartSelectedBox`, eliminating the
  separate compact-image hypothesis in the selected-box single-point and finite
  cover IFT routes.
- `Stokes.Global.ArtificialFromCompactSelectionAuto` derives endpoint
  artificial-face support-zero data from compact-support finite active
  selections, localized-piece chart alignment, and strict selected/outer box
  margins.
- `Stokes.Global.NaturalCompactSupportEndpointConcrete` is the most concrete
  theorem-facing endpoint source so far: it generates the bulk a.e. input from
  selected reconstruction data and can generate artificial-face cancellation
  from strict support data.  It now exposes
  `NaturalCompactSupportEndpointSelectedCompactSources`, the shortest endpoint
  source so far, combining selected-reconstruction bulk ext-deriv data with
  compact-selected-box artificial cancellation.

## Current External Progress

### mathlib

Checked snapshot: `leanprover-community/mathlib4` at commit `2715441`
from 2026-05-23.

Relevant existing pieces:

- `Mathlib.Analysis.Calculus.DifferentialForm.Basic` defines `extDeriv`,
  `extDerivWithin`, proves linearity, `extDeriv_extDeriv`, and
  `extDeriv_pullback` for forms on normed spaces.
- `Mathlib.Analysis.Calculus.DifferentialForm.VectorField` proves the vector
  field formula for `extDeriv`, including the commuting-vector-field
  specialization useful for coordinate bases.
- `Mathlib.MeasureTheory.Integral.DivergenceTheorem` proves the Bochner
  divergence theorem on boxes:
  `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`.
- `Mathlib.Geometry.Manifold.*` has smooth manifolds with corners,
  `ContMDiff`, tangent/vector bundle infrastructure, bump functions, smooth
  partitions of unity, and interior/boundary definitions.

Important missing pieces in mathlib for full manifold Stokes:

- bundled smooth differential forms on manifolds;
- integration of differential forms over manifolds;
- manifold orientation and induced boundary orientation API sufficient for
  Stokes;
- a Stokes theorem for smooth manifolds with boundary.

### LeanStokes Prior Art

Checked repository: `https://github.com/d0d1/lean-stokes-theorem` at commit
`adffb99` from 2026-05-07. It is pinned to Lean 4.29.1 and mathlib `v4.29.1`.

What it has:

- sorry-free smooth singular cubical Stokes:
  `SingularCubeStokes.singularStokes`;
- box Stokes via mathlib divergence theorem:
  `CubeStokes.stokes_on_box`;
- bridge from coordinate forms to mathlib `extDeriv`:
  `CubeStokes.stokes_extDeriv_smooth`;
- true pullback of forms via `fderiv`;
- cubical/singular chains and `partial^2 = 0`;
- theorem specializations including FTC, Green, divergence/Gauss, and
  integration by parts.

Scope limitations:

- no integration of forms on manifolds;
- no partition-of-unity definition of manifold integrals;
- no manifold boundary orientation theorem;
- no final smooth-manifold Stokes theorem.

Licensing note: the project is GPL-3.0-only. Use it as prior art unless this
repository deliberately adopts a compatible license.

## Strategy

The fastest credible path is not to jump directly to a global manifold theorem.
First lock down the Euclidean and singular-cube layer, then add the manifold
integration machinery in small testable pieces.

## Long-Run Execution Mode

The active development mode is a controlled parallel Stokes push.

- The endpoint remains the full smooth-manifold Stokes theorem, or the clean
  compact-support version if that is the first mathlib-compatible global
  statement.
- Use parallel agents by default whenever independent blockers can be split into
  disjoint Lean modules or reports.  The expected long-run rhythm is:
  identify a narrow bottleneck family, launch a controlled wave, keep the main
  thread on integration or a non-overlapping critical-path proof, then close the
  wave with focused checks and full repository verification.
- Prefer a wave of several small workers over a single broad worker when the
  blueprint exposes independent proof obligations; keep file ownership
  explicit to avoid merge churn.
- Subagents must never launch further subagents.
- The main thread owns integration, public imports, focused checks, full
  `lake build`, and the forbidden-placeholder scan.
- Each wave should advance a mathematically real bottleneck, not only add
  wrapper layers.

Current long-run objective:

```text
Finish the compact-support/global Stokes route by repeatedly converting
remaining explicit hypotheses into constructors from selected chart boxes,
oriented-atlas data, local inverse/target-image data, and measure-localization
lemmas, while preserving buildability and the no-placeholder invariant after
every wave.  Treat parallel-agent waves as the default engine for this long
run, with the main thread acting as integrator and proof-shape referee.
```

## Milestones

### M0: Lean Workspace Bootstrap

Status: complete.

- Choose repository license.
- Create a Lean 4 project at the root.
- Pin a mathlib version, initially either latest stable or the version used by
  the prior Stokes artifact.
- Add CI or local scripts for `lake build`, placeholder search, and axiom
  checks.
- Add a naming convention for namespaces, likely `Stokes`.

Deliverable: buildable Lean project with a first Stokes wrapper theorem.

Remaining policy item: choose the final repository license. The current code
imports a GPL-3.0-only dependency but does not copy its source.

### M1: Euclidean Box Stokes Baseline

Status: complete as a wrapper over LeanStokes.

- Define or wrap coordinate top coefficients for forms on `Fin n -> R`.
- Prove box Stokes from mathlib's divergence theorem.
- Prove the bridge between coordinate formulas and mathlib `extDeriv`.
- State a clean `stokes_extDeriv_smooth` for boxes.

Deliverable: box Stokes for mathlib differential forms on rectangular boxes,
currently exposed as `Stokes.box_stokes_extDeriv_smooth`.

### M2: Smooth Singular Cubes

Status: complete as a wrapper over LeanStokes.

- Define `SmoothSingularCube n m` as a globally smooth map
  `(Fin n -> R) -> (Fin m -> R)`.
- Define face maps, boundary signs, and pullback via `fderiv`.
- Use `extDeriv_pullback` plus M1 to prove singular cubical Stokes.
- Define finite singular cubical chains and prove `partial^2 = 0`.

Deliverable: singular cubical Stokes and chain-level boundary identity,
currently exposed through `Stokes.SingularCube`.

API note: the public M2 statements use mathlib's `extDeriv`,
`ContDiff`, and `ContinuousAlternatingMap` form representation. The singular
cube and chain types are still inherited from LeanStokes; this is acceptable for
the current milestone, but manifold-facing APIs should avoid depending on
coordinate-only helper types unless they are hidden behind local chart layers.

### M3: Local Manifold Form Layer

Status: started with a minimal, buildable manifold-facing API.

- Design a minimal bundled form API for manifolds, or a thin wrapper around
  chartwise mathlib forms.
- Define pullback of forms by smooth maps in the chartwise setting.
- Prove chart-change compatibility lemmas needed for integration.
- Keep all statements local and finite-dimensional over `R`.

Current API:

- `Stokes.ModelForm`: mathlib differential forms on a model normed vector
  space;
- `Stokes.ManifoldForm`: bare fiberwise forms using mathlib `TangentSpace`;
- `Stokes.ManifoldForm.pullback`: pullback along a map via mathlib `mfderiv`;
- `Stokes.ManifoldForm.inChart`: pull a manifold form back to model coordinates
  through `extChartAt`;
- `Stokes.ManifoldForm.inChart_chartTransition`: chart-overlap
  compatibility of the local form representatives;
- `Stokes.ContinuousAlternatingMap.contDiffOn_compContinuousLinearMap`: a
  smoothness bridge for pulling back continuous alternating maps along a smooth
  family of continuous linear maps, proved via multilinear `CPolynomial`
  smoothness and alternatization;
- `Stokes.ManifoldForm.contDiffOn_transitionPullbackInChart_of_contDiffOn`: the
  direct analytic chart-change lemma deriving smoothness of
  `transitionPullbackInChart` from smoothness of `inChart x1`,
  `chartTransition`, and `chartTransitionDeriv`;
- `Stokes.ManifoldForm.contDiffOn_chartTransition` and
  `Stokes.ManifoldForm.contDiffOn_chartTransitionDeriv`: concrete smoothness of
  the coordinate transition and its derivative, discharged from mathlib's
  extended-chart and tangent-coordinate-change APIs;
- `Stokes.ManifoldForm.chartTransitionDeriv_eq_fderivWithin`: bridge showing
  the project-level transition derivative agrees with mathlib's
  `fderivWithin` coordinate-change derivative on chart overlaps;
- `Stokes.ManifoldForm.transitionPullbackInChart` and
  `Stokes.ManifoldForm.contDiffOn_inChart_of_transitionPullback`: one direction
  of local smoothness transport from the transition-pullback expression to the
  `x0` chart representative;
- `Stokes.ManifoldForm.contDiffOn_transitionPullbackInChart_of_contDiffOn_inChart`
  and `Stokes.ManifoldForm.contDiffOn_transitionPullbackInChart_iff`: the
  reverse direction and the resulting `ContDiffOn` equivalence on chart
  overlaps;
- `Stokes.ManifoldForm.ChartwiseSmooth`: chart-target-local smoothness
  predicate phrased as `ContDiffOn` for `inChart`;
- `Stokes.ManifoldForm.ChartwiseSmooth.contDiffOn_inChart`: restriction of
  chartwise smoothness to smaller model-coordinate domains;
- `Stokes.ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_contDiffOn`:
  chartwise-smooth wrapper for the direct analytic transition-pullback lemma;
- `Stokes.ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart_of_chartAPI`:
  chartwise-smooth transport across chart changes using the concrete mathlib
  smoothness lemmas for `chartTransition` and `chartTransitionDeriv`;
- `Stokes.ManifoldForm.ChartwiseSmooth.contDiffOn_transitionPullbackInChart`:
  ready-to-use smoothness of transition-pullback representatives on subsets of
  a chart target and chart overlap.

Deliverable: chartwise smooth forms and pullback lemmas for manifold charts.
Remaining M3 work is to extend this transport from chart representatives to
the local integration statements and later orientation glue.

### M4: Local Integration and Half-Space Stokes

Status: started with coordinate half-space, boundary-sign conventions, a
box-based local half-space Stokes statement with explicit artificial-face
remainder, and reusable vanishing/cancellation APIs for that remainder.

- Define top-form integration on open subsets of Euclidean space.
- Prove invariance under orientation-preserving chart changes.
- Prove compactly supported local Stokes on boxes and half-spaces.
- Formalize the boundary sign convention with the half-space model.

Current API:

- `Stokes.upperHalfSpace`, `Stokes.upperHalfSpaceBoundary`, and
  `Stokes.upperHalfSpaceInterior`;
- `Stokes.boundaryInclusion` with `Stokes.range_boundaryInclusion`;
- `Stokes.inwardNormal`, `Stokes.outwardNormal`, and boundary tangent/frame
  helpers;
- `Stokes.boundaryTangentInclusion` and
  `Stokes.boundaryTangentProjection`, the linear inclusion/projection maps for
  boundary tangent coordinates;
- `Stokes.det_outwardFirstBoundaryMatrix`, proving the outward-normal-first
  boundary frame has determinant `-1` relative to the ambient standard frame;
- `Stokes.coordinateOrientationSign`,
  `Stokes.outwardFirstBoundaryOrientationSign`, and
  `Stokes.halfSpaceBoundarySign_eq_outwardFirstBoundaryOrientationSign`,
  giving the minimal finite-frame orientation sign bridge and proving that the
  half-space lower-face sign agrees with the outward-normal-first boundary
  orientation convention;
- `Stokes.upperFaceSign`, `Stokes.lowerFaceSign`, and
  `Stokes.halfSpaceBoundarySign_eq`, fixing the lower `x₀ = 0` boundary sign
  as `-1`;
- `Stokes.boxLowerZeroCoordFaceTerm_eq_halfSpaceBoundaryCoordTerm` and
  `Stokes.boxLowerZeroCoordFaceTerm_toCoordNForm_eq_halfSpaceBoundaryFormTerm`,
  connecting the lower `0`-face term from the box boundary integral to the
  half-space boundary-sign convention;
- `Stokes.boundaryInclusion_mem_Icc_of_mem_lowerZeroFaceDomain`, recording the
  basic geometry that points of the lower boundary face lie in the selected
  ambient box;
- `Stokes.boundaryTangentPullbackForm`,
  `Stokes.boundaryTangentPullbackForm_comp_apply_basisFun_eq_det_mul`, and
  `Stokes.ambientBoundaryForm_tangentMap_eq_det_mul`, proving the algebraic
  top-degree determinant rule for boundary tangent maps before any
  measure-theoretic change-of-variables theorem is used;
- `Stokes.boxUpperCoordFaceTerm`, `Stokes.boxLowerCoordFaceTerm`,
  `Stokes.boxUpperFormFaceIntegral`, and `Stokes.boxLowerFormFaceIntegral`,
  giving reusable coordinate and mathlib-form APIs for every box face;
- `Stokes.halfSpaceSupportBox`, `Stokes.boxFaceCoeffTSupportInHalfSpaceBox`,
  and `Stokes.exists_halfSpaceSupportBox_of_isCompact`, packaging the
  compact-support chart-box selection condition and proving that compact
  subsets of the half-space admit such a selected box;
- `Stokes.boxFormFaceCoeff_tsupport_subset` and
  `Stokes.boxFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset`, showing that
  if a full chart representative is topologically supported in the selected
  half-space box, then all face coefficients satisfy the selected-box support
  predicate;
- `Stokes.toCoordNForm_contDiffOn`, the local-smoothness bridge from mathlib
  forms to LeanStokes coordinate coefficients;
- `Stokes.boxRemainingFormFaceTerms` and
  `Stokes.bdryIntegral_eq_lowerZero_add_remaining`, splitting the box boundary
  into the geometric lower `0`-face plus all artificial auxiliary-box faces;
- `Stokes.boxRemainingFormFaceTerms_eq_zero_of_face_cancellation`,
  `Stokes.boxRemainingFormFaceTerms_eq_zero_of_support_disjoint`, and
  `Stokes.boxRemainingFormFaceTerms_eq_zero_of_tsupport_disjoint`, proving the
  artificial face remainder vanishes when signed face pairs cancel or when the
  face coefficient support/topological support misses each artificial face;
- `Stokes.boxRemainingFormFaceTerms_eq_zero_of_tsupport_subset_halfSpaceSupportBox`,
  deriving artificial-face vanishing directly from the selected compact-support
  box condition;
- `Stokes.box_stokes_extDeriv_contDiffOn_isOpen`, proving box Stokes for
  mathlib forms that are smooth on an open neighborhood of the closed box,
  rather than globally smooth;
- `Stokes.halfSpaceLocalStokes_with_remainder`,
  `Stokes.halfSpaceLocalStokes_with_remainder_of_contDiffOn_isOpen`,
  `Stokes.halfSpaceLocalStokes_of_remainder_eq_zero`, and
  `Stokes.halfSpaceLocalStokes_of_remainder_eq_zero_of_contDiffOn_isOpen`,
  assembling the local half-space Stokes statement from box Stokes in both
  global-smooth and local-smooth forms;
- `Stokes.halfSpaceLocalStokes_of_face_cancellation`,
  `Stokes.halfSpaceLocalStokes_of_support_disjoint`, and
  `Stokes.halfSpaceLocalStokes_of_tsupport_disjoint`, feeding those
  artificial-face hypotheses directly into the local half-space Stokes
  statement;
- `Stokes.halfSpaceLocalStokes_compactSupport`,
  `Stokes.halfSpaceLocalStokes_compactSupport_of_contDiffOn_isOpen`,
  `Stokes.localHalfSpaceStokes_compactSupport`, and
  `Stokes.localHalfSpaceStokes_compactSupport_of_contDiffOn_isOpen`, the
  cleaner selected-box local Stokes statements;
- `Stokes.halfSpaceBoundaryTransitionFormIntegral`,
  `Stokes.contDiffOn_transitionPullbackInChart_upperHalfSpaceBoundary`,
  `Stokes.contDiffOn_transitionPullbackInChart_halfSpaceBox`, and
  `Stokes.boxLowerZeroCoordFaceTerm_transitionPullback_eq_halfSpaceBoundaryTransitionFormTerm`,
  feeding chart-transition pullbacks into the half-space boundary term;
- `Stokes.boxFaceCoeffTSupportInHalfSpaceBox_transitionPullback_of_tsupport_subset`,
  `Stokes.halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset`,
  and `Stokes.exists_halfSpaceTransitionFaceCoeffTSupportInHalfSpaceBox_of_isCompact`,
  connecting compact support of a manifold form's transition-pullback chart
  representative to the selected-box face coefficient predicates;
- `Stokes.boundaryChartDomain`, `Stokes.boundaryChartSelectedBox`, and
  `Stokes.boundaryChartExtendedBox`, packaging the natural chart target/overlap
  domain, the chosen half-space chart box, and the ambient smooth extension
  witness currently needed by the `extDeriv` box theorem.  The extension witness
  is intentionally separate because chart targets for manifolds with boundary
  are generally relatively open in `range I`, not ambient-open subsets of the
  model vector space;
- `Stokes.boundaryChartTransition`,
  `Stokes.boundaryChartTransitionTangentMap`,
  `Stokes.boundaryChartTransitionMatrix`, and
  `Stokes.boundaryChartTransitionJacobian`, defining the boundary coordinate
  transition, its tangential derivative, and its Jacobian determinant;
- `Stokes.boundaryChartTransitionPreservesBoundaryAt` and
  `Stokes.boundaryChartTransitionDerivPreservesTangentAt`, the explicit local
  hypotheses needed to say an ambient chart transition preserves the boundary
  face and sends boundary tangent vectors to boundary tangent vectors;
- `Stokes.boundaryChartTransition_pointwise_pullback_det`, the M5.3 pointwise
  chart-change/Jacobian formula for the boundary integrand;
- `Stokes.boundaryChartTransitionCompatibleOn`,
  `Stokes.boundaryChartOrientationCompatibleOn`,
  `Stokes.boundaryChartTransitionJacobianIntegrand`, and
  `Stokes.boundaryChartOrientedChangeOfVariables`, packaging boundary
  preservation, tangent preservation, positive tangential Jacobian, and the
  Jacobian-weighted local change-of-variables equality;
- `Stokes.halfSpaceBoundaryTransitionFormIntegral_eq_inChart_of_orientedChangeOfVariables`
  and
  `Stokes.outwardFirstBoundaryChartIntegral_eq_inChart_of_orientedChangeOfVariables`,
  lifting the pointwise Jacobian formula to an integral-level boundary chart
  change statement under the oriented change-of-variables package;
- `Stokes.halfSpaceBoundaryInChartIntegral`,
  `Stokes.outwardFirstBoundaryInChartIntegral`, and
  `Stokes.boundaryChartChangeCompatible`, giving a fixed-boundary-chart target
  for comparing transition-pulled boundary representatives;
- `Stokes.halfSpaceBoundaryTransitionFormIntegral_eq_inChart_of_boundaryFace_subset_overlap`
  and
  `Stokes.outwardFirstBoundaryChartIntegral_eq_inChart_of_boundaryFace_subset_overlap`,
  proving that the boundary integral computed from a transition-pulled
  representative agrees with the direct `x0` chart representative on the
  boundary face;
- `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant`,
  `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant_of_selectedBoxes`,
  and
  `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant_of_extendedBoxes`,
  proving the current M5.2 chart-change invariance theorem: for a fixed
  boundary chart `x0` and fixed boundary box, the outward-normal-first boundary
  integral is independent of which overlapping auxiliary chart is used to write
  the transition-pullback representative;
- `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables`,
  `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_selected`,
  and
  `Stokes.outwardFirstBoundaryChartIntegral_chartChange_invariant_of_orientedChangeOfVariables_extended`,
  proving the integral-level orientation-compatible boundary chart-change
  invariant form, with the actual MeasureTheory change-of-variables theorem
  still packaged as a local hypothesis;
- `Stokes.halfSpaceLocalStokes_transitionPullback_with_remainder` and
  `Stokes.halfSpaceLocalStokes_transitionPullback_of_remainder_eq_zero`, the
  same local statement for transition-pulled chart representatives;
- `Stokes.halfSpaceLocalStokes_transitionPullback_of_face_cancellation`,
  `Stokes.halfSpaceLocalStokes_transitionPullback_of_support_disjoint`, and
  `Stokes.halfSpaceLocalStokes_transitionPullback_of_tsupport_disjoint`, the
  transition-pullback versions needed for compact-support local chart boxes;
- `Stokes.halfSpaceLocalStokes_transitionPullback_compactSupport`,
  `Stokes.halfSpaceLocalStokes_transitionPullback_compactSupport_of_contDiffOn_isOpen`,
  `Stokes.localHalfSpaceStokes_transitionPullback_compactSupport`, and
  `Stokes.localHalfSpaceStokes_transitionPullback_compactSupport_of_contDiffOn_isOpen`,
  selected-box local Stokes for transition-pulled chart representatives;
- `Stokes.boundaryChartLocalStokes_transitionPullback_compactSupport` and
  `Stokes.boundaryChartLocalStokes_transitionPullback_compactSupport_eq`, a
  boundary-chart package combining `ChartwiseSmooth` smoothness on an open
  chart-box neighborhood, transition-pullback support control, and the
  selected-box local Stokes equality without a global `ContDiff` assumption;
- `Stokes.boundaryChartLocalStokes_transitionPullback_of_extendedBox` and
  `Stokes.boundaryChartLocalStokes_transitionPullback_of_extendedBox_package`,
  the M4.6 natural-input wrappers: callers pass a selected/extended boundary
  chart box instead of threading the ambient open neighborhood through the
  theorem statement;
- `Stokes.outwardFirstBoundaryChartIntegral`,
  `Stokes.outwardFirstBoundaryChartIntegral_eq_halfSpaceBoundarySign_mul`,
  `Stokes.boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst`,
  and
  `Stokes.boundaryChartLocalStokes_transitionPullback_of_extendedBox_outwardFirst_package`,
  rephrasing the local boundary chart theorem with the boundary integral
  oriented by the outward-normal-first convention;
- wrappers for mathlib's `𝓡∂ n` range and frontier descriptions.

Deliverable: local Stokes theorem in chart domains, including boundary charts.

### M5: Orientation and Boundary Orientation

M5.1 status: done as a minimal local sign bridge.  The current API proves that
the half-space lower-face sign `halfSpaceBoundarySign n` equals the determinant
sign of the outward-normal-first boundary frame, and exposes local boundary
chart Stokes with an `outwardFirstBoundaryChartIntegral` right-hand side.

M5.2 status: started with the fixed-boundary-chart invariance theorem.  For a
fixed boundary chart `x0` and fixed lower-face box, the
`outwardFirstBoundaryChartIntegral` is now proved independent of the overlapping
auxiliary chart used to write the transition pullback.  The stronger theorem
comparing different boundary coordinate boxes remains a change-of-variables
task.

M5.3 status: done as a pointwise Jacobian layer.  Boundary chart transitions,
their tangential derivative matrices, and the determinant factor for top-degree
boundary integrands are now formalized.  The proof is conditional on explicit
boundary-preservation and tangent-preservation hypotheses; deriving those
hypotheses automatically from the half-space model/frontier API is a separate
next step.

M5.4 status: started with the theorem-facing invariant form.  The new
`boundaryChartOrientedChangeOfVariables` package includes boundary/tangent
compatibility, positive tangential Jacobian, and the Jacobian-weighted integral
identity.  Under that package, `outwardFirstBoundaryChartIntegral` is proved
invariant when changing from one boundary chart box to another.  Remaining work
is to prove the package from mathlib's concrete change-of-variables and
half-space chart APIs.

- Build the minimal orientation API needed for finite-dimensional smooth
  manifolds.
- Define induced orientation on the boundary.
- Prove local sign compatibility between outward-normal-first convention and
  the half-space theorem.

Deliverable: oriented boundary integration agrees with local Stokes signs.

### M6: Manifold Integration via Partition of Unity

M6.0 status: done.  The half-space and boundary-chart modules have been split
enough to support parallel development without forcing all work through a
single file.

M6.1 status: in progress.  The compact-support artificial-face route now has a
strict-buffer API:

- `Stokes.CompactSupportBoxBuffer`;
- `Stokes.CompactSupportBoxBuffer.ofLocalizedInteriorCoefficientBuffer`;
- `Stokes.LocalizedInteriorFormInnerBoxBuffer`;
- `Stokes.LocalizedInteriorCoefficientInnerBoxBuffer`;
- `Stokes.Icc_subset_boxInteriorSupportBox`;
- `Stokes.exists_boxInteriorSupportBox_subset_of_isCompact`.

This reduces artificial-face cancellation to proving that selected localized
chart representatives, or their transition coefficients, are supported in an
inner closed coordinate box with a strict margin inside the selected outer box.

Recent M6.1 strict-buffer and selected-box alignment modules:

- `Stokes.Global.NaturalCompactActiveStrictBuilder`;
- `Stokes.Global.SelectedPartitionCompactActiveAlignment`;
- `Stokes.Global.LocalizedInteriorPieceAlignment`;
- `Stokes.Global.BulkMeasureSelectedBoxAlignment`;
- `Stokes.Global.BoundaryTargetSelectedBoxAlignment`;
- `Stokes.Global.TargetOrientationSelectedBoxAlignment`.

These modules reduce a significant part of the artificial-face and selected-box
bookkeeping to reusable constructors.  They do not yet prove the true bulk or
boundary measure-localization equalities.

The next controlled parallel wave added:

- `Stokes.Global.NaturalMeasureStrictBuilder`;
- `Stokes.Global.BoundaryTargetMeasureBuilderGlue`;
- `Stokes.Global.BulkMeasurePartitionLocalizationWrappers`;
- `Stokes.Global.BoundaryMeasurePartitionLocalizationWrappers`;
- `Stokes.Global.LocalizedInteriorConstructorAlignment`;
- `Stokes.BoundaryChart.TargetImageSelectedBoxBuilder`;
- `Stokes.BoundaryChart.OrientationAtlasSelectedBoxBuilder`;
- `reports/m8_end_to_end_gap_audit.md`.

This wave pushed the wrapper layer close to the current theorem endpoint:
`naturalCompactSupportStokes_canonical` already exists, and the central remaining
problem is constructing its `NaturalCompactSupportStokesInput` from natural
geometric and measure-theoretic data.

M6.2 status: started with `Stokes.Global.EndToEndRemainingInput`.

- `NaturalCompactSupportEndToEndInput` records the current shortest
  end-to-end construction route:
  compact-support form data, selected partition, target-image input, selected
  bulk measure data, canonical boundary target compact-support data, compact
  active boxes, localized-piece chart alignment, and strict outer-box margins.
- `NaturalCompactSupportEndToEndInput.toNaturalCompactSupportStokesInput`
  converts this record to the existing natural input.
- `naturalCompactSupportStokes_canonical_of_endToEnd` exposes the current
  theorem endpoint in canonical names.

This is a zero-semantics staging interface: it proves no new measure, IFT, COV,
or orientation fact, but it makes the remaining proof debt exact and parallel
friendly.

The following parallel wave began replacing the largest end-to-end fields by
smaller, more geometric or analytic inputs:

- `Stokes.Global.BulkMeasureExtDerivFromPartition` fixes canonical bulk scalar
  terms and packages the remaining bulk measure facts in
  `SelectedPartitionBulkMeasureExtDerivInput`, which constructs
  `BulkMeasureFromPartitionData`.
- `Stokes.Global.BoundaryMeasureFromTargetCOV` transports target-image COV data
  into the boundary set-integral field, reducing the remaining input to source
  project-local boundary integral equals selected set integral.
- `Stokes.Global.BoundaryMeasureAEReconstruction` proves support-based finite
  indicator reconstruction, reducing the AE boundary field to a finite
  piece-sum equality plus support containment.
- `Stokes.BoundaryChart.TargetBoxFromIFT` constructs target-box selection and
  selected-box auto-data from local openness plus compact-image containment.
- `Stokes.BoundaryChart.OrientedAtlasFromMathlib` gives a fieldized
  `Orientation.map` bridge from mathlib linear orientation data to the
  project-local boundary oriented atlas.
- `Stokes.Global.CompactSupportSelectedBoxEndToEnd` connects compact-support
  finite active selections, strict margins, and localized chart alignment to
  `NaturalCompactSupportEndToEndInput`.
- `Stokes.Global.MeasureBuilderFromCanonicalPieces` composes the canonical bulk
  ext-derivative input and boundary COV input with the selected-box branch,
  exposing `naturalCompactSupportStokes_canonical_of_canonicalPieces`.

This wave did not finish global Stokes, but it shrank the major black-box
fields into more local obligations: bulk measure facts, source boundary
set-integral facts, boundary finite piece-sum/support facts, compact-image
target-box containment, and fieldized orientation compatibility.  The current
theorem-facing route is:

```text
NaturalCompactSupportCanonicalPiecesInput
  -> NaturalCompactSupportEndToEndInput
  -> NaturalCompactSupportStokesInput
  -> naturalCompactSupportStokes_canonical
```

After local-facts composition, the more refined route is:

```text
NaturalCompactSupportLocalFactsInput
  -> NaturalCompactSupportCanonicalPiecesInput
  -> NaturalCompactSupportEndToEndInput
  -> naturalCompactSupportStokes_canonical
```

The next parallel wave reduced several fields further:

- `Stokes.Global.BulkMeasureCanonicalLocalFacts` proves canonical bulk scalar
  terms vanish off their selected boxes from localized support data, leaving the
  bulk integral equalities and local compact-support construction as the main
  bulk blockers.
- `Stokes.Global.BoundarySourceSetIntegral` isolates the source project-local
  boundary set-integral theorem and aligns it with existing
  `ProjectLocalBoundaryMeasureData`.
- `Stokes.Global.BoundaryPieceSupportFiniteSum` reduces boundary AE
  reconstruction to a finite piece-sum equality plus support containment, and
  makes support automatic for indicator-localized pieces.
- `Stokes.BoundaryChart.TargetBoxCompactImage` separates compact source-image
  containment from local-openness target-box selection, clarifying that the
  source box generally must be shrunk or the target box chosen to contain a
  compact image bounding box.
- `Stokes.BoundaryChart.OrientationMapCompatibility` relates fieldized
  `Orientation.map` compatibility to positive tangential Jacobian data and
  documents the current mathlib manifold-orientation gap in
  `reports/orientation_map_compatibility_gap.md`.
- `Stokes.Global.CanonicalPiecesFromLocalFacts` composes local bulk facts and
  support-finite boundary COV data into the canonical-pieces endpoint, exposing
  `naturalCompactSupportStokes_canonical_of_localFacts`.

The latest parallel wave reduced the remaining local-facts fields:

- `Stokes.Global.BulkLocalTermCompactSupportConstructor` constructs
  `BulkLocalTermCompactSupportData` from localized smooth neighborhoods and
  support control.
- `Stokes.Global.BulkMeasureIntegralIdentities` reduces the three bulk integral
  equalities to local set-integral identities and a boundary
  `Icc`-to-`halfSpaceSupportBox` transfer.
- `Stokes.Global.ProjectLocalBoundaryMeasureConstructor` expands
  `projectLocalBoundaryIntegral` as the canonical lower-zero-face set integral
  and routes it to `BoundarySourceSetIntegralInput`.
- `Stokes.BoundaryChart.TargetBoxSourceShrink` formalizes the recommended
  target-box geometry route: shrink source boundary boxes so their images land
  in a fixed target box.
- `Stokes.BoundaryChart.PositiveJacobianOrientationRoute` runs the local
  positive-Jacobian orientation path through the boundary-sign/COV APIs.
- `Stokes.Global.NaturalCompactSupportSeparatedMeasures` fixes the main
  measure-space mismatch by combining ambient bulk measure data and
  lower-dimensional boundary measure data only at the M8 localization layer.
- `Stokes.Global.MeasureLocalBoxTermAuto` collapses the measure-local box API
  to a canonical project-local box-term choice.
- `Stokes.Global.BoundaryCanonicalRouteFromContinuity` now builds the
  full boundary canonical route from a compact theorem-facing triple.
- `Stokes.BoundaryChart.TargetBoxToM8Glue` packages source-shrink target-box
  data as selected-box/M8 target-image resolved input.
- `Stokes.Global.NaturalCompactSupportCombinedEndpoint` is now the preferred
  current endpoint for the compact-support route: it no longer forces the
  boundary measure to live in the ambient chart space and no longer asks for
  manual `MeasureLocalBoxTermAPI` data.
- The same endpoint now has migration constructors from the older bulk
  project-local-auto input, plus variants that consume
  `ProjectLocalBoundaryGlobalMeasureFacts`,
  `ProjectLocalBoundarySupportFiniteMeasureFacts`,
  `BulkIntegrandAEProjectLocalAutoInput`, and
  `BoundarySourceTargetImageAlignmentFields`.
- `Stokes.Global.NaturalCompactSupportEndpointSelectedCompactAuto` now lets the
  selected-reconstruction endpoint consume the three remaining compact-selection
  geometry fields directly, without manual
  `EndpointCompactSelectionArtificialAlignment` assembly.
- `Stokes.Global.NaturalCompactSupportEndpointSelectedAuto` exposes the shorter
  selected-reconstruction endpoint route directly: selected reconstruction plus
  compact-selection artificial alignment generate the bulk a.e. input,
  artificial fields, and endpoint theorem.
- `Stokes.BoundaryChart.SelectedBoxImageDataAuto` provides theorem-facing
  selected-box routes from local-openness or IFT data directly to oriented
  boundary change-of-variables statements, generating the target image data
  internally from the selected-box image pipeline.
- `Stokes.BoundaryChart.SelectedBoxIFTAuto` packages the selected-box IFT
  route so callers no longer pass `IsCompact image` or raw
  `compactImageForLocalInverseTargets`; the remaining real field is compact
  coordinate image-box containment inside selected local-inverse targets.
- `Stokes.Global.NaturalCompactSupportEndpointConstructorFieldsAuto` lets the
  selected-reconstruction compact endpoint consume constructor-side
  `LocalizedInteriorM8ChartAlignment` and generate the endpoint-facing
  `LocalizedInteriorPieceAlignment`; the remaining compact-selection fields are
  the two strict selected/outer margin inequalities.
- `Stokes.BoundaryChart.SelectedBoxContainsAuto` adds selected image-box,
  image-subset, `MapsTo`, and IFT routes to oriented boundary COV, so callers
  can avoid the stronger arbitrary compact-box `hcontains` callback when a
  selected box shrink supplies direct image containment.
- `Stokes.Global.SelectedReconstructionSourceAuto` packages the selected
  reconstruction origin so endpoint callers can supply a reconstruction source
  instead of a loose `reconstruction_active` equality.
- `Stokes.Global.NaturalCompactSupportEndpointMarginAuto` replaces the two
  exposed selected/outer strict-margin inequalities with the existing
  `SelectedBoxStrictMarginData` route, and provides an
  `ActiveStrictInnerOuterBoxSelections` bridge when box identifications are
  available.
- `Stokes.BoundaryChart.SelectedImageBoxFromTargetAuto` builds selected
  image-box containment and oriented COV routes from target-box or compact
  image-box data, avoiding manual record assembly at call sites.
- `Stokes.BoundaryChart.SourceShrinkMapsToAuto` projects source-shrink
  `MapsTo`/image-subset facts into selected target-image and oriented COV
  APIs.
- `Stokes.Global.SelectedReconstructionSourceConstructorsAuto` routes older
  ext-derivative endpoint sources and generated selected-partition
  constructors into the source-packaged reconstruction endpoint.
- `Stokes.Global.NaturalCompactSupportEndpointMarginConstructorsAuto` replaces
  four exposed selected/outer box-identification facts with the natural
  geometric condition that each selected compact box lies inside the endpoint
  localized outer box.
- `Stokes.Global.NaturalCompactSupportEndpointFacade` is the first
  endpoint-facing facade: callers can use source-packaged reconstruction,
  M8 chart alignment, and margin data without knowing the older endpoint
  base records.
- `Stokes.BoundaryChart.SelectedImageBoxContainmentFromShrinkAuto` reduces the
  `target_contains_selectedImageBox` callback to lower-zero box containment,
  tangent bounds, or ambient target shrink data.
- `Stokes.BoundaryChart.SourceShrinkSelectedCOVFacade` packages source-shrink
  inverse/local-homeomorphism data directly into selected boundary-chart COV
  statements, with the remaining geometry named as one containment predicate.
- `Stokes.BoundaryChart.BoundaryChartCOVFacade` and
  `reports/stokes_module_consolidation_audit.md` start the facade-first module
  consolidation strategy: keep small proof files, but expose stable public
  entry points instead of asking global code to import every adapter directly.
- `Stokes.Global.EndpointLocalizedOuterBoxFromCompactSelectionAuto` proves the
  endpoint localized outer-box containment from existing strict-buffer
  alignment data, so `compactBox_subset_endpointInterior` is no longer an
  isolated endpoint hypothesis.
- `Stokes.Global.CompactSupportEndpointFacade` is now the preferred endpoint
  public API: source-packaged or ext-deriv endpoint sources plus M8 chart
  alignment and localized outer-box / strict-buffer / outer-box data imply the
  endpoint Stokes equality.
- `Stokes.BoundaryChart.LaterTargetShrinkFromSelectionAuto` packages the
  remaining boundary later-target inclusion as coordinatewise shrink data and
  connects it to local-openness, IFT target covers, and source-shrink
  containment.
- `Stokes.BoundaryChart.SourceShrinkSelectedCOVFromShrinkAuto` lets
  source-shrink inverse/local-homeomorphism data plus ambient shrink or
  tangent-bound data produce selected boundary COV statements directly.
- `Stokes.BoundaryChart.BoundaryChartGeometryFacade` provides a pure geometry
  public import layer for selected boxes, local inverses, target boxes,
  source-shrink, and later-target shrink APIs without pulling in global/M8
  glue.
- `reports/stokes_next_hard_gaps.md` records the current real bottlenecks:
  coherent endpoint strict-box construction, controlled boundary target-box
  selection, then global compact-support partition/orientation/integration.
- `Stokes.Global.CompactActiveStrictBufferConstructorAuto` moves endpoint
  strict-buffer alignment one step upstream: one strict outer-box source around
  compact active boxes now generates the downstream
  `CompactActiveBoxStrictBufferAlignment`.
- `Stokes.BoundaryChart.ConstrainedTargetBoxSelectionAuto` fixes the boundary
  target-box API shape: later target boxes should be chosen by a controlled
  selection record rather than quantified over arbitrarily.
- `Stokes.BoundaryChart.OrientationToCOVFacade` lets selected-box and
  source-shrink COV routes consume mathlib-facing orientation bridge data
  directly, with all-chart oriented-manifold data installed locally.
- `Stokes.Global.CanonicalCompactSupportEndpointFacade` lifts current endpoint
  and separated compact-support routes to the canonical equality
  `manifoldExtDerivIntegral = boundaryFormIntegral`.
- `Stokes.Global.ArtificialFaceCancellationFacade` gives the compact-support
  route a single theorem-facing artificial-face cancellation input instead of
  exposing all support-zero / adjacent-face / overlap-pairing constructors.
- `Stokes.SingularCube.SmoothBridgeFacade` and
  `reports/smooth_singular_bridge_gap.md` define a parallel smooth-singular
  bridge path; its next hard theorem is local singular Stokes from a smooth
  extension of the chart representative.
- `Stokes.BoundaryChart.ControlledTargetBoxFromLocalInverseAuto` constructs
  controlled target boxes from local-openness/local-inverse/source-shrink data,
  so the boundary chart-change route no longer quantifies over arbitrary later
  target boxes.
- `Stokes.SingularCube.IntegralCongruence` proves congruence lemmas for
  singular-cube bulk and boundary integrals, isolating the remaining analytic
  gap to locality of `extDeriv` under equality on a neighborhood.
- `Stokes.Global.NaturalCompactSupportPartitionConstructorAuto` packages
  compact-support/partition data into the selected-partition and ext-deriv
  endpoint fields used by the compact-support route.
- `Stokes.Global.CompactActiveStrictOuterBoxFromLocalizedPiecesAuto` makes
  strict outer boxes definitional from localized-piece corners; callers now
  only provide the genuine strict margin facts.
- `Stokes.Global.ArtificialFaceFromStrictBufferAuto` derives the public
  artificial-face cancellation input from strict-buffer alignment/constructor
  data.
- `Stokes.BoundaryChart.OrientationMembershipAuto` packages the oriented-atlas
  membership proofs required by boundary chart-change COV routes.
- `Stokes.Global.LocalizedPieceStrictMarginsAuto` turns existing selected-box
  strict margins into the compact-active localized-piece strict margins needed
  by the endpoint strict-buffer route.
- `Stokes.BoundaryChart.ControlledTargetBoxFromIFTAuto` connects controlled
  target-box selection to the IFT/local-openness and selected-box APIs, removing
  more raw compact-image/local-inverse bookkeeping.
- `Stokes.SingularCube.ExtDerivLocality` discharges the smooth-singular bridge
  blocker that neighborhood equality of Euclidean forms implies equality of
  their `extDeriv` on cube images.
- `Stokes.Global.NaturalFiniteActiveChartBoxSelectionAuto` packages compact
  chart supports, selected chart boxes, and chartwise smoothness neighborhoods
  into finite-active compact-support selection data.
- `Stokes.Global.BoundaryOrientationMembershipToCOVAuto` projects global
  boundary atlas membership into the local two-chart orientation membership
  used by boundary COV routes.
- `Stokes.Global.BoundaryControlledTargetToM8Auto` turns controlled boundary
  target families into the resolved target-image and M8 input packages.
- `Stokes.Global.NaturalCompactSupportEndpointEndToEndAuto` combines partition
  constructor data, localized-piece strict margins, artificial-face
  cancellation, and canonical endpoint names into a higher-level compact-support
  endpoint theorem.
- `Stokes.Global.CurrentGapReductionAudit` and
  `reports/current_gap_reduction_audit.md` classify remaining inputs as
  automated fields, genuine mathematical fields, or engineering glue.
- `Stokes.Global.SelectedStrictMarginsFromChartBoxAuto` proves that selected
  chart-box strict containment yields `SelectedBoxStrictMarginData`, and routes
  this containment directly into endpoint Stokes wrappers.
- `Stokes.Global.NaturalStrictAlignmentFromFiniteSelectionAuto` packages the
  strict/alignment data generated after finite-active chart-box selection, so
  endpoint callers no longer pass selected-partition alignment and localized
  strict-margin projections separately.
- `Stokes.BoundaryChart.CompactImageBoxContainmentAuto` connects selected image
  containment and later-target shrink data to controlled target-box selection,
  reducing the remaining `compactBox_subset` / `hcontains` style fields.
- `Stokes.Global.BoundaryControlledTargetOrientationEndpointAuto` and
  `Stokes.Global.BoundaryCanonicalTargetFromControlledCOVAuto` push controlled
  boundary target families through orientation-membership COV into canonical
  boundary route, compact-support boundary target, and boundary-only M8 measure
  packages.
- `Stokes.Global.NaturalCompactSupportEndpointNaturalInputAuto` exposes a more
  natural compact-support endpoint input based on compactly supported form data,
  finite-active chart boxes, and boundary/measure packages.
- `Stokes.SingularCube.SmoothBridgeLocalityFacade` gives the smooth-singular
  route theorem statements with local extension equality on neighborhoods or
  open sets, hiding the pointwise `extDeriv` congruence hypothesis.
- `Stokes.Global.HighLeverageGapAudit` and
  `reports/high_leverage_gap_audit.md` identify the next highest-yield
  reductions; the audit file remains outside public facades by design.
- `Stokes.Global.EndpointSelectedStrictMarginsFromNaturalChartBoxesAuto` and
  `Stokes.Global.CompactSupportEndpointSelectedMarginFacade` promote the
  selected-margin compact-support endpoint to theorem-facing wrappers, including
  direct routes from chart-box containment and active strict inner/outer boxes.
- `Stokes.BoundaryChart.ControlledTargetNoContainmentAuto` gives selected-box
  IFT/local-openness constructors that consume target-box shrink or tangent
  bounds instead of exposing `compactBox_subset` / `hcontains` fields.
- `Stokes.Global.BoundaryUnifiedToControlledM8InputAuto` turns unified
  source-shrink boundary data directly into `M8BoundaryControlledTargetInput`,
  removing manual controlled target-family assembly.
- `Stokes.Global.BoundaryCanonicalTargetNaturalInputAuto` packages controlled
  boundary target data with project-local global/support-finite measure facts
  and face continuity into canonical boundary target and boundary-only M8
  measure inputs.
- `Stokes.Global.BulkCanonicalLocalFactsFromExtDerivAuto` builds the bulk
  canonical local-facts route from ext-deriv constructor or partition
  reconstruction data once the boundary active-chart alignment is supplied.
- `Stokes.Global.NaturalFiniteActiveFromCompactSupportAuto` pushes natural
  finite-active chart-box selection upstream to compact support/source-support
  data.
- `Stokes.Global.NaturalEndpointStrictAlignmentRouteAuto` connects natural
  endpoint inputs and strict-alignment packages directly to canonical equality
  statements.
- `Stokes.SingularCube.SmoothBridgeExtensionInputAuto` packages the smooth
  singular local extension hypotheses into one open-extension input record and
  states the future extension theorem output shape.
- `Stokes.Global.IntegrationDependencyAudit` and
  `reports/integration_dependency_audit.md` record public import risks; the
  audit file remains private.

- Use mathlib smooth partitions of unity to define integrals of compactly
  supported top forms.
- Prove independence of partition and chart choices.
- Establish linearity, support restriction, and local-to-global summation
  lemmas.

Deliverable: `integral_form M omega` for oriented smooth manifolds in the
needed finite-dimensional compact-support setting.

### M7: Global Smooth Manifold Stokes

- Reduce a compactly supported form to a locally finite partition of unity.
- Apply M4 in each chart.
- Show interior chart boundary terms cancel or vanish.
- Show boundary chart terms assemble to the induced boundary integral.

Deliverable: first global Stokes theorem for oriented smooth manifolds with
boundary.

### M8: Upstreaming and Case Studies

- Split definitions and lemmas into upstreamable mathlib-sized PRs.
- Add examples: interval FTC, Green's theorem, Gauss/divergence theorem, and
  a simple compact manifold-with-boundary example.
- Write documentation explaining theorem statements and sign conventions.

Deliverable: documented formalization with upstream-ready modules.

## Immediate Next Steps

1. Build a single natural selected chart-box constructor that produces the
   selected-reconstruction compact endpoint from compact-support form data,
   selected boxes, unified source-shrink/M8 boundary data, and the remaining
   compact-selection geometry fields.
2. Prove or route the remaining selected reconstruction equality
   `selectedPartitionBulkActive P boundary = R.activeCharts` from the actual
   partition reconstruction constructor that creates `R`.
3. Produce constructor-side localized chart alignment and the two strict
   selected/outer box margins required by the compact endpoint from the
   existing compact-support box selection and localized-interior construction.
4. Use `SelectedBoxContainsAuto` to replace remaining compact-image target
   hypotheses in source-shrink/local-inverse target-image builders with
   direct `image_subset`/`MapsTo` facts from selected box shrink.
5. Compose `BoundaryPartitionTermFromResolvedTarget`,
   `BoundaryAtlasMembershipAuto`, and the selected-box COV route into the
   concrete endpoint, so selected boundary chart-change data is generated from
   unified source-shrink/M8 data rather than passed as an endpoint field.
6. After the concrete compact-support endpoint is assembled, identify the next
   nonlocal mathematical gap toward the full smooth manifold theorem:
   finite-chart/partition construction, boundary collar/half-space coverage,
   or orientation API, depending on which field remains genuinely unfilled.
7. Main thread integrates only focused-check-clean modules, reruns
   `lake build`, and scans for forbidden placeholders after each wave.
8. Decide the repository license strategy around the GPL-3.0-only dependency.

## Source Links

- mathlib: <https://github.com/leanprover-community/mathlib4>
- mathlib documentation: <https://leanprover-community.github.io/mathlib4_docs/>
- LeanStokes prior art: <https://github.com/d0d1/lean-stokes-theorem>
- arXiv paper: <https://arxiv.org/abs/2605.01028>
