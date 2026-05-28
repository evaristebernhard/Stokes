# Stokes M8 Agent Wave Report

Date: 2026-05-24.

Scope: documentation-only coordination report for the current 20-agent M8 wave.
This report records task ownership, true blockers, parallel work queues, and
which declarations are field projections rather than new analytic proofs.  No
Lean source file is intentionally changed by this agent.

## Wave Snapshot

The previous active agent set was shut down by the supervisor after the
interrupted fourth wave.  The current wave is a 20-agent restart aimed at
turning the M8 global Stokes interface from large manual fields into smaller
theorem-produced packages.

The important architectural constraint remains:

- Do not import `Stokes.Global.*` into `Stokes.HalfSpace`.
- Boundary-chart utilities that depend on global assembly must stay out of the
  `Stokes.HalfSpace` aggregator, otherwise the existing import path
  `Stokes.Global.InteriorChart -> Stokes.HalfSpace` creates cycles.

## 20-Agent Division Of Labor

| Agent | Area | Expected output | Current integration meaning |
|---|---|---|---|
| 1 | Bulk integrand a.e. replacement | `Stokes/Global/BulkIntegrandAE.lean` | Reduce bulk scalar integrand replacement to an explicit a.e. package. |
| 2 | Indicator support localization | `Stokes/Global/IndicatorSupportLocalization.lean` | Prove support/indicator rewrites used by finite measure localization. |
| 3 | Bulk localization constructor | `Stokes/Global/BulkIntegralLocalizationConstructor.lean` | Derive `bulkIntegralLocalizes` from smaller measure/integrand/integrability fields. |
| 4 | Boundary measure localization | `Stokes/Global/BoundaryMeasureLocalization.lean` | Turn boundary measure integral reconstruction into a reusable finite-sum theorem. |
| 5 | Boundary COV measure constructor | `Stokes/Global/BoundaryCOVMeasureConstructor.lean` | Connect source boundary COV terms to partition terms by finite sums. |
| 6 | Boundary compact-support integrability | `Stokes/Global/BoundaryIntegrabilityCompactSupport.lean` | Package boundary-piece integrability from compact-support-style inputs. |
| 7 | Global integral definitions | `Stokes/Global/GlobalIntegralDefinitions.lean` | Name represented bulk and boundary integrals without committing to the final canonical API. |
| 8 | Natural measure constructor | `Stokes/Global/NaturalMeasureConstructor.lean` | Wrap natural global input plus bulk/boundary measure-localization fields. |
| 9 | M8 statement | `Stokes/Global/M8Statement.lean` | Present the current M8 theorem as a clean conditional statement. |
| 10 | Artificial-face field reduction | `Stokes/Global/ArtificialFaceFieldReduction.lean` | Collapse support-zero, overlap-pairing, and selected-face routes to one cancellation package. |
| 11 | Boundary target image reduction | `Stokes/BoundaryChart/TargetImageFieldReduction.lean` | Keep target-image data in pure boundary-chart land and avoid HalfSpace cycles. |
| 12 | Boundary target image to assembly | `Stokes/Global/BoundaryTargetImageToAssembly.lean` | Adapt target-image packages to global boundary assembly fields. |
| 13 | Measure box API | `Stokes/Global/MeasureBoxAPI.lean` | Identify project-local box terms with measure-localized piece terms. |
| 14 | Bulk measure localization fields | `Stokes/Global/BulkMeasureLocalizationFields.lean` | Isolate the minimal bulk measure fields still needed upstream. |
| 15 | Measure localization audit | `Stokes/Global/MeasureLocalizationAudit.lean` or report notes | Audit what fields remain after measure constructors. |
| 16 | Build/import explorer | build-status notes | Keep the import graph acyclic and identify focused build failures. |
| 17 | Remaining FIELD audit | audit report | Classify true blockers versus constructor/projection wrappers. |
| 18 | Import graph audit | import report | Recommend imports to add only after focused builds pass. |
| 19 | Agent-wave report | `reports/stokes-m8-agent-wave.md` | This documentation-only coordination report. |
| 20 | Blueprint update | `blueprint/src/stokes-m8-measure.tex` | Add measure-localization blueprint nodes and rebuild the PDF. |

## True Blockers

These are still mathematical or API-construction blockers.  They are not solved
by record projections alone.

| Blocker | Current best entry point | What is still required |
|---|---|---|
| Bulk measure localization | `BulkIntegralLocalizationConstructor` and `MeasureIntegralLocalization` | Construct the genuine bulk measure integral, prove the a.e. indicator decomposition of the global integrand, prove active-piece integrability, and identify each measure-local term with the selected box term. |
| Boundary measure reconstruction | `BoundaryMeasureLocalization` and `BoundaryCOVMeasureConstructor` | Define the genuine boundary measure/integrand, prove its a.e. finite indicator decomposition, prove boundary-piece integrability, and identify each piece integral with the boundary partition term. |
| Canonical global integrals | `GlobalIntegralDefinitions` and `NaturalMeasureConstructor` | Replace represented `Real` fields by the final manifold integral of `d omega` and induced-boundary integral of `omega`. |
| Target boundary boxes | `BoundaryChart.TargetImageFieldReduction`, `BoundaryTargetImageToAssembly` | Construct target boxes from actual boundary chart transitions using local openness/inverse function data, then prove source/target image and local inverse facts for selected compact boundary boxes. |
| Artificial-face cancellation | `ArtificialFaceFieldReduction`, `ArtificialFaceAdjacency`, `ArtificialFaceOverlapPairing` | Produce the real geometric face decomposition/pairing for selected interior boxes, or prove the support-zero alternative for all artificial faces. |
| Boundary orientation | `BoundaryChart.OrientedAtlas*`, `BoundaryOrientationToGlobal` | Connect the local positive-Jacobian boundary chart predicates to the global oriented manifold with boundary and the outward-normal-first convention. |
| Partition and localized pieces | `SelectedInteriorAssembly`, `SelectedBoundaryAssembly`, `PartitionCompactSupport` | Build selected finite chart boxes and localized partition pieces directly from compact support, rather than taking them as input packages. |

## Projection Wrappers Versus Analytic Proofs

The following declarations are useful, but should not be reported as final
analytic Stokes progress unless their input fields are theorem-produced.

| Declaration family | Why it is mainly projection/bookkeeping |
|---|---|
| `NaturalMeasureStokesInput.stokes`, `naturalMeasureStokes`, `M8GlobalStokesInput.stokes`, `m8GlobalStokes` | They prove equality from already supplied natural/global data plus bulk and boundary localization fields.  They do not yet construct those fields from a manifold form. |
| `BulkMeasureLocalizationFields.*` and `BulkMeasureLocalizationTermFields.bulkIntegralLocalizes` | They turn smaller fields into the existing `bulkIntegralLocalizes` field.  The genuine measure split, integrand a.e. equality, integrability, and box-term identification remain inputs. |
| `BoundaryMeasureLocalizationFields.*` and `toBoundaryIntegralPartitionReconstructionData` | They package boundary measure reconstruction once the boundary measure integral and finite-sum equality are already supplied or proved elsewhere. |
| `BoundaryCOVMeasureConstructor.FieldizedBoundaryCOVMeasureData.*` | It transports a fieldized COV source sum to partition reconstruction; it still assumes the boundary measure equals the source sum. |
| `ArtificialFaceResolvedData.to_interiorBoundaryCancellation` | It is the unified exit to the global cancellation field.  The real geometry is in constructing support-zero, overlap-pairing, or adjacent-face input data. |
| `BoundaryChartTargetImageResolvedFamily.*` | It removes duplicated target-image fields, but still requires a genuine `targetBox` and local inverse/image data. |
| `GlobalIntegralInterface`-style represented integral records | They make statement plumbing cleaner, but are not yet the canonical definition of integration of forms on manifolds. |

By contrast, the pure finite-measure lemmas in
`MeasureIntegralLocalization`, the indicator support lemmas in
`IndicatorSupportLocalization`, and the finite COV sum transport lemmas in
`BoundaryCOVMeasureConstructor` are real theorem work, provided their
hypotheses are met.

## Parallel Task Queue

The next wave can be parallelized safely if each worker keeps to one side of the
import boundary.

| Priority | Task | Suggested owner type | Success criterion |
|---|---|---|---|
| P0 | Focused build cleanup for every fourth-wave module | build worker | `lake build Stokes.Global.<Module>` or `lake build Stokes.BoundaryChart.<Module>` passes for each touched file. |
| P0 | M8 statement alignment | theorem-shape worker | `Stokes/Global/M8Statement.lean` imports the stable structures and has no unresolved names. |
| P0 | Boundary measure constructor from existing localization data | measure worker | A constructor fills `boundaryMeasureIntegral_eq_partitionSum` from `BoundaryMeasureLocalizationData`, keeping only `globalBoundaryIntegral = boundaryMeasureIntegral` fieldized. |
| P0 | Bulk constructor from pure measure finite-sum theorem | measure worker | A constructor fills the bulk finite-sum equality from an a.e. indicator decomposition and integrability hypotheses. |
| P1 | Target-image family to assembly convergence | boundary/global adapter worker | One adapter path from pure `BoundaryChart.TargetImageFieldReduction` to global boundary assembly, without importing Global into HalfSpace. |
| P1 | Artificial-face support-zero route | geometry worker | For selected compact-support interior boxes, prove artificial boundary terms vanish outside true boundary or reduce to zero. |
| P1 | Artificial-face overlap-pairing route | geometry worker | Build pairing data with opposite signs and same unsigned geometric face for adjacent selected boxes. |
| P1 | Boundary chart target box construction | boundary-chart worker | Derive selected target boundary box and local inverse data from inverse function theorem/local openness inputs. |
| P2 | Canonical integral interface audit | API worker | Propose a final API replacing represented `Real` fields with manifold-form integrals while preserving existing theorem statements. |
| P2 | Blueprint sync | documentation worker | Add blueprint nodes only when they correspond to stable Lean declarations or explicit blockers. |

## Recommended Immediate Merge Rule

Only integrate a module into an aggregator after all three checks are true:

1. Its focused `lake build` passes.
2. It does not introduce a `Global -> HalfSpace -> Global` import cycle.
3. It reduces a field surface or proves a reusable theorem; it is not a
   duplicate wrapper with a different name.

For now, new imports should be added to `Stokes/Global.lean` only after focused
builds pass.  Do not add global-dependent boundary convenience files to
`Stokes/HalfSpace.lean`.

## Verification

This agent changed only this report file.  The requested Lean placeholder scan
was run after the edit:

```text
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

Result: no matches.
