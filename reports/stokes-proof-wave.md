# Stokes Proof Wave Report

Date: 2026-05-24.

Scope: documentation-only report for the current 16-agent Stokes proof wave.
This agent is Agent 16/16.  It edits no Lean files and does not run
`lake build`.  The purpose is to record the parallel task split, how each node
reduces the visible M8/natural compact-support field surface, which parts are
still genuine mathematics, and how the parent process should integrate the
wave safely.

## Wave Aim

The repository now has a conditional global Stokes layer:

```text
M8 measure localization
  + localized interior pieces
  + target-image boundary data
  + artificial-face cancellation
  + represented integral interface
  -> global Stokes equality
```

Recent constructor layers have moved the theorem surface closer to a natural
compact-support statement.  This proof wave is meant to push from:

```text
hand-filled M8GlobalStokesInput fields
```

toward:

```text
compactly supported smooth form
  + finite selected chart boxes
  + local partition and chart-transition facts
  -> NaturalCompactSupportStokesInput
  -> canonical natural compact-support Stokes statement
```

The crucial standard is: a wrapper is useful only if it makes the next genuine
proof obligation smaller and better named.

## 16-Agent Division Of Labor

| Agent | Area | Main Lean target or output | Field reduction meaning |
|---|---|---|---|
| 1 | Compact finite-active selection to builder | `CompactSupportFiniteActiveToBuilder` | Replaces manual selected-partition/support-set wiring by a finite-active compact-support builder input. |
| 2 | Bulk a.e. integrand from partition | `BulkIntegrandAEFromPartition` | Moves bulk integrand a.e. equality toward partition-local eventual equality plus measure-support hypotheses. |
| 3 | Bulk measure from selected partition | `BulkMeasureFromPartition` / compact-support bulk data | Reduces `bulkMeasureIntegral_eq_localBulkSum` to integrability, indicator reconstruction, and measure-box term identification. |
| 4 | Boundary measure from partition | `BoundaryMeasureFromPartition` | Reduces `boundaryMeasureIntegral_eq_partitionSum` to boundary piece integrability and an a.e. indicator sum. |
| 5 | Natural boundary measure builder | `NaturalBoundaryMeasureBuilder` | Packages boundary compact/set-integral fields into `M8BoundaryMeasureData`, avoiding direct hand-fill of M8 boundary fields. |
| 6 | Measure-box term alignment | `MeasureBoxAPI`-facing adapters | Identifies measure-local bulk/boundary terms with project-local box terms used by local Stokes. |
| 7 | Localized interior from selected boxes | `CompactSupportPartitionToLocalized` and related localized constructors | Makes `localizedInterior`, `localized_active`, and `localized_coefficient` come from selected partition data. |
| 8 | Target-image construction | `TargetImageFromLocalInverse`, `TargetImageLocalOpenness`, target-image adapters | Replaces raw target-image fields by local inverse/image data for boundary chart transitions. |
| 9 | Orientation bridge to M8 | `OrientationMathlibBridge`, `OrientationBridgeToM8` | Packages future mathlib/oriented-atlas data as the two M8 source-chart membership fields. |
| 10 | Artificial-face support-zero route | `ArtificialFaceSupportZeroToM8`, `InteriorBoundarySupportZero` | Turns support containment in interior boxes into zero artificial-boundary contribution. |
| 11 | Artificial-face pairing route | `ArtificialFacePairingToM8`, adjacency/overlap files | Turns adjacent selected-face pairing into M8 artificial-face cancellation fields. |
| 12 | Natural compact-support builder | `NaturalCompactSupportBuilder` | Combines resolved measure, target-image, and artificial-face packages into the natural compact-support input. |
| 13 | Canonical theorem surface | `CanonicalIntegralInterface`, `CanonicalNaturalStokes` | States the compact-support theorem with future-facing names `manifoldExtDerivIntegral` and `boundaryFormIntegral`. |
| 14 | Import and build coordinator | import-graph notes and focused checks | Keeps new Global adapters out of `Stokes.HalfSpace` and defers aggregator imports until focused files pass. |
| 15 | Blueprint/proof ledger sync | blueprint or proof-obligation notes | Keeps the visual proof graph aligned with actual Lean declarations and true blockers. |
| 16 | Reports | `reports/stokes-proof-wave.md` | This file; records the wave without changing Lean or running `lake build`. |

## Fields Reduced By This Wave

The following field surfaces are now expected to be supplied through named
packages rather than by filling the final M8 records directly.

| Old visible surface | New preferred source | What still has mathematical content |
|---|---|---|
| `selectedPartition.K = formData.supportSet` | finite-active compact-support builder data | Constructing finite chart boxes that really cover the compact support. |
| `localizedInterior`, `localized_active`, `localized_coefficient` | selected-partition localized constructors | Proving each localized piece has the required local Stokes data. |
| bulk a.e. equality for `d omega` | `BulkIntegrandAEFromPartition` from partition-local eventual equality | Showing exterior derivative commutes with the localized partition expression on the chart support. |
| `bulkMeasureIntegral_eq_localBulkSum` | compact-support bulk measure package plus M8 bulk adapters | Proving integrability, a.e. indicator decomposition, and equality with project-local box integrals. |
| `boundaryMeasureIntegral_eq_partitionSum` | boundary compact measure package plus natural boundary builder | Proving boundary measure/integrand definitions decompose over selected boundary pieces. |
| target image activity/source membership fields | target-image resolved input and orientation bridge | Constructing local inverse/target box data from actual boundary chart transitions. |
| `targetBoundaryTerm_eq_partition` | target-image to assembly plus boundary COV measure constructors | Proving chart-change COV terms are exactly the boundary partition terms used by measure localization. |
| artificial-face M8 fields | support-zero or adjacent-face pairing packages | Proving interior artificial faces vanish or cancel with correct signs. |
| represented bulk/boundary integral equality | natural/canonical compact-support theorem wrappers | Replacing represented `Real` fields by final manifold-form integral definitions. |

This is real progress only when the new package is produced from lower-level
geometry or measure theory.  If the new package merely contains the old field
with a shorter name, it is still useful bookkeeping, but not a discharged proof
node.

## True Mathematical Blockers

These are the remaining obstacles between the current compact-support-facing
API and a general smooth manifold Stokes theorem.

### Compact Support To Chart Boxes

Mathematically, compact support should allow a finite choice of interior and
boundary coordinate boxes.  Lean still needs coherent data saying:

```text
support(omega) is contained in the finite selected chart boxes
```

and that the same active set drives the localized partition, bulk measure
terms, boundary pieces, target images, and artificial-face geometry.  This is
the bridge from compactness to a finite combinatorial Stokes sum.

### Partition And Exterior Derivative

The bulk side needs the local identity behind Stokes:

```text
d(Σ_i ρ_i · omega) = d omega
```

on the region where the selected partition controls the form.  The current
constructors can consume partition-local eventual equality and a.e. support
facts, but the genuine proof still has to connect `extDeriv`, chartwise
pullbacks, partition coefficients, and support containment.

### Bulk Measure Localization

The theorem needs:

```text
∫_M d omega = Σ selected local bulk integrals
```

In Lean this means measurable integrands, `IntegrableOn` facts, a.e. indicator
splitting, finite-sum integral reconstruction, and equality between
measure-local terms and project-local chart-box terms.  The record surface is
smaller now, but this remains one of the main analytic proof nodes.

### Boundary Measure Localization

The boundary side needs:

```text
∫_∂M omega = Σ selected boundary chart-piece integrals
```

The hard content is the boundary measure and boundary integrand definition,
their finite indicator decomposition, compact-support integrability of each
piece, and compatibility with target-image/chart-change data.

### Target Images And Local Inverses

Boundary chart transitions must carry source boundary boxes to usable target
boxes with local inverse/image control.  The project has pure BoundaryChart
records for this, but the real proof has to come from inverse-function or
local-openness facts for boundary chart transitions.

### Artificial Face Cancellation

Local box Stokes creates extra faces inside the manifold.  They must either:

```text
vanish because support stays away from the artificial face
```

or

```text
cancel in opposite-oriented adjacent pairs
```

The first route depends on strong support/box choices; the second route depends
on face matching, sign comparison, and equality of the underlying unsigned face
integrals.

### Boundary Orientation

The local half-space theorem uses an outward-normal-first sign convention.
The final theorem must show that this is the same as the induced boundary
orientation coming from the oriented smooth manifold.  Current bridge files
keep the project-local orientation data explicit; the mathlib-facing
orientation theorem is still a sensitive proof node.

### Canonical Manifold Integral API

The theorem surface now has canonical names, but the underlying values are
still represented measure-localization fields.  The final step is to define or
identify:

```text
manifoldExtDerivIntegral = ∫_M dω
boundaryFormIntegral     = ∫_∂M ω
```

using the eventual project/mathlib integration API for differential forms on
oriented manifolds with boundary.

## Mathematical Meaning Of The Current Stage

The proof is now shaped like a standard globalization argument:

1. choose a finite chart-box cover of the compact support;
2. multiply the form by a partition of unity;
3. apply the already-local half-space/box Stokes theorem in each selected box;
4. sum the local equalities;
5. cancel artificial interior faces;
6. identify the remaining boundary terms with the induced boundary integral;
7. rewrite the represented sums as the canonical manifold integrals.

The Lean work is hard because every arrow above has to preserve the exact
indexing, support, smoothness, orientation, and measure-theoretic hypotheses.
The current wave is successful when the final theorem asks for these proof
nodes by their mathematical names, not as dozens of unrelated record fields.

## Recommended Next Proof Attacks

The next wave should favor true blockers over additional wrapper layers.

| Priority | Attack | Why it is high leverage |
|---|---|---|
| P0 | Prove one complete bulk localization path from selected partition data to `M8BulkMeasureFields`. | It directly shortens the left-hand side `∫_M dω` pipeline. |
| P0 | Prove one complete boundary localization path from selected boundary pieces to `M8BoundaryMeasureData`. | It directly shortens the right-hand side `∫_∂M ω` pipeline. |
| P0 | Decide support-zero versus pairing as the primary artificial-face route. | The two routes need different chart-box selection hypotheses; choosing one avoids duplicating geometry. |
| P1 | Construct target-image resolved families from local openness for boundary chart transitions. | This turns target boxes from input data into theorem-produced data. |
| P1 | Connect `OrientationBridgeToM8` to a concrete mathlib-oriented atlas input. | This is needed before the statement deserves to be called a manifold orientation theorem. |
| P2 | Keep canonical integral definitions thin until localization is stable. | Premature final integral API work can force rewrites across every localization theorem. |

## Build And Concurrency Strategy

Parallel agents are useful here, but only if they avoid shared build output
contention.

1. Each proof agent should own one narrow module or one new adapter file.
2. Agents should run only focused checks such as:

```text
lake env lean Stokes\Global\File.lean
lake env lean Stokes\BoundaryChart\File.lean
```

3. Agents should not run full `lake build`; the parent integration step runs it
   once after all workers finish.
4. Documentation agents should not run Lean builds at all.
5. Aggregator imports should be added last.
6. Do not import `Stokes.Global.*` into `Stokes.HalfSpace`.
7. Pure `Stokes.BoundaryChart.*` files should stay free of `Stokes.Global.*`.

The practical reason is simple: the Windows workspace can suffer `.olean` and
Lake cache contention when many workers build broad targets at once.  Focused
checks keep errors attributable and avoid file-lock churn.

## Reporting Standard

Use these labels in future progress notes:

- **True proof node**: a theorem constructs a previously assumed analytic,
  geometric, orientation, or measure-theoretic field from natural lower-level
  hypotheses.
- **Constructor/projection**: a record wrapper or theorem repackages existing
  hypotheses into a cleaner shape.
- **Statement surface**: a theorem restates an existing result under more
  natural names, such as canonical integral names.
- **Audit/report**: documentation, import graph, or blueprint work only.

For estimating distance to final Stokes, count true proof nodes much more than
constructor/projection nodes.

## Verification Policy For This Agent

This report agent edits only:

```text
reports/stokes-proof-wave.md
```

Allowed verification:

```text
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

Result for this run: no matches.

Forbidden for this agent:

```text
lake build
```
