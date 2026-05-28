# Remaining input scoreboard

Date: 2026-05-25

Scope: task K.  This report accompanies
`Stokes/Global/RemainingInputScoreboard.lean`.  The Lean module is intentionally
an audit layer: it does not add public imports and does not claim any new
analytic, orientation, inverse-function, or change-of-variables theorem.

## Current size baseline

Current Lean footprint under `Stokes/` is about 310 files and 93k lines:

- `Stokes/Global`: about 69k lines.
- `Stokes/BoundaryChart`: about 20k lines.
- Remaining directories and facades: about 4k lines.

This matters because the next progress should not be another large wrapper
wave.  The codebase already has enough projection and facade layers.  The next
useful code should remove theorem-facing assumptions from the exact packages
named in the scoreboard.

## Lean scoreboard declarations

The new module names four precise dependency layers.

- `RemainingChartBoxSelectionPackage`
  - Fields:
    `CompactlySupportedSmoothFormData I omega` and
    `CompactlySupportedSmoothFormData.NaturalFiniteActiveFromCompactSupportData`.
  - Meaning:
    compact support has been turned into active chart boxes, compact coordinate
    support, support containment, chart containment, and smoothness
    neighborhoods.

- `RemainingBulkBoundaryRoutePackage`
  - Fields:
    `NaturalBulkEndpointCommonData` and its
    `BulkCanonicalLocalFactsExtDerivConstructorRoute`.
  - Meaning:
    the bulk exterior-derivative route, boundary source data, boundary
    face-continuity, selected reconstruction source, and chartwise measure have
    been synchronized.

- `RemainingEndpointGeometryPackage`
  - Fields:
    `LocalizedInteriorM8ChartAlignment` and
    `StrictAlignmentChartBoxContainmentData`.
  - Meaning:
    localized interior chart labels and strict/contained endpoint boxes are
    available in the exact shape consumed by the one-package theorem.

- `RemainingOnePackageConstructionScoreboard`
  - Combines the three layers above and constructs
    `NaturalCompactSupportOnePackageChartBoxStokesInput`.
  - The theorem `represented_stokes` then proves the current
    `CanonicalIntegralInterface.stokesStatement`.

The final marker,
`RemainingGeneralSmoothManifoldExitScoreboard`, records the honest endpoint of
the current formalization: we have a represented statement through
`CanonicalIntegralInterface`, not yet a mathlib-native manifold integral
statement.

## Remaining work by code volume

These estimates are for real proof-producing code, excluding another layer of
thin facades.

1. Endpoint chart-box coherence: 800-1800 Lean lines.
   - Target packages:
     `RemainingChartBoxSelectionPackage` and
     `RemainingEndpointGeometryPackage`.
   - Main declarations likely belong in `StrictInnerOuterBox`,
     `CompactSupportStrictBufferFromActive`, and
     `EndpointLocalizedOuterBoxFromCompactSelectionAuto`.
   - Mathematical difficulty: medium.  The math is compact-box selection with
     strict inner/outer room; the Lean difficulty is keeping chosen boxes
     definitionally aligned.
   - Parallel suitability: high, if files are split by box constructor,
     localized outer alignment, and endpoint conversion.

2. Bulk ext-derivative and measure route: 1200-2500 Lean lines.
   - Target package:
     `RemainingBulkBoundaryRoutePackage`.
   - Main declarations likely extend `BulkCanonicalLocalFactsFromExtDerivAuto`,
     `BulkExtDerivProjectLocalAuto`, and measure reconstruction files.
   - Mathematical difficulty: medium-high.  Needs chartwise exterior derivative
     equality, a.e. comparison, and finite partition reconstruction in the
     exact selected-partition shape.
   - Parallel suitability: medium.  Some local lemmas are parallelizable, but
     the final route has a narrow dependency chain.

3. Boundary target boxes and local inverse data: 1500-3500 Lean lines.
   - Target packages:
     `NaturalBulkEndpointCommonData.boundaryUnified`,
     `BoundarySourceAlignmentUnifiedData`, and the canonical target route used
     by `RemainingBulkBoundaryRoutePackage`.
   - Main declarations should live in existing `BoundaryChart` geometry files,
     especially target-box/source-shrink/local-inverse modules.
   - Mathematical difficulty: high.  The key is not proving an arbitrary
     "future box contains selected box" callback; it is choosing future boxes
     constrained to contain the selected compact image while staying in the
     inverse-function neighborhood.
   - Parallel suitability: high for API search and local topology lemmas;
     low for the final constructor, which should be main-thread integrated.

4. Orientation bridge to real oriented manifold data: 1000-2500 Lean lines.
   - Target fields:
     `BoundaryChartOrientedAtlas`, orientation compatibility inside boundary
     COV, and the outward-first boundary convention.
   - Mathematical difficulty: high because it must match mathlib's orientation
     API and the project's half-space sign convention.
   - Parallel suitability: medium-high.  One worker can audit mathlib API,
     another can connect existing boundary-chart orientation records, and the
     main thread should integrate the chosen theorem shape.

5. Canonical integral interface replacement: 2000-5000 Lean lines.
   - Target:
     replace the represented `CanonicalIntegralInterface` values with actual
     compactly supported top-degree form integrals and boundary integrals.
   - Mathematical difficulty: very high.  This includes partition
     independence, chart-change invariance, and equality with the current
     measure-localized values.
   - Parallel suitability: medium.  Definition work, chart-change lemmas, and
     reconstruction lemmas can split, but the final theorem shape should stay
     centralized.

6. Compact support to compact manifold/general statement: 700-1800 Lean lines
   after the canonical integral interface exists.
   - Target:
     turn compact manifold support into the compact-support input, or state the
     compact-support theorem as the first public final theorem.
   - Mathematical difficulty: medium after previous tracks; mostly support and
     theorem-shape work.
   - Parallel suitability: medium.

Conservative total estimate from the current represented one-package route to
a credible compact-support smooth-manifold theorem is about 7k-17k additional
Lean lines.  A polished compact oriented manifold-with-boundary theorem may add
another 2k-6k lines, mostly in final theorem shaping and API cleanup.

## Best next parallel wave

Good parallel tasks:

- Box constructor worker:
  build strict inner/outer boxes as the single source of truth for compact
  active boxes and localized outer boxes.

- Endpoint geometry worker:
  use that box constructor to produce `LocalizedInteriorM8ChartAlignment` and
  `StrictAlignmentChartBoxContainmentData` without manual margin fields.

- Boundary target-box worker:
  prove the constrained target-box selection lemma: selected compact image box
  contained in the later target box, later target box contained in the local
  inverse neighborhood.

- Orientation API worker:
  connect `BoundaryChartOrientedAtlas` to mathlib-oriented atlas/manifold data,
  and identify the exact missing theorem if mathlib lacks a bridge.

- Bulk ext-derivative worker:
  construct the `BulkCanonicalLocalFactsExtDerivConstructorRoute` from the
  current selected-partition exterior derivative route.

- Measure reconstruction worker:
  reduce remaining `BoundaryChartChangeSelectedFamilyData` and
  `ProjectLocalBoundaryCanonicalFaceContinuityData` fields from existing COV
  and continuity packages.

Main-thread critical path:

- Decide the next public theorem-facing input:
  either `RemainingOnePackageConstructionScoreboard` or the existing
  `NaturalCompactSupportOnePackageChartBoxStokesInput`.
- Integrate only modules that remove fields from the scoreboard.
- Keep audit-only files private until a constructor actually discharges one
  of the named packages.

## Practical metric

The scoreboard gives a concrete progress metric:

- A proof wave succeeds only if it constructs one of the fields in
  `RemainingChartBoxSelectionPackage`,
  `RemainingBulkBoundaryRoutePackage`, or
  `RemainingEndpointGeometryPackage` from more natural manifold/chart data.
- A wrapper that merely repackages an already-assumed field should not count as
  mathematical progress unless it deletes a field from a public theorem input.

