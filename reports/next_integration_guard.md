# Next integration guard

Date: 2026-05-25

Scope: this report tracks the next public-import pass for the current parallel
Stokes route/facade wave.  The companion Lean module
`Stokes/Global/NextIntegrationGuard.lean` imports the candidate modules together
and `#check`s their theorem-facing declarations.  It is a guard only; it should
not itself be imported by public facades.

## Guarded modules

The guard currently checks these candidate modules together:

- `Stokes.Global.ActiveStrictInnerOuterFromCompactSupportAuto`
- `Stokes.Global.LocalizedChartAlignmentFromNaturalSelectionAuto`
- `Stokes.Global.NaturalBulkFromExtDerivRouteAuto`
- `Stokes.Global.BoundaryUnifiedCanonicalTargetRouteAuto`
- `Stokes.Global.BoundaryUnifiedToEndpointBaseAuto`
- `Stokes.Global.BulkBoundaryActiveAlignmentAuto`
- `Stokes.Global.NaturalCompactSupportOnePackageStokesAuto`
- `Stokes.BoundaryChart.ControlledTargetFromSourceShrinkCoverAuto`

## Suggested public imports

Recommended for `Stokes.Global.lean` after focused checks:

- `Stokes.Global.ActiveStrictInnerOuterFromCompactSupportAuto`
  - theorem-facing compact-support to strict inner/outer source constructors.
- `Stokes.Global.LocalizedChartAlignmentFromNaturalSelectionAuto`
  - removes a common endpoint chart-alignment manual input.
- `Stokes.Global.NaturalBulkFromExtDerivRouteAuto`
  - stable route from synchronized bulk ext-deriv/reconstruction facts to the
    natural endpoint boundary-measure input.
- `Stokes.Global.BoundaryUnifiedCanonicalTargetRouteAuto`
  - stable unified-boundary to canonical target natural route.
- `Stokes.Global.BoundaryUnifiedToEndpointBaseAuto`
  - endpoint-facing wrapper from unified boundary data to compact-support
    separated-boundary base input.
- `Stokes.Global.BulkBoundaryActiveAlignmentAuto`
  - removes repeated active-chart equality plumbing for bulk canonical local
    facts.
- `Stokes.Global.NaturalCompactSupportOnePackageStokesAuto`
  - highest-level theorem-facing compact-support package from this wave.

Recommended for `Stokes/BoundaryChart/BoundaryChartGeometryFacade.lean` after
focused checks:

- `Stokes.BoundaryChart.ControlledTargetFromSourceShrinkCoverAuto`
  - pure boundary-chart geometry constructor layer; it should stay in the
    BoundaryChart facade rather than in `Stokes.Global.lean`.

## Keep private

Do not public-import the guard itself:

- `Stokes.Global.NextIntegrationGuard`
  - compatibility sentinel only; importing it publicly would expose broad
    integration checks as API surface.

Existing audit/report modules should also remain private:

- `Stokes.Global.CurrentGapReductionAudit`
- `Stokes.Global.HighLeverageGapAudit`
- `Stokes.Global.IntegrationDependencyAudit`

They are useful for planning but intentionally broad and more likely to create
name or dependency churn than theorem-facing route modules.

## Checks covered

The Lean guard references:

- compact-support to active strict-box constructors;
- localized chart-alignment transport from selected natural chart boxes;
- natural endpoint boundary-measure routes from bulk ext-deriv facts;
- unified boundary source routes into canonical target and endpoint inputs;
- active-chart alignment wrappers for bulk canonical local facts;
- one-package compact-support Stokes statements;
- BoundaryChart controlled-target constructors from source-shrink/local-open/IFT
  data.

This should catch the most likely next integration failures: import order
breakage, stale declarations, and accidental reuse of public theorem names.
