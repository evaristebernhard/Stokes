# Integration dependency audit

Date: 2026-05-25

Scope: this report audits the current high-leverage Stokes integration wave and
the public import risks around `Stokes.Global.lean`, `Stokes.lean`, and
`Stokes/BoundaryChart/BoundaryChartGeometryFacade.lean`.

## Current public imports that are already safe

These imports are already present in public facades and should remain:

- `Stokes.BoundaryChart.CompactImageBoxContainmentAuto`
  - imported by `Stokes/BoundaryChart/BoundaryChartGeometryFacade.lean`
  - safe boundary-geometry layer; it does not pull global/M8 facades back into
    the boundary chart geometry facade.
- `Stokes.SingularCube.SmoothBridgeLocalityFacade`
  - imported by `Stokes.lean`
  - safe public singular bridge facade.
- `Stokes.Global.NaturalStrictAlignmentFromFiniteSelectionAuto`
  - imported by `Stokes/Global.lean`
  - safe global endpoint constructor layer.
- `Stokes.Global.SelectedStrictMarginsFromChartBoxAuto`
  - imported by `Stokes/Global.lean`
  - safe global strict-margin bridge.
- `Stokes.Global.NaturalCompactSupportEndpointNaturalInputAuto`
  - imported by `Stokes/Global.lean`
  - safe natural endpoint input layer.
- `Stokes.Global.BoundaryControlledTargetOrientationEndpointAuto`
  - imported by `Stokes/Global.lean`
  - safe controlled-target/orientation endpoint route.
- `Stokes.Global.BoundaryCanonicalTargetFromControlledCOVAuto`
  - imported by `Stokes/Global.lean`
  - safe controlled-target canonical boundary measure route.

The two controlled-target modules now import together successfully.  The
earlier overlap in target-image projection lemma names has been avoided by the
`...Canonical` suffixes in
`BoundaryCanonicalTargetFromControlledCOVAuto.lean`.

## Public imports promoted after repair

`Stokes.Global.CompactSupportEndpointSelectedMarginFacade` is theorem-facing
and focused-builds successfully.  It has now been promoted to
`Stokes.Global.lean`.

`Stokes.Global.EndpointSelectedStrictMarginsFromNaturalChartBoxesAuto` was
repaired before public promotion: it no longer imports
`Stokes.Global.HighLeverageGapAudit`, and its local chart-box containment
abbreviations were renamed away from the public facade names.

The public imports now include:

```lean
import Stokes.Global.CompactSupportEndpointSelectedMarginFacade
import Stokes.Global.EndpointSelectedStrictMarginsFromNaturalChartBoxesAuto
```

## Audit files that should stay private

Do not import these from public facades:

- `Stokes.Global.CurrentGapReductionAudit`
- `Stokes.Global.HighLeverageGapAudit`
- `Stokes.Global.IntegrationDependencyAudit`

They are useful for dependency and gap tracking, but they either duplicate
theorem-facing names or intentionally import a broad cross-section of modules.

## New low-risk Lean helper

Added in `Stokes/Global/IntegrationDependencyAudit.lean`:

```lean
M8BoundaryControlledTargetInput.BoundaryCanonicalProjectLocalFields
  .ofTargetImageAlignmentFields
```

It constructs
`M8BoundaryControlledTargetInput.BoundaryCanonicalProjectLocalFields` directly
from `BoundarySourceTargetImageAlignmentFields D.toM8TargetImageInput P` and
the controlled boundary-partition term equality.  This avoids manually calling
`toBoundarySourceProjectLocalAlignment` at later endpoint integration sites.

This is only record repackaging; it adds no analytic, measure-theoretic,
orientation, or inverse-function content.

## Verification

The helper module focused-checks after avoiding the audit/facade conflict:

```text
lake env lean Stokes\Global\IntegrationDependencyAudit.lean
```

The originally observed audit/facade conflict has been fixed in the
theorem-facing modules.  The audit file itself remains private.
