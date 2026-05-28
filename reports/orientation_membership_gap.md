# Orientation Membership Gap

Worker D added `Stokes/BoundaryChart/OrientationMembershipAuto.lean`.

## What is now automated

The new Lean module introduces:

- `BoundaryChartOrientationMembership charts x0 x1`
- constructors for raw atlas membership and all-chart/universal membership
- membership projections for:
  - `BoundaryChartMathlibOrientationAtlasData`
  - `BoundaryChartMathlibOrientationManifoldData`
  - `BoundaryChartMathlibOrientedAtlasBridge`
  - `BoundaryChartMathlibOrientedManifoldBridge`
- COV wrappers that consume the bundled membership pair for:
  - `BoundaryChartSelectedBoxTargetImageAutoData`
  - `BoundaryChartSelectedImageBoxContainment`
  - `BoundaryChartSourceShrinkInverseTargetBoxData`
  - `BoundaryChartSourceShrinkOpenPartialHomeomorphData`

This removes repeated theorem-facing `hx0 hx1` plumbing once a local or global
constructor has produced the two membership facts.

## Precise remaining gap

The atlas cover field

```lean
∀ p : M, ∃ x ∈ charts, p ∈ (extChartAt I x).source
```

does not imply that an arbitrary point-centered chart `x0` belongs to
`charts`.  It only gives some atlas chart center whose extended chart contains
the point.  Therefore the following statement is not derivable from the current
atlas record alone:

```lean
x0 ∈ O.charts ∧ x1 ∈ O.charts
```

for arbitrary selected boundary chart centers `x0 x1`.

The missing construction fact should come from the source that chooses the
boundary charts.  A clean future statement is:

```lean
def selectedBoundaryChartOrientationMembership
    (O : BoundaryChartMathlibOrientationAtlasData I M 𝓞)
    (S : SelectedBoundaryChartData I x0 x1 ...)
    (hselectedFromAtlas :
      S.sourceChart ∈ O.charts ∧ S.boundarySourceChart ∈ O.charts) :
    BoundaryChartOrientationMembership O.charts S.sourceChart S.boundarySourceChart
```

In the current global route this information is already present as resolved
target-image membership (`source_mem` and `boundarySource_mem`).  The right
next integration step is to project those fields into
`BoundaryChartOrientationMembership` at the call site, not to try to recover
them from `covers`.
