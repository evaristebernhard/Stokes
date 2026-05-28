# AGENTS.md

This repository is now a Lean 4 Stokes theorem formalization workspace.

## Project Goal

Formalize Stokes' theorem in Lean 4, with the long-term target including smooth
manifolds with boundary:

```text
local Euclidean Stokes -> differential-form integration -> manifold Stokes.
```

The project should build on mathlib rather than reimplementing analysis,
topology, manifolds, or exterior algebra from scratch.

## Repository Layout

- root directory: active Lean 4 Stokes project material.
- `ROADMAP.md`: current plan, external progress notes, and milestone tracking.
- `archive/nodal-surfaces/`: historical material from the previous nodal
  surfaces project.

Do not edit archived files unless the task explicitly asks for historical
cleanup, migration, or case-study extraction.

## Active Technical Scope

Prioritize a staged, mathlib-compatible development:

- Euclidean box Stokes as a wrapper around mathlib's divergence theorem.
- mathlib differential forms via `ContinuousAlternatingMap` and `extDeriv`.
- Pullback of forms via the Frechet derivative and mathlib's
  `extDeriv_pullback`.
- Smooth singular cubes and cubical chains as an intermediate target.
- Local Stokes on half-spaces and coordinate charts.
- Compactly supported top-degree form integration in Euclidean charts.
- Orientations, induced boundary orientations, and sign conventions.
- Integration of forms on oriented smooth manifolds via charts and partitions of
  unity.
- Final theorem for compact oriented smooth manifolds with boundary, or the
  compact-support variant if that is the cleaner first milestone.

Defer broad formalization projects unless needed for Stokes:

- Full de Rham cohomology.
- General singular homology beyond the cubical/singular-chain interface needed
  for Stokes.
- Currents, distributions, or weak forms.
- Numerical or computational geometry.
- Alternative foundations for integration when mathlib already provides a
  suitable theorem.

## External Reference Policy

Use external Lean developments as references, not as trusted proof or vendored
source by default.

- Prefer mathlib APIs and upstream-compatible theorem shapes.
- The `d0d1/lean-stokes-theorem` project is useful prior art for cubical and
  smooth-singular-cube Stokes. It is GPL-3.0-only, so do not copy code into this
  repository unless the user explicitly chooses a compatible licensing strategy.
- Temporary clones for research should live outside the repository unless the
  task explicitly asks to vendor or preserve them.
- When importing ideas from prior work, record the source and keep proofs
  clean-room unless licensing has been settled.

## Engineering Principles

- Keep theorem statements small, explicit, and aligned with mathlib conventions.
- Prefer abstractions that reduce coordinate bookkeeping without hiding the
  analytic hypotheses.
- Prove local Euclidean statements before global manifold statements.
- Track sign conventions carefully, especially for boundary orientation.
- Avoid `sorry`, `admit`, new axioms, or opaque shortcuts in committed proofs.
- If a temporary theorem is needed, mark it clearly and keep it out of final
  milestone claims.

## Multi-Agent Discipline

Parallel agents are the default execution mode for clearly separated Stokes
subtasks once the main thread has identified independent blockers.  If a task
can be split into disjoint proof/search modules without blocking the critical
path, prefer a parallel wave over single-threaded exploration.  The main thread
remains the single integration point.

- Subagents must not spawn, delegate to, or otherwise launch further subagents.
- Each subagent task must have an explicit, bounded ownership scope, preferably
  a disjoint Lean file or module family.
- Subagents should report blockers and proposed follow-up work back to the main
  thread instead of opening a new parallel wave on their own.
- The main thread is responsible for deciding which generated modules become
  public imports and for running the final `lake build` and no-placeholder scan.
- For long Stokes pushes, prefer batches of several independent agents over
  single-threaded local exploration, provided their write scopes are disjoint.
- Do not under-delegate Stokes bottlenecks: when there are multiple independent
  proof obligations, API audits, or wrapper-constructor tasks, split them into a
  controlled wave early.
- Do not wait idly for agents.  While they run, the main thread should continue
  on a non-overlapping critical-path task or prepare integration/verification.
- End each parallel wave by closing all agents, focused-checking their files,
  integrating only stable modules, and rerunning the repository verification
  gates.

## Verification Expectations

For Lean code changes, run the relevant focused checks first. Once a Lean
workspace exists at the root, prefer:

```text
lake exe cache get
lake build
```

For targeted files, use:

```text
lake env lean path/to/File.lean
```

Before reporting a formalization milestone, also check for forbidden proof
placeholders:

```text
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

When feasible, audit important declarations with `#print axioms` and state any
skipped checks clearly.

If only archive material is touched, run checks from `archive/nodal-surfaces/`
when feasible and state any skipped checks clearly.
