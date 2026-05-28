# Stokes Blueprint

This directory contains the source for a `leanblueprint`-style blueprint of the
Lean 4 Stokes formalization.

The source files live in `src/`:

- `src/web.tex`: web/plasTeX entry point.
- `src/print.tex`: printable PDF entry point.
- `src/content.tex`: theorem dependency graph content.
- `src/macros/`: shared and target-specific macros.
- `src/figures/`: Graphviz sources for the printable dependency graphs.

Local build commands, once `leanblueprint` is installed:

```text
leanblueprint web
leanblueprint pdf
leanblueprint checkdecls
leanblueprint serve
```

On Windows, `leanblueprint` currently needs Graphviz and a working pygraphviz
build environment. If local installation is painful, build the blueprint on a
Linux machine or in CI after installing `graphviz` and `libgraphviz-dev`.

The checked-in PDF can also be rebuilt locally without the full web stack:

```powershell
cd .\src
$env:Path += ";C:\Program Files\Graphviz\bin"
dot -Tpdf figures\stokes-core-graph.dot -o figures\stokes-core-graph.pdf
dot -Tpdf figures\stokes-halfspace-graph.dot -o figures\stokes-halfspace-graph.pdf
dot -Tpdf figures\stokes-boundary-chart-graph.dot -o figures\stokes-boundary-chart-graph.pdf
dot -Tpdf figures\stokes-global-assembly-graph.dot -o figures\stokes-global-assembly-graph.pdf
xelatex -interaction=nonstopmode -halt-on-error print.tex
xelatex -interaction=nonstopmode -halt-on-error print.tex
Copy-Item -LiteralPath print.pdf -Destination ..\stokes-blueprint.pdf -Force
```
