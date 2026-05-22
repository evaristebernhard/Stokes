# Nodal Surfaces 文献库

这个文件记录本地已经下载的论文，以及仍需补的历史文献。分类不是严格书目学分类，而是按复现 Endraß octic 时最有用的阅读路线来分。

## 主目标

- `arxiv/endrass_9507011.pdf`
  S. Endraß, "A Projective Surface of Degree Eight with 168 Nodes", arXiv:alg-geom/9507011.
  作用：168 节点八次曲面的原始构造。

## 构造技术

- `arxiv/construction/catanese-ceresa-1982-constructing-sextic-surfaces.pdf`
  F. Catanese, G. Ceresa, "Constructing Sextic Surfaces with a Given Number d of Nodes", JPAA 23 (1982), 1-12.
  作用：Segre trick 的系统化版本；Proposition 5 给出平方覆盖下的节点计数公式 `d = 8t + 4r + 2s + m`。

- `arxiv/construction/kuehnel-2002-octic-hypersurfaces-with-many-nodes.pdf`
  M. Kühnel, "A note on octic hypersurfaces with many nodes", arXiv:math/0210440.
  作用：Endraß 之后的八次曲面背景，提到 Miyaoka 174 上界和 octic 构造变体。

- `arxiv/construction/breske-labs-van-straten-2005-real-line-arrangements.pdf`
  B. Breske, O. Labs, D. van Straten, "Real line arrangements and surfaces with many real nodes", arXiv 版本。
  作用：线配置和多实节点构造，属于 Endraß 之后的系统构造路线。

- `arxiv/construction/breske-labs-van-straten-2008-real-line-arrangements-published.pdf`
  同题发表版本。
  作用：保留发表版用于引用。

- `arxiv/construction/labs-2006-septic-99-real-nodes.pdf`
  O. Labs, "A septic with 99 real nodes", Rend. Sem. Mat. Univ. Padova 116 (2006), 299-313.
  作用：七次曲面的实节点构造，连接 Chmutov/line arrangement 传统。

- `arxiv/construction/escudero-2011-surfaces-many-real-nodes.pdf`
  J. Escudero, "A construction of algebraic surfaces with many real nodes", arXiv:1107.3401.
  作用：Chmutov/Folding/Chebyshev 型构造的后续发展。

- `arxiv/construction/escudero-2013-family-complex-surfaces-degree-3n.pdf`
  J. Escudero, "On a family of complex algebraic surfaces of degree 3n", arXiv:1302.6747.
  作用：系统化构造多节点曲面的后续材料。

## 上界证明

- `arxiv/bounds/varchenko-1983-semicontinuity-spectrum.pdf`
  A. N. Varchenko, "Semicontinuity of the spectrum and an upper bound for the number of singular points of the projective hypersurface", Dokl. Akad. Nauk SSSR 270 (1983), 1294-1297.
  作用：spectrum 半连续性给出 Arnold number 上界。对八次曲面给 180，不是 174。

- Miyaoka, "The Maximal Number of Quotient Singularities on Surfaces with Given Numerical Invariants", Math. Ann. 268 (1984), 159-171.
  作用：给出 nodal surface 的 Miyaoka 上界 `mu(d) <= floor(4/9 d(d-1)^2)`；对 `d = 8` 得 174。
  状态：已确认出处，开放 PDF 暂未下载成功。EuDML 条目：https://eudml.org/doc/182912

- `arxiv/bounds/beauville-1980-mu5-equals-31.pdf`
  A. Beauville, "Sur le nombre maximum de points doubles d'une surface dans P3 (mu(5)=31)", Algebraic Geometry Angers 1979, pp. 207-215.
  作用：证明五次曲面最大节点数 `mu(5) = 31`。本地 PDF 是扫描版，暂未 OCR。

- `arxiv/bounds/jaffe-ruberman-1995-sextic-cannot-have-66-nodes.pdf`
  D. Jaffe, D. Ruberman, "A sextic surface cannot have 66 nodes", arXiv:alg-geom/9502001.
  作用：六次曲面上界 `mu(6) <= 65` 的关键文献。
  状态：arXiv 当前只提供一页说明，原 PostScript 地址已经失效；需继续寻找完整扫描件。

- `arxiv/bounds/pignatelli-on-wahl-proof-mu6-65.pdf`
  R. Pignatelli, notes on Wahl/Jaffe-Ruberman style proof around `mu(6)=65`.
  作用：辅助理解六次曲面上界和 Barth sextic 的 code 方法。

## 低次数入口

- `arxiv/low-degree/stagnaro-1983-degree-5-31-nodes.pdf`
  E. Stagnaro, "A new construction of a surface of degree 5 having 31 nodes", Rend. Sem. Mat. Univ. Padova 69 (1983), 27-33.
  作用：给出 Togliatti 五次曲面的另一种构造，适合复现。

## 综述和历史

- `arxiv/surveys/labs-2005-hypersurfaces-with-many-singularities-thesis.pdf`
  O. Labs, "Hypersurfaces with Many Singularities", PhD thesis, Mainz, 2005.
  作用：目前最适合当路线图的综述；包含 lower/upper bound 表、Miyaoka/Varchenko 比较、Chmutov 和高对称构造。

- `arxiv/surveys/catanese-2022-nodal-surfaces-coding-theory-cubic-discriminants.pdf`
  F. Catanese, M. Kiermaier, S. Kurz, "Nodal Surfaces, Coding Theory, and Cubic Discriminants", arXiv:2206.05492.
  作用：把 Cayley/Kummer/Togliatti/Barth 与 binary codes 统一起来，非常适合理解低次数极值例子背后的结构。

- `arxiv/surveys/stagnaro-1978-max-isolated-double-points.pdf`
  E. Stagnaro, "Sul massimo numero di punti doppi isolati di una superficie algebrica di P3", Rend. Sem. Mat. Univ. Padova 59 (1978), 179-198.
  作用：旧纪录、Basset/Segre/Gallarati/Kreiss 等历史线索。

- `arxiv/surveys/barth-obituary-2017-history-symmetry-surfaces.pdf`
  Barth obituary / historical account.
  作用：辅助理解 Barth 的高对称曲面传统。

## 待补优先级

1. Barth, "Two projective surfaces with many nodes, admitting the symmetries of the icosahedron", JAG 5 (1996), 173-186.
   价值：Barth sextic 原始构造；目前只在二手资料和综述中可读。

2. Jaffe-Ruberman 完整正文。
   价值：`mu(6)=65` 的上界证明；arXiv 当前只剩说明页。

3. Miyaoka 1984 完整 PDF。
   价值：174 上界的真正来源。

4. Chmutov 1992 原文。
   价值：Chebyshev/Folding polynomial 系统造节点的起点。

5. Togliatti 1940 原文。
   价值：五次 31 节点的经典构造源头。

6. Gallarati/Kreiss 关于八次 160 节点的原始材料。
   价值：Endraß 打破的旧纪录来源。
