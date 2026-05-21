# 项目结构

这个目录放阅读、复现过程文档和工程路线说明；代码实现放在 workspace 的 `crates/` 下。

## 目录

- `arxiv/`: 参考论文原文、PDF、TeX 源和提取文本。
- `doc/`: 过程文档、论文理解笔记、后续复现路线。

## 当前资料

- `arxiv/endrass_9507011.pdf`: Endraß 的原始论文 PDF。
- `arxiv/endrass_9507011.tex`: arXiv TeX 源。
- `arxiv/endrass_9507011.txt`: 从 PDF 提取出的纯文本，便于搜索。
- `arxiv/endrass_9507011.tex.gz`: arXiv e-print 原始压缩包。

`arxiv/` 下面现在还按主题分了子目录：

- `bounds/`: 上界证明或上界相关资料。
- `construction/`: 构造技术和后续多节点曲面。
- `low-degree/`: 低次数经典例子的构造材料。
- `surveys/`: 综述、博士论文、历史线索。
- `classical/`: 暂留给更早的经典扫描件。

`doc/` 中的重要文件：

- `bibliography.md`: 本地文献库和待补文献清单。
- `historical-roadmap.md`: 从 2 次到 8 次的来时路和构造脉络。
- `endrass-octic-reading-notes.md`: Endraß 论文的初读笔记。
- `engineering-roadmap.md`: Rust workspace 的实现边界和各次数复现状态。
- `groebner-certificate-format.md`: 外部 CAS Groebner basis 导入格式与当前 verifier 语义。
- `cas-toolchain.md`: Windows/Cygwin-based Singular 工具链、构建补丁和 smoke test。
- `kummer-quartic.md`: `degree04` Kummer quartic 的数学解释、奇异集穷尽证书和 `16_6` 配置说明。
- `togliatti-quintic.md`: `degree05` Togliatti quintic 的两个模型、special 分支 31 节点证书链和 determinant 分支 blocker。
- `degree05-lessons.md`: `degree05` 复现后的数学/工程经验总结，解释 length、saturation、Hessian 和 lift 证书的作用。
- `barth-sextic.md`: `degree06` Barth sextic 的数学预备文档，整理方程、A/B/C 节点 orbit、`65=15+30+20` 的几何来源、`mu(6)=65` 上界来源和 Rust 证书路线。
- `surfer-web-reuse-audit.md`: 对已有 `surfer-web` 项目中公式、gallery、parser、渲染资产的复用判断。

## 暂定原则

- 先理解论文结构，再把可检验证书落到代码。
- 先做低维/小次数验证，再复现 Endraß octic。
- Rust 主线保持 exact algebra；数值或渲染项目只作为公式和视觉参考。
