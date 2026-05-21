# surfer-web 参考盘点

## 结论

`C:\Users\jiang\Desktop\surfer-web` 对本项目的价值主要是“公式资料库”和“渲染对照”，不是证明系统的代码来源。

原因很简单：`surfer-web` 的公式 parser、evaluator、GLSL 展开和 WebGL solver 都服务于数值渲染。它们能帮助我们找到方程、看图、做 sanity check，但不能替代 exact algebra proof。

因此当前原则是：

- 只把 gallery 公式、参数、曲面名称和来源路径作为资料引用。
- 不搬 `.surfer`/RunMat/MATLAB 前端。
- 不移植 `packages/lab-surface/src/parser/*`，除非后续只是为了读入 gallery 字符串做探索。
- 证明主线由本项目自己的 Rust exact polynomial / gradient / Hessian 工具承担。

另外，`surfer-web` 当前工作树很脏，很多源码在 working tree 里被删除；本次只读取了 `HEAD`，不修改它。

## 可参考资产

| 资产 | surfer-web 位置 | 用途 | 是否进入证明主线 |
|---|---|---|---|
| gallery records | `examples/script/gallery/record/*.surfer` | 低次数到高次数的现成公式库 | 作为资料，不直接证明 |
| 公式 AST/parser | `packages/lab-surface/src/parser/*` | 理解 gallery 字符串语法；必要时做离线转换参考 | 不进入 |
| CPU evaluator | `evaluator.ts` | 数值 smoke test、调参、梯度探针 | 不进入 |
| GLSL 多项式发射 | `glslEmitterPolynomial.ts` | 理解渲染时如何沿射线展开一元多项式 | 不进入 |
| WebGL solver | `packages/runtime-surface-core/src/webgl/*`, `src/shaders/*` | 后续做可视化时可借鉴 | 不进入 |
| RunMat Rust parser | `runmat/crates/runmat-parser`, `runmat-lexer` | Rust parser 工程组织参考 | 不进入 |

## gallery 对我们的价值

`surfer-web` 的 record gallery 已经覆盖了我们关心的“来时路”：

| 文件 | 例子 | 次数 | 对复现项目的用途 |
|---|---|---:|---|
| `record_doppelkegel.surfer` | double cone / quadric cone | 2 | 对照 `degree02` |
| `record_cayleycubic.surfer` | Cayley cubic | 3 | `degree03` 的可视化/affine 对照 |
| `record_kummerquartic.surfer` | Kummer quartic | 4 | 进入 16 nodes 配置 |
| `record_togliatti.surfer` | Togliatti quintic | 5 | 五重对称构造 |
| `record_barthsextic.surfer` | Barth sextic | 6 | 黄金比/二十面体对称 |
| `record_labsseptic.surfer` | Labs septic | 7 | 99 nodes 下界路线 |
| `record_endrass.surfer` | Endraß octic | 8 | 当前主目标的 affine 渲染公式 |
| `record_chmutovoktic.surfer` | Chmutov octic | 8 | 与 Endraß 对比的另一类构造 |

这里最该保留的是来源索引：这些公式可以作为“历史图库”和 regression corpus，但节点证明必须回到齐次方程、偏导方程和 Hessian 非退化性。

## degree03 的调整

`degree03` 不从 gallery parser 开始，而是直接做证明。

1. `degree03` 的证明目标仍用标准齐次 Cayley cubic：

   ```text
   wxy + wxz + wyz + xyz = 0
   ```

   这个形式四个节点一眼可列，适合做 exact proof。

2. `surfer-web` 的 Cayley 公式只作为 gallery 对照：

   ```text
   x^3+y^3+z^3+1-0.25*(x+y+z+1)^3
   ```

   它是 affine 渲染入口，不必强行作为第一版证明目标。后续可以做齐次化：

   ```text
   X^3 + Y^3 + Z^3 + W^3 - (1/4)(X+Y+Z+W)^3
   ```

3. 不为 `degree03` 单独造 parser。先在 `nodal-core` 建一个小的 exact homogeneous polynomial 表示，能表达 monomial + coefficient + derivative + Hessian rank 即可。

4. 即使后续需要读取 gallery 公式，也优先写一个很小的离线转换器；证明层仍只接受明确的 exact polynomial 数据结构。

## 后续建议

短期：

- 在 `doc/engineering-roadmap.md` 标记 `surfer-web` 为公式资料来源。
- `degree03` 只做 exact Cayley cubic，不先搬 parser。
- 新增一个资料层，例如 `data/surfer-web-gallery/records.toml`，记录 title、formula、params、source path。

中期：

- 至少支持 `Q`、`Q(sqrt(2))`、`Q(sqrt(5))` 三档；Endraß、Kummer、Barth 都会用到。
- 区分两条链路：
  - proof lane：本项目 exact polynomial, gradient ideal, Hessian nondegeneracy。
  - exploration lane：数值 evaluator, sampling, visualization, surfer gallery preview。

暂不搬：

- `.surfer` 脚本宿主。
- `packages/lab-surface/src/parser/*`。
- RunMat MATLAB parser。
- WebGL shader solver。

这些以后做可视化或 WebLab 集成时很有用，但现在会压过“理解构造和证明节点数”的主线。
