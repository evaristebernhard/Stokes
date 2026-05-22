# Degree08 Critical-Value Profile Search

## 目标

这一支路线先不从 Endraß 的

```text
F = P8 - R4^2
```

出发，而是研究分离变量曲面

```text
F(x,y,z,w) = alpha*Q_h(x,y,w) + T8_h(z,w) + lambda*w^8
```

其中 `Q(x,y)` 是八条仿射直线的乘积：

```text
Q = prod_{i=1}^8 l_i(x,y)
```

核心问题是二维 critical-value profile：

```text
Q_x = Q_y = 0
```

的临界点能否高度集中到两个临界值层。

## 计数公式

在 affine chart `w=1` 中，若

```text
F = P(x,y) + T8(z) + lambda
```

且 `P` 的目标临界点都是 Morse 临界点，则曲面奇点来自

```text
P_x = P_y = 0
T8'(z) = 0
P(x,y) + T8(z) + lambda = 0
```

`T8` 的临界值为 `-1,+1`，对应临界点数分别是：

```text
T8 = -1: 4
T8 = +1: 3
```

所以若把 `P` 的两个临界值层记为

```text
a = m_P(t)
b = m_P(t-2)
```

则理想节点数为：

```text
N = 4a + 3b
```

当前 CLI 对任意两个不同的有限域临界值 `u,v` 做归一化：

```text
alpha = 2 / (u - v)
lambda = 1 - alpha*u
```

这样 `u` 对齐到 `T8=-1` 的四重侧，`v` 对齐到 `T8=+1` 的三重侧。

## 49 与 28+21

一般八次二维多项式的有限临界点数上限是：

```text
(8 - 1)^2 = 49
```

对八线乘积 `Q=prod l_i`，如果八条线无平行、无三线共点，则：

```text
Q = 0
```

在 28 个两两交点处给出 Morse 临界点，因为局部形状是

```text
unit * u * v
```

剩余理论预算是：

```text
49 - 28 = 21
```

因此最关键的突破 profile 是：

```text
(28,19) -> 4*28 + 3*19 = 169
```

更强的目标包括：

```text
(27,21) -> 171
(27,22) -> 174
```

这解释了为什么这条路线不是寻找“多一点点”节点，而是寻找一个几乎把全部 49 个二维临界点压进两个值层的八线 arrangement。

## 有限域语义

当前实现枚举的是：

```text
A^2(F_p)
```

上的可见临界点，而不是代数闭包上的完整 critical scheme。这个限制很重要。

对一般八线 arrangement，28 个线交点在 `F_p` 上可见，但另外 21 个 off-line 临界点常常定义在扩域里。因此有限域 profile 中常见现象是：

```text
zero_morse = 28
best_nonzero_morse = 1,2,3
```

这不证明特征零中不存在好 arrangement；它只说明当前 `F_p` rational-point 雷达没有看到强候选。若未来要真正分析 off-line 21 点，可能需要加入代数闭包意义的 elimination/Groebner critical-value certificate，而不是只枚举 `A^2(F_p)`。

## Rust 实现

基础设施在：

```text
crates/degree08/src/critical_profile.rs
```

它提供：

```text
AffineLineArrangementFp
AffineLineArrangementFp::normal_form10(...)
critical_value_profile(P)
critical_value_profile_for_lines_fast(lines)
line_product_polynomial(lines)
slope_polynomial_lines(coefficients)
homogenize_affine_bivariate_to_p3(P, degree, x, y, w)
chebyshev_profile_surface(P, pair)
```

CLI 在：

```text
crates/degree08/src/bin/search_critical_profile.rs
```

现在有两条八线参数族：

```text
slope-poly:
t in {-4,-3,-2,-1,1,2,3,4}
l_t = x + t*y + (a0*t^2 + a1*t^3 + ...)*1

normal10:
L0 = x
L1 = y
L2 = 1 - x - y
Li = 1 + s_i*(r_i*x + y), i=3,...,7
```

`coeff-count=6` 时，这相当于固定 8 个斜率后扫描 6 个有效截距自由度；低于一次的截距项对应 affine 坐标变化，因此不列入参数。

`normal10` 是八条仿射直线模 affine/projective 归一化后的 10 维 chart。前三条线被规范化为坐标三角形，后五条线由 `(r_i,s_i)` 给出。Rust 端对每个 arrangement 先做 determinant 预过滤：

```text
parallel pair:
  a_i*b_j - a_j*b_i = 0

triple concurrency:
  det [[a_i,b_i,c_i],
       [a_j,b_j,c_j],
       [a_k,b_k,c_k]] = 0

infinity/empty-line degeneracy:
  (a_i,b_i) = (0,0)
```

只有无平行、无三线共点、无无穷远退化的 simple arrangement 才进入 profile 评分。

八线 profile 现在走专用 fast path。对 `Q=prod_i L_i`，在每个 `A^2(F_p)` 点直接计算线值：

```text
Q    = prod_i L_i
Qx   = sum_i a_i prod_{j!=i} L_j
Qy   = sum_i b_i prod_{j!=i} L_j
Qxx  = 2 sum_{i<j} a_i*a_j prod_{k!=i,j} L_k
Qxy  = sum_{i<j} (a_i*b_j+a_j*b_i) prod_{k!=i,j} L_k
Qyy  = 2 sum_{i<j} b_i*b_j prod_{k!=i,j} L_k
```

因此内层搜索不再为每个候选展开 `SparsePolynomial`；只有 top candidates 在 projective scorer 验证时才构造 `Q_h`。

使用示例：

```text
cargo run -q -p degree08 --bin search_critical_profile -- \
  --prime 31 --coeff-count 6 --sample lcg --seed 1 \
  --scan-limit 50000 --profile-limit 40 --verify-top 12

cargo run -q -p degree08 --bin search_critical_profile -- \
  --family normal10 --prime 31 --scan-limit 50000 \
  --directions 500 --intercepts-per-direction 200 \
  --local-climb 4 --pair-sweep 1 \
  --profile-limit 64 --verify-top 12
```

程序先按二维 profile 排序，再只把 top candidates 齐次化并调用既有：

```text
score_projective_surface
```

做 projective finite-field scorer 验证。

`search_critical_profile` 对 `normal10` 采用 direction/intercept 分层采样：先抽五个方向 `r_i`，再为这一组方向抽多组截距参数 `s_i`。top-k 用 heap 保留；之后可对前若干候选做 coordinate climb，和对更少候选做 pair sweep。`--params` 可以把某个候选的整数参数原样拿到其它素数复验。

CAS 导出器在：

```text
crates/degree08/src/bin/export_critical_profile_offline_singular.rs
```

它为候选输出 Singular 脚本，计算 off-line critical algebra：

```text
K = <Qx,Qy,uQ-1> subset F_p[x,y,u]
```

这里 `uQ-1` 去掉 `Q=0` 的 28 个线交点，只看剩余 21 个 off-line 临界点。脚本使用：

```text
G = std(K)
B = qbase(G)
M = matmult(Q,B,G)
charpoly(M)
factorize(charpoly(M))
```

`factorize(charpoly(M))` 中每个不可约因子的指数就是代数闭包中对应 critical-value fiber 的长度；当前记录的中筛指标是：

```text
off_best_bucket = max factor exponent
```

## 当前 smoke 结果

结果文件：

```text
crates/degree08/search-results/critical-profile-eight-line-mod31.tsv
crates/degree08/search-results/critical-profile-eight-line-mod47.tsv
crates/degree08/search-results/critical-profile-eight-line-mod97.tsv
crates/degree08/search-results/critical-profile-normal10-mod31.tsv
crates/degree08/search-results/critical-profile-normal10-mod31.jsonl
crates/degree08/search-results/critical-profile-normal10-top-mod47.tsv
crates/degree08/search-results/critical-profile-normal10-top-mod47.jsonl
crates/degree08/search-results/critical-profile-normal10-top-mod97.tsv
crates/degree08/search-results/critical-profile-normal10-top-mod97.jsonl
crates/degree08/search-results/critical-profile-normal10-top-mod31-offline.txt
crates/degree08/search-results/critical-profile-normal10-top-mod47-offline.txt
crates/degree08/search-results/critical-profile-normal10-top-mod97-offline.txt
```

固定斜率 `slope-poly` 的 best visible profiles：

```text
p=31, scan-limit=50000:
  zero_morse=28, best_nonzero_morse=3
  predicted_affine_nodes=121
  full projective node_like=121, bad_sing=0

p=47, scan-limit=30000:
  zero_morse=28, best_nonzero_morse=2
  predicted_affine_nodes=118
  full projective node_like=118, bad_sing=0

p=97, scan-limit=5000:
  zero_morse=28, best_nonzero_morse=2
  predicted_affine_nodes=118
  full projective node_like=118, bad_sing=0
```

因此这一轮没有得到 `164+` near hit，更没有得到 `(28,19)`。按原计划，`p=113,127` 应用于复验稳定 hit；因为 `31/47/97` 没有稳定强 hit，本轮没有继续消耗时间做深复验。

10 维 `normal10` 第一轮搜索：

```text
p=31, scan-limit=50000, directions=500, intercepts=200,
local-climb=4, pair-sweep=1:
  best params = 15,3,-3,14,-5,-14,-4,-11,5,-15
  visible profile = 0:28, 28:3, 20:1
  predicted_affine_nodes = 121
  full projective node_like = 121, bad_sing = 0

same integer params over p=47:
  visible profile = 0:28, 4:1
  predicted_affine_nodes = 115
  full projective node_like = 115, bad_sing = 0

same integer params over p=97:
  visible profile = 0:28, 6:1
  predicted_affine_nodes = 115
  full projective node_like = 115, bad_sing = 0
```

off-line CAS 中筛：

```text
p=31:
  off_length = 21
  qbase_size = 21
  det(m_Q) = 8
  F_p fibers: value 20 has length 1, value 28 has length 3
  charpoly factors have exponents 1,1,1,1,3
  off_best_bucket = 3

p=47:
  off_length = 21
  F_p fiber: value 4 has length 1
  off_best_bucket = 1

p=97:
  off_length = 21
  F_p fiber: value 6 has length 1
  off_best_bucket = 1
```

这说明 `p=31` 的 `28+3` 不是一个稳定的代数闭包聚集信号；跨素数后同一候选只保留 `28+1`，而 `off_best_bucket` 远低于继续投入阈值 `12`，更不用说目标 `19`。

## 结论

这轮工程主线是成功的：现在已经能从八线 arrangement 直接得到 critical-value profile、构造对应 octic 曲面，并用统一 projective scorer 验证。

但数学信号是负的：固定斜率 `slope-poly` 和第一轮 10 维 `normal10` 都没有显示接近 `(28,19)` 的迹象。特别是 `normal10` 已经把“只看 `A^2(F_p)` 可见点”的疑问推进到 off-line critical algebra 的 charpoly 中筛，而 best candidate 仍只有 `off_best_bucket=3`。

因此八线乘积路线应暂时降级：保留基础设施，但不继续在同一采样范式上做纯放量。若未来继续追八线乘积，应优先升级两个方向：

```text
1. 代数闭包 critical-value profile：
   把 charpoly/factorization 中筛从 top candidate 后处理，前移成更强的 CAS/符号搜索器。

2. 更自由的 arrangement 参数：
   normal10 已经覆盖一个 10 维 chart；下一步需要改变目标函数或结构假设，而不只是随机扫更多点。
```

否则只扩大当前 profile scan，很可能继续看到 `28 + small`，而不是接近 `(28,19)`。

## 几何 no-go 后记

后续数学分析把这条支线从“搜索信号弱”推进到了“clean model 中几何排除”。对八线 pencil

```text
C_t : Q_h - t w^8 = 0
```

非零 fiber 在八个无穷远方向上带有 8 个 total-contact flex。Plucker ramification 预算给出：

```text
delta(C_t) <= 16.
```

因此目标 `(28,19)` 对应的 `19` 节点平面八次 fiber 在特征零 clean model 中不存在。这条路线后续只保留为基础设施和反例经验，不再作为继续放量搜索的主线。

详细解释见：

```text
doc/degree08-plane-octic-plucker.md
doc/degree08-no-go-summary.md
```
