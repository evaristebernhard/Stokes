# CAS 工具链

本项目的证明主线仍然是 Rust verifier；外部 CAS 只负责生成候选 Groebner basis、消元多项式或节点坐标证书。外部输出必须落成可复查的文本证书，再由 `nodal-core` 做 exact verification。

## 当前本机选择

Windows 本机采用 Cygwin-based Singular，而不是 WSL/Ubuntu。

安装根目录：

```text
%LOCALAPPDATA%\MathCAS\cygwin64
```

Cygwin setup 缓存：

```text
%LOCALAPPDATA%\MathCAS\cygwin-setup
%LOCALAPPDATA%\MathCAS\cygwin-packages
```

当前可执行文件在 Cygwin 内：

```text
/usr/local/bin/Singular.exe
```

从 PowerShell 调用：

```powershell
& "$env:LOCALAPPDATA\MathCAS\cygwin64\bin\bash.exe" -lc "export PATH=/usr/local/bin:/usr/bin:/bin; Singular --version"
```

已验证版本：

```text
Singular for x86_64-CYGWIN_NT-10.0-26200 version 4.4.1 (44105, 64 bit)
```

内置模块包含：

```text
gfanlib gitfan interval loctriv partialgb syzextra customstd cohomo subsets freealgebra systhreads
```

最小 Groebner smoke test：

```powershell
& "$env:LOCALAPPDATA\MathCAS\cygwin64\bin\bash.exe" -lc "export PATH=/usr/local/bin:/usr/bin:/bin; Singular -q --no-rc -c 'ring r=0,(x,y),dp; ideal I=x^2-y,y^2-x; ideal G=std(I); G; quit;'"
```

输出应为：

```text
G[1]=y2-x
G[2]=x2-y
```

## 本地构建补丁

Cygwin 在这台 Windows 环境里返回：

```text
getconf PAGESIZE = 65536
```

Singular 源码中的 `omalloc` 原先只接受 `4096`、`8192`、`16384`，因此 configure 会失败。当前在临时源码树：

```text
%LOCALAPPDATA%\MathCAS\cygwin64\tmp\wawa\singular\omalloc
```

做了最小补丁：

- `configure.ac` 与生成的 `configure` 接受 `65536`。
- `omDerivedConfig.h` 增加 `SIZEOF_SYSTEM_PAGE == 65536` 时的 `LOG_BIT_SIZEOF_SYSTEM_PAGE = 16`。

这是工具链构建补丁，不属于数学证明本体。后续若重拉 Singular 源码，需要重复这个补丁，或改用已经支持 64K page size 的上游版本。

## WSL 状态

本项目当前不使用 Ubuntu/WSL 作为 CAS 依赖。`wsl -l -v` 已确认没有 Ubuntu 发行版，只剩 `docker-desktop`。

## 与 degree05 的关系

Togliatti quintic 的 `w=1` chart 用 SymPy 可以算出一份 grevlex basis，但系数会超过当前 `i128 Rational` 的安全范围。下一步更适合用 Singular 生成稳定的 chart-by-chart 证书，然后在 Rust 里实现：

- BigRational 系数支持。
- Singular 输出到 `doc/groebner-certificate-format.md` 所定义格式的导出器。
- Rust 侧 Groebner basis verifier 与 quotient length verifier。
- projective chart/saturation 语义检查。

原则上，Singular 的计算结果只作为证书来源；项目结论仍以 Rust verifier 通过为准。
