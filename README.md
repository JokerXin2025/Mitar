# Mitar

Mitar 是 [ProofScript](https://github.com/JokerXin2025/ProofScript) 的静态 HTML
渲染器。ProofScript 在 Lean 编译期导出页面组件和结构化证明树，Mitar 读取这些 JSON，
将 Lean 表达式转换为 TeX，并生成带有证明步骤、源码翻转、文献引用、图片和项目导航的页面。

```text
Lean source
  -> ProofScript
  -> .ProofScript/pages + .ProofScript/proofs
  -> Mitar
  -> .Mitar/build
```

Mitar 不替代 Lean 的证明检查，也不解析 Lean 源码来重建证明；证明语义和页面组件均以
ProofScript 的 JSON Schema 为准。

## 目录

- [功能](#功能)
- [快速开始](#快速开始)
- [CLI](#cli)
- [页面组件](#页面组件)
- [证明渲染](#证明渲染)
- [引用与文献](#引用与文献)
- [项目产物](#项目产物)
- [渲染规则扩展](#渲染规则扩展)
- [环境要求](#环境要求)
- [Demo](#demo)
- [当前限制](#当前限制)

## 功能

- 按 Lean 模块镜像结构生成 HTML 页面和项目入口页；
- 完整渲染当前 ProofText inline/block 语法；
- 渲染 `@theorem` / `@lemma` 的结构化证明树；
- 将 ProofScript ExprJSON 转换为 TeX，并通过 KaTeX 显示数学表达式；
- 使用 Pygments 在构建期高亮 ProofText 代码块和 theorem 源码；
- 显示证明状态：通过、使用 `sorryAx`、JSON/证明结构错误；
- 渲染 `ProjectInfo`、跨页面标签、参考文献和模块导航；
- 渲染页面级 `@latex` SVG 和 `@figure` 图片资源；
- 在专用 Web Worker 中运行 finalized `@computation` Lean/Wasm 组件；
- 对未知 proof tactic 显示红色“未知策略”步骤，而不是静默丢弃；
- 为 Lean2TeX fallback 和媒体错误生成 `.Mitar/build/lean2tex-report.json`。

## 快速开始

### 1. 安装环境

需要安装：

- Lean 4、Lake 和 Elan；
- Python 3.11 或更高版本；
- Pygments（安装 Mitar 时自动安装）；
- 可选：使用 `@latex` 或证明内 LaTeX 策略时，需要 `latex`、`dvisvgm` 和相应 TeX 宏包。

推荐将 ProofScript 和 Mitar 仓库并排放置：

```text
workspace/
├── ProofScript/
└── Mitar/
```

从 Mitar 目录安装：

```bash
git clone https://github.com/JokerXin2025/ProofScript.git
git clone https://github.com/JokerXin2025/Mitar.git
cd Mitar
make install
```

`make install` 会：

- 将 ProofScript 安装至 `~/.ProofScript/`；
- 将 Mitar 的 CSS/JS 安装至 `~/.Mitar/`；
- 执行 `lake build` 构建 ProofScript；
- 以 editable 模式安装 Python 包和 `mitar` 命令。

开发 Mitar 本身时也可以只安装 Python 包：

```bash
python3 -m pip install -e .
```

此时 Lean 项目需要自行在 `lakefile.toml` 中指向可用的 ProofScript 仓库。

### 2. 配置 Lean 项目

`lakefile.toml` 示例：

```toml
name = "Example"
version = "0.1.0"
defaultTargets = ["Example"]

[[require]]
name = "ProofScript"
path = "/Users/you/.ProofScript"

[[lean_lib]]
name = "Example"
```

开发时也可以使用相对路径：

```toml
[[require]]
name = "ProofScript"
path = "../../ProofScript"
```

更新依赖：

```bash
lake update
```

### 3. 编写页面

```lean
import ProofScript

project_info {
  title := "An Example Formal Paper",
  authors := "Alice, Bob",
  abstract := "A small ProofScript and Mitar demonstration.",
  keywords := "Lean, formal proof, structured proof",
  year := "2026"
}

@text r#"
= Introduction <introduction>

This page contains a recorded theorem. See @thm:main-result.

- ProofScript exports semantic JSON
- Mitar renders the project as HTML
"#

@theorem @[theorem_info (
  name := "Main Result",
  label := "main-result"
)] mainResult (P : Prop) (h : P) : P := script
  remark "The hypothesis is exactly the desired conclusion."
  provide h

@references

page_end
```

`page_end` 会结束当前模块页面并写出 Page JSON；其后的页面组件会被 ProofScript 忽略。
ProofScript DSL、策略和 recorder 的完整说明请参考
[ProofScript README](https://github.com/JokerXin2025/ProofScript/blob/main/README.md)。

### 4. 构建 HTML

在 Lean 项目根目录执行：

```bash
mitar make .
```

也可以省略 `make`：

```bash
mitar .
```

打开：

```text
.Mitar/build/index.html
```

包含嵌入式计算的页面不能通过 `file://` 直接打开。请启动 Mitar 的静态服务器：

```bash
mitar serve
```

然后访问 `http://127.0.0.1:8000/`。该服务器会设置 Wasm MIME、COOP、COEP 和 CSP 响应头。

允许同一局域网内的设备访问：

```bash
mitar serve --lan
```

命令会监听所有网卡并打印本机局域网 URL。普通页面可以通过 LAN HTTP 查看；当前 pthread
计算使用 `SharedArrayBuffer`，在非 localhost 设备上还要求受信任 HTTPS。可用 `mkcert` 为本机
IP 生成受信任证书，然后运行：

```bash
mitar serve --lan --cert ./localhost+2.pem --key ./localhost+2-key.pem
```

证书必须包含输出的局域网 IP，并在访问设备上受信任。

## CLI

### 构建整个项目

```bash
mitar make .
```

Mitar 在非缓存模式下会先清空整个 `.ProofScript/`，避免复用过期的页面、证明树或 computation
资源，然后执行 `lake build`。这对项目级构建和单模块构建都适用。由于清空后页面 JSON 不存在，项目级
构建会扫描项目中的 Lean 源文件，补编译包含 `page_end` 的页面模块；没有 `page_end` 的普通 Lean
模块不会被 Mitar 导出为页面。随后 Mitar 构建并 finalize Wasm，再按模块镜像结构生成 HTML。需要完全
跳过 Lean 和 computation 构建、直接使用已有 ProofScript JSON 时仍可使用 `--cache`。

### 构建单个模块

```bash
mitar make Paper.Main
```

模块名会解析为：

```text
Paper.Main
-> Paper/Main.lean
-> .ProofScript/pages/Paper/Main.json
-> .Mitar/build/Paper/Main.html
```

非缓存的单模块模式同样先清空整个 `.ProofScript/`，然后构建模块 C IR，再强制执行页面导出：

```bash
lake build Paper.Main
lake env lean Paper/Main.lean
```

### 使用已有缓存

```bash
mitar make . --cache
mitar make Paper.Main --cache
```

`--cache`（`-c`）完全跳过 Lean 编译，直接渲染已有 ProofScript JSON。该模式不会检查
JSON 是否比 Lean 源文件更新；页面或证明树缺失时会报告错误。

### 加载额外 tactic 渲染规则

```bash
mitar make . --config ./MyRules
mitar make . -t ./RulesA -t ./RulesB
```

每个目录下的 `*.toml` 会作为额外 proof tactic 展示规则加载。

### 清理产物

```bash
mitar clean
```

删除当前 Lean 项目的：

```text
.ProofScript/
.Mitar/build/
```

## 页面组件

### ProjectInfo

Mitar 从每个 Page JSON 根字段 `ProjectInfo` 读取项目元数据。项目入口页会显示首个具有非空
标题的 ProjectInfo，包括标题、作者、期刊、年份和摘要。

### ProofText

Mitar 支持当前 ProofText Schema 中的全部公开 inline/block 类型：

- 1 至 4 级标题与标题 label；
- 段落、软换行和硬换行；
- 粗体、强调、粗体强调、删除线、下划线和高亮；
- 上标、下标、行内代码和行内数学；
- URL、标题引用、定理引用和图片引用；
- 无序列表、有序列表和强制序号；
- 引用块、行间公式和整段代码块。

代码块根据语言查找 Pygments lexer，成功时生成 Mitar 自有 token class；未知语言安全回退为
HTML 转义后的纯文本。ProofText 代码块使用 dark 主题。

### ``

ProofScript 将任意 LaTeX 编译为 SVG：

```lean
 (
  title := "交换图",
  label := "commutative-diagram"
) r#"
\begin{tikzpicture}
  \draw[->] (0,0) -- (1,0);
\end{tikzpicture}
"#
```

Mitar 将 SVG 编码为 `data:image/svg+xml;base64,...` 并通过 `<img>` 嵌入页面。LaTeX 组件
与 figure 共用 `figure` 引用命名空间：

```text
@fig:commutative-diagram
```

### ``

```lean
 (
  title := "架构图",
  label := "architecture",
  width := "wide"
) "assets/architecture.png"
```

Mitar 相对于 Lean 项目根目录读取资源，阻止绝对路径和目录越界，将图片编码为 data URI
嵌入 HTML。资源缺失或字段错误时，页面显示媒体错误块并写入 diagnostics。

`metadata.extra` 当前保存在 HTML 的 `data-extra` 属性中，但尚未自动解释为布局选项。

### References

ProofScript 会收集证明中实际使用且注册了 `theorem_info` 的声明；`` 将当前暂存区
作为页面组件插入。Mitar 按 ProjectInfo 分组展示文献信息，并在目标 theorem 同样被导出为
页面组件时生成跨页面链接。

### ``

Mitar 在非 `--cache` 构建中完成最后一次 Lean 编译后，自动执行 ProofScript 的
`build-computations.mjs` 和 `finalize-computations.mjs`，并将 finalized computation 资源发布到
`.Mitar/build/.ProofScript/resources/computation/`。构建 Wasm 需要设置：

```bash
export PROOF_SCRIPT_LEAN_WASM_PREFIX=/path/to/matching/lean-wasm-prefix
mitar make .
```

浏览器运行时校验 manifest、ES module 和 Wasm 的 SHA-256 与字节长度，在专用 module Worker
中执行 ABI 调用，并按 bundle hash 复用 Worker。Mitar 只通过本地 registry 解析 renderer ID；
renderer 可在自有前端脚本中注册：

```js
MitarComputation.register("my-project/calculator-v1", async ({ component, compute, element }) => {
  const result = await compute({ value: 21 });
  element.textContent = result.ok ? String(result.value.doubled) : result.error.message;
});
```

`pending` 或未知 renderer 只显示 payload fallback，不会执行 payload 中的代码。计算页面必须通过
HTTP(S) 静态服务发布，不能直接用 `file://` 打开；服务应为 `.wasm` 返回
`application/wasm`，并设置 `Cross-Origin-Opener-Policy: same-origin`、
`Cross-Origin-Embedder-Policy: require-corp` 以及允许同源 Worker 和 Wasm 的 CSP。

内置的 `proofscript/e8-root-explorer-v2` renderer 支持 E8 根族筛选、精确坐标查看、二维可视化、
packing density 和有理半径判定。计数、根坐标、范数及密度数据全部来自 `computeE8` response；
renderer 不重新实现根枚举，也不硬编码根的数量。交互页面还支持坐标轴选择、散点 hover/click、
精确分数坐标检查和反根跳转；二维投影矩阵仅用于 visualization，不作为形式证书。

## 证明渲染

`` 的证明树位于：

```text
.ProofScript/proofs/<module path>/<declaration path>_script.json
```

Proof JSON 顶层包含：

```json
{
  "schemaVersion": "0.2.0",
  "code": " ...",
  "proof": []
}
```

Mitar 会：

- 校验 goal/step 交替结构和核心 discriminator；
- 将目标与策略参数中的 Lean ExprJSON 转换为 TeX；
- 按 Python/TOML 规则将步骤和概略渲染为自然语言结构；
- 在源码翻转面板显示 proof JSON 的完整 `code`，并使用 light Pygments 主题；
- 将未知策略渲染为红色“未知策略”步骤。

状态标记：

| 状态 | 显示 | 条件 |
| --- | --- | --- |
| Pass | 蓝色完成符号 | JSON 和证明结构可正常渲染 |
| Warning | 黄色警告符号 | theorem component 的 `sorryAx` 为 `true` |
| Error | 红色错误符号 | JSON、核心字段、goal/step 结构或渲染发生错误 |

Error 优先于 Warning。单个 theorem 发生错误时，Mitar 尽量保留整个页面并将错误局部显示，
而不是中止所有模块的 HTML 输出。

## 引用与文献

ProofText 引用形式：

| 语法 | 目标 |
| --- | --- |
| `@<label>` | 标题 |
| `@thm:label` | theorem component |
| `@fig:label` | `` 或 `` |

Mitar 在加载全部 Page JSON 后建立跨页面 label index。无法解析的引用会保留为带有明显样式的
文本，而不是生成错误链接。

Reference JSON 当前不携带普通 theorem 的源码位置。如果被引用 theorem 没有通过 ``
导出成页面组件，Mitar 可以显示其元数据，但无法链接到源码或 HTML theorem 锚点。

## 项目产物

假设模块为 `Paper.Main`，主要产物为：

```text
.ProofScript/
├── pages/
│   └── Paper/Main.json
└── proofs/
    └── Paper/Main/<declaration>.json

.Mitar/build/
├── index.html
├── lean2tex-report.json
└── Paper/Main.html
```

`lean2tex-report.json` 包含：

- Lean2TeX fallback/缺失宏诊断；
- theorem 与 proof 路径；
- 媒体资源错误；
- 按诊断 code 汇总的信息。

页面的 CSS、JS 和字体会复制到 `.Mitar/build/assets/`，使 HTML、Worker 和 Wasm 可以通过
同一个 HTTP(S) 静态站点发布。KaTeX 默认仍从 CDN 加载。

## 渲染规则扩展

### TOML tactic 规则

简单 proof tactic 可以使用 TOML 描述：

```toml
name = "provide"
syntax = "provide proof:term"
tag = "构造"
content = "断言${proof}就是符合条件的对象"
```

Tactic 模板支持中文和英文。推荐使用语言区块：

```toml
name = "simp"
syntax = "simp [lemmas:term]"

[language.zh]
tag = "化简后，"
content = "目标可化简为${goal}。"

[language.en]
tag = "After simplification,"
content = "the goal becomes ${goal}."
```

常用字段：

| 字段 | 说明 |
| --- | --- |
| `name` | ProofScript proof JSON 中的 `_step_` 名称 |
| `syntax` | 参数名和类型；Mitar 从中提取参数名 |
| `tag` | 页面步骤标签 |
| `content` | 展示模板 |

模板可以使用：

- `${goal}`：执行前目标；
- `${goal'}`：执行后目标；
- `${parameter}`：策略参数经 Lean2TeX 渲染后的值；
- `$$`：输出字面量 `$`。

条件模板支持：

```toml
[Final]
content = "综上得证"

[NonFinal]
content = "化简后继续证明${goal'}"

[NonFinal.Contra]
content = "由此推出矛盾"
```

内置规则索引位于：

```text
Mitar/Tactic/
```

它加载：

```text
Mitar/Tactic/Built-in/
Mitar/Tactic/Mathlib/
Mitar/Strategy/
```

### Python 规则

复杂步骤和概略仍使用 Python handler，例如：

```text
Mitar/Rules/calc.py
Mitar/Rules/infer.py
Mitar/Rules/have.py
```

Strategy 已统一由 `Mitar/strategy.py` 加载 `Mitar/Strategy/*.toml` 并渲染。每个 Strategy
配置声明 `kind`、节点和所有语言模板；不再为每个 Strategy 单独维护 Python 文件。
普通 tactic 的 TOML loader 位于 `Mitar/tactic.py`，不再放在 `Mitar/Rules/Tactics/`。
使用 `--config DIR` 时，Mitar 会递归扫描 `DIR/Tactic/` 与 `DIR/Strategy/`。

未知策略由 `Mitar/Rules/unknown.py` 生成红色 fallback。新增 ProofScript tactic 后，如果没有
对应 TOML/Python 规则，证明仍可生成页面，但该步骤不会自动获得自然语言语义。

### Lean 表达式

Lean ExprJSON 的语义渲染由 `Lean2TeX/` 完成。宏和变量命名配置位于：

```text
Lean2TeX/config/macros.toml
Lean2TeX/config/variable.toml
```

详细接口参见 [`Lean2TeX/README.md`](Lean2TeX/README.md)。

## 多语言页面

Mitar 当前支持 `zh` 和 `en`。页面构建时会同时生成两种定理证明文本，右上角语言菜单负责无刷新切换。
默认语言可以通过 CLI 指定：

```bash
mitar make Demo --language en
```

也可以在项目根目录的 `mitar.toml` 中指定：

```toml
[mitar]
default_language = "en"
```

CLI 参数优先于项目配置。Tactic、Strategy、Lean2TeX prose、页面导航和参考文献组件都会使用当前语言。

## 环境要求

### 必需

```text
Lean 4 + Lake + Elan
Python >= 3.11
Pygments >= 2.18, < 3
```

### 可选 LaTeX 工具链

使用 `` 或证明内 `tikz`/`figure`/`table` 策略时，需要：

```bash
latex --version
dvisvgm --version
```

还必须安装源码使用的 TeX 宏包，例如 TikZ、booktabs 等。LaTeX 编译发生在 ProofScript
阶段；编译失败会导致 Lean elaboration 失败，Mitar 不会重新编译 LaTeX。

## Demo

仓库内 `demo/` 是可编译的完整示例，包含：

- ProjectInfo 和项目入口；
- 全部当前 ProofText 结构；
- 多种 theorem/proof tree；
- Pygments dark/light 高亮；
- 跨模块文献引用；
- 页面级 ``；
- 页面级 `` 和真实图片资源；
- 大型 Lean 表达式与 Lean2TeX diagnostics。

构建：

```bash
cd demo
lake update
mitar make .
```

打开：

```text
demo/.Mitar/build/index.html
```

若 Mathlib 依赖已经配置，可先获取其缓存：

```bash
lake exe cache get
```

## 当前限制

- ProofScript page schema 中预留的 `custom` component 尚无 Mitar 插件协议；
- 证明内 `tikz` 有基础 SVG 展示，证明内 `figure`/`table` 暂无专用 renderer，会显示“未知策略”；
- Pygments 当前使用 Lean lexer，不是完整 Lean 4 parser，对宏和 ProofScript DSL 的分类可能不精确；
- 图片和 LaTeX SVG 当前以内嵌 data URI 输出，大资源会显著增大 HTML；
- figure 相对路径按 Lean 项目根目录解释；
- `metadata.extra` 被保留但尚无通用布局语义；
- Reference JSON 不包含普通 theorem source location；
- 引用当前显示 label，尚无 theorem/figure/section 自动编号；
- KaTeX 默认来自 CDN，尚未提供完全离线站点模式；
- 项目入口从页面中选择第一个非空 ProjectInfo，尚未支持多文档或自定义入口模板；
- 模块名解析默认对应项目根目录下的 `Module/Path.lean`，复杂 Lake workspace/`srcDir` 尚未完整支持；
- 未执行完整 JSON Schema Draft 2020-12 校验，当前使用核心字段与 proof 结构校验。

## 相关项目与文档

- [ProofScript](https://github.com/JokerXin2025/ProofScript)
- [ProofScript README](https://github.com/JokerXin2025/ProofScript/blob/main/README.md)
- [`Lean2TeX/README.md`](Lean2TeX/README.md)
- [`demo/README.md`](demo/README.md)
- [ProofScript JSON Schema 文档](https://github.com/JokerXin2025/ProofScript/tree/main/docs)

## License

本项目使用 Apache License 2.0，标准许可证全文见 [`LICENSE`](LICENSE)。
