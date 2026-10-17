import ProofScript

project_info {
  title := "Mitar 完整组件展示",
  authors := "Mitar Contributors",
  abstract := "一个由 ProofScript 编写并由 Mitar 生成的交互式形式化数学展示项目。",
  keywords := "Lean 4, ProofScript, Mitar, formal mathematics",
  journal := "Mitar Demo Collection",
  year := "2026",
  url := "https://github.com/JokerXin2025/Mitar",
  license := "Apache-2.0",
  note := "此页面同时作为跨模块参考文献的来源。"
}

namespace MitarDemo.Library

@text r#"
= 参考定理库 <library>

本模块提供主展示页面所引用的基础结果。定理元数据会跨模块保存在环境中，
当另一个 `@theorem` 使用这些结果时，ProofScript 会自动把它们加入参考文献暂存区。
"#

@theorem @[theorem_info (
    name := "合取左投影",
    label := "and-left",
    tags := "logic, projection",
    note := "从合取命题中取得左侧结论"
  )] andLeft (P Q : Prop) (h : P ∧ Q) : P := script
  cause "h.left"

@text r#"
上面的证明展示了一个最小但完整的 theorem component。主页面会引用
@thm:and-left，并在参考文献板块中链接回本页。
"#

page_end

end MitarDemo.Library
