import ProofScript

set_option linter.defProp false

project_info {
  title := "Mitar 完整组件展示",
  authors := "Mitar Contributors",
  abstract := "一个由 ProofScript 编写并由 Mitar 生成的交互式形式化数学展示项目。",
  keywords := "Lean 4, ProofScript, Mitar, calculus, theorem dependencies",
  journal := "Mitar Demo Collection",
  year := "2026",
  license := "Apache-2.0"
}

namespace MitarDemo.Dependencies

@text r#"
= 高等数学定理依赖导航 <calculus-dependency-navigation>

本页用本科高等数学中的典型结果展示定理依赖导航。网络从数列与函数极限出发，经过连续、
微分中值定理、等价无穷小、洛必达法则和泰勒公式，最后连接定积分、反常积分与无穷级数。

为了让示例只关注依赖关系而不额外引入 Mathlib 的分析学体系，下面的 Lean 声明使用统一的
轻量命题接口；定理名称和 `apply_thm` 调用表达课程层面的直接依赖，而不是这些分析定理的
完整形式化陈述。
"#

@theorem @[theorem_info (name := "极限唯一性定理", label := "limit-uniqueness", tags := "calculus, limit, foundation")]
    limitUniqueness (P : Prop) (h : P) : P := script
  apply_h h

@theorem @[theorem_info (name := "极限的四则运算法则", label := "limit-arithmetic", tags := "calculus, limit")]
    limitArithmetic (P : Prop) (h : P) : P := script
  apply_thm limitUniqueness
  apply_h h

@theorem @[theorem_info (name := "夹逼定理", label := "squeeze-theorem", tags := "calculus, limit")]
    squeezeTheorem (P : Prop) (h : P) : P := script
  apply_thm limitUniqueness
  apply_h h

@theorem @[theorem_info (name := "第一个重要极限", label := "first-important-limit", tags := "calculus, limit")]
    firstImportantLimit (P : Prop) (h : P) : P := script
  apply_thm squeezeTheorem
  apply_h h

@theorem @[theorem_info (name := "第二个重要极限", label := "second-important-limit", tags := "calculus, limit")]
    secondImportantLimit (P : Prop) (h : P) : P := script
  apply_thm limitArithmetic
  apply_thm squeezeTheorem
  apply_h h

@theorem @[theorem_info (name := "连续函数的复合定理", label := "continuity-composition", tags := "calculus, continuity")]
    continuityComposition (P : Prop) (h : P) : P := script
  apply_thm limitArithmetic
  apply_h h

@theorem @[theorem_info (name := "基本等价无穷小公式", label := "equivalent-infinitesimals", tags := "calculus, infinitesimal")]
    equivalentInfinitesimals (P : Prop) (h : P) : P := script
  apply_thm firstImportantLimit
  apply_thm secondImportantLimit
  apply_h h

@theorem @[theorem_info (name := "等价无穷小代换定理", label := "equivalent-substitution", tags := "calculus, infinitesimal")]
    equivalentSubstitution (P : Prop) (h : P) : P := script
  apply_thm equivalentInfinitesimals
  apply_thm limitArithmetic
  apply_h h

@theorem @[theorem_info (name := "导数定义与可导必连续", label := "differentiability-continuity", tags := "calculus, derivative")]
    differentiabilityImpliesContinuity (P : Prop) (h : P) : P := script
  apply_thm limitArithmetic
  apply_thm continuityComposition
  apply_h h

@theorem @[theorem_info (name := "费马驻点定理", label := "fermat-theorem", tags := "calculus, derivative")]
    fermatTheorem (P : Prop) (h : P) : P := script
  apply_thm differentiabilityImpliesContinuity
  apply_h h

@theorem @[theorem_info (name := "罗尔中值定理", label := "rolle-theorem", tags := "calculus, mean-value")]
    rolleTheorem (P : Prop) (h : P) : P := script
  apply_thm fermatTheorem
  apply_thm continuityComposition
  apply_h h

@theorem @[theorem_info (name := "拉格朗日中值定理", label := "lagrange-mean-value", tags := "calculus, mean-value")]
    lagrangeMeanValueTheorem (P : Prop) (h : P) : P := script
  apply_thm rolleTheorem
  apply_h h

@theorem @[theorem_info (name := "柯西中值定理", label := "cauchy-mean-value", tags := "calculus, mean-value")]
    cauchyMeanValueTheorem (P : Prop) (h : P) : P := script
  apply_thm rolleTheorem
  apply_thm lagrangeMeanValueTheorem
  apply_h h

@theorem @[theorem_info (name := "洛必达法则", label := "lhopital-rule", tags := "calculus, limit, derivative")]
    lHopitalRule (P : Prop) (h : P) : P := script
  apply_thm cauchyMeanValueTheorem
  apply_thm equivalentSubstitution
  apply_h h

@theorem @[theorem_info (name := "函数单调性的导数判别法", label := "monotonicity-criterion", tags := "calculus, derivative, application")]
    monotonicityCriterion (P : Prop) (h : P) : P := script
  apply_thm lagrangeMeanValueTheorem
  apply_h h

@theorem @[theorem_info (name := "函数极值的充分条件", label := "extremum-criterion", tags := "calculus, derivative, application")]
    extremumCriterion (P : Prop) (h : P) : P := script
  apply_thm fermatTheorem
  apply_thm monotonicityCriterion
  apply_h h

@theorem @[theorem_info (name := "曲线凹凸性与拐点判别", label := "convexity-criterion", tags := "calculus, derivative, application")]
    convexityCriterion (P : Prop) (h : P) : P := script
  apply_thm monotonicityCriterion
  apply_thm differentiabilityImpliesContinuity
  apply_h h

@theorem @[theorem_info (name := "泰勒公式（皮亚诺余项）", label := "taylor-peano", tags := "calculus, taylor")]
    taylorFormulaPeano (P : Prop) (h : P) : P := script
  apply_thm equivalentInfinitesimals
  apply_thm differentiabilityImpliesContinuity
  apply_thm lagrangeMeanValueTheorem
  apply_h h

@theorem @[theorem_info (name := "泰勒公式（拉格朗日余项）", label := "taylor-lagrange", tags := "calculus, taylor")]
    taylorFormulaLagrange (P : Prop) (h : P) : P := script
  apply_thm taylorFormulaPeano
  apply_thm lagrangeMeanValueTheorem
  apply_h h

@theorem @[theorem_info (name := "泰勒展开求极限法", label := "taylor-limit-method", tags := "calculus, taylor, limit")]
    taylorLimitMethod (P : Prop) (h : P) : P := script
  apply_thm taylorFormulaPeano
  apply_thm equivalentSubstitution
  apply_thm lHopitalRule
  apply_h h

@theorem @[theorem_info (name := "微积分基本定理", label := "fundamental-calculus", tags := "calculus, integral")]
    fundamentalTheoremOfCalculus (P : Prop) (h : P) : P := script
  apply_thm continuityComposition
  apply_thm lagrangeMeanValueTheorem
  apply_h h

@theorem @[theorem_info (name := "牛顿—莱布尼茨公式", label := "newton-leibniz", tags := "calculus, integral")]
    newtonLeibnizFormula (P : Prop) (h : P) : P := script
  apply_thm fundamentalTheoremOfCalculus
  apply_h h

@theorem @[theorem_info (name := "定积分换元法", label := "integration-substitution", tags := "calculus, integral")]
    integrationBySubstitution (P : Prop) (h : P) : P := script
  apply_thm newtonLeibnizFormula
  apply_thm continuityComposition
  apply_h h

@theorem @[theorem_info (name := "定积分分部积分法", label := "integration-by-parts", tags := "calculus, integral")]
    integrationByParts (P : Prop) (h : P) : P := script
  apply_thm newtonLeibnizFormula
  apply_thm differentiabilityImpliesContinuity
  apply_h h

@theorem @[theorem_info (name := "反常积分比较判别法", label := "improper-integral-comparison", tags := "calculus, improper-integral")]
    improperIntegralComparison (P : Prop) (h : P) : P := script
  apply_thm squeezeTheorem
  apply_thm newtonLeibnizFormula
  apply_h h

@theorem @[theorem_info (name := "正项级数比较判别法", label := "series-comparison", tags := "calculus, series")]
    positiveSeriesComparison (P : Prop) (h : P) : P := script
  apply_thm squeezeTheorem
  apply_thm improperIntegralComparison
  apply_h h

@theorem @[theorem_info (name := "比值与根值判别法", label := "ratio-root-tests", tags := "calculus, series")]
    ratioAndRootTests (P : Prop) (h : P) : P := script
  apply_thm positiveSeriesComparison
  apply_thm secondImportantLimit
  apply_h h

@theorem @[theorem_info (name := "幂级数的逐项求导与积分", label := "power-series-operations", tags := "calculus, power-series")]
    powerSeriesOperations (P : Prop) (h : P) : P := script
  apply_thm ratioAndRootTests
  apply_thm fundamentalTheoremOfCalculus
  apply_thm taylorFormulaLagrange
  apply_h h

@theorem @[theorem_info (name := "函数的幂级数展开", label := "power-series-expansion", tags := "calculus, power-series, conclusion")]
    powerSeriesExpansion (P : Prop) (h : P) : P := script
  apply_thm powerSeriesOperations
  apply_thm taylorFormulaLagrange
  apply_thm taylorLimitMethod
  apply_h h

page_end

end MitarDemo.Dependencies
