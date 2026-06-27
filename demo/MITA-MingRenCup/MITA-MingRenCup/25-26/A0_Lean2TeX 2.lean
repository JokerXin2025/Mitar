import Lean2TeX
import «Calculus@Mitar»

def equation_1 : ∀ x > 0,
    (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)
    = (e ^ (e ^ x^2 - 1) - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)
:= by
  Lean2TeX equation_1 <- _goal_
  Lean2TeX equation_1 <- "sorry"
  sorry

def MingRenCup_A₀ :
    lim₊ (fun x ↦ (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)) 0 = the (e^2)
:= by
  Lean2TeX MingRenCup_A₀ <- _goal_
  have h_ifs : isRightInfinitesimal (fun x ↦ e ^ x^2 - 1) 0 := by
    Lean2TeX _proof <- _goal_
    Lean2TeX _proof <- "apply"
    apply FuncLimitExpr.toRight
    Lean2TeX _proof <- _goal_
    Lean2TeX _proof <- "exact"
    Lean2TeX MingRenCup_A₀ <- "have" &_proof("proof")
    exact Eq.trans (Check_Continuous _ _) (by norm_num)
  Lean2TeX MingRenCup_A₀ <- _goal_
  Lean2TeX MingRenCup_A₀ <- "calc" &_calc_("calc_steps")
  calc
        lim₊ (fun x ↦ (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)) 0
     =  lim₊ (fun x ↦ (e ^ (e ^ x^2 - 1) - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
          := by lim_congr equation_1 within 1                   -- 同余代换（引理）
  _  =? lim₊ (fun x ↦ (e ^ x^2 - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
          := by lim_equiv                                       -- 等价无穷小代换
  _  =  lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / ((1 + x) ^ e⁻¹ - 1)) 0
          := by lim_congr_by_field                              -- 同余代换（域公理）
  _  =? lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / (e⁻¹ * x)) 0
          := by lim_equiv                                       -- 等价无穷小代换
  _  =  lim₊ (fun x ↦ e^2 * ((e ^ x^2 - 1) / x^2)) 0
          := by lim_congr_by_field                              -- 同余代换（域公理）
  _  =? lim₊ (fun x ↦ e^2 * ((e ^ x - 1) / x)) 0
          := FuncLimit_Comp? (by lim_simp)                      -- 化简（变量代换）
  _  =? lim₊ (fun _ ↦ e^2) 0 * lim₊ (fun x ↦ (e ^ x - 1) / x) 0
          := RightLimit_Mul? _ _ _                              -- 乘法法则
  _  =  the (e^2) * lim₊ (fun x ↦ (e ^ x - 1) / x) 0
          := by lim_simp                                        -- 化简（常数极限）
  _  =? the (e^2) * lim₊ (fun x ↦ x / x) 0
          := sorry                                     -- 等价无穷小代换
  _  =  the (e^2)
          := by lim_simp                                        -- 常规化简

-- Step 1: 同余代换（引理）
def step_1 :
    lim₊ (fun x ↦ (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)) 0
  = lim₊ (fun x ↦ (e ^ (e ^ x^2 - 1) - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
:= by lim_congr equation_1 within 1

-- Step 2: 等价无穷小代换
def step_2 :
    lim₊ (fun x ↦ (e ^ (e ^ x^2 - 1) - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
  =? lim₊ (fun x ↦ (e ^ x^2 - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
:= by
  Lean2TeX step_2 <- _goal_
  have h_ifs : isRightInfinitesimal (fun x ↦ e ^ x^2 - 1) 0 := by
    Lean2TeX _proof <- _goal_
    Lean2TeX _proof <- "apply"
    apply FuncLimitExpr.toRight
    Lean2TeX _proof <- _goal_
    Lean2TeX _proof <- "exact"
    Lean2TeX step_2 <- "have" &_proof("proof")
    exact Eq.trans (Check_Continuous _ _) (by norm_num)
  lim_equiv

-- Step 3: 同余代换（域公理）
def step_3 :
    lim₊ (fun x ↦ (e ^ x^2 - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
  = lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / ((1 + x) ^ e⁻¹ - 1)) 0
:= by lim_congr_by_field

-- Step 4: 等价无穷小代换
def step_4 :
    lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / ((1 + x) ^ e⁻¹ - 1)) 0
  =? lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / (e⁻¹ * x)) 0
:= by lim_equiv

-- Step 5: 同余代换（域公理）
def step_5 :
    lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / (e⁻¹ * x)) 0
  = lim₊ (fun x ↦ e^2 * ((e ^ x^2 - 1) / x^2)) 0
:= by lim_congr_by_field

-- Step 6: 化简（变量代换）
def step_6 :
    lim₊ (fun x ↦ e^2 * ((e ^ x^2 - 1) / x^2)) 0
  =? lim₊ (fun x ↦ e^2 * ((e ^ x - 1) / x)) 0
:= FuncLimit_Comp? (by lim_simp)
-- Step 7: 乘法法则
theorem step_7 :
    lim₊ (fun x ↦ e^2 * ((e ^ x - 1) / x)) 0
  =? lim₊ (fun _ ↦ e^2) 0 * lim₊ (fun x ↦ (e ^ x - 1) / x) 0
:= RightLimit_Mul? _ _ _
-- Step 8: 化简（常数极限）
theorem step_8 :
    lim₊ (fun _ ↦ e^2) 0 * lim₊ (fun x ↦ (e ^ x - 1) / x) 0
  = the (e^2) * lim₊ (fun x ↦ (e ^ x - 1) / x) 0
:= by lim_simp

-- Step 9: 等价无穷小代换
def step_9 :
    the (e^2) * lim₊ (fun x ↦ (e ^ x - 1) / x) 0
  =? the (e^2) * lim₊ (fun x ↦ x / x) 0
:= by
  Lean2TeX step_9 <- _goal_
  have h_ifs : isRightInfinitesimal (fun x ↦ x) 0 := FuncLimitExpr.toRight x_isContinuous
  Lean2TeX step_9 <- "have" h_ifs("prop")
  Lean2TeX step_9 <- _goal_
  Lean2TeX step_9 <- "sorry"
  sorry
  -- lim_equiv

-- Step 10: 常规化简
def step_10 :
    the (e^2) * lim₊ (fun x ↦ x / x) 0
  = the (e^2)
:= by
  Lean2TeX step_10 <- _goal_
  Lean2TeX step_10 <- "lim_simp"
  Lean2TeX vals Lean2TeX_Data <- &equation_1 &MingRenCup_A₀ &step_1 &step_2 &step_3 &step_4 &step_5 &step_6 &step_9 &step_10
  lim_simp

Lean2TeX Lean2TeX_Data => "MITA-MingRenCup/25-26/A0_Lean2TeX.json"

-- Lean2TeX 1782122358.0985038
