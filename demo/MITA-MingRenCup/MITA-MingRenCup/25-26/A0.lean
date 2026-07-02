import «Calculus@JokerXin»

example : D (exp + sin) 2 = the (exp 2 + cos 2) := by
  deriv


lemma equation_1 : ∀ x > 0,
    (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)
    = (e ^ (e ^ x^2 - 1) - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)
:= by
  sorry

theorem MingRenCup_A₀ :
    lim₊ (fun x ↦ (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)) 0 = the (e^2)
:= by
  have h_ifs : isRightInfinitesimal (fun x ↦ e ^ x^2 - 1) 0 := by
    sorry -- exact Eq.trans (Check_Continuous _ _) (by norm_num)
  calc
          lim₊ (fun x ↦ (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)) 0
       =  lim₊ (fun x ↦ (e ^ (e ^ x^2 - 1) - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
          := by sorry -- lim_congr equation_1 within 1                   -- 同余代换（引理）
    _  =? lim₊ (fun x ↦ (e ^ x^2 - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
          := by lim_equiv                                       -- 等价无穷小代换
    _  =  lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / ((1 + x) ^ e⁻¹ - 1)) 0
          := by sorry -- lim_congr_by_field                              -- 同余代换（域公理）
    _  =? lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / (e⁻¹ * x)) 0
          := sorry -- by lim_equiv                                       -- 等价无穷小代换
    _  =  lim₊ (fun x ↦ e^2 * ((e ^ x^2 - 1) / x^2)) 0
          := by sorry -- lim_congr_by_field                              -- 同余代换（域公理）
    _  =? lim₊ (fun x ↦ e^2 * ((e ^ x - 1) / x)) 0
          := sorry -- FuncLimit_Comp? (by lim_simp)                      -- 化简（变量代换）
    _  =? lim₊ (fun _ ↦ e^2) 0 * lim₊ (fun x ↦ (e ^ x - 1) / x) 0
          := RightLimitExpr.Mul                                 -- 乘法法则
    _  =  the (e^2) * lim₊ (fun x ↦ (e ^ x - 1) / x) 0
          := by sorry -- lim_simp                                        -- 化简（常数极限）
    _  =? the (e^2) * lim₊ (fun x ↦ x / x) 0
          := sorry                                     -- 等价无穷小代换
    _  =  the (e^2)
          := by lim_simp                                        -- 常规化简

-- Step 1: 同余代换（引理）
theorem step_1 :
    lim₊ (fun x ↦ (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)) 0
  = lim₊ (fun x ↦ (e ^ (e ^ x^2 - 1) - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
:= by
  lim_congr equation_1 within 1

-- Step 2: 等价无穷小代换
theorem step_2 :
    lim₊ (fun x ↦ (e ^ (e ^ x^2 - 1) - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
  =? lim₊ (fun x ↦ (e ^ x^2 - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
:= by
  have h_ifs : isRightInfinitesimal (fun x ↦ e ^ x^2 - 1) 0 := by
    apply FuncLimitExpr.toRight
    exact Eq.trans (Check_Continuous _ _) (by norm_num)
  lim_equiv

-- Step 3: 同余代换（域公理）
theorem step_3 :
    lim₊ (fun x ↦ (e ^ x^2 - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
  = lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / ((1 + x) ^ e⁻¹ - 1)) 0
:= by
  lim_congr_by_field

-- Step 4: 等价无穷小代换
theorem step_4 :
    lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / ((1 + x) ^ e⁻¹ - 1)) 0
  =? lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / (e⁻¹ * x)) 0
:= by
  lim_equiv

-- Step 5: 同余代换（域公理）
theorem step_5 :
    lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / (e⁻¹ * x)) 0
  = lim₊ (fun x ↦ e^2 * ((e ^ x^2 - 1) / x^2)) 0
:= by
  lim_congr_by_field

-- Step 6: 化简（变量代换）
theorem step_6 :
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
:= by
  lim_simp

-- Step 9: 等价无穷小代换
theorem step_9 :
    the (e^2) * lim₊ (fun x ↦ (e ^ x - 1) / x) 0
  =? the (e^2) * lim₊ (fun x ↦ x / x) 0
:= by
  have h_ifs : isRightInfinitesimal (fun x ↦ x) 0 := FuncLimitExpr.toRight x_isContinuous
  sorry
  -- lim_equiv

-- Step 10: 常规化简
theorem step_10 :
    the (e^2) * lim₊ (fun x ↦ x / x) 0
  = the (e^2)
:= by
  lim_simp
