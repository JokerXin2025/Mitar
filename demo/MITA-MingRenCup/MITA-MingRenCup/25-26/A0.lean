import «Calculus@Mitar»

lemma equation_1 : ∀ x > 0,
    (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)
    = (e ^ (e ^ x^2 - 1) - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)
:= by
  sorry

theorem MingRenCup_A₀ :
    lim₊ (fun x ↦ (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)) 0 = the (e^2)
:= by
  have h_ifs : isRightInfinitesimal (fun x ↦ e ^ x^2 - 1) 0 := by
    sorry -- apply FuncLimitExpr.toRight
    -- exact Eq.trans (Check_Continuous _ _) (by norm_num)
  calc
          lim₊ (fun x ↦ (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)) 0
       =  lim₊ (fun x ↦ (e ^ (e ^ x^2 - 1) - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
          := by lim_congr equation_1 within 1                   -- 同余代换（引理）
    _  =? lim₊ (fun x ↦ (e ^ x^2 - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
          := by lim_equiv                                       -- 等价无穷小代换
    _  =  lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / ((1 + x) ^ e⁻¹ - 1)) 0
          := by lim_congr_by_field                              -- 同余代换（域公理）
    _  =? lim₊ (fun x ↦ (e / x * (e ^ x^2 - 1)) / (e⁻¹ * x)) 0
          := sorry -- by lim_equiv                                       -- 等价无穷小代换
    _  =  lim₊ (fun x ↦ e^2 * ((e ^ x^2 - 1) / x^2)) 0
          := by lim_congr_by_field                              -- 同余代换（域公理）
    _  =? lim₊ (fun x ↦ e^2 * ((e ^ x - 1) / x)) 0
          := sorry -- FuncLimit_Comp? (by lim_simp)                      -- 化简（变量代换）
    _  =? lim₊ (fun _ ↦ e^2) 0 * lim₊ (fun x ↦ (e ^ x - 1) / x) 0
          := RightLimit_Mul?                                    -- 乘法法则
    _  =  the (e^2) * lim₊ (fun x ↦ (e ^ x - 1) / x) 0
          := by lim_simp                                        -- 化简（常数极限）
    _  =? the (e^2) * lim₊ (fun x ↦ x / x) 0
          := sorry                                     -- 等价无穷小代换
    _  =  the (e^2)
          := by lim_simp                                        -- 常规化简

-- Step 1: 同余代换（引理）
theorem step_1 :
    lim₊ (fun x ↦ (e ^ e ^ x^2 - e) / ((x ^ e + x ^ (e + 1)) ^ e⁻¹ - x)) 0
  = lim₊ (fun x ↦ (e ^ (e ^ x^2 - 1) - 1) / (x * ((1 + x) ^ e⁻¹ - 1) / e)) 0
:= by
  sorry
