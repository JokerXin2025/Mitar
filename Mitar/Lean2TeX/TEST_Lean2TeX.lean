import Lean2TeX
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.tactic.Ring.RingNF

def a : ℕ → ℤ
  | 0 => 2
  | n + 1 => a n * (a n - 1) + 1

def Lemma1 (n : ℕ) : a n ≥ 2 := by
  Lean2TeX Lemma1 <- _goal_
  Lean2TeX _info <- n ("on")
  induction n with
  | zero =>
    Lean2TeX _base <- _goal_
    Lean2TeX _base <- "rfl"
    rfl
  | succ k ih =>
    Lean2TeX _induct <- _goal_ k("assume_on") ih("assume_h")
    Lean2TeX _induct <- "unfold" a("concept")
    unfold a
    Lean2TeX _induct <- _goal_
    let _lhs_ := 2
    let _rhs1_ := 2 * 1
    Lean2TeX _calc_ <- "$=$" _lhs_("lhs") _rhs1_("rhs")
    let _rhs2_ := a k * (a k - 1)
    Lean2TeX _calc_ <- "$\\leqslant$" _rhs2_("rhs")
    let _rhs3_ := a k * (a k - 1) + 1
    Lean2TeX _calc_ <- "$\\leqslant$" _rhs3_("rhs")
    Lean2TeX _induct <- "calc" &_calc_("calc_steps")
    Lean2TeX Lemma1 <- "Induction" *_info("info") &_base("base") &_induct("inductive")
    calc
      2 = 2 * 1 := by
        rfl
      _ ≤ a k * (a k - 1) :=
        mul_le_mul ih (by omega) (by decide) (by omega)
      _ ≤ a k * (a k - 1) + 1 := by
        omega
def Theorem (n : ℕ) : ¬ ∃ m : ℕ, a n = m ^ 2 := by
  Lean2TeX Theorem <- _goal_
  intro h_intro
  Lean2TeX _info <- h_intro("h_contra")
  Lean2TeX _proof <- _goal_
  obtain ⟨m, h_m⟩ := h_intro
  Lean2TeX _proof <- "obtain" m h_m
  Lean2TeX _proof <- _goal_
  Lean2TeX __info <- n("NaturalNumber")
  cases n with
  | zero =>
    Lean2TeX __zero <- _goal_
    Lean2TeX __zero <- "unfold" a("concept") h_m("at")
    unfold a at h_m
    Lean2TeX __zero <- _goal_ h_m("last_at")
    have h_cases : m = 0 ∨ m = 1 ∨ m ≥ 2 := by omega
    Lean2TeX __zero <- _goal_
    Lean2TeX ___info <- h_cases("principle")
    rcases h_cases with rfl | rfl | _
    · Lean2TeX ___case1 <- _goal_
      Lean2TeX ___case1 <- "norm_num" h_m("h")
      norm_num at h_m
    · Lean2TeX ___case2 <- _goal_
      Lean2TeX ___case2 <- "norm_num" h_m("h")
      norm_num at h_m
    · have : (m : ℤ) ^ 2 ≥ 4 := by
        Lean2TeX ___case3 <- _goal_
        Lean2TeX ___case3 <- "norm_cast"
        norm_cast
        Lean2TeX ___case3 <- _goal_
        Lean2TeX ___case3 <- "change"
        change m ^ 2 ≥ 2 ^ 2
        Lean2TeX ___case3 <- _goal_
        Lean2TeX ___case3 <- "gcongr"
        gcongr
      Lean2TeX ___case3 <- _goal_
      Lean2TeX ___case3 <- "omega"
      Lean2TeX vals ___cases <- &___case1 &___case2 &___case3
      Lean2TeX __zero <- "Cases" *___info("info") &___cases("cases")
      omega
  | succ k =>
    Lean2TeX __succ <- _goal_ k("n-1")
    Lean2TeX __succ <- "unfold" a("concept") h_m("at")
    unfold a at h_m
    Lean2TeX __succ <- _goal_ h_m("last_at")
    have h_ak_geq_2 := Lemma1 k
    let A := 2 * (m : ℤ) - 2 * a k + 1
    let B := 2 * (m : ℤ) + 2 * a k - 1
    have h_factor : A * B = 3 := by
      Lean2TeX ___proof <- _goal_
      let _lhs_ := A * B
      let _rhs1_ := 4 * (m : ℤ) ^ 2 - (2 * a k - 1) ^ 2
      Lean2TeX _calc_ <- "$=$" _lhs_("lhs") _rhs1_("rhs")
      let _rhs2_ := 4 * (a k * (a k - 1) + 1) - (2 * a k - 1) ^ 2
      Lean2TeX _calc_ <- "$=$" _rhs2_("rhs")
      let _rhs3_ := 3
      Lean2TeX _calc_ <- "$=$" _rhs3_("rhs")
      Lean2TeX ___proof <- "calc" &_calc_("calc_steps")
      Lean2TeX __succ <- "have" &___proof("proof")
      calc
        A * B = 4 * (m : ℤ) ^ 2 - (2 * a k - 1) ^ 2 := by
          ring
        _     = 4 * (a k * (a k - 1) + 1) - (2 * a k - 1) ^ 2 := by
          rw [h_m]
        _     = 3 := by
          ring
    Lean2TeX __succ <- _goal_
    have h_A_geq_1 : A ≥ 1 := by
      Lean2TeX ___proof <- _goal_
      by_contra h_A_l_1
      Lean2TeX ____info <- h_A_l_1("h_contra")
      Lean2TeX ____proof <- _goal_
      have h_AB_leq_0 : A * B ≤ 0 := by nlinarith
      Lean2TeX ____proof <- _goal_
      Lean2TeX ____proof <- "linarith"
      Lean2TeX ___proof <- "Contradiction" *____info("info") &____proof("proof")
      Lean2TeX __succ <- "have" &___proof("proof")
      linarith
    Lean2TeX __succ <- _goal_
    have h_A_eq_1 : A = 1 := le_antisymm h_A_leq_1 h_A_geq_1
    Lean2TeX __succ <- "have_term" h_A_eq_1("prop")
    Lean2TeX __succ <- _goal_
    Lean2TeX __succ <- "omega"
    Lean2TeX vals __cases <- &__zero &__succ
    Lean2TeX _proof <- "Cases" *__info("info") &__cases("cases")
    Lean2TeX Theorem <- "Contradiction" *_info("info") &_proof("proof")
    Lean2TeX vals TEST <- &Lemma1 &Theorem
    omega

Lean2TeX TEST => "/Users/zhoukexin/Desktop/Mitar/Mitar/Lean2TeX/TEST.json"

-- Lean2TeX 1781051577.415901
