import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.tactic.Ring.RingNF
import Lean2TeX

-- Load Mathlib tactic configs (nlinarith, linarith, ring, norm_cast, ...)
-- so the text-level matcher can instrument them.
#load_tactics "/Users/zhoukexin/Mitar/Lean2TeX/Lean2TeX/tactics_mathlib.json"

-- The `#Lean2TeX` pipeline re-elaborates the proof text, so the `unusedTactic`
-- linter (Mathlib, on by default) sees the `Lean2TeX` recorders (pure side
-- effects that never change the goal) as "does nothing", and the
-- `unreachableTactic` linter (Lean core) sees the original tactic sequence as
-- "never executed" (it is only used as the text-level blueprint).  Both are
-- harmless; disable them for this file.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def a : ℕ → ℤ
  | 0 => 2
  | n + 1 => a n * (a n - 1) + 1

lemma Lemma1 (n : ℕ) : a n ≥ 2 := by
  induction n with
  | zero =>
    rfl
  | succ k ih =>
    unfold a
    calc
      2 = 2 * 1 := by
        rfl
      _ ≤ a k * (a k - 1) :=
        mul_le_mul ih (by omega) (by decide) (by omega)
      _ ≤ a k * (a k - 1) + 1 := by
        omega

#Lean2TeX theorem Theorem (n : ℕ) : ¬ ∃ m : ℕ, a n = m ^ 2 := by
  intro h_intro
  obtain ⟨m, h_m⟩ := h_intro
  cases n with
  | zero =>
    unfold a at h_m
    have h_cases : m = 0 ∨ m = 1 ∨ m ≥ 2 := by
      omega
    rcases h_cases with rfl | rfl | _
    · norm_num at h_m
    · norm_num at h_m
    · have : (m : ℤ) ^ 2 ≥ 4 := by
        norm_cast
        change m ^ 2 ≥ 2 ^ 2
        gcongr
      omega
  | succ k =>
    unfold a at h_m
    have h_ak_geq_2 := Lemma1 k
    let A := 2 * (m : ℤ) - 2 * a k + 1
    let B := 2 * (m : ℤ) + 2 * a k - 1
    have h_factor : A * B = 3 := by
      calc
        A * B = 4 * (m : ℤ) ^ 2 - (2 * a k - 1) ^ 2 := by
          ring
        _     = 4 * (a k * (a k - 1) + 1) - (2 * a k - 1) ^ 2 := by
          rw [h_m]
        _     = 3 := by
          ring
    have h_B_geq_3 : B ≥ 3 := by
      omega
    have h_A_geq_1 : A ≥ 1 := by
      by_contra h_A_l_1
      have h_AB_leq_0 : A * B ≤ 0 := by
        nlinarith
      linarith
    have h_A_leq_1 : A ≤ 1 := by
      by_contra h_A_g_1
      have h_AB_geq_6 : A * B ≥ 6 := by
        nlinarith
      linarith
    have h_A_eq_1 : A = 1 := le_antisymm h_A_leq_1 h_A_geq_1
    have h_B_eq_3 : B = 3 := by
      calc
        B = 1 * B := by
          ring
        _ = A * B := by
          rw [h_A_eq_1]
        _ = 3 :=
          h_factor
    omega
