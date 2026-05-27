/- # Import Lean2TeX commands -/

import Lean2TeX.Command

/-
  __* Print const's definition in InfoView (Developer Tool) *__
  Usage: `#Lean2TeX_const ⟨const⟩`
-/
/-
  __*  *__
  Usage: `Lean2TeX ⟨box⟩ => "⟨file⟩.json"`
-/


/- # Import Lean2TeX tactics -/

import Lean2TeX.Tactic

/-
  __*  *__
  Usage: `Lean2TeX_step ⟨box⟩ <- ⟨tactic⟩ {⟨arg⟩}* {| ⟨expression⟩}?`
-/
/-
  __*  *__
  Usage: `Lean2TeX_record ⟨box⟩ <- goal {⟨args⟩}*`
-/
