/- # Import Lean2TeX commands -/

import Lean2TeX.Command

/-
  __* Print const's definition in InfoView (Developer Tool) *__
  Usage: `#Lean2TeX_const ⟨const⟩`
--
  __*  *__
  Usage: `Lean2TeX ⟨box⟩ => "⟨file⟩.json"`
-/


/- # Import Lean2TeX tactics -/

import Lean2TeX.Tactic

/-
  __* Record the step infomation *__
  Usage: `Lean2TeX_step ⟨box⟩ <- ⟨tactic⟩ {⟨arg⟩}* {| ⟨expression⟩}?`
--
  __* Record the current proof state *__
  Usage: `Lean2TeX_state ⟨box⟩ <- goal {⟨args⟩}*`
-/
