
import Lean2TeX.Command

/-
  # Print const's definition in InfoView (Developer Tool)
  Usage: `#Lean2TeX_const ⟨const⟩`
--
  #
  Usage: `Lean2TeX ⟨box⟩ => "⟨file⟩.json"`
-/

import Lean2TeX.Tactic

/-
  # Record the step infomation
  Usage: `Lean2TeX_step ⟨box⟩ <- ⟨tactic⟩ {⟨arg⟩}* {| ⟨expression⟩}?`
--
  # Record the current proof state
  Usage: `Lean2TeX_state ⟨box⟩ <- goal {⟨args⟩}*`
-/
