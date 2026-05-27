import Lean2TeX.Basic

def Rule_Mathbb_Nat : Rule := fun expr _ => do
  if expr.isConstOf ``Nat then
    return s!"\\mathbb{"{"}N{"}"}"
  return none

def Rule_Mathbf_Nat : Rule := fun expr _ => do
  if expr.isConstOf ``Nat then
    return s!"\\mathbf{"{"}N{"}"}"
  return none

def Rule_Mathbb_Real : Rule := fun expr _ => do
  if expr.isConstOf ``Real then
    return s!"\\mathbb{"{"}N{"}"}"
  return none

def Rule_Mathbf_Real : Rule := fun expr _ => do
  if expr.isConstOf ``Real then
    return s!"\\mathbf{"{"}N{"}"}"
  return none
