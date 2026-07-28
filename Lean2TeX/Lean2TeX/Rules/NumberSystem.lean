import Lean2TeX.Prelude

open Lean2TeX


def Rule_Mathbb_Nat : Rule := fun expr _ _ _ => do
  if expr.isConstOf ``Nat then
    return (s!"\\mathbb{"{"}N{"}"}", NodeType.Unit)
  return none

def Rule_Mathbf_Nat : Rule := fun expr _ _ _ => do
  if expr.isConstOf ``Nat then
    return (s!"\\mathbf{"{"}N{"}"}", NodeType.Unit)
  return none

def Rule_Mathbb_Real : Rule := fun expr _ _ _ => do
  if expr.isConstOf `Real then
    return (s!"\\mathbb{"{"}R{"}"}", NodeType.Unit)
  return none

def Rule_Mathbf_Real : Rule := fun expr _ _ _ => do
  if expr.isConstOf `Real then
    return (s!"\\mathbf{"{"}R{"}"}", NodeType.Unit)
  return none
