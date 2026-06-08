import Lean2TeX.Basic

open Lean2TeX

def Rule_Mathbb_Nat : Rule := fun expr _ => do
  if expr.consumeMData.isConstOf ``Nat then
    return (s!"\\mathbb{"{"}N{"}"}", OperNode.Unit)
  return none

def Rule_Mathbf_Nat : Rule := fun expr _ => do
  if expr.consumeMData.isConstOf ``Nat then
    return (s!"\\mathbf{"{"}N{"}"}", OperNode.Unit)
  return none

def Rule_Mathbb_Real : Rule := fun expr _ => do
  if expr.consumeMData.isConstOf `Real then
    return (s!"\\mathbb{"{"}R{"}"}", OperNode.Unit)
  return none

def Rule_Mathbf_Real : Rule := fun expr _ => do
  if expr.consumeMData.isConstOf `Real then
    return (s!"\\mathbf{"{"}R{"}"}", OperNode.Unit)
  return none
