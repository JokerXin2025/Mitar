import Lean2TeX.Attributes
import Lean2TeX.Core


attribute [Lean2TeX_unwrap 1] OfNat.ofNat
attribute [Lean2TeX_unwrap 2] Nat.cast
attribute [Lean2TeX_unwrap 2] Int.cast

attribute [Lean2TeX "矛盾" Text] False
attribute [Lean2TeX "矛盾" Text (target_display := Word)] False

attribute [Lean2TeX "@1且@2" Text any any] And
attribute [Lean2TeX "@1且@2" Text any any (target_display := Word)] And

attribute [Lean2TeX "@1或@2" Text any any] Or
attribute [Lean2TeX "@1或@2" Text any any (target_display := Word)] Or

attribute [Lean2TeX "@1当且仅当@2" Text any any] Iff
attribute [Lean2TeX "@1当且仅当@2" Text any any (target_display := Word)] Iff

attribute [Lean2TeX "@1+1" Add left] Nat.succ
attribute [Lean2TeX "@5+@6" Add any any any any left right] HAdd.hAdd
attribute [Lean2TeX "@5-@6" Add any any any any left right] HSub.hSub
attribute [Lean2TeX "@5\\cdot @6" Mul any any any any left right] HMul.hMul
attribute [Lean2TeX "\\frac{@5}{@6}" Frac any any any any numerator denominator] HDiv.hDiv
attribute [Lean2TeX "@5^{@6}" Supscript any any any any base script] HPow.hPow
attribute [Lean2TeX "-@3" Minus any any only] Neg.neg
attribute [Lean2TeX "@3^{-1}" Supscript any any base] Inv.inv

attribute [Lean2TeX "@2=@3" Rel any left right] Eq
attribute [Lean2TeX "@2\\ne @3" Rel any left right] Ne
attribute [Lean2TeX "@3<@4" Rel any any left right] LT.lt
attribute [Lean2TeX "@3\\leqslant @4" Rel any any left right] LE.le
attribute [Lean2TeX "@3>@4" Rel any any left right] GT.gt
attribute [Lean2TeX "@3\\geqslant @4" Rel any any left right] GE.ge

attribute [Lean2TeX "\\mathbb{N}" Unit] Nat
attribute [Lean2TeX "\\mathbb{N}" Unit (target_display := Mathbb)] Nat
attribute [Lean2TeX "\\mathbf{N}" Unit (target_display := Mathbf)] Nat
