module AnalysisBase where

open import AgdaAsciiPrelude.AsciiPrelude

variable
  l l' l1 l2 l3 : Level
  A B C : Set l

Commutativity : (A -> A -> A) -> Set _
Commutativity _op_ = forall x y -> x op y === y op x

Associativity : (A -> A -> A) -> Set _
Associativity _op_ = forall x y z -> (x op y) op z === x op (y op z)

NeutralElement : (A -> A -> A) -> A -> Set _
NeutralElement _op_ e = forall x -> e op x === x

Inverse : (A -> A -> A) -> (A -> A) -> A -> Set _
Inverse _op_ _^-1 one = forall x -> x op (x ^-1) === one

record Rationals (R : Set l) : Set l where
  field
    _+_ : R -> R -> R
    -_ : R -> R
    zero : R

    _*_ : R -> R -> R
    _^-1 : R -> R
    one : R
