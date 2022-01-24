module Group where

open import AgdaAsciiPrelude.AsciiPrelude renaming (_*_ to _*-nat_)
open import BaseProperties

private
  variable
    l l' l1 l2 l3 : Level
    A B C : Set l


record GroupProp (A : Set l) (e : A) (_^-1 : A -> A) (_*_ : A -> A -> A) : Set l where
  field
    group-assoc : Associativity (_*_)
    group-ex-neut : NeutralElement (_*_) e
    group-inv : Inverse (_*_) (_^-1) e

open GroupProp {{...}}

record Group (A : Set l) : Set l where
  field
    _*_ : A -> A -> A
    _^-1 : A -> A
    e : A
    {{group-props}} : GroupProp A e (_^-1) (_*_)

open Group {{...}}

record AbelianGroup (A : Set l) : Set l where
  field
    {{abel-group}} : Group A
    group-comm : Commutativity (_*_)

commut-neut : {{_ : Group A}} -> (x : A) -> x * e === x
commut-neut x = {!!}

unique-neut : {{_ : Group A}} -> (e' : A) -> NeutralElement (_*_) e' -> e' === e
unique-neut e' neut-prop with eq1 <- neut-prop e | eq2 <- group-ex-neut e' = {!  !}
