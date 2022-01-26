module Group where

open import AgdaAsciiPrelude.AsciiPrelude renaming (_*_ to _*-nat_)
open import BaseProperties

open import Data.Integer hiding (suc) renaming (ℤ to Zet; _+_ to _+z_; _*_ to _*z_)
open import Data.Integer hiding (ℤ; _+_; _*_; suc)

private
  variable
    l l' l1 l2 l3 : Level
    A B C : Set l


record GroupProp (A : Set l) (e : A) (_^-1 : A -> A) (_*_ : A -> A -> A) : Set l where
  field
    group-assoc : Associativity (_*_)
    group-left-neut : LeftNeutralElement (_*_) e
    group-left-inv : LeftInverse (_*_) (_^-1) e

  unique-left-e : Unique (LeftNeutralElement (_*_))
  unique-left-e = {!!}

  unique-right-e : Unique (RightNeutralElement (_*_))
  unique-right-e = {!!}

  group-right-neut : RightNeutralElement (_*_) e
  group-right-neut = {!!}

  group-right-inv : RightInverse (_*_) (_^-1) e
  group-right-inv = {!!}

  left-inverse-unique : forall x y -> x * y === e -> y === x ^-1
  left-inverse-unique = {!!}

  right-inverse-unique : forall x y -> x * y === e -> x === y ^-1
  right-inverse-unique = {!!}

  double-inv : forall x -> (x ^-1) ^-1 === x
  double-inv = {!!}

  cong-inv : forall a b -> (a * b) ^-1 === (a ^-1) * (b ^-1)
  cong-inv = {!!}

  cancel-left : forall a b b' -> a * b === a * b' -> b === b'
  cancel-left = {!!}

  cancel-right : forall a b b' -> b * a === b' * a -> b === b'
  cancel-right = {!!}

record Group (A : Set l) : Set l where
  field
    _*_ : A -> A -> A
    _^-1 : A -> A
    e : A
    group-props : GroupProp A e (_^-1) (_*_)
  open GroupProp group-props public

  _pow-1_ : A -> Nat -> A
  _ pow-1 zero = e
  x pow-1 (suc n) = (x ^-1) * (x pow-1 n)

  _pow_ : A -> Zet -> A
  _ pow +0 = e
  x pow (+[1+ n ]) = x * (x pow (+ n))
  x pow (-[1+ n ]) = x pow-1 (suc n)


record FiniteGroup (A : Set l) : Set l where
  field
    group-finite : Group A
    finA : Sized A
  open Group group-finite public

module GroupOps where
  I_I : FiniteGroup A -> Nat
  I g I = size
    where
      open FiniteGroup g
      open Sized finA


record AbelianGroup (A : Set l) : Set l where
  field
    group-abel : Group A
  open Group group-abel public
  field
    group-comm : Commutativity (_*_)


record Subgroup {A : Set l} (G : Group A) (H : A -> Set l) : Set l where
  open Group G public
  field
    sg-nonempty : exists a st H a
    sg-op-preserve : forall a b -> H (a * b)
    sg-inv-preserve : forall a -> H (a ^-1)


subgroup-preserve-group-2-1-15 : {A B : Set l} {G : Group A} {H : A -> Set l}  ->
  A subtype B of H -> Subgroup G H -> Group B
subgroup-preserve-group-2-1-15 = {!!}

module 2-1-16 {A : Set l} {G : Group A} {H : A -> Set l}  where
  open Group G
  2-1-16a : Subgroup G H -> forall a b -> H ((a * b) ^-1)
  2-1-16a = {!!}
  2-1-16b : forall a b -> H ((a * b) ^-1) -> Subgroup G H
  2-1-16b = {!!}


record CyclicGroupProp {A : Set l} (G : Group A) : Set l where
  open Group G
  field
    g : A
    cyc-prop : forall (x : A) -> exists n st (g pow n === x)

<[_]>_ : {A : Set l} -> A -> Group A -> A -> Set l
<[_]>_ {A = A} g G x = exists n st (g pow n === x)
  where
    open Group G
