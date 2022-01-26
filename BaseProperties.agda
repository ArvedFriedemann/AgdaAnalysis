module BaseProperties where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    l l' l1 l2 l3 : Level
    A B C : Set l

Commutativity : (A -> A -> A) -> Set _
Commutativity _op_ = forall x y -> x op y === y op x

Associativity : (A -> A -> A) -> Set _
Associativity _op_ = forall x y z -> (x op y) op z === x op (y op z)

LeftNeutralElement : (A -> A -> A) -> A -> Set _
LeftNeutralElement _op_ e = forall x -> e op x === x

RightNeutralElement : (A -> A -> A) -> A -> Set _
RightNeutralElement _op_ e = forall x -> x op e === x

RightInverse : (A -> A -> A) -> (A -> A) -> A -> Set _
RightInverse _op_ _^-1 one = forall x -> x op (x ^-1) === one

LeftInverse : (A -> A -> A) -> (A -> A) -> A -> Set _
LeftInverse _op_ _^-1 one = forall x -> (x ^-1) op x === one

Unique : (A -> Set l) -> Set _
Unique P = forall a b -> P a -> P b -> a === b

Injective : {A : Set l1} {B : Set l2}  -> (A -> B) -> Set (l1 ~U~ l2)
Injective f = forall x y -> f x === f y -> x === y

Surjective : {A : Set l1} {B : Set l2}  -> (A -> B) -> Set (l1 ~U~ l2)
Surjective f = forall b -> exists a st (f a === b)

Bijective : {A : Set l1} {B : Set l2}  -> (A -> B) -> Set (l1 ~U~ l2)
Bijective f = (Injective f) and (Surjective f)

record Bijection {A : Set l1} {B : Set l2} (f : A -> B) : Set (l1 ~U~ l2) where
  field
    rev : B -> A
    bij-prop-BAB : forall x -> (f o rev) x === x
    bij-prop-ABA : forall x -> (rev o f) x === x

data Fin {l : Level} : Nat -> Set l where
  zero-fin : {n : Nat} -> Fin {l} n
  succ-fin : {n : Nat} -> (f : Fin {l} n) -> Fin {l} (suc n)

toNat : {n : Nat} -> Fin {l} n -> Nat
toNat {n = n} _ = n

record Sized (A : Set l) : Set l where
  field
    size : Nat
    sized-bij-fkt : A -> Fin {l} size
    sized-bij : Bijection sized-bij-fkt

record _subtype_of_ (A B : Set l) (H : A -> Set l) : Set l where
  field
    to : (a : A) -> H a -> B
    from : B -> A
    preserves-H : forall b -> H (from b)
    subt-bij-BAB : forall a -> (h : H a) -> from (to a h) === a
    subt-bij-ABA : forall b -> to (from b) (preserves-H b) === b

_elem_ : {A : Set l} -> A -> (A -> Set l) -> Set l
x elem P = P x
