module TT2 where

record _×_ (A B : Set) : Set where
  field
    proj₁ : A
    proj₂ : B

open _×_

_,_ : {A B : Set} -> A -> B -> A × B
a , b = record { proj₁ = a ; proj₂ = b }

swap : {A B : Set} -> A × B -> B × A
swap record { proj₁ = proj₁ ; proj₂ = proj₂ } = proj₂ , proj₁

curry : {A B C : Set} -> (A × B -> C) -> A -> B -> C
curry f = λ { x y →  f (x , y) }

uncurry : {A B C : Set} -> (A -> B -> C) -> A × B -> C
uncurry f = λ { record { proj₁ = p₁ ; proj₂ = p₂ } →  f p₁ p₂ }

data _⨄_ (A B : Set) : Set where
  inj₁ : A -> A ⨄ B
  inj₂ : B -> A ⨄ B

prop = Set

infix 3 _∧_
_∧_ : prop -> prop -> prop
_∧_ = _×_

infix 2 _∨_
_∨_ : prop -> prop -> prop
_∨_ = _⨄_

infix 1 _⇒_
_⇒_ : prop -> prop -> prop
P ⇒ Q = P -> Q

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

True : prop
True = ⊤

False : prop
False = ⊥

¬ : prop -> prop
¬ P = P -> ⊥

infix 0 _⇔_
_⇔_ : prop -> prop -> prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

deMorgan : {P Q : prop} -> ¬ (P ∨ Q) ⇔ (¬ P ∧ ¬ Q)
proj₁ (proj₁ deMorgan x) x₁ = x (inj₁ x₁)
proj₂ (proj₁ deMorgan x) x₁ = x (inj₂ x₁)
_×_.proj₂ deMorgan record { proj₁ = proj₁ ; proj₂ = proj₂ } (inj₁ x₁) = proj₁ x₁
_×_.proj₂ deMorgan record { proj₁ = proj₁ ; proj₂ = proj₂ } (inj₂ x₁) = proj₂ x₁

deMorgan' : {P Q : prop} -> ¬ (P ∧ Q) ⇔ (¬ P ∨ ¬ Q)
proj₁ deMorgan' x = {! !} -- Not Provable!
_×_.proj₂ deMorgan' (inj₁ x) record { proj₁ = proj₁ ; proj₂ = proj₂ } = x proj₁
_×_.proj₂ deMorgan' (inj₂ x) record { proj₁ = proj₁ ; proj₂ = proj₂ } = x proj₂

TMD : prop -> prop
TMD P = P ∨ ¬ P

deMorgan'' : {P Q : prop} -> TMD P -> ¬ (P ∧ Q) ⇔ ((¬ P) ∨ (¬ Q))
proj₁ (deMorgan'' (inj₁ x₁)) x = let lemma = curry x in inj₂ (lemma x₁)
proj₁ (deMorgan'' (inj₂ x₁)) x = inj₁ x₁
_×_.proj₂ (deMorgan'' npq) (inj₁ x) record { proj₁ = proj₁ ; proj₂ = proj₂ } = x proj₁
_×_.proj₂ (deMorgan'' npq) (inj₂ x) record { proj₁ = proj₁ ; proj₂ = proj₂ } = x proj₂

RAA : prop -> prop
RAA P = ¬ (¬ P) -> P

case⊥ : {C : prop} -> ⊥ -> C
case⊥ ()

tmd-raa : {P : prop} -> TMD P -> RAA P
tmd-raa (inj₁ x) x₁ = x
tmd-raa (inj₂ x) x₁ = case⊥ (x₁ x)

{-
Exercises
-}

p1 : {P : prop } -> P ⇔ (P ∧ P)
proj₁ p1 = λ { x →  x , x }
proj₂ p1 = λ { record { proj₁ = proj₁ ; proj₂ = proj₂ } →  proj₁ }

p2 : {P Q : Set} -> P ∨ ¬ P ⇒ (¬ (P ∧ Q) ⇔ ¬ P ∨ ¬ Q)
proj₁ (p2 (inj₁ x)) x₁ = {! !}
proj₁ (p2 (inj₂ x)) x₁ = inj₁ x
_×_.proj₂ (p2 x) (inj₁ x₁) record { proj₁ = proj₁ ; proj₂ = proj₂ } = x₁ proj₁
_×_.proj₂ (p2 x) (inj₂ x₁) record { proj₁ = proj₁ ; proj₂ = proj₂ } = x₁ proj₂

p3 : {P : prop} -> ¬ (P ∧ ¬ P)
p3 record { proj₁ = proj₁ ; proj₂ = proj₂ } = proj₂ proj₁

open import Function using (_∘_; const)

p4 : {P : prop } -> ¬ (P ⇔ ¬ P)
p4 = ? -- can't prove P from ¬ P

p4' : {P : prop } -> P -> ¬ (P ⇔ ¬ P)
p4' x record { proj₁ = proj₁ ; proj₂ = proj₂ } = proj₁ x x -- can't prove P from ¬ P

p4'' : {P : prop} → (TMD P → (¬ (P ⇔ ¬ P)))
p4'' (inj₁ lem) record { proj₁ = proj₁ ; proj₂ = proj₂ } = proj₁ lem lem
p4'' (inj₂ lem) record { proj₁ = proj₁ ; proj₂ = proj₂ } =
  let p = proj₂ lem
  in proj₁ p p

p5 : {P : prop } -> ¬ (¬ (P ∨ ¬ P))
p5 x = {!!} -- (λ x₁ -> {! !})-- Can't prove P ∨ ¬ P without LEM

p5' : {P : prop } -> TMD P -> ¬ (¬ (P ∨ ¬ P))
p5' lem x₁ = x₁ lem  -- (λ x₁ -> {! !})-- Can't prove P ∨ ¬ P without LEM

p6 : {P : prop } -> ¬ P ⇔ ¬ (¬ (¬ P))
proj₁ p6 x x₁ = x₁ x
proj₂ p6 x x₁ = x λ { x₂ →  x₂ x₁ }

p7 : {P : prop } -> (¬ (¬ P ⇒ P)) ⇒ (P ∨ ¬ P)
p7 x = {!!}

p8 : {P : prop } -> (P ∨ ¬ P) ⇒ (¬ (¬ P ⇒ P))
p8 (inj₁ x) x₁ = {!!}
p8 (inj₂ x) x₁ = x (x₁ x)

-----------------------------------------

data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}


