{-
OPLSS 22 : Introduction to Type Theory (1)
-}

{-
What is Type Theory?
- a foundational system, an alternative to Set Theory
- a logic
- a programming language
-}

{-
What are the difference to set theory?
- elementhood is judgement not proposition
- logic is intuitionistic, propositions as types explanation
- functions are primitive
-}

{-
What is a function?
-}
open import Data.Nat

f : ℕ → ℕ
f n = n + 2
{-
f 3
= (n + 2)[n := 3] -- β-rule
= 3 + 2
= 5
-}

f' : ℕ → ℕ
f' = λ n → n + 2
{-
f' 3
= (λ n → n + 2) 3
= (n + 2)[n := 3]
= 3 + 2
= 5

(λ x → M) N = M[x := N] -- β-rule
-}

-- Schönfinkel, Curry
g : ℕ → ℕ → ℕ
g = λ x → λ y → y + x

-- A → B → C = A → (B → C)
-- g x y = (g x) y

h : (ℕ → ℕ) → ℕ
h = λ k → k 2
{-
h f'
= (λ k → k 2)(λ n → n + 2) --β rule
= (k 2)[k := λ n → n + 2]
= (λ n → n + 2) 2
= (n + 2)[n := 2] -- β - rule
= 2 + 2
= 4
-}

{-
g : ℕ → ℕ → ℕ
g = λ x → λ y → y + x

-}

module _(y : ℕ) where

  x = {!g y!}
  {- (λ x → λ y → y + x) y
   = (λ y → y + x)[x := y]
   = (λ z → z + x)[x := y] -- α conversion
   = λ z → z + y
-}
hh : ℕ → ℕ
hh = λ n → f' n
{-
hh = f' -- η - rule
extensionality
-}

{-
combinators
-}

variable A B C : Set

id : A → A
id x = x

_∘_ : (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

K : A → B → A
K a b = a

S : (A → B → C) → (A → B) → (A → C)
S f g a = f a (g a)

I : A → A
I {A} = S K (K {B = A})

CC : (B → C) → (A → B) → A → C
CC = λ g f x → g (f x)

{-
λ x → x = I
λ x → y = K y
λ x → M N = S (λ x → M) (λ x → N)

(λ x → M N) L
= (M N)[x := L]
= M[x := L] N [x := L]

S (λ x → M) (λ x → N) L
= (λ x → M) L ((λ x → N) L)
= M[x := L] N[x := L]

-- λ x → (λ y → M) cannot happen

λ x → K = K K
λ x → S = K S

if x does not occur in M then
λ x → M = K M
λ x → M x = M


-}

{- S f g a = f a (g a) -}
CC-sk : (B → C) → (A → B) → (A → C)
CC-sk = S (K S) K
{-
λ f g a → f (g a)
= λ f → λ g → λ a → f (g a)
= λ f → λ g → S (λ a → f) (λ a → g a)
= λ f → λ g → S (K f) g
= λ f → λ g → (S (K f)) g
= λ f → S (K f)
= S (λ f → S) (λ f → K f)
= S (K S) K
-}
