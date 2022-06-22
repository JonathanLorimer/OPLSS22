# Algebra of Programming

## Folds and unfolds

Δ - fork combinator runs a function on two sides of a cartesian product of the same element

#### Examples
```
h = f Δ g <=> fst . h = f ^ snd . h = g
fst . (f Δ g) = f ~ snd . (f Δ g) = g
h = (fst . h) Δ (snd . h)
(f Δ g) . h = (f . h) Δ (g . h)
f: C -> A, g: C -> B
--------------------
f Δ g : C -> A x B
(Δ): (c -> a) -> (c -> b) -> c -> (a,b)
```

▼ -

```
h = f ▼ g <=> h . Left = f ^ h . Right = g
```

#### Functors
A x B is an operation on typs but can also be an operation on functions

```
f : A -> C, g : B -> D
----------------------
f x g : A x B -> C x D

f x g = (f . fst) Δ (g . snd)
```

#### Polynomial Functors

x, +, 1 (unit), constants

```
N X = 1 + X
L X = 1 + N x X
Ta X = A + (X x X)
```

have least fixed points

muF ~ F (muF)
in: F(muF) -> muF

F(muF) -> F(A)
|         |
V         V
muF    -> A

```haskell
data Mu f = In (f (Mu f))
```

least fp "initial algebra" is
in : f x -> x
out : x -> f x

F X -fh-> F A
|in       |phi
V         V
X    -h-> A


F X <-fh- F A
^         ^
|out      |phi
X   <-h-  A

## Para / histo / hylo

## Metamorphisms

## Traversals
