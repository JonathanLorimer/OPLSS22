# Proof Theory

## Propositions as types

- Conjunction corresponds to pairs
- The proof of conjunction introduction is effectively the program that tuples 2 variables

```haskell
proofOfConjunctionIntroduction :: a -> b -> (a,b)
proofOfConjunctionElimA :: (a,b) -> a
proofOfConjunctionElimA :: (a,b) -> b
```
- Reduction corresponse to computation

Connectives should only be composed of non-connectives

Notational definitions define things in terms of what you already know
