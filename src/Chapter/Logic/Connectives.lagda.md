---
title: Logical connectives and constants
next:  Chapter.Logic.Negation
---

```
module Chapter.Logic.Connectives where
```

The logic we have been using so far is based on a limited set of
Agda types:

* **Logical implication** corresponds to the *arrow type*: a proof
  of `A → B` is a function that, applied to a proof of `A`, yields
  a proof of `B`.
* **Universal quantification** corresponds to the **dependent arrow
  type**: a proof of `∀(x : A) → B` is a function that, applied to
  an element `x` of type `A`, yields a proof of `B` (where `x` may
  occur in `B`).
* **Equality** `E ≡ F` is the type of proofs showing that `E` is
  equal to `F`. In order to prove equalities we have used
  *reflexivity* and equational reasoning.

In general, we will need a richer set of logical connectives in
order to prove interesting properties of programs. For example, to
prove the correctness of a sorting function on lists we must be able
to state that the list resulting from the function is sorted *and*
that it is also a permutation of the original list. This property is
the *conjunction* of two sub-properties of lists, that is being
sorted and being a permutation of another list. In this chapter we
will see how to represent **conjunction**, **disjunction**,
**truth** and **falsity** in constructive logic by means of suitably
defined data types.

## Imports

```
open import Function using (const; id; _∘_)
open import Data.Bool using (Bool; true; false)
open import Data.Nat
open import Relation.Binary.PropositionalEquality
```

## Conjunction

In constructive logic, a proof of *`A` and `B`* is a **pair** `(p ,
q)` consisting of a proof `p` of `A` and a proof `q` of `B`. Thus,
we can define conjunction as a data type for representing
pairs. Naturally, the data type will be parametric in the type of
the two components of the pair.

```
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
```

Notice that we have chosen an infix form for both the data type
`_×_` and its constructor `_,_`. In this way, we will be able to
write `A × B` for the type of pairs whose first component has type
`A` and whose second component has type `B`. Analogously, we will be
able to write `p , q` for the pair whose first component is `p` and
whose second component is `q`. We specify the fixity of `×` and `,`
so that they are both right associative.

```
infixr 3 _×_
infixr 4 _,_
```

For example, `A × B × C` means `A × (B × C)` and `p , q , r` means
`p , (q , r)`.

The most common way of "consuming" pairs is by performing case
analysis on them. Since the `_×_` data type has only one
constructor, when we perform case analysis we end up considering
just one case in which the pair has the form `(x , y)`. As an
example, we can define two projections `fst` and `snd` that allow us
to access the two components of a pair.

```
fst : ∀{A B : Set} → A × B → A
fst (x , _) = x

snd : ∀{A B : Set} → A × B → B
snd (_ , y) = y
```

Note that `fst` and `snd` are also proofs of two well-known theorems
about conjunctions: if `A × B` is true, then `A` is true (`fst`) and
`B` is true (`snd`).

By combining conjunction (given by the data type `×`) and
implication (given by the native Agda's arrow type `→`) we can also
model double implication, commonly known as "if and only if".

```
_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)
```

<!--
```
infixr 1 _⇔_
```
-→

## Disjunction

In constructive logic, a proof of *`A` or `B`* is either a proof of
`A` or a proof of `B` together with an indication of which proof we
are providing. This interpretation suggests the representation of
disjunction `⊎` as a data type with two constructors, one taking a
proof of `A` and the other taking a proof of `B`, to yield a proof
of `A ⊎ B`. The name of the constructor indicates which of the two
proofs is provided. We call the two constructors `inj₁` and `inj₂` for
"inject left" and "inject right".

```
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
```

We declare `⊎` as a right associative operator with smaller
precedence than `×`.

```
infixr 2 _⊎_
```

As for conjunctions, we will use case analysis on terms of type `A ⊎
B`. As an example, we can formulate the elimination principle for
disjunctions as the following function.

```
⊎-elim : ∀{A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
⊎-elim f g (inj₁ x) = f x
⊎-elim f g (inj₂ x) = g x
```

For instance, we can use `⊎-elim` to prove that disjunction is
commutative:

```
⊎-comm : ∀{A B : Set} → A ⊎ B → B ⊎ A
⊎-comm = ⊎-elim inj₂ inj₁
```

## Truth

The always true proposition `⊤` is represented as a data type with a
single constructor without arguments. That is, truth is a
proposition for which we can provide a proof without any effort.

```
data ⊤ : Set where
  tt : ⊤
```

## Falsity

The always false proposition `⊥` must not be provable. As such, we
can represent it by a data type without constructors.

```
data ⊥ : Set where
```

The elimination principle for `⊥` is sometimes called *principle of
explosion* or *ex falso quodlibet*. It states that if it is possible
to prove `⊥`, then it is possible to prove anything. Stating this
principle in Agda requires the use of the **absurd pattern**.

```
⊥-elim : ∀{A : Set} → ⊥ → A
⊥-elim ()
```

The pattern `()` in the definition of `⊥-elim` matches an
hypothetical value of type `⊥`. Since no constructor is provided for
`⊥` and no such value may exist, the equation *has no right hand
side* (note that there is no equal sign) and we are not obliged to
provide a proof of `A` as required by the codomain of `⊥-elim`.

In other programming languages that are capable of defining a data
type analogous to `⊥` it is possible to assign the type `⊥` to
non-terminating expressions. If this were allowed also in Agda, the
whole language would be useless insofar program verification is
concerned, since `⊥-elim` would easily allow us to prove *any*
property about *any* program. For this reason, Agda has a
*termination checker* making sure that every definition is
*terminating*. For example, if define `loop` as follows

<!--
```
{-# TERMINATING #-}
```
-→
```
loop : ℕ → ⊥
loop n = loop (suc n)
```

Agda reports that this definition does not pass the termination
check. Indeed, `loop` is recursively applied to increasingly larger
arguments. An even simpler example of non-terminating definition is
`bottom`, shown below.

<!--
```
{-# TERMINATING #-}
```
-→
```
bottom : ⊥
bottom = bottom
```

All the recursive functions we have defined until now are verified
by Agda to be *terminating* because there is an argument that
becomes *structurally smaller* from an application of the function
to its recursive invocation. Structural recursion applies to a large
family of functions, but some of them
<!--
(e.g. [division](Chapter.Fun.Division.html) or [quick
sort](Chapter.Fun.QuickSort.html))
-→
cannot be easily formulated in this way. We will see a general
technique for having these functions accepted by Agda in later
sections.

## Exercises

1. Prove that conjunction is commutative, namely the theorem
   `×-comm : ∀{A B : Set} → A × B → B × A`.
2. Prove that `×` and `⊎` are idempotent, namely the theorems
   `×-idem : ∀{A : Set} → A × A ⇔ A` and `⊎-idem : ∀{A : Set} → A
   ⊎ A ⇔ A`.
3. Prove that `×` distributes over `⊎` on the left, namely the
   theorem `×⊎-dist : ∀{A B C : Set} → A × (B ⊎ C) ⇔ (A × B) ⊎ (A ×
   C)`.
4. Prove that `⊤` is the unit of conjuction, namely the theorems
   `×-unit-l : ∀{A : Set} → ⊤ × A ⇔ A` and `×-unit-r : ∀{A : Set}
   → A × ⊤ ⇔ A`.
5. Prove that `⊤` absorbs disjunctions, namely the theorems `⊎-⊤-l :
   ∀{A : Set} → ⊤ ⊎ A ⇔ ⊤` and `⊎-⊤-r : ∀{A : Set} → A ⊎ ⊤ ⇔ ⊤`.
6. Prove that `⊥` is the unit of disjunctions, namely the theorems
   `⊎-unit-l : ∀{A : Set} → ⊥ ⊎ A ⇔ A` and `⊎-unit-r : ∀{A : Set}
   → A ⊎ ⊥ ⇔ A`.
7. Prove that `⊥` absorbs conjunctions, namely the theorems `×-⊥-l :
   ∀{A : Set} → ⊥ × A ⇔ ⊥` and `×-⊥-r : ∀{A : Set} → A × ⊥ ⇔ ⊥`.
8. Prove that every boolean value is either `true` or `false`,
   namely the theorem `Bool-⊎ : ∀(b : Bool) → (b ≡ true) ⊎ (b ≡
   false)`.

```
-- EXERCISE 1
×-comm : ∀{A B : Set} → A × B → B × A
×-comm (x , y) = y , x

-- EXERCISE 2
×-idem : ∀{A : Set} → A × A ⇔ A
×-idem = fst , λ x → (x , x)

⊎-idem : ∀{A : Set} → A ⊎ A ⇔ A
⊎-idem = ⊎-elim id id , inj₁

-- EXERCISE 3
×⊎-dist : ∀{A B C : Set} → A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
×⊎-dist =
  (λ p → ⊎-elim (inj₁ ∘ (fst p ,_)) (inj₂ ∘ (fst p ,_)) (snd p)) ,
  ⊎-elim (λ p → fst p , inj₁ (snd p)) (λ p → fst p , inj₂ (snd p))

-- EXERCISE 4
×-unit-l : ∀{A : Set} → ⊤ × A ⇔ A
×-unit-l = snd , (tt ,_)

×-unit-r : ∀{A : Set} → A × ⊤ ⇔ A
×-unit-r = fst , (_, tt)

-- EXERCISE 5
⊎-unit-l : ∀{A : Set} → ⊥ ⊎ A ⇔ A
⊎-unit-l = ⊎-elim ⊥-elim id , inj₂

⊎-unit-r : ∀{A : Set} → A ⊎ ⊥ ⇔ A
⊎-unit-r = ⊎-elim id ⊥-elim , inj₁

-- EXERCISE 6
⊎-⊤-l : ∀{A : Set} → ⊤ ⊎ A ⇔ ⊤
⊎-⊤-l = const tt , inj₁

⊎-⊤-r : ∀{A : Set} → A ⊎ ⊤ ⇔ ⊤
⊎-⊤-r = const tt , inj₂

-- EXERCISE 7
×-⊥-l : ∀{A : Set} → ⊥ × A ⇔ ⊥
×-⊥-l = fst , ⊥-elim

×-⊥-r : ∀{A : Set} → A × ⊥ ⇔ ⊥
×-⊥-r = snd , ⊥-elim

-- EXERCISE 8
Bool-⊎ : ∀(b : Bool) → (b ≡ true) ⊎ (b ≡ false)
Bool-⊎ true  = inj₁ refl
Bool-⊎ false = inj₂ refl

```
{:.solution}
