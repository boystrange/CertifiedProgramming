---
title: Negation and decidability
prev:  Chapter.Logic.Connectives
next:  Chapter.Logic.Existential
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}
```
-->

```
module Chapter.Logic.Negation where
```

## Imports

```
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## Constructive negation

In constructive logic, the `⊥` data type has a fundamental role
since it allows us to define negation. Showing that the *negation*
of a proposition `A` holds amounts to showing that a proof of `A`
can be turned into a proof of `⊥`.

```
¬_ : Set → Set
¬ A = A → ⊥
```

Using negation in conjunction with propositional equality we can
define the notion of "being different from", thus:

```
_≢_ : ∀{A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)
```

As an example, let us prove that `true` and `false` are
different. We start with a definition like this:

```
true≢false₁ : true ≢ false
true≢false₁ = {!!}
```

In order to make progress, recall that the type `true ≢ false` is
definitionally equal to the type `¬ (true ≡ false)` which, in turn,
is definitionally equal to the type `true ≡ false → ⊥`. That is,
`true≢false` is nothing but a *function* that accepts a proof of
`true ≡ false` and yields something of type `⊥`. We can obtain
evidence of this fact by giving a name --- say `p` --- to the
argument of the function:

```
true≢false₂ : true ≢ false
true≢false₂ p = {!!}
```

At this stage Agda expects us to fill the hole with a term of type
`⊥`. This is clearly impossible, but in the context we also have a
proof `p` that `true ≡ false`. If we inspect `p` using case
analysis, Agda figures out that there cannot be such proof and
replaces `p` with the absurd pattern. This way, we are freed from
the obligation to fill the goal.

```
true≢false₃ : true ≢ false
true≢false₃ ()
```

Occasionally it is useful to define a function that accepts an
absurd pattern "on the spot". In these cases we can use the syntax
`λ ()` to define such function. For example, we can prove that
`true` is different from `false` also in the following way:

```
true≢false₄ : true ≢ false
true≢false₄ = λ ()
```

We will see below examples where this notation is useful.

## Properties of negation

We will make a rather extensive use of negation in the following
chapters. For the time being, we prove a few laws related to
negation. The first one is **contradiction**, namely the fact that
if we have both a proof of `A` and a proof of `¬ A` then we can
derive a proof of `⊥`. Recalling that the negation of `A` is defined
as a function that turns a proof of `A` into a proof of `⊥`, we see
that contradiction simply amounts to function application.

```
contradiction : ∀{A : Set} → A → ¬ A → ⊥
contradiction p n = n p
```

Recalling that in Agda the type `¬ A` is *defined* to be the same as
the type `A → ⊥`, the type of `contradiction` can also be written
as `∀{A : Set} → A → ¬ ¬ A`. This is one of the so-called "double
negation" laws.

```
double-negation : ∀{A : Set} → A → ¬ ¬ A
double-negation = contradiction
```

In classical logic, the inverse implication `¬ ¬ A → A` is also
assumed to be true. However, this implication is not provable in
constructive logic (it is instructive to **attempt** proving this
property).

Another interesting law concerning negation is **contraposition**,
asserting that if `A` implies `B`, then `¬ B` implies `¬ A`.

```
contraposition : ∀{A B : Set} → (A → B) → ¬ B → ¬ A
contraposition f p q = p (f q)
```

Observe that we define `contraposition` as a function with three
arguments `f`, `p` and `q`, while its type appears to have only two
arguments, one of type `A → B` (that would be `f`) and the other of
type `¬ B` (that would be `p`). However, the type `¬ A` is actually
the type `A → ⊥`, so `contraposition` can be seen as also having a
third argument of type `A`, that would be `q`.

Using `contraposition` and `double-negation` we can prove that
*triple* negation implies *single* negation.

```
triple-negation : ∀{A : Set} → ¬ ¬ ¬ A → ¬ A
triple-negation = contraposition double-negation
```

## Decidability

In classical logic it is common to assume the validity of the
*excluded middle* principle, namely that `¬ A ⊎ A` is true for every
proposition `A`. As we know from the [previous
chapter](Chapter.Logic.Connectives.html), in constructive logic, a
proof of a disjunction `¬ A ⊎ A` embeds either a proof of `¬ A` or a
proof of `A`, hence it may very well be the case that we are unable
to prove `¬ A ⊎ A` if we cannot find either a proof of `¬ A` or a
proof of `A`. The propositions for which we are able to prove `¬ A ⊎
A` are said to be **decidable**.

```
Decidable : Set → Set
Decidable A = ¬ A ⊎ A
```

As an example of decidable property, consider the problem of
determining whether two boolean values are equal or not.  This can
be shown by considering all the possible cases, which are finite.

```
Bool-eq-decidable : ∀(x y : Bool) → Decidable (x ≡ y)
Bool-eq-decidable true  true  = inj₂ refl
Bool-eq-decidable true  false = inj₁ λ ()
Bool-eq-decidable false true  = inj₁ λ ()
Bool-eq-decidable false false = inj₂ refl
```

Note that we use the constructor `inj₂` for representing a positive
answer to the question "is `x` equal to `y`?" and `inj₁` for
representing a negative answer. For readability purposes, it may be
appropriate to give these constructors more evocative names, such as
`yes` and `no`. We can do so (without defining an *ad hoc*
`Decidable` data type) by means of **pattern synonyms**.

```
pattern yes x = inj₂ x
pattern no  x = inj₁ x
```

With these declarations, we may write `Bool-eq-decidable` as follows.

```
Bool-eq-decidable₁ : ∀(x y : Bool) → Decidable (x ≡ y)
Bool-eq-decidable₁ true  true  = yes refl
Bool-eq-decidable₁ true  false = no λ ()
Bool-eq-decidable₁ false true  = no λ ()
Bool-eq-decidable₁ false false = yes refl
```

Another example of decidabile property is the equality for natural
numbers. In this case, when we compare two numbers of the form `suc
x` and `suc y`, we first decide whether `x` and `y` are equal. If
they are not, then we conclude that `suc x` and `suc y` must be
different (recall that constructors such as `suc` are injective). If
`x` and `y` are equal, then they can be unified and we can prove
`suc x ≡ suc y` by reflexivity.

```
Nat-eq-decidable : ∀(x y : ℕ) → Decidable (x ≡ y)
Nat-eq-decidable zero    zero    = yes refl
Nat-eq-decidable zero    (suc y) = no λ ()
Nat-eq-decidable (suc x) zero    = no λ ()
Nat-eq-decidable (suc x) (suc y) with Nat-eq-decidable x y
... | no  neq  = no λ { refl → neq refl }
... | yes refl = yes refl
```

As a final example we show that the equality of lists is decidable,
provided that the equality between their elements is also decidable.

```
List-eq-decidable : ∀{A : Set} → (∀(x y : A) → Decidable (x ≡ y)) → (xs ys : List A) → Decidable (xs ≡ ys)
List-eq-decidable _≡?_ []        []       = yes refl
List-eq-decidable _≡?_ []        (x ∷ ys) = no λ ()
List-eq-decidable _≡?_ (x ∷ xs) []        = no λ ()
List-eq-decidable _≡?_ (x ∷ xs) (y ∷ ys) with x ≡? y | List-eq-decidable _≡?_ xs ys
... | no  neq  | _        = no λ { refl → neq refl }
... | yes _    | no  neq  = no λ { refl → neq refl }
... | yes refl | yes refl = yes refl
```

The case in which we compare two lists of the form `x ∷ xs` and `y
∷ ys` illustrates the use of multiple `with` clauses. In this case,
we have to compare both the heads and the tails of the two
lists. Only if both components are equal can we conclude that the
original lists are equal. Note that each case after the `with`
clauses has as many patterns as the number of `with` clauses.

## Exercises

1. Prove the theorem `ntop : ¬ ⊤ → ⊥`.
2. Which of the following De Morgan's laws can be proved?
   ```text
   ¬ A ⊎ ¬ B → ¬ (A × B)
   ¬ A × ¬ B → ¬ (A ⊎ B)
   ¬ (A ⊎ B) → ¬ A × ¬ B
   ¬ (A × B) → ¬ A ⊎ ¬ B
   ```
3. Show that the excluded middle implies double negation
   elimination, namely prove the theorem `em-dn : (∀{A : Set} → ¬ A
   ⊎ A) → ∀{A : Set} → ¬ ¬ A → A`
4. Prove the theorem `nndec : ∀{A : Set} → ¬ ¬ Decidable A`. Hint:
   one of the De Morgan's laws helps.
5. In classical logic the double negation elimination `¬ ¬ A → A`
   is usually assumed to be true. This is not the case in
   constructive logic. Show that double negation elimination implies
   the excluded middle, namely prove the theorem `dn-em : (∀{A : Set}
   → (¬ ¬ A → A)) → ∀{A : Set} → Decidable A `. Hint: use the
   solution to the previous exercise.
```
-- EXERCISE 1

ntop : ¬ ⊤ → ⊥
ntop p = p tt

-- EXERCISE 2: all laws but the last one can be proved.

de-morgan-1 : ∀{A B : Set} → ¬ A ⊎ ¬ B → ¬ (A × B)
de-morgan-1 = {!!} -- ⊎-elim (contraposition fst) (contraposition snd)

de-morgan-2 : ∀{A B : Set} → ¬ A × ¬ B → ¬ (A ⊎ B)
de-morgan-2 p = {!!} -- ⊎-elim (fst p) (snd p)

de-morgan-3 : ∀{A B : Set} → ¬ (A ⊎ B) → ¬ A × ¬ B
de-morgan-3 nab = {!!} -- contraposition inj₁ nab , contraposition inj₂ nab

-- EXERCISE 3

em-dn : (∀{A : Set} → ¬ A ⊎ A) → ∀{A : Set} → ¬ ¬ A → A
em-dn f {A} g with f {A}
... | inj₁ x = ⊥-elim (g x)
... | inj₂ x = x

-- EXERCISE 4

nndec : ∀{A : Set} → ¬ ¬ Decidable A
nndec p with de-morgan-3 p
... | nna , na = nna na

-- EXERCISE 5

dn-em : (∀{A : Set} → (¬ ¬ A → A)) → ∀{B : Set} → Decidable B
dn-em f = f nndec
```
{:.solution}
