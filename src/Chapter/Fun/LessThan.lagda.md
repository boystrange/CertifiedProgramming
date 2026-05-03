---
title: Inequality
next:  Chapter.Fun.SortedLists
---

```
module Chapter.Fun.LessThan where
```

In this section we define the non-strict inequality relation on
natural numbers and prove some of its fundamental properties.

## Imports

```
open import Function
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
```

## Non-strict inequality

We define non-strict inequality as an inductive family according to
the following rules.

                             x ≤ y
    [z≤n] -----    [s≤s] -------------
          0 ≤ x          1 + x ≤ 1 + y

This is not the only conceivable inference system that defines
non-strict inequality. However, it turns out to be a convenient one
in most situations.

```
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀{x : ℕ} → 0 ≤ x
  s≤s : ∀{x y : ℕ} → x ≤ y → suc x ≤ suc y
```

The axiom `z≤n` proves that `0` is the least element, whereas the
rule `s≤s` builds a proof of `suc x ≤ suc y` from a proof of `x ≤
y`. As an example, we can derive `2 ≤ 3` with two applications of
`s≤s` and one application of `z≤n`. In general, there are as many
applications of `s≤s` as the value of the smaller number.

```
_ : 2 ≤ 3
_ = s≤s (s≤s z≤n)
```

## Correctness and completeness

Even though the definition of `≤` seems to make sense, one may
wonder whether it actually characterizes the non-strict inequality
on natural numbers. We can see that this is the case by showing that
`≤` is correct and complete with respect to another characterization
of such relation given in terms of addition.

```
_≤ₘ_ : ℕ → ℕ → Set
x ≤ₘ y = ∃[ z ] x + z ≡ y
```

According to this definition, `x` is not larger than `y` if there
exists some natural number `z` such that `x + z ≡ y`. We can prove
that `≤` implies `≤ₘ` as follows.

```
≤-correct : ∀{x y : ℕ} → x ≤ y → x ≤ₘ y
≤-correct z≤n = _ , refl
≤-correct (s≤s le) with ≤-correct le
... | z , refl = z , refl
```

The idea is that the `z` in the definition of `≤ₘ` coincides with
the `y` found in the application of `z≤n`. We have used the
underscore since `refl` unifies `z` with `y` when `x` is `0`. For
every application of `s≤s` proving `suc x ≤ suc y` we recursively
find the `z` such that `x + z ≡ y`, which is the same `z` such that
`suc x + z ≡ suc y`. Note that we cannot simplify this case to

    ≤-correct (s≤s le) = ≤-correct le

even though the result of `≤-correct le` superficially appears to
be the same result of `≤-correct (s≤s le)`, the reason being that
the two `refl`s prove different equalities (`x + z ≡ y` in the
former case and `suc x + z ≡ suc y` in the latter). In fact, (some
of) the implicit arguments supplied to the two occurrences of `refl`
differ.

We can also show that `≤` is complete with respect to `≤ₘ`.

```
≤-complete : ∀{x y : ℕ} → x ≤ₘ y → x ≤ y
≤-complete (z , refl) = lemma
  where
    lemma : ∀{x y : ℕ} → x ≤ x + y
    lemma {zero}   = z≤n
    lemma {suc _} = s≤s lemma
```

By performing case analysis on the proof of `x ≤ₘ y` we unify `y`
with `x + z`, so our goal turns into providing a proof of `x ≤ x +
z`. This is done by means of the local `lemma`.

## Inequality is a total order

Here we prove that `≤` is a **total order** on the natural
numbers. We begin by proving **reflexivity**.

```
≤-refl : ∀{x : ℕ} → x ≤ x
≤-refl {zero}  = z≤n
≤-refl {suc x} = s≤s ≤-refl
```

If two numbers are mutually related by `≤`, then they must be
equal. This property is called **antisymmetry** and is proved below.

```
≤-antisym : ∀{x y : ℕ} → x ≤ y → y ≤ x → x ≡ y
≤-antisym z≤n     z≤n     = refl
≤-antisym (s≤s p) (s≤s q) = cong suc (≤-antisym p q)
```

It is interesting to observe that the case analysis only considers
those combinations in which `x ≤ y` and `y ≤ x` are proved by means
of the same constructors. Indeed, when `x ≤ y` is proved by `z≤n`,
then `x` must be `0` and the only proof of `y ≤ x` must have been
obtained with `z≤n` as well. Similarly, when `x ≤ y` is proved by
`s≤s` then `y` must have the form `suc z` for some `z`, hence the
proof of `y ≤ x` must have been obtained by an application of `s≤s`
too.

Concerning **transitivity**, it is convenient to perform case
analysis on the proofs of `x ≤ y` and `y ≤ z`. Note that, when the
former relation is proved by `s≤s`, the second relation can only be
proved by `s≤s` because `y` has the form `suc y'`.

```
≤-trans : ∀{x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
≤-trans z≤n     q       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)
```

To conclude the proof that `≤` is a total order we have to show
that any two natural numbers `x` and `y` are related in one way or
another. This follows from a straightforward cases analysis on them.

```
≤-total : ∀(x y : ℕ) → x ≤ y ⊎ y ≤ x
≤-total zero    _       = inj₁ z≤n
≤-total (suc _) zero    = inj₂ z≤n
≤-total (suc x) (suc y) with ≤-total x y
... | inj₁ p = inj₁ (s≤s p)
... | inj₂ q = inj₂ (s≤s q)
```

## Exercises

1. Show that `≤` is decidable, namely prove the theorem `_≤?_ : ∀(x
   y : ℕ) → ¬ x ≤ y ⊎ x ≤ y`.
2. Define `min : ℕ → ℕ → ℕ` and `max : ℕ → ℕ → ℕ` and prove the
   theorems `≤-min : ∀{x y z : ℕ} → x ≤ y → x ≤ z → x ≤ min y z`
   and `≤-max : ∀{x y z : ℕ} → x ≤ z → y ≤ z → max x y ≤ z`.
3. Strict inequality `x < y` can be defined to be the same as `suc x
   ≤ y`. Prove that this relation is transitive and irreflexive.

```
-- EXERCISE 1

_≤?_ : ∀(x y : ℕ) → ¬ x ≤ y ⊎ x ≤ y
zero   ≤? y    = inj₂ z≤n
suc x ≤? zero = inj₁ λ ()
suc x ≤? suc y with x ≤? y
... | inj₁ gt = inj₁ λ { (s≤s le) → gt le }
... | inj₂ le = inj₂ (s≤s le)

_<_ : ℕ → ℕ → Set
x < y = suc x ≤ y

-- EXERCISE 2

-- ...

-- EXERCISE 3

lt-irrefl : ∀{x : ℕ} → ¬ (x < x)
lt-irrefl {suc zero}     (s≤s ())
lt-irrefl {suc (suc _)} (s≤s (s≤s lt)) = lt-irrefl lt

-- ...
```
{:.solution}
