---
title: Existential quantification
prev:  Chapter.Logic.Negation
next:  Chapter.Logic.Predicates
---

```
module Chapter.Logic.Existential where
```

## Imports

```
open import Function using (_∘_)
open import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong; sym; subst)
```

## Defining the existential quantifier

In constructive logic, the proof of a predicate of the form $∃x\in
A.P(x)$ is a **pair** consisting of a particular element $x$ of $A$
called *witness* along with a proof that $x$ satisfies the predicate
$P$. This is an example of **dependent pair** where the type of the
second component depends on the value $x$ of the first one. The data
type that we use to represent dependent pairs is traditionally
called "sigma type" and is a refinement of the type `_×_` we have
defined in a [previous
chapter](Chapter.Logic.Connectives.html#conjunction).

    data Σ (A : Set) (B : A → Set) : Set where
      _,_ : ∀(x : A) → B x → Σ A B

The *non-dependent* pair type can be defined as an instance of a
sigma type where the type of the second component *does not* depend
on the value of the first one.

    _×_ : Set → Set → Set
    A × B = Σ A λ _ → B

The two projections `fst` and `snd` for sigma types are the same we
have already defined for `_×_`, except for their type. In
particular, the type of `snd` refers to the first component of a
dependent pair by means of `fst`.

```
fst : ∀{A : Set} {B : A → Set} → Σ A B → A
fst (x , _) = x

snd : ∀{A : Set} {B : A → Set} (p : Σ A B) → B (fst p)
snd (_ , y) = y
```

Sigma types have plenty of uses in the specification and
verification of programs. Below we see a few examples.

## Refined types

We can use sigma types to *refine* an existing type to some elements
that have a certain property. For example, we can define the type of
non-null natural numbers as follows.

```
ℕ⁺ : Set
ℕ⁺ = Σ ℕ (_≢ 0)
```

A non-null natural number, that is an element of the type `ℕ⁺`, is a
pair consisting of some natural number `x` and a proof that `x` is
different from `0`. For example, `1` is an element of `ℕ⁺`.

```
_ : ℕ⁺
_ = 1 , λ ()
```

Analogously, we can define the type of non-empty lists as follows.

```
List⁺ : Set → Set
List⁺ A = Σ (List A) (_≢ [])
```

## Partial functions

Type refinements may be useful for the implementation of *partial
functions* that are only defined for a subset of their
domain. Typical examples are division, which is defined only for
non-null divisors, and the functions `head` and `tail` that
respectively return the head and the tail of a non-empty list.

```
head : ∀{A : Set} → List⁺ A → A
head ([]     , ne) = contradiction refl ne
head (x ∷ _  , _ ) = x

tail : ∀{A : Set} → List⁺ A → List A
tail ([]     , ne) = contradiction refl ne
tail (_ ∷ xs , _ ) = xs
```

In the definition of `head` and `tail` we perform case analysis on
an element of type `List⁺ A`, which is a pair consisting of a list
and a proof that the list is not empty. We further analyze the
structure of the list. Agda is not able to automatically rule out
the case in which the list is `[]`. However, this case is made
impossible by the proof `ne` that the list is not empty, hence we
can honor our obligation to yield a result of the desired type by
invoking `contradiction`. When the list is not empty, we simply
return the right component.

## Intrinsic verification

Another typical use case of sigma types is in providing type-rich
information about the result returned by a function. For example,
suppose we wish to implement a function `pred` that, applied to a
natural number different from `0` (that is, an element of `ℕ⁺`),
returns its predecessor. We could implement `pred` simply as a
function of type `ℕ⁺ → ℕ`, however this type would not provide any
information about the property of the returned result. In fact, such
function could return any number, not necessarily the desired
one. Alternatively, we could implement `pred` so that it returns a
natural number along with a proof that its successor is the number
passed to the function. But this is just what a sigma type allows us
to do. To make the syntax evocative of the fact that we are
describing the existence of a term with a certain property the Agda
library defines

    ∃[ x ] A

as syntactic sugar for

    Σ _ λ x → A

where `x` typically occurs in `A` and the underscore is a
placeholder for the type of the first component of the dependent
pair, which can be automatically inferred by Agda in many
cases. With the help of this syntax we define `pred` thus.

```
pred : ∀(p : ℕ⁺) → ∃[ x ] fst p ≡ suc x
pred (zero  , nz) = contradiction refl nz
pred (suc x , _ ) = x , refl
```

Note the use of `fst` in the type of `pred` to refer to the first
component of the pair `p`. As usual, we perform case analysis on the
argument of type `ℕ⁺`, further analyzing the witness in the
pair. Once we have established that this must have the form `suc x`,
we return `x` along with the proof that this is the correct result.

The definition of functions whose type specifies their behavior in
detail is called *intrinsic verification*. We will see more
substantial examples of this technique in later sections.

## Defining predicates

As final use case for existential quantification we consider the
definition of a binary predicate `x ∣ y` indicating that `x` divides
`y`. This relation among `x` and `y` can be expressed as the
existence of some natural number `z` such that `z` times `x` results
into `y`.

```
_∣_ : ℕ → ℕ → Set
x ∣ y = ∃[ z ] z * x ≡ y
```

For example, the type `2 ∣ 64` is inhabited by the witness `32`
along with a proof that `32 * 2` is equal to `64`.

```
_ : 2 ∣ 64
_ = 32 , refl
```

Beware that the symbol `∣` used here and in the rest of this chapter
is the Unicode character obtained by the combination `\|`
(backslash-bar) and is different from the mere vertical bar `|`,
which is one of the few symbols that have a special meaning and are
reserved by Agda.

We can prove that `∣` is a partial order on natural number by
showing that it is reflexive, antisymmetric and
transitive. Reflexivity is shown by taking `1` as witness along with
the proof that `1` is the left unit of multiplication.

```
∣-refl : ∀{x : ℕ} → x ∣ x
∣-refl {x} = 1 , *-identityˡ x
```

Concerning transitivity, by pattern matching on the proofs of `x ∣
y` and `y ∣ z` we find out two witnesses `u` and `v` such that `u *
x == y` and `v * (u * x) == z`. The witness proving that `x` divides
`z` is `v * u`, but we have to reassociate the product `v * (u * x)`
into `(v * u) * x` in order to show that it serves the desired
purpose.

```
∣-trans : ∀{x y z : ℕ} → x ∣ y → y ∣ z → x ∣ z
∣-trans (u , refl) (v , refl) = v * u , *-assoc v u _
```

Proving that `∣` is antisymmetric requires some more work, including
some tedious properties of addition and multiplication. We start by
showing that adding a non-null number `suc y` to `x` cannot yield
`x` and multiplying zero to `x` cannot yield `1`.

```
+-suc-neq : ∀{x y : ℕ} → x + suc y ≢ x
+-suc-neq {suc x} eq = +-suc-neq (suc-injective eq)

*-zero-neq-one : ∀(x : ℕ) → x * 0 ≢ 1
*-zero-neq-one (suc x) eq = *-zero-neq-one x eq
```

Next we show that if the product of two numbers yields `1`, then
both numbers must be `1`.

```
*-one : ∀(x y : ℕ) → x * y ≡ 1 → x ≡ 1 × y ≡ 1
*-one (suc  x)        zero            eq = contradiction eq (*-zero-neq-one x)
*-one (suc  zero)     (suc  zero)     eq = refl , refl
*-one (suc  (suc  x)) (suc  zero)     ()
*-one (suc  (suc  x)) (suc  (suc  y)) ()
```

Then we prove that if the product of `x` and `y` yields `y`, then
either `x` is `1` or `y` is `0`.

```
*-same : ∀(x y : ℕ) → x * y ≡ y → x ≡ 1 ⊎ y ≡ 0
*-same x             zero    eq = inj₂ refl
*-same (suc zero)    (suc y) eq = inj₁ refl
*-same (suc (suc x)) (suc y) eq = contradiction eq +-suc-neq
```

We combine these results to prove that `∣` is antisymmetric.

```
∣-antisymm : ∀{x y : ℕ} → x ∣ y → y ∣ x → x ≡ y
∣-antisymm {x} (u , refl) (v , q) with *-same (v * u) x (subst (_≡ x) (sym (*-assoc v u x)) q)
... | inj₂ refl = sym (*-zeroʳ u)
... | inj₁ eq with *-one v u eq
... | refl , refl = sym (*-identityˡ x)
```

By pattern matching on the proof of `x ∣ y` we find out a `u` such
that `u * x ≡ y`. When we pattern match on the proof of `y ∣ x` we
also find the witness `v` such that `v * y ≡ x`. However, we are
unable to also perform case analysis on the proof of this equality
since the `y` has been unified with `u * x` and `q` is actually a
proof of `v * (u * x) ≡ x` (the unification fails in this case
because `x` occurs on both sides of the equality). We use `subst`
(WARNING `subst` IS DEFINED LATER) to obtain from `q` a proof of the
equality `(v * u) * x ≡ x` and now we use `*-same` to deduce that
either `v * u` is `1` or `x` is `0`. In the latter case we conclude
using the property that `0` absorbs multiplication on the right. In
the former case, we use `*-one` to deduce that both `u` and `v` must
be `1` and we conclude using the property that `1` is the unit of
multiplication on the left.

## Exercises

1. Prove the theorem `pred' : ∀(x : ℕ) → x ≡ 0 ⊎ (∃[ y ] x ≡ suc y)`.
2. Define the type `ℕ₂` of natural numbers greater that `1`. Show
   that `2` (along with a suitable proof) is an element of `ℕ₂`. Then define
   the succesor on `ℕ₂`, namely the function `succ₂ : ℕ₂ → ℕ₂`.
3. Prove that if `x` divides both `y` and `z`, then `x` divides
   `y + z` as well.
4. Prove the theorem `∣-not-total : ∃[ x ] ∃[ y ] ¬ (x ∣ y) × ¬ (y ∣ x)`.
5. Prove the theorem `last-view : ∀{A : Set} (xs : List A) → xs !=
   [] → ∃[ ys ] ∃[ y ] xs ≡ ys ++ [ y ]`.
6. Prove the theorem `half : ∀(x : ℕ) → ∃[ y ] ∃[ z ] x ≡ y * 2 + z
   × (z ≡ 0 ⊎ z ≡ 1)`.

```
-- EXERCISE 1

pred' : ∀(x : ℕ) → x ≡ 0 ⊎ (∃[ y ] x ≡ suc y)
pred' zero     = inj₁ refl
pred' (suc x) = inj₂ (x , refl)

-- EXERCISE 2

ℕ₂ : Set
ℕ₂ = Σ ℕ λ x → x ≢ 0 × x ≢ 1

_ : ℕ₂
_ = 2 , (λ ()) , (λ ())

succ₂ : ℕ₂ → ℕ₂
succ₂ (x , nzero , none) = suc x , (λ ()) , λ { refl → nzero refl }

-- EXERCISE 3

∣-plus : ∀{x y z : ℕ} → x ∣ y → x ∣ z → x ∣ (y + z)
∣-plus {x} (u , refl) (v , refl) = u + v , *-distribʳ-+ x u v

-- EXERCISE 4

∣-not-total : ∃[ x ] ∃[ y ] ¬ (x ∣ y) × ¬ (y ∣ x)
∣-not-total = 2 , 3 , f , g
  where
    f : ¬ (2 ∣ 3)
    f (suc zero    , ())
    f (suc (suc _) , ())

    g : ¬ (3 ∣ 2)
    g (zero  , ())
    g (suc _ , ())

-- EXERCISE 5

last-view : ∀{A : Set} (xs : List A) → xs ≢ [] → ∃[ ys ] ∃[ y ] xs ≡ ys ++ [ y ]
last-view []           nempty = contradiction refl nempty
last-view (x ∷ [])     nempty = [] , x , refl
last-view (x ∷ z ∷ xs) nempty with last-view (z ∷ xs) (λ ())
... | ys , y , eq = x ∷ ys , y , cong (x ∷_) eq

-- EXERCISE 6

half : ∀(x : ℕ) → ∃[ y ] ∃[ z ] x ≡ y * 2 + z × (z ≡ 0 ⊎ z ≡ 1)
half zero           = 0 , 0 , refl , inj₁ refl
half (suc zero)     = 0 , 1 , refl , inj₂ refl
half (suc (suc x)) with half x
... | y , z , eq , zr = suc y , z , cong (suc ∘ suc) eq , zr
```
{:.solution}
