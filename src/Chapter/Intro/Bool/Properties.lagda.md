---
title: Proving properties of Booleans
next:  Chapter.Intro.NaturalNumbers
prev:  Chapter.Intro.Bool
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}
```
-->

```
module Chapter.Intro.Bool.Properties where
```

In this section we start exploring the use of Agda not only as a
language for writing programs, but also as a language for writing
**proofs** about programs.

## Imports

We must be able to express **propositions**, namely assertions that
can be either "true" (if we are able to come up with a proof for
them) or "false" (if we are able to show that every proof of them
leads to a contradiction). In this chapter we will use
**propositional equality**. This relation is not built into Agda,
but is actually definable as a data type. For the time being, we
simply *use* the definition of propositional equality from the
standard library without looking at its definition. To this aim, we
*import* the `PropositionalEquality` module, along with the `Bool`
module which defines boolean values and functions/operators on them.

```
open import Data.Bool
open import Relation.Binary.PropositionalEquality
```

## Propositional equality

The first aspect we have to familiarize with is that, unlike the
equality operator that is commonly found in ordinary programming
languages, Agda's propositional equality `≡` allows us to build
*types*. More precisely, we can write types such as `true ≡ true`
and `true ≡ false` or, equivalently, `_≡_ true true` and `_≡_
true false`. An expression of type `true ≡ true` is meant to
represent a *proof* that `true` is equal to `true`, just like an
expression of type `false ≡ false` is meant to represent a *proof*
that `false` is equal to `false`. Understandably, we should be
unable to write expressions of type `true ≡ false` or `false ≡
true`, since `true` and `false` are distinct values of type `Bool`
which should be never identified.

The question now is what *is* a proof that `true` is equal to `true`
and, similarly, what is a proof that `false` is equal to
`false`. Recall that, when we have defined the `Bool` data type, we
have also listed all the *values* of type `Bool`, namely `true` and
`false`. In a similar fashion, the `_≡_` data type has a
constructor called `refl` (for *reflexivity*) which is a proof of
the fact that any value is equal to itself. We can use `refl` to
write our first theorem about boolean values, namely that `true` is
equal to `true`.

```
true-eq : true ≡ true
true-eq = refl
```

In a similar fashion, it is easy to prove that `false` is
equal to itself, again using the `refl` constructor:

```
false-eq : false ≡ false
false-eq = refl
```

In general, `refl` can be used to prove any equality of the form `v
≡ w` where `v` and `w` "are the same". In `true-eq` and `false-eq`
we have taken `v` and `w` to be syntactically the same term, which
resulted in somewhat obvious and rather uninteresting properties. In
general, Agda considers two expressions to be the same if they
evaluate to the same value (technically speaking, if they have the
same normal form). In the previous section we have seen the use of
`C-c C-n` to *normalize* an expression such as `not true`, which
yields `false`. So, `false` is the normal form of `not true`,
meaning that for Agda `not true` and `false` are actually
"equal". This leads to a more interesting result about the behavior
of `not`.

```
not-true-eq : not true ≡ false
not-true-eq = refl
```

Here too we use the `refl` constructor as a proof that `not true`
and `false` are equal. In order to accept this proof, Agda evaluates
`not true` and `false`. The second term is already in normal
form. The first term can be normalized using the definition of
`not`, according to which `not true` yields `false`. This is enough
to conclude that `not true` and `false` are equal.

## Proving that `not` is an involution

Let us now prove that `not` is an involution, namely that `not` is
the inverse function of itself. First of all we have to understand
how to formulate this property. In mathematics we would write the
following predicate:

    ∀(x : Bool) . not (not x) ≡ x

In Agda, we may state this property as the type

    ∀(x : Bool) -> not (not x) ≡ x

which describes a function that, when applied to a value `x` of type
`Bool`, yields a proof that `not (not x)` is equal to `x`. Unlike
the arrow types that we have used until now, this is an example of
**dependent function type** because the type of the codomain of the
function -- `not (not x) ≡ x` -- *depends* on the argument `x` to
which the function is applied. The `∀` symbol is purely cosmetic and
may be omitted. We will use it merely for readability.

Going back to our goal, proving that `not` is an involution is the
same as finding a function that has type `∀(x : Bool) -> not (not x)
≡ x`. That is, our goal is to fill the hole in the following
partial definition:

```
not-inv : ∀(x : Bool) -> not (not x) ≡ x
not-inv x = {!!}
```

By placing the cursor in the hole and hitting `C-c C-,` we see that
our goal is to provide an expression of type `not (not x) ≡ x`
having at our disposal a value `x` of type `Bool`. At this stage we
might be tempted to fill the hole with `refl`, just like we've done
before for `true-eq`, but if we try to do so Agda will complain with
an error message saying that `not (not x)` and `x` are not the
same. What happens here is that Agda tries to evaluate `not (not x)`
and `x` to see if they have the same normal form. However, since
both contain a variable `x`, which stands for an unknown boolean
value, Agda is unable to reduce these terms any further: `x` is in
normal form, `not (not x)` is in normal form and, for Agda, these
terms are far from being the same.  If `not` is applied to `true`,
then Agda knows that the result is `false`, and if `not` is applied
to `false`, then Agda knows that the result is `true`, but if `not`
is applied to some unknown boolean value `x`, the evaluation of `not
x` (and thus of `not (not x)` as well) is simply stuck.

To make some progress from here we have to recall that `not` has
been defined *by cases* on its argument. The idea then is to proceed
in a similar fashion also for the definition of `not-inv` by
performing a case analysis on `x`.

```
not-inv₁ : ∀(x : Bool) -> not (not x) ≡ x
not-inv₁ true  = {!!}
not-inv₁ false = {!!}
```

Just like in the definition of `not`, here too we end up with two
equations corresponding to the two possible forms for the argument
`x`. However, something interesting happens in the type of the
function: if we place the cursor in the first hole and hit `C-c C-,`
we see that the goal is now `true ≡ true` instead of `not (not
x)`. What has happened here is that the first hole corresponds to
the case in which `x` is `true`. In this case, Agda is able to
evaluate `not (not x)` to `true` using the definition of `not`. The
good news is that we are now able to provide the proof that `true`
is equal to `true`, that is just `true-eq`. A similar thing happens
for the second hole. In this case, Agda knows that `x` is `false`,
so the goal simplifies to `false ≡ false` for which `false-eq` is a
perfectly valid proof. We have thus completed our first proper
theorem in Agda:

```
not-inv₂ : ∀(x : Bool) -> not (not x) ≡ x
not-inv₂ true  = true-eq
not-inv₂ false = false-eq
```

Note that, since `true-eq` and `false-eq` are definitionally equal
to `refl`, we could have equivalently written `refl` on the right
hand side of the two equations in the definition of `not-inv₂`.

## Commutativity of `∧` and telescopes

We conclude this chapter with another simple proof concerning the
fact that `∧` is commutative, namely that `x ∧ y ≡ y ∧ x` for
every `x` and `y`.

```
∧-comm : ∀(x : Bool) -> ∀(y : Bool) -> x ∧ y ≡ y ∧ x
∧-comm true  true  = refl
∧-comm true  false = refl
∧-comm false true  = refl
∧-comm false false = refl
```

In this proof we have to perform two independent case analyses, one
for each argument of `∧-comm`. This happens because the `_∧_`
function is defined by case analysis on its first argument so, by
doing case analysis only on `x`, Agda is able to simplify the `x ∧
y` part of the goal but not the `y ∧ x` part. Symmetrically, by
doing case analysis only on `y`, Agda is able to simplify the `y ∧
x` part of the goal but not the `x ∧ y` part.

We take advantage of this example to illustrate some convenient
syntactic sugar that allows us to write more compact and more
readable types. From the type of `∧-comm` we see that `∧-comm` is
a function that, when applied to two arguments `x` and `y` of type
`Bool`, yields a proof that `x ∧ y ≡ y ∧ x`. In Agda it is not
necessary to write the `->` symbol to separate subsequent arguments
in a dependent function type. That is, the type of `∧-comm` can be
equivalently written as

    ∧-comm : ∀(x : Bool) (y : Bool) -> x ∧ y ≡ y ∧ x

Also, where there are multiple subsequent arguments of the same type
in a dependent function type we can collapse them together, like
this:

    ∧-comm : ∀(x y : Bool) -> x ∧ y ≡ y ∧ x

This is sometimes referred to as Agda's "telescopic notation". Note
that these types are totally equivalent and therefore
interchangeable.

## Exercises

1. Prove that `true` is both a left and a right unit for `∧`,
   namely that `true ∧ x ≡ x` and `x ∧ true ≡ x` for every
   `x`. Make sure to use case analysis on `x` only if necessary.
2. Prove that `∧` is associative, namely that `x ∧ (y ∧ z) ≡ (x
   ∧ y) ∧ z` for every `x`, `y` and `z`. Make sure to use the
   telescopic notation and case analysis only if necessary.
3. Prove De Morgan's laws for the boolean operators, namely that
   `not (x ∧ y) ≡ not x ∨ not y` and that `not (x ∨ y) ≡ not x
   ∧ not y`.

```
-- EXERCISE 1

-- when proving that x is a left unit for ∧ it is not necessary to
-- perform a case analysis on x because, according to the definition
-- of ∧, true ∧ x is the same as x

∧-unit-l : ∀(x : Bool) -> true ∧ x ≡ x
∧-unit-l x = refl

∧-unit-r : ∀(x : Bool) -> x ∧ true ≡ x
∧-unit-r true  = refl
∧-unit-r false = refl

-- EXERCISE 2

∧-assoc : ∀(x y z : Bool) -> x ∧ (y ∧ z) ≡ (x ∧ y) ∧ z
∧-assoc true y z = refl
∧-assoc false y z = refl

-- EXERCISE 3

not-∧ : ∀(x y : Bool) -> not (x ∧ y) ≡ not x ∨ not y
not-∧ true  _ = refl
not-∧ false _ = refl

not-∨ : ∀(x y : Bool) -> not (x ∨ y) ≡ not x ∧ not y
not-∨ true  _ = refl
not-∨ false _ = refl
```
{:.solution}
