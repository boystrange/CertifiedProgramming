---
title: Inductive families and vectors
prev:  Chapter.Intro.Lists
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}
```
-->

```
module Chapter.Intro.Vectors where
```

...

## Imports

```
open import Function using (_∘_; flip)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-suc; +-identityʳ)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
```

## Data types with indices

The `List A` data type has a type parameter `A` that specifies the
type of the elements of the list. In a **parametric** data type such
as `List A`, the parameters are uniform in the types of the
constructors. For example, `[]` has type `List A` and `_∷_` has type
`A -> List A -> List A`. Note how the paramtere is always `A`,
independently of the constructor. In addition to parameters, a data
type may also contain **indices**. Unlike parameters, the indices
may depend on the specific constructor used to build a term of the
data type. A typical example of indexed data type is that of lists
of a specific length $n$, where $n$ is an index of the data type. We
call such lists **vectors**.

We can define the data type `Vec A n` of vectors with elements of
type `A` and length `n` thus:

```
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)
```

According to this definition, `Vec` has a parameter `A` indicating
the type of the elements it contains. Also, `Vec A` is *not* a type,
but rather a function of type `ℕ → Set`, that is a function yielding
a type when applied to a natural number. This number is an index
used to indicate the length of the vector.

Similarly to lists, we build vectors using the constructors `[]` and
`_∷_`. When we use `[]` we are building a vector with no elements,
hence the type of the vector is `Vec A 0`. When we use `_∷_`, we are
creating a vector `x ∷ xs` of length `suc n` starting with the
element `x` (of type `A`) followed by a vector `xs` of length
`n`.

```
infixr 5 _∷_
```

For example, the following vectors contains the first four natural
numbers.

```
_ : Vec ℕ 4
_ = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
```

## Building vectors

As noted above, each constructor of vectors carries an implicit
argument `A` standing for the type of the elements of the list being
constructed. We have to bear this aspect in mind when we define
functions that manipulate lists. For example, the following function
creates a list containing a single element.

```
[_] : ∀{A : Set} -> A -> Vec A 1
[_] = _∷ []
```

Now we can write `[ 0 ]` for the list consisting of the sole element
`0` or `[ true ]` for the list consisting of the sole element
`true`. The type of the elements of these lists is inferred
automatically by Agda. If we want to write the implicit argument
explicitly, we have to resort to the prefix notation: `[_] {ℕ} 0` is
the singleton list made of `0` and `[_] {Bool} true` is the
singleton list made of `true`.

```
repeat : ∀{A} → (n : ℕ) → A → Vec A n
repeat zero    x = []
repeat (suc n) x = x ∷ repeat n x
```

Note the use of a dependent function type to bind the length `n` of
the desired vector in the type `Vec A n` of the vector.

## Operations on vectors

We define vector concatenation in a similar way as we did for list
concatenation. The key difference is that we are able to specify *in
the type* of the operation the property that relates the length of
the concatenation with that of the vectors being concatenated.

```
_++_ : ∀{A m n} -> Vec A m -> Vec A n -> Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
```

Just as in the case of `++` for lists, we stipulate that `++` is
right associative and has the same priority as `∷`.

```
infixr 5 _++_
```

If we have a vector of `n` vectors all of the same length `m`, we
can define a flattening (or concatenating) operation that creates a
single vector with all the contained elements, of the appropriate
length `n * m`. Note that the same definition would not work had we
chosen to use the index `m * n`, since the length of the resulting
vector is computed as `n` times the sum of `m` rather than `m` times
the sum of `n`.

```
concat : ∀{A m n} → Vec (Vec A m) n → Vec A (n * m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss
```

We conclude this section with two additional (and common) functions
on vectors, where we see once again the role of the index as a
specification of some property of the function. The first function
uniformly transforms each element of a vector by means of a provided
function. The length `n` of the resulting vector matches that of the
original one.

```
map : ∀{A B n} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs
```

The next function can be used to *combine* element-wise two vectors,
provided that they have the same length `n`. In this case, the index
specifies both a requirement on the vectors provided as arguments
(the fact that they must have the same length) as well as a
guarantee on the result (which is a vector of length `n`).

```
zip-with : ∀{A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zip-with f [] [] = []
zip-with f (x ∷ xs) (y ∷ ys) = f x y ∷ zip-with f xs ys
```

## Reversing a vector

We now address the problem of reversing a vector. As we will see,
this operation turns out to be more difficult to implement because
of the additional information in the type of the vector being
reversed. At first we might be tempted to use the same code that we
have already defined for reversing a list:

```
broken-reverse : ∀{A n} → Vec A n → Vec A n
broken-reverse []       = []
broken-reverse (x ∷ xs) = {!!} -- broken-reverse xs ++ [ x ]
```

If we try to fill the hole with the commented expression Agda
complains about a mismatch of the form `n + m != suc n of type ℕ` in
the second equation. In order to understand this message, we have to
think carefully at what we are trying to achieve in this particular
case: we have established that the vector to be reversed has the
form `x ∷ xs`, therefore its type must be `Vec A (suc n)` for some
suitable `n` and we are supposed to produce a vector *of the same
type, with the same index `suc n`*. By itself, the expression
`broken-reverse xs ++ [ x ]` is perfectly reasonable and also well
typed. If we recall the type we gave to `_++_` above, we establish
that its type is `Vec A (n + 1)` and here lies the problem. For
Agda, the type `Vec A (suc n)` is not (definitionally) equal to the
type `Vec A (n + 1)` because the index `n + 1` is not the same as
the index `suc n`.

There are several ways to work around this issue; here we discuss
three of them. The first possibility is to define an *ad hoc*
operator `∷ʳ` to append a single element `x` at the end of a vector
of length `n`, yielding a vector of length `suc n`. Such operator
could be defined thus:

```
_∷ʳ_ : ∀{A n} → Vec A n → A → Vec A (suc n)
[]       ∷ʳ x = [ x ]
(y ∷ ys) ∷ʳ x = y ∷ (ys ∷ʳ x)
```

Then we could define a well-typed version of `reverse` thus:

```
reverse₁ : ∀{A n} → Vec A n → Vec A n
reverse₁ []       = []
reverse₁ (x ∷ xs) = reverse₁ xs ∷ʳ x
```

Another possibility is to convince Agda that `n + 1` is indeed
(propositionally) equal to `suc n`, and therefore that the
expression `broken-reverse xs ++ [ x ]` has the right type to be
used in the second equation of `broken-reverse`. We do so by using
an explicit *substitution*, which is akin to a "cast" in other
programming languages with the difference that we have to provide
evidence of the equivalence of two types. Such substitution is
implemented by a function `subst`. For the sake of illustration, it
may be useful to see a particular instantiation of the type of
`subst`, which we rename as `cast` for readability.

```
cast : ∀{I : Set} (F : I → Set) {x y : I} → x ≡ y → F x → F y
cast = subst
```

In words, `cast` (and therefore `subst`) accepts a function `F` from
`I` to `Set`, that is an indexed family, a proof that `x` and `y`
(of type `I`) are propositionally equal, and a term of type `F x` to
produce a term of type `F y`. In our case, these ingredients are
spelled out as follows:

* `I` is ℕ, that is the type of indices for `Vec`.
* `F` is `Vec A`, that is a function that accepts an index `n` and
  yields the type of vectors of length `n` with elements of type
  `A`.
* `x` and `y` are respectively the expressions `n + 1` and `suc
  n`. The expression `n + 1` is the index in the type of the
  expression that we are able to write, whereas the expression `suc
  n` is the index in the type expected by Agda.
* There are various ways in which we can provide a proof that `n + 1
  ≡ suc n`. One example is `+-comm n 1`.
* `F x` is the expression `broken-reverse xs ++ [ x ]`, whose type
  is `Vec A (n + 1)`.

Using `cast` (or equivalently `subst`) we can then obtain another
well-typed version of `reverse` thus:

```
reverse₂ : ∀{A n} → Vec A n → Vec A n
reverse₂ []       = []
reverse₂ (x ∷ xs) = cast (Vec _) (+-comm _ 1) (reverse₂ xs ++ [ x ])
```

Note that we have used underscores `_` in two places where Agda is
able to infer automatically from the context the missing parts. In
this way we avoid binding the implicit arguments `A` and `n` and
obtain a more streamlined definition.

The final solution we discuss corresponds to the efficient reverse
function we have seen for lists. We start by defining an auxiliary
function `reverse-onto`, thus:

```
reverse-onto : ∀{A m n} → Vec A m → Vec A n → Vec A (n + m)
reverse-onto ys []       = ys
reverse-onto ys (x ∷ xs) = cast (Vec _) (+-suc _ _) (reverse-onto (x ∷ ys) xs)
```

Note that we need to use a cast: in the second equation, Agda
expects us to provide an expression of type `Vec A (suc n + m)`, but
the expression `reverse-onto (x ∷ ys) xs` has type `Vec A (n + suc
m)`. We use `+-suc` to witness the equality `n + suc m ≡ suc n +
m`. Now we can obtain the efficient implementation of `reverse` for
vector thus:

```
reverse₃ : ∀{A n} → Vec A n → Vec A n
reverse₃ xs = cast (Vec _) (+-identityʳ _) (reverse-onto [] xs)
```

Here too we need a cast, because `reverse-onto [] xs` is an
expression of type `Vec A (n + 0)`, while we need an expression of
type `Vec A n`.

<!--
```
foldl : ∀{A n} (B : ℕ → Set) → (∀{n} → B n → A → B (suc n)) → B zero → Vec A n → B n
foldl B _⊕_ e []       = e
foldl B _⊕_ e (x ∷ xs) = foldl (B ∘ suc) _⊕_ (e ⊕ x) xs

reverse : ∀{A : Set} {n : ℕ} -> Vec A n -> Vec A n
reverse xs = foldl (Vec _) (λ xs x → x ∷ xs) [] xs
```
-->

## Exercises

1. Define the scalar product `_·_ : ∀{n} → Vec ℕ n → Vec ℕ n → ℕ` of
   two vectors of the same length.
2. Define `Mat : ℕ → ℕ → Set` so that `Mat m n` is the type of $m
   \times n$ matrices represented as vectors of vectors.
3. Define a function `identity : (n : ℕ) → Mat n n` that builds the
   `n × n` identity matrix.
4. Without using recursion, define a function `add : ∀{m n} → Mat m
   n → Mat m n → Mat m n` to add two matrices of the same shape.
5. Define a function `transpose : ∀{m n} → Mat m n → Mat n m` to
   transpose a matrix.
6. Without using recursion, define a function `_×_` to multiply two
   matrices. Give this function an appropriate type to make sure
   that the matrices being multiplied have compatible shapes.

```
-- EXERCISE 1

_·_ : ∀{n} → Vec ℕ n → Vec ℕ n → ℕ
[]       · []       = 0
(x ∷ xs) · (y ∷ ys) = x * y + (xs · ys)

-- EXERCISE 2

Mat : ℕ → ℕ → Set
Mat m n = Vec (Vec ℕ n) m

-- EXERCISE 3

identity : (n : ℕ) → Mat n n
identity zero    = []
identity (suc n) = (1 ∷ repeat n 0) ∷ map (0 ∷_) (identity n)

-- EXERCISE 4

add : ∀{m n} → Mat m n → Mat m n → Mat m n
add = zip-with (zip-with _+_)

-- EXERCISE 5

transpose : ∀{m n} → Mat m n → Mat n m
transpose {_} {n} []       = repeat n []
transpose         (xs ∷ M) = zip-with _∷_ xs (transpose M)

-- EXERCISE 6

_×_ : ∀{m n o} → Mat m n → Mat n o → Mat m o
M × N = map (λ r → map (r ·_) (transpose N)) M
```
{:.solution}
