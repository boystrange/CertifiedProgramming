---
title: Types and functions
next:  Chapter.Intro.Bool
---

<pre class="Agda"><a id="67" class="Keyword">module</a> <a id="74" href="Chapter.Intro.Lambda.html" class="Module">Chapter.Intro.Lambda</a> <a id="95" class="Keyword">where</a>
</pre>
## Imports

To try out the examples discussed in this chapter and to solve the
proposed exercises it is necessary to import the `Data.Nat` module,
which defines the natural numbers and some basic operations on
them. We will see how natural numbers are defined in a future
chapter. For the time being, we simply import the module and make
its content accessible by means of the following clause.

<pre class="Agda"><a id="506" class="Keyword">open</a> <a id="511" class="Keyword">import</a> <a id="518" href="Data.Nat.html" class="Module">Data.Nat</a>
</pre>
## Simple types

Agda is a strongly typed programming language and every term of the
language must be **well typed** in order to be considered by
Agda. For now we only consider a small set of **simple types**:

* `ℕ` stands for the type of **natural numbers**;
* if `A` and `B` are types, then `(A -> B)` is the type of
  **functions** that, when applied to an argument of type `A`, yield a
  result of type `B`.

To limit the amount of parentheses we have to write in types and to
improve readability, we adopt the following conventions:

* we omit topmost parentheses, so that `A -> B` stands for `(A -> B)`;
* we assume that `->` associates to the **right**, so that e.g. `A
  -> B -> C` stands for `A -> (B -> C)` and not for `(A -> B) -> C`.

## Defining functions

An Agda function is written as a term of the form `λ (x : A) -> M`
where

* `x` is the **name of the argument** of the function;
* `A` is the **type of the argument** of the function;
* `M` is the **body** of the function, namely the expression that
  computes the result of applying the function to its argument.

Below are a few simple examples of functions that make use of types
and operators defined in the `Data.Nat` module:

* `λ (x : ℕ) -> x` is the identity function for natural numbers;
* `λ (x : ℕ) -> x + 1` is the successor function for natural numbers;
* `λ (x : ℕ) -> x ^ 2 + 1` is the function that, applied to a
  natural number $x$, computes $x^2 + 1$.

All of these functions have type `ℕ -> ℕ` since they accept a
natural number as argument (the `ℕ` to the lhs of `->`) and produce
a natural number as result (the `ℕ` to the rhs of `->`).  The type
annotation of the argument can be omitted when its type can be
inferred from the context. For example, since the `+` and `^`
operators defined in the `Data.Nat` module can only be applied to
natural numbers, the last two functions above can be more concisely
written as `λ x -> x + 1` and `λ x -> x ^ 2 + 1` respectively. We
can verify this by asking Agda to compute the type of these
functions. This is achieved by typing `C-c C-d` followed by the
function (more generally the term) for which we want Agda to infer
the type.

All the examples above define **anonymous functions**, functions
without a name that are defined "on the spot", wherever we need. It
if often convenient to give names to functions, especially if we
plan to apply them multiple times or if we want to make them
available in a library or a complex Agda development. In an Agda
**program** we can use **definitions** to give names to terms and to
specify their type. For example, the program containing the
following two lines specify that `f` is a function of type `ℕ -> ℕ`
that maps $x$ to $x^2 + 1$:

<pre class="Agda"><a id="f"></a><a id="3253" href="Chapter.Intro.Lambda.html#3253" class="Function">f</a> <a id="3255" class="Symbol">:</a> <a id="3257" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="3259" class="Symbol">-&gt;</a> <a id="3262" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="3264" href="Chapter.Intro.Lambda.html#3253" class="Function">f</a> <a id="3266" class="Symbol">=</a> <a id="3268" class="Symbol">λ</a> <a id="3270" href="Chapter.Intro.Lambda.html#3270" class="Bound">x</a> <a id="3272" class="Symbol">-&gt;</a> <a id="3275" href="Chapter.Intro.Lambda.html#3270" class="Bound">x</a> <a id="3277" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="3279" class="Number">2</a> <a id="3281" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="3283" class="Number">1</a>
</pre>
The first line provides the **signature** of `f`. Top-level
definitions like this one must always be accompanied by a
signature. The second line provides the **definition** of `f` with
which we establish that the name `f` is **definitionally** the same
as the abstraction `λ x -> x ^ 2 + 1`. That is, for Agda the name
`f` and the term `λ x -> x ^ 2 + 1` are **equal**. Note that we omit
the type of the argument `x` for this abstraction, since Agda is
able to figure out that `x` has type `ℕ` from both the signature of
`f` and the fact that the operators `^` and `+` concern natural
numbers. Speaking of these operators, in definitions like this it is
possible to *click* on any colored symbol to reach its definition.

By loading the program using `C-c C-l`, Agda verifies that `f` is
well typed and that its type is consistent with the one provided in
its signature. Once this is done, we can use again `C-c C-d` to
verify that `f` has type `ℕ -> ℕ`.

When defining functions, Agda provides an alternative, more
convenient notation with which argument and body of the function are
separated by the symbol `=` . For example, an equivalent way of
defining `f` is

<pre class="Agda"><a id="f₁"></a><a id="4460" href="Chapter.Intro.Lambda.html#4460" class="Function">f₁</a> <a id="4463" class="Symbol">:</a> <a id="4465" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="4467" class="Symbol">-&gt;</a> <a id="4470" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="4472" href="Chapter.Intro.Lambda.html#4460" class="Function">f₁</a> <a id="4475" href="Chapter.Intro.Lambda.html#4475" class="Bound">x</a> <a id="4477" class="Symbol">=</a> <a id="4479" href="Chapter.Intro.Lambda.html#4475" class="Bound">x</a> <a id="4481" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="4483" class="Number">2</a> <a id="4485" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4487" class="Number">1</a>
</pre>
which can be read as "`f₁` applied to `x` is equal to `x ^ 2 +
1`". We have named this alternative definition of the function `f₁`
instead of `f` to avoid a *name clash*: there cannot be two
definitions with the same name in the same Agda file. Here and in
the following we will use indices whenever we need to provide
multiple versions of the same definition.

## Applying functions

Applying a function `M` to an argument `N` is achieved simply by
placing `M` and `N` next to each other, usually separated by one
space. For example, the expression `f 2` means the application of
`f` (defined above) to the natural number `2`. We can evaluate this
application by entering `C-c C-n f 2`, with which we obtain `5` as
result. The command `C-c C-n` asks Agda to *evaluate* (technically,
to *normalize*), the provided expression.

Agda is a strongly typed language, in the sense that it only
considers (and evaluates) terms that are **well typed** according to
a specific set of **typing rules**. We will not describe Agda's
typing rules in detail. For the time being, the following informal
statements explain when a function and an application are well
typed:

* If `M` is a term of type `B` under the assumption that `x` has
  type `A`, then `λ (x : A) -> M` is a term of type `A -> B`;
* If `M` is a term of type `A -> B` and `N` is a term of type `A`,
  then `M N` is a term of type `B`.

In order to limit the use of parentheses and improve readability, in
the following we will make extensive use of some (standard)
conventions concerning function definitions and applications:

* We will omit the type of an argument when it is unimportant or
  clear from the context.
* We will often collapse nested functions into one, so that e.g. `λ
  x y z -> M` stands for `λ x -> λ y -> λ z -> M`.
* We will assume that the body of a function extends as much as
  possible to the right. For example, `λ x y -> x y` stands for `λ x
  y -> (x y)` and not for `(λ x y -> x) y`.
* We will assume that application is **left associative**, so that
  `M₁ M₂ M₃` stands for `(M₁ M₂) M₃` and not for `M₁ (M₂ M₃)`.

We will introduce new terms in the following chapters. For the time
being, since we have imported the `Data.Nat` module from the
library, a number of terms defined therein are also available. In
particular:

* `zero` of type `ℕ` represents the natural number zero;
* `suc` of type `ℕ -> ℕ` is a function that, applied to a natural
  number, yields its successor.
* `_+_` of type `ℕ -> ℕ -> ℕ` is the function such that `_+_ M N`
  adds `M` and `N`. We often write this application in the usual
  infix notation `M + N`.
* `_^_` of type `ℕ -> ℕ -> ℕ` is the function such that `_^_ M N`
  computes `M` to the power `N`. We often write this application in
  the infix notation `M ^ N`.

The usual positional notation for natural numbers is also available,
so that `0` can be used as abbreviation for `zero`, `2` can be used
for abbreviation for `(suc (suc zero))` and `42` can be used for
abbreviation for 42 applications of `suc` to `zero`.

Finally, a note on **spacing** in Agda: unlike most programming
languages, Agda allows almost any character to be part of an
identifier. For example, `^` and `+` are plain Agda identifiers just
like `f` and `ℕ`. If we write `x^2` (without spaces around `^`),
Agda considers this as a single identifier (for which there is no
definition).

## Multi-argument and higher-order functions

Strictly speaking, all Agda functions have exactly one argument. The
usual way of representing multi-argument functions in a functional
language like Agda is by means of functions that yield other
functions as result. For example, `g` below is defined as a function
that maps $x$ to a function that maps $y$ to $x^2 + 2xy + 1$.

<pre class="Agda"><a id="g"></a><a id="8253" href="Chapter.Intro.Lambda.html#8253" class="Function">g</a> <a id="8255" class="Symbol">:</a> <a id="8257" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8259" class="Symbol">-&gt;</a> <a id="8262" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8264" class="Symbol">-&gt;</a> <a id="8267" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="8269" href="Chapter.Intro.Lambda.html#8253" class="Function">g</a> <a id="8271" class="Symbol">=</a> <a id="8273" class="Symbol">λ</a> <a id="8275" href="Chapter.Intro.Lambda.html#8275" class="Bound">x</a> <a id="8277" class="Symbol">-&gt;</a> <a id="8280" class="Symbol">λ</a> <a id="8282" href="Chapter.Intro.Lambda.html#8282" class="Bound">y</a> <a id="8284" class="Symbol">-&gt;</a> <a id="8287" href="Chapter.Intro.Lambda.html#8275" class="Bound">x</a> <a id="8289" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="8291" class="Number">2</a> <a id="8293" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="8295" class="Number">2</a> <a id="8297" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="8299" href="Chapter.Intro.Lambda.html#8275" class="Bound">x</a> <a id="8301" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="8303" href="Chapter.Intro.Lambda.html#8282" class="Bound">y</a> <a id="8305" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="8307" class="Number">1</a>
</pre>
Equivalently, `g` can be written as follows:

<pre class="Agda"><a id="g₁"></a><a id="8364" href="Chapter.Intro.Lambda.html#8364" class="Function">g₁</a> <a id="8367" class="Symbol">:</a> <a id="8369" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8371" class="Symbol">-&gt;</a> <a id="8374" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8376" class="Symbol">-&gt;</a> <a id="8379" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="8381" href="Chapter.Intro.Lambda.html#8364" class="Function">g₁</a> <a id="8384" href="Chapter.Intro.Lambda.html#8384" class="Bound">x</a> <a id="8386" href="Chapter.Intro.Lambda.html#8386" class="Bound">y</a> <a id="8388" class="Symbol">=</a> <a id="8390" href="Chapter.Intro.Lambda.html#8384" class="Bound">x</a> <a id="8392" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="8394" class="Number">2</a> <a id="8396" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="8398" class="Number">2</a> <a id="8400" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="8402" href="Chapter.Intro.Lambda.html#8384" class="Bound">x</a> <a id="8404" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="8406" href="Chapter.Intro.Lambda.html#8386" class="Bound">y</a> <a id="8408" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="8410" class="Number">1</a>
</pre>
We can use `C-c C-n` to verify that `g 2 3` evaluates to `17`. Since
function application is left associative, `g 2 3` is the same as `(g
2) 3`. That is, we first apply `g` to `2` to obtain the function

    λ y -> 2 ^ 2 + 2 * 2 * y + 1

and then we apply this function to `3`, to obtain
`2 ^ 2 + 2 * 2 * 3 + 1` that is `17`.

As in most functional programming languages, functions are
first-class entities that can be provided as arguments and returned
as results of other functions. For example, the function

<pre class="Agda"><a id="twice"></a><a id="8933" href="Chapter.Intro.Lambda.html#8933" class="Function">twice</a> <a id="8939" class="Symbol">:</a> <a id="8941" class="Symbol">(</a><a id="8942" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8944" class="Symbol">-&gt;</a> <a id="8947" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="8948" class="Symbol">)</a> <a id="8950" class="Symbol">-&gt;</a> <a id="8953" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8955" class="Symbol">-&gt;</a> <a id="8958" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="8960" href="Chapter.Intro.Lambda.html#8933" class="Function">twice</a> <a id="8966" href="Chapter.Intro.Lambda.html#8966" class="Bound">f</a> <a id="8968" href="Chapter.Intro.Lambda.html#8968" class="Bound">x</a> <a id="8970" class="Symbol">=</a> <a id="8972" href="Chapter.Intro.Lambda.html#8966" class="Bound">f</a> <a id="8974" class="Symbol">(</a><a id="8975" href="Chapter.Intro.Lambda.html#8966" class="Bound">f</a> <a id="8977" href="Chapter.Intro.Lambda.html#8968" class="Bound">x</a><a id="8978" class="Symbol">)</a>
</pre>
applied to a function `f` and an argument `x` applies `f` to `x`
twice. Evaluating `twice f 2` where `f` is the function defined
above yields `26`.

## Exercises

1. Define at least six different versions of the function that
   computes the successor of a natural number.
2. Define a function `poly₁` that, applied to a natural number $x$,
   yields $2x^2$.
3. Define a function `poly₂` that, applied to two natural numbers
   $x$ and $y$, yields $2(x^3 + y^2)$.
4. Which of the following terms are well typed? Use Agda to verify
   whether your answers are correct.
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ -> ℕ) -> x y`
   * `λ (x : (ℕ -> ℕ) -> ℕ) (y : ℕ) -> x y`
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x x y`
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x (x y)`
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x y y`

<pre class="Agda"><a id="9783" class="Comment">-- EXERCISE 1</a>

<a id="suc₁"></a><a id="9798" href="Chapter.Intro.Lambda.html#9798" class="Function">suc₁</a> <a id="9803" class="Symbol">:</a> <a id="9805" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9807" class="Symbol">-&gt;</a> <a id="9810" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9812" href="Chapter.Intro.Lambda.html#9798" class="Function">suc₁</a> <a id="9817" class="Symbol">=</a> <a id="9819" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a>

<a id="suc₂"></a><a id="9824" href="Chapter.Intro.Lambda.html#9824" class="Function">suc₂</a> <a id="9829" class="Symbol">:</a> <a id="9831" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9833" class="Symbol">-&gt;</a> <a id="9836" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9838" href="Chapter.Intro.Lambda.html#9824" class="Function">suc₂</a> <a id="9843" href="Chapter.Intro.Lambda.html#9843" class="Bound">x</a> <a id="9845" class="Symbol">=</a> <a id="9847" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="9851" href="Chapter.Intro.Lambda.html#9843" class="Bound">x</a>

<a id="suc₃"></a><a id="9854" href="Chapter.Intro.Lambda.html#9854" class="Function">suc₃</a> <a id="9859" class="Symbol">:</a> <a id="9861" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9863" class="Symbol">-&gt;</a> <a id="9866" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9868" href="Chapter.Intro.Lambda.html#9854" class="Function">suc₃</a> <a id="9873" class="Symbol">=</a> <a id="9875" class="Symbol">λ</a> <a id="9877" href="Chapter.Intro.Lambda.html#9877" class="Bound">x</a> <a id="9879" class="Symbol">-&gt;</a> <a id="9882" href="Chapter.Intro.Lambda.html#9877" class="Bound">x</a> <a id="9884" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="9886" class="Number">1</a>

<a id="suc₄"></a><a id="9889" href="Chapter.Intro.Lambda.html#9889" class="Function">suc₄</a> <a id="9894" class="Symbol">:</a> <a id="9896" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9898" class="Symbol">-&gt;</a> <a id="9901" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9903" href="Chapter.Intro.Lambda.html#9889" class="Function">suc₄</a> <a id="9908" class="Symbol">=</a> <a id="9910" class="Symbol">λ</a> <a id="9912" href="Chapter.Intro.Lambda.html#9912" class="Bound">x</a> <a id="9914" class="Symbol">-&gt;</a> <a id="9917" class="Number">1</a> <a id="9919" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="9921" href="Chapter.Intro.Lambda.html#9912" class="Bound">x</a>

<a id="suc₅"></a><a id="9924" href="Chapter.Intro.Lambda.html#9924" class="Function">suc₅</a> <a id="9929" class="Symbol">:</a> <a id="9931" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9933" class="Symbol">-&gt;</a> <a id="9936" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9938" href="Chapter.Intro.Lambda.html#9924" class="Function">suc₅</a> <a id="9943" href="Chapter.Intro.Lambda.html#9943" class="Bound">x</a> <a id="9945" class="Symbol">=</a> <a id="9947" href="Chapter.Intro.Lambda.html#9943" class="Bound">x</a> <a id="9949" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="9951" class="Number">1</a>

<a id="suc₆"></a><a id="9954" href="Chapter.Intro.Lambda.html#9954" class="Function">suc₆</a> <a id="9959" class="Symbol">:</a> <a id="9961" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9963" class="Symbol">-&gt;</a> <a id="9966" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9968" href="Chapter.Intro.Lambda.html#9954" class="Function">suc₆</a> <a id="9973" href="Chapter.Intro.Lambda.html#9973" class="Bound">x</a> <a id="9975" class="Symbol">=</a> <a id="9977" class="Number">1</a> <a id="9979" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="9981" href="Chapter.Intro.Lambda.html#9973" class="Bound">x</a>

<a id="9984" class="Comment">-- EXERCISE 2</a>

<a id="poly₂"></a><a id="9999" href="Chapter.Intro.Lambda.html#9999" class="Function">poly₂</a> <a id="10005" class="Symbol">:</a> <a id="10007" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="10009" class="Symbol">-&gt;</a> <a id="10012" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="10014" href="Chapter.Intro.Lambda.html#9999" class="Function">poly₂</a> <a id="10020" href="Chapter.Intro.Lambda.html#10020" class="Bound">x</a> <a id="10022" class="Symbol">=</a> <a id="10024" class="Number">2</a> <a id="10026" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="10028" href="Chapter.Intro.Lambda.html#10020" class="Bound">x</a> <a id="10030" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="10032" class="Number">2</a>

<a id="poly₃"></a><a id="10035" href="Chapter.Intro.Lambda.html#10035" class="Function">poly₃</a> <a id="10041" class="Symbol">:</a> <a id="10043" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="10045" class="Symbol">-&gt;</a> <a id="10048" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="10050" class="Symbol">-&gt;</a> <a id="10053" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="10055" href="Chapter.Intro.Lambda.html#10035" class="Function">poly₃</a> <a id="10061" href="Chapter.Intro.Lambda.html#10061" class="Bound">x</a> <a id="10063" href="Chapter.Intro.Lambda.html#10063" class="Bound">y</a> <a id="10065" class="Symbol">=</a> <a id="10067" class="Number">2</a> <a id="10069" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="10071" class="Symbol">(</a><a id="10072" href="Chapter.Intro.Lambda.html#10061" class="Bound">x</a> <a id="10074" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="10076" class="Number">3</a> <a id="10078" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="10080" href="Chapter.Intro.Lambda.html#10063" class="Bound">y</a> <a id="10082" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="10084" class="Number">2</a><a id="10085" class="Symbol">)</a>
</pre>{:.solution}
