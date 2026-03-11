---
title: Types and functions
next:  Chapter.Intro.Bool
---

<pre class="Agda"><a id="67" class="Keyword">module</a> <a id="74" href="Chapter.Intro.Lambda.html" class="Module">Chapter.Intro.Lambda</a> <a id="95" class="Keyword">where</a>
</pre>
## Imports

To try out the examples discussed in this chapter and to solve the
proposed exercises it is necessary to import the `Nat` module, which
defines the natural numbers and some basic operations on them. We
will see how natural numbers are defined in a [dedicated
chapter](Chapter.Intro.NaturalNumbers.html). For the time being, we
simply import the module and make its content accessible by means of
the following clause.

<pre class="Agda"><a id="541" class="Keyword">open</a> <a id="546" class="Keyword">import</a> <a id="553" href="Data.Nat.html" class="Module">Data.Nat</a>
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
and operators defined in the `Nat` module:

* `λ (x : ℕ) -> x` is the identity function for natural numbers;
* `λ (x : ℕ) -> x + 1` is the successor function for natural numbers;
* `λ (x : ℕ) -> x ^ 2 + 1` is the function that, applied to a
  natural number $x$, computes $x^2 + 1$.

All of these functions have type `ℕ -> ℕ` since they accept a
natural number as argument (the `ℕ` to the lhs of `->`) and produce
a natural number as result (the `ℕ` to the rhs of `->`).  The type
annotation of the argument can be omitted when its type can be
inferred from the context. For example, since the `+` and `^`
operators defined in the `Nat` module can only be applied to natural
numbers, the last two functions above can be more concisely written
as `λ x -> x + 1` and `λ x -> x ^ 2 + 1` respectively. We can verify
this by asking Agda to compute the type of these functions. This is
achieved by typing `C-c C-d` followed by the function (more
generally the term) for which we want Agda to infer the type.

All the examples above define **anonymous functions**, functions
without a name that are defined "on the spot", wherever we need. It
if often convenient to give names to functions, especially if we
plan to apply them multiple times or if we want to make them
available in a library or a complex Agda development. In an Agda
**program** we can use **definitions** to give names to terms and to
specify their type. For example, the program containing the
following two lines specify that `f` is a function of type `ℕ -> ℕ`
that maps $x$ to $x^2 + 1$:

<pre class="Agda"><a id="f"></a><a id="3278" href="Chapter.Intro.Lambda.html#3278" class="Function">f</a> <a id="3280" class="Symbol">:</a> <a id="3282" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="3284" class="Symbol">-&gt;</a> <a id="3287" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="3289" href="Chapter.Intro.Lambda.html#3278" class="Function">f</a> <a id="3291" class="Symbol">=</a> <a id="3293" class="Symbol">λ</a> <a id="3295" href="Chapter.Intro.Lambda.html#3295" class="Bound">x</a> <a id="3297" class="Symbol">-&gt;</a> <a id="3300" href="Chapter.Intro.Lambda.html#3295" class="Bound">x</a> <a id="3302" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="3304" class="Number">2</a> <a id="3306" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="3308" class="Number">1</a>
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

<pre class="Agda"><a id="f₁"></a><a id="4485" href="Chapter.Intro.Lambda.html#4485" class="Function">f₁</a> <a id="4488" class="Symbol">:</a> <a id="4490" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="4492" class="Symbol">-&gt;</a> <a id="4495" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="4497" href="Chapter.Intro.Lambda.html#4485" class="Function">f₁</a> <a id="4500" href="Chapter.Intro.Lambda.html#4500" class="Bound">x</a> <a id="4502" class="Symbol">=</a> <a id="4504" href="Chapter.Intro.Lambda.html#4500" class="Bound">x</a> <a id="4506" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="4508" class="Number">2</a> <a id="4510" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4512" class="Number">1</a>
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
being, since we have imported the `Nat` module from the library, a
number of terms defined therein are also available. In particular:

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

<pre class="Agda"><a id="g"></a><a id="8273" href="Chapter.Intro.Lambda.html#8273" class="Function">g</a> <a id="8275" class="Symbol">:</a> <a id="8277" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8279" class="Symbol">-&gt;</a> <a id="8282" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8284" class="Symbol">-&gt;</a> <a id="8287" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="8289" href="Chapter.Intro.Lambda.html#8273" class="Function">g</a> <a id="8291" class="Symbol">=</a> <a id="8293" class="Symbol">λ</a> <a id="8295" href="Chapter.Intro.Lambda.html#8295" class="Bound">x</a> <a id="8297" class="Symbol">-&gt;</a> <a id="8300" class="Symbol">λ</a> <a id="8302" href="Chapter.Intro.Lambda.html#8302" class="Bound">y</a> <a id="8304" class="Symbol">-&gt;</a> <a id="8307" href="Chapter.Intro.Lambda.html#8295" class="Bound">x</a> <a id="8309" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="8311" class="Number">2</a> <a id="8313" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="8315" class="Number">2</a> <a id="8317" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="8319" href="Chapter.Intro.Lambda.html#8295" class="Bound">x</a> <a id="8321" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="8323" href="Chapter.Intro.Lambda.html#8302" class="Bound">y</a> <a id="8325" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="8327" class="Number">1</a>
</pre>
Equivalently, `g` can be written as follows:

<pre class="Agda"><a id="g₁"></a><a id="8384" href="Chapter.Intro.Lambda.html#8384" class="Function">g₁</a> <a id="8387" class="Symbol">:</a> <a id="8389" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8391" class="Symbol">-&gt;</a> <a id="8394" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8396" class="Symbol">-&gt;</a> <a id="8399" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="8401" href="Chapter.Intro.Lambda.html#8384" class="Function">g₁</a> <a id="8404" href="Chapter.Intro.Lambda.html#8404" class="Bound">x</a> <a id="8406" href="Chapter.Intro.Lambda.html#8406" class="Bound">y</a> <a id="8408" class="Symbol">=</a> <a id="8410" href="Chapter.Intro.Lambda.html#8404" class="Bound">x</a> <a id="8412" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="8414" class="Number">2</a> <a id="8416" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="8418" class="Number">2</a> <a id="8420" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="8422" href="Chapter.Intro.Lambda.html#8404" class="Bound">x</a> <a id="8424" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="8426" href="Chapter.Intro.Lambda.html#8406" class="Bound">y</a> <a id="8428" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="8430" class="Number">1</a>
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

<pre class="Agda"><a id="twice"></a><a id="8953" href="Chapter.Intro.Lambda.html#8953" class="Function">twice</a> <a id="8959" class="Symbol">:</a> <a id="8961" class="Symbol">(</a><a id="8962" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8964" class="Symbol">-&gt;</a> <a id="8967" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="8968" class="Symbol">)</a> <a id="8970" class="Symbol">-&gt;</a> <a id="8973" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="8975" class="Symbol">-&gt;</a> <a id="8978" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="8980" href="Chapter.Intro.Lambda.html#8953" class="Function">twice</a> <a id="8986" href="Chapter.Intro.Lambda.html#8986" class="Bound">f</a> <a id="8988" href="Chapter.Intro.Lambda.html#8988" class="Bound">x</a> <a id="8990" class="Symbol">=</a> <a id="8992" href="Chapter.Intro.Lambda.html#8986" class="Bound">f</a> <a id="8994" class="Symbol">(</a><a id="8995" href="Chapter.Intro.Lambda.html#8986" class="Bound">f</a> <a id="8997" href="Chapter.Intro.Lambda.html#8988" class="Bound">x</a><a id="8998" class="Symbol">)</a>
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

<pre class="Agda"><a id="9803" class="Comment">-- EXERCISE 1</a>

<a id="suc₁"></a><a id="9818" href="Chapter.Intro.Lambda.html#9818" class="Function">suc₁</a> <a id="9823" class="Symbol">:</a> <a id="9825" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9827" class="Symbol">-&gt;</a> <a id="9830" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9832" href="Chapter.Intro.Lambda.html#9818" class="Function">suc₁</a> <a id="9837" class="Symbol">=</a> <a id="9839" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a>

<a id="suc₂"></a><a id="9844" href="Chapter.Intro.Lambda.html#9844" class="Function">suc₂</a> <a id="9849" class="Symbol">:</a> <a id="9851" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9853" class="Symbol">-&gt;</a> <a id="9856" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9858" href="Chapter.Intro.Lambda.html#9844" class="Function">suc₂</a> <a id="9863" href="Chapter.Intro.Lambda.html#9863" class="Bound">x</a> <a id="9865" class="Symbol">=</a> <a id="9867" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="9871" href="Chapter.Intro.Lambda.html#9863" class="Bound">x</a>

<a id="suc₃"></a><a id="9874" href="Chapter.Intro.Lambda.html#9874" class="Function">suc₃</a> <a id="9879" class="Symbol">:</a> <a id="9881" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9883" class="Symbol">-&gt;</a> <a id="9886" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9888" href="Chapter.Intro.Lambda.html#9874" class="Function">suc₃</a> <a id="9893" class="Symbol">=</a> <a id="9895" class="Symbol">λ</a> <a id="9897" href="Chapter.Intro.Lambda.html#9897" class="Bound">x</a> <a id="9899" class="Symbol">-&gt;</a> <a id="9902" href="Chapter.Intro.Lambda.html#9897" class="Bound">x</a> <a id="9904" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="9906" class="Number">1</a>

<a id="suc₄"></a><a id="9909" href="Chapter.Intro.Lambda.html#9909" class="Function">suc₄</a> <a id="9914" class="Symbol">:</a> <a id="9916" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9918" class="Symbol">-&gt;</a> <a id="9921" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9923" href="Chapter.Intro.Lambda.html#9909" class="Function">suc₄</a> <a id="9928" class="Symbol">=</a> <a id="9930" class="Symbol">λ</a> <a id="9932" href="Chapter.Intro.Lambda.html#9932" class="Bound">x</a> <a id="9934" class="Symbol">-&gt;</a> <a id="9937" class="Number">1</a> <a id="9939" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="9941" href="Chapter.Intro.Lambda.html#9932" class="Bound">x</a>

<a id="suc₅"></a><a id="9944" href="Chapter.Intro.Lambda.html#9944" class="Function">suc₅</a> <a id="9949" class="Symbol">:</a> <a id="9951" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9953" class="Symbol">-&gt;</a> <a id="9956" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9958" href="Chapter.Intro.Lambda.html#9944" class="Function">suc₅</a> <a id="9963" href="Chapter.Intro.Lambda.html#9963" class="Bound">x</a> <a id="9965" class="Symbol">=</a> <a id="9967" href="Chapter.Intro.Lambda.html#9963" class="Bound">x</a> <a id="9969" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="9971" class="Number">1</a>

<a id="suc₆"></a><a id="9974" href="Chapter.Intro.Lambda.html#9974" class="Function">suc₆</a> <a id="9979" class="Symbol">:</a> <a id="9981" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="9983" class="Symbol">-&gt;</a> <a id="9986" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="9988" href="Chapter.Intro.Lambda.html#9974" class="Function">suc₆</a> <a id="9993" href="Chapter.Intro.Lambda.html#9993" class="Bound">x</a> <a id="9995" class="Symbol">=</a> <a id="9997" class="Number">1</a> <a id="9999" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="10001" href="Chapter.Intro.Lambda.html#9993" class="Bound">x</a>

<a id="10004" class="Comment">-- EXERCISE 2</a>

<a id="poly₂"></a><a id="10019" href="Chapter.Intro.Lambda.html#10019" class="Function">poly₂</a> <a id="10025" class="Symbol">:</a> <a id="10027" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="10029" class="Symbol">-&gt;</a> <a id="10032" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="10034" href="Chapter.Intro.Lambda.html#10019" class="Function">poly₂</a> <a id="10040" href="Chapter.Intro.Lambda.html#10040" class="Bound">x</a> <a id="10042" class="Symbol">=</a> <a id="10044" class="Number">2</a> <a id="10046" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="10048" href="Chapter.Intro.Lambda.html#10040" class="Bound">x</a> <a id="10050" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="10052" class="Number">2</a>

<a id="poly₃"></a><a id="10055" href="Chapter.Intro.Lambda.html#10055" class="Function">poly₃</a> <a id="10061" class="Symbol">:</a> <a id="10063" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="10065" class="Symbol">-&gt;</a> <a id="10068" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="10070" class="Symbol">-&gt;</a> <a id="10073" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="10075" href="Chapter.Intro.Lambda.html#10055" class="Function">poly₃</a> <a id="10081" href="Chapter.Intro.Lambda.html#10081" class="Bound">x</a> <a id="10083" href="Chapter.Intro.Lambda.html#10083" class="Bound">y</a> <a id="10085" class="Symbol">=</a> <a id="10087" class="Number">2</a> <a id="10089" href="Agda.Builtin.Nat.html#539" class="Primitive Operator">*</a> <a id="10091" class="Symbol">(</a><a id="10092" href="Chapter.Intro.Lambda.html#10081" class="Bound">x</a> <a id="10094" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="10096" class="Number">3</a> <a id="10098" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="10100" href="Chapter.Intro.Lambda.html#10083" class="Bound">y</a> <a id="10102" href="Data.Nat.Base.html#6567" class="Function Operator">^</a> <a id="10104" class="Number">2</a><a id="10105" class="Symbol">)</a>
</pre>{:.solution}
