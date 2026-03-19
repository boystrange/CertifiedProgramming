---
title: Proving properties of Booleans
next:  Chapter.Intro.NaturalNumbers
prev:  Chapter.Intro.Bool
---

<!--
<pre class="Agda"><a id="119" class="Symbol">{-#</a> <a id="123" class="Keyword">OPTIONS</a> <a id="131" class="Pragma">--allow-unsolved-metas</a> <a id="154" class="Symbol">#-}</a>
</pre>-->

<pre class="Agda"><a id="171" class="Keyword">module</a> <a id="178" href="Chapter.Intro.Bool.Properties.html" class="Module">Chapter.Intro.Bool.Properties</a> <a id="208" class="Keyword">where</a>
</pre>
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

<pre class="Agda"><a id="1047" class="Keyword">open</a> <a id="1052" class="Keyword">import</a> <a id="1059" href="Data.Bool.html" class="Module">Data.Bool</a>
<a id="1069" class="Keyword">open</a> <a id="1074" class="Keyword">import</a> <a id="1081" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
</pre>
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

<pre class="Agda"><a id="true-eq"></a><a id="2434" href="Chapter.Intro.Bool.Properties.html#2434" class="Function">true-eq</a> <a id="2442" class="Symbol">:</a> <a id="2444" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a> <a id="2449" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="2451" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>
<a id="2456" href="Chapter.Intro.Bool.Properties.html#2434" class="Function">true-eq</a> <a id="2464" class="Symbol">=</a> <a id="2466" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
In a similar fashion, it is easy to prove that `false` is
equal to itself, again using the `refl` constructor:

<pre class="Agda"><a id="false-eq"></a><a id="2592" href="Chapter.Intro.Bool.Properties.html#2592" class="Function">false-eq</a> <a id="2601" class="Symbol">:</a> <a id="2603" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="2609" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="2611" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a>
<a id="2617" href="Chapter.Intro.Bool.Properties.html#2592" class="Function">false-eq</a> <a id="2626" class="Symbol">=</a> <a id="2628" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
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

<pre class="Agda"><a id="not-true-eq"></a><a id="3374" href="Chapter.Intro.Bool.Properties.html#3374" class="Function">not-true-eq</a> <a id="3386" class="Symbol">:</a> <a id="3388" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="3392" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a> <a id="3397" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3399" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a>
<a id="3405" href="Chapter.Intro.Bool.Properties.html#3374" class="Function">not-true-eq</a> <a id="3417" class="Symbol">=</a> <a id="3419" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
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

<pre class="Agda"><a id="not-inv"></a><a id="4873" href="Chapter.Intro.Bool.Properties.html#4873" class="Function">not-inv</a> <a id="4881" class="Symbol">:</a> <a id="4883" class="Symbol">∀(</a><a id="4885" href="Chapter.Intro.Bool.Properties.html#4885" class="Bound">x</a> <a id="4887" class="Symbol">:</a> <a id="4889" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="4893" class="Symbol">)</a> <a id="4895" class="Symbol">-&gt;</a> <a id="4898" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="4902" class="Symbol">(</a><a id="4903" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="4907" href="Chapter.Intro.Bool.Properties.html#4885" class="Bound">x</a><a id="4908" class="Symbol">)</a> <a id="4910" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4912" href="Chapter.Intro.Bool.Properties.html#4885" class="Bound">x</a>
<a id="4914" href="Chapter.Intro.Bool.Properties.html#4873" class="Function">not-inv</a> <a id="4922" href="Chapter.Intro.Bool.Properties.html#4922" class="Bound">x</a> <a id="4924" class="Symbol">=</a> <a id="4926" class="Hole">{!!}</a>
</pre>
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

<pre class="Agda"><a id="not-inv₁"></a><a id="6231" href="Chapter.Intro.Bool.Properties.html#6231" class="Function">not-inv₁</a> <a id="6240" class="Symbol">:</a> <a id="6242" class="Symbol">∀(</a><a id="6244" href="Chapter.Intro.Bool.Properties.html#6244" class="Bound">x</a> <a id="6246" class="Symbol">:</a> <a id="6248" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="6252" class="Symbol">)</a> <a id="6254" class="Symbol">-&gt;</a> <a id="6257" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="6261" class="Symbol">(</a><a id="6262" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="6266" href="Chapter.Intro.Bool.Properties.html#6244" class="Bound">x</a><a id="6267" class="Symbol">)</a> <a id="6269" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6271" href="Chapter.Intro.Bool.Properties.html#6244" class="Bound">x</a>
<a id="6273" href="Chapter.Intro.Bool.Properties.html#6231" class="Function">not-inv₁</a> <a id="6282" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="6288" class="Symbol">=</a> <a id="6290" class="Hole">{!!}</a>
<a id="6295" href="Chapter.Intro.Bool.Properties.html#6231" class="Function">not-inv₁</a> <a id="6304" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="6310" class="Symbol">=</a> <a id="6312" class="Hole">{!!}</a>
</pre>
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

<pre class="Agda"><a id="not-inv₂"></a><a id="7202" href="Chapter.Intro.Bool.Properties.html#7202" class="Function">not-inv₂</a> <a id="7211" class="Symbol">:</a> <a id="7213" class="Symbol">∀(</a><a id="7215" href="Chapter.Intro.Bool.Properties.html#7215" class="Bound">x</a> <a id="7217" class="Symbol">:</a> <a id="7219" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="7223" class="Symbol">)</a> <a id="7225" class="Symbol">-&gt;</a> <a id="7228" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="7232" class="Symbol">(</a><a id="7233" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="7237" href="Chapter.Intro.Bool.Properties.html#7215" class="Bound">x</a><a id="7238" class="Symbol">)</a> <a id="7240" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7242" href="Chapter.Intro.Bool.Properties.html#7215" class="Bound">x</a>
<a id="7244" href="Chapter.Intro.Bool.Properties.html#7202" class="Function">not-inv₂</a> <a id="7253" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="7259" class="Symbol">=</a> <a id="7261" href="Chapter.Intro.Bool.Properties.html#2434" class="Function">true-eq</a>
<a id="7269" href="Chapter.Intro.Bool.Properties.html#7202" class="Function">not-inv₂</a> <a id="7278" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="7284" class="Symbol">=</a> <a id="7286" href="Chapter.Intro.Bool.Properties.html#2592" class="Function">false-eq</a>
</pre>
Note that, since `true-eq` and `false-eq` are definitionally equal
to `refl`, we could have equivalently written `refl` on the right
hand side of the two equations in the definition of `not-inv₂`.

## Commutativity of `∧` and telescopes

We conclude this chapter with another simple proof concerning the
fact that `∧` is commutative, namely that `x ∧ y ≡ y ∧ x` for
every `x` and `y`.

<pre class="Agda"><a id="∧-comm"></a><a id="7690" href="Chapter.Intro.Bool.Properties.html#7690" class="Function">∧-comm</a> <a id="7697" class="Symbol">:</a> <a id="7699" class="Symbol">∀(</a><a id="7701" href="Chapter.Intro.Bool.Properties.html#7701" class="Bound">x</a> <a id="7703" class="Symbol">:</a> <a id="7705" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="7709" class="Symbol">)</a> <a id="7711" class="Symbol">-&gt;</a> <a id="7714" class="Symbol">∀(</a><a id="7716" href="Chapter.Intro.Bool.Properties.html#7716" class="Bound">y</a> <a id="7718" class="Symbol">:</a> <a id="7720" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="7724" class="Symbol">)</a> <a id="7726" class="Symbol">-&gt;</a> <a id="7729" href="Chapter.Intro.Bool.Properties.html#7701" class="Bound">x</a> <a id="7731" href="Data.Bool.Base.html#1005" class="Function Operator">∧</a> <a id="7733" href="Chapter.Intro.Bool.Properties.html#7716" class="Bound">y</a> <a id="7735" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="7737" href="Chapter.Intro.Bool.Properties.html#7716" class="Bound">y</a> <a id="7739" href="Data.Bool.Base.html#1005" class="Function Operator">∧</a> <a id="7741" href="Chapter.Intro.Bool.Properties.html#7701" class="Bound">x</a>
<a id="7743" href="Chapter.Intro.Bool.Properties.html#7690" class="Function">∧-comm</a> <a id="7750" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="7756" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="7762" class="Symbol">=</a> <a id="7764" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="7769" href="Chapter.Intro.Bool.Properties.html#7690" class="Function">∧-comm</a> <a id="7776" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="7782" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="7788" class="Symbol">=</a> <a id="7790" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="7795" href="Chapter.Intro.Bool.Properties.html#7690" class="Function">∧-comm</a> <a id="7802" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="7808" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="7814" class="Symbol">=</a> <a id="7816" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="7821" href="Chapter.Intro.Bool.Properties.html#7690" class="Function">∧-comm</a> <a id="7828" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="7834" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="7840" class="Symbol">=</a> <a id="7842" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
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

<pre class="Agda"><a id="9687" class="Comment">-- EXERCISE 1</a>

<a id="9702" class="Comment">-- when proving that x is a left unit for ∧ it is not necessary to</a>
<a id="9769" class="Comment">-- perform a case analysis on x because, according to the definition</a>
<a id="9838" class="Comment">-- of ∧, true ∧ x is the same as x</a>

<a id="∧-unit-l"></a><a id="9874" href="Chapter.Intro.Bool.Properties.html#9874" class="Function">∧-unit-l</a> <a id="9883" class="Symbol">:</a> <a id="9885" class="Symbol">∀(</a><a id="9887" href="Chapter.Intro.Bool.Properties.html#9887" class="Bound">x</a> <a id="9889" class="Symbol">:</a> <a id="9891" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="9895" class="Symbol">)</a> <a id="9897" class="Symbol">-&gt;</a> <a id="9900" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a> <a id="9905" href="Data.Bool.Base.html#1005" class="Function Operator">∧</a> <a id="9907" href="Chapter.Intro.Bool.Properties.html#9887" class="Bound">x</a> <a id="9909" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9911" href="Chapter.Intro.Bool.Properties.html#9887" class="Bound">x</a>
<a id="9913" href="Chapter.Intro.Bool.Properties.html#9874" class="Function">∧-unit-l</a> <a id="9922" href="Chapter.Intro.Bool.Properties.html#9922" class="Bound">x</a> <a id="9924" class="Symbol">=</a> <a id="9926" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="∧-unit-r"></a><a id="9932" href="Chapter.Intro.Bool.Properties.html#9932" class="Function">∧-unit-r</a> <a id="9941" class="Symbol">:</a> <a id="9943" class="Symbol">∀(</a><a id="9945" href="Chapter.Intro.Bool.Properties.html#9945" class="Bound">x</a> <a id="9947" class="Symbol">:</a> <a id="9949" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="9953" class="Symbol">)</a> <a id="9955" class="Symbol">-&gt;</a> <a id="9958" href="Chapter.Intro.Bool.Properties.html#9945" class="Bound">x</a> <a id="9960" href="Data.Bool.Base.html#1005" class="Function Operator">∧</a> <a id="9962" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a> <a id="9967" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9969" href="Chapter.Intro.Bool.Properties.html#9945" class="Bound">x</a>
<a id="9971" href="Chapter.Intro.Bool.Properties.html#9932" class="Function">∧-unit-r</a> <a id="9980" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="9986" class="Symbol">=</a> <a id="9988" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="9993" href="Chapter.Intro.Bool.Properties.html#9932" class="Function">∧-unit-r</a> <a id="10002" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="10008" class="Symbol">=</a> <a id="10010" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="10016" class="Comment">-- EXERCISE 2</a>

<a id="∧-assoc"></a><a id="10031" href="Chapter.Intro.Bool.Properties.html#10031" class="Function">∧-assoc</a> <a id="10039" class="Symbol">:</a> <a id="10041" class="Symbol">∀(</a><a id="10043" href="Chapter.Intro.Bool.Properties.html#10043" class="Bound">x</a> <a id="10045" href="Chapter.Intro.Bool.Properties.html#10045" class="Bound">y</a> <a id="10047" href="Chapter.Intro.Bool.Properties.html#10047" class="Bound">z</a> <a id="10049" class="Symbol">:</a> <a id="10051" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="10055" class="Symbol">)</a> <a id="10057" class="Symbol">-&gt;</a> <a id="10060" href="Chapter.Intro.Bool.Properties.html#10043" class="Bound">x</a> <a id="10062" href="Data.Bool.Base.html#1005" class="Function Operator">∧</a> <a id="10064" class="Symbol">(</a><a id="10065" href="Chapter.Intro.Bool.Properties.html#10045" class="Bound">y</a> <a id="10067" href="Data.Bool.Base.html#1005" class="Function Operator">∧</a> <a id="10069" href="Chapter.Intro.Bool.Properties.html#10047" class="Bound">z</a><a id="10070" class="Symbol">)</a> <a id="10072" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10074" class="Symbol">(</a><a id="10075" href="Chapter.Intro.Bool.Properties.html#10043" class="Bound">x</a> <a id="10077" href="Data.Bool.Base.html#1005" class="Function Operator">∧</a> <a id="10079" href="Chapter.Intro.Bool.Properties.html#10045" class="Bound">y</a><a id="10080" class="Symbol">)</a> <a id="10082" href="Data.Bool.Base.html#1005" class="Function Operator">∧</a> <a id="10084" href="Chapter.Intro.Bool.Properties.html#10047" class="Bound">z</a>
<a id="10086" href="Chapter.Intro.Bool.Properties.html#10031" class="Function">∧-assoc</a> <a id="10094" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a> <a id="10099" href="Chapter.Intro.Bool.Properties.html#10099" class="Bound">y</a> <a id="10101" href="Chapter.Intro.Bool.Properties.html#10101" class="Bound">z</a> <a id="10103" class="Symbol">=</a> <a id="10105" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="10110" href="Chapter.Intro.Bool.Properties.html#10031" class="Function">∧-assoc</a> <a id="10118" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="10124" href="Chapter.Intro.Bool.Properties.html#10124" class="Bound">y</a> <a id="10126" href="Chapter.Intro.Bool.Properties.html#10126" class="Bound">z</a> <a id="10128" class="Symbol">=</a> <a id="10130" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="10136" class="Comment">-- EXERCISE 3</a>

<a id="not-∧"></a><a id="10151" href="Chapter.Intro.Bool.Properties.html#10151" class="Function">not-∧</a> <a id="10157" class="Symbol">:</a> <a id="10159" class="Symbol">∀(</a><a id="10161" href="Chapter.Intro.Bool.Properties.html#10161" class="Bound">x</a> <a id="10163" href="Chapter.Intro.Bool.Properties.html#10163" class="Bound">y</a> <a id="10165" class="Symbol">:</a> <a id="10167" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="10171" class="Symbol">)</a> <a id="10173" class="Symbol">-&gt;</a> <a id="10176" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="10180" class="Symbol">(</a><a id="10181" href="Chapter.Intro.Bool.Properties.html#10161" class="Bound">x</a> <a id="10183" href="Data.Bool.Base.html#1005" class="Function Operator">∧</a> <a id="10185" href="Chapter.Intro.Bool.Properties.html#10163" class="Bound">y</a><a id="10186" class="Symbol">)</a> <a id="10188" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10190" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="10194" href="Chapter.Intro.Bool.Properties.html#10161" class="Bound">x</a> <a id="10196" href="Data.Bool.Base.html#1063" class="Function Operator">∨</a> <a id="10198" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="10202" href="Chapter.Intro.Bool.Properties.html#10163" class="Bound">y</a>
<a id="10204" href="Chapter.Intro.Bool.Properties.html#10151" class="Function">not-∧</a> <a id="10210" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="10216" class="Symbol">_</a> <a id="10218" class="Symbol">=</a> <a id="10220" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="10225" href="Chapter.Intro.Bool.Properties.html#10151" class="Function">not-∧</a> <a id="10231" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="10237" class="Symbol">_</a> <a id="10239" class="Symbol">=</a> <a id="10241" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

<a id="not-∨"></a><a id="10247" href="Chapter.Intro.Bool.Properties.html#10247" class="Function">not-∨</a> <a id="10253" class="Symbol">:</a> <a id="10255" class="Symbol">∀(</a><a id="10257" href="Chapter.Intro.Bool.Properties.html#10257" class="Bound">x</a> <a id="10259" href="Chapter.Intro.Bool.Properties.html#10259" class="Bound">y</a> <a id="10261" class="Symbol">:</a> <a id="10263" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="10267" class="Symbol">)</a> <a id="10269" class="Symbol">-&gt;</a> <a id="10272" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="10276" class="Symbol">(</a><a id="10277" href="Chapter.Intro.Bool.Properties.html#10257" class="Bound">x</a> <a id="10279" href="Data.Bool.Base.html#1063" class="Function Operator">∨</a> <a id="10281" href="Chapter.Intro.Bool.Properties.html#10259" class="Bound">y</a><a id="10282" class="Symbol">)</a> <a id="10284" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10286" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="10290" href="Chapter.Intro.Bool.Properties.html#10257" class="Bound">x</a> <a id="10292" href="Data.Bool.Base.html#1005" class="Function Operator">∧</a> <a id="10294" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="10298" href="Chapter.Intro.Bool.Properties.html#10259" class="Bound">y</a>
<a id="10300" href="Chapter.Intro.Bool.Properties.html#10247" class="Function">not-∨</a> <a id="10306" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="10312" class="Symbol">_</a> <a id="10314" class="Symbol">=</a> <a id="10316" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="10321" href="Chapter.Intro.Bool.Properties.html#10247" class="Function">not-∨</a> <a id="10327" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="10333" class="Symbol">_</a> <a id="10335" class="Symbol">=</a> <a id="10337" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>{:.solution}
