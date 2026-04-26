---
title: Inequality
prev:  Chapter.Logic.Equality
---

<pre class="Agda"><a id="62" class="Keyword">module</a> <a id="69" href="Chapter.Logic.LessThan.html" class="Module">Chapter.Logic.LessThan</a> <a id="92" class="Keyword">where</a>
</pre>
In this section we define the non-strict inequality relation on
natural numbers and prove some of its fundamental properties.

## Imports

<pre class="Agda"><a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="Function.html" class="Module">Function</a>
<a id="267" class="Keyword">open</a> <a id="272" class="Keyword">import</a> <a id="279" href="Data.Nat.html" class="Module">Data.Nat</a> <a id="288" class="Keyword">using</a> <a id="294" class="Symbol">(</a><a id="295" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="296" class="Symbol">;</a> <a id="298" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="302" class="Symbol">;</a> <a id="304" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a><a id="307" class="Symbol">;</a> <a id="309" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">_+_</a><a id="312" class="Symbol">)</a>
<a id="314" class="Keyword">open</a> <a id="319" class="Keyword">import</a> <a id="326" href="Data.Product.html" class="Module">Data.Product</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="Data.Sum.html" class="Module">Data.Sum</a>
<a id="360" class="Keyword">open</a> <a id="365" class="Keyword">import</a> <a id="372" href="Relation.Nullary.html" class="Module">Relation.Nullary</a>
<a id="389" class="Keyword">open</a> <a id="394" class="Keyword">import</a> <a id="401" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
</pre>
## Non-strict inequality

We define non-strict inequality as an inductive family according to
the following rules.

                             x ≤ y
    [z≤n] -----    [s≤s] -------------
          0 ≤ x          1 + x ≤ 1 + y

This is not the only conceivable inference system that defines
non-strict inequality. However, it turns out to be a convenient one
in most situations.

<pre class="Agda"><a id="830" class="Keyword">infix</a> <a id="836" class="Number">4</a> <a id="838" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">_≤_</a>

<a id="843" class="Keyword">data</a> <a id="_≤_"></a><a id="848" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">_≤_</a> <a id="852" class="Symbol">:</a> <a id="854" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="856" class="Symbol">→</a> <a id="858" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="860" class="Symbol">→</a> <a id="862" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="866" class="Keyword">where</a>
  <a id="_≤_.z≤n"></a><a id="874" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a> <a id="878" class="Symbol">:</a> <a id="880" class="Symbol">∀{</a><a id="882" href="Chapter.Logic.LessThan.html#882" class="Bound">x</a> <a id="884" class="Symbol">:</a> <a id="886" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="887" class="Symbol">}</a> <a id="889" class="Symbol">→</a> <a id="891" class="Number">0</a> <a id="893" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="895" href="Chapter.Logic.LessThan.html#882" class="Bound">x</a>
  <a id="_≤_.s≤s"></a><a id="899" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="903" class="Symbol">:</a> <a id="905" class="Symbol">∀{</a><a id="907" href="Chapter.Logic.LessThan.html#907" class="Bound">x</a> <a id="909" href="Chapter.Logic.LessThan.html#909" class="Bound">y</a> <a id="911" class="Symbol">:</a> <a id="913" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="914" class="Symbol">}</a> <a id="916" class="Symbol">→</a> <a id="918" href="Chapter.Logic.LessThan.html#907" class="Bound">x</a> <a id="920" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="922" href="Chapter.Logic.LessThan.html#909" class="Bound">y</a> <a id="924" class="Symbol">→</a> <a id="926" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="930" href="Chapter.Logic.LessThan.html#907" class="Bound">x</a> <a id="932" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="934" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="938" href="Chapter.Logic.LessThan.html#909" class="Bound">y</a>
</pre>
The axiom `z≤n` proves that `0` is the least element, whereas the
rule `s≤s` builds a proof of `suc x ≤ suc y` from a proof of `x ≤
y`. As an example, we can derive `2 ≤ 3` with two applications of
`s≤s` and one application of `z≤n`. In general, there are as many
applications of `s≤s` as the value of the smaller number.

<pre class="Agda"><a id="1272" href="Chapter.Logic.LessThan.html#1272" class="Function">_</a> <a id="1274" class="Symbol">:</a> <a id="1276" class="Number">2</a> <a id="1278" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="1280" class="Number">3</a>
<a id="1282" class="Symbol">_</a> <a id="1284" class="Symbol">=</a> <a id="1286" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="1290" class="Symbol">(</a><a id="1291" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="1295" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a><a id="1298" class="Symbol">)</a>
</pre>
## Correctness and completeness

Even though the definition of `≤` seems to make sense, one may
wonder whether it actually characterizes the non-strict inequality
on natural numbers. We can see that this is the case by showing that
`≤` is correct and complete with respect to another characterization
of such relation given in terms of addition.

<pre class="Agda"><a id="_≤ₘ_"></a><a id="1656" href="Chapter.Logic.LessThan.html#1656" class="Function Operator">_≤ₘ_</a> <a id="1661" class="Symbol">:</a> <a id="1663" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1665" class="Symbol">→</a> <a id="1667" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1669" class="Symbol">→</a> <a id="1671" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="1675" href="Chapter.Logic.LessThan.html#1675" class="Bound">x</a> <a id="1677" href="Chapter.Logic.LessThan.html#1656" class="Function Operator">≤ₘ</a> <a id="1680" href="Chapter.Logic.LessThan.html#1680" class="Bound">y</a> <a id="1682" class="Symbol">=</a> <a id="1684" href="Data.Product.Base.html#1371" class="Function">∃[</a> <a id="1687" href="Chapter.Logic.LessThan.html#1687" class="Bound">z</a> <a id="1689" href="Data.Product.Base.html#1371" class="Function">]</a> <a id="1691" href="Chapter.Logic.LessThan.html#1675" class="Bound">x</a> <a id="1693" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="1695" href="Chapter.Logic.LessThan.html#1687" class="Bound">z</a> <a id="1697" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="1699" href="Chapter.Logic.LessThan.html#1680" class="Bound">y</a>
</pre>
According to this definition, `x` is not larger than `y` if there
exists some natural number `z` such that `x + z ≡ y`. We can prove
that `≤` implies `≤ₘ` as follows.

<pre class="Agda"><a id="≤-correct"></a><a id="1878" href="Chapter.Logic.LessThan.html#1878" class="Function">≤-correct</a> <a id="1888" class="Symbol">:</a> <a id="1890" class="Symbol">∀{</a><a id="1892" href="Chapter.Logic.LessThan.html#1892" class="Bound">x</a> <a id="1894" href="Chapter.Logic.LessThan.html#1894" class="Bound">y</a> <a id="1896" class="Symbol">:</a> <a id="1898" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="1899" class="Symbol">}</a> <a id="1901" class="Symbol">→</a> <a id="1903" href="Chapter.Logic.LessThan.html#1892" class="Bound">x</a> <a id="1905" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="1907" href="Chapter.Logic.LessThan.html#1894" class="Bound">y</a> <a id="1909" class="Symbol">→</a> <a id="1911" href="Chapter.Logic.LessThan.html#1892" class="Bound">x</a> <a id="1913" href="Chapter.Logic.LessThan.html#1656" class="Function Operator">≤ₘ</a> <a id="1916" href="Chapter.Logic.LessThan.html#1894" class="Bound">y</a>
<a id="1918" href="Chapter.Logic.LessThan.html#1878" class="Function">≤-correct</a> <a id="1928" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a> <a id="1932" class="Symbol">=</a> <a id="1934" class="Symbol">_</a> <a id="1936" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="1938" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="1943" href="Chapter.Logic.LessThan.html#1878" class="Function">≤-correct</a> <a id="1953" class="Symbol">(</a><a id="1954" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="1958" href="Chapter.Logic.LessThan.html#1958" class="Bound">le</a><a id="1960" class="Symbol">)</a> <a id="1962" class="Keyword">with</a> <a id="1967" href="Chapter.Logic.LessThan.html#1878" class="Function">≤-correct</a> <a id="1977" href="Chapter.Logic.LessThan.html#1958" class="Bound">le</a>
<a id="1980" class="Symbol">...</a> <a id="1984" class="Symbol">|</a> <a id="1986" href="Chapter.Logic.LessThan.html#1986" class="Bound">z</a> <a id="1988" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="1990" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="1995" class="Symbol">=</a> <a id="1997" href="Chapter.Logic.LessThan.html#1986" class="Bound">z</a> <a id="1999" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="2001" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
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

<pre class="Agda"><a id="≤-complete"></a><a id="2845" href="Chapter.Logic.LessThan.html#2845" class="Function">≤-complete</a> <a id="2856" class="Symbol">:</a> <a id="2858" class="Symbol">∀{</a><a id="2860" href="Chapter.Logic.LessThan.html#2860" class="Bound">x</a> <a id="2862" href="Chapter.Logic.LessThan.html#2862" class="Bound">y</a> <a id="2864" class="Symbol">:</a> <a id="2866" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="2867" class="Symbol">}</a> <a id="2869" class="Symbol">→</a> <a id="2871" href="Chapter.Logic.LessThan.html#2860" class="Bound">x</a> <a id="2873" href="Chapter.Logic.LessThan.html#1656" class="Function Operator">≤ₘ</a> <a id="2876" href="Chapter.Logic.LessThan.html#2862" class="Bound">y</a> <a id="2878" class="Symbol">→</a> <a id="2880" href="Chapter.Logic.LessThan.html#2860" class="Bound">x</a> <a id="2882" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="2884" href="Chapter.Logic.LessThan.html#2862" class="Bound">y</a>
<a id="2886" href="Chapter.Logic.LessThan.html#2845" class="Function">≤-complete</a> <a id="2897" class="Symbol">(</a><a id="2898" href="Chapter.Logic.LessThan.html#2898" class="Bound">z</a> <a id="2900" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="2902" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a><a id="2906" class="Symbol">)</a> <a id="2908" class="Symbol">=</a> <a id="2910" href="Chapter.Logic.LessThan.html#2928" class="Function">lemma</a>
  <a id="2918" class="Keyword">where</a>
    <a id="2928" href="Chapter.Logic.LessThan.html#2928" class="Function">lemma</a> <a id="2934" class="Symbol">:</a> <a id="2936" class="Symbol">∀{</a><a id="2938" href="Chapter.Logic.LessThan.html#2938" class="Bound">x</a> <a id="2940" href="Chapter.Logic.LessThan.html#2940" class="Bound">y</a> <a id="2942" class="Symbol">:</a> <a id="2944" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="2945" class="Symbol">}</a> <a id="2947" class="Symbol">→</a> <a id="2949" href="Chapter.Logic.LessThan.html#2938" class="Bound">x</a> <a id="2951" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="2953" href="Chapter.Logic.LessThan.html#2938" class="Bound">x</a> <a id="2955" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="2957" href="Chapter.Logic.LessThan.html#2940" class="Bound">y</a>
    <a id="2963" href="Chapter.Logic.LessThan.html#2928" class="Function">lemma</a> <a id="2969" class="Symbol">{</a><a id="2970" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="2974" class="Symbol">}</a>   <a id="2978" class="Symbol">=</a> <a id="2980" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a>
    <a id="2988" href="Chapter.Logic.LessThan.html#2928" class="Function">lemma</a> <a id="2994" class="Symbol">{</a><a id="2995" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="2999" class="Symbol">_}</a> <a id="3002" class="Symbol">=</a> <a id="3004" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="3008" href="Chapter.Logic.LessThan.html#2928" class="Function">lemma</a>
</pre>
By performing case analysis on the proof of `x ≤ₘ y` we unify `y`
with `x + z`, so our goal turns into providing a proof of `x ≤ x +
z`. This is done by means of the local `lemma`.

## Inequality is a total order

Here we prove that `≤` is a **total order** on the natural
numbers. We begin by proving **reflexivity**.

<pre class="Agda"><a id="≤-refl"></a><a id="3343" href="Chapter.Logic.LessThan.html#3343" class="Function">≤-refl</a> <a id="3350" class="Symbol">:</a> <a id="3352" class="Symbol">∀{</a><a id="3354" href="Chapter.Logic.LessThan.html#3354" class="Bound">x</a> <a id="3356" class="Symbol">:</a> <a id="3358" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="3359" class="Symbol">}</a> <a id="3361" class="Symbol">→</a> <a id="3363" href="Chapter.Logic.LessThan.html#3354" class="Bound">x</a> <a id="3365" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="3367" href="Chapter.Logic.LessThan.html#3354" class="Bound">x</a>
<a id="3369" href="Chapter.Logic.LessThan.html#3343" class="Function">≤-refl</a> <a id="3376" class="Symbol">{</a><a id="3377" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="3381" class="Symbol">}</a>  <a id="3384" class="Symbol">=</a> <a id="3386" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a>
<a id="3390" href="Chapter.Logic.LessThan.html#3343" class="Function">≤-refl</a> <a id="3397" class="Symbol">{</a><a id="3398" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="3402" href="Chapter.Logic.LessThan.html#3402" class="Bound">x</a><a id="3403" class="Symbol">}</a> <a id="3405" class="Symbol">=</a> <a id="3407" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="3411" href="Chapter.Logic.LessThan.html#3343" class="Function">≤-refl</a>
</pre>
If two numbers are mutually related by `≤`, then they must be
equal. This property is called **antisymmetry** and is proved below.

<pre class="Agda"><a id="≤-antisym"></a><a id="3559" href="Chapter.Logic.LessThan.html#3559" class="Function">≤-antisym</a> <a id="3569" class="Symbol">:</a> <a id="3571" class="Symbol">∀{</a><a id="3573" href="Chapter.Logic.LessThan.html#3573" class="Bound">x</a> <a id="3575" href="Chapter.Logic.LessThan.html#3575" class="Bound">y</a> <a id="3577" class="Symbol">:</a> <a id="3579" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="3580" class="Symbol">}</a> <a id="3582" class="Symbol">→</a> <a id="3584" href="Chapter.Logic.LessThan.html#3573" class="Bound">x</a> <a id="3586" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="3588" href="Chapter.Logic.LessThan.html#3575" class="Bound">y</a> <a id="3590" class="Symbol">→</a> <a id="3592" href="Chapter.Logic.LessThan.html#3575" class="Bound">y</a> <a id="3594" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="3596" href="Chapter.Logic.LessThan.html#3573" class="Bound">x</a> <a id="3598" class="Symbol">→</a> <a id="3600" href="Chapter.Logic.LessThan.html#3573" class="Bound">x</a> <a id="3602" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3604" href="Chapter.Logic.LessThan.html#3575" class="Bound">y</a>
<a id="3606" href="Chapter.Logic.LessThan.html#3559" class="Function">≤-antisym</a> <a id="3616" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a>     <a id="3624" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a>     <a id="3632" class="Symbol">=</a> <a id="3634" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="3639" href="Chapter.Logic.LessThan.html#3559" class="Function">≤-antisym</a> <a id="3649" class="Symbol">(</a><a id="3650" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="3654" href="Chapter.Logic.LessThan.html#3654" class="Bound">p</a><a id="3655" class="Symbol">)</a> <a id="3657" class="Symbol">(</a><a id="3658" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="3662" href="Chapter.Logic.LessThan.html#3662" class="Bound">q</a><a id="3663" class="Symbol">)</a> <a id="3665" class="Symbol">=</a> <a id="3667" href="Relation.Binary.PropositionalEquality.Core.html#1481" class="Function">cong</a> <a id="3672" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="3676" class="Symbol">(</a><a id="3677" href="Chapter.Logic.LessThan.html#3559" class="Function">≤-antisym</a> <a id="3687" href="Chapter.Logic.LessThan.html#3654" class="Bound">p</a> <a id="3689" href="Chapter.Logic.LessThan.html#3662" class="Bound">q</a><a id="3690" class="Symbol">)</a>
</pre>
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
proved by `s≤s` because `y` has the form `suc z`.

<pre class="Agda"><a id="≤-trans"></a><a id="4423" href="Chapter.Logic.LessThan.html#4423" class="Function">≤-trans</a> <a id="4431" class="Symbol">:</a> <a id="4433" class="Symbol">∀{</a><a id="4435" href="Chapter.Logic.LessThan.html#4435" class="Bound">x</a> <a id="4437" href="Chapter.Logic.LessThan.html#4437" class="Bound">y</a> <a id="4439" href="Chapter.Logic.LessThan.html#4439" class="Bound">z</a> <a id="4441" class="Symbol">:</a> <a id="4443" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="4444" class="Symbol">}</a> <a id="4446" class="Symbol">→</a> <a id="4448" href="Chapter.Logic.LessThan.html#4435" class="Bound">x</a> <a id="4450" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="4452" href="Chapter.Logic.LessThan.html#4437" class="Bound">y</a> <a id="4454" class="Symbol">→</a> <a id="4456" href="Chapter.Logic.LessThan.html#4437" class="Bound">y</a> <a id="4458" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="4460" href="Chapter.Logic.LessThan.html#4439" class="Bound">z</a> <a id="4462" class="Symbol">→</a> <a id="4464" href="Chapter.Logic.LessThan.html#4435" class="Bound">x</a> <a id="4466" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="4468" href="Chapter.Logic.LessThan.html#4439" class="Bound">z</a>
<a id="4470" href="Chapter.Logic.LessThan.html#4423" class="Function">≤-trans</a> <a id="4478" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a>     <a id="4486" href="Chapter.Logic.LessThan.html#4486" class="Bound">q</a>       <a id="4494" class="Symbol">=</a> <a id="4496" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a>
<a id="4500" href="Chapter.Logic.LessThan.html#4423" class="Function">≤-trans</a> <a id="4508" class="Symbol">(</a><a id="4509" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="4513" href="Chapter.Logic.LessThan.html#4513" class="Bound">p</a><a id="4514" class="Symbol">)</a> <a id="4516" class="Symbol">(</a><a id="4517" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="4521" href="Chapter.Logic.LessThan.html#4521" class="Bound">q</a><a id="4522" class="Symbol">)</a> <a id="4524" class="Symbol">=</a> <a id="4526" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="4530" class="Symbol">(</a><a id="4531" href="Chapter.Logic.LessThan.html#4423" class="Function">≤-trans</a> <a id="4539" href="Chapter.Logic.LessThan.html#4513" class="Bound">p</a> <a id="4541" href="Chapter.Logic.LessThan.html#4521" class="Bound">q</a><a id="4542" class="Symbol">)</a>
</pre>
To conclude the proof that `≤` is a total order we have to show
that any two natural numbers `x` and `y` are related in one way or
another. This follows from a straightforward cases analysis on them.

<pre class="Agda"><a id="≤-total"></a><a id="4754" href="Chapter.Logic.LessThan.html#4754" class="Function">≤-total</a> <a id="4762" class="Symbol">:</a> <a id="4764" class="Symbol">∀(</a><a id="4766" href="Chapter.Logic.LessThan.html#4766" class="Bound">x</a> <a id="4768" href="Chapter.Logic.LessThan.html#4768" class="Bound">y</a> <a id="4770" class="Symbol">:</a> <a id="4772" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="4773" class="Symbol">)</a> <a id="4775" class="Symbol">→</a> <a id="4777" href="Chapter.Logic.LessThan.html#4766" class="Bound">x</a> <a id="4779" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="4781" href="Chapter.Logic.LessThan.html#4768" class="Bound">y</a> <a id="4783" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="4785" href="Chapter.Logic.LessThan.html#4768" class="Bound">y</a> <a id="4787" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="4789" href="Chapter.Logic.LessThan.html#4766" class="Bound">x</a>
<a id="4791" href="Chapter.Logic.LessThan.html#4754" class="Function">≤-total</a> <a id="4799" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="4807" class="Symbol">_</a>       <a id="4815" class="Symbol">=</a> <a id="4817" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="4822" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a>
<a id="4826" href="Chapter.Logic.LessThan.html#4754" class="Function">≤-total</a> <a id="4834" class="Symbol">(</a><a id="4835" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4839" class="Symbol">_)</a> <a id="4842" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="4850" class="Symbol">=</a> <a id="4852" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="4857" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a>
<a id="4861" href="Chapter.Logic.LessThan.html#4754" class="Function">≤-total</a> <a id="4869" class="Symbol">(</a><a id="4870" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4874" href="Chapter.Logic.LessThan.html#4874" class="Bound">x</a><a id="4875" class="Symbol">)</a> <a id="4877" class="Symbol">(</a><a id="4878" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4882" href="Chapter.Logic.LessThan.html#4882" class="Bound">y</a><a id="4883" class="Symbol">)</a> <a id="4885" class="Keyword">with</a> <a id="4890" href="Chapter.Logic.LessThan.html#4754" class="Function">≤-total</a> <a id="4898" href="Chapter.Logic.LessThan.html#4874" class="Bound">x</a> <a id="4900" href="Chapter.Logic.LessThan.html#4882" class="Bound">y</a>
<a id="4902" class="Symbol">...</a> <a id="4906" class="Symbol">|</a> <a id="4908" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="4913" href="Chapter.Logic.LessThan.html#4913" class="Bound">p</a> <a id="4915" class="Symbol">=</a> <a id="4917" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="4922" class="Symbol">(</a><a id="4923" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="4927" href="Chapter.Logic.LessThan.html#4913" class="Bound">p</a><a id="4928" class="Symbol">)</a>
<a id="4930" class="Symbol">...</a> <a id="4934" class="Symbol">|</a> <a id="4936" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="4941" href="Chapter.Logic.LessThan.html#4941" class="Bound">q</a> <a id="4943" class="Symbol">=</a> <a id="4945" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="4950" class="Symbol">(</a><a id="4951" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="4955" href="Chapter.Logic.LessThan.html#4941" class="Bound">q</a><a id="4956" class="Symbol">)</a>
</pre>
## Exercises

1. Show that `≤` is decidable, namely prove the theorem `_≤?_ : ∀(x
   y : ℕ) → ¬ x ≤ y ⊎ x ≤ y`.
2. Define `min : ℕ → ℕ → ℕ` and `max : ℕ → ℕ → ℕ` and prove the
   theorems `≤-min : ∀{x y z : ℕ} → x ≤ y → x ≤ z → x ≤ min y z`
   and `≤-max : ∀{x y z : ℕ} → x ≤ z → y ≤ z → max x y ≤ z`.
3. Strict inequality `x < y` can be defined to be the same as `suc x
   ≤ y`. Prove that this relation is transitive and irreflexive.

<pre class="Agda"><a id="5404" class="Comment">-- EXERCISE 1</a>

<a id="_≤?_"></a><a id="5419" href="Chapter.Logic.LessThan.html#5419" class="Function Operator">_≤?_</a> <a id="5424" class="Symbol">:</a> <a id="5426" class="Symbol">∀(</a><a id="5428" href="Chapter.Logic.LessThan.html#5428" class="Bound">x</a> <a id="5430" href="Chapter.Logic.LessThan.html#5430" class="Bound">y</a> <a id="5432" class="Symbol">:</a> <a id="5434" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="5435" class="Symbol">)</a> <a id="5437" class="Symbol">→</a> <a id="5439" href="Relation.Nullary.Negation.Core.html#677" class="Function Operator">¬</a> <a id="5441" href="Chapter.Logic.LessThan.html#5428" class="Bound">x</a> <a id="5443" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="5445" href="Chapter.Logic.LessThan.html#5430" class="Bound">y</a> <a id="5447" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="5449" href="Chapter.Logic.LessThan.html#5428" class="Bound">x</a> <a id="5451" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="5453" href="Chapter.Logic.LessThan.html#5430" class="Bound">y</a>
<a id="5455" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>   <a id="5462" href="Chapter.Logic.LessThan.html#5419" class="Function Operator">≤?</a> <a id="5465" href="Chapter.Logic.LessThan.html#5465" class="Bound">y</a>    <a id="5470" class="Symbol">=</a> <a id="5472" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="5477" href="Chapter.Logic.LessThan.html#874" class="InductiveConstructor">z≤n</a>
<a id="5481" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5485" href="Chapter.Logic.LessThan.html#5485" class="Bound">x</a> <a id="5487" href="Chapter.Logic.LessThan.html#5419" class="Function Operator">≤?</a> <a id="5490" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="5495" class="Symbol">=</a> <a id="5497" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="5502" class="Symbol">λ</a> <a id="5504" class="Symbol">()</a>
<a id="5507" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5511" href="Chapter.Logic.LessThan.html#5511" class="Bound">x</a> <a id="5513" href="Chapter.Logic.LessThan.html#5419" class="Function Operator">≤?</a> <a id="5516" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5520" href="Chapter.Logic.LessThan.html#5520" class="Bound">y</a> <a id="5522" class="Keyword">with</a> <a id="5527" href="Chapter.Logic.LessThan.html#5511" class="Bound">x</a> <a id="5529" href="Chapter.Logic.LessThan.html#5419" class="Function Operator">≤?</a> <a id="5532" href="Chapter.Logic.LessThan.html#5520" class="Bound">y</a>
<a id="5534" class="Symbol">...</a> <a id="5538" class="Symbol">|</a> <a id="5540" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="5545" href="Chapter.Logic.LessThan.html#5545" class="Bound">gt</a> <a id="5548" class="Symbol">=</a> <a id="5550" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="5555" class="Symbol">λ</a> <a id="5557" class="Symbol">{</a> <a id="5559" class="Symbol">(</a><a id="5560" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="5564" href="Chapter.Logic.LessThan.html#5564" class="Bound">le</a><a id="5566" class="Symbol">)</a> <a id="5568" class="Symbol">→</a> <a id="5570" href="Chapter.Logic.LessThan.html#5545" class="Bound">gt</a> <a id="5573" href="Chapter.Logic.LessThan.html#5564" class="Bound">le</a> <a id="5576" class="Symbol">}</a>
<a id="5578" class="Symbol">...</a> <a id="5582" class="Symbol">|</a> <a id="5584" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="5589" href="Chapter.Logic.LessThan.html#5589" class="Bound">le</a> <a id="5592" class="Symbol">=</a> <a id="5594" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="5599" class="Symbol">(</a><a id="5600" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="5604" href="Chapter.Logic.LessThan.html#5589" class="Bound">le</a><a id="5606" class="Symbol">)</a>

<a id="_&lt;_"></a><a id="5609" href="Chapter.Logic.LessThan.html#5609" class="Function Operator">_&lt;_</a> <a id="5613" class="Symbol">:</a> <a id="5615" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="5617" class="Symbol">→</a> <a id="5619" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="5621" class="Symbol">→</a> <a id="5623" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="5627" href="Chapter.Logic.LessThan.html#5627" class="Bound">x</a> <a id="5629" href="Chapter.Logic.LessThan.html#5609" class="Function Operator">&lt;</a> <a id="5631" href="Chapter.Logic.LessThan.html#5631" class="Bound">y</a> <a id="5633" class="Symbol">=</a> <a id="5635" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5639" href="Chapter.Logic.LessThan.html#5627" class="Bound">x</a> <a id="5641" href="Chapter.Logic.LessThan.html#848" class="Datatype Operator">≤</a> <a id="5643" href="Chapter.Logic.LessThan.html#5631" class="Bound">y</a>

<a id="5646" class="Comment">-- EXERCISE 2</a>

<a id="5661" class="Comment">-- ...</a>

<a id="5669" class="Comment">-- EXERCISE 3</a>

<a id="lt-irrefl"></a><a id="5684" href="Chapter.Logic.LessThan.html#5684" class="Function">lt-irrefl</a> <a id="5694" class="Symbol">:</a> <a id="5696" class="Symbol">∀{</a><a id="5698" href="Chapter.Logic.LessThan.html#5698" class="Bound">x</a> <a id="5700" class="Symbol">:</a> <a id="5702" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="5703" class="Symbol">}</a> <a id="5705" class="Symbol">→</a> <a id="5707" href="Relation.Nullary.Negation.Core.html#677" class="Function Operator">¬</a> <a id="5709" class="Symbol">(</a><a id="5710" href="Chapter.Logic.LessThan.html#5698" class="Bound">x</a> <a id="5712" href="Chapter.Logic.LessThan.html#5609" class="Function Operator">&lt;</a> <a id="5714" href="Chapter.Logic.LessThan.html#5698" class="Bound">x</a><a id="5715" class="Symbol">)</a>
<a id="5717" href="Chapter.Logic.LessThan.html#5684" class="Function">lt-irrefl</a> <a id="5727" class="Symbol">{</a><a id="5728" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5732" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="5736" class="Symbol">}</a>     <a id="5742" class="Symbol">(</a><a id="5743" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="5747" class="Symbol">())</a>
<a id="5751" href="Chapter.Logic.LessThan.html#5684" class="Function">lt-irrefl</a> <a id="5761" class="Symbol">{</a><a id="5762" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5766" class="Symbol">(</a><a id="5767" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5771" class="Symbol">_)}</a> <a id="5775" class="Symbol">(</a><a id="5776" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="5780" class="Symbol">(</a><a id="5781" href="Chapter.Logic.LessThan.html#899" class="InductiveConstructor">s≤s</a> <a id="5785" href="Chapter.Logic.LessThan.html#5785" class="Bound">lt</a><a id="5787" class="Symbol">))</a> <a id="5790" class="Symbol">=</a> <a id="5792" href="Chapter.Logic.LessThan.html#5684" class="Function">lt-irrefl</a> <a id="5802" href="Chapter.Logic.LessThan.html#5785" class="Bound">lt</a>

<a id="5806" class="Comment">-- ...</a>
</pre>{:.solution}
