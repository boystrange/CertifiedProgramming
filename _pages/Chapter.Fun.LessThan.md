---
title: Inequality
next:  Chapter.Fun.SortedLists
---

<pre class="Agda"><a id="63" class="Keyword">module</a> <a id="70" href="Chapter.Fun.LessThan.html" class="Module">Chapter.Fun.LessThan</a> <a id="91" class="Keyword">where</a>
</pre>
In this section we define the non-strict inequality relation on
natural numbers and prove some of its fundamental properties.

## Imports

<pre class="Agda"><a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="Function.html" class="Module">Function</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="Data.Nat.html" class="Module">Data.Nat</a> <a id="287" class="Keyword">using</a> <a id="293" class="Symbol">(</a><a id="294" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="295" class="Symbol">;</a> <a id="297" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="301" class="Symbol">;</a> <a id="303" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a><a id="306" class="Symbol">;</a> <a id="308" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">_+_</a><a id="311" class="Symbol">)</a>
<a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="Data.Product.html" class="Module">Data.Product</a>
<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="Data.Sum.html" class="Module">Data.Sum</a>
<a id="359" class="Keyword">open</a> <a id="364" class="Keyword">import</a> <a id="371" href="Relation.Nullary.html" class="Module">Relation.Nullary</a>
<a id="388" class="Keyword">open</a> <a id="393" class="Keyword">import</a> <a id="400" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
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

<pre class="Agda"><a id="829" class="Keyword">infix</a> <a id="835" class="Number">4</a> <a id="837" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">_≤_</a>

<a id="842" class="Keyword">data</a> <a id="_≤_"></a><a id="847" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">_≤_</a> <a id="851" class="Symbol">:</a> <a id="853" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="855" class="Symbol">→</a> <a id="857" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="859" class="Symbol">→</a> <a id="861" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="865" class="Keyword">where</a>
  <a id="_≤_.z≤n"></a><a id="873" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a> <a id="877" class="Symbol">:</a> <a id="879" class="Symbol">∀{</a><a id="881" href="Chapter.Fun.LessThan.html#881" class="Bound">x</a> <a id="883" class="Symbol">:</a> <a id="885" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="886" class="Symbol">}</a> <a id="888" class="Symbol">→</a> <a id="890" class="Number">0</a> <a id="892" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="894" href="Chapter.Fun.LessThan.html#881" class="Bound">x</a>
  <a id="_≤_.s≤s"></a><a id="898" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="902" class="Symbol">:</a> <a id="904" class="Symbol">∀{</a><a id="906" href="Chapter.Fun.LessThan.html#906" class="Bound">x</a> <a id="908" href="Chapter.Fun.LessThan.html#908" class="Bound">y</a> <a id="910" class="Symbol">:</a> <a id="912" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="913" class="Symbol">}</a> <a id="915" class="Symbol">→</a> <a id="917" href="Chapter.Fun.LessThan.html#906" class="Bound">x</a> <a id="919" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="921" href="Chapter.Fun.LessThan.html#908" class="Bound">y</a> <a id="923" class="Symbol">→</a> <a id="925" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="929" href="Chapter.Fun.LessThan.html#906" class="Bound">x</a> <a id="931" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="933" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="937" href="Chapter.Fun.LessThan.html#908" class="Bound">y</a>
</pre>
The axiom `z≤n` proves that `0` is the least element, whereas the
rule `s≤s` builds a proof of `suc x ≤ suc y` from a proof of `x ≤
y`. As an example, we can derive `2 ≤ 3` with two applications of
`s≤s` and one application of `z≤n`. In general, there are as many
applications of `s≤s` as the value of the smaller number.

<pre class="Agda"><a id="1271" href="Chapter.Fun.LessThan.html#1271" class="Function">_</a> <a id="1273" class="Symbol">:</a> <a id="1275" class="Number">2</a> <a id="1277" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="1279" class="Number">3</a>
<a id="1281" class="Symbol">_</a> <a id="1283" class="Symbol">=</a> <a id="1285" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="1289" class="Symbol">(</a><a id="1290" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="1294" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a><a id="1297" class="Symbol">)</a>
</pre>
## Correctness and completeness

Even though the definition of `≤` seems to make sense, one may
wonder whether it actually characterizes the non-strict inequality
on natural numbers. We can see that this is the case by showing that
`≤` is correct and complete with respect to another characterization
of such relation given in terms of addition.

<pre class="Agda"><a id="_≤ₘ_"></a><a id="1655" href="Chapter.Fun.LessThan.html#1655" class="Function Operator">_≤ₘ_</a> <a id="1660" class="Symbol">:</a> <a id="1662" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1664" class="Symbol">→</a> <a id="1666" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1668" class="Symbol">→</a> <a id="1670" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="1674" href="Chapter.Fun.LessThan.html#1674" class="Bound">x</a> <a id="1676" href="Chapter.Fun.LessThan.html#1655" class="Function Operator">≤ₘ</a> <a id="1679" href="Chapter.Fun.LessThan.html#1679" class="Bound">y</a> <a id="1681" class="Symbol">=</a> <a id="1683" href="Data.Product.Base.html#1371" class="Function">∃[</a> <a id="1686" href="Chapter.Fun.LessThan.html#1686" class="Bound">z</a> <a id="1688" href="Data.Product.Base.html#1371" class="Function">]</a> <a id="1690" href="Chapter.Fun.LessThan.html#1674" class="Bound">x</a> <a id="1692" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="1694" href="Chapter.Fun.LessThan.html#1686" class="Bound">z</a> <a id="1696" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="1698" href="Chapter.Fun.LessThan.html#1679" class="Bound">y</a>
</pre>
According to this definition, `x` is not larger than `y` if there
exists some natural number `z` such that `x + z ≡ y`. We can prove
that `≤` implies `≤ₘ` as follows.

<pre class="Agda"><a id="≤-correct"></a><a id="1877" href="Chapter.Fun.LessThan.html#1877" class="Function">≤-correct</a> <a id="1887" class="Symbol">:</a> <a id="1889" class="Symbol">∀{</a><a id="1891" href="Chapter.Fun.LessThan.html#1891" class="Bound">x</a> <a id="1893" href="Chapter.Fun.LessThan.html#1893" class="Bound">y</a> <a id="1895" class="Symbol">:</a> <a id="1897" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="1898" class="Symbol">}</a> <a id="1900" class="Symbol">→</a> <a id="1902" href="Chapter.Fun.LessThan.html#1891" class="Bound">x</a> <a id="1904" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="1906" href="Chapter.Fun.LessThan.html#1893" class="Bound">y</a> <a id="1908" class="Symbol">→</a> <a id="1910" href="Chapter.Fun.LessThan.html#1891" class="Bound">x</a> <a id="1912" href="Chapter.Fun.LessThan.html#1655" class="Function Operator">≤ₘ</a> <a id="1915" href="Chapter.Fun.LessThan.html#1893" class="Bound">y</a>
<a id="1917" href="Chapter.Fun.LessThan.html#1877" class="Function">≤-correct</a> <a id="1927" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a> <a id="1931" class="Symbol">=</a> <a id="1933" class="Symbol">_</a> <a id="1935" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="1937" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="1942" href="Chapter.Fun.LessThan.html#1877" class="Function">≤-correct</a> <a id="1952" class="Symbol">(</a><a id="1953" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="1957" href="Chapter.Fun.LessThan.html#1957" class="Bound">le</a><a id="1959" class="Symbol">)</a> <a id="1961" class="Keyword">with</a> <a id="1966" href="Chapter.Fun.LessThan.html#1877" class="Function">≤-correct</a> <a id="1976" href="Chapter.Fun.LessThan.html#1957" class="Bound">le</a>
<a id="1979" class="Symbol">...</a> <a id="1983" class="Symbol">|</a> <a id="1985" href="Chapter.Fun.LessThan.html#1985" class="Bound">z</a> <a id="1987" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="1989" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="1994" class="Symbol">=</a> <a id="1996" href="Chapter.Fun.LessThan.html#1985" class="Bound">z</a> <a id="1998" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="2000" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
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

<pre class="Agda"><a id="≤-complete"></a><a id="2844" href="Chapter.Fun.LessThan.html#2844" class="Function">≤-complete</a> <a id="2855" class="Symbol">:</a> <a id="2857" class="Symbol">∀{</a><a id="2859" href="Chapter.Fun.LessThan.html#2859" class="Bound">x</a> <a id="2861" href="Chapter.Fun.LessThan.html#2861" class="Bound">y</a> <a id="2863" class="Symbol">:</a> <a id="2865" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="2866" class="Symbol">}</a> <a id="2868" class="Symbol">→</a> <a id="2870" href="Chapter.Fun.LessThan.html#2859" class="Bound">x</a> <a id="2872" href="Chapter.Fun.LessThan.html#1655" class="Function Operator">≤ₘ</a> <a id="2875" href="Chapter.Fun.LessThan.html#2861" class="Bound">y</a> <a id="2877" class="Symbol">→</a> <a id="2879" href="Chapter.Fun.LessThan.html#2859" class="Bound">x</a> <a id="2881" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="2883" href="Chapter.Fun.LessThan.html#2861" class="Bound">y</a>
<a id="2885" href="Chapter.Fun.LessThan.html#2844" class="Function">≤-complete</a> <a id="2896" class="Symbol">(</a><a id="2897" href="Chapter.Fun.LessThan.html#2897" class="Bound">z</a> <a id="2899" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="2901" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a><a id="2905" class="Symbol">)</a> <a id="2907" class="Symbol">=</a> <a id="2909" href="Chapter.Fun.LessThan.html#2927" class="Function">lemma</a>
  <a id="2917" class="Keyword">where</a>
    <a id="2927" href="Chapter.Fun.LessThan.html#2927" class="Function">lemma</a> <a id="2933" class="Symbol">:</a> <a id="2935" class="Symbol">∀{</a><a id="2937" href="Chapter.Fun.LessThan.html#2937" class="Bound">x</a> <a id="2939" href="Chapter.Fun.LessThan.html#2939" class="Bound">y</a> <a id="2941" class="Symbol">:</a> <a id="2943" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="2944" class="Symbol">}</a> <a id="2946" class="Symbol">→</a> <a id="2948" href="Chapter.Fun.LessThan.html#2937" class="Bound">x</a> <a id="2950" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="2952" href="Chapter.Fun.LessThan.html#2937" class="Bound">x</a> <a id="2954" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="2956" href="Chapter.Fun.LessThan.html#2939" class="Bound">y</a>
    <a id="2962" href="Chapter.Fun.LessThan.html#2927" class="Function">lemma</a> <a id="2968" class="Symbol">{</a><a id="2969" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="2973" class="Symbol">}</a>   <a id="2977" class="Symbol">=</a> <a id="2979" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a>
    <a id="2987" href="Chapter.Fun.LessThan.html#2927" class="Function">lemma</a> <a id="2993" class="Symbol">{</a><a id="2994" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="2998" class="Symbol">_}</a> <a id="3001" class="Symbol">=</a> <a id="3003" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="3007" href="Chapter.Fun.LessThan.html#2927" class="Function">lemma</a>
</pre>
By performing case analysis on the proof of `x ≤ₘ y` we unify `y`
with `x + z`, so our goal turns into providing a proof of `x ≤ x +
z`. This is done by means of the local `lemma`.

## Inequality is a total order

Here we prove that `≤` is a **total order** on the natural
numbers. We begin by proving **reflexivity**.

<pre class="Agda"><a id="≤-refl"></a><a id="3342" href="Chapter.Fun.LessThan.html#3342" class="Function">≤-refl</a> <a id="3349" class="Symbol">:</a> <a id="3351" class="Symbol">∀{</a><a id="3353" href="Chapter.Fun.LessThan.html#3353" class="Bound">x</a> <a id="3355" class="Symbol">:</a> <a id="3357" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="3358" class="Symbol">}</a> <a id="3360" class="Symbol">→</a> <a id="3362" href="Chapter.Fun.LessThan.html#3353" class="Bound">x</a> <a id="3364" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="3366" href="Chapter.Fun.LessThan.html#3353" class="Bound">x</a>
<a id="3368" href="Chapter.Fun.LessThan.html#3342" class="Function">≤-refl</a> <a id="3375" class="Symbol">{</a><a id="3376" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="3380" class="Symbol">}</a>  <a id="3383" class="Symbol">=</a> <a id="3385" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a>
<a id="3389" href="Chapter.Fun.LessThan.html#3342" class="Function">≤-refl</a> <a id="3396" class="Symbol">{</a><a id="3397" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="3401" href="Chapter.Fun.LessThan.html#3401" class="Bound">x</a><a id="3402" class="Symbol">}</a> <a id="3404" class="Symbol">=</a> <a id="3406" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="3410" href="Chapter.Fun.LessThan.html#3342" class="Function">≤-refl</a>
</pre>
If two numbers are mutually related by `≤`, then they must be
equal. This property is called **antisymmetry** and is proved below.

<pre class="Agda"><a id="≤-antisym"></a><a id="3558" href="Chapter.Fun.LessThan.html#3558" class="Function">≤-antisym</a> <a id="3568" class="Symbol">:</a> <a id="3570" class="Symbol">∀{</a><a id="3572" href="Chapter.Fun.LessThan.html#3572" class="Bound">x</a> <a id="3574" href="Chapter.Fun.LessThan.html#3574" class="Bound">y</a> <a id="3576" class="Symbol">:</a> <a id="3578" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="3579" class="Symbol">}</a> <a id="3581" class="Symbol">→</a> <a id="3583" href="Chapter.Fun.LessThan.html#3572" class="Bound">x</a> <a id="3585" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="3587" href="Chapter.Fun.LessThan.html#3574" class="Bound">y</a> <a id="3589" class="Symbol">→</a> <a id="3591" href="Chapter.Fun.LessThan.html#3574" class="Bound">y</a> <a id="3593" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="3595" href="Chapter.Fun.LessThan.html#3572" class="Bound">x</a> <a id="3597" class="Symbol">→</a> <a id="3599" href="Chapter.Fun.LessThan.html#3572" class="Bound">x</a> <a id="3601" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="3603" href="Chapter.Fun.LessThan.html#3574" class="Bound">y</a>
<a id="3605" href="Chapter.Fun.LessThan.html#3558" class="Function">≤-antisym</a> <a id="3615" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a>     <a id="3623" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a>     <a id="3631" class="Symbol">=</a> <a id="3633" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="3638" href="Chapter.Fun.LessThan.html#3558" class="Function">≤-antisym</a> <a id="3648" class="Symbol">(</a><a id="3649" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="3653" href="Chapter.Fun.LessThan.html#3653" class="Bound">p</a><a id="3654" class="Symbol">)</a> <a id="3656" class="Symbol">(</a><a id="3657" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="3661" href="Chapter.Fun.LessThan.html#3661" class="Bound">q</a><a id="3662" class="Symbol">)</a> <a id="3664" class="Symbol">=</a> <a id="3666" href="Relation.Binary.PropositionalEquality.Core.html#1481" class="Function">cong</a> <a id="3671" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="3675" class="Symbol">(</a><a id="3676" href="Chapter.Fun.LessThan.html#3558" class="Function">≤-antisym</a> <a id="3686" href="Chapter.Fun.LessThan.html#3653" class="Bound">p</a> <a id="3688" href="Chapter.Fun.LessThan.html#3661" class="Bound">q</a><a id="3689" class="Symbol">)</a>
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
proved by `s≤s` because `y` has the form `suc y'`.

<pre class="Agda"><a id="≤-trans"></a><a id="4423" href="Chapter.Fun.LessThan.html#4423" class="Function">≤-trans</a> <a id="4431" class="Symbol">:</a> <a id="4433" class="Symbol">∀{</a><a id="4435" href="Chapter.Fun.LessThan.html#4435" class="Bound">x</a> <a id="4437" href="Chapter.Fun.LessThan.html#4437" class="Bound">y</a> <a id="4439" href="Chapter.Fun.LessThan.html#4439" class="Bound">z</a> <a id="4441" class="Symbol">:</a> <a id="4443" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="4444" class="Symbol">}</a> <a id="4446" class="Symbol">→</a> <a id="4448" href="Chapter.Fun.LessThan.html#4435" class="Bound">x</a> <a id="4450" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="4452" href="Chapter.Fun.LessThan.html#4437" class="Bound">y</a> <a id="4454" class="Symbol">→</a> <a id="4456" href="Chapter.Fun.LessThan.html#4437" class="Bound">y</a> <a id="4458" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="4460" href="Chapter.Fun.LessThan.html#4439" class="Bound">z</a> <a id="4462" class="Symbol">→</a> <a id="4464" href="Chapter.Fun.LessThan.html#4435" class="Bound">x</a> <a id="4466" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="4468" href="Chapter.Fun.LessThan.html#4439" class="Bound">z</a>
<a id="4470" href="Chapter.Fun.LessThan.html#4423" class="Function">≤-trans</a> <a id="4478" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a>     <a id="4486" href="Chapter.Fun.LessThan.html#4486" class="Bound">q</a>       <a id="4494" class="Symbol">=</a> <a id="4496" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a>
<a id="4500" href="Chapter.Fun.LessThan.html#4423" class="Function">≤-trans</a> <a id="4508" class="Symbol">(</a><a id="4509" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="4513" href="Chapter.Fun.LessThan.html#4513" class="Bound">p</a><a id="4514" class="Symbol">)</a> <a id="4516" class="Symbol">(</a><a id="4517" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="4521" href="Chapter.Fun.LessThan.html#4521" class="Bound">q</a><a id="4522" class="Symbol">)</a> <a id="4524" class="Symbol">=</a> <a id="4526" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="4530" class="Symbol">(</a><a id="4531" href="Chapter.Fun.LessThan.html#4423" class="Function">≤-trans</a> <a id="4539" href="Chapter.Fun.LessThan.html#4513" class="Bound">p</a> <a id="4541" href="Chapter.Fun.LessThan.html#4521" class="Bound">q</a><a id="4542" class="Symbol">)</a>
</pre>
To conclude the proof that `≤` is a total order we have to show
that any two natural numbers `x` and `y` are related in one way or
another. This follows from a straightforward cases analysis on them.

<pre class="Agda"><a id="≤-total"></a><a id="4754" href="Chapter.Fun.LessThan.html#4754" class="Function">≤-total</a> <a id="4762" class="Symbol">:</a> <a id="4764" class="Symbol">∀(</a><a id="4766" href="Chapter.Fun.LessThan.html#4766" class="Bound">x</a> <a id="4768" href="Chapter.Fun.LessThan.html#4768" class="Bound">y</a> <a id="4770" class="Symbol">:</a> <a id="4772" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="4773" class="Symbol">)</a> <a id="4775" class="Symbol">→</a> <a id="4777" href="Chapter.Fun.LessThan.html#4766" class="Bound">x</a> <a id="4779" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="4781" href="Chapter.Fun.LessThan.html#4768" class="Bound">y</a> <a id="4783" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="4785" href="Chapter.Fun.LessThan.html#4768" class="Bound">y</a> <a id="4787" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="4789" href="Chapter.Fun.LessThan.html#4766" class="Bound">x</a>
<a id="4791" href="Chapter.Fun.LessThan.html#4754" class="Function">≤-total</a> <a id="4799" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="4807" class="Symbol">_</a>       <a id="4815" class="Symbol">=</a> <a id="4817" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="4822" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a>
<a id="4826" href="Chapter.Fun.LessThan.html#4754" class="Function">≤-total</a> <a id="4834" class="Symbol">(</a><a id="4835" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4839" class="Symbol">_)</a> <a id="4842" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="4850" class="Symbol">=</a> <a id="4852" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="4857" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a>
<a id="4861" href="Chapter.Fun.LessThan.html#4754" class="Function">≤-total</a> <a id="4869" class="Symbol">(</a><a id="4870" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4874" href="Chapter.Fun.LessThan.html#4874" class="Bound">x</a><a id="4875" class="Symbol">)</a> <a id="4877" class="Symbol">(</a><a id="4878" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4882" href="Chapter.Fun.LessThan.html#4882" class="Bound">y</a><a id="4883" class="Symbol">)</a> <a id="4885" class="Keyword">with</a> <a id="4890" href="Chapter.Fun.LessThan.html#4754" class="Function">≤-total</a> <a id="4898" href="Chapter.Fun.LessThan.html#4874" class="Bound">x</a> <a id="4900" href="Chapter.Fun.LessThan.html#4882" class="Bound">y</a>
<a id="4902" class="Symbol">...</a> <a id="4906" class="Symbol">|</a> <a id="4908" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="4913" href="Chapter.Fun.LessThan.html#4913" class="Bound">p</a> <a id="4915" class="Symbol">=</a> <a id="4917" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="4922" class="Symbol">(</a><a id="4923" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="4927" href="Chapter.Fun.LessThan.html#4913" class="Bound">p</a><a id="4928" class="Symbol">)</a>
<a id="4930" class="Symbol">...</a> <a id="4934" class="Symbol">|</a> <a id="4936" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="4941" href="Chapter.Fun.LessThan.html#4941" class="Bound">q</a> <a id="4943" class="Symbol">=</a> <a id="4945" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="4950" class="Symbol">(</a><a id="4951" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="4955" href="Chapter.Fun.LessThan.html#4941" class="Bound">q</a><a id="4956" class="Symbol">)</a>
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

<a id="_≤?_"></a><a id="5419" href="Chapter.Fun.LessThan.html#5419" class="Function Operator">_≤?_</a> <a id="5424" class="Symbol">:</a> <a id="5426" class="Symbol">∀(</a><a id="5428" href="Chapter.Fun.LessThan.html#5428" class="Bound">x</a> <a id="5430" href="Chapter.Fun.LessThan.html#5430" class="Bound">y</a> <a id="5432" class="Symbol">:</a> <a id="5434" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="5435" class="Symbol">)</a> <a id="5437" class="Symbol">→</a> <a id="5439" href="Relation.Nullary.Negation.Core.html#677" class="Function Operator">¬</a> <a id="5441" href="Chapter.Fun.LessThan.html#5428" class="Bound">x</a> <a id="5443" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="5445" href="Chapter.Fun.LessThan.html#5430" class="Bound">y</a> <a id="5447" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="5449" href="Chapter.Fun.LessThan.html#5428" class="Bound">x</a> <a id="5451" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="5453" href="Chapter.Fun.LessThan.html#5430" class="Bound">y</a>
<a id="5455" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>   <a id="5462" href="Chapter.Fun.LessThan.html#5419" class="Function Operator">≤?</a> <a id="5465" href="Chapter.Fun.LessThan.html#5465" class="Bound">y</a>    <a id="5470" class="Symbol">=</a> <a id="5472" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="5477" href="Chapter.Fun.LessThan.html#873" class="InductiveConstructor">z≤n</a>
<a id="5481" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5485" href="Chapter.Fun.LessThan.html#5485" class="Bound">x</a> <a id="5487" href="Chapter.Fun.LessThan.html#5419" class="Function Operator">≤?</a> <a id="5490" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="5495" class="Symbol">=</a> <a id="5497" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="5502" class="Symbol">λ</a> <a id="5504" class="Symbol">()</a>
<a id="5507" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5511" href="Chapter.Fun.LessThan.html#5511" class="Bound">x</a> <a id="5513" href="Chapter.Fun.LessThan.html#5419" class="Function Operator">≤?</a> <a id="5516" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5520" href="Chapter.Fun.LessThan.html#5520" class="Bound">y</a> <a id="5522" class="Keyword">with</a> <a id="5527" href="Chapter.Fun.LessThan.html#5511" class="Bound">x</a> <a id="5529" href="Chapter.Fun.LessThan.html#5419" class="Function Operator">≤?</a> <a id="5532" href="Chapter.Fun.LessThan.html#5520" class="Bound">y</a>
<a id="5534" class="Symbol">...</a> <a id="5538" class="Symbol">|</a> <a id="5540" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="5545" href="Chapter.Fun.LessThan.html#5545" class="Bound">gt</a> <a id="5548" class="Symbol">=</a> <a id="5550" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="5555" class="Symbol">λ</a> <a id="5557" class="Symbol">{</a> <a id="5559" class="Symbol">(</a><a id="5560" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="5564" href="Chapter.Fun.LessThan.html#5564" class="Bound">le</a><a id="5566" class="Symbol">)</a> <a id="5568" class="Symbol">→</a> <a id="5570" href="Chapter.Fun.LessThan.html#5545" class="Bound">gt</a> <a id="5573" href="Chapter.Fun.LessThan.html#5564" class="Bound">le</a> <a id="5576" class="Symbol">}</a>
<a id="5578" class="Symbol">...</a> <a id="5582" class="Symbol">|</a> <a id="5584" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="5589" href="Chapter.Fun.LessThan.html#5589" class="Bound">le</a> <a id="5592" class="Symbol">=</a> <a id="5594" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="5599" class="Symbol">(</a><a id="5600" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="5604" href="Chapter.Fun.LessThan.html#5589" class="Bound">le</a><a id="5606" class="Symbol">)</a>

<a id="_&lt;_"></a><a id="5609" href="Chapter.Fun.LessThan.html#5609" class="Function Operator">_&lt;_</a> <a id="5613" class="Symbol">:</a> <a id="5615" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="5617" class="Symbol">→</a> <a id="5619" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="5621" class="Symbol">→</a> <a id="5623" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="5627" href="Chapter.Fun.LessThan.html#5627" class="Bound">x</a> <a id="5629" href="Chapter.Fun.LessThan.html#5609" class="Function Operator">&lt;</a> <a id="5631" href="Chapter.Fun.LessThan.html#5631" class="Bound">y</a> <a id="5633" class="Symbol">=</a> <a id="5635" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5639" href="Chapter.Fun.LessThan.html#5627" class="Bound">x</a> <a id="5641" href="Chapter.Fun.LessThan.html#847" class="Datatype Operator">≤</a> <a id="5643" href="Chapter.Fun.LessThan.html#5631" class="Bound">y</a>

<a id="5646" class="Comment">-- EXERCISE 2</a>

<a id="5661" class="Comment">-- ...</a>

<a id="5669" class="Comment">-- EXERCISE 3</a>

<a id="lt-irrefl"></a><a id="5684" href="Chapter.Fun.LessThan.html#5684" class="Function">lt-irrefl</a> <a id="5694" class="Symbol">:</a> <a id="5696" class="Symbol">∀{</a><a id="5698" href="Chapter.Fun.LessThan.html#5698" class="Bound">x</a> <a id="5700" class="Symbol">:</a> <a id="5702" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="5703" class="Symbol">}</a> <a id="5705" class="Symbol">→</a> <a id="5707" href="Relation.Nullary.Negation.Core.html#677" class="Function Operator">¬</a> <a id="5709" class="Symbol">(</a><a id="5710" href="Chapter.Fun.LessThan.html#5698" class="Bound">x</a> <a id="5712" href="Chapter.Fun.LessThan.html#5609" class="Function Operator">&lt;</a> <a id="5714" href="Chapter.Fun.LessThan.html#5698" class="Bound">x</a><a id="5715" class="Symbol">)</a>
<a id="5717" href="Chapter.Fun.LessThan.html#5684" class="Function">lt-irrefl</a> <a id="5727" class="Symbol">{</a><a id="5728" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5732" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="5736" class="Symbol">}</a>     <a id="5742" class="Symbol">(</a><a id="5743" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="5747" class="Symbol">())</a>
<a id="5751" href="Chapter.Fun.LessThan.html#5684" class="Function">lt-irrefl</a> <a id="5761" class="Symbol">{</a><a id="5762" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5766" class="Symbol">(</a><a id="5767" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5771" class="Symbol">_)}</a> <a id="5775" class="Symbol">(</a><a id="5776" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="5780" class="Symbol">(</a><a id="5781" href="Chapter.Fun.LessThan.html#898" class="InductiveConstructor">s≤s</a> <a id="5785" href="Chapter.Fun.LessThan.html#5785" class="Bound">lt</a><a id="5787" class="Symbol">))</a> <a id="5790" class="Symbol">=</a> <a id="5792" href="Chapter.Fun.LessThan.html#5684" class="Function">lt-irrefl</a> <a id="5802" href="Chapter.Fun.LessThan.html#5785" class="Bound">lt</a>

<a id="5806" class="Comment">-- ...</a>
</pre>{:.solution}
