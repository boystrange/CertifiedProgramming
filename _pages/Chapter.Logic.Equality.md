---
title: Equality
prev:  Chapter.Logic.Predicates
---

<!--
<pre class="Agda"><a id="67" class="Symbol">{-#</a> <a id="71" class="Keyword">OPTIONS</a> <a id="79" class="Pragma">--allow-unsolved-metas</a> <a id="102" class="Symbol">#-}</a>
</pre>-->

<pre class="Agda"><a id="119" class="Keyword">module</a> <a id="126" href="Chapter.Logic.Equality.html" class="Module">Chapter.Logic.Equality</a> <a id="149" class="Keyword">where</a>
</pre>
We have now all the necessary ingredients to understand how
propositional equality is defined in Agda.

## Imports

<pre class="Agda"><a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="Data.Empty.html" class="Module">Data.Empty</a>
<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="Data.Bool.html" class="Module">Data.Bool</a>
<a id="325" class="Keyword">open</a> <a id="330" class="Keyword">import</a> <a id="337" href="Data.Nat.html" class="Module">Data.Nat</a>
<a id="346" class="Keyword">open</a> <a id="351" class="Keyword">import</a> <a id="358" href="Data.List.html" class="Module">Data.List</a>
<a id="368" class="Keyword">open</a> <a id="373" class="Keyword">import</a> <a id="380" href="Data.Product.html" class="Module">Data.Product</a>
<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="Relation.Nullary.html" class="Module">Relation.Nullary</a>
</pre>
## Propositional equality

Propositional equality is nothing but an inductive family with an
implicit parameter `A` (the type of the terms being compared), a
parameter `x` (the leftmost term being compared) and an index (the
rightmost term being compared).

<pre class="Agda"><a id="689" class="Keyword">infix</a> <a id="695" class="Number">4</a> <a id="697" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">_≡_</a>

<a id="702" class="Keyword">data</a> <a id="_≡_"></a><a id="707" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">_≡_</a> <a id="711" class="Symbol">{</a><a id="712" href="Chapter.Logic.Equality.html#712" class="Bound">A</a> <a id="714" class="Symbol">:</a> <a id="716" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="719" class="Symbol">}</a> <a id="721" class="Symbol">(</a><a id="722" href="Chapter.Logic.Equality.html#722" class="Bound">x</a> <a id="724" class="Symbol">:</a> <a id="726" href="Chapter.Logic.Equality.html#712" class="Bound">A</a><a id="727" class="Symbol">)</a> <a id="729" class="Symbol">:</a> <a id="731" href="Chapter.Logic.Equality.html#712" class="Bound">A</a> <a id="733" class="Symbol">→</a> <a id="735" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="739" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="747" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="752" class="Symbol">:</a> <a id="754" href="Chapter.Logic.Equality.html#722" class="Bound">x</a> <a id="756" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="758" href="Chapter.Logic.Equality.html#722" class="Bound">x</a>
</pre>
As we can see from its definition, there is just one way of proving
an equality `x ≡ y`, namely by using the constructor `refl`, which
imposes the two compared terms to be the same `x`. The name of this
constructor is intended to suggest that we are using the
*reflexivity* property of equality: every term is equal to
itself. In general, since Agda considers two terms to be "the same"
if they have the same normal form, we can use `refl` to construct
equality proofs for any two terms `x` and `y` that have the same
normal form. We have already seen a few examples of this when
proving [properties of boolean
values](Chapter.Intro.BoolProperties.html) and when introducing
[natural numbers](Chapter.Intro.NaturalNumbers.html).

<pre class="Agda"><a id="1499" href="Chapter.Logic.Equality.html#1499" class="Function">_</a> <a id="1501" class="Symbol">:</a> <a id="1503" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="1507" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a> <a id="1512" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="1514" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a>
<a id="1520" class="Symbol">_</a> <a id="1522" class="Symbol">=</a> <a id="1524" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a>

<a id="1530" href="Chapter.Logic.Equality.html#1530" class="Function">_</a> <a id="1532" class="Symbol">:</a> <a id="1534" class="Number">1</a> <a id="1536" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="1538" class="Number">2</a> <a id="1540" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="1542" class="Number">3</a>
<a id="1544" class="Symbol">_</a> <a id="1546" class="Symbol">=</a> <a id="1548" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a>
</pre>
## Symmetry and transitivity

At first, it may be surprising that there are no ways of proving the
equality of two terms `x` and `y` other than reflexivity. After all,
we expect equality to be an equivalence relation, hence it should
also be *symmetric* and *transitive*. As it turns out, symmetry and
transitivity of equality can be proved as consequences of
reflexivity.

Let us start with symmetry. The property that we want to prove is
stated as follows.

<pre class="Agda"><a id="sym"></a><a id="2022" href="Chapter.Logic.Equality.html#2022" class="Function">sym</a> <a id="2026" class="Symbol">:</a> <a id="2028" class="Symbol">∀{</a><a id="2030" href="Chapter.Logic.Equality.html#2030" class="Bound">A</a> <a id="2032" class="Symbol">:</a> <a id="2034" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2037" class="Symbol">}</a> <a id="2039" class="Symbol">{</a><a id="2040" href="Chapter.Logic.Equality.html#2040" class="Bound">x</a> <a id="2042" href="Chapter.Logic.Equality.html#2042" class="Bound">y</a> <a id="2044" class="Symbol">:</a> <a id="2046" href="Chapter.Logic.Equality.html#2030" class="Bound">A</a><a id="2047" class="Symbol">}</a> <a id="2049" class="Symbol">→</a> <a id="2051" href="Chapter.Logic.Equality.html#2040" class="Bound">x</a> <a id="2053" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="2055" href="Chapter.Logic.Equality.html#2042" class="Bound">y</a> <a id="2057" class="Symbol">→</a> <a id="2059" href="Chapter.Logic.Equality.html#2042" class="Bound">y</a> <a id="2061" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="2063" href="Chapter.Logic.Equality.html#2040" class="Bound">x</a>
<a id="2065" href="Chapter.Logic.Equality.html#2022" class="Function">sym</a> <a id="2069" class="Symbol">{_}</a> <a id="2073" class="Symbol">{</a><a id="2074" href="Chapter.Logic.Equality.html#2074" class="Bound">x</a><a id="2075" class="Symbol">}</a> <a id="2077" class="Symbol">{</a><a id="2078" href="Chapter.Logic.Equality.html#2078" class="Bound">y</a><a id="2079" class="Symbol">}</a> <a id="2081" href="Chapter.Logic.Equality.html#2081" class="Bound">eq</a> <a id="2084" class="Symbol">=</a> <a id="2086" class="Hole">{!!}</a>
</pre>
For the sake of illustration, we have given names to the implicit
arguments `x` and `y`, whereas we have kept `A` unnamed as it plays
no interesting role in the proof. By inspecting the hole, we see
that we have to provide a proof of `y ≡ x` in a context where we
have two elements `x` and `y` of type `A` and a term `eq` of type `x
≡ y`. Given the current situation, there isn't much we can do except
recall that equality is an inductively defined data type. As such,
we can perform case analysis on `eq`.

<pre class="Agda"><a id="sym₁"></a><a id="2608" href="Chapter.Logic.Equality.html#2608" class="Function">sym₁</a> <a id="2613" class="Symbol">:</a> <a id="2615" class="Symbol">∀{</a><a id="2617" href="Chapter.Logic.Equality.html#2617" class="Bound">A</a> <a id="2619" class="Symbol">:</a> <a id="2621" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2624" class="Symbol">}</a> <a id="2626" class="Symbol">{</a><a id="2627" href="Chapter.Logic.Equality.html#2627" class="Bound">x</a> <a id="2629" href="Chapter.Logic.Equality.html#2629" class="Bound">y</a> <a id="2631" class="Symbol">:</a> <a id="2633" href="Chapter.Logic.Equality.html#2617" class="Bound">A</a><a id="2634" class="Symbol">}</a> <a id="2636" class="Symbol">→</a> <a id="2638" href="Chapter.Logic.Equality.html#2627" class="Bound">x</a> <a id="2640" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="2642" href="Chapter.Logic.Equality.html#2629" class="Bound">y</a> <a id="2644" class="Symbol">→</a> <a id="2646" href="Chapter.Logic.Equality.html#2629" class="Bound">y</a> <a id="2648" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="2650" href="Chapter.Logic.Equality.html#2627" class="Bound">x</a>
<a id="2652" href="Chapter.Logic.Equality.html#2608" class="Function">sym₁</a> <a id="2657" class="Symbol">{_}</a> <a id="2661" class="Symbol">{</a><a id="2662" href="Chapter.Logic.Equality.html#2662" class="Bound">x</a><a id="2663" class="Symbol">}</a> <a id="2665" class="Symbol">{</a><a id="2666" href="Chapter.Logic.Equality.html#2666" class="Bound">y</a><a id="2667" class="Symbol">}</a> <a id="2669" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="2674" class="Symbol">=</a> <a id="2676" class="Hole">{!!}</a>
</pre>
As expected, the `eq` argument has turned into `refl`. However, case
analysis has also changed the set of assumptions that we are working
with in order to prove the goal. In particular, the context now
contains a *unification constraint* of the form `y = x` meaning that
the two variables `x` and `y` have been *unified* as a consequence
of the hypothesis `x ≡ y`. The reason is that the only way the
constructor `refl` can be used as evidence for the equality `x ≡ y`
is when `x` and `y` are the same (up to Agda's definitional
equality).

This case analysis has another interesting effect on the goal we are
supposed to prove. As as result of the unification between `x` and
`y`, the type of the hole has changed from `y ≡ x` to `x ≡ x`. This
means that we are now able to complete the proof, since `refl` will
provide evidence of the fact that `x` is equal to itself.

<pre class="Agda"><a id="sym₂"></a><a id="3562" href="Chapter.Logic.Equality.html#3562" class="Function">sym₂</a> <a id="3567" class="Symbol">:</a> <a id="3569" class="Symbol">∀{</a><a id="3571" href="Chapter.Logic.Equality.html#3571" class="Bound">A</a> <a id="3573" class="Symbol">:</a> <a id="3575" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3578" class="Symbol">}</a> <a id="3580" class="Symbol">{</a><a id="3581" href="Chapter.Logic.Equality.html#3581" class="Bound">x</a> <a id="3583" href="Chapter.Logic.Equality.html#3583" class="Bound">y</a> <a id="3585" class="Symbol">:</a> <a id="3587" href="Chapter.Logic.Equality.html#3571" class="Bound">A</a><a id="3588" class="Symbol">}</a> <a id="3590" class="Symbol">→</a> <a id="3592" href="Chapter.Logic.Equality.html#3581" class="Bound">x</a> <a id="3594" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="3596" href="Chapter.Logic.Equality.html#3583" class="Bound">y</a> <a id="3598" class="Symbol">→</a> <a id="3600" href="Chapter.Logic.Equality.html#3583" class="Bound">y</a> <a id="3602" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="3604" href="Chapter.Logic.Equality.html#3581" class="Bound">x</a>
<a id="3606" href="Chapter.Logic.Equality.html#3562" class="Function">sym₂</a> <a id="3611" class="Symbol">{_}</a> <a id="3615" class="Symbol">{</a><a id="3616" href="Chapter.Logic.Equality.html#3616" class="Bound">x</a><a id="3617" class="Symbol">}</a> <a id="3619" class="Symbol">{</a><a id="3620" href="Chapter.Logic.Equality.html#3620" class="Bound">y</a><a id="3621" class="Symbol">}</a> <a id="3623" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="3628" class="Symbol">=</a> <a id="3630" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a>
</pre>
The proof that equality is transitive follows a similar pattern.

<pre class="Agda"><a id="trans"></a><a id="3710" href="Chapter.Logic.Equality.html#3710" class="Function">trans</a> <a id="3716" class="Symbol">:</a> <a id="3718" class="Symbol">∀{</a><a id="3720" href="Chapter.Logic.Equality.html#3720" class="Bound">A</a> <a id="3722" class="Symbol">:</a> <a id="3724" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3727" class="Symbol">}</a> <a id="3729" class="Symbol">{</a><a id="3730" href="Chapter.Logic.Equality.html#3730" class="Bound">x</a> <a id="3732" href="Chapter.Logic.Equality.html#3732" class="Bound">y</a> <a id="3734" href="Chapter.Logic.Equality.html#3734" class="Bound">z</a> <a id="3736" class="Symbol">:</a> <a id="3738" href="Chapter.Logic.Equality.html#3720" class="Bound">A</a><a id="3739" class="Symbol">}</a> <a id="3741" class="Symbol">→</a> <a id="3743" href="Chapter.Logic.Equality.html#3730" class="Bound">x</a> <a id="3745" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="3747" href="Chapter.Logic.Equality.html#3732" class="Bound">y</a> <a id="3749" class="Symbol">→</a> <a id="3751" href="Chapter.Logic.Equality.html#3732" class="Bound">y</a> <a id="3753" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="3755" href="Chapter.Logic.Equality.html#3734" class="Bound">z</a> <a id="3757" class="Symbol">→</a> <a id="3759" href="Chapter.Logic.Equality.html#3730" class="Bound">x</a> <a id="3761" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="3763" href="Chapter.Logic.Equality.html#3734" class="Bound">z</a>
<a id="3765" href="Chapter.Logic.Equality.html#3710" class="Function">trans</a> <a id="3771" href="Chapter.Logic.Equality.html#3771" class="Bound">eq1</a> <a id="3775" href="Chapter.Logic.Equality.html#3775" class="Bound">eq2</a> <a id="3779" class="Symbol">=</a> <a id="3781" class="Hole">{!!}</a>
</pre>
By performing case analysis on `eq1` and `eq2` we effectively unify
the three (implicit) arguments `x`, `y` and `z`, so that we end up
with having to prove `x ≡ x`, which can be done by reflexivity.

<pre class="Agda"><a id="trans₁"></a><a id="3995" href="Chapter.Logic.Equality.html#3995" class="Function">trans₁</a> <a id="4002" class="Symbol">:</a> <a id="4004" class="Symbol">∀{</a><a id="4006" href="Chapter.Logic.Equality.html#4006" class="Bound">A</a> <a id="4008" class="Symbol">:</a> <a id="4010" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4013" class="Symbol">}</a> <a id="4015" class="Symbol">{</a><a id="4016" href="Chapter.Logic.Equality.html#4016" class="Bound">x</a> <a id="4018" href="Chapter.Logic.Equality.html#4018" class="Bound">y</a> <a id="4020" href="Chapter.Logic.Equality.html#4020" class="Bound">z</a> <a id="4022" class="Symbol">:</a> <a id="4024" href="Chapter.Logic.Equality.html#4006" class="Bound">A</a><a id="4025" class="Symbol">}</a> <a id="4027" class="Symbol">→</a> <a id="4029" href="Chapter.Logic.Equality.html#4016" class="Bound">x</a> <a id="4031" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="4033" href="Chapter.Logic.Equality.html#4018" class="Bound">y</a> <a id="4035" class="Symbol">→</a> <a id="4037" href="Chapter.Logic.Equality.html#4018" class="Bound">y</a> <a id="4039" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="4041" href="Chapter.Logic.Equality.html#4020" class="Bound">z</a> <a id="4043" class="Symbol">→</a> <a id="4045" href="Chapter.Logic.Equality.html#4016" class="Bound">x</a> <a id="4047" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="4049" href="Chapter.Logic.Equality.html#4020" class="Bound">z</a>
<a id="4051" href="Chapter.Logic.Equality.html#3995" class="Function">trans₁</a> <a id="4058" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="4063" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="4068" class="Symbol">=</a> <a id="4070" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a>
</pre>
## Congruence and substitution

In the chapter on [natural
numbers](Chapter.Intro.NaturalNumbers.html) we have used the
congruence property of function application, namely the property
that, if `x ≡ y`, then `f x ≡ f y`. We can now see how this theorem
is proved.

<pre class="Agda"><a id="cong"></a><a id="4349" href="Chapter.Logic.Equality.html#4349" class="Function">cong</a> <a id="4354" class="Symbol">:</a> <a id="4356" class="Symbol">∀{</a><a id="4358" href="Chapter.Logic.Equality.html#4358" class="Bound">A</a> <a id="4360" href="Chapter.Logic.Equality.html#4360" class="Bound">B</a> <a id="4362" class="Symbol">:</a> <a id="4364" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4367" class="Symbol">}</a> <a id="4369" class="Symbol">(</a><a id="4370" href="Chapter.Logic.Equality.html#4370" class="Bound">f</a> <a id="4372" class="Symbol">:</a> <a id="4374" href="Chapter.Logic.Equality.html#4358" class="Bound">A</a> <a id="4376" class="Symbol">→</a> <a id="4378" href="Chapter.Logic.Equality.html#4360" class="Bound">B</a><a id="4379" class="Symbol">)</a> <a id="4381" class="Symbol">{</a><a id="4382" href="Chapter.Logic.Equality.html#4382" class="Bound">x</a> <a id="4384" href="Chapter.Logic.Equality.html#4384" class="Bound">y</a> <a id="4386" class="Symbol">:</a> <a id="4388" href="Chapter.Logic.Equality.html#4358" class="Bound">A</a><a id="4389" class="Symbol">}</a> <a id="4391" class="Symbol">→</a> <a id="4393" href="Chapter.Logic.Equality.html#4382" class="Bound">x</a> <a id="4395" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="4397" href="Chapter.Logic.Equality.html#4384" class="Bound">y</a> <a id="4399" class="Symbol">→</a> <a id="4401" href="Chapter.Logic.Equality.html#4370" class="Bound">f</a> <a id="4403" href="Chapter.Logic.Equality.html#4382" class="Bound">x</a> <a id="4405" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="4407" href="Chapter.Logic.Equality.html#4370" class="Bound">f</a> <a id="4409" href="Chapter.Logic.Equality.html#4384" class="Bound">y</a>
<a id="4411" href="Chapter.Logic.Equality.html#4349" class="Function">cong</a> <a id="4416" class="Symbol">_</a> <a id="4418" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="4423" class="Symbol">=</a> <a id="4425" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a>
</pre>
Once again we rely on case analysis to force the unification of `x`
and `y`, thereby turning congruence into another case of
reflexivity. Another principle related to equality is
*substitution*, asserting that if `x ≡ y` and we know that `x`
satisfies some predicate `P`, then `y` also satisfies the same
predicate.

<pre class="Agda"><a id="subst"></a><a id="4756" href="Chapter.Logic.Equality.html#4756" class="Function">subst</a> <a id="4762" class="Symbol">:</a> <a id="4764" class="Symbol">∀{</a><a id="4766" href="Chapter.Logic.Equality.html#4766" class="Bound">A</a> <a id="4768" class="Symbol">:</a> <a id="4770" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4773" class="Symbol">}</a> <a id="4775" class="Symbol">(</a><a id="4776" href="Chapter.Logic.Equality.html#4776" class="Bound">P</a> <a id="4778" class="Symbol">:</a> <a id="4780" href="Chapter.Logic.Equality.html#4766" class="Bound">A</a> <a id="4782" class="Symbol">→</a> <a id="4784" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4787" class="Symbol">)</a> <a id="4789" class="Symbol">{</a><a id="4790" href="Chapter.Logic.Equality.html#4790" class="Bound">x</a> <a id="4792" href="Chapter.Logic.Equality.html#4792" class="Bound">y</a> <a id="4794" class="Symbol">:</a> <a id="4796" href="Chapter.Logic.Equality.html#4766" class="Bound">A</a><a id="4797" class="Symbol">}</a> <a id="4799" class="Symbol">→</a> <a id="4801" href="Chapter.Logic.Equality.html#4790" class="Bound">x</a> <a id="4803" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="4805" href="Chapter.Logic.Equality.html#4792" class="Bound">y</a> <a id="4807" class="Symbol">→</a> <a id="4809" href="Chapter.Logic.Equality.html#4776" class="Bound">P</a> <a id="4811" href="Chapter.Logic.Equality.html#4790" class="Bound">x</a> <a id="4813" class="Symbol">→</a> <a id="4815" href="Chapter.Logic.Equality.html#4776" class="Bound">P</a> <a id="4817" href="Chapter.Logic.Equality.html#4792" class="Bound">y</a>
<a id="4819" href="Chapter.Logic.Equality.html#4756" class="Function">subst</a> <a id="4825" class="Symbol">_</a> <a id="4827" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="4832" href="Chapter.Logic.Equality.html#4832" class="Bound">p</a> <a id="4834" class="Symbol">=</a> <a id="4836" href="Chapter.Logic.Equality.html#4832" class="Bound">p</a>
</pre>
## Homework

1. Prove that `suc` is injective, namely the theorem
   `suc-injective : ∀{x y : ℕ} → suc x ≡ suc y → x ≡ y`.
2. Define the relation `_≢_` as the negation of equality.
   Prove that `zero` is different from any other natural number, namely
   the theorem `zero-suc : ∀{x : ℕ} → zero ≢ suc x`
3. Prove the theorem `ne-ne : ∀{x y : ℕ} → suc x ≢ suc y → x ≢ y`.
4. Prove that `_∷_` is injective, namely the theorem
   `∷-injective : ∀{A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys →
   x ≡ y × xs ≡ ys`.
5. Prove a version of `cong` for two-argument functions, namely the
   theorem `cong2 : ∀{A B C : Set} (f : A → B → C) {x y : A} {u v :
   B} → x ≡ y → u ≡ v → f x u ≡ f y v`

<pre class="Agda"><a id="5545" class="Comment">-- EXERCISE 1</a>

<a id="suc-injective"></a><a id="5560" href="Chapter.Logic.Equality.html#5560" class="Function">suc-injective</a> <a id="5574" class="Symbol">:</a> <a id="5576" class="Symbol">∀{</a><a id="5578" href="Chapter.Logic.Equality.html#5578" class="Bound">x</a> <a id="5580" href="Chapter.Logic.Equality.html#5580" class="Bound">y</a> <a id="5582" class="Symbol">:</a> <a id="5584" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="5585" class="Symbol">}</a> <a id="5587" class="Symbol">→</a> <a id="5589" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5593" href="Chapter.Logic.Equality.html#5578" class="Bound">x</a> <a id="5595" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="5597" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5601" href="Chapter.Logic.Equality.html#5580" class="Bound">y</a> <a id="5603" class="Symbol">→</a> <a id="5605" href="Chapter.Logic.Equality.html#5578" class="Bound">x</a> <a id="5607" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="5609" href="Chapter.Logic.Equality.html#5580" class="Bound">y</a>
<a id="5611" href="Chapter.Logic.Equality.html#5560" class="Function">suc-injective</a> <a id="5625" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="5630" class="Symbol">=</a> <a id="5632" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a>

<a id="5638" class="Comment">-- EXERCISE 2</a>

<a id="_≢_"></a><a id="5653" href="Chapter.Logic.Equality.html#5653" class="Function Operator">_≢_</a> <a id="5657" class="Symbol">:</a> <a id="5659" class="Symbol">∀{</a><a id="5661" href="Chapter.Logic.Equality.html#5661" class="Bound">A</a> <a id="5663" class="Symbol">:</a> <a id="5665" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5668" class="Symbol">}</a> <a id="5670" class="Symbol">→</a> <a id="5672" href="Chapter.Logic.Equality.html#5661" class="Bound">A</a> <a id="5674" class="Symbol">→</a> <a id="5676" href="Chapter.Logic.Equality.html#5661" class="Bound">A</a> <a id="5678" class="Symbol">→</a> <a id="5680" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="5684" href="Chapter.Logic.Equality.html#5684" class="Bound">x</a> <a id="5686" href="Chapter.Logic.Equality.html#5653" class="Function Operator">≢</a> <a id="5688" href="Chapter.Logic.Equality.html#5688" class="Bound">y</a> <a id="5690" class="Symbol">=</a> <a id="5692" href="Relation.Nullary.Negation.Core.html#677" class="Function Operator">¬</a> <a id="5694" class="Symbol">(</a><a id="5695" href="Chapter.Logic.Equality.html#5684" class="Bound">x</a> <a id="5697" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="5699" href="Chapter.Logic.Equality.html#5688" class="Bound">y</a><a id="5700" class="Symbol">)</a>

<a id="zero-suc"></a><a id="5703" href="Chapter.Logic.Equality.html#5703" class="Function">zero-suc</a> <a id="5712" class="Symbol">:</a> <a id="5714" class="Symbol">∀{</a><a id="5716" href="Chapter.Logic.Equality.html#5716" class="Bound">x</a> <a id="5718" class="Symbol">:</a> <a id="5720" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="5721" class="Symbol">}</a> <a id="5723" class="Symbol">→</a> <a id="5725" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="5730" href="Chapter.Logic.Equality.html#5653" class="Function Operator">≢</a> <a id="5732" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5736" href="Chapter.Logic.Equality.html#5716" class="Bound">x</a>
<a id="5738" href="Chapter.Logic.Equality.html#5703" class="Function">zero-suc</a> <a id="5747" class="Symbol">()</a>

<a id="5751" class="Comment">-- EXERCISE 3</a>

<a id="ne-ne"></a><a id="5766" href="Chapter.Logic.Equality.html#5766" class="Function">ne-ne</a> <a id="5772" class="Symbol">:</a> <a id="5774" class="Symbol">∀{</a><a id="5776" href="Chapter.Logic.Equality.html#5776" class="Bound">x</a> <a id="5778" href="Chapter.Logic.Equality.html#5778" class="Bound">y</a> <a id="5780" class="Symbol">:</a> <a id="5782" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="5783" class="Symbol">}</a> <a id="5785" class="Symbol">→</a> <a id="5787" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5791" href="Chapter.Logic.Equality.html#5776" class="Bound">x</a> <a id="5793" href="Chapter.Logic.Equality.html#5653" class="Function Operator">≢</a> <a id="5795" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5799" href="Chapter.Logic.Equality.html#5778" class="Bound">y</a> <a id="5801" class="Symbol">→</a> <a id="5803" href="Chapter.Logic.Equality.html#5776" class="Bound">x</a> <a id="5805" href="Chapter.Logic.Equality.html#5653" class="Function Operator">≢</a> <a id="5807" href="Chapter.Logic.Equality.html#5778" class="Bound">y</a>
<a id="5809" href="Chapter.Logic.Equality.html#5766" class="Function">ne-ne</a> <a id="5815" href="Chapter.Logic.Equality.html#5815" class="Bound">neq</a> <a id="5819" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="5824" class="Symbol">=</a> <a id="5826" href="Chapter.Logic.Equality.html#5815" class="Bound">neq</a> <a id="5830" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a>

<a id="5836" class="Comment">-- EXERCISE 4</a>

<a id="∷-injective"></a><a id="5851" href="Chapter.Logic.Equality.html#5851" class="Function">∷-injective</a> <a id="5863" class="Symbol">:</a> <a id="5865" class="Symbol">∀{</a><a id="5867" href="Chapter.Logic.Equality.html#5867" class="Bound">A</a> <a id="5869" class="Symbol">:</a> <a id="5871" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5874" class="Symbol">}</a> <a id="5876" class="Symbol">{</a><a id="5877" href="Chapter.Logic.Equality.html#5877" class="Bound">x</a> <a id="5879" href="Chapter.Logic.Equality.html#5879" class="Bound">y</a> <a id="5881" class="Symbol">:</a> <a id="5883" href="Chapter.Logic.Equality.html#5867" class="Bound">A</a><a id="5884" class="Symbol">}</a> <a id="5886" class="Symbol">{</a><a id="5887" href="Chapter.Logic.Equality.html#5887" class="Bound">xs</a> <a id="5890" href="Chapter.Logic.Equality.html#5890" class="Bound">ys</a> <a id="5893" class="Symbol">:</a> <a id="5895" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="5900" href="Chapter.Logic.Equality.html#5867" class="Bound">A</a><a id="5901" class="Symbol">}</a> <a id="5903" class="Symbol">→</a> <a id="5905" href="Chapter.Logic.Equality.html#5877" class="Bound">x</a> <a id="5907" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="5909" href="Chapter.Logic.Equality.html#5887" class="Bound">xs</a> <a id="5912" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="5914" href="Chapter.Logic.Equality.html#5879" class="Bound">y</a> <a id="5916" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="5918" href="Chapter.Logic.Equality.html#5890" class="Bound">ys</a> <a id="5921" class="Symbol">→</a> <a id="5923" href="Chapter.Logic.Equality.html#5877" class="Bound">x</a> <a id="5925" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="5927" href="Chapter.Logic.Equality.html#5879" class="Bound">y</a> <a id="5929" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="5931" href="Chapter.Logic.Equality.html#5887" class="Bound">xs</a> <a id="5934" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="5936" href="Chapter.Logic.Equality.html#5890" class="Bound">ys</a>
<a id="5939" href="Chapter.Logic.Equality.html#5851" class="Function">∷-injective</a> <a id="5951" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="5956" class="Symbol">=</a> <a id="5958" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="5963" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="5965" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a>

<a id="5971" class="Comment">-- EXERCISE 5</a>

<a id="cong2"></a><a id="5986" href="Chapter.Logic.Equality.html#5986" class="Function">cong2</a> <a id="5992" class="Symbol">:</a> <a id="5994" class="Symbol">∀{</a><a id="5996" href="Chapter.Logic.Equality.html#5996" class="Bound">A</a> <a id="5998" href="Chapter.Logic.Equality.html#5998" class="Bound">B</a> <a id="6000" href="Chapter.Logic.Equality.html#6000" class="Bound">C</a> <a id="6002" class="Symbol">:</a> <a id="6004" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="6007" class="Symbol">}</a> <a id="6009" class="Symbol">(</a><a id="6010" href="Chapter.Logic.Equality.html#6010" class="Bound">f</a> <a id="6012" class="Symbol">:</a> <a id="6014" href="Chapter.Logic.Equality.html#5996" class="Bound">A</a> <a id="6016" class="Symbol">→</a> <a id="6018" href="Chapter.Logic.Equality.html#5998" class="Bound">B</a> <a id="6020" class="Symbol">→</a> <a id="6022" href="Chapter.Logic.Equality.html#6000" class="Bound">C</a><a id="6023" class="Symbol">)</a> <a id="6025" class="Symbol">{</a><a id="6026" href="Chapter.Logic.Equality.html#6026" class="Bound">x</a> <a id="6028" href="Chapter.Logic.Equality.html#6028" class="Bound">y</a> <a id="6030" class="Symbol">:</a> <a id="6032" href="Chapter.Logic.Equality.html#5996" class="Bound">A</a><a id="6033" class="Symbol">}</a> <a id="6035" class="Symbol">{</a><a id="6036" href="Chapter.Logic.Equality.html#6036" class="Bound">u</a> <a id="6038" href="Chapter.Logic.Equality.html#6038" class="Bound">v</a> <a id="6040" class="Symbol">:</a> <a id="6042" href="Chapter.Logic.Equality.html#5998" class="Bound">B</a><a id="6043" class="Symbol">}</a> <a id="6045" class="Symbol">→</a> <a id="6047" href="Chapter.Logic.Equality.html#6026" class="Bound">x</a> <a id="6049" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="6051" href="Chapter.Logic.Equality.html#6028" class="Bound">y</a> <a id="6053" class="Symbol">→</a> <a id="6055" href="Chapter.Logic.Equality.html#6036" class="Bound">u</a> <a id="6057" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="6059" href="Chapter.Logic.Equality.html#6038" class="Bound">v</a> <a id="6061" class="Symbol">→</a> <a id="6063" href="Chapter.Logic.Equality.html#6010" class="Bound">f</a> <a id="6065" href="Chapter.Logic.Equality.html#6026" class="Bound">x</a> <a id="6067" href="Chapter.Logic.Equality.html#6036" class="Bound">u</a> <a id="6069" href="Chapter.Logic.Equality.html#707" class="Datatype Operator">≡</a> <a id="6071" href="Chapter.Logic.Equality.html#6010" class="Bound">f</a> <a id="6073" href="Chapter.Logic.Equality.html#6028" class="Bound">y</a> <a id="6075" href="Chapter.Logic.Equality.html#6038" class="Bound">v</a>
<a id="6077" href="Chapter.Logic.Equality.html#5986" class="Function">cong2</a> <a id="6083" class="Symbol">_</a> <a id="6085" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="6090" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a> <a id="6095" class="Symbol">=</a> <a id="6097" href="Chapter.Logic.Equality.html#747" class="InductiveConstructor">refl</a>
</pre>{:.solution}
