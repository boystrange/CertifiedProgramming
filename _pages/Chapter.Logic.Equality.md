---
title: Equality
prev:  Chapter.Logic.Predicates
next:  Chapter.Logic.LessThan
---

<!--
<pre class="Agda"><a id="97" class="Symbol">{-#</a> <a id="101" class="Keyword">OPTIONS</a> <a id="109" class="Pragma">--allow-unsolved-metas</a> <a id="132" class="Symbol">#-}</a>
</pre>-->

<pre class="Agda"><a id="149" class="Keyword">module</a> <a id="156" href="Chapter.Logic.Equality.html" class="Module">Chapter.Logic.Equality</a> <a id="179" class="Keyword">where</a>
</pre>
We have now all the necessary ingredients to understand how
propositional equality is defined in Agda.

## Imports

<pre class="Agda"><a id="310" class="Keyword">open</a> <a id="315" class="Keyword">import</a> <a id="322" href="Data.Empty.html" class="Module">Data.Empty</a>
<a id="333" class="Keyword">open</a> <a id="338" class="Keyword">import</a> <a id="345" href="Data.Bool.html" class="Module">Data.Bool</a>
<a id="355" class="Keyword">open</a> <a id="360" class="Keyword">import</a> <a id="367" href="Data.Nat.html" class="Module">Data.Nat</a>
<a id="376" class="Keyword">open</a> <a id="381" class="Keyword">import</a> <a id="388" href="Data.List.html" class="Module">Data.List</a>
<a id="398" class="Keyword">open</a> <a id="403" class="Keyword">import</a> <a id="410" href="Data.Product.html" class="Module">Data.Product</a>
<a id="423" class="Keyword">open</a> <a id="428" class="Keyword">import</a> <a id="435" href="Relation.Nullary.html" class="Module">Relation.Nullary</a>
</pre>
## Propositional equality

Propositional equality is nothing but an inductive family with an
implicit parameter `A` (the type of the terms being compared), a
parameter `x` (the leftmost term being compared) and an index (the
rightmost term being compared).

<pre class="Agda"><a id="719" class="Keyword">infix</a> <a id="725" class="Number">4</a> <a id="727" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">_≡_</a>

<a id="732" class="Keyword">data</a> <a id="_≡_"></a><a id="737" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">_≡_</a> <a id="741" class="Symbol">{</a><a id="742" href="Chapter.Logic.Equality.html#742" class="Bound">A</a> <a id="744" class="Symbol">:</a> <a id="746" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="749" class="Symbol">}</a> <a id="751" class="Symbol">(</a><a id="752" href="Chapter.Logic.Equality.html#752" class="Bound">x</a> <a id="754" class="Symbol">:</a> <a id="756" href="Chapter.Logic.Equality.html#742" class="Bound">A</a><a id="757" class="Symbol">)</a> <a id="759" class="Symbol">:</a> <a id="761" href="Chapter.Logic.Equality.html#742" class="Bound">A</a> <a id="763" class="Symbol">→</a> <a id="765" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="769" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="777" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="782" class="Symbol">:</a> <a id="784" href="Chapter.Logic.Equality.html#752" class="Bound">x</a> <a id="786" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="788" href="Chapter.Logic.Equality.html#752" class="Bound">x</a>
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

<pre class="Agda"><a id="1529" href="Chapter.Logic.Equality.html#1529" class="Function">_</a> <a id="1531" class="Symbol">:</a> <a id="1533" href="Data.Bool.Base.html#951" class="Function">not</a> <a id="1537" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a> <a id="1542" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="1544" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a>
<a id="1550" class="Symbol">_</a> <a id="1552" class="Symbol">=</a> <a id="1554" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a>

<a id="1560" href="Chapter.Logic.Equality.html#1560" class="Function">_</a> <a id="1562" class="Symbol">:</a> <a id="1564" class="Number">1</a> <a id="1566" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="1568" class="Number">2</a> <a id="1570" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="1572" class="Number">3</a>
<a id="1574" class="Symbol">_</a> <a id="1576" class="Symbol">=</a> <a id="1578" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a>
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

<pre class="Agda"><a id="sym"></a><a id="2052" href="Chapter.Logic.Equality.html#2052" class="Function">sym</a> <a id="2056" class="Symbol">:</a> <a id="2058" class="Symbol">∀{</a><a id="2060" href="Chapter.Logic.Equality.html#2060" class="Bound">A</a> <a id="2062" class="Symbol">:</a> <a id="2064" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2067" class="Symbol">}</a> <a id="2069" class="Symbol">{</a><a id="2070" href="Chapter.Logic.Equality.html#2070" class="Bound">x</a> <a id="2072" href="Chapter.Logic.Equality.html#2072" class="Bound">y</a> <a id="2074" class="Symbol">:</a> <a id="2076" href="Chapter.Logic.Equality.html#2060" class="Bound">A</a><a id="2077" class="Symbol">}</a> <a id="2079" class="Symbol">→</a> <a id="2081" href="Chapter.Logic.Equality.html#2070" class="Bound">x</a> <a id="2083" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="2085" href="Chapter.Logic.Equality.html#2072" class="Bound">y</a> <a id="2087" class="Symbol">→</a> <a id="2089" href="Chapter.Logic.Equality.html#2072" class="Bound">y</a> <a id="2091" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="2093" href="Chapter.Logic.Equality.html#2070" class="Bound">x</a>
<a id="2095" href="Chapter.Logic.Equality.html#2052" class="Function">sym</a> <a id="2099" class="Symbol">{_}</a> <a id="2103" class="Symbol">{</a><a id="2104" href="Chapter.Logic.Equality.html#2104" class="Bound">x</a><a id="2105" class="Symbol">}</a> <a id="2107" class="Symbol">{</a><a id="2108" href="Chapter.Logic.Equality.html#2108" class="Bound">y</a><a id="2109" class="Symbol">}</a> <a id="2111" href="Chapter.Logic.Equality.html#2111" class="Bound">eq</a> <a id="2114" class="Symbol">=</a> <a id="2116" class="Hole">{!!}</a>
</pre>
For the sake of illustration, we have given names to the implicit
arguments `x` and `y`, whereas we have kept `A` unnamed as it plays
no interesting role in the proof. By inspecting the hole, we see
that we have to provide a proof of `y ≡ x` in a context where we
have two elements `x` and `y` of type `A` and a term `eq` of type `x
≡ y`. Given the current situation, there isn't much we can do except
recall that equality is an inductively defined data type. As such,
we can perform case analysis on `eq`.

<pre class="Agda"><a id="sym₁"></a><a id="2638" href="Chapter.Logic.Equality.html#2638" class="Function">sym₁</a> <a id="2643" class="Symbol">:</a> <a id="2645" class="Symbol">∀{</a><a id="2647" href="Chapter.Logic.Equality.html#2647" class="Bound">A</a> <a id="2649" class="Symbol">:</a> <a id="2651" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2654" class="Symbol">}</a> <a id="2656" class="Symbol">{</a><a id="2657" href="Chapter.Logic.Equality.html#2657" class="Bound">x</a> <a id="2659" href="Chapter.Logic.Equality.html#2659" class="Bound">y</a> <a id="2661" class="Symbol">:</a> <a id="2663" href="Chapter.Logic.Equality.html#2647" class="Bound">A</a><a id="2664" class="Symbol">}</a> <a id="2666" class="Symbol">→</a> <a id="2668" href="Chapter.Logic.Equality.html#2657" class="Bound">x</a> <a id="2670" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="2672" href="Chapter.Logic.Equality.html#2659" class="Bound">y</a> <a id="2674" class="Symbol">→</a> <a id="2676" href="Chapter.Logic.Equality.html#2659" class="Bound">y</a> <a id="2678" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="2680" href="Chapter.Logic.Equality.html#2657" class="Bound">x</a>
<a id="2682" href="Chapter.Logic.Equality.html#2638" class="Function">sym₁</a> <a id="2687" class="Symbol">{_}</a> <a id="2691" class="Symbol">{</a><a id="2692" href="Chapter.Logic.Equality.html#2692" class="Bound">x</a><a id="2693" class="Symbol">}</a> <a id="2695" class="Symbol">{</a><a id="2696" href="Chapter.Logic.Equality.html#2696" class="Bound">y</a><a id="2697" class="Symbol">}</a> <a id="2699" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="2704" class="Symbol">=</a> <a id="2706" class="Hole">{!!}</a>
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

<pre class="Agda"><a id="sym₂"></a><a id="3592" href="Chapter.Logic.Equality.html#3592" class="Function">sym₂</a> <a id="3597" class="Symbol">:</a> <a id="3599" class="Symbol">∀{</a><a id="3601" href="Chapter.Logic.Equality.html#3601" class="Bound">A</a> <a id="3603" class="Symbol">:</a> <a id="3605" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3608" class="Symbol">}</a> <a id="3610" class="Symbol">{</a><a id="3611" href="Chapter.Logic.Equality.html#3611" class="Bound">x</a> <a id="3613" href="Chapter.Logic.Equality.html#3613" class="Bound">y</a> <a id="3615" class="Symbol">:</a> <a id="3617" href="Chapter.Logic.Equality.html#3601" class="Bound">A</a><a id="3618" class="Symbol">}</a> <a id="3620" class="Symbol">→</a> <a id="3622" href="Chapter.Logic.Equality.html#3611" class="Bound">x</a> <a id="3624" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="3626" href="Chapter.Logic.Equality.html#3613" class="Bound">y</a> <a id="3628" class="Symbol">→</a> <a id="3630" href="Chapter.Logic.Equality.html#3613" class="Bound">y</a> <a id="3632" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="3634" href="Chapter.Logic.Equality.html#3611" class="Bound">x</a>
<a id="3636" href="Chapter.Logic.Equality.html#3592" class="Function">sym₂</a> <a id="3641" class="Symbol">{_}</a> <a id="3645" class="Symbol">{</a><a id="3646" href="Chapter.Logic.Equality.html#3646" class="Bound">x</a><a id="3647" class="Symbol">}</a> <a id="3649" class="Symbol">{</a><a id="3650" href="Chapter.Logic.Equality.html#3650" class="Bound">y</a><a id="3651" class="Symbol">}</a> <a id="3653" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="3658" class="Symbol">=</a> <a id="3660" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a>
</pre>
The proof that equality is transitive follows a similar pattern.

<pre class="Agda"><a id="trans"></a><a id="3740" href="Chapter.Logic.Equality.html#3740" class="Function">trans</a> <a id="3746" class="Symbol">:</a> <a id="3748" class="Symbol">∀{</a><a id="3750" href="Chapter.Logic.Equality.html#3750" class="Bound">A</a> <a id="3752" class="Symbol">:</a> <a id="3754" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3757" class="Symbol">}</a> <a id="3759" class="Symbol">{</a><a id="3760" href="Chapter.Logic.Equality.html#3760" class="Bound">x</a> <a id="3762" href="Chapter.Logic.Equality.html#3762" class="Bound">y</a> <a id="3764" href="Chapter.Logic.Equality.html#3764" class="Bound">z</a> <a id="3766" class="Symbol">:</a> <a id="3768" href="Chapter.Logic.Equality.html#3750" class="Bound">A</a><a id="3769" class="Symbol">}</a> <a id="3771" class="Symbol">→</a> <a id="3773" href="Chapter.Logic.Equality.html#3760" class="Bound">x</a> <a id="3775" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="3777" href="Chapter.Logic.Equality.html#3762" class="Bound">y</a> <a id="3779" class="Symbol">→</a> <a id="3781" href="Chapter.Logic.Equality.html#3762" class="Bound">y</a> <a id="3783" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="3785" href="Chapter.Logic.Equality.html#3764" class="Bound">z</a> <a id="3787" class="Symbol">→</a> <a id="3789" href="Chapter.Logic.Equality.html#3760" class="Bound">x</a> <a id="3791" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="3793" href="Chapter.Logic.Equality.html#3764" class="Bound">z</a>
<a id="3795" href="Chapter.Logic.Equality.html#3740" class="Function">trans</a> <a id="3801" href="Chapter.Logic.Equality.html#3801" class="Bound">eq1</a> <a id="3805" href="Chapter.Logic.Equality.html#3805" class="Bound">eq2</a> <a id="3809" class="Symbol">=</a> <a id="3811" class="Hole">{!!}</a>
</pre>
By performing case analysis on `eq1` and `eq2` we effectively unify
the three (implicit) arguments `x`, `y` and `z`, so that we end up
with having to prove `x ≡ x`, which can be done by reflexivity.

<pre class="Agda"><a id="trans₁"></a><a id="4025" href="Chapter.Logic.Equality.html#4025" class="Function">trans₁</a> <a id="4032" class="Symbol">:</a> <a id="4034" class="Symbol">∀{</a><a id="4036" href="Chapter.Logic.Equality.html#4036" class="Bound">A</a> <a id="4038" class="Symbol">:</a> <a id="4040" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4043" class="Symbol">}</a> <a id="4045" class="Symbol">{</a><a id="4046" href="Chapter.Logic.Equality.html#4046" class="Bound">x</a> <a id="4048" href="Chapter.Logic.Equality.html#4048" class="Bound">y</a> <a id="4050" href="Chapter.Logic.Equality.html#4050" class="Bound">z</a> <a id="4052" class="Symbol">:</a> <a id="4054" href="Chapter.Logic.Equality.html#4036" class="Bound">A</a><a id="4055" class="Symbol">}</a> <a id="4057" class="Symbol">→</a> <a id="4059" href="Chapter.Logic.Equality.html#4046" class="Bound">x</a> <a id="4061" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="4063" href="Chapter.Logic.Equality.html#4048" class="Bound">y</a> <a id="4065" class="Symbol">→</a> <a id="4067" href="Chapter.Logic.Equality.html#4048" class="Bound">y</a> <a id="4069" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="4071" href="Chapter.Logic.Equality.html#4050" class="Bound">z</a> <a id="4073" class="Symbol">→</a> <a id="4075" href="Chapter.Logic.Equality.html#4046" class="Bound">x</a> <a id="4077" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="4079" href="Chapter.Logic.Equality.html#4050" class="Bound">z</a>
<a id="4081" href="Chapter.Logic.Equality.html#4025" class="Function">trans₁</a> <a id="4088" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="4093" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="4098" class="Symbol">=</a> <a id="4100" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a>
</pre>
## Congruence and substitution

In the chapter on [natural
numbers](Chapter.Intro.NaturalNumbers.html) we have used the
congruence property of function application, namely the property
that, if `x ≡ y`, then `f x ≡ f y`. We can now see how this theorem
is proved.

<pre class="Agda"><a id="cong"></a><a id="4379" href="Chapter.Logic.Equality.html#4379" class="Function">cong</a> <a id="4384" class="Symbol">:</a> <a id="4386" class="Symbol">∀{</a><a id="4388" href="Chapter.Logic.Equality.html#4388" class="Bound">A</a> <a id="4390" href="Chapter.Logic.Equality.html#4390" class="Bound">B</a> <a id="4392" class="Symbol">:</a> <a id="4394" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4397" class="Symbol">}</a> <a id="4399" class="Symbol">(</a><a id="4400" href="Chapter.Logic.Equality.html#4400" class="Bound">f</a> <a id="4402" class="Symbol">:</a> <a id="4404" href="Chapter.Logic.Equality.html#4388" class="Bound">A</a> <a id="4406" class="Symbol">→</a> <a id="4408" href="Chapter.Logic.Equality.html#4390" class="Bound">B</a><a id="4409" class="Symbol">)</a> <a id="4411" class="Symbol">{</a><a id="4412" href="Chapter.Logic.Equality.html#4412" class="Bound">x</a> <a id="4414" href="Chapter.Logic.Equality.html#4414" class="Bound">y</a> <a id="4416" class="Symbol">:</a> <a id="4418" href="Chapter.Logic.Equality.html#4388" class="Bound">A</a><a id="4419" class="Symbol">}</a> <a id="4421" class="Symbol">→</a> <a id="4423" href="Chapter.Logic.Equality.html#4412" class="Bound">x</a> <a id="4425" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="4427" href="Chapter.Logic.Equality.html#4414" class="Bound">y</a> <a id="4429" class="Symbol">→</a> <a id="4431" href="Chapter.Logic.Equality.html#4400" class="Bound">f</a> <a id="4433" href="Chapter.Logic.Equality.html#4412" class="Bound">x</a> <a id="4435" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="4437" href="Chapter.Logic.Equality.html#4400" class="Bound">f</a> <a id="4439" href="Chapter.Logic.Equality.html#4414" class="Bound">y</a>
<a id="4441" href="Chapter.Logic.Equality.html#4379" class="Function">cong</a> <a id="4446" class="Symbol">_</a> <a id="4448" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="4453" class="Symbol">=</a> <a id="4455" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a>
</pre>
Once again we rely on case analysis to force the unification of `x`
and `y`, thereby turning congruence into another case of
reflexivity. Another principle related to equality is
*substitution*, asserting that if `x ≡ y` and we know that `x`
satisfies some predicate `P`, then `y` also satisfies the same
predicate.

<pre class="Agda"><a id="subst"></a><a id="4786" href="Chapter.Logic.Equality.html#4786" class="Function">subst</a> <a id="4792" class="Symbol">:</a> <a id="4794" class="Symbol">∀{</a><a id="4796" href="Chapter.Logic.Equality.html#4796" class="Bound">A</a> <a id="4798" class="Symbol">:</a> <a id="4800" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4803" class="Symbol">}</a> <a id="4805" class="Symbol">(</a><a id="4806" href="Chapter.Logic.Equality.html#4806" class="Bound">P</a> <a id="4808" class="Symbol">:</a> <a id="4810" href="Chapter.Logic.Equality.html#4796" class="Bound">A</a> <a id="4812" class="Symbol">→</a> <a id="4814" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4817" class="Symbol">)</a> <a id="4819" class="Symbol">{</a><a id="4820" href="Chapter.Logic.Equality.html#4820" class="Bound">x</a> <a id="4822" href="Chapter.Logic.Equality.html#4822" class="Bound">y</a> <a id="4824" class="Symbol">:</a> <a id="4826" href="Chapter.Logic.Equality.html#4796" class="Bound">A</a><a id="4827" class="Symbol">}</a> <a id="4829" class="Symbol">→</a> <a id="4831" href="Chapter.Logic.Equality.html#4820" class="Bound">x</a> <a id="4833" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="4835" href="Chapter.Logic.Equality.html#4822" class="Bound">y</a> <a id="4837" class="Symbol">→</a> <a id="4839" href="Chapter.Logic.Equality.html#4806" class="Bound">P</a> <a id="4841" href="Chapter.Logic.Equality.html#4820" class="Bound">x</a> <a id="4843" class="Symbol">→</a> <a id="4845" href="Chapter.Logic.Equality.html#4806" class="Bound">P</a> <a id="4847" href="Chapter.Logic.Equality.html#4822" class="Bound">y</a>
<a id="4849" href="Chapter.Logic.Equality.html#4786" class="Function">subst</a> <a id="4855" class="Symbol">_</a> <a id="4857" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="4862" href="Chapter.Logic.Equality.html#4862" class="Bound">p</a> <a id="4864" class="Symbol">=</a> <a id="4866" href="Chapter.Logic.Equality.html#4862" class="Bound">p</a>
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

<pre class="Agda"><a id="5575" class="Comment">-- EXERCISE 1</a>

<a id="suc-injective"></a><a id="5590" href="Chapter.Logic.Equality.html#5590" class="Function">suc-injective</a> <a id="5604" class="Symbol">:</a> <a id="5606" class="Symbol">∀{</a><a id="5608" href="Chapter.Logic.Equality.html#5608" class="Bound">x</a> <a id="5610" href="Chapter.Logic.Equality.html#5610" class="Bound">y</a> <a id="5612" class="Symbol">:</a> <a id="5614" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="5615" class="Symbol">}</a> <a id="5617" class="Symbol">→</a> <a id="5619" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5623" href="Chapter.Logic.Equality.html#5608" class="Bound">x</a> <a id="5625" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="5627" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5631" href="Chapter.Logic.Equality.html#5610" class="Bound">y</a> <a id="5633" class="Symbol">→</a> <a id="5635" href="Chapter.Logic.Equality.html#5608" class="Bound">x</a> <a id="5637" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="5639" href="Chapter.Logic.Equality.html#5610" class="Bound">y</a>
<a id="5641" href="Chapter.Logic.Equality.html#5590" class="Function">suc-injective</a> <a id="5655" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="5660" class="Symbol">=</a> <a id="5662" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a>

<a id="5668" class="Comment">-- EXERCISE 2</a>

<a id="_≢_"></a><a id="5683" href="Chapter.Logic.Equality.html#5683" class="Function Operator">_≢_</a> <a id="5687" class="Symbol">:</a> <a id="5689" class="Symbol">∀{</a><a id="5691" href="Chapter.Logic.Equality.html#5691" class="Bound">A</a> <a id="5693" class="Symbol">:</a> <a id="5695" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5698" class="Symbol">}</a> <a id="5700" class="Symbol">→</a> <a id="5702" href="Chapter.Logic.Equality.html#5691" class="Bound">A</a> <a id="5704" class="Symbol">→</a> <a id="5706" href="Chapter.Logic.Equality.html#5691" class="Bound">A</a> <a id="5708" class="Symbol">→</a> <a id="5710" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="5714" href="Chapter.Logic.Equality.html#5714" class="Bound">x</a> <a id="5716" href="Chapter.Logic.Equality.html#5683" class="Function Operator">≢</a> <a id="5718" href="Chapter.Logic.Equality.html#5718" class="Bound">y</a> <a id="5720" class="Symbol">=</a> <a id="5722" href="Relation.Nullary.Negation.Core.html#677" class="Function Operator">¬</a> <a id="5724" class="Symbol">(</a><a id="5725" href="Chapter.Logic.Equality.html#5714" class="Bound">x</a> <a id="5727" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="5729" href="Chapter.Logic.Equality.html#5718" class="Bound">y</a><a id="5730" class="Symbol">)</a>

<a id="zero-suc"></a><a id="5733" href="Chapter.Logic.Equality.html#5733" class="Function">zero-suc</a> <a id="5742" class="Symbol">:</a> <a id="5744" class="Symbol">∀{</a><a id="5746" href="Chapter.Logic.Equality.html#5746" class="Bound">x</a> <a id="5748" class="Symbol">:</a> <a id="5750" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="5751" class="Symbol">}</a> <a id="5753" class="Symbol">→</a> <a id="5755" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="5760" href="Chapter.Logic.Equality.html#5683" class="Function Operator">≢</a> <a id="5762" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5766" href="Chapter.Logic.Equality.html#5746" class="Bound">x</a>
<a id="5768" href="Chapter.Logic.Equality.html#5733" class="Function">zero-suc</a> <a id="5777" class="Symbol">()</a>

<a id="5781" class="Comment">-- EXERCISE 3</a>

<a id="ne-ne"></a><a id="5796" href="Chapter.Logic.Equality.html#5796" class="Function">ne-ne</a> <a id="5802" class="Symbol">:</a> <a id="5804" class="Symbol">∀{</a><a id="5806" href="Chapter.Logic.Equality.html#5806" class="Bound">x</a> <a id="5808" href="Chapter.Logic.Equality.html#5808" class="Bound">y</a> <a id="5810" class="Symbol">:</a> <a id="5812" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="5813" class="Symbol">}</a> <a id="5815" class="Symbol">→</a> <a id="5817" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5821" href="Chapter.Logic.Equality.html#5806" class="Bound">x</a> <a id="5823" href="Chapter.Logic.Equality.html#5683" class="Function Operator">≢</a> <a id="5825" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5829" href="Chapter.Logic.Equality.html#5808" class="Bound">y</a> <a id="5831" class="Symbol">→</a> <a id="5833" href="Chapter.Logic.Equality.html#5806" class="Bound">x</a> <a id="5835" href="Chapter.Logic.Equality.html#5683" class="Function Operator">≢</a> <a id="5837" href="Chapter.Logic.Equality.html#5808" class="Bound">y</a>
<a id="5839" href="Chapter.Logic.Equality.html#5796" class="Function">ne-ne</a> <a id="5845" href="Chapter.Logic.Equality.html#5845" class="Bound">neq</a> <a id="5849" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="5854" class="Symbol">=</a> <a id="5856" href="Chapter.Logic.Equality.html#5845" class="Bound">neq</a> <a id="5860" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a>

<a id="5866" class="Comment">-- EXERCISE 4</a>

<a id="∷-injective"></a><a id="5881" href="Chapter.Logic.Equality.html#5881" class="Function">∷-injective</a> <a id="5893" class="Symbol">:</a> <a id="5895" class="Symbol">∀{</a><a id="5897" href="Chapter.Logic.Equality.html#5897" class="Bound">A</a> <a id="5899" class="Symbol">:</a> <a id="5901" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5904" class="Symbol">}</a> <a id="5906" class="Symbol">{</a><a id="5907" href="Chapter.Logic.Equality.html#5907" class="Bound">x</a> <a id="5909" href="Chapter.Logic.Equality.html#5909" class="Bound">y</a> <a id="5911" class="Symbol">:</a> <a id="5913" href="Chapter.Logic.Equality.html#5897" class="Bound">A</a><a id="5914" class="Symbol">}</a> <a id="5916" class="Symbol">{</a><a id="5917" href="Chapter.Logic.Equality.html#5917" class="Bound">xs</a> <a id="5920" href="Chapter.Logic.Equality.html#5920" class="Bound">ys</a> <a id="5923" class="Symbol">:</a> <a id="5925" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="5930" href="Chapter.Logic.Equality.html#5897" class="Bound">A</a><a id="5931" class="Symbol">}</a> <a id="5933" class="Symbol">→</a> <a id="5935" href="Chapter.Logic.Equality.html#5907" class="Bound">x</a> <a id="5937" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="5939" href="Chapter.Logic.Equality.html#5917" class="Bound">xs</a> <a id="5942" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="5944" href="Chapter.Logic.Equality.html#5909" class="Bound">y</a> <a id="5946" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="5948" href="Chapter.Logic.Equality.html#5920" class="Bound">ys</a> <a id="5951" class="Symbol">→</a> <a id="5953" href="Chapter.Logic.Equality.html#5907" class="Bound">x</a> <a id="5955" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="5957" href="Chapter.Logic.Equality.html#5909" class="Bound">y</a> <a id="5959" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="5961" href="Chapter.Logic.Equality.html#5917" class="Bound">xs</a> <a id="5964" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="5966" href="Chapter.Logic.Equality.html#5920" class="Bound">ys</a>
<a id="5969" href="Chapter.Logic.Equality.html#5881" class="Function">∷-injective</a> <a id="5981" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="5986" class="Symbol">=</a> <a id="5988" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="5993" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="5995" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a>

<a id="6001" class="Comment">-- EXERCISE 5</a>

<a id="cong2"></a><a id="6016" href="Chapter.Logic.Equality.html#6016" class="Function">cong2</a> <a id="6022" class="Symbol">:</a> <a id="6024" class="Symbol">∀{</a><a id="6026" href="Chapter.Logic.Equality.html#6026" class="Bound">A</a> <a id="6028" href="Chapter.Logic.Equality.html#6028" class="Bound">B</a> <a id="6030" href="Chapter.Logic.Equality.html#6030" class="Bound">C</a> <a id="6032" class="Symbol">:</a> <a id="6034" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="6037" class="Symbol">}</a> <a id="6039" class="Symbol">(</a><a id="6040" href="Chapter.Logic.Equality.html#6040" class="Bound">f</a> <a id="6042" class="Symbol">:</a> <a id="6044" href="Chapter.Logic.Equality.html#6026" class="Bound">A</a> <a id="6046" class="Symbol">→</a> <a id="6048" href="Chapter.Logic.Equality.html#6028" class="Bound">B</a> <a id="6050" class="Symbol">→</a> <a id="6052" href="Chapter.Logic.Equality.html#6030" class="Bound">C</a><a id="6053" class="Symbol">)</a> <a id="6055" class="Symbol">{</a><a id="6056" href="Chapter.Logic.Equality.html#6056" class="Bound">x</a> <a id="6058" href="Chapter.Logic.Equality.html#6058" class="Bound">y</a> <a id="6060" class="Symbol">:</a> <a id="6062" href="Chapter.Logic.Equality.html#6026" class="Bound">A</a><a id="6063" class="Symbol">}</a> <a id="6065" class="Symbol">{</a><a id="6066" href="Chapter.Logic.Equality.html#6066" class="Bound">u</a> <a id="6068" href="Chapter.Logic.Equality.html#6068" class="Bound">v</a> <a id="6070" class="Symbol">:</a> <a id="6072" href="Chapter.Logic.Equality.html#6028" class="Bound">B</a><a id="6073" class="Symbol">}</a> <a id="6075" class="Symbol">→</a> <a id="6077" href="Chapter.Logic.Equality.html#6056" class="Bound">x</a> <a id="6079" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="6081" href="Chapter.Logic.Equality.html#6058" class="Bound">y</a> <a id="6083" class="Symbol">→</a> <a id="6085" href="Chapter.Logic.Equality.html#6066" class="Bound">u</a> <a id="6087" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="6089" href="Chapter.Logic.Equality.html#6068" class="Bound">v</a> <a id="6091" class="Symbol">→</a> <a id="6093" href="Chapter.Logic.Equality.html#6040" class="Bound">f</a> <a id="6095" href="Chapter.Logic.Equality.html#6056" class="Bound">x</a> <a id="6097" href="Chapter.Logic.Equality.html#6066" class="Bound">u</a> <a id="6099" href="Chapter.Logic.Equality.html#737" class="Datatype Operator">≡</a> <a id="6101" href="Chapter.Logic.Equality.html#6040" class="Bound">f</a> <a id="6103" href="Chapter.Logic.Equality.html#6058" class="Bound">y</a> <a id="6105" href="Chapter.Logic.Equality.html#6068" class="Bound">v</a>
<a id="6107" href="Chapter.Logic.Equality.html#6016" class="Function">cong2</a> <a id="6113" class="Symbol">_</a> <a id="6115" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="6120" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a> <a id="6125" class="Symbol">=</a> <a id="6127" href="Chapter.Logic.Equality.html#777" class="InductiveConstructor">refl</a>
</pre>{:.solution}
