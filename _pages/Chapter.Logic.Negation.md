---
title: Negation and decidability
prev:  Chapter.Logic.Connectives
next:  Chapter.Logic.Existential
---

<!--
<pre class="Agda"><a id="118" class="Symbol">{-#</a> <a id="122" class="Keyword">OPTIONS</a> <a id="130" class="Pragma">--allow-unsolved-metas</a> <a id="153" class="Symbol">#-}</a>
</pre>-->

<pre class="Agda"><a id="170" class="Keyword">module</a> <a id="177" href="Chapter.Logic.Negation.html" class="Module">Chapter.Logic.Negation</a> <a id="200" class="Keyword">where</a>
</pre>
## Imports

<pre class="Agda"><a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="Data.Empty.html" class="Module">Data.Empty</a>
<a id="250" class="Keyword">open</a> <a id="255" class="Keyword">import</a> <a id="262" href="Data.Unit.html" class="Module">Data.Unit</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="Data.Sum.html" class="Module">Data.Sum</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="Data.Product.html" class="Module">Data.Product</a>
<a id="318" class="Keyword">open</a> <a id="323" class="Keyword">import</a> <a id="330" href="Data.Bool.html" class="Module">Data.Bool</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="Data.Nat.html" class="Module">Data.Nat</a>
<a id="361" class="Keyword">open</a> <a id="366" class="Keyword">import</a> <a id="373" href="Data.List.html" class="Module">Data.List</a>
<a id="383" class="Keyword">open</a> <a id="388" class="Keyword">import</a> <a id="395" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="433" class="Keyword">using</a> <a id="439" class="Symbol">(</a><a id="440" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a><a id="443" class="Symbol">;</a> <a id="445" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a><a id="449" class="Symbol">)</a>
</pre>
## Constructive negation

In constructive logic, the `⊥` data type has a fundamental role
since it allows us to define negation. Showing that the *negation*
of a proposition `A` holds amounts to showing that a proof of `A`
can be turned into a proof of `⊥`.

<pre class="Agda"><a id="¬_"></a><a id="719" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬_</a> <a id="722" class="Symbol">:</a> <a id="724" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="728" class="Symbol">→</a> <a id="730" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="734" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="736" href="Chapter.Logic.Negation.html#736" class="Bound">A</a> <a id="738" class="Symbol">=</a> <a id="740" href="Chapter.Logic.Negation.html#736" class="Bound">A</a> <a id="742" class="Symbol">→</a> <a id="744" href="Data.Empty.html#914" class="Function">⊥</a>
</pre>
Using negation in conjunction with propositional equality we can
define the notion of "being different from", thus:

<pre class="Agda"><a id="_≢_"></a><a id="872" href="Chapter.Logic.Negation.html#872" class="Function Operator">_≢_</a> <a id="876" class="Symbol">:</a> <a id="878" class="Symbol">∀{</a><a id="880" href="Chapter.Logic.Negation.html#880" class="Bound">A</a> <a id="882" class="Symbol">:</a> <a id="884" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="887" class="Symbol">}</a> <a id="889" class="Symbol">→</a> <a id="891" href="Chapter.Logic.Negation.html#880" class="Bound">A</a> <a id="893" class="Symbol">→</a> <a id="895" href="Chapter.Logic.Negation.html#880" class="Bound">A</a> <a id="897" class="Symbol">→</a> <a id="899" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="903" href="Chapter.Logic.Negation.html#903" class="Bound">x</a> <a id="905" href="Chapter.Logic.Negation.html#872" class="Function Operator">≢</a> <a id="907" href="Chapter.Logic.Negation.html#907" class="Bound">y</a> <a id="909" class="Symbol">=</a> <a id="911" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="913" class="Symbol">(</a><a id="914" href="Chapter.Logic.Negation.html#903" class="Bound">x</a> <a id="916" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="918" href="Chapter.Logic.Negation.html#907" class="Bound">y</a><a id="919" class="Symbol">)</a>
</pre>
As an example, let us prove that `true` and `false` are
different. We start with a definition like this:

<pre class="Agda"><a id="true≢false₁"></a><a id="1036" href="Chapter.Logic.Negation.html#1036" class="Function">true≢false₁</a> <a id="1048" class="Symbol">:</a> <a id="1050" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a> <a id="1055" href="Chapter.Logic.Negation.html#872" class="Function Operator">≢</a> <a id="1057" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a>
<a id="1063" href="Chapter.Logic.Negation.html#1036" class="Function">true≢false₁</a> <a id="1075" class="Symbol">=</a> <a id="1077" class="Hole">{!!}</a>
</pre>
In order to make progress, recall that the type `true ≢ false` is
definitionally equal to the type `¬ (true ≡ false)` which, in turn,
is definitionally equal to the type `true ≡ false → ⊥`. That is,
`true≢false` is nothing but a *function* that accepts a proof of
`true ≡ false` and yields something of type `⊥`. We can obtain
evidence of this fact by giving a name --- say `p` --- to the
argument of the function:

<pre class="Agda"><a id="true≢false₂"></a><a id="1507" href="Chapter.Logic.Negation.html#1507" class="Function">true≢false₂</a> <a id="1519" class="Symbol">:</a> <a id="1521" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a> <a id="1526" href="Chapter.Logic.Negation.html#872" class="Function Operator">≢</a> <a id="1528" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a>
<a id="1534" href="Chapter.Logic.Negation.html#1507" class="Function">true≢false₂</a> <a id="1546" href="Chapter.Logic.Negation.html#1546" class="Bound">p</a> <a id="1548" class="Symbol">=</a> <a id="1550" class="Hole">{!!}</a>
</pre>
At this stage Agda expects us to fill the hole with a term of type
`⊥`. This is clearly impossible, but in the context we also have a
proof `p` that `true ≡ false`. If we inspect `p` using case
analysis, Agda figures out that there cannot be such proof and
replaces `p` with the absurd pattern. This way, we are freed from
the obligation to fill the goal.

<pre class="Agda"><a id="true≢false₃"></a><a id="1921" href="Chapter.Logic.Negation.html#1921" class="Function">true≢false₃</a> <a id="1933" class="Symbol">:</a> <a id="1935" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a> <a id="1940" href="Chapter.Logic.Negation.html#872" class="Function Operator">≢</a> <a id="1942" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a>
<a id="1948" href="Chapter.Logic.Negation.html#1921" class="Function">true≢false₃</a> <a id="1960" class="Symbol">()</a>
</pre>
Occasionally it is useful to define a function that accepts an
absurd pattern "on the spot". In these cases we can use the syntax
`λ ()` to define such function. For example, we can prove that
`true` is different from `false` also in the following way:

<pre class="Agda"><a id="true≢false₄"></a><a id="2226" href="Chapter.Logic.Negation.html#2226" class="Function">true≢false₄</a> <a id="2238" class="Symbol">:</a> <a id="2240" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a> <a id="2245" href="Chapter.Logic.Negation.html#872" class="Function Operator">≢</a> <a id="2247" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a>
<a id="2253" href="Chapter.Logic.Negation.html#2226" class="Function">true≢false₄</a> <a id="2265" class="Symbol">=</a> <a id="2267" class="Symbol">λ</a> <a id="2269" class="Symbol">()</a>
</pre>
We will see below examples where this notation is useful.

## Properties of negation

We will make a rather extensive use of negation in the following
chapters. For the time being, we prove a few laws related to
negation. The first one is **contradiction**, namely the fact that
if we have both a proof of `A` and a proof of `¬ A` then we can
derive a proof of `⊥`. Recalling that the negation of `A` is defined
as a function that turns a proof of `A` into a proof of `⊥`, we see
that contradiction simply amounts to function application.

<pre class="Agda"><a id="contradiction"></a><a id="2821" href="Chapter.Logic.Negation.html#2821" class="Function">contradiction</a> <a id="2835" class="Symbol">:</a> <a id="2837" class="Symbol">∀{</a><a id="2839" href="Chapter.Logic.Negation.html#2839" class="Bound">A</a> <a id="2841" class="Symbol">:</a> <a id="2843" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2846" class="Symbol">}</a> <a id="2848" class="Symbol">→</a> <a id="2850" href="Chapter.Logic.Negation.html#2839" class="Bound">A</a> <a id="2852" class="Symbol">→</a> <a id="2854" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="2856" href="Chapter.Logic.Negation.html#2839" class="Bound">A</a> <a id="2858" class="Symbol">→</a> <a id="2860" href="Data.Empty.html#914" class="Function">⊥</a>
<a id="2862" href="Chapter.Logic.Negation.html#2821" class="Function">contradiction</a> <a id="2876" href="Chapter.Logic.Negation.html#2876" class="Bound">p</a> <a id="2878" href="Chapter.Logic.Negation.html#2878" class="Bound">n</a> <a id="2880" class="Symbol">=</a> <a id="2882" href="Chapter.Logic.Negation.html#2878" class="Bound">n</a> <a id="2884" href="Chapter.Logic.Negation.html#2876" class="Bound">p</a>
</pre>
Recalling that in Agda the type `¬ A` is *defined* to be the same as
the type `A → ⊥`, the type of `contradiction` can also be written
as `∀{A : Set} → A → ¬ ¬ A`. This is one of the so-called "double
negation" laws.

<pre class="Agda"><a id="double-negation"></a><a id="3113" href="Chapter.Logic.Negation.html#3113" class="Function">double-negation</a> <a id="3129" class="Symbol">:</a> <a id="3131" class="Symbol">∀{</a><a id="3133" href="Chapter.Logic.Negation.html#3133" class="Bound">A</a> <a id="3135" class="Symbol">:</a> <a id="3137" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3140" class="Symbol">}</a> <a id="3142" class="Symbol">→</a> <a id="3144" href="Chapter.Logic.Negation.html#3133" class="Bound">A</a> <a id="3146" class="Symbol">→</a> <a id="3148" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="3150" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="3152" href="Chapter.Logic.Negation.html#3133" class="Bound">A</a>
<a id="3154" href="Chapter.Logic.Negation.html#3113" class="Function">double-negation</a> <a id="3170" class="Symbol">=</a> <a id="3172" href="Chapter.Logic.Negation.html#2821" class="Function">contradiction</a>
</pre>
In classical logic, the inverse implication `¬ ¬ A → A` is also
assumed to be true. However, this implication is not provable in
constructive logic (it is instructive to **attempt** proving this
property).

Another interesting law concerning negation is **contraposition**,
asserting that if `A` implies `B`, then `¬ B` implies `¬ A`.

<pre class="Agda"><a id="contraposition"></a><a id="3531" href="Chapter.Logic.Negation.html#3531" class="Function">contraposition</a> <a id="3546" class="Symbol">:</a> <a id="3548" class="Symbol">∀{</a><a id="3550" href="Chapter.Logic.Negation.html#3550" class="Bound">A</a> <a id="3552" href="Chapter.Logic.Negation.html#3552" class="Bound">B</a> <a id="3554" class="Symbol">:</a> <a id="3556" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3559" class="Symbol">}</a> <a id="3561" class="Symbol">→</a> <a id="3563" class="Symbol">(</a><a id="3564" href="Chapter.Logic.Negation.html#3550" class="Bound">A</a> <a id="3566" class="Symbol">→</a> <a id="3568" href="Chapter.Logic.Negation.html#3552" class="Bound">B</a><a id="3569" class="Symbol">)</a> <a id="3571" class="Symbol">→</a> <a id="3573" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="3575" href="Chapter.Logic.Negation.html#3552" class="Bound">B</a> <a id="3577" class="Symbol">→</a> <a id="3579" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="3581" href="Chapter.Logic.Negation.html#3550" class="Bound">A</a>
<a id="3583" href="Chapter.Logic.Negation.html#3531" class="Function">contraposition</a> <a id="3598" href="Chapter.Logic.Negation.html#3598" class="Bound">f</a> <a id="3600" href="Chapter.Logic.Negation.html#3600" class="Bound">p</a> <a id="3602" href="Chapter.Logic.Negation.html#3602" class="Bound">q</a> <a id="3604" class="Symbol">=</a> <a id="3606" href="Chapter.Logic.Negation.html#3600" class="Bound">p</a> <a id="3608" class="Symbol">(</a><a id="3609" href="Chapter.Logic.Negation.html#3598" class="Bound">f</a> <a id="3611" href="Chapter.Logic.Negation.html#3602" class="Bound">q</a><a id="3612" class="Symbol">)</a>
</pre>
Observe that we define `contraposition` as a function with three
arguments `f`, `p` and `q`, while its type appears to have only two
arguments, one of type `A → B` (that would be `f`) and the other of
type `¬ B` (that would be `p`). However, the type `¬ A` is actually
the type `A → ⊥`, so `contraposition` can be seen as also having a
third argument of type `A`, that would be `q`.

Using `contraposition` and `double-negation` we can prove that
*triple* negation implies *single* negation.

<pre class="Agda"><a id="triple-negation"></a><a id="4116" href="Chapter.Logic.Negation.html#4116" class="Function">triple-negation</a> <a id="4132" class="Symbol">:</a> <a id="4134" class="Symbol">∀{</a><a id="4136" href="Chapter.Logic.Negation.html#4136" class="Bound">A</a> <a id="4138" class="Symbol">:</a> <a id="4140" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4143" class="Symbol">}</a> <a id="4145" class="Symbol">→</a> <a id="4147" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="4149" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="4151" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="4153" href="Chapter.Logic.Negation.html#4136" class="Bound">A</a> <a id="4155" class="Symbol">→</a> <a id="4157" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="4159" href="Chapter.Logic.Negation.html#4136" class="Bound">A</a>
<a id="4161" href="Chapter.Logic.Negation.html#4116" class="Function">triple-negation</a> <a id="4177" class="Symbol">=</a> <a id="4179" href="Chapter.Logic.Negation.html#3531" class="Function">contraposition</a> <a id="4194" href="Chapter.Logic.Negation.html#3113" class="Function">double-negation</a>
</pre>
## Decidability

In classical logic it is common to assume the validity of the
*excluded middle* principle, namely that `¬ A ⊎ A` is true for every
proposition `A`. As we know from the [previous
chapter](Chapter.Logic.Connectives.html), in constructive logic, a
proof of a disjunction `¬ A ⊎ A` embeds either a proof of `¬ A` or a
proof of `A`, hence it may very well be the case that we are unable
to prove `¬ A ⊎ A` if we cannot find either a proof of `¬ A` or a
proof of `A`. The propositions for which we are able to prove `¬ A ⊎
A` are said to be **decidable**.

<pre class="Agda"><a id="Decidable"></a><a id="4787" href="Chapter.Logic.Negation.html#4787" class="Function">Decidable</a> <a id="4797" class="Symbol">:</a> <a id="4799" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="4803" class="Symbol">→</a> <a id="4805" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="4809" href="Chapter.Logic.Negation.html#4787" class="Function">Decidable</a> <a id="4819" href="Chapter.Logic.Negation.html#4819" class="Bound">A</a> <a id="4821" class="Symbol">=</a> <a id="4823" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="4825" href="Chapter.Logic.Negation.html#4819" class="Bound">A</a> <a id="4827" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="4829" href="Chapter.Logic.Negation.html#4819" class="Bound">A</a>
</pre>
As an example of decidable property, consider the problem of
determining whether two boolean values are equal or not.  This can
be shown by considering all the possible cases, which are finite.

<pre class="Agda"><a id="Bool-eq-decidable"></a><a id="5035" href="Chapter.Logic.Negation.html#5035" class="Function">Bool-eq-decidable</a> <a id="5053" class="Symbol">:</a> <a id="5055" class="Symbol">∀(</a><a id="5057" href="Chapter.Logic.Negation.html#5057" class="Bound">x</a> <a id="5059" href="Chapter.Logic.Negation.html#5059" class="Bound">y</a> <a id="5061" class="Symbol">:</a> <a id="5063" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="5067" class="Symbol">)</a> <a id="5069" class="Symbol">→</a> <a id="5071" href="Chapter.Logic.Negation.html#4787" class="Function">Decidable</a> <a id="5081" class="Symbol">(</a><a id="5082" href="Chapter.Logic.Negation.html#5057" class="Bound">x</a> <a id="5084" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="5086" href="Chapter.Logic.Negation.html#5059" class="Bound">y</a><a id="5087" class="Symbol">)</a>
<a id="5089" href="Chapter.Logic.Negation.html#5035" class="Function">Bool-eq-decidable</a> <a id="5107" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="5113" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="5119" class="Symbol">=</a> <a id="5121" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="5126" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="5131" href="Chapter.Logic.Negation.html#5035" class="Function">Bool-eq-decidable</a> <a id="5149" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="5155" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="5161" class="Symbol">=</a> <a id="5163" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="5168" class="Symbol">λ</a> <a id="5170" class="Symbol">()</a>
<a id="5173" href="Chapter.Logic.Negation.html#5035" class="Function">Bool-eq-decidable</a> <a id="5191" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="5197" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="5203" class="Symbol">=</a> <a id="5205" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="5210" class="Symbol">λ</a> <a id="5212" class="Symbol">()</a>
<a id="5215" href="Chapter.Logic.Negation.html#5035" class="Function">Bool-eq-decidable</a> <a id="5233" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="5239" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="5245" class="Symbol">=</a> <a id="5247" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="5252" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
Note that we use the constructor `inj₂` for representing a positive
answer to the question "is `x` equal to `y`?" and `inj₁` for
representing a negative answer. For readability purposes, it may be
appropriate to give these constructors more evocative names, such as
`yes` and `no`. We can do so (without defining an *ad hoc*
`Decidable` data type) by means of **pattern synonyms**.

<pre class="Agda"><a id="5649" class="Keyword">pattern</a> <a id="yes"></a><a id="5657" href="Chapter.Logic.Negation.html#5657" class="InductiveConstructor">yes</a> <a id="5661" href="Chapter.Logic.Negation.html#5670" class="Bound">x</a> <a id="5663" class="Symbol">=</a> <a id="5665" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="5670" href="Chapter.Logic.Negation.html#5670" class="Bound">x</a>
<a id="5672" class="Keyword">pattern</a> <a id="no"></a><a id="5680" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a>  <a id="5684" href="Chapter.Logic.Negation.html#5693" class="Bound">x</a> <a id="5686" class="Symbol">=</a> <a id="5688" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="5693" href="Chapter.Logic.Negation.html#5693" class="Bound">x</a>
</pre>
With these declarations, we may write `Bool-eq-decidable` as follows.

<pre class="Agda"><a id="Bool-eq-decidable₁"></a><a id="5775" href="Chapter.Logic.Negation.html#5775" class="Function">Bool-eq-decidable₁</a> <a id="5794" class="Symbol">:</a> <a id="5796" class="Symbol">∀(</a><a id="5798" href="Chapter.Logic.Negation.html#5798" class="Bound">x</a> <a id="5800" href="Chapter.Logic.Negation.html#5800" class="Bound">y</a> <a id="5802" class="Symbol">:</a> <a id="5804" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="5808" class="Symbol">)</a> <a id="5810" class="Symbol">→</a> <a id="5812" href="Chapter.Logic.Negation.html#4787" class="Function">Decidable</a> <a id="5822" class="Symbol">(</a><a id="5823" href="Chapter.Logic.Negation.html#5798" class="Bound">x</a> <a id="5825" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="5827" href="Chapter.Logic.Negation.html#5800" class="Bound">y</a><a id="5828" class="Symbol">)</a>
<a id="5830" href="Chapter.Logic.Negation.html#5775" class="Function">Bool-eq-decidable₁</a> <a id="5849" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="5855" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="5861" class="Symbol">=</a> <a id="5863" href="Chapter.Logic.Negation.html#5657" class="InductiveConstructor">yes</a> <a id="5867" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="5872" href="Chapter.Logic.Negation.html#5775" class="Function">Bool-eq-decidable₁</a> <a id="5891" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="5897" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="5903" class="Symbol">=</a> <a id="5905" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a> <a id="5908" class="Symbol">λ</a> <a id="5910" class="Symbol">()</a>
<a id="5913" href="Chapter.Logic.Negation.html#5775" class="Function">Bool-eq-decidable₁</a> <a id="5932" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="5938" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="5944" class="Symbol">=</a> <a id="5946" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a> <a id="5949" class="Symbol">λ</a> <a id="5951" class="Symbol">()</a>
<a id="5954" href="Chapter.Logic.Negation.html#5775" class="Function">Bool-eq-decidable₁</a> <a id="5973" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="5979" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="5985" class="Symbol">=</a> <a id="5987" href="Chapter.Logic.Negation.html#5657" class="InductiveConstructor">yes</a> <a id="5991" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
Another example of decidabile property is the equality for natural
numbers. In this case, when we compare two numbers of the form `suc
x` and `suc y`, we first decide whether `x` and `y` are equal. If
they are not, then we conclude that `suc x` and `suc y` must be
different (recall that constructors such as `suc` are injective). If
`x` and `y` are equal, then they can be unified and we can prove
`suc x ≡ suc y` by reflexivity.

<pre class="Agda"><a id="Nat-eq-decidable"></a><a id="6437" href="Chapter.Logic.Negation.html#6437" class="Function">Nat-eq-decidable</a> <a id="6454" class="Symbol">:</a> <a id="6456" class="Symbol">∀(</a><a id="6458" href="Chapter.Logic.Negation.html#6458" class="Bound">x</a> <a id="6460" href="Chapter.Logic.Negation.html#6460" class="Bound">y</a> <a id="6462" class="Symbol">:</a> <a id="6464" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="6465" class="Symbol">)</a> <a id="6467" class="Symbol">→</a> <a id="6469" href="Chapter.Logic.Negation.html#4787" class="Function">Decidable</a> <a id="6479" class="Symbol">(</a><a id="6480" href="Chapter.Logic.Negation.html#6458" class="Bound">x</a> <a id="6482" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6484" href="Chapter.Logic.Negation.html#6460" class="Bound">y</a><a id="6485" class="Symbol">)</a>
<a id="6487" href="Chapter.Logic.Negation.html#6437" class="Function">Nat-eq-decidable</a> <a id="6504" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="6512" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="6520" class="Symbol">=</a> <a id="6522" href="Chapter.Logic.Negation.html#5657" class="InductiveConstructor">yes</a> <a id="6526" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="6531" href="Chapter.Logic.Negation.html#6437" class="Function">Nat-eq-decidable</a> <a id="6548" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="6556" class="Symbol">(</a><a id="6557" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="6561" href="Chapter.Logic.Negation.html#6561" class="Bound">y</a><a id="6562" class="Symbol">)</a> <a id="6564" class="Symbol">=</a> <a id="6566" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a> <a id="6569" class="Symbol">λ</a> <a id="6571" class="Symbol">()</a>
<a id="6574" href="Chapter.Logic.Negation.html#6437" class="Function">Nat-eq-decidable</a> <a id="6591" class="Symbol">(</a><a id="6592" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="6596" href="Chapter.Logic.Negation.html#6596" class="Bound">x</a><a id="6597" class="Symbol">)</a> <a id="6599" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="6607" class="Symbol">=</a> <a id="6609" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a> <a id="6612" class="Symbol">λ</a> <a id="6614" class="Symbol">()</a>
<a id="6617" href="Chapter.Logic.Negation.html#6437" class="Function">Nat-eq-decidable</a> <a id="6634" class="Symbol">(</a><a id="6635" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="6639" href="Chapter.Logic.Negation.html#6639" class="Bound">x</a><a id="6640" class="Symbol">)</a> <a id="6642" class="Symbol">(</a><a id="6643" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="6647" href="Chapter.Logic.Negation.html#6647" class="Bound">y</a><a id="6648" class="Symbol">)</a> <a id="6650" class="Keyword">with</a> <a id="6655" href="Chapter.Logic.Negation.html#6437" class="Function">Nat-eq-decidable</a> <a id="6672" href="Chapter.Logic.Negation.html#6639" class="Bound">x</a> <a id="6674" href="Chapter.Logic.Negation.html#6647" class="Bound">y</a>
<a id="6676" class="Symbol">...</a> <a id="6680" class="Symbol">|</a> <a id="6682" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a>  <a id="6686" href="Chapter.Logic.Negation.html#6686" class="Bound">neq</a>  <a id="6691" class="Symbol">=</a> <a id="6693" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a> <a id="6696" class="Symbol">λ</a> <a id="6698" class="Symbol">{</a> <a id="6700" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="6705" class="Symbol">→</a> <a id="6707" href="Chapter.Logic.Negation.html#6686" class="Bound">neq</a> <a id="6711" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="6716" class="Symbol">}</a>
<a id="6718" class="Symbol">...</a> <a id="6722" class="Symbol">|</a> <a id="6724" href="Chapter.Logic.Negation.html#5657" class="InductiveConstructor">yes</a> <a id="6728" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="6733" class="Symbol">=</a> <a id="6735" href="Chapter.Logic.Negation.html#5657" class="InductiveConstructor">yes</a> <a id="6739" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
As a final example we show that the equality of lists is decidable,
provided that the equality between their elements is also decidable.

<pre class="Agda"><a id="List-eq-decidable"></a><a id="6891" href="Chapter.Logic.Negation.html#6891" class="Function">List-eq-decidable</a> <a id="6909" class="Symbol">:</a> <a id="6911" class="Symbol">∀{</a><a id="6913" href="Chapter.Logic.Negation.html#6913" class="Bound">A</a> <a id="6915" class="Symbol">:</a> <a id="6917" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="6920" class="Symbol">}</a> <a id="6922" class="Symbol">→</a> <a id="6924" class="Symbol">(∀(</a><a id="6927" href="Chapter.Logic.Negation.html#6927" class="Bound">x</a> <a id="6929" href="Chapter.Logic.Negation.html#6929" class="Bound">y</a> <a id="6931" class="Symbol">:</a> <a id="6933" href="Chapter.Logic.Negation.html#6913" class="Bound">A</a><a id="6934" class="Symbol">)</a> <a id="6936" class="Symbol">→</a> <a id="6938" href="Chapter.Logic.Negation.html#4787" class="Function">Decidable</a> <a id="6948" class="Symbol">(</a><a id="6949" href="Chapter.Logic.Negation.html#6927" class="Bound">x</a> <a id="6951" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6953" href="Chapter.Logic.Negation.html#6929" class="Bound">y</a><a id="6954" class="Symbol">))</a> <a id="6957" class="Symbol">→</a> <a id="6959" class="Symbol">(</a><a id="6960" href="Chapter.Logic.Negation.html#6960" class="Bound">xs</a> <a id="6963" href="Chapter.Logic.Negation.html#6963" class="Bound">ys</a> <a id="6966" class="Symbol">:</a> <a id="6968" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="6973" href="Chapter.Logic.Negation.html#6913" class="Bound">A</a><a id="6974" class="Symbol">)</a> <a id="6976" class="Symbol">→</a> <a id="6978" href="Chapter.Logic.Negation.html#4787" class="Function">Decidable</a> <a id="6988" class="Symbol">(</a><a id="6989" href="Chapter.Logic.Negation.html#6960" class="Bound">xs</a> <a id="6992" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6994" href="Chapter.Logic.Negation.html#6963" class="Bound">ys</a><a id="6996" class="Symbol">)</a>
<a id="6998" href="Chapter.Logic.Negation.html#6891" class="Function">List-eq-decidable</a> <a id="7016" href="Chapter.Logic.Negation.html#7016" class="Bound Operator">_≡?_</a> <a id="7021" href="Agda.Builtin.List.html#184" class="InductiveConstructor">[]</a>        <a id="7031" href="Agda.Builtin.List.html#184" class="InductiveConstructor">[]</a>       <a id="7040" class="Symbol">=</a> <a id="7042" href="Chapter.Logic.Negation.html#5657" class="InductiveConstructor">yes</a> <a id="7046" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="7051" href="Chapter.Logic.Negation.html#6891" class="Function">List-eq-decidable</a> <a id="7069" href="Chapter.Logic.Negation.html#7069" class="Bound Operator">_≡?_</a> <a id="7074" href="Agda.Builtin.List.html#184" class="InductiveConstructor">[]</a>        <a id="7084" class="Symbol">(</a><a id="7085" href="Chapter.Logic.Negation.html#7085" class="Bound">x</a> <a id="7087" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="7089" href="Chapter.Logic.Negation.html#7089" class="Bound">ys</a><a id="7091" class="Symbol">)</a> <a id="7093" class="Symbol">=</a> <a id="7095" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a> <a id="7098" class="Symbol">λ</a> <a id="7100" class="Symbol">()</a>
<a id="7103" href="Chapter.Logic.Negation.html#6891" class="Function">List-eq-decidable</a> <a id="7121" href="Chapter.Logic.Negation.html#7121" class="Bound Operator">_≡?_</a> <a id="7126" class="Symbol">(</a><a id="7127" href="Chapter.Logic.Negation.html#7127" class="Bound">x</a> <a id="7129" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="7131" href="Chapter.Logic.Negation.html#7131" class="Bound">xs</a><a id="7133" class="Symbol">)</a> <a id="7135" href="Agda.Builtin.List.html#184" class="InductiveConstructor">[]</a>        <a id="7145" class="Symbol">=</a> <a id="7147" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a> <a id="7150" class="Symbol">λ</a> <a id="7152" class="Symbol">()</a>
<a id="7155" href="Chapter.Logic.Negation.html#6891" class="Function">List-eq-decidable</a> <a id="7173" href="Chapter.Logic.Negation.html#7173" class="Bound Operator">_≡?_</a> <a id="7178" class="Symbol">(</a><a id="7179" href="Chapter.Logic.Negation.html#7179" class="Bound">x</a> <a id="7181" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="7183" href="Chapter.Logic.Negation.html#7183" class="Bound">xs</a><a id="7185" class="Symbol">)</a> <a id="7187" class="Symbol">(</a><a id="7188" href="Chapter.Logic.Negation.html#7188" class="Bound">y</a> <a id="7190" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="7192" href="Chapter.Logic.Negation.html#7192" class="Bound">ys</a><a id="7194" class="Symbol">)</a> <a id="7196" class="Keyword">with</a> <a id="7201" href="Chapter.Logic.Negation.html#7179" class="Bound">x</a> <a id="7203" href="Chapter.Logic.Negation.html#7173" class="Bound Operator">≡?</a> <a id="7206" href="Chapter.Logic.Negation.html#7188" class="Bound">y</a> <a id="7208" class="Symbol">|</a> <a id="7210" href="Chapter.Logic.Negation.html#6891" class="Function">List-eq-decidable</a> <a id="7228" href="Chapter.Logic.Negation.html#7173" class="Bound Operator">_≡?_</a> <a id="7233" href="Chapter.Logic.Negation.html#7183" class="Bound">xs</a> <a id="7236" href="Chapter.Logic.Negation.html#7192" class="Bound">ys</a>
<a id="7239" class="Symbol">...</a> <a id="7243" class="Symbol">|</a> <a id="7245" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a>  <a id="7249" href="Chapter.Logic.Negation.html#7249" class="Bound">neq</a>  <a id="7254" class="Symbol">|</a> <a id="7256" class="Symbol">_</a>        <a id="7265" class="Symbol">=</a> <a id="7267" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a> <a id="7270" class="Symbol">λ</a> <a id="7272" class="Symbol">{</a> <a id="7274" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="7279" class="Symbol">→</a> <a id="7281" href="Chapter.Logic.Negation.html#7249" class="Bound">neq</a> <a id="7285" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="7290" class="Symbol">}</a>
<a id="7292" class="Symbol">...</a> <a id="7296" class="Symbol">|</a> <a id="7298" href="Chapter.Logic.Negation.html#5657" class="InductiveConstructor">yes</a> <a id="7302" class="Symbol">_</a>    <a id="7307" class="Symbol">|</a> <a id="7309" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a>  <a id="7313" href="Chapter.Logic.Negation.html#7313" class="Bound">neq</a>  <a id="7318" class="Symbol">=</a> <a id="7320" href="Chapter.Logic.Negation.html#5680" class="InductiveConstructor">no</a> <a id="7323" class="Symbol">λ</a> <a id="7325" class="Symbol">{</a> <a id="7327" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="7332" class="Symbol">→</a> <a id="7334" href="Chapter.Logic.Negation.html#7313" class="Bound">neq</a> <a id="7338" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="7343" class="Symbol">}</a>
<a id="7345" class="Symbol">...</a> <a id="7349" class="Symbol">|</a> <a id="7351" href="Chapter.Logic.Negation.html#5657" class="InductiveConstructor">yes</a> <a id="7355" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="7360" class="Symbol">|</a> <a id="7362" href="Chapter.Logic.Negation.html#5657" class="InductiveConstructor">yes</a> <a id="7366" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a> <a id="7371" class="Symbol">=</a> <a id="7373" href="Chapter.Logic.Negation.html#5657" class="InductiveConstructor">yes</a> <a id="7377" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
The case in which we compare two lists of the form `x ∷ xs` and `y
∷ ys` illustrates the use of multiple `with` clauses. In this case,
we have to compare both the heads and the tails of the two
lists. Only if both components are equal can we conclude that the
original lists are equal. Note that each case after the `with`
clauses has as many patterns as the number of `with` clauses.

## Exercises

1. Prove the theorem `ntop : ¬ ⊤ → ⊥`.
2. Which of the following De Morgan's laws can be proved?
   ```text
   ¬ A ⊎ ¬ B → ¬ (A × B)
   ¬ A × ¬ B → ¬ (A ⊎ B)
   ¬ (A ⊎ B) → ¬ A × ¬ B
   ¬ (A × B) → ¬ A ⊎ ¬ B
   ```
3. Show that the excluded middle implies double negation
   elimination, namely prove the theorem `em-dn : (∀{A : Set} → ¬ A
   ⊎ A) → ∀{A : Set} → ¬ ¬ A → A`
4. Prove the theorem `nndec : ∀{A : Set} → ¬ ¬ Decidable A`. Hint:
   one of the De Morgan's laws helps.
5. In classical logic the double negation elimination `¬ ¬ A → A`
   is usually assumed to be true. This is not the case in
   constructive logic. Show that double negation elimination implies
   the excluded middle, namely prove the theorem `dn-em : (∀{A : Set}
   → (¬ ¬ A → A)) → ∀{A : Set} → Decidable A `. Hint: use the
   solution to the previous exercise.
<pre class="Agda"><a id="8633" class="Comment">-- EXERCISE 1</a>

<a id="ntop"></a><a id="8648" href="Chapter.Logic.Negation.html#8648" class="Function">ntop</a> <a id="8653" class="Symbol">:</a> <a id="8655" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="8657" href="Agda.Builtin.Unit.html#175" class="Record">⊤</a> <a id="8659" class="Symbol">→</a> <a id="8661" href="Data.Empty.html#914" class="Function">⊥</a>
<a id="8663" href="Chapter.Logic.Negation.html#8648" class="Function">ntop</a> <a id="8668" href="Chapter.Logic.Negation.html#8668" class="Bound">p</a> <a id="8670" class="Symbol">=</a> <a id="8672" href="Chapter.Logic.Negation.html#8668" class="Bound">p</a> <a id="8674" href="Agda.Builtin.Unit.html#212" class="InductiveConstructor">tt</a>

<a id="8678" class="Comment">-- EXERCISE 2: all laws but the last one can be proved.</a>

<a id="de-morgan-1"></a><a id="8735" href="Chapter.Logic.Negation.html#8735" class="Function">de-morgan-1</a> <a id="8747" class="Symbol">:</a> <a id="8749" class="Symbol">∀{</a><a id="8751" href="Chapter.Logic.Negation.html#8751" class="Bound">A</a> <a id="8753" href="Chapter.Logic.Negation.html#8753" class="Bound">B</a> <a id="8755" class="Symbol">:</a> <a id="8757" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8760" class="Symbol">}</a> <a id="8762" class="Symbol">→</a> <a id="8764" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="8766" href="Chapter.Logic.Negation.html#8751" class="Bound">A</a> <a id="8768" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="8770" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="8772" href="Chapter.Logic.Negation.html#8753" class="Bound">B</a> <a id="8774" class="Symbol">→</a> <a id="8776" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="8778" class="Symbol">(</a><a id="8779" href="Chapter.Logic.Negation.html#8751" class="Bound">A</a> <a id="8781" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="8783" href="Chapter.Logic.Negation.html#8753" class="Bound">B</a><a id="8784" class="Symbol">)</a>
<a id="8786" href="Chapter.Logic.Negation.html#8735" class="Function">de-morgan-1</a> <a id="8798" class="Symbol">=</a> <a id="8800" class="Hole">{!!}</a> <a id="8805" class="Comment">-- ⊎-elim (contraposition fst) (contraposition snd)</a>

<a id="de-morgan-2"></a><a id="8858" href="Chapter.Logic.Negation.html#8858" class="Function">de-morgan-2</a> <a id="8870" class="Symbol">:</a> <a id="8872" class="Symbol">∀{</a><a id="8874" href="Chapter.Logic.Negation.html#8874" class="Bound">A</a> <a id="8876" href="Chapter.Logic.Negation.html#8876" class="Bound">B</a> <a id="8878" class="Symbol">:</a> <a id="8880" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8883" class="Symbol">}</a> <a id="8885" class="Symbol">→</a> <a id="8887" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="8889" href="Chapter.Logic.Negation.html#8874" class="Bound">A</a> <a id="8891" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="8893" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="8895" href="Chapter.Logic.Negation.html#8876" class="Bound">B</a> <a id="8897" class="Symbol">→</a> <a id="8899" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="8901" class="Symbol">(</a><a id="8902" href="Chapter.Logic.Negation.html#8874" class="Bound">A</a> <a id="8904" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="8906" href="Chapter.Logic.Negation.html#8876" class="Bound">B</a><a id="8907" class="Symbol">)</a>
<a id="8909" href="Chapter.Logic.Negation.html#8858" class="Function">de-morgan-2</a> <a id="8921" href="Chapter.Logic.Negation.html#8921" class="Bound">p</a> <a id="8923" class="Symbol">=</a> <a id="8925" class="Hole">{!!}</a> <a id="8930" class="Comment">-- ⊎-elim (fst p) (snd p)</a>

<a id="de-morgan-3"></a><a id="8957" href="Chapter.Logic.Negation.html#8957" class="Function">de-morgan-3</a> <a id="8969" class="Symbol">:</a> <a id="8971" class="Symbol">∀{</a><a id="8973" href="Chapter.Logic.Negation.html#8973" class="Bound">A</a> <a id="8975" href="Chapter.Logic.Negation.html#8975" class="Bound">B</a> <a id="8977" class="Symbol">:</a> <a id="8979" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8982" class="Symbol">}</a> <a id="8984" class="Symbol">→</a> <a id="8986" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="8988" class="Symbol">(</a><a id="8989" href="Chapter.Logic.Negation.html#8973" class="Bound">A</a> <a id="8991" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="8993" href="Chapter.Logic.Negation.html#8975" class="Bound">B</a><a id="8994" class="Symbol">)</a> <a id="8996" class="Symbol">→</a> <a id="8998" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="9000" href="Chapter.Logic.Negation.html#8973" class="Bound">A</a> <a id="9002" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="9004" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="9006" href="Chapter.Logic.Negation.html#8975" class="Bound">B</a>
<a id="9008" href="Chapter.Logic.Negation.html#8957" class="Function">de-morgan-3</a> <a id="9020" href="Chapter.Logic.Negation.html#9020" class="Bound">nab</a> <a id="9024" class="Symbol">=</a> <a id="9026" class="Hole">{!!}</a> <a id="9031" class="Comment">-- contraposition inj₁ nab , contraposition inj₂ nab</a>

<a id="9085" class="Comment">-- EXERCISE 3</a>

<a id="em-dn"></a><a id="9100" href="Chapter.Logic.Negation.html#9100" class="Function">em-dn</a> <a id="9106" class="Symbol">:</a> <a id="9108" class="Symbol">(∀{</a><a id="9111" href="Chapter.Logic.Negation.html#9111" class="Bound">A</a> <a id="9113" class="Symbol">:</a> <a id="9115" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="9118" class="Symbol">}</a> <a id="9120" class="Symbol">→</a> <a id="9122" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="9124" href="Chapter.Logic.Negation.html#9111" class="Bound">A</a> <a id="9126" href="Data.Sum.Base.html#625" class="Datatype Operator">⊎</a> <a id="9128" href="Chapter.Logic.Negation.html#9111" class="Bound">A</a><a id="9129" class="Symbol">)</a> <a id="9131" class="Symbol">→</a> <a id="9133" class="Symbol">∀{</a><a id="9135" href="Chapter.Logic.Negation.html#9135" class="Bound">A</a> <a id="9137" class="Symbol">:</a> <a id="9139" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="9142" class="Symbol">}</a> <a id="9144" class="Symbol">→</a> <a id="9146" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="9148" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="9150" href="Chapter.Logic.Negation.html#9135" class="Bound">A</a> <a id="9152" class="Symbol">→</a> <a id="9154" href="Chapter.Logic.Negation.html#9135" class="Bound">A</a>
<a id="9156" href="Chapter.Logic.Negation.html#9100" class="Function">em-dn</a> <a id="9162" href="Chapter.Logic.Negation.html#9162" class="Bound">f</a> <a id="9164" class="Symbol">{</a><a id="9165" href="Chapter.Logic.Negation.html#9165" class="Bound">A</a><a id="9166" class="Symbol">}</a> <a id="9168" href="Chapter.Logic.Negation.html#9168" class="Bound">g</a> <a id="9170" class="Keyword">with</a> <a id="9175" href="Chapter.Logic.Negation.html#9162" class="Bound">f</a> <a id="9177" class="Symbol">{</a><a id="9178" href="Chapter.Logic.Negation.html#9165" class="Bound">A</a><a id="9179" class="Symbol">}</a>
<a id="9181" class="Symbol">...</a> <a id="9185" class="Symbol">|</a> <a id="9187" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="9192" href="Chapter.Logic.Negation.html#9192" class="Bound">x</a> <a id="9194" class="Symbol">=</a> <a id="9196" href="Data.Empty.html#1069" class="Function">⊥-elim</a> <a id="9203" class="Symbol">(</a><a id="9204" class="Bound">g</a> <a id="9206" href="Chapter.Logic.Negation.html#9192" class="Bound">x</a><a id="9207" class="Symbol">)</a>
<a id="9209" class="Symbol">...</a> <a id="9213" class="Symbol">|</a> <a id="9215" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="9220" href="Chapter.Logic.Negation.html#9220" class="Bound">x</a> <a id="9222" class="Symbol">=</a> <a id="9224" href="Chapter.Logic.Negation.html#9220" class="Bound">x</a>

<a id="9227" class="Comment">-- EXERCISE 4</a>

<a id="nndec"></a><a id="9242" href="Chapter.Logic.Negation.html#9242" class="Function">nndec</a> <a id="9248" class="Symbol">:</a> <a id="9250" class="Symbol">∀{</a><a id="9252" href="Chapter.Logic.Negation.html#9252" class="Bound">A</a> <a id="9254" class="Symbol">:</a> <a id="9256" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="9259" class="Symbol">}</a> <a id="9261" class="Symbol">→</a> <a id="9263" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="9265" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="9267" href="Chapter.Logic.Negation.html#4787" class="Function">Decidable</a> <a id="9277" href="Chapter.Logic.Negation.html#9252" class="Bound">A</a>
<a id="9279" href="Chapter.Logic.Negation.html#9242" class="Function">nndec</a> <a id="9285" href="Chapter.Logic.Negation.html#9285" class="Bound">p</a> <a id="9287" class="Keyword">with</a> <a id="9292" href="Chapter.Logic.Negation.html#8957" class="Function">de-morgan-3</a> <a id="9304" href="Chapter.Logic.Negation.html#9285" class="Bound">p</a>
<a id="9306" class="Symbol">...</a> <a id="9310" class="Symbol">|</a> <a id="9312" href="Chapter.Logic.Negation.html#9312" class="Bound">nna</a> <a id="9316" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="9318" href="Chapter.Logic.Negation.html#9318" class="Bound">na</a> <a id="9321" class="Symbol">=</a> <a id="9323" href="Chapter.Logic.Negation.html#9312" class="Bound">nna</a> <a id="9327" href="Chapter.Logic.Negation.html#9318" class="Bound">na</a>

<a id="9331" class="Comment">-- EXERCISE 5</a>

<a id="dn-em"></a><a id="9346" href="Chapter.Logic.Negation.html#9346" class="Function">dn-em</a> <a id="9352" class="Symbol">:</a> <a id="9354" class="Symbol">(∀{</a><a id="9357" href="Chapter.Logic.Negation.html#9357" class="Bound">A</a> <a id="9359" class="Symbol">:</a> <a id="9361" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="9364" class="Symbol">}</a> <a id="9366" class="Symbol">→</a> <a id="9368" class="Symbol">(</a><a id="9369" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="9371" href="Chapter.Logic.Negation.html#719" class="Function Operator">¬</a> <a id="9373" href="Chapter.Logic.Negation.html#9357" class="Bound">A</a> <a id="9375" class="Symbol">→</a> <a id="9377" href="Chapter.Logic.Negation.html#9357" class="Bound">A</a><a id="9378" class="Symbol">))</a> <a id="9381" class="Symbol">→</a> <a id="9383" class="Symbol">∀{</a><a id="9385" href="Chapter.Logic.Negation.html#9385" class="Bound">B</a> <a id="9387" class="Symbol">:</a> <a id="9389" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="9392" class="Symbol">}</a> <a id="9394" class="Symbol">→</a> <a id="9396" href="Chapter.Logic.Negation.html#4787" class="Function">Decidable</a> <a id="9406" href="Chapter.Logic.Negation.html#9385" class="Bound">B</a>
<a id="9408" href="Chapter.Logic.Negation.html#9346" class="Function">dn-em</a> <a id="9414" href="Chapter.Logic.Negation.html#9414" class="Bound">f</a> <a id="9416" class="Symbol">=</a> <a id="9418" href="Chapter.Logic.Negation.html#9414" class="Bound">f</a> <a id="9420" href="Chapter.Logic.Negation.html#9242" class="Function">nndec</a>
</pre>{:.solution}
