---
title: Logical connectives and constants
next:  Chapter.Logic.Negation
---

<pre class="Agda"><a id="85" class="Keyword">module</a> <a id="92" href="Chapter.Logic.Connectives.html" class="Module">Chapter.Logic.Connectives</a> <a id="118" class="Keyword">where</a>
</pre>
The logic we have been using so far is based on a limited set of
Agda types:

* **Logical implication** corresponds to the *arrow type*: a proof
  of `A → B` is a function that, applied to a proof of `A`, yields
  a proof of `B`.
* **Universal quantification** corresponds to the **dependent arrow
  type**: a proof of `∀(x : A) → B` is a function that, applied to
  an element `x` of type `A`, yields a proof of `B` (where `x` may
  occur in `B`).
* **Equality** `E ≡ F` is the type of proofs showing that `E` is
  equal to `F`. In order to prove equalities we have used
  *reflexivity* and equational reasoning.

In general, we will need a richer set of logical connectives in
order to prove interesting properties of programs. For example, to
prove the correctness of a sorting function on lists we must be able
to state that the list resulting from the function is sorted *and*
that it is also a permutation of the original list. This property is
the *conjunction* of two sub-properties of lists, that is being
sorted and being a permutation of another list. In this chapter we
will see how to represent **conjunction**, **disjunction**,
**truth** and **falsity** in constructive logic by means of suitably
defined data types.

## Imports

<pre class="Agda"><a id="1377" class="Keyword">open</a> <a id="1382" class="Keyword">import</a> <a id="1389" href="Function.html" class="Module">Function</a> <a id="1398" class="Keyword">using</a> <a id="1404" class="Symbol">(</a><a id="1405" href="Function.Base.html#725" class="Function">const</a><a id="1410" class="Symbol">;</a> <a id="1412" href="Function.Base.html#704" class="Function">id</a><a id="1414" class="Symbol">;</a> <a id="1416" href="Function.Base.html#1134" class="Function Operator">_∘_</a><a id="1419" class="Symbol">)</a>
<a id="1421" class="Keyword">open</a> <a id="1426" class="Keyword">import</a> <a id="1433" href="Data.Bool.html" class="Module">Data.Bool</a> <a id="1443" class="Keyword">using</a> <a id="1449" class="Symbol">(</a><a id="1450" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="1454" class="Symbol">;</a> <a id="1456" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a><a id="1460" class="Symbol">;</a> <a id="1462" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a><a id="1467" class="Symbol">)</a>
<a id="1469" class="Keyword">open</a> <a id="1474" class="Keyword">import</a> <a id="1481" href="Data.Nat.html" class="Module">Data.Nat</a>
<a id="1490" class="Keyword">open</a> <a id="1495" class="Keyword">import</a> <a id="1502" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
</pre>
## Conjunction

In constructive logic, a proof of *`A` and `B`* is a **pair** `(p ,
q)` consisting of a proof `p` of `A` and a proof `q` of `B`. Thus,
we can define conjunction as a data type for representing
pairs. Naturally, the data type will be parametric in the type of
the two components of the pair.

<pre class="Agda"><a id="1857" class="Keyword">data</a> <a id="_×_"></a><a id="1862" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">_×_</a> <a id="1866" class="Symbol">(</a><a id="1867" href="Chapter.Logic.Connectives.html#1867" class="Bound">A</a> <a id="1869" href="Chapter.Logic.Connectives.html#1869" class="Bound">B</a> <a id="1871" class="Symbol">:</a> <a id="1873" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="1876" class="Symbol">)</a> <a id="1878" class="Symbol">:</a> <a id="1880" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="1884" class="Keyword">where</a>
  <a id="_×_._,_"></a><a id="1892" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">_,_</a> <a id="1896" class="Symbol">:</a> <a id="1898" href="Chapter.Logic.Connectives.html#1867" class="Bound">A</a> <a id="1900" class="Symbol">→</a> <a id="1902" href="Chapter.Logic.Connectives.html#1869" class="Bound">B</a> <a id="1904" class="Symbol">→</a> <a id="1906" href="Chapter.Logic.Connectives.html#1867" class="Bound">A</a> <a id="1908" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="1910" href="Chapter.Logic.Connectives.html#1869" class="Bound">B</a>
</pre>
Notice that we have chosen an infix form for both the data type
`_×_` and its constructor `_,_`. In this way, we will be able to
write `A × B` for the type of pairs whose first component has type
`A` and whose second component has type `B`. Analogously, we will be
able to write `p , q` for the pair whose first component is `p` and
whose second component is `q`. We specify the fixity of `×` and `,`
so that they are both right associative.

<pre class="Agda"><a id="2364" class="Keyword">infixr</a> <a id="2371" class="Number">3</a> <a id="2373" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">_×_</a>
<a id="2377" class="Keyword">infixr</a> <a id="2384" class="Number">4</a> <a id="2386" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">_,_</a>
</pre>
For example, `A × B × C` means `A × (B × C)` and `p , q , r` means
`p , (q , r)`.

The most common way of "consuming" pairs is by performing case
analysis on them. Since the `_×_` data type has only one
constructor, when we perform case analysis we end up considering
just one case in which the pair has the form `(x , y)`. As an
example, we can define two projections `fst` and `snd` that allow us
to access the two components of a pair.

<pre class="Agda"><a id="fst"></a><a id="2839" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="2843" class="Symbol">:</a> <a id="2845" class="Symbol">∀{</a><a id="2847" href="Chapter.Logic.Connectives.html#2847" class="Bound">A</a> <a id="2849" href="Chapter.Logic.Connectives.html#2849" class="Bound">B</a> <a id="2851" class="Symbol">:</a> <a id="2853" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2856" class="Symbol">}</a> <a id="2858" class="Symbol">→</a> <a id="2860" href="Chapter.Logic.Connectives.html#2847" class="Bound">A</a> <a id="2862" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="2864" href="Chapter.Logic.Connectives.html#2849" class="Bound">B</a> <a id="2866" class="Symbol">→</a> <a id="2868" href="Chapter.Logic.Connectives.html#2847" class="Bound">A</a>
<a id="2870" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="2874" class="Symbol">(</a><a id="2875" href="Chapter.Logic.Connectives.html#2875" class="Bound">x</a> <a id="2877" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="2879" class="Symbol">_)</a> <a id="2882" class="Symbol">=</a> <a id="2884" href="Chapter.Logic.Connectives.html#2875" class="Bound">x</a>

<a id="snd"></a><a id="2887" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="2891" class="Symbol">:</a> <a id="2893" class="Symbol">∀{</a><a id="2895" href="Chapter.Logic.Connectives.html#2895" class="Bound">A</a> <a id="2897" href="Chapter.Logic.Connectives.html#2897" class="Bound">B</a> <a id="2899" class="Symbol">:</a> <a id="2901" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2904" class="Symbol">}</a> <a id="2906" class="Symbol">→</a> <a id="2908" href="Chapter.Logic.Connectives.html#2895" class="Bound">A</a> <a id="2910" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="2912" href="Chapter.Logic.Connectives.html#2897" class="Bound">B</a> <a id="2914" class="Symbol">→</a> <a id="2916" href="Chapter.Logic.Connectives.html#2897" class="Bound">B</a>
<a id="2918" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="2922" class="Symbol">(_</a> <a id="2925" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="2927" href="Chapter.Logic.Connectives.html#2927" class="Bound">y</a><a id="2928" class="Symbol">)</a> <a id="2930" class="Symbol">=</a> <a id="2932" href="Chapter.Logic.Connectives.html#2927" class="Bound">y</a>
</pre>
Note that `fst` and `snd` are also proofs of two well-known theorems
about conjunctions: if `A × B` is true, then `A` is true (`fst`) and
`B` is true (`snd`).

By combining conjunction (given by the data type `×`) and
implication (given by the native Agda's arrow type `→`) we can also
model double implication, commonly known as "if and only if".

<pre class="Agda"><a id="_⇔_"></a><a id="3292" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">_⇔_</a> <a id="3296" class="Symbol">:</a> <a id="3298" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3302" class="Symbol">→</a> <a id="3304" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3308" class="Symbol">→</a> <a id="3310" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="3314" href="Chapter.Logic.Connectives.html#3314" class="Bound">A</a> <a id="3316" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="3318" href="Chapter.Logic.Connectives.html#3318" class="Bound">B</a> <a id="3320" class="Symbol">=</a> <a id="3322" class="Symbol">(</a><a id="3323" href="Chapter.Logic.Connectives.html#3314" class="Bound">A</a> <a id="3325" class="Symbol">→</a> <a id="3327" href="Chapter.Logic.Connectives.html#3318" class="Bound">B</a><a id="3328" class="Symbol">)</a> <a id="3330" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="3332" class="Symbol">(</a><a id="3333" href="Chapter.Logic.Connectives.html#3318" class="Bound">B</a> <a id="3335" class="Symbol">→</a> <a id="3337" href="Chapter.Logic.Connectives.html#3314" class="Bound">A</a><a id="3338" class="Symbol">)</a>
</pre>
We declare `⇔` as a right associative operator with small priority.

<pre class="Agda"><a id="3418" class="Keyword">infixr</a> <a id="3425" class="Number">1</a> <a id="3427" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">_⇔_</a>
</pre>
## Disjunction

In constructive logic, a proof of *`A` or `B`* is either a proof of
`A` or a proof of `B` together with an indication of which proof we
are providing. This interpretation suggests the representation of
disjunction `⊎` as a data type with two constructors, one taking a
proof of `A` and the other taking a proof of `B`, to yield a proof
of `A ⊎ B`. The name of the constructor indicates which of the two
proofs is provided. We call the two constructors `inj₁` and `inj₂`.

<pre class="Agda"><a id="3928" class="Keyword">data</a> <a id="_⊎_"></a><a id="3933" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">_⊎_</a> <a id="3937" class="Symbol">(</a><a id="3938" href="Chapter.Logic.Connectives.html#3938" class="Bound">A</a> <a id="3940" href="Chapter.Logic.Connectives.html#3940" class="Bound">B</a> <a id="3942" class="Symbol">:</a> <a id="3944" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3947" class="Symbol">)</a> <a id="3949" class="Symbol">:</a> <a id="3951" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3955" class="Keyword">where</a>
  <a id="_⊎_.inj₁"></a><a id="3963" href="Chapter.Logic.Connectives.html#3963" class="InductiveConstructor">inj₁</a> <a id="3968" class="Symbol">:</a> <a id="3970" href="Chapter.Logic.Connectives.html#3938" class="Bound">A</a> <a id="3972" class="Symbol">→</a> <a id="3974" href="Chapter.Logic.Connectives.html#3938" class="Bound">A</a> <a id="3976" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="3978" href="Chapter.Logic.Connectives.html#3940" class="Bound">B</a>
  <a id="_⊎_.inj₂"></a><a id="3982" href="Chapter.Logic.Connectives.html#3982" class="InductiveConstructor">inj₂</a> <a id="3987" class="Symbol">:</a> <a id="3989" href="Chapter.Logic.Connectives.html#3940" class="Bound">B</a> <a id="3991" class="Symbol">→</a> <a id="3993" href="Chapter.Logic.Connectives.html#3938" class="Bound">A</a> <a id="3995" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="3997" href="Chapter.Logic.Connectives.html#3940" class="Bound">B</a>
</pre>
We declare `⊎` as a right associative operator with smaller
precedence than `×`.

<pre class="Agda"><a id="4090" class="Keyword">infixr</a> <a id="4097" class="Number">2</a> <a id="4099" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">_⊎_</a>
</pre>
As for conjunctions, we will use case analysis on terms of type `A ⊎
B`. As an example, we can formulate the elimination principle for
disjunctions as the following function.

<pre class="Agda"><a id="⊎-elim"></a><a id="4288" href="Chapter.Logic.Connectives.html#4288" class="Function">⊎-elim</a> <a id="4295" class="Symbol">:</a> <a id="4297" class="Symbol">∀{</a><a id="4299" href="Chapter.Logic.Connectives.html#4299" class="Bound">A</a> <a id="4301" href="Chapter.Logic.Connectives.html#4301" class="Bound">B</a> <a id="4303" href="Chapter.Logic.Connectives.html#4303" class="Bound">C</a> <a id="4305" class="Symbol">:</a> <a id="4307" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4310" class="Symbol">}</a> <a id="4312" class="Symbol">→</a> <a id="4314" class="Symbol">(</a><a id="4315" href="Chapter.Logic.Connectives.html#4299" class="Bound">A</a> <a id="4317" class="Symbol">→</a> <a id="4319" href="Chapter.Logic.Connectives.html#4303" class="Bound">C</a><a id="4320" class="Symbol">)</a> <a id="4322" class="Symbol">→</a> <a id="4324" class="Symbol">(</a><a id="4325" href="Chapter.Logic.Connectives.html#4301" class="Bound">B</a> <a id="4327" class="Symbol">→</a> <a id="4329" href="Chapter.Logic.Connectives.html#4303" class="Bound">C</a><a id="4330" class="Symbol">)</a> <a id="4332" class="Symbol">→</a> <a id="4334" href="Chapter.Logic.Connectives.html#4299" class="Bound">A</a> <a id="4336" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="4338" href="Chapter.Logic.Connectives.html#4301" class="Bound">B</a> <a id="4340" class="Symbol">→</a> <a id="4342" href="Chapter.Logic.Connectives.html#4303" class="Bound">C</a>
<a id="4344" href="Chapter.Logic.Connectives.html#4288" class="Function">⊎-elim</a> <a id="4351" href="Chapter.Logic.Connectives.html#4351" class="Bound">f</a> <a id="4353" href="Chapter.Logic.Connectives.html#4353" class="Bound">g</a> <a id="4355" class="Symbol">(</a><a id="4356" href="Chapter.Logic.Connectives.html#3963" class="InductiveConstructor">inj₁</a> <a id="4361" href="Chapter.Logic.Connectives.html#4361" class="Bound">x</a><a id="4362" class="Symbol">)</a> <a id="4364" class="Symbol">=</a> <a id="4366" href="Chapter.Logic.Connectives.html#4351" class="Bound">f</a> <a id="4368" href="Chapter.Logic.Connectives.html#4361" class="Bound">x</a>
<a id="4370" href="Chapter.Logic.Connectives.html#4288" class="Function">⊎-elim</a> <a id="4377" href="Chapter.Logic.Connectives.html#4377" class="Bound">f</a> <a id="4379" href="Chapter.Logic.Connectives.html#4379" class="Bound">g</a> <a id="4381" class="Symbol">(</a><a id="4382" href="Chapter.Logic.Connectives.html#3982" class="InductiveConstructor">inj₂</a> <a id="4387" href="Chapter.Logic.Connectives.html#4387" class="Bound">x</a><a id="4388" class="Symbol">)</a> <a id="4390" class="Symbol">=</a> <a id="4392" href="Chapter.Logic.Connectives.html#4379" class="Bound">g</a> <a id="4394" href="Chapter.Logic.Connectives.html#4387" class="Bound">x</a>
</pre>
For instance, we can use `⊎-elim` to prove that disjunction is
commutative:

<pre class="Agda"><a id="⊎-comm"></a><a id="4482" href="Chapter.Logic.Connectives.html#4482" class="Function">⊎-comm</a> <a id="4489" class="Symbol">:</a> <a id="4491" class="Symbol">∀{</a><a id="4493" href="Chapter.Logic.Connectives.html#4493" class="Bound">A</a> <a id="4495" href="Chapter.Logic.Connectives.html#4495" class="Bound">B</a> <a id="4497" class="Symbol">:</a> <a id="4499" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4502" class="Symbol">}</a> <a id="4504" class="Symbol">→</a> <a id="4506" href="Chapter.Logic.Connectives.html#4493" class="Bound">A</a> <a id="4508" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="4510" href="Chapter.Logic.Connectives.html#4495" class="Bound">B</a> <a id="4512" class="Symbol">→</a> <a id="4514" href="Chapter.Logic.Connectives.html#4495" class="Bound">B</a> <a id="4516" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="4518" href="Chapter.Logic.Connectives.html#4493" class="Bound">A</a>
<a id="4520" href="Chapter.Logic.Connectives.html#4482" class="Function">⊎-comm</a> <a id="4527" class="Symbol">=</a> <a id="4529" href="Chapter.Logic.Connectives.html#4288" class="Function">⊎-elim</a> <a id="4536" href="Chapter.Logic.Connectives.html#3982" class="InductiveConstructor">inj₂</a> <a id="4541" href="Chapter.Logic.Connectives.html#3963" class="InductiveConstructor">inj₁</a>
</pre>
## Truth

The always true proposition `⊤` is represented as a data type with a
single constructor without arguments. That is, truth is a
proposition for which we can provide a proof without any effort.

<pre class="Agda"><a id="4758" class="Keyword">data</a> <a id="⊤"></a><a id="4763" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a> <a id="4765" class="Symbol">:</a> <a id="4767" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="4771" class="Keyword">where</a>
  <a id="⊤.tt"></a><a id="4779" href="Chapter.Logic.Connectives.html#4779" class="InductiveConstructor">tt</a> <a id="4782" class="Symbol">:</a> <a id="4784" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a>
</pre>
## Falsity

The always false proposition `⊥` must not be provable. As such, we
can represent it by a data type without constructors.

<pre class="Agda"><a id="4929" class="Keyword">data</a> <a id="⊥"></a><a id="4934" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a> <a id="4936" class="Symbol">:</a> <a id="4938" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="4942" class="Keyword">where</a>
</pre>
The elimination principle for `⊥` is sometimes called *principle of
explosion* or *ex falso quodlibet*. It states that if it is possible
to prove `⊥`, then it is possible to prove anything. Stating this
principle in Agda requires the use of the **absurd pattern**.

<pre class="Agda"><a id="⊥-elim"></a><a id="5223" href="Chapter.Logic.Connectives.html#5223" class="Function">⊥-elim</a> <a id="5230" class="Symbol">:</a> <a id="5232" class="Symbol">∀{</a><a id="5234" href="Chapter.Logic.Connectives.html#5234" class="Bound">A</a> <a id="5236" class="Symbol">:</a> <a id="5238" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5241" class="Symbol">}</a> <a id="5243" class="Symbol">→</a> <a id="5245" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a> <a id="5247" class="Symbol">→</a> <a id="5249" href="Chapter.Logic.Connectives.html#5234" class="Bound">A</a>
<a id="5251" href="Chapter.Logic.Connectives.html#5223" class="Function">⊥-elim</a> <a id="5258" class="Symbol">()</a>
</pre>
The pattern `()` in the definition of `⊥-elim` matches an
hypothetical value of type `⊥`. Since no constructor is provided for
`⊥` and no such value may exist, the equation *has no right hand
side* (note that there is no equal sign) and we are not obliged to
provide a proof of `A` as required by the codomain of `⊥-elim`.

In other programming languages that are capable of defining a data
type analogous to `⊥` it is possible to assign the type `⊥` to
non-terminating expressions. If this were allowed also in Agda, the
whole language would be useless insofar program verification is
concerned, since `⊥-elim` would easily allow us to prove *any*
property about *any* program. For this reason, Agda has a
*termination checker* making sure that every definition is
*terminating*. For example, if define `loop` as follows

<!--
<pre class="Agda"><a id="6098" class="Symbol">{-#</a> <a id="6102" class="Keyword">TERMINATING</a> <a id="6114" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="loop"></a><a id="6130" href="Chapter.Logic.Connectives.html#6130" class="Function">loop</a> <a id="6135" class="Symbol">:</a> <a id="6137" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6139" class="Symbol">→</a> <a id="6141" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a>
<a id="6143" href="Chapter.Logic.Connectives.html#6130" class="Function">loop</a> <a id="6148" href="Chapter.Logic.Connectives.html#6148" class="Bound">n</a> <a id="6150" class="Symbol">=</a> <a id="6152" href="Chapter.Logic.Connectives.html#6130" class="Function">loop</a> <a id="6157" class="Symbol">(</a><a id="6158" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="6162" href="Chapter.Logic.Connectives.html#6148" class="Bound">n</a><a id="6163" class="Symbol">)</a>
</pre>
Agda reports that this definition does not pass the termination
check. Indeed, `loop` is recursively applied to increasingly larger
arguments. An even simpler example of non-terminating definition is
`bottom`, shown below.

<!--
<pre class="Agda"><a id="6403" class="Symbol">{-#</a> <a id="6407" class="Keyword">TERMINATING</a> <a id="6419" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="bottom"></a><a id="6435" href="Chapter.Logic.Connectives.html#6435" class="Function">bottom</a> <a id="6442" class="Symbol">:</a> <a id="6444" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a>
<a id="6446" href="Chapter.Logic.Connectives.html#6435" class="Function">bottom</a> <a id="6453" class="Symbol">=</a> <a id="6455" href="Chapter.Logic.Connectives.html#6435" class="Function">bottom</a>
</pre>
All the recursive functions we have defined until now are verified
by Agda to be *terminating* because there is an argument that
becomes *structurally smaller* from an application of the function
to its recursive invocation. Structural recursion applies to a large
family of functions, but some of them
<!--
(e.g. [division](Chapter.Fun.Division.html) or [quick
sort](Chapter.Fun.QuickSort.html))
-->
cannot be easily formulated in this way. We will see a general
technique for having these functions accepted by Agda in later
sections.

## Exercises

1. Prove that conjunction is commutative, namely the theorem
   `×-comm : ∀{A B : Set} → A × B → B × A`.
2. Prove that `×` and `⊎` are idempotent, namely the theorems
   `×-idem : ∀{A : Set} → A × A ⇔ A` and `⊎-idem : ∀{A : Set} → A
   ⊎ A ⇔ A`.
3. Prove that `×` distributes over `⊎` on the left, namely the
   theorem `×⊎-dist : ∀{A B C : Set} → A × (B ⊎ C) ⇔ (A × B) ⊎ (A ×
   C)`.
4. Prove that `⊤` is the unit of conjuction, namely the theorems
   `×-unit-l : ∀{A : Set} → ⊤ × A ⇔ A` and `×-unit-r : ∀{A : Set}
   → A × ⊤ ⇔ A`.
5. Prove that `⊤` absorbs disjunctions, namely the theorems `⊎-⊤-l :
   ∀{A : Set} → ⊤ ⊎ A ⇔ ⊤` and `⊎-⊤-r : ∀{A : Set} → A ⊎ ⊤ ⇔ ⊤`.
6. Prove that `⊥` is the unit of disjunctions, namely the theorems
   `⊎-unit-l : ∀{A : Set} → ⊥ ⊎ A ⇔ A` and `⊎-unit-r : ∀{A : Set}
   → A ⊎ ⊥ ⇔ A`.
7. Prove that `⊥` absorbs conjunctions, namely the theorems `×-⊥-l :
   ∀{A : Set} → ⊥ × A ⇔ ⊥` and `×-⊥-r : ∀{A : Set} → A × ⊥ ⇔ ⊥`.
8. Prove that every boolean value is either `true` or `false`,
   namely the theorem `Bool-⊎ : ∀(b : Bool) → (b ≡ true) ⊎ (b ≡
   false)`.

<pre class="Agda"><a id="8114" class="Comment">-- EXERCISE 1</a>
<a id="×-comm"></a><a id="8128" href="Chapter.Logic.Connectives.html#8128" class="Function">×-comm</a> <a id="8135" class="Symbol">:</a> <a id="8137" class="Symbol">∀{</a><a id="8139" href="Chapter.Logic.Connectives.html#8139" class="Bound">A</a> <a id="8141" href="Chapter.Logic.Connectives.html#8141" class="Bound">B</a> <a id="8143" class="Symbol">:</a> <a id="8145" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8148" class="Symbol">}</a> <a id="8150" class="Symbol">→</a> <a id="8152" href="Chapter.Logic.Connectives.html#8139" class="Bound">A</a> <a id="8154" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8156" href="Chapter.Logic.Connectives.html#8141" class="Bound">B</a> <a id="8158" class="Symbol">→</a> <a id="8160" href="Chapter.Logic.Connectives.html#8141" class="Bound">B</a> <a id="8162" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8164" href="Chapter.Logic.Connectives.html#8139" class="Bound">A</a>
<a id="8166" href="Chapter.Logic.Connectives.html#8128" class="Function">×-comm</a> <a id="8173" class="Symbol">(</a><a id="8174" href="Chapter.Logic.Connectives.html#8174" class="Bound">x</a> <a id="8176" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8178" href="Chapter.Logic.Connectives.html#8178" class="Bound">y</a><a id="8179" class="Symbol">)</a> <a id="8181" class="Symbol">=</a> <a id="8183" href="Chapter.Logic.Connectives.html#8178" class="Bound">y</a> <a id="8185" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8187" href="Chapter.Logic.Connectives.html#8174" class="Bound">x</a>

<a id="8190" class="Comment">-- EXERCISE 2</a>
<a id="×-idem"></a><a id="8204" href="Chapter.Logic.Connectives.html#8204" class="Function">×-idem</a> <a id="8211" class="Symbol">:</a> <a id="8213" class="Symbol">∀{</a><a id="8215" href="Chapter.Logic.Connectives.html#8215" class="Bound">A</a> <a id="8217" class="Symbol">:</a> <a id="8219" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8222" class="Symbol">}</a> <a id="8224" class="Symbol">→</a> <a id="8226" href="Chapter.Logic.Connectives.html#8215" class="Bound">A</a> <a id="8228" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8230" href="Chapter.Logic.Connectives.html#8215" class="Bound">A</a> <a id="8232" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8234" href="Chapter.Logic.Connectives.html#8215" class="Bound">A</a>
<a id="8236" href="Chapter.Logic.Connectives.html#8204" class="Function">×-idem</a> <a id="8243" class="Symbol">=</a> <a id="8245" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8249" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8251" class="Symbol">λ</a> <a id="8253" href="Chapter.Logic.Connectives.html#8253" class="Bound">x</a> <a id="8255" class="Symbol">→</a> <a id="8257" class="Symbol">(</a><a id="8258" href="Chapter.Logic.Connectives.html#8253" class="Bound">x</a> <a id="8260" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8262" href="Chapter.Logic.Connectives.html#8253" class="Bound">x</a><a id="8263" class="Symbol">)</a>

<a id="⊎-idem"></a><a id="8266" href="Chapter.Logic.Connectives.html#8266" class="Function">⊎-idem</a> <a id="8273" class="Symbol">:</a> <a id="8275" class="Symbol">∀{</a><a id="8277" href="Chapter.Logic.Connectives.html#8277" class="Bound">A</a> <a id="8279" class="Symbol">:</a> <a id="8281" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8284" class="Symbol">}</a> <a id="8286" class="Symbol">→</a> <a id="8288" href="Chapter.Logic.Connectives.html#8277" class="Bound">A</a> <a id="8290" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="8292" href="Chapter.Logic.Connectives.html#8277" class="Bound">A</a> <a id="8294" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8296" href="Chapter.Logic.Connectives.html#8277" class="Bound">A</a>
<a id="8298" href="Chapter.Logic.Connectives.html#8266" class="Function">⊎-idem</a> <a id="8305" class="Symbol">=</a> <a id="8307" href="Chapter.Logic.Connectives.html#4288" class="Function">⊎-elim</a> <a id="8314" href="Function.Base.html#704" class="Function">id</a> <a id="8317" href="Function.Base.html#704" class="Function">id</a> <a id="8320" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8322" href="Chapter.Logic.Connectives.html#3963" class="InductiveConstructor">inj₁</a>

<a id="8328" class="Comment">-- EXERCISE 3</a>
<a id="×⊎-dist"></a><a id="8342" href="Chapter.Logic.Connectives.html#8342" class="Function">×⊎-dist</a> <a id="8350" class="Symbol">:</a> <a id="8352" class="Symbol">∀{</a><a id="8354" href="Chapter.Logic.Connectives.html#8354" class="Bound">A</a> <a id="8356" href="Chapter.Logic.Connectives.html#8356" class="Bound">B</a> <a id="8358" href="Chapter.Logic.Connectives.html#8358" class="Bound">C</a> <a id="8360" class="Symbol">:</a> <a id="8362" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8365" class="Symbol">}</a> <a id="8367" class="Symbol">→</a> <a id="8369" href="Chapter.Logic.Connectives.html#8354" class="Bound">A</a> <a id="8371" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8373" class="Symbol">(</a><a id="8374" href="Chapter.Logic.Connectives.html#8356" class="Bound">B</a> <a id="8376" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="8378" href="Chapter.Logic.Connectives.html#8358" class="Bound">C</a><a id="8379" class="Symbol">)</a> <a id="8381" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8383" class="Symbol">(</a><a id="8384" href="Chapter.Logic.Connectives.html#8354" class="Bound">A</a> <a id="8386" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8388" href="Chapter.Logic.Connectives.html#8356" class="Bound">B</a><a id="8389" class="Symbol">)</a> <a id="8391" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="8393" class="Symbol">(</a><a id="8394" href="Chapter.Logic.Connectives.html#8354" class="Bound">A</a> <a id="8396" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8398" href="Chapter.Logic.Connectives.html#8358" class="Bound">C</a><a id="8399" class="Symbol">)</a>
<a id="8401" href="Chapter.Logic.Connectives.html#8342" class="Function">×⊎-dist</a> <a id="8409" class="Symbol">=</a>
  <a id="8413" class="Symbol">(λ</a> <a id="8416" href="Chapter.Logic.Connectives.html#8416" class="Bound">p</a> <a id="8418" class="Symbol">→</a> <a id="8420" href="Chapter.Logic.Connectives.html#4288" class="Function">⊎-elim</a> <a id="8427" class="Symbol">(</a><a id="8428" href="Chapter.Logic.Connectives.html#3963" class="InductiveConstructor">inj₁</a> <a id="8433" href="Function.Base.html#1134" class="Function Operator">∘</a> <a id="8435" class="Symbol">(</a><a id="8436" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8440" href="Chapter.Logic.Connectives.html#8416" class="Bound">p</a> <a id="8442" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,_</a><a id="8444" class="Symbol">))</a> <a id="8447" class="Symbol">(</a><a id="8448" href="Chapter.Logic.Connectives.html#3982" class="InductiveConstructor">inj₂</a> <a id="8453" href="Function.Base.html#1134" class="Function Operator">∘</a> <a id="8455" class="Symbol">(</a><a id="8456" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8460" href="Chapter.Logic.Connectives.html#8416" class="Bound">p</a> <a id="8462" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,_</a><a id="8464" class="Symbol">))</a> <a id="8467" class="Symbol">(</a><a id="8468" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="8472" href="Chapter.Logic.Connectives.html#8416" class="Bound">p</a><a id="8473" class="Symbol">))</a> <a id="8476" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a>
  <a id="8480" href="Chapter.Logic.Connectives.html#4288" class="Function">⊎-elim</a> <a id="8487" class="Symbol">(λ</a> <a id="8490" href="Chapter.Logic.Connectives.html#8490" class="Bound">p</a> <a id="8492" class="Symbol">→</a> <a id="8494" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8498" href="Chapter.Logic.Connectives.html#8490" class="Bound">p</a> <a id="8500" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8502" href="Chapter.Logic.Connectives.html#3963" class="InductiveConstructor">inj₁</a> <a id="8507" class="Symbol">(</a><a id="8508" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="8512" href="Chapter.Logic.Connectives.html#8490" class="Bound">p</a><a id="8513" class="Symbol">))</a> <a id="8516" class="Symbol">(λ</a> <a id="8519" href="Chapter.Logic.Connectives.html#8519" class="Bound">p</a> <a id="8521" class="Symbol">→</a> <a id="8523" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8527" href="Chapter.Logic.Connectives.html#8519" class="Bound">p</a> <a id="8529" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8531" href="Chapter.Logic.Connectives.html#3982" class="InductiveConstructor">inj₂</a> <a id="8536" class="Symbol">(</a><a id="8537" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="8541" href="Chapter.Logic.Connectives.html#8519" class="Bound">p</a><a id="8542" class="Symbol">))</a>

<a id="8546" class="Comment">-- EXERCISE 4</a>
<a id="×-unit-l"></a><a id="8560" href="Chapter.Logic.Connectives.html#8560" class="Function">×-unit-l</a> <a id="8569" class="Symbol">:</a> <a id="8571" class="Symbol">∀{</a><a id="8573" href="Chapter.Logic.Connectives.html#8573" class="Bound">A</a> <a id="8575" class="Symbol">:</a> <a id="8577" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8580" class="Symbol">}</a> <a id="8582" class="Symbol">→</a> <a id="8584" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a> <a id="8586" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8588" href="Chapter.Logic.Connectives.html#8573" class="Bound">A</a> <a id="8590" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8592" href="Chapter.Logic.Connectives.html#8573" class="Bound">A</a>
<a id="8594" href="Chapter.Logic.Connectives.html#8560" class="Function">×-unit-l</a> <a id="8603" class="Symbol">=</a> <a id="8605" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="8609" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8611" class="Symbol">(</a><a id="8612" href="Chapter.Logic.Connectives.html#4779" class="InductiveConstructor">tt</a> <a id="8615" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,_</a><a id="8617" class="Symbol">)</a>

<a id="×-unit-r"></a><a id="8620" href="Chapter.Logic.Connectives.html#8620" class="Function">×-unit-r</a> <a id="8629" class="Symbol">:</a> <a id="8631" class="Symbol">∀{</a><a id="8633" href="Chapter.Logic.Connectives.html#8633" class="Bound">A</a> <a id="8635" class="Symbol">:</a> <a id="8637" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8640" class="Symbol">}</a> <a id="8642" class="Symbol">→</a> <a id="8644" href="Chapter.Logic.Connectives.html#8633" class="Bound">A</a> <a id="8646" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8648" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a> <a id="8650" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8652" href="Chapter.Logic.Connectives.html#8633" class="Bound">A</a>
<a id="8654" href="Chapter.Logic.Connectives.html#8620" class="Function">×-unit-r</a> <a id="8663" class="Symbol">=</a> <a id="8665" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8669" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8671" class="Symbol">(</a><a id="8672" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">_,</a> <a id="8675" href="Chapter.Logic.Connectives.html#4779" class="InductiveConstructor">tt</a><a id="8677" class="Symbol">)</a>

<a id="8680" class="Comment">-- EXERCISE 5</a>
<a id="⊎-unit-l"></a><a id="8694" href="Chapter.Logic.Connectives.html#8694" class="Function">⊎-unit-l</a> <a id="8703" class="Symbol">:</a> <a id="8705" class="Symbol">∀{</a><a id="8707" href="Chapter.Logic.Connectives.html#8707" class="Bound">A</a> <a id="8709" class="Symbol">:</a> <a id="8711" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8714" class="Symbol">}</a> <a id="8716" class="Symbol">→</a> <a id="8718" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a> <a id="8720" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="8722" href="Chapter.Logic.Connectives.html#8707" class="Bound">A</a> <a id="8724" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8726" href="Chapter.Logic.Connectives.html#8707" class="Bound">A</a>
<a id="8728" href="Chapter.Logic.Connectives.html#8694" class="Function">⊎-unit-l</a> <a id="8737" class="Symbol">=</a> <a id="8739" href="Chapter.Logic.Connectives.html#4288" class="Function">⊎-elim</a> <a id="8746" href="Chapter.Logic.Connectives.html#5223" class="Function">⊥-elim</a> <a id="8753" href="Function.Base.html#704" class="Function">id</a> <a id="8756" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8758" href="Chapter.Logic.Connectives.html#3982" class="InductiveConstructor">inj₂</a>

<a id="⊎-unit-r"></a><a id="8764" href="Chapter.Logic.Connectives.html#8764" class="Function">⊎-unit-r</a> <a id="8773" class="Symbol">:</a> <a id="8775" class="Symbol">∀{</a><a id="8777" href="Chapter.Logic.Connectives.html#8777" class="Bound">A</a> <a id="8779" class="Symbol">:</a> <a id="8781" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8784" class="Symbol">}</a> <a id="8786" class="Symbol">→</a> <a id="8788" href="Chapter.Logic.Connectives.html#8777" class="Bound">A</a> <a id="8790" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="8792" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a> <a id="8794" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8796" href="Chapter.Logic.Connectives.html#8777" class="Bound">A</a>
<a id="8798" href="Chapter.Logic.Connectives.html#8764" class="Function">⊎-unit-r</a> <a id="8807" class="Symbol">=</a> <a id="8809" href="Chapter.Logic.Connectives.html#4288" class="Function">⊎-elim</a> <a id="8816" href="Function.Base.html#704" class="Function">id</a> <a id="8819" href="Chapter.Logic.Connectives.html#5223" class="Function">⊥-elim</a> <a id="8826" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8828" href="Chapter.Logic.Connectives.html#3963" class="InductiveConstructor">inj₁</a>

<a id="8834" class="Comment">-- EXERCISE 6</a>
<a id="⊎-⊤-l"></a><a id="8848" href="Chapter.Logic.Connectives.html#8848" class="Function">⊎-⊤-l</a> <a id="8854" class="Symbol">:</a> <a id="8856" class="Symbol">∀{</a><a id="8858" href="Chapter.Logic.Connectives.html#8858" class="Bound">A</a> <a id="8860" class="Symbol">:</a> <a id="8862" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8865" class="Symbol">}</a> <a id="8867" class="Symbol">→</a> <a id="8869" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a> <a id="8871" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="8873" href="Chapter.Logic.Connectives.html#8858" class="Bound">A</a> <a id="8875" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8877" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a>
<a id="8879" href="Chapter.Logic.Connectives.html#8848" class="Function">⊎-⊤-l</a> <a id="8885" class="Symbol">=</a> <a id="8887" href="Function.Base.html#725" class="Function">const</a> <a id="8893" href="Chapter.Logic.Connectives.html#4779" class="InductiveConstructor">tt</a> <a id="8896" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8898" href="Chapter.Logic.Connectives.html#3963" class="InductiveConstructor">inj₁</a>

<a id="⊎-⊤-r"></a><a id="8904" href="Chapter.Logic.Connectives.html#8904" class="Function">⊎-⊤-r</a> <a id="8910" class="Symbol">:</a> <a id="8912" class="Symbol">∀{</a><a id="8914" href="Chapter.Logic.Connectives.html#8914" class="Bound">A</a> <a id="8916" class="Symbol">:</a> <a id="8918" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8921" class="Symbol">}</a> <a id="8923" class="Symbol">→</a> <a id="8925" href="Chapter.Logic.Connectives.html#8914" class="Bound">A</a> <a id="8927" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="8929" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a> <a id="8931" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8933" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a>
<a id="8935" href="Chapter.Logic.Connectives.html#8904" class="Function">⊎-⊤-r</a> <a id="8941" class="Symbol">=</a> <a id="8943" href="Function.Base.html#725" class="Function">const</a> <a id="8949" href="Chapter.Logic.Connectives.html#4779" class="InductiveConstructor">tt</a> <a id="8952" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8954" href="Chapter.Logic.Connectives.html#3982" class="InductiveConstructor">inj₂</a>

<a id="8960" class="Comment">-- EXERCISE 7</a>
<a id="×-⊥-l"></a><a id="8974" href="Chapter.Logic.Connectives.html#8974" class="Function">×-⊥-l</a> <a id="8980" class="Symbol">:</a> <a id="8982" class="Symbol">∀{</a><a id="8984" href="Chapter.Logic.Connectives.html#8984" class="Bound">A</a> <a id="8986" class="Symbol">:</a> <a id="8988" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8991" class="Symbol">}</a> <a id="8993" class="Symbol">→</a> <a id="8995" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a> <a id="8997" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8999" href="Chapter.Logic.Connectives.html#8984" class="Bound">A</a> <a id="9001" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="9003" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a>
<a id="9005" href="Chapter.Logic.Connectives.html#8974" class="Function">×-⊥-l</a> <a id="9011" class="Symbol">=</a> <a id="9013" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="9017" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="9019" href="Chapter.Logic.Connectives.html#5223" class="Function">⊥-elim</a>

<a id="×-⊥-r"></a><a id="9027" href="Chapter.Logic.Connectives.html#9027" class="Function">×-⊥-r</a> <a id="9033" class="Symbol">:</a> <a id="9035" class="Symbol">∀{</a><a id="9037" href="Chapter.Logic.Connectives.html#9037" class="Bound">A</a> <a id="9039" class="Symbol">:</a> <a id="9041" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="9044" class="Symbol">}</a> <a id="9046" class="Symbol">→</a> <a id="9048" href="Chapter.Logic.Connectives.html#9037" class="Bound">A</a> <a id="9050" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="9052" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a> <a id="9054" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="9056" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a>
<a id="9058" href="Chapter.Logic.Connectives.html#9027" class="Function">×-⊥-r</a> <a id="9064" class="Symbol">=</a> <a id="9066" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="9070" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="9072" href="Chapter.Logic.Connectives.html#5223" class="Function">⊥-elim</a>

<a id="9080" class="Comment">-- EXERCISE 8</a>
<a id="Bool-⊎"></a><a id="9094" href="Chapter.Logic.Connectives.html#9094" class="Function">Bool-⊎</a> <a id="9101" class="Symbol">:</a> <a id="9103" class="Symbol">∀(</a><a id="9105" href="Chapter.Logic.Connectives.html#9105" class="Bound">b</a> <a id="9107" class="Symbol">:</a> <a id="9109" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="9113" class="Symbol">)</a> <a id="9115" class="Symbol">→</a> <a id="9117" class="Symbol">(</a><a id="9118" href="Chapter.Logic.Connectives.html#9105" class="Bound">b</a> <a id="9120" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9122" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a><a id="9126" class="Symbol">)</a> <a id="9128" href="Chapter.Logic.Connectives.html#3933" class="Datatype Operator">⊎</a> <a id="9130" class="Symbol">(</a><a id="9131" href="Chapter.Logic.Connectives.html#9105" class="Bound">b</a> <a id="9133" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9135" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a><a id="9140" class="Symbol">)</a>
<a id="9142" href="Chapter.Logic.Connectives.html#9094" class="Function">Bool-⊎</a> <a id="9149" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="9155" class="Symbol">=</a> <a id="9157" href="Chapter.Logic.Connectives.html#3963" class="InductiveConstructor">inj₁</a> <a id="9162" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="9167" href="Chapter.Logic.Connectives.html#9094" class="Function">Bool-⊎</a> <a id="9174" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="9180" class="Symbol">=</a> <a id="9182" href="Chapter.Logic.Connectives.html#3982" class="InductiveConstructor">inj₂</a> <a id="9187" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

</pre>{:.solution}
