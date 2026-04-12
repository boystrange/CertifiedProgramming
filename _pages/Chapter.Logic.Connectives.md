---
title: Logical connectives and constants
next:  Chapter.Logic.Negation
---

<pre class="Agda"><a id="85" class="Keyword">module</a> <a id="92" href="Chapter.Logic.Connectives.html" class="Module">Chapter.Logic.Connectives</a> <a id="118" class="Keyword">where</a>
</pre>
The logic we have been using so far is based on a limited set of
Agda types:

* **Logical implication** corresponds to the *arrow type*: a proof
  of `A -> B` is a function that, applied to a proof of `A`, yields
  a proof of `B`.
* **Universal quantification** corresponds to the **dependent arrow
  type**: a proof of `∀(x : A) -> B` is a function that, applied to
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

<pre class="Agda"><a id="1379" class="Keyword">open</a> <a id="1384" class="Keyword">import</a> <a id="1391" href="Function.html" class="Module">Function</a> <a id="1400" class="Keyword">using</a> <a id="1406" class="Symbol">(</a><a id="1407" href="Function.Base.html#725" class="Function">const</a><a id="1412" class="Symbol">;</a> <a id="1414" href="Function.Base.html#704" class="Function">id</a><a id="1416" class="Symbol">;</a> <a id="1418" href="Function.Base.html#1134" class="Function Operator">_∘_</a><a id="1421" class="Symbol">)</a>
<a id="1423" class="Keyword">open</a> <a id="1428" class="Keyword">import</a> <a id="1435" href="Data.Bool.html" class="Module">Data.Bool</a> <a id="1445" class="Keyword">using</a> <a id="1451" class="Symbol">(</a><a id="1452" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="1456" class="Symbol">;</a> <a id="1458" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a><a id="1462" class="Symbol">;</a> <a id="1464" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a><a id="1469" class="Symbol">)</a>
<a id="1471" class="Keyword">open</a> <a id="1476" class="Keyword">import</a> <a id="1483" href="Data.Nat.html" class="Module">Data.Nat</a>
<a id="1492" class="Keyword">open</a> <a id="1497" class="Keyword">import</a> <a id="1504" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
</pre>
## Conjunction

In constructive logic, a proof of *`A` and `B`* is a **pair** `(p ,
q)` consisting of a proof `p` of `A` and a proof `q` of `B`. Thus,
we can define conjunction as a data type for representing
pairs. Naturally, the data type will be parametric in the type of
the two components of the pair.

<pre class="Agda"><a id="1859" class="Keyword">data</a> <a id="_×_"></a><a id="1864" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">_×_</a> <a id="1868" class="Symbol">(</a><a id="1869" href="Chapter.Logic.Connectives.html#1869" class="Bound">A</a> <a id="1871" href="Chapter.Logic.Connectives.html#1871" class="Bound">B</a> <a id="1873" class="Symbol">:</a> <a id="1875" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="1878" class="Symbol">)</a> <a id="1880" class="Symbol">:</a> <a id="1882" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="1886" class="Keyword">where</a>
  <a id="_×_._,_"></a><a id="1894" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">_,_</a> <a id="1898" class="Symbol">:</a> <a id="1900" href="Chapter.Logic.Connectives.html#1869" class="Bound">A</a> <a id="1902" class="Symbol">-&gt;</a> <a id="1905" href="Chapter.Logic.Connectives.html#1871" class="Bound">B</a> <a id="1907" class="Symbol">-&gt;</a> <a id="1910" href="Chapter.Logic.Connectives.html#1869" class="Bound">A</a> <a id="1912" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="1914" href="Chapter.Logic.Connectives.html#1871" class="Bound">B</a>
</pre>
Notice that we have chosen an infix form for both the data type
`_×_` and its constructor `_,_`. In this way, we will be able to
write `A × B` for the type of pairs whose first component has type
`A` and whose second component has type `B`. Analogously, we will be
able to write `p , q` for the pair whose first component is `p` and
whose second component is `q`. We specify the fixity of `×` and `,`
so that they are both right associative.

<pre class="Agda"><a id="2368" class="Keyword">infixr</a> <a id="2375" class="Number">3</a> <a id="2377" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">_×_</a>
<a id="2381" class="Keyword">infixr</a> <a id="2388" class="Number">4</a> <a id="2390" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">_,_</a>
</pre>
For example, `A × B × C` means `A × (B × C)` and `p , q , r` means
`p , (q , r)`.

The most common way of "consuming" pairs is by performing case
analysis on them. Since the `_×_` data type has only one
constructor, when we perform case analysis we end up considering
just one case in which the pair has the form `(x , y)`. As an
example, we can define two projections `fst` and `snd` that allow us
to access the two components of a pair.

<pre class="Agda"><a id="fst"></a><a id="2843" href="Chapter.Logic.Connectives.html#2843" class="Function">fst</a> <a id="2847" class="Symbol">:</a> <a id="2849" class="Symbol">∀{</a><a id="2851" href="Chapter.Logic.Connectives.html#2851" class="Bound">A</a> <a id="2853" href="Chapter.Logic.Connectives.html#2853" class="Bound">B</a> <a id="2855" class="Symbol">:</a> <a id="2857" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2860" class="Symbol">}</a> <a id="2862" class="Symbol">-&gt;</a> <a id="2865" href="Chapter.Logic.Connectives.html#2851" class="Bound">A</a> <a id="2867" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="2869" href="Chapter.Logic.Connectives.html#2853" class="Bound">B</a> <a id="2871" class="Symbol">-&gt;</a> <a id="2874" href="Chapter.Logic.Connectives.html#2851" class="Bound">A</a>
<a id="2876" href="Chapter.Logic.Connectives.html#2843" class="Function">fst</a> <a id="2880" class="Symbol">(</a><a id="2881" href="Chapter.Logic.Connectives.html#2881" class="Bound">x</a> <a id="2883" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="2885" class="Symbol">_)</a> <a id="2888" class="Symbol">=</a> <a id="2890" href="Chapter.Logic.Connectives.html#2881" class="Bound">x</a>

<a id="snd"></a><a id="2893" href="Chapter.Logic.Connectives.html#2893" class="Function">snd</a> <a id="2897" class="Symbol">:</a> <a id="2899" class="Symbol">∀{</a><a id="2901" href="Chapter.Logic.Connectives.html#2901" class="Bound">A</a> <a id="2903" href="Chapter.Logic.Connectives.html#2903" class="Bound">B</a> <a id="2905" class="Symbol">:</a> <a id="2907" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2910" class="Symbol">}</a> <a id="2912" class="Symbol">-&gt;</a> <a id="2915" href="Chapter.Logic.Connectives.html#2901" class="Bound">A</a> <a id="2917" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="2919" href="Chapter.Logic.Connectives.html#2903" class="Bound">B</a> <a id="2921" class="Symbol">-&gt;</a> <a id="2924" href="Chapter.Logic.Connectives.html#2903" class="Bound">B</a>
<a id="2926" href="Chapter.Logic.Connectives.html#2893" class="Function">snd</a> <a id="2930" class="Symbol">(_</a> <a id="2933" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="2935" href="Chapter.Logic.Connectives.html#2935" class="Bound">y</a><a id="2936" class="Symbol">)</a> <a id="2938" class="Symbol">=</a> <a id="2940" href="Chapter.Logic.Connectives.html#2935" class="Bound">y</a>
</pre>
Note that `fst` and `snd` are also proofs of two well-known theorems
about conjunctions: if `A × B` is true, then `A` is true (`fst`) and
`B` is true (`snd`).

By combining conjunction (given by the data type `×`) and
implication (given by the native Agda's arrow type `->`) we can also
model double implication, commonly known as "if and only if".

<pre class="Agda"><a id="_⇔_"></a><a id="3301" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">_⇔_</a> <a id="3305" class="Symbol">:</a> <a id="3307" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3311" class="Symbol">-&gt;</a> <a id="3314" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3318" class="Symbol">-&gt;</a> <a id="3321" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="3325" href="Chapter.Logic.Connectives.html#3325" class="Bound">A</a> <a id="3327" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="3329" href="Chapter.Logic.Connectives.html#3329" class="Bound">B</a> <a id="3331" class="Symbol">=</a> <a id="3333" class="Symbol">(</a><a id="3334" href="Chapter.Logic.Connectives.html#3325" class="Bound">A</a> <a id="3336" class="Symbol">-&gt;</a> <a id="3339" href="Chapter.Logic.Connectives.html#3329" class="Bound">B</a><a id="3340" class="Symbol">)</a> <a id="3342" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="3344" class="Symbol">(</a><a id="3345" href="Chapter.Logic.Connectives.html#3329" class="Bound">B</a> <a id="3347" class="Symbol">-&gt;</a> <a id="3350" href="Chapter.Logic.Connectives.html#3325" class="Bound">A</a><a id="3351" class="Symbol">)</a>
</pre>
<!--
<pre class="Agda"><a id="3367" class="Keyword">infixr</a> <a id="3374" class="Number">1</a> <a id="3376" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">_⇔_</a>
</pre>-->

## Disjunction

In constructive logic, a proof of *`A` or `B`* is either a proof of
`A` or a proof of `B` together with an indication of which proof we
are providing. This interpretation suggests the representation of
disjunction `⊎` as a data type with two constructors, one taking a
proof of `A` and the other taking a proof of `B`, to yield a proof
of `A ⊎ B`. The name of the constructor indicates which of the two
proofs is provided. We call the two constructors `inj₁` and `inj₂` for
"inject left" and "inject right".

<pre class="Agda"><a id="3918" class="Keyword">data</a> <a id="_⊎_"></a><a id="3923" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">_⊎_</a> <a id="3927" class="Symbol">(</a><a id="3928" href="Chapter.Logic.Connectives.html#3928" class="Bound">A</a> <a id="3930" href="Chapter.Logic.Connectives.html#3930" class="Bound">B</a> <a id="3932" class="Symbol">:</a> <a id="3934" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3937" class="Symbol">)</a> <a id="3939" class="Symbol">:</a> <a id="3941" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3945" class="Keyword">where</a>
  <a id="_⊎_.inj₁"></a><a id="3953" href="Chapter.Logic.Connectives.html#3953" class="InductiveConstructor">inj₁</a> <a id="3958" class="Symbol">:</a> <a id="3960" href="Chapter.Logic.Connectives.html#3928" class="Bound">A</a> <a id="3962" class="Symbol">-&gt;</a> <a id="3965" href="Chapter.Logic.Connectives.html#3928" class="Bound">A</a> <a id="3967" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="3969" href="Chapter.Logic.Connectives.html#3930" class="Bound">B</a>
  <a id="_⊎_.inj₂"></a><a id="3973" href="Chapter.Logic.Connectives.html#3973" class="InductiveConstructor">inj₂</a> <a id="3978" class="Symbol">:</a> <a id="3980" href="Chapter.Logic.Connectives.html#3930" class="Bound">B</a> <a id="3982" class="Symbol">-&gt;</a> <a id="3985" href="Chapter.Logic.Connectives.html#3928" class="Bound">A</a> <a id="3987" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="3989" href="Chapter.Logic.Connectives.html#3930" class="Bound">B</a>
</pre>
We declare `⊎` as a right associative operator with smaller
precedence than `×`.

<pre class="Agda"><a id="4082" class="Keyword">infixr</a> <a id="4089" class="Number">2</a> <a id="4091" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">_⊎_</a>
</pre>
As for conjunctions, we will use case analysis on terms of type `A ⊎
B`. As an example, we can formulate the elimination principle for
disjunctions as the following function.

<pre class="Agda"><a id="⊎-elim"></a><a id="4280" href="Chapter.Logic.Connectives.html#4280" class="Function">⊎-elim</a> <a id="4287" class="Symbol">:</a> <a id="4289" class="Symbol">∀{</a><a id="4291" href="Chapter.Logic.Connectives.html#4291" class="Bound">A</a> <a id="4293" href="Chapter.Logic.Connectives.html#4293" class="Bound">B</a> <a id="4295" href="Chapter.Logic.Connectives.html#4295" class="Bound">C</a> <a id="4297" class="Symbol">:</a> <a id="4299" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4302" class="Symbol">}</a> <a id="4304" class="Symbol">-&gt;</a> <a id="4307" class="Symbol">(</a><a id="4308" href="Chapter.Logic.Connectives.html#4291" class="Bound">A</a> <a id="4310" class="Symbol">-&gt;</a> <a id="4313" href="Chapter.Logic.Connectives.html#4295" class="Bound">C</a><a id="4314" class="Symbol">)</a> <a id="4316" class="Symbol">-&gt;</a> <a id="4319" class="Symbol">(</a><a id="4320" href="Chapter.Logic.Connectives.html#4293" class="Bound">B</a> <a id="4322" class="Symbol">-&gt;</a> <a id="4325" href="Chapter.Logic.Connectives.html#4295" class="Bound">C</a><a id="4326" class="Symbol">)</a> <a id="4328" class="Symbol">-&gt;</a> <a id="4331" href="Chapter.Logic.Connectives.html#4291" class="Bound">A</a> <a id="4333" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="4335" href="Chapter.Logic.Connectives.html#4293" class="Bound">B</a> <a id="4337" class="Symbol">-&gt;</a> <a id="4340" href="Chapter.Logic.Connectives.html#4295" class="Bound">C</a>
<a id="4342" href="Chapter.Logic.Connectives.html#4280" class="Function">⊎-elim</a> <a id="4349" href="Chapter.Logic.Connectives.html#4349" class="Bound">f</a> <a id="4351" href="Chapter.Logic.Connectives.html#4351" class="Bound">g</a> <a id="4353" class="Symbol">(</a><a id="4354" href="Chapter.Logic.Connectives.html#3953" class="InductiveConstructor">inj₁</a> <a id="4359" href="Chapter.Logic.Connectives.html#4359" class="Bound">x</a><a id="4360" class="Symbol">)</a> <a id="4362" class="Symbol">=</a> <a id="4364" href="Chapter.Logic.Connectives.html#4349" class="Bound">f</a> <a id="4366" href="Chapter.Logic.Connectives.html#4359" class="Bound">x</a>
<a id="4368" href="Chapter.Logic.Connectives.html#4280" class="Function">⊎-elim</a> <a id="4375" href="Chapter.Logic.Connectives.html#4375" class="Bound">f</a> <a id="4377" href="Chapter.Logic.Connectives.html#4377" class="Bound">g</a> <a id="4379" class="Symbol">(</a><a id="4380" href="Chapter.Logic.Connectives.html#3973" class="InductiveConstructor">inj₂</a> <a id="4385" href="Chapter.Logic.Connectives.html#4385" class="Bound">x</a><a id="4386" class="Symbol">)</a> <a id="4388" class="Symbol">=</a> <a id="4390" href="Chapter.Logic.Connectives.html#4377" class="Bound">g</a> <a id="4392" href="Chapter.Logic.Connectives.html#4385" class="Bound">x</a>
</pre>
For instance, we can use `⊎-elim` to prove that disjunction is
commutative:

<pre class="Agda"><a id="⊎-comm"></a><a id="4480" href="Chapter.Logic.Connectives.html#4480" class="Function">⊎-comm</a> <a id="4487" class="Symbol">:</a> <a id="4489" class="Symbol">∀{</a><a id="4491" href="Chapter.Logic.Connectives.html#4491" class="Bound">A</a> <a id="4493" href="Chapter.Logic.Connectives.html#4493" class="Bound">B</a> <a id="4495" class="Symbol">:</a> <a id="4497" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4500" class="Symbol">}</a> <a id="4502" class="Symbol">-&gt;</a> <a id="4505" href="Chapter.Logic.Connectives.html#4491" class="Bound">A</a> <a id="4507" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="4509" href="Chapter.Logic.Connectives.html#4493" class="Bound">B</a> <a id="4511" class="Symbol">-&gt;</a> <a id="4514" href="Chapter.Logic.Connectives.html#4493" class="Bound">B</a> <a id="4516" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="4518" href="Chapter.Logic.Connectives.html#4491" class="Bound">A</a>
<a id="4520" href="Chapter.Logic.Connectives.html#4480" class="Function">⊎-comm</a> <a id="4527" class="Symbol">=</a> <a id="4529" href="Chapter.Logic.Connectives.html#4280" class="Function">⊎-elim</a> <a id="4536" href="Chapter.Logic.Connectives.html#3973" class="InductiveConstructor">inj₂</a> <a id="4541" href="Chapter.Logic.Connectives.html#3953" class="InductiveConstructor">inj₁</a>
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

<pre class="Agda"><a id="ex-falso"></a><a id="5223" href="Chapter.Logic.Connectives.html#5223" class="Function">ex-falso</a> <a id="5232" class="Symbol">:</a> <a id="5234" class="Symbol">∀{</a><a id="5236" href="Chapter.Logic.Connectives.html#5236" class="Bound">A</a> <a id="5238" class="Symbol">:</a> <a id="5240" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5243" class="Symbol">}</a> <a id="5245" class="Symbol">-&gt;</a> <a id="5248" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a> <a id="5250" class="Symbol">-&gt;</a> <a id="5253" href="Chapter.Logic.Connectives.html#5236" class="Bound">A</a>
<a id="5255" href="Chapter.Logic.Connectives.html#5223" class="Function">ex-falso</a> <a id="5264" class="Symbol">()</a>
</pre>
The pattern `()` in the definition of `ex-falso` matches an
hypothetical value of type `⊥`. Since no constructor is provided for
`⊥` and no such value may exist, the equation *has no right hand
side* (note that there is no equal sign) and we are not obliged to
provide a proof of `A` as required by the codomain of `ex-falso`.

In other programming languages that are capable of defining a data
type analogous to `⊥` it is possible to assign the type `⊥` to
non-terminating expressions. If this were allowed also in Agda, the
whole language would be useless insofar program verification is
concerned, since `ex-falso` would easily allow us to prove *any*
property about *any* program. For this reason, Agda has a
*termination checker* making sure that every definition is
*terminating*. For example, if define `loop` as follows

<!--
<pre class="Agda"><a id="6110" class="Symbol">{-#</a> <a id="6114" class="Keyword">TERMINATING</a> <a id="6126" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="loop"></a><a id="6142" href="Chapter.Logic.Connectives.html#6142" class="Function">loop</a> <a id="6147" class="Symbol">:</a> <a id="6149" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6151" class="Symbol">-&gt;</a> <a id="6154" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a>
<a id="6156" href="Chapter.Logic.Connectives.html#6142" class="Function">loop</a> <a id="6161" href="Chapter.Logic.Connectives.html#6161" class="Bound">n</a> <a id="6163" class="Symbol">=</a> <a id="6165" href="Chapter.Logic.Connectives.html#6142" class="Function">loop</a> <a id="6170" class="Symbol">(</a><a id="6171" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="6175" href="Chapter.Logic.Connectives.html#6161" class="Bound">n</a><a id="6176" class="Symbol">)</a>
</pre>
Agda reports that this definition does not pass the termination
check. Indeed, `loop` is recursively applied to increasingly larger
arguments. An even simpler example of non-terminating definition is
`bottom`, shown below.

<!--
<pre class="Agda"><a id="6416" class="Symbol">{-#</a> <a id="6420" class="Keyword">TERMINATING</a> <a id="6432" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="bottom"></a><a id="6448" href="Chapter.Logic.Connectives.html#6448" class="Function">bottom</a> <a id="6455" class="Symbol">:</a> <a id="6457" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a>
<a id="6459" href="Chapter.Logic.Connectives.html#6448" class="Function">bottom</a> <a id="6466" class="Symbol">=</a> <a id="6468" href="Chapter.Logic.Connectives.html#6448" class="Function">bottom</a>
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
   `×-comm : ∀{A B : Set} -> A × B -> B × A`.
2. Prove that `×` and `⊎` are idempotent, namely the theorems
   `×-idem : ∀{A : Set} -> A × A ⇔ A` and `⊎-idem : ∀{A : Set} -> A
   ⊎ A ⇔ A`.
3. Prove that `×` distributes over `⊎` on the left, namely the
   theorem `×⊎-dist : ∀{A B C : Set} -> A × (B ⊎ C) ⇔ (A × B) ⊎ (A ×
   C)`.
4. Prove that `⊤` is the unit of conjuction, namely the theorems
   `×-unit-l : ∀{A : Set} -> ⊤ × A ⇔ A` and `×-unit-r : ∀{A : Set}
   -> A × ⊤ ⇔ A`.
5. Prove that `⊤` absorbs disjunctions, namely the theorems `⊎-⊤-l :
   ∀{A : Set} -> ⊤ ⊎ A ⇔ ⊤` and `⊎-⊤-r : ∀{A : Set} -> A ⊎ ⊤ ⇔ ⊤`.
6. Prove that `⊥` is the unit of disjunctions, namely the theorems
   `⊎-unit-l : ∀{A : Set} -> ⊥ ⊎ A ⇔ A` and `⊎-unit-r : ∀{A : Set}
   -> A ⊎ ⊥ ⇔ A`.
7. Prove that `⊥` absorbs conjunctions, namely the theorems `×-⊥-l :
   ∀{A : Set} -> ⊥ × A ⇔ ⊥` and `×-⊥-r : ∀{A : Set} -> A × ⊥ ⇔ ⊥`.
8. Prove that every boolean value is either `true` or `false`,
   namely the theorem `Bool-⊎ : ∀(b : Bool) -> (b ≡ true) ⊎ (b ≡
   false)`.

<pre class="Agda"><a id="8141" class="Comment">-- EXERCISE 1</a>
<a id="×-comm"></a><a id="8155" href="Chapter.Logic.Connectives.html#8155" class="Function">×-comm</a> <a id="8162" class="Symbol">:</a> <a id="8164" class="Symbol">∀{</a><a id="8166" href="Chapter.Logic.Connectives.html#8166" class="Bound">A</a> <a id="8168" href="Chapter.Logic.Connectives.html#8168" class="Bound">B</a> <a id="8170" class="Symbol">:</a> <a id="8172" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8175" class="Symbol">}</a> <a id="8177" class="Symbol">-&gt;</a> <a id="8180" href="Chapter.Logic.Connectives.html#8166" class="Bound">A</a> <a id="8182" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="8184" href="Chapter.Logic.Connectives.html#8168" class="Bound">B</a> <a id="8186" class="Symbol">-&gt;</a> <a id="8189" href="Chapter.Logic.Connectives.html#8168" class="Bound">B</a> <a id="8191" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="8193" href="Chapter.Logic.Connectives.html#8166" class="Bound">A</a>
<a id="8195" href="Chapter.Logic.Connectives.html#8155" class="Function">×-comm</a> <a id="8202" class="Symbol">(</a><a id="8203" href="Chapter.Logic.Connectives.html#8203" class="Bound">x</a> <a id="8205" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8207" href="Chapter.Logic.Connectives.html#8207" class="Bound">y</a><a id="8208" class="Symbol">)</a> <a id="8210" class="Symbol">=</a> <a id="8212" href="Chapter.Logic.Connectives.html#8207" class="Bound">y</a> <a id="8214" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8216" href="Chapter.Logic.Connectives.html#8203" class="Bound">x</a>

<a id="8219" class="Comment">-- EXERCISE 2</a>
<a id="×-idem"></a><a id="8233" href="Chapter.Logic.Connectives.html#8233" class="Function">×-idem</a> <a id="8240" class="Symbol">:</a> <a id="8242" class="Symbol">∀{</a><a id="8244" href="Chapter.Logic.Connectives.html#8244" class="Bound">A</a> <a id="8246" class="Symbol">:</a> <a id="8248" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8251" class="Symbol">}</a> <a id="8253" class="Symbol">-&gt;</a> <a id="8256" href="Chapter.Logic.Connectives.html#8244" class="Bound">A</a> <a id="8258" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="8260" href="Chapter.Logic.Connectives.html#8244" class="Bound">A</a> <a id="8262" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="8264" href="Chapter.Logic.Connectives.html#8244" class="Bound">A</a>
<a id="8266" href="Chapter.Logic.Connectives.html#8233" class="Function">×-idem</a> <a id="8273" class="Symbol">=</a> <a id="8275" href="Chapter.Logic.Connectives.html#2843" class="Function">fst</a> <a id="8279" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8281" class="Symbol">λ</a> <a id="8283" href="Chapter.Logic.Connectives.html#8283" class="Bound">x</a> <a id="8285" class="Symbol">-&gt;</a> <a id="8288" class="Symbol">(</a><a id="8289" href="Chapter.Logic.Connectives.html#8283" class="Bound">x</a> <a id="8291" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8293" href="Chapter.Logic.Connectives.html#8283" class="Bound">x</a><a id="8294" class="Symbol">)</a>

<a id="⊎-idem"></a><a id="8297" href="Chapter.Logic.Connectives.html#8297" class="Function">⊎-idem</a> <a id="8304" class="Symbol">:</a> <a id="8306" class="Symbol">∀{</a><a id="8308" href="Chapter.Logic.Connectives.html#8308" class="Bound">A</a> <a id="8310" class="Symbol">:</a> <a id="8312" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8315" class="Symbol">}</a> <a id="8317" class="Symbol">-&gt;</a> <a id="8320" href="Chapter.Logic.Connectives.html#8308" class="Bound">A</a> <a id="8322" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="8324" href="Chapter.Logic.Connectives.html#8308" class="Bound">A</a> <a id="8326" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="8328" href="Chapter.Logic.Connectives.html#8308" class="Bound">A</a>
<a id="8330" href="Chapter.Logic.Connectives.html#8297" class="Function">⊎-idem</a> <a id="8337" class="Symbol">=</a> <a id="8339" href="Chapter.Logic.Connectives.html#4280" class="Function">⊎-elim</a> <a id="8346" href="Function.Base.html#704" class="Function">id</a> <a id="8349" href="Function.Base.html#704" class="Function">id</a> <a id="8352" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8354" href="Chapter.Logic.Connectives.html#3953" class="InductiveConstructor">inj₁</a>

<a id="8360" class="Comment">-- EXERCISE 3</a>
<a id="×⊎-dist"></a><a id="8374" href="Chapter.Logic.Connectives.html#8374" class="Function">×⊎-dist</a> <a id="8382" class="Symbol">:</a> <a id="8384" class="Symbol">∀{</a><a id="8386" href="Chapter.Logic.Connectives.html#8386" class="Bound">A</a> <a id="8388" href="Chapter.Logic.Connectives.html#8388" class="Bound">B</a> <a id="8390" href="Chapter.Logic.Connectives.html#8390" class="Bound">C</a> <a id="8392" class="Symbol">:</a> <a id="8394" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8397" class="Symbol">}</a> <a id="8399" class="Symbol">-&gt;</a> <a id="8402" href="Chapter.Logic.Connectives.html#8386" class="Bound">A</a> <a id="8404" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="8406" class="Symbol">(</a><a id="8407" href="Chapter.Logic.Connectives.html#8388" class="Bound">B</a> <a id="8409" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="8411" href="Chapter.Logic.Connectives.html#8390" class="Bound">C</a><a id="8412" class="Symbol">)</a> <a id="8414" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="8416" class="Symbol">(</a><a id="8417" href="Chapter.Logic.Connectives.html#8386" class="Bound">A</a> <a id="8419" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="8421" href="Chapter.Logic.Connectives.html#8388" class="Bound">B</a><a id="8422" class="Symbol">)</a> <a id="8424" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="8426" class="Symbol">(</a><a id="8427" href="Chapter.Logic.Connectives.html#8386" class="Bound">A</a> <a id="8429" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="8431" href="Chapter.Logic.Connectives.html#8390" class="Bound">C</a><a id="8432" class="Symbol">)</a>
<a id="8434" href="Chapter.Logic.Connectives.html#8374" class="Function">×⊎-dist</a> <a id="8442" class="Symbol">=</a>
  <a id="8446" class="Symbol">(λ</a> <a id="8449" href="Chapter.Logic.Connectives.html#8449" class="Bound">p</a> <a id="8451" class="Symbol">-&gt;</a> <a id="8454" href="Chapter.Logic.Connectives.html#4280" class="Function">⊎-elim</a> <a id="8461" class="Symbol">(</a><a id="8462" href="Chapter.Logic.Connectives.html#3953" class="InductiveConstructor">inj₁</a> <a id="8467" href="Function.Base.html#1134" class="Function Operator">∘</a> <a id="8469" class="Symbol">(</a><a id="8470" href="Chapter.Logic.Connectives.html#2843" class="Function">fst</a> <a id="8474" href="Chapter.Logic.Connectives.html#8449" class="Bound">p</a> <a id="8476" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,_</a><a id="8478" class="Symbol">))</a> <a id="8481" class="Symbol">(</a><a id="8482" href="Chapter.Logic.Connectives.html#3973" class="InductiveConstructor">inj₂</a> <a id="8487" href="Function.Base.html#1134" class="Function Operator">∘</a> <a id="8489" class="Symbol">(</a><a id="8490" href="Chapter.Logic.Connectives.html#2843" class="Function">fst</a> <a id="8494" href="Chapter.Logic.Connectives.html#8449" class="Bound">p</a> <a id="8496" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,_</a><a id="8498" class="Symbol">))</a> <a id="8501" class="Symbol">(</a><a id="8502" href="Chapter.Logic.Connectives.html#2893" class="Function">snd</a> <a id="8506" href="Chapter.Logic.Connectives.html#8449" class="Bound">p</a><a id="8507" class="Symbol">))</a> <a id="8510" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a>
  <a id="8514" href="Chapter.Logic.Connectives.html#4280" class="Function">⊎-elim</a> <a id="8521" class="Symbol">(λ</a> <a id="8524" href="Chapter.Logic.Connectives.html#8524" class="Bound">p</a> <a id="8526" class="Symbol">-&gt;</a> <a id="8529" href="Chapter.Logic.Connectives.html#2843" class="Function">fst</a> <a id="8533" href="Chapter.Logic.Connectives.html#8524" class="Bound">p</a> <a id="8535" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8537" href="Chapter.Logic.Connectives.html#3953" class="InductiveConstructor">inj₁</a> <a id="8542" class="Symbol">(</a><a id="8543" href="Chapter.Logic.Connectives.html#2893" class="Function">snd</a> <a id="8547" href="Chapter.Logic.Connectives.html#8524" class="Bound">p</a><a id="8548" class="Symbol">))</a> <a id="8551" class="Symbol">(λ</a> <a id="8554" href="Chapter.Logic.Connectives.html#8554" class="Bound">p</a> <a id="8556" class="Symbol">-&gt;</a> <a id="8559" href="Chapter.Logic.Connectives.html#2843" class="Function">fst</a> <a id="8563" href="Chapter.Logic.Connectives.html#8554" class="Bound">p</a> <a id="8565" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8567" href="Chapter.Logic.Connectives.html#3973" class="InductiveConstructor">inj₂</a> <a id="8572" class="Symbol">(</a><a id="8573" href="Chapter.Logic.Connectives.html#2893" class="Function">snd</a> <a id="8577" href="Chapter.Logic.Connectives.html#8554" class="Bound">p</a><a id="8578" class="Symbol">))</a>

<a id="8582" class="Comment">-- EXERCISE 4</a>
<a id="×-unit-l"></a><a id="8596" href="Chapter.Logic.Connectives.html#8596" class="Function">×-unit-l</a> <a id="8605" class="Symbol">:</a> <a id="8607" class="Symbol">∀{</a><a id="8609" href="Chapter.Logic.Connectives.html#8609" class="Bound">A</a> <a id="8611" class="Symbol">:</a> <a id="8613" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8616" class="Symbol">}</a> <a id="8618" class="Symbol">-&gt;</a> <a id="8621" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a> <a id="8623" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="8625" href="Chapter.Logic.Connectives.html#8609" class="Bound">A</a> <a id="8627" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="8629" href="Chapter.Logic.Connectives.html#8609" class="Bound">A</a>
<a id="8631" href="Chapter.Logic.Connectives.html#8596" class="Function">×-unit-l</a> <a id="8640" class="Symbol">=</a> <a id="8642" href="Chapter.Logic.Connectives.html#2893" class="Function">snd</a> <a id="8646" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8648" class="Symbol">(</a><a id="8649" href="Chapter.Logic.Connectives.html#4779" class="InductiveConstructor">tt</a> <a id="8652" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,_</a><a id="8654" class="Symbol">)</a>

<a id="×-unit-r"></a><a id="8657" href="Chapter.Logic.Connectives.html#8657" class="Function">×-unit-r</a> <a id="8666" class="Symbol">:</a> <a id="8668" class="Symbol">∀{</a><a id="8670" href="Chapter.Logic.Connectives.html#8670" class="Bound">A</a> <a id="8672" class="Symbol">:</a> <a id="8674" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8677" class="Symbol">}</a> <a id="8679" class="Symbol">-&gt;</a> <a id="8682" href="Chapter.Logic.Connectives.html#8670" class="Bound">A</a> <a id="8684" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="8686" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a> <a id="8688" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="8690" href="Chapter.Logic.Connectives.html#8670" class="Bound">A</a>
<a id="8692" href="Chapter.Logic.Connectives.html#8657" class="Function">×-unit-r</a> <a id="8701" class="Symbol">=</a> <a id="8703" href="Chapter.Logic.Connectives.html#2843" class="Function">fst</a> <a id="8707" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8709" class="Symbol">(</a><a id="8710" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">_,</a> <a id="8713" href="Chapter.Logic.Connectives.html#4779" class="InductiveConstructor">tt</a><a id="8715" class="Symbol">)</a>

<a id="8718" class="Comment">-- EXERCISE 5</a>
<a id="⊎-unit-l"></a><a id="8732" href="Chapter.Logic.Connectives.html#8732" class="Function">⊎-unit-l</a> <a id="8741" class="Symbol">:</a> <a id="8743" class="Symbol">∀{</a><a id="8745" href="Chapter.Logic.Connectives.html#8745" class="Bound">A</a> <a id="8747" class="Symbol">:</a> <a id="8749" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8752" class="Symbol">}</a> <a id="8754" class="Symbol">-&gt;</a> <a id="8757" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a> <a id="8759" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="8761" href="Chapter.Logic.Connectives.html#8745" class="Bound">A</a> <a id="8763" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="8765" href="Chapter.Logic.Connectives.html#8745" class="Bound">A</a>
<a id="8767" href="Chapter.Logic.Connectives.html#8732" class="Function">⊎-unit-l</a> <a id="8776" class="Symbol">=</a> <a id="8778" href="Chapter.Logic.Connectives.html#4280" class="Function">⊎-elim</a> <a id="8785" href="Chapter.Logic.Connectives.html#5223" class="Function">ex-falso</a> <a id="8794" href="Function.Base.html#704" class="Function">id</a> <a id="8797" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8799" href="Chapter.Logic.Connectives.html#3973" class="InductiveConstructor">inj₂</a>

<a id="⊎-unit-r"></a><a id="8805" href="Chapter.Logic.Connectives.html#8805" class="Function">⊎-unit-r</a> <a id="8814" class="Symbol">:</a> <a id="8816" class="Symbol">∀{</a><a id="8818" href="Chapter.Logic.Connectives.html#8818" class="Bound">A</a> <a id="8820" class="Symbol">:</a> <a id="8822" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8825" class="Symbol">}</a> <a id="8827" class="Symbol">-&gt;</a> <a id="8830" href="Chapter.Logic.Connectives.html#8818" class="Bound">A</a> <a id="8832" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="8834" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a> <a id="8836" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="8838" href="Chapter.Logic.Connectives.html#8818" class="Bound">A</a>
<a id="8840" href="Chapter.Logic.Connectives.html#8805" class="Function">⊎-unit-r</a> <a id="8849" class="Symbol">=</a> <a id="8851" href="Chapter.Logic.Connectives.html#4280" class="Function">⊎-elim</a> <a id="8858" href="Function.Base.html#704" class="Function">id</a> <a id="8861" href="Chapter.Logic.Connectives.html#5223" class="Function">ex-falso</a> <a id="8870" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8872" href="Chapter.Logic.Connectives.html#3953" class="InductiveConstructor">inj₁</a>

<a id="8878" class="Comment">-- EXERCISE 6</a>
<a id="⊎-⊤-l"></a><a id="8892" href="Chapter.Logic.Connectives.html#8892" class="Function">⊎-⊤-l</a> <a id="8898" class="Symbol">:</a> <a id="8900" class="Symbol">∀{</a><a id="8902" href="Chapter.Logic.Connectives.html#8902" class="Bound">A</a> <a id="8904" class="Symbol">:</a> <a id="8906" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8909" class="Symbol">}</a> <a id="8911" class="Symbol">-&gt;</a> <a id="8914" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a> <a id="8916" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="8918" href="Chapter.Logic.Connectives.html#8902" class="Bound">A</a> <a id="8920" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="8922" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a>
<a id="8924" href="Chapter.Logic.Connectives.html#8892" class="Function">⊎-⊤-l</a> <a id="8930" class="Symbol">=</a> <a id="8932" href="Function.Base.html#725" class="Function">const</a> <a id="8938" href="Chapter.Logic.Connectives.html#4779" class="InductiveConstructor">tt</a> <a id="8941" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="8943" href="Chapter.Logic.Connectives.html#3953" class="InductiveConstructor">inj₁</a>

<a id="⊎-⊤-r"></a><a id="8949" href="Chapter.Logic.Connectives.html#8949" class="Function">⊎-⊤-r</a> <a id="8955" class="Symbol">:</a> <a id="8957" class="Symbol">∀{</a><a id="8959" href="Chapter.Logic.Connectives.html#8959" class="Bound">A</a> <a id="8961" class="Symbol">:</a> <a id="8963" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8966" class="Symbol">}</a> <a id="8968" class="Symbol">-&gt;</a> <a id="8971" href="Chapter.Logic.Connectives.html#8959" class="Bound">A</a> <a id="8973" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="8975" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a> <a id="8977" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="8979" href="Chapter.Logic.Connectives.html#4763" class="Datatype">⊤</a>
<a id="8981" href="Chapter.Logic.Connectives.html#8949" class="Function">⊎-⊤-r</a> <a id="8987" class="Symbol">=</a> <a id="8989" href="Function.Base.html#725" class="Function">const</a> <a id="8995" href="Chapter.Logic.Connectives.html#4779" class="InductiveConstructor">tt</a> <a id="8998" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="9000" href="Chapter.Logic.Connectives.html#3973" class="InductiveConstructor">inj₂</a>

<a id="9006" class="Comment">-- EXERCISE 7</a>
<a id="×-⊥-l"></a><a id="9020" href="Chapter.Logic.Connectives.html#9020" class="Function">×-⊥-l</a> <a id="9026" class="Symbol">:</a> <a id="9028" class="Symbol">∀{</a><a id="9030" href="Chapter.Logic.Connectives.html#9030" class="Bound">A</a> <a id="9032" class="Symbol">:</a> <a id="9034" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="9037" class="Symbol">}</a> <a id="9039" class="Symbol">-&gt;</a> <a id="9042" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a> <a id="9044" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="9046" href="Chapter.Logic.Connectives.html#9030" class="Bound">A</a> <a id="9048" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="9050" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a>
<a id="9052" href="Chapter.Logic.Connectives.html#9020" class="Function">×-⊥-l</a> <a id="9058" class="Symbol">=</a> <a id="9060" href="Chapter.Logic.Connectives.html#2843" class="Function">fst</a> <a id="9064" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="9066" href="Chapter.Logic.Connectives.html#5223" class="Function">ex-falso</a>

<a id="×-⊥-r"></a><a id="9076" href="Chapter.Logic.Connectives.html#9076" class="Function">×-⊥-r</a> <a id="9082" class="Symbol">:</a> <a id="9084" class="Symbol">∀{</a><a id="9086" href="Chapter.Logic.Connectives.html#9086" class="Bound">A</a> <a id="9088" class="Symbol">:</a> <a id="9090" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="9093" class="Symbol">}</a> <a id="9095" class="Symbol">-&gt;</a> <a id="9098" href="Chapter.Logic.Connectives.html#9086" class="Bound">A</a> <a id="9100" href="Chapter.Logic.Connectives.html#1864" class="Datatype Operator">×</a> <a id="9102" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a> <a id="9104" href="Chapter.Logic.Connectives.html#3301" class="Function Operator">⇔</a> <a id="9106" href="Chapter.Logic.Connectives.html#4934" class="Datatype">⊥</a>
<a id="9108" href="Chapter.Logic.Connectives.html#9076" class="Function">×-⊥-r</a> <a id="9114" class="Symbol">=</a> <a id="9116" href="Chapter.Logic.Connectives.html#2893" class="Function">snd</a> <a id="9120" href="Chapter.Logic.Connectives.html#1894" class="InductiveConstructor Operator">,</a> <a id="9122" href="Chapter.Logic.Connectives.html#5223" class="Function">ex-falso</a>

<a id="9132" class="Comment">-- EXERCISE 8</a>
<a id="Bool-⊎"></a><a id="9146" href="Chapter.Logic.Connectives.html#9146" class="Function">Bool-⊎</a> <a id="9153" class="Symbol">:</a> <a id="9155" class="Symbol">∀(</a><a id="9157" href="Chapter.Logic.Connectives.html#9157" class="Bound">b</a> <a id="9159" class="Symbol">:</a> <a id="9161" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="9165" class="Symbol">)</a> <a id="9167" class="Symbol">-&gt;</a> <a id="9170" class="Symbol">(</a><a id="9171" href="Chapter.Logic.Connectives.html#9157" class="Bound">b</a> <a id="9173" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9175" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a><a id="9179" class="Symbol">)</a> <a id="9181" href="Chapter.Logic.Connectives.html#3923" class="Datatype Operator">⊎</a> <a id="9183" class="Symbol">(</a><a id="9184" href="Chapter.Logic.Connectives.html#9157" class="Bound">b</a> <a id="9186" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9188" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a><a id="9193" class="Symbol">)</a>
<a id="9195" href="Chapter.Logic.Connectives.html#9146" class="Function">Bool-⊎</a> <a id="9202" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="9208" class="Symbol">=</a> <a id="9210" href="Chapter.Logic.Connectives.html#3953" class="InductiveConstructor">inj₁</a> <a id="9215" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="9220" href="Chapter.Logic.Connectives.html#9146" class="Function">Bool-⊎</a> <a id="9227" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="9233" class="Symbol">=</a> <a id="9235" href="Chapter.Logic.Connectives.html#3973" class="InductiveConstructor">inj₂</a> <a id="9240" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

</pre>{:.solution}
