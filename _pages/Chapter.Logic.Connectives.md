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
<!--
<pre class="Agda"><a id="3354" class="Keyword">infixr</a> <a id="3361" class="Number">1</a> <a id="3363" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">_⇔_</a>
</pre>-→

## Disjunction

In constructive logic, a proof of *`A` or `B`* is either a proof of
`A` or a proof of `B` together with an indication of which proof we
are providing. This interpretation suggests the representation of
disjunction `⊎` as a data type with two constructors, one taking a
proof of `A` and the other taking a proof of `B`, to yield a proof
of `A ⊎ B`. The name of the constructor indicates which of the two
proofs is provided. We call the two constructors `inj₁` and `inj₂` for
"inject left" and "inject right".

<pre class="Agda"><a id="3904" class="Keyword">data</a> <a id="_⊎_"></a><a id="3909" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">_⊎_</a> <a id="3913" class="Symbol">(</a><a id="3914" href="Chapter.Logic.Connectives.html#3914" class="Bound">A</a> <a id="3916" href="Chapter.Logic.Connectives.html#3916" class="Bound">B</a> <a id="3918" class="Symbol">:</a> <a id="3920" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3923" class="Symbol">)</a> <a id="3925" class="Symbol">:</a> <a id="3927" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3931" class="Keyword">where</a>
  <a id="_⊎_.inj₁"></a><a id="3939" href="Chapter.Logic.Connectives.html#3939" class="InductiveConstructor">inj₁</a> <a id="3944" class="Symbol">:</a> <a id="3946" href="Chapter.Logic.Connectives.html#3914" class="Bound">A</a> <a id="3948" class="Symbol">→</a> <a id="3950" href="Chapter.Logic.Connectives.html#3914" class="Bound">A</a> <a id="3952" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="3954" href="Chapter.Logic.Connectives.html#3916" class="Bound">B</a>
  <a id="_⊎_.inj₂"></a><a id="3958" href="Chapter.Logic.Connectives.html#3958" class="InductiveConstructor">inj₂</a> <a id="3963" class="Symbol">:</a> <a id="3965" href="Chapter.Logic.Connectives.html#3916" class="Bound">B</a> <a id="3967" class="Symbol">→</a> <a id="3969" href="Chapter.Logic.Connectives.html#3914" class="Bound">A</a> <a id="3971" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="3973" href="Chapter.Logic.Connectives.html#3916" class="Bound">B</a>
</pre>
We declare `⊎` as a right associative operator with smaller
precedence than `×`.

<pre class="Agda"><a id="4066" class="Keyword">infixr</a> <a id="4073" class="Number">2</a> <a id="4075" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">_⊎_</a>
</pre>
As for conjunctions, we will use case analysis on terms of type `A ⊎
B`. As an example, we can formulate the elimination principle for
disjunctions as the following function.

<pre class="Agda"><a id="⊎-elim"></a><a id="4264" href="Chapter.Logic.Connectives.html#4264" class="Function">⊎-elim</a> <a id="4271" class="Symbol">:</a> <a id="4273" class="Symbol">∀{</a><a id="4275" href="Chapter.Logic.Connectives.html#4275" class="Bound">A</a> <a id="4277" href="Chapter.Logic.Connectives.html#4277" class="Bound">B</a> <a id="4279" href="Chapter.Logic.Connectives.html#4279" class="Bound">C</a> <a id="4281" class="Symbol">:</a> <a id="4283" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4286" class="Symbol">}</a> <a id="4288" class="Symbol">→</a> <a id="4290" class="Symbol">(</a><a id="4291" href="Chapter.Logic.Connectives.html#4275" class="Bound">A</a> <a id="4293" class="Symbol">→</a> <a id="4295" href="Chapter.Logic.Connectives.html#4279" class="Bound">C</a><a id="4296" class="Symbol">)</a> <a id="4298" class="Symbol">→</a> <a id="4300" class="Symbol">(</a><a id="4301" href="Chapter.Logic.Connectives.html#4277" class="Bound">B</a> <a id="4303" class="Symbol">→</a> <a id="4305" href="Chapter.Logic.Connectives.html#4279" class="Bound">C</a><a id="4306" class="Symbol">)</a> <a id="4308" class="Symbol">→</a> <a id="4310" href="Chapter.Logic.Connectives.html#4275" class="Bound">A</a> <a id="4312" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="4314" href="Chapter.Logic.Connectives.html#4277" class="Bound">B</a> <a id="4316" class="Symbol">→</a> <a id="4318" href="Chapter.Logic.Connectives.html#4279" class="Bound">C</a>
<a id="4320" href="Chapter.Logic.Connectives.html#4264" class="Function">⊎-elim</a> <a id="4327" href="Chapter.Logic.Connectives.html#4327" class="Bound">f</a> <a id="4329" href="Chapter.Logic.Connectives.html#4329" class="Bound">g</a> <a id="4331" class="Symbol">(</a><a id="4332" href="Chapter.Logic.Connectives.html#3939" class="InductiveConstructor">inj₁</a> <a id="4337" href="Chapter.Logic.Connectives.html#4337" class="Bound">x</a><a id="4338" class="Symbol">)</a> <a id="4340" class="Symbol">=</a> <a id="4342" href="Chapter.Logic.Connectives.html#4327" class="Bound">f</a> <a id="4344" href="Chapter.Logic.Connectives.html#4337" class="Bound">x</a>
<a id="4346" href="Chapter.Logic.Connectives.html#4264" class="Function">⊎-elim</a> <a id="4353" href="Chapter.Logic.Connectives.html#4353" class="Bound">f</a> <a id="4355" href="Chapter.Logic.Connectives.html#4355" class="Bound">g</a> <a id="4357" class="Symbol">(</a><a id="4358" href="Chapter.Logic.Connectives.html#3958" class="InductiveConstructor">inj₂</a> <a id="4363" href="Chapter.Logic.Connectives.html#4363" class="Bound">x</a><a id="4364" class="Symbol">)</a> <a id="4366" class="Symbol">=</a> <a id="4368" href="Chapter.Logic.Connectives.html#4355" class="Bound">g</a> <a id="4370" href="Chapter.Logic.Connectives.html#4363" class="Bound">x</a>
</pre>
For instance, we can use `⊎-elim` to prove that disjunction is
commutative:

<pre class="Agda"><a id="⊎-comm"></a><a id="4458" href="Chapter.Logic.Connectives.html#4458" class="Function">⊎-comm</a> <a id="4465" class="Symbol">:</a> <a id="4467" class="Symbol">∀{</a><a id="4469" href="Chapter.Logic.Connectives.html#4469" class="Bound">A</a> <a id="4471" href="Chapter.Logic.Connectives.html#4471" class="Bound">B</a> <a id="4473" class="Symbol">:</a> <a id="4475" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4478" class="Symbol">}</a> <a id="4480" class="Symbol">→</a> <a id="4482" href="Chapter.Logic.Connectives.html#4469" class="Bound">A</a> <a id="4484" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="4486" href="Chapter.Logic.Connectives.html#4471" class="Bound">B</a> <a id="4488" class="Symbol">→</a> <a id="4490" href="Chapter.Logic.Connectives.html#4471" class="Bound">B</a> <a id="4492" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="4494" href="Chapter.Logic.Connectives.html#4469" class="Bound">A</a>
<a id="4496" href="Chapter.Logic.Connectives.html#4458" class="Function">⊎-comm</a> <a id="4503" class="Symbol">=</a> <a id="4505" href="Chapter.Logic.Connectives.html#4264" class="Function">⊎-elim</a> <a id="4512" href="Chapter.Logic.Connectives.html#3958" class="InductiveConstructor">inj₂</a> <a id="4517" href="Chapter.Logic.Connectives.html#3939" class="InductiveConstructor">inj₁</a>
</pre>
## Truth

The always true proposition `⊤` is represented as a data type with a
single constructor without arguments. That is, truth is a
proposition for which we can provide a proof without any effort.

<pre class="Agda"><a id="4734" class="Keyword">data</a> <a id="⊤"></a><a id="4739" href="Chapter.Logic.Connectives.html#4739" class="Datatype">⊤</a> <a id="4741" class="Symbol">:</a> <a id="4743" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="4747" class="Keyword">where</a>
  <a id="⊤.tt"></a><a id="4755" href="Chapter.Logic.Connectives.html#4755" class="InductiveConstructor">tt</a> <a id="4758" class="Symbol">:</a> <a id="4760" href="Chapter.Logic.Connectives.html#4739" class="Datatype">⊤</a>
</pre>
## Falsity

The always false proposition `⊥` must not be provable. As such, we
can represent it by a data type without constructors.

<pre class="Agda"><a id="4905" class="Keyword">data</a> <a id="⊥"></a><a id="4910" href="Chapter.Logic.Connectives.html#4910" class="Datatype">⊥</a> <a id="4912" class="Symbol">:</a> <a id="4914" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="4918" class="Keyword">where</a>
</pre>
The elimination principle for `⊥` is sometimes called *principle of
explosion* or *ex falso quodlibet*. It states that if it is possible
to prove `⊥`, then it is possible to prove anything. Stating this
principle in Agda requires the use of the **absurd pattern**.

<pre class="Agda"><a id="⊥-elim"></a><a id="5199" href="Chapter.Logic.Connectives.html#5199" class="Function">⊥-elim</a> <a id="5206" class="Symbol">:</a> <a id="5208" class="Symbol">∀{</a><a id="5210" href="Chapter.Logic.Connectives.html#5210" class="Bound">A</a> <a id="5212" class="Symbol">:</a> <a id="5214" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5217" class="Symbol">}</a> <a id="5219" class="Symbol">→</a> <a id="5221" href="Chapter.Logic.Connectives.html#4910" class="Datatype">⊥</a> <a id="5223" class="Symbol">→</a> <a id="5225" href="Chapter.Logic.Connectives.html#5210" class="Bound">A</a>
<a id="5227" href="Chapter.Logic.Connectives.html#5199" class="Function">⊥-elim</a> <a id="5234" class="Symbol">()</a>
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
<pre class="Agda"><a id="6074" class="Symbol">{-#</a> <a id="6078" class="Keyword">TERMINATING</a> <a id="6090" class="Symbol">#-}</a>
</pre>-→
<pre class="Agda"><a id="loop"></a><a id="6105" href="Chapter.Logic.Connectives.html#6105" class="Function">loop</a> <a id="6110" class="Symbol">:</a> <a id="6112" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="6114" class="Symbol">→</a> <a id="6116" href="Chapter.Logic.Connectives.html#4910" class="Datatype">⊥</a>
<a id="6118" href="Chapter.Logic.Connectives.html#6105" class="Function">loop</a> <a id="6123" href="Chapter.Logic.Connectives.html#6123" class="Bound">n</a> <a id="6125" class="Symbol">=</a> <a id="6127" href="Chapter.Logic.Connectives.html#6105" class="Function">loop</a> <a id="6132" class="Symbol">(</a><a id="6133" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="6137" href="Chapter.Logic.Connectives.html#6123" class="Bound">n</a><a id="6138" class="Symbol">)</a>
</pre>
Agda reports that this definition does not pass the termination
check. Indeed, `loop` is recursively applied to increasingly larger
arguments. An even simpler example of non-terminating definition is
`bottom`, shown below.

<!--
<pre class="Agda"><a id="6378" class="Symbol">{-#</a> <a id="6382" class="Keyword">TERMINATING</a> <a id="6394" class="Symbol">#-}</a>
</pre>-→
<pre class="Agda"><a id="bottom"></a><a id="6409" href="Chapter.Logic.Connectives.html#6409" class="Function">bottom</a> <a id="6416" class="Symbol">:</a> <a id="6418" href="Chapter.Logic.Connectives.html#4910" class="Datatype">⊥</a>
<a id="6420" href="Chapter.Logic.Connectives.html#6409" class="Function">bottom</a> <a id="6427" class="Symbol">=</a> <a id="6429" href="Chapter.Logic.Connectives.html#6409" class="Function">bottom</a>
</pre>
All the recursive functions we have defined until now are verified
by Agda to be *terminating* because there is an argument that
becomes *structurally smaller* from an application of the function
to its recursive invocation. Structural recursion applies to a large
family of functions, but some of them
<!--
(e.g. [division](Chapter.Fun.Division.html) or [quick
sort](Chapter.Fun.QuickSort.html))
-→
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

<pre class="Agda"><a id="8087" class="Comment">-- EXERCISE 1</a>
<a id="×-comm"></a><a id="8101" href="Chapter.Logic.Connectives.html#8101" class="Function">×-comm</a> <a id="8108" class="Symbol">:</a> <a id="8110" class="Symbol">∀{</a><a id="8112" href="Chapter.Logic.Connectives.html#8112" class="Bound">A</a> <a id="8114" href="Chapter.Logic.Connectives.html#8114" class="Bound">B</a> <a id="8116" class="Symbol">:</a> <a id="8118" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8121" class="Symbol">}</a> <a id="8123" class="Symbol">→</a> <a id="8125" href="Chapter.Logic.Connectives.html#8112" class="Bound">A</a> <a id="8127" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8129" href="Chapter.Logic.Connectives.html#8114" class="Bound">B</a> <a id="8131" class="Symbol">→</a> <a id="8133" href="Chapter.Logic.Connectives.html#8114" class="Bound">B</a> <a id="8135" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8137" href="Chapter.Logic.Connectives.html#8112" class="Bound">A</a>
<a id="8139" href="Chapter.Logic.Connectives.html#8101" class="Function">×-comm</a> <a id="8146" class="Symbol">(</a><a id="8147" href="Chapter.Logic.Connectives.html#8147" class="Bound">x</a> <a id="8149" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8151" href="Chapter.Logic.Connectives.html#8151" class="Bound">y</a><a id="8152" class="Symbol">)</a> <a id="8154" class="Symbol">=</a> <a id="8156" href="Chapter.Logic.Connectives.html#8151" class="Bound">y</a> <a id="8158" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8160" href="Chapter.Logic.Connectives.html#8147" class="Bound">x</a>

<a id="8163" class="Comment">-- EXERCISE 2</a>
<a id="×-idem"></a><a id="8177" href="Chapter.Logic.Connectives.html#8177" class="Function">×-idem</a> <a id="8184" class="Symbol">:</a> <a id="8186" class="Symbol">∀{</a><a id="8188" href="Chapter.Logic.Connectives.html#8188" class="Bound">A</a> <a id="8190" class="Symbol">:</a> <a id="8192" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8195" class="Symbol">}</a> <a id="8197" class="Symbol">→</a> <a id="8199" href="Chapter.Logic.Connectives.html#8188" class="Bound">A</a> <a id="8201" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8203" href="Chapter.Logic.Connectives.html#8188" class="Bound">A</a> <a id="8205" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8207" href="Chapter.Logic.Connectives.html#8188" class="Bound">A</a>
<a id="8209" href="Chapter.Logic.Connectives.html#8177" class="Function">×-idem</a> <a id="8216" class="Symbol">=</a> <a id="8218" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8222" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8224" class="Symbol">λ</a> <a id="8226" href="Chapter.Logic.Connectives.html#8226" class="Bound">x</a> <a id="8228" class="Symbol">→</a> <a id="8230" class="Symbol">(</a><a id="8231" href="Chapter.Logic.Connectives.html#8226" class="Bound">x</a> <a id="8233" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8235" href="Chapter.Logic.Connectives.html#8226" class="Bound">x</a><a id="8236" class="Symbol">)</a>

<a id="⊎-idem"></a><a id="8239" href="Chapter.Logic.Connectives.html#8239" class="Function">⊎-idem</a> <a id="8246" class="Symbol">:</a> <a id="8248" class="Symbol">∀{</a><a id="8250" href="Chapter.Logic.Connectives.html#8250" class="Bound">A</a> <a id="8252" class="Symbol">:</a> <a id="8254" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8257" class="Symbol">}</a> <a id="8259" class="Symbol">→</a> <a id="8261" href="Chapter.Logic.Connectives.html#8250" class="Bound">A</a> <a id="8263" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="8265" href="Chapter.Logic.Connectives.html#8250" class="Bound">A</a> <a id="8267" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8269" href="Chapter.Logic.Connectives.html#8250" class="Bound">A</a>
<a id="8271" href="Chapter.Logic.Connectives.html#8239" class="Function">⊎-idem</a> <a id="8278" class="Symbol">=</a> <a id="8280" href="Chapter.Logic.Connectives.html#4264" class="Function">⊎-elim</a> <a id="8287" href="Function.Base.html#704" class="Function">id</a> <a id="8290" href="Function.Base.html#704" class="Function">id</a> <a id="8293" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8295" href="Chapter.Logic.Connectives.html#3939" class="InductiveConstructor">inj₁</a>

<a id="8301" class="Comment">-- EXERCISE 3</a>
<a id="×⊎-dist"></a><a id="8315" href="Chapter.Logic.Connectives.html#8315" class="Function">×⊎-dist</a> <a id="8323" class="Symbol">:</a> <a id="8325" class="Symbol">∀{</a><a id="8327" href="Chapter.Logic.Connectives.html#8327" class="Bound">A</a> <a id="8329" href="Chapter.Logic.Connectives.html#8329" class="Bound">B</a> <a id="8331" href="Chapter.Logic.Connectives.html#8331" class="Bound">C</a> <a id="8333" class="Symbol">:</a> <a id="8335" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8338" class="Symbol">}</a> <a id="8340" class="Symbol">→</a> <a id="8342" href="Chapter.Logic.Connectives.html#8327" class="Bound">A</a> <a id="8344" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8346" class="Symbol">(</a><a id="8347" href="Chapter.Logic.Connectives.html#8329" class="Bound">B</a> <a id="8349" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="8351" href="Chapter.Logic.Connectives.html#8331" class="Bound">C</a><a id="8352" class="Symbol">)</a> <a id="8354" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8356" class="Symbol">(</a><a id="8357" href="Chapter.Logic.Connectives.html#8327" class="Bound">A</a> <a id="8359" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8361" href="Chapter.Logic.Connectives.html#8329" class="Bound">B</a><a id="8362" class="Symbol">)</a> <a id="8364" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="8366" class="Symbol">(</a><a id="8367" href="Chapter.Logic.Connectives.html#8327" class="Bound">A</a> <a id="8369" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8371" href="Chapter.Logic.Connectives.html#8331" class="Bound">C</a><a id="8372" class="Symbol">)</a>
<a id="8374" href="Chapter.Logic.Connectives.html#8315" class="Function">×⊎-dist</a> <a id="8382" class="Symbol">=</a>
  <a id="8386" class="Symbol">(λ</a> <a id="8389" href="Chapter.Logic.Connectives.html#8389" class="Bound">p</a> <a id="8391" class="Symbol">→</a> <a id="8393" href="Chapter.Logic.Connectives.html#4264" class="Function">⊎-elim</a> <a id="8400" class="Symbol">(</a><a id="8401" href="Chapter.Logic.Connectives.html#3939" class="InductiveConstructor">inj₁</a> <a id="8406" href="Function.Base.html#1134" class="Function Operator">∘</a> <a id="8408" class="Symbol">(</a><a id="8409" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8413" href="Chapter.Logic.Connectives.html#8389" class="Bound">p</a> <a id="8415" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,_</a><a id="8417" class="Symbol">))</a> <a id="8420" class="Symbol">(</a><a id="8421" href="Chapter.Logic.Connectives.html#3958" class="InductiveConstructor">inj₂</a> <a id="8426" href="Function.Base.html#1134" class="Function Operator">∘</a> <a id="8428" class="Symbol">(</a><a id="8429" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8433" href="Chapter.Logic.Connectives.html#8389" class="Bound">p</a> <a id="8435" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,_</a><a id="8437" class="Symbol">))</a> <a id="8440" class="Symbol">(</a><a id="8441" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="8445" href="Chapter.Logic.Connectives.html#8389" class="Bound">p</a><a id="8446" class="Symbol">))</a> <a id="8449" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a>
  <a id="8453" href="Chapter.Logic.Connectives.html#4264" class="Function">⊎-elim</a> <a id="8460" class="Symbol">(λ</a> <a id="8463" href="Chapter.Logic.Connectives.html#8463" class="Bound">p</a> <a id="8465" class="Symbol">→</a> <a id="8467" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8471" href="Chapter.Logic.Connectives.html#8463" class="Bound">p</a> <a id="8473" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8475" href="Chapter.Logic.Connectives.html#3939" class="InductiveConstructor">inj₁</a> <a id="8480" class="Symbol">(</a><a id="8481" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="8485" href="Chapter.Logic.Connectives.html#8463" class="Bound">p</a><a id="8486" class="Symbol">))</a> <a id="8489" class="Symbol">(λ</a> <a id="8492" href="Chapter.Logic.Connectives.html#8492" class="Bound">p</a> <a id="8494" class="Symbol">→</a> <a id="8496" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8500" href="Chapter.Logic.Connectives.html#8492" class="Bound">p</a> <a id="8502" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8504" href="Chapter.Logic.Connectives.html#3958" class="InductiveConstructor">inj₂</a> <a id="8509" class="Symbol">(</a><a id="8510" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="8514" href="Chapter.Logic.Connectives.html#8492" class="Bound">p</a><a id="8515" class="Symbol">))</a>

<a id="8519" class="Comment">-- EXERCISE 4</a>
<a id="×-unit-l"></a><a id="8533" href="Chapter.Logic.Connectives.html#8533" class="Function">×-unit-l</a> <a id="8542" class="Symbol">:</a> <a id="8544" class="Symbol">∀{</a><a id="8546" href="Chapter.Logic.Connectives.html#8546" class="Bound">A</a> <a id="8548" class="Symbol">:</a> <a id="8550" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8553" class="Symbol">}</a> <a id="8555" class="Symbol">→</a> <a id="8557" href="Chapter.Logic.Connectives.html#4739" class="Datatype">⊤</a> <a id="8559" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8561" href="Chapter.Logic.Connectives.html#8546" class="Bound">A</a> <a id="8563" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8565" href="Chapter.Logic.Connectives.html#8546" class="Bound">A</a>
<a id="8567" href="Chapter.Logic.Connectives.html#8533" class="Function">×-unit-l</a> <a id="8576" class="Symbol">=</a> <a id="8578" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="8582" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8584" class="Symbol">(</a><a id="8585" href="Chapter.Logic.Connectives.html#4755" class="InductiveConstructor">tt</a> <a id="8588" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,_</a><a id="8590" class="Symbol">)</a>

<a id="×-unit-r"></a><a id="8593" href="Chapter.Logic.Connectives.html#8593" class="Function">×-unit-r</a> <a id="8602" class="Symbol">:</a> <a id="8604" class="Symbol">∀{</a><a id="8606" href="Chapter.Logic.Connectives.html#8606" class="Bound">A</a> <a id="8608" class="Symbol">:</a> <a id="8610" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8613" class="Symbol">}</a> <a id="8615" class="Symbol">→</a> <a id="8617" href="Chapter.Logic.Connectives.html#8606" class="Bound">A</a> <a id="8619" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8621" href="Chapter.Logic.Connectives.html#4739" class="Datatype">⊤</a> <a id="8623" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8625" href="Chapter.Logic.Connectives.html#8606" class="Bound">A</a>
<a id="8627" href="Chapter.Logic.Connectives.html#8593" class="Function">×-unit-r</a> <a id="8636" class="Symbol">=</a> <a id="8638" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8642" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8644" class="Symbol">(</a><a id="8645" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">_,</a> <a id="8648" href="Chapter.Logic.Connectives.html#4755" class="InductiveConstructor">tt</a><a id="8650" class="Symbol">)</a>

<a id="8653" class="Comment">-- EXERCISE 5</a>
<a id="⊎-unit-l"></a><a id="8667" href="Chapter.Logic.Connectives.html#8667" class="Function">⊎-unit-l</a> <a id="8676" class="Symbol">:</a> <a id="8678" class="Symbol">∀{</a><a id="8680" href="Chapter.Logic.Connectives.html#8680" class="Bound">A</a> <a id="8682" class="Symbol">:</a> <a id="8684" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8687" class="Symbol">}</a> <a id="8689" class="Symbol">→</a> <a id="8691" href="Chapter.Logic.Connectives.html#4910" class="Datatype">⊥</a> <a id="8693" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="8695" href="Chapter.Logic.Connectives.html#8680" class="Bound">A</a> <a id="8697" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8699" href="Chapter.Logic.Connectives.html#8680" class="Bound">A</a>
<a id="8701" href="Chapter.Logic.Connectives.html#8667" class="Function">⊎-unit-l</a> <a id="8710" class="Symbol">=</a> <a id="8712" href="Chapter.Logic.Connectives.html#4264" class="Function">⊎-elim</a> <a id="8719" href="Chapter.Logic.Connectives.html#5199" class="Function">⊥-elim</a> <a id="8726" href="Function.Base.html#704" class="Function">id</a> <a id="8729" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8731" href="Chapter.Logic.Connectives.html#3958" class="InductiveConstructor">inj₂</a>

<a id="⊎-unit-r"></a><a id="8737" href="Chapter.Logic.Connectives.html#8737" class="Function">⊎-unit-r</a> <a id="8746" class="Symbol">:</a> <a id="8748" class="Symbol">∀{</a><a id="8750" href="Chapter.Logic.Connectives.html#8750" class="Bound">A</a> <a id="8752" class="Symbol">:</a> <a id="8754" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8757" class="Symbol">}</a> <a id="8759" class="Symbol">→</a> <a id="8761" href="Chapter.Logic.Connectives.html#8750" class="Bound">A</a> <a id="8763" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="8765" href="Chapter.Logic.Connectives.html#4910" class="Datatype">⊥</a> <a id="8767" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8769" href="Chapter.Logic.Connectives.html#8750" class="Bound">A</a>
<a id="8771" href="Chapter.Logic.Connectives.html#8737" class="Function">⊎-unit-r</a> <a id="8780" class="Symbol">=</a> <a id="8782" href="Chapter.Logic.Connectives.html#4264" class="Function">⊎-elim</a> <a id="8789" href="Function.Base.html#704" class="Function">id</a> <a id="8792" href="Chapter.Logic.Connectives.html#5199" class="Function">⊥-elim</a> <a id="8799" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8801" href="Chapter.Logic.Connectives.html#3939" class="InductiveConstructor">inj₁</a>

<a id="8807" class="Comment">-- EXERCISE 6</a>
<a id="⊎-⊤-l"></a><a id="8821" href="Chapter.Logic.Connectives.html#8821" class="Function">⊎-⊤-l</a> <a id="8827" class="Symbol">:</a> <a id="8829" class="Symbol">∀{</a><a id="8831" href="Chapter.Logic.Connectives.html#8831" class="Bound">A</a> <a id="8833" class="Symbol">:</a> <a id="8835" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8838" class="Symbol">}</a> <a id="8840" class="Symbol">→</a> <a id="8842" href="Chapter.Logic.Connectives.html#4739" class="Datatype">⊤</a> <a id="8844" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="8846" href="Chapter.Logic.Connectives.html#8831" class="Bound">A</a> <a id="8848" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8850" href="Chapter.Logic.Connectives.html#4739" class="Datatype">⊤</a>
<a id="8852" href="Chapter.Logic.Connectives.html#8821" class="Function">⊎-⊤-l</a> <a id="8858" class="Symbol">=</a> <a id="8860" href="Function.Base.html#725" class="Function">const</a> <a id="8866" href="Chapter.Logic.Connectives.html#4755" class="InductiveConstructor">tt</a> <a id="8869" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8871" href="Chapter.Logic.Connectives.html#3939" class="InductiveConstructor">inj₁</a>

<a id="⊎-⊤-r"></a><a id="8877" href="Chapter.Logic.Connectives.html#8877" class="Function">⊎-⊤-r</a> <a id="8883" class="Symbol">:</a> <a id="8885" class="Symbol">∀{</a><a id="8887" href="Chapter.Logic.Connectives.html#8887" class="Bound">A</a> <a id="8889" class="Symbol">:</a> <a id="8891" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8894" class="Symbol">}</a> <a id="8896" class="Symbol">→</a> <a id="8898" href="Chapter.Logic.Connectives.html#8887" class="Bound">A</a> <a id="8900" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="8902" href="Chapter.Logic.Connectives.html#4739" class="Datatype">⊤</a> <a id="8904" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8906" href="Chapter.Logic.Connectives.html#4739" class="Datatype">⊤</a>
<a id="8908" href="Chapter.Logic.Connectives.html#8877" class="Function">⊎-⊤-r</a> <a id="8914" class="Symbol">=</a> <a id="8916" href="Function.Base.html#725" class="Function">const</a> <a id="8922" href="Chapter.Logic.Connectives.html#4755" class="InductiveConstructor">tt</a> <a id="8925" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8927" href="Chapter.Logic.Connectives.html#3958" class="InductiveConstructor">inj₂</a>

<a id="8933" class="Comment">-- EXERCISE 7</a>
<a id="×-⊥-l"></a><a id="8947" href="Chapter.Logic.Connectives.html#8947" class="Function">×-⊥-l</a> <a id="8953" class="Symbol">:</a> <a id="8955" class="Symbol">∀{</a><a id="8957" href="Chapter.Logic.Connectives.html#8957" class="Bound">A</a> <a id="8959" class="Symbol">:</a> <a id="8961" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8964" class="Symbol">}</a> <a id="8966" class="Symbol">→</a> <a id="8968" href="Chapter.Logic.Connectives.html#4910" class="Datatype">⊥</a> <a id="8970" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="8972" href="Chapter.Logic.Connectives.html#8957" class="Bound">A</a> <a id="8974" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="8976" href="Chapter.Logic.Connectives.html#4910" class="Datatype">⊥</a>
<a id="8978" href="Chapter.Logic.Connectives.html#8947" class="Function">×-⊥-l</a> <a id="8984" class="Symbol">=</a> <a id="8986" href="Chapter.Logic.Connectives.html#2839" class="Function">fst</a> <a id="8990" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="8992" href="Chapter.Logic.Connectives.html#5199" class="Function">⊥-elim</a>

<a id="×-⊥-r"></a><a id="9000" href="Chapter.Logic.Connectives.html#9000" class="Function">×-⊥-r</a> <a id="9006" class="Symbol">:</a> <a id="9008" class="Symbol">∀{</a><a id="9010" href="Chapter.Logic.Connectives.html#9010" class="Bound">A</a> <a id="9012" class="Symbol">:</a> <a id="9014" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="9017" class="Symbol">}</a> <a id="9019" class="Symbol">→</a> <a id="9021" href="Chapter.Logic.Connectives.html#9010" class="Bound">A</a> <a id="9023" href="Chapter.Logic.Connectives.html#1862" class="Datatype Operator">×</a> <a id="9025" href="Chapter.Logic.Connectives.html#4910" class="Datatype">⊥</a> <a id="9027" href="Chapter.Logic.Connectives.html#3292" class="Function Operator">⇔</a> <a id="9029" href="Chapter.Logic.Connectives.html#4910" class="Datatype">⊥</a>
<a id="9031" href="Chapter.Logic.Connectives.html#9000" class="Function">×-⊥-r</a> <a id="9037" class="Symbol">=</a> <a id="9039" href="Chapter.Logic.Connectives.html#2887" class="Function">snd</a> <a id="9043" href="Chapter.Logic.Connectives.html#1892" class="InductiveConstructor Operator">,</a> <a id="9045" href="Chapter.Logic.Connectives.html#5199" class="Function">⊥-elim</a>

<a id="9053" class="Comment">-- EXERCISE 8</a>
<a id="Bool-⊎"></a><a id="9067" href="Chapter.Logic.Connectives.html#9067" class="Function">Bool-⊎</a> <a id="9074" class="Symbol">:</a> <a id="9076" class="Symbol">∀(</a><a id="9078" href="Chapter.Logic.Connectives.html#9078" class="Bound">b</a> <a id="9080" class="Symbol">:</a> <a id="9082" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="9086" class="Symbol">)</a> <a id="9088" class="Symbol">→</a> <a id="9090" class="Symbol">(</a><a id="9091" href="Chapter.Logic.Connectives.html#9078" class="Bound">b</a> <a id="9093" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9095" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a><a id="9099" class="Symbol">)</a> <a id="9101" href="Chapter.Logic.Connectives.html#3909" class="Datatype Operator">⊎</a> <a id="9103" class="Symbol">(</a><a id="9104" href="Chapter.Logic.Connectives.html#9078" class="Bound">b</a> <a id="9106" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="9108" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a><a id="9113" class="Symbol">)</a>
<a id="9115" href="Chapter.Logic.Connectives.html#9067" class="Function">Bool-⊎</a> <a id="9122" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>  <a id="9128" class="Symbol">=</a> <a id="9130" href="Chapter.Logic.Connectives.html#3939" class="InductiveConstructor">inj₁</a> <a id="9135" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="9140" href="Chapter.Logic.Connectives.html#9067" class="Function">Bool-⊎</a> <a id="9147" href="Agda.Builtin.Bool.html#192" class="InductiveConstructor">false</a> <a id="9153" class="Symbol">=</a> <a id="9155" href="Chapter.Logic.Connectives.html#3958" class="InductiveConstructor">inj₂</a> <a id="9160" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>

</pre>{:.solution}
