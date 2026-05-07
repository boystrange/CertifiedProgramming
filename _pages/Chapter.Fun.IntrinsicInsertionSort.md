---
title: Intrinsic verification of insertion sort
prev:  Chapter.Fun.ExtrinsicInsertionSort
---

<pre class="Agda"><a id="104" class="Keyword">module</a> <a id="111" href="Chapter.Fun.IntrinsicInsertionSort.html" class="Module">Chapter.Fun.IntrinsicInsertionSort</a> <a id="146" class="Keyword">where</a>
</pre>
The extrinsic verification of insertion sort allowed us to prove the
correctness of insertion sort by considering each aspect of the
algorithm in isolation. Indeed, we have defined the algorithm
(`insertion-sort`), the proof that the algorithm yields a sorted
list (`sorted-insertion-sort`) and the proof that the algorithm
yields a permutation of the original list
(`insertion-sort-permutation`) as separate elements. It is easy to
observe that these elements are structurally related. In particular,
most proofs must perform a case analysis on an application of
`≤-total` because that is the way in which the `insert` function is
defined. As a consequence, there is a certain amount of redundancy
in the proofs.

In this chapter we revisit the verification of insertion sort, but
we do so using a different approach called *intrinsic
verification*. In this approach, the implementation of the algorithm
and the proof of its properties are done simultaneously. As we will
see, the overall amount of Agda code we have to write is noticeably
smaller, although the code itself is necessarily more convoluted.

## Imports

<pre class="Agda"><a id="1281" class="Keyword">open</a> <a id="1286" class="Keyword">import</a> <a id="1293" href="Data.Nat.html" class="Module">Data.Nat</a> <a id="1302" class="Keyword">using</a> <a id="1308" class="Symbol">(</a><a id="1309" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="1310" class="Symbol">;</a> <a id="1312" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="1316" class="Symbol">;</a> <a id="1318" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a><a id="1321" class="Symbol">;</a> <a id="1323" href="Data.Nat.Base.html#1697" class="Datatype Operator">_≤_</a><a id="1326" class="Symbol">)</a>
<a id="1328" class="Keyword">open</a> <a id="1333" class="Keyword">import</a> <a id="1340" href="Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="1360" class="Keyword">using</a> <a id="1366" class="Symbol">(</a><a id="1367" href="Data.Nat.Properties.html#7023" class="Function">≤-total</a><a id="1374" class="Symbol">)</a>
<a id="1376" class="Keyword">open</a> <a id="1381" class="Keyword">import</a> <a id="1388" href="Data.List.html" class="Module">Data.List</a> <a id="1398" class="Keyword">using</a> <a id="1404" class="Symbol">(</a><a id="1405" href="Agda.Builtin.List.html#147" class="Datatype">List</a><a id="1409" class="Symbol">;</a> <a id="1411" href="Data.List.Base.html#7301" class="InductiveConstructor">[]</a><a id="1413" class="Symbol">;</a> <a id="1415" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">_∷_</a><a id="1418" class="Symbol">;</a> <a id="1420" href="Data.List.Base.html#4907" class="Function Operator">[_]</a><a id="1423" class="Symbol">)</a>
<a id="1425" class="Keyword">open</a> <a id="1430" class="Keyword">import</a> <a id="1437" href="Data.Product.html" class="Module">Data.Product</a>
<a id="1450" class="Keyword">open</a> <a id="1455" class="Keyword">import</a> <a id="1462" href="Data.Sum.html" class="Module">Data.Sum</a> <a id="1471" class="Keyword">using</a> <a id="1477" class="Symbol">(</a><a id="1478" href="Data.Sum.Base.html#625" class="Datatype Operator">_⊎_</a><a id="1481" class="Symbol">;</a> <a id="1483" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a><a id="1487" class="Symbol">;</a> <a id="1489" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a><a id="1493" class="Symbol">)</a>
<a id="1495" class="Keyword">open</a> <a id="1500" class="Keyword">import</a> <a id="1507" href="Chapter.Fun.SortedLists.html" class="Module">Chapter.Fun.SortedLists</a>
</pre>
## Intrinsically verified insertion

As expected, if we aim at providing an intrinsically verified
insertion sort we have to provide an intrinsically verified
insertion operation, which we specify thus.

<pre class="Agda"><a id="intrinsic-insert"></a><a id="1744" href="Chapter.Fun.IntrinsicInsertionSort.html#1744" class="Function">intrinsic-insert</a> <a id="1761" class="Symbol">:</a> <a id="1763" class="Symbol">∀(</a><a id="1765" href="Chapter.Fun.IntrinsicInsertionSort.html#1765" class="Bound">x</a> <a id="1767" class="Symbol">:</a> <a id="1769" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="1770" class="Symbol">)</a> <a id="1772" class="Symbol">(</a><a id="1773" href="Chapter.Fun.IntrinsicInsertionSort.html#1773" class="Bound">ys</a> <a id="1776" class="Symbol">:</a> <a id="1778" href="Agda.Builtin.List.html#147" class="Datatype">List</a> <a id="1783" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="1784" class="Symbol">)</a> <a id="1786" class="Symbol">-&gt;</a> <a id="1789" href="Chapter.Fun.SortedLists.html#4454" class="Datatype">Sorted</a> <a id="1796" href="Chapter.Fun.IntrinsicInsertionSort.html#1773" class="Bound">ys</a> <a id="1799" class="Symbol">-&gt;</a>
                   <a id="1821" href="Data.Product.Base.html#1371" class="Function">∃[</a> <a id="1824" href="Chapter.Fun.IntrinsicInsertionSort.html#1824" class="Bound">zs</a> <a id="1827" href="Data.Product.Base.html#1371" class="Function">]</a> <a id="1829" href="Chapter.Fun.IntrinsicInsertionSort.html#1824" class="Bound">zs</a> <a id="1832" href="Chapter.Fun.SortedLists.html#6237" class="Datatype Operator">#</a> <a id="1834" href="Chapter.Fun.IntrinsicInsertionSort.html#1765" class="Bound">x</a> <a id="1836" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="1838" href="Chapter.Fun.IntrinsicInsertionSort.html#1773" class="Bound">ys</a> <a id="1841" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="1843" href="Chapter.Fun.SortedLists.html#4454" class="Datatype">Sorted</a> <a id="1850" href="Chapter.Fun.IntrinsicInsertionSort.html#1824" class="Bound">zs</a>
</pre>
In words, the insert operation applied to a number `x` and a sorted
list `ys` yields another sorted list `zs` that is a permutation of
`x ∷ ys`. Note that now the function takes not only the element and
the list on which it operates, but also a proof that the list is
sorted.

The base case in which `ys` is empty is handled by the following
equation.

<pre class="Agda"><a id="2215" href="Chapter.Fun.IntrinsicInsertionSort.html#1744" class="Function">intrinsic-insert</a> <a id="2232" href="Chapter.Fun.IntrinsicInsertionSort.html#2232" class="Bound">x</a> <a id="2234" href="Agda.Builtin.List.html#184" class="InductiveConstructor">[]</a> <a id="2237" href="Chapter.Fun.SortedLists.html#4484" class="InductiveConstructor">sorted-[]</a> <a id="2247" class="Symbol">=</a> <a id="2249" href="Data.List.Base.html#4907" class="Function Operator">[</a> <a id="2251" href="Chapter.Fun.IntrinsicInsertionSort.html#2232" class="Bound">x</a> <a id="2253" href="Data.List.Base.html#4907" class="Function Operator">]</a> <a id="2255" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="2257" href="Chapter.Fun.SortedLists.html#6283" class="InductiveConstructor">#refl</a> <a id="2263" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="2265" href="Chapter.Fun.SortedLists.html#4671" class="Function">singleton-sorted</a> <a id="2282" href="Chapter.Fun.IntrinsicInsertionSort.html#2232" class="Bound">x</a>
</pre>
Remeber that a proof of an existential quantification `∃[ x ] P` is
a pair consisting of a witness and a proof that the witness
satisfies `P`. In this case, the predicate `P` is a conjunction
whose proof is itself a pair. For this reason, `intrinsic-insert`
yields a *triple* made of the witness, which is the singleton list
`[ x ]`, a proof that `[ x ]` is a permutation of `x ∷ []` and a
proof that `[ x ]` is sorted. Recall from the definition of `[_]`
that `[ x ]` and `x ∷ []` are definitionally equal, so `#refl`
suffices to prove that they are one the permutation of the other.

When we are inserting `x` in a non-empty list `y ∷ ys` we have to
establish the relationship between `x` and `y`, which we do by
performing case analysis on `≤-total x y`.

<pre class="Agda"><a id="3052" href="Chapter.Fun.IntrinsicInsertionSort.html#1744" class="Function">intrinsic-insert</a> <a id="3069" href="Chapter.Fun.IntrinsicInsertionSort.html#3069" class="Bound">x</a> <a id="3071" class="Symbol">(</a><a id="3072" href="Chapter.Fun.IntrinsicInsertionSort.html#3072" class="Bound">y</a> <a id="3074" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="3076" href="Chapter.Fun.IntrinsicInsertionSort.html#3076" class="Bound">ys</a><a id="3078" class="Symbol">)</a> <a id="3080" class="Symbol">(</a><a id="3081" href="Chapter.Fun.SortedLists.html#4508" class="InductiveConstructor">sorted-∷</a> <a id="3090" href="Chapter.Fun.IntrinsicInsertionSort.html#3090" class="Bound">y≤ys</a> <a id="3095" href="Chapter.Fun.IntrinsicInsertionSort.html#3095" class="Bound">ys-sorted</a><a id="3104" class="Symbol">)</a> <a id="3106" class="Keyword">with</a> <a id="3111" href="Data.Nat.Properties.html#7023" class="Function">≤-total</a> <a id="3119" href="Chapter.Fun.IntrinsicInsertionSort.html#3069" class="Bound">x</a> <a id="3121" href="Chapter.Fun.IntrinsicInsertionSort.html#3072" class="Bound">y</a>
</pre>
Since the list in which we are inserting `x` is not empty, the proof
that it is sorted must have the form `sorted-∷ y≤ys ys-sorted`,
which contains a sub-proof that `y` is a lower bound for `ys` and
that `ys` is itself sorted. Let us now consider the case in which `x
≤ y`.

<pre class="Agda"><a id="3407" class="Symbol">...</a> <a id="3411" class="Symbol">|</a> <a id="3413" href="Data.Sum.Base.html#675" class="InductiveConstructor">inj₁</a> <a id="3418" href="Chapter.Fun.IntrinsicInsertionSort.html#3418" class="Bound">x≤y</a> <a id="3422" class="Symbol">=</a> <a id="3424" class="Bound">x</a> <a id="3426" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="3428" class="Bound">y</a> <a id="3430" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="3432" class="Bound">ys</a> <a id="3435" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a>
                 <a id="3454" href="Chapter.Fun.SortedLists.html#6283" class="InductiveConstructor">#refl</a> <a id="3460" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a>
                 <a id="3479" href="Chapter.Fun.SortedLists.html#4508" class="InductiveConstructor">sorted-∷</a> <a id="3488" class="Symbol">(</a><a id="3489" href="Chapter.Fun.SortedLists.html#3550" class="InductiveConstructor">lb-∷</a> <a id="3494" href="Chapter.Fun.IntrinsicInsertionSort.html#3418" class="Bound">x≤y</a> <a id="3498" class="Symbol">(</a><a id="3499" href="Chapter.Fun.SortedLists.html#3769" class="Function">lower-lower-bound</a> <a id="3517" href="Chapter.Fun.IntrinsicInsertionSort.html#3418" class="Bound">x≤y</a> <a id="3521" class="Bound">y≤ys</a><a id="3525" class="Symbol">))</a>
                          <a id="3554" class="Symbol">(</a><a id="3555" href="Chapter.Fun.SortedLists.html#4508" class="InductiveConstructor">sorted-∷</a> <a id="3564" class="Bound">y≤ys</a> <a id="3569" class="Bound">ys-sorted</a><a id="3578" class="Symbol">)</a>
</pre>
Here `x` is inserted just at the front of the list, so no swapping
is necessary and `#refl` suffices as far as permutations are
concerned. In order to prove that the resulting list is sorted we
need a proof that `x` is a lower bound for `y ∷ ys`, which we
obtain from the proof that `y` is a lower bound for `ys` along with
the hypothesis `x≤y` using the `lower-lower-bound` lemma that we
have proved in a previous chapter.

<pre class="Agda"><a id="4014" class="Symbol">...</a> <a id="4018" class="Symbol">|</a> <a id="4020" href="Data.Sum.Base.html#700" class="InductiveConstructor">inj₂</a> <a id="4025" href="Chapter.Fun.IntrinsicInsertionSort.html#4025" class="Bound">y≤x</a> <a id="4029" class="Keyword">with</a> <a id="4034" href="Chapter.Fun.IntrinsicInsertionSort.html#1744" class="Function">intrinsic-insert</a> <a id="4051" class="Bound">x</a> <a id="4053" class="Bound">ys</a> <a id="4056" class="Bound">ys-sorted</a>
</pre>
If `y ≤ x`, then we have to insert `x` in `ys`. This operation will
not only return the resulting list `zs`, but also a proof `π` that
`zs` is a permutation of `x ∷ ys` and a proof `zs-sorted` that `zs`
is sorted. We combine these proofs in the result of the function.

<pre class="Agda"><a id="4345" class="Symbol">...</a> <a id="4349" class="Symbol">|</a> <a id="4351" href="Chapter.Fun.IntrinsicInsertionSort.html#4351" class="Bound">zs</a> <a id="4354" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="4356" href="Chapter.Fun.IntrinsicInsertionSort.html#4356" class="Bound">π</a> <a id="4358" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="4360" href="Chapter.Fun.IntrinsicInsertionSort.html#4360" class="Bound">zs-sorted</a> <a id="4370" class="Symbol">=</a>
  <a id="4374" class="Bound">y</a> <a id="4376" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="4378" href="Chapter.Fun.IntrinsicInsertionSort.html#4351" class="Bound">zs</a> <a id="4381" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a>
  <a id="4385" class="Symbol">(</a><a id="4386" href="Chapter.Fun.SortedLists.html#7170" class="Function Operator">#begin</a>
    <a id="4397" class="Bound">y</a> <a id="4399" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="4401" href="Chapter.Fun.IntrinsicInsertionSort.html#4351" class="Bound">zs</a>     <a id="4408" href="Chapter.Fun.SortedLists.html#7300" class="Function Operator">#⟨</a> <a id="4411" href="Chapter.Fun.SortedLists.html#6379" class="InductiveConstructor">#cong</a> <a id="4417" href="Chapter.Fun.IntrinsicInsertionSort.html#4356" class="Bound">π</a> <a id="4419" href="Chapter.Fun.SortedLists.html#7300" class="Function Operator">⟩</a>
    <a id="4425" class="Bound">y</a> <a id="4427" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="4429" class="Bound">x</a> <a id="4431" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="4433" class="Bound">ys</a> <a id="4436" href="Chapter.Fun.SortedLists.html#7300" class="Function Operator">#⟨</a> <a id="4439" href="Chapter.Fun.SortedLists.html#6318" class="InductiveConstructor">#swap</a> <a id="4445" href="Chapter.Fun.SortedLists.html#7300" class="Function Operator">⟩</a>
    <a id="4451" class="Bound">x</a> <a id="4453" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="4455" class="Bound">y</a> <a id="4457" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="4459" class="Bound">ys</a> <a id="4462" href="Chapter.Fun.SortedLists.html#7244" class="Function Operator">#∎</a><a id="4464" class="Symbol">)</a> <a id="4466" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a>
  <a id="4470" href="Chapter.Fun.SortedLists.html#4508" class="InductiveConstructor">sorted-∷</a> <a id="4479" class="Symbol">(</a><a id="4480" href="Chapter.Fun.SortedLists.html#8798" class="Function">lower-bound-permutation</a> <a id="4504" href="Chapter.Fun.IntrinsicInsertionSort.html#4356" class="Bound">π</a> <a id="4506" class="Symbol">(</a><a id="4507" href="Chapter.Fun.SortedLists.html#3550" class="InductiveConstructor">lb-∷</a> <a id="4512" class="Bound">y≤x</a> <a id="4516" class="Bound">y≤ys</a><a id="4520" class="Symbol">))</a> <a id="4523" href="Chapter.Fun.IntrinsicInsertionSort.html#4360" class="Bound">zs-sorted</a>
</pre>
## Intrinsically verified insertion sort

We are now ready to complete the intrinsic verification of insertion
sort.

<pre class="Agda"><a id="verified-insertion-sort"></a><a id="4660" href="Chapter.Fun.IntrinsicInsertionSort.html#4660" class="Function">verified-insertion-sort</a> <a id="4684" class="Symbol">:</a> <a id="4686" href="Chapter.Fun.SortedLists.html#8642" class="Function">SortingFunction</a>
</pre>
In the base case, when the list to be sorted is empty, there isn't
much to do except providing the easy proofs that the empty list is
sorted and a permutation of itself.

<pre class="Agda"><a id="4882" href="Chapter.Fun.IntrinsicInsertionSort.html#4660" class="Function">verified-insertion-sort</a> <a id="4906" href="Agda.Builtin.List.html#184" class="InductiveConstructor">[]</a> <a id="4909" class="Symbol">=</a> <a id="4911" href="Agda.Builtin.List.html#184" class="InductiveConstructor">[]</a> <a id="4914" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="4916" href="Chapter.Fun.SortedLists.html#6283" class="InductiveConstructor">#refl</a> <a id="4922" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="4924" href="Chapter.Fun.SortedLists.html#4484" class="InductiveConstructor">sorted-[]</a>
</pre>
In the inductive case, first of all we recursively sort the tail of
the list.

<pre class="Agda"><a id="5022" href="Chapter.Fun.IntrinsicInsertionSort.html#4660" class="Function">verified-insertion-sort</a> <a id="5046" class="Symbol">(</a><a id="5047" href="Chapter.Fun.IntrinsicInsertionSort.html#5047" class="Bound">x</a> <a id="5049" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="5051" href="Chapter.Fun.IntrinsicInsertionSort.html#5051" class="Bound">xs</a><a id="5053" class="Symbol">)</a> <a id="5055" class="Keyword">with</a> <a id="5060" href="Chapter.Fun.IntrinsicInsertionSort.html#4660" class="Function">verified-insertion-sort</a> <a id="5084" href="Chapter.Fun.IntrinsicInsertionSort.html#5051" class="Bound">xs</a>
</pre>
By performing case analysis we get access to the resulting list
`ys`, a proof `ys#xs` that `ys` is a permutation of `xs` and a proof
`ys-sorted` that `ys` is sorted. Now we can insert `x` into `ys`.

<pre class="Agda"><a id="5296" class="Symbol">...</a> <a id="5300" class="Symbol">|</a> <a id="5302" href="Chapter.Fun.IntrinsicInsertionSort.html#5302" class="Bound">ys</a> <a id="5305" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="5307" href="Chapter.Fun.IntrinsicInsertionSort.html#5307" class="Bound">ys#xs</a> <a id="5313" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="5315" href="Chapter.Fun.IntrinsicInsertionSort.html#5315" class="Bound">ys-sorted</a> <a id="5325" class="Keyword">with</a> <a id="5330" href="Chapter.Fun.IntrinsicInsertionSort.html#1744" class="Function">intrinsic-insert</a> <a id="5347" class="Bound">x</a> <a id="5349" href="Chapter.Fun.IntrinsicInsertionSort.html#5302" class="Bound">ys</a> <a id="5352" href="Chapter.Fun.IntrinsicInsertionSort.html#5315" class="Bound">ys-sorted</a>
</pre>
We do case analysis on the result once again so that we get access
to the resulting list `zs`, the proof `π` that `zs` is a permutation
of `x ∷ ys` and the proof `zs-sorted` that `zs` is sorted. The
proof that `zs` is a permutation of `x ∷ xs` follows from
transitivity of permutations and the sub-proofs `ys#xs` and `π`.

<pre class="Agda"><a id="5694" class="Symbol">...</a> <a id="5698" class="Symbol">|</a> <a id="5700" href="Chapter.Fun.IntrinsicInsertionSort.html#5700" class="Bound">zs</a> <a id="5703" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="5705" href="Chapter.Fun.IntrinsicInsertionSort.html#5705" class="Bound">π</a> <a id="5707" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="5709" href="Chapter.Fun.IntrinsicInsertionSort.html#5709" class="Bound">zs-sorted</a> <a id="5719" class="Symbol">=</a>
  <a id="5723" href="Chapter.Fun.IntrinsicInsertionSort.html#5700" class="Bound">zs</a> <a id="5726" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a>
  <a id="5730" class="Symbol">(</a><a id="5731" href="Chapter.Fun.SortedLists.html#7170" class="Function Operator">#begin</a>
    <a id="5742" href="Chapter.Fun.IntrinsicInsertionSort.html#5700" class="Bound">zs</a>     <a id="5749" href="Chapter.Fun.SortedLists.html#7300" class="Function Operator">#⟨</a> <a id="5752" href="Chapter.Fun.IntrinsicInsertionSort.html#5705" class="Bound">π</a> <a id="5754" href="Chapter.Fun.SortedLists.html#7300" class="Function Operator">⟩</a>
    <a id="5760" class="Bound">x</a> <a id="5762" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="5764" class="Bound">ys</a> <a id="5767" href="Chapter.Fun.SortedLists.html#7300" class="Function Operator">#⟨</a> <a id="5770" href="Chapter.Fun.SortedLists.html#6379" class="InductiveConstructor">#cong</a> <a id="5776" class="Bound">ys#xs</a> <a id="5782" href="Chapter.Fun.SortedLists.html#7300" class="Function Operator">⟩</a>
    <a id="5788" class="Bound">x</a> <a id="5790" href="Agda.Builtin.List.html#199" class="InductiveConstructor Operator">∷</a> <a id="5792" class="Bound">xs</a> <a id="5795" href="Chapter.Fun.SortedLists.html#7244" class="Function Operator">#∎</a><a id="5797" class="Symbol">)</a> <a id="5799" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a>
  <a id="5803" href="Chapter.Fun.IntrinsicInsertionSort.html#5709" class="Bound">zs-sorted</a>
</pre>