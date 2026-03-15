---
title: A taste of Agda
next:  Chapter.Prologue.Setup
---

<pre class="Agda"><a id="67" class="Keyword">module</a> <a id="74" href="Chapter.Prologue.Demo.html" class="Module">Chapter.Prologue.Demo</a> <a id="96" class="Keyword">where</a>
</pre>
## Imports

The program described in this chapter makes use of natural numbers
and of the equality predicate, whose definitions must be imported
from Agda's standard library. The directives shown below do exactly
that. For the time being, we will use natural numbers and equality
as black boxes; we will see how they can be defined in Agda later
on.

<pre class="Agda"><a id="462" class="Keyword">open</a> <a id="467" class="Keyword">import</a> <a id="474" href="Data.Nat.html" class="Module">Data.Nat</a>
<a id="483" class="Keyword">open</a> <a id="488" class="Keyword">import</a> <a id="495" href="Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a>
<a id="515" class="Keyword">open</a> <a id="520" class="Keyword">import</a> <a id="527" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
<a id="565" class="Keyword">open</a> <a id="570" href="Relation.Binary.PropositionalEquality.Properties.html#6850" class="Module">≡-Reasoning</a>
</pre>
## The sequence of Fibonacci numbers

To get a taste of Agda, let us write a `fibo` function that computes
the k-th number in the sequence of Fibonacci, that is the sequence

    0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, ...

that starts with 0 followed by 1 and such that each subsequent
number is the sum of the previous two. For example, we expect `fibo`
to return 55 when it is applied to 10, since 55 is the 11th number
in the sequence. The easiest implementation of `fibo` in Agda is
shown below.

<pre class="Agda"><a id="fibo"></a><a id="1094" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="1099" class="Symbol">:</a> <a id="1101" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1103" class="Symbol">-&gt;</a> <a id="1106" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="1108" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="1113" class="Number">0</a>             <a id="1127" class="Symbol">=</a> <a id="1129" class="Number">0</a>
<a id="1131" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="1136" class="Number">1</a>             <a id="1150" class="Symbol">=</a> <a id="1152" class="Number">1</a>
<a id="1154" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="1159" class="Symbol">(</a><a id="1160" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1164" class="Symbol">(</a><a id="1165" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1169" href="Chapter.Prologue.Demo.html#1169" class="Bound">k</a><a id="1170" class="Symbol">))</a> <a id="1173" class="Symbol">=</a> <a id="1175" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="1180" href="Chapter.Prologue.Demo.html#1169" class="Bound">k</a> <a id="1182" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="1184" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="1189" class="Symbol">(</a><a id="1190" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1194" href="Chapter.Prologue.Demo.html#1169" class="Bound">k</a><a id="1195" class="Symbol">)</a>
</pre>
Once this script is loaded, we can ask Agda to compute the result of
applying `fibo` to some numbers. By pressing `C-c C-n` and then
entering `fibo 10` we obtain 55, as expected. 

It is a known fact that the shown implementation of `fibo` is
inefficient. In fact, the time for computing the k-th Fibonacci
number is exponential in k. We can propose a more efficient, albeit
slightly more complex function that computes the k-th Fibonacci
number in linear time, as follows.

<pre class="Agda"><a id="fibo-from"></a><a id="1681" href="Chapter.Prologue.Demo.html#1681" class="Function">fibo-from</a> <a id="1691" class="Symbol">:</a> <a id="1693" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1695" class="Symbol">-&gt;</a> <a id="1698" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1700" class="Symbol">-&gt;</a> <a id="1703" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1705" class="Symbol">-&gt;</a> <a id="1708" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="1710" href="Chapter.Prologue.Demo.html#1681" class="Function">fibo-from</a> <a id="1720" href="Chapter.Prologue.Demo.html#1720" class="Bound">m</a> <a id="1722" href="Chapter.Prologue.Demo.html#1722" class="Bound">n</a> <a id="1724" class="Number">0</a>       <a id="1732" class="Symbol">=</a> <a id="1734" href="Chapter.Prologue.Demo.html#1720" class="Bound">m</a>
<a id="1736" href="Chapter.Prologue.Demo.html#1681" class="Function">fibo-from</a> <a id="1746" href="Chapter.Prologue.Demo.html#1746" class="Bound">m</a> <a id="1748" href="Chapter.Prologue.Demo.html#1748" class="Bound">n</a> <a id="1750" class="Symbol">(</a><a id="1751" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1755" href="Chapter.Prologue.Demo.html#1755" class="Bound">k</a><a id="1756" class="Symbol">)</a> <a id="1758" class="Symbol">=</a> <a id="1760" href="Chapter.Prologue.Demo.html#1681" class="Function">fibo-from</a> <a id="1770" href="Chapter.Prologue.Demo.html#1748" class="Bound">n</a> <a id="1772" class="Symbol">(</a><a id="1773" href="Chapter.Prologue.Demo.html#1746" class="Bound">m</a> <a id="1775" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="1777" href="Chapter.Prologue.Demo.html#1748" class="Bound">n</a><a id="1778" class="Symbol">)</a> <a id="1780" href="Chapter.Prologue.Demo.html#1755" class="Bound">k</a>

<a id="fast-fibo"></a><a id="1783" href="Chapter.Prologue.Demo.html#1783" class="Function">fast-fibo</a> <a id="1793" class="Symbol">:</a> <a id="1795" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1797" class="Symbol">-&gt;</a> <a id="1800" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="1802" href="Chapter.Prologue.Demo.html#1783" class="Function">fast-fibo</a> <a id="1812" class="Symbol">=</a> <a id="1814" href="Chapter.Prologue.Demo.html#1681" class="Function">fibo-from</a> <a id="1824" class="Number">0</a> <a id="1826" class="Number">1</a>
</pre>
The `fast-fibo` function is just a wrapper for the auxiliary
`fibo-from` function, which takes three arguments: `m` and `n`,
which are supposed to be two subsequent numbers in the Fibonacci
sequence, and then an index `k` which represents the number of steps
to make in the sequence, starting from `m` and `n`, in order to
reach the desired number. When `k` is 0, the desired number is just
`m`. When `k` is greater than 0 we recursively apply `fibo-from` so
that `m` becomes `n`, `n` becomes the sum of the (old) `m` and of
the (old) `n`, and `k` is decreased by one. That is, `fibo-from` is
basically a functional implementation of the classical loop that
finds the desired number in the Fibonacci sequence by using (and
updating) two auxiliary variables `m` and `n` initialized with 0 and
1.

Now, since `fast-fibo` (and particularly `fibo-from` on which it
relies) is substantially more complex than `fibo`, we may wonder
whether `fast-fibo` is in fact equivalent to `fibo`. We may perform
a few tests asking Agda to evaluate `fast-fibo`, but these tests are
**necessarily finite**. The only way to be absolutely sure that
`fibo` and `fast-fibo` are the same function is by **proving** that
they are equivalent.

It is not too difficult to come up with a pen-and-paper proof that
`fibo` and `fast-fibo` are indeed equivalent, but the doubt might
remain that the proof could contain a mistake. After all, we're
humans and all humans make mistakes. Here is where Agda comes to the
rescue, in that it provides us with some tools for **checking**
whether an equivance proof for `fibo` and `fast-fibo` is valid. Even
more surprisingly, the equivalence proof turns out to be a
collection of functions written in the same language in which we
have implemented `fibo` and `fast-fibo`.

Below are two functions, called `lemma` and `theorem`, that prove
the equivalence of `fibo` and `fast-fibo`. For the time being they
look like almost random sequences of meaningless symbols. In this
course we will learn how to write such proofs with the help of the
interactive features of Agda. For the sake of this quick
introduction, though, it may be worth to notice that in the
**types** of these functions we recognize occurrences of `∀` (the
*universal quantifier*), `->` (*logical implication*), and `≡`
(*propositional equality*). In particular the type of `theorem`
specifies that, for every natural number `k`, the value resulting
from the application `fast-fibo k` is the same value resulting from
the application `fibo k`.

<pre class="Agda"><a id="lemma"></a><a id="4356" href="Chapter.Prologue.Demo.html#4356" class="Function">lemma</a> <a id="4362" class="Symbol">:</a> <a id="4364" class="Symbol">∀(</a><a id="4366" href="Chapter.Prologue.Demo.html#4366" class="Bound">k</a> <a id="4368" href="Chapter.Prologue.Demo.html#4368" class="Bound">i</a> <a id="4370" class="Symbol">:</a> <a id="4372" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="4373" class="Symbol">)</a> <a id="4375" class="Symbol">-&gt;</a> <a id="4378" href="Chapter.Prologue.Demo.html#1681" class="Function">fibo-from</a> <a id="4388" class="Symbol">(</a><a id="4389" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4394" href="Chapter.Prologue.Demo.html#4366" class="Bound">k</a><a id="4395" class="Symbol">)</a> <a id="4397" class="Symbol">(</a><a id="4398" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4403" class="Symbol">(</a><a id="4404" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4408" href="Chapter.Prologue.Demo.html#4366" class="Bound">k</a><a id="4409" class="Symbol">))</a> <a id="4412" href="Chapter.Prologue.Demo.html#4368" class="Bound">i</a> <a id="4414" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4416" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4421" class="Symbol">(</a><a id="4422" href="Chapter.Prologue.Demo.html#4368" class="Bound">i</a> <a id="4424" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4426" href="Chapter.Prologue.Demo.html#4366" class="Bound">k</a><a id="4427" class="Symbol">)</a>
<a id="4429" href="Chapter.Prologue.Demo.html#4356" class="Function">lemma</a> <a id="4435" href="Chapter.Prologue.Demo.html#4435" class="Bound">k</a> <a id="4437" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="4442" class="Symbol">=</a> <a id="4444" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="4449" href="Chapter.Prologue.Demo.html#4356" class="Function">lemma</a> <a id="4455" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a> <a id="4457" class="Symbol">(</a><a id="4458" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4462" href="Chapter.Prologue.Demo.html#4462" class="Bound">i</a><a id="4463" class="Symbol">)</a> <a id="4465" class="Symbol">=</a>
  <a id="4469" href="Relation.Binary.Reasoning.Syntax.html#1572" class="Function Operator">begin</a>
    <a id="4479" href="Chapter.Prologue.Demo.html#1681" class="Function">fibo-from</a> <a id="4489" class="Symbol">(</a><a id="4490" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4495" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a><a id="4496" class="Symbol">)</a> <a id="4498" class="Symbol">(</a><a id="4499" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4504" class="Symbol">(</a><a id="4505" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4509" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a><a id="4510" class="Symbol">))</a> <a id="4513" class="Symbol">(</a><a id="4514" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4518" href="Chapter.Prologue.Demo.html#4462" class="Bound">i</a><a id="4519" class="Symbol">)</a> <a id="4521" href="Relation.Binary.Reasoning.Syntax.html#11079" class="Function">≡⟨⟩</a>
    <a id="4529" href="Chapter.Prologue.Demo.html#1681" class="Function">fibo-from</a> <a id="4539" class="Symbol">(</a><a id="4540" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4545" class="Symbol">(</a><a id="4546" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4550" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a><a id="4551" class="Symbol">))</a> <a id="4554" class="Symbol">(</a><a id="4555" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4560" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a> <a id="4562" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4564" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4569" class="Symbol">(</a><a id="4570" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4574" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a><a id="4575" class="Symbol">))</a> <a id="4578" href="Chapter.Prologue.Demo.html#4462" class="Bound">i</a> <a id="4580" href="Relation.Binary.Reasoning.Syntax.html#11079" class="Function">≡⟨⟩</a>
    <a id="4588" href="Chapter.Prologue.Demo.html#1681" class="Function">fibo-from</a> <a id="4598" class="Symbol">(</a><a id="4599" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4604" class="Symbol">(</a><a id="4605" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4609" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a><a id="4610" class="Symbol">))</a> <a id="4613" class="Symbol">(</a><a id="4614" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4619" class="Symbol">(</a><a id="4620" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4624" class="Symbol">(</a><a id="4625" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4629" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a><a id="4630" class="Symbol">)))</a> <a id="4634" href="Chapter.Prologue.Demo.html#4462" class="Bound">i</a>
      <a id="4642" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">≡⟨</a> <a id="4645" href="Chapter.Prologue.Demo.html#4356" class="Function">lemma</a> <a id="4651" class="Symbol">(</a><a id="4652" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4656" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a><a id="4657" class="Symbol">)</a> <a id="4659" href="Chapter.Prologue.Demo.html#4462" class="Bound">i</a> <a id="4661" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">⟩</a>
    <a id="4667" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4672" class="Symbol">(</a><a id="4673" href="Chapter.Prologue.Demo.html#4462" class="Bound">i</a> <a id="4675" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4677" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4681" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a><a id="4682" class="Symbol">)</a>
      <a id="4690" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">≡⟨</a> <a id="4693" href="Relation.Binary.PropositionalEquality.Core.html#1481" class="Function">cong</a> <a id="4698" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4703" class="Symbol">(</a><a id="4704" href="Data.Nat.Properties.html#15415" class="Function">+-suc</a> <a id="4710" href="Chapter.Prologue.Demo.html#4462" class="Bound">i</a> <a id="4712" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a><a id="4713" class="Symbol">)</a> <a id="4715" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">⟩</a>
    <a id="4721" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4726" class="Symbol">(</a><a id="4727" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4731" href="Chapter.Prologue.Demo.html#4462" class="Bound">i</a> <a id="4733" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4735" href="Chapter.Prologue.Demo.html#4455" class="Bound">k</a><a id="4736" class="Symbol">)</a>
  <a id="4740" href="Relation.Binary.Reasoning.Syntax.html#12345" class="Function Operator">∎</a>

<a id="theorem"></a><a id="4743" href="Chapter.Prologue.Demo.html#4743" class="Function">theorem</a> <a id="4751" class="Symbol">:</a> <a id="4753" class="Symbol">∀(</a><a id="4755" href="Chapter.Prologue.Demo.html#4755" class="Bound">k</a> <a id="4757" class="Symbol">:</a> <a id="4759" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="4760" class="Symbol">)</a> <a id="4762" class="Symbol">-&gt;</a> <a id="4765" href="Chapter.Prologue.Demo.html#1783" class="Function">fast-fibo</a> <a id="4775" href="Chapter.Prologue.Demo.html#4755" class="Bound">k</a> <a id="4777" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4779" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4784" href="Chapter.Prologue.Demo.html#4755" class="Bound">k</a>
<a id="4786" href="Chapter.Prologue.Demo.html#4743" class="Function">theorem</a> <a id="4794" href="Chapter.Prologue.Demo.html#4794" class="Bound">k</a> <a id="4796" class="Symbol">=</a>
  <a id="4800" href="Relation.Binary.Reasoning.Syntax.html#1572" class="Function Operator">begin</a>
    <a id="4810" href="Chapter.Prologue.Demo.html#1783" class="Function">fast-fibo</a> <a id="4820" href="Chapter.Prologue.Demo.html#4794" class="Bound">k</a>     <a id="4826" href="Relation.Binary.Reasoning.Syntax.html#11079" class="Function">≡⟨⟩</a>
    <a id="4834" href="Chapter.Prologue.Demo.html#1681" class="Function">fibo-from</a> <a id="4844" class="Number">0</a> <a id="4846" class="Number">1</a> <a id="4848" href="Chapter.Prologue.Demo.html#4794" class="Bound">k</a> <a id="4850" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">≡⟨</a> <a id="4853" href="Chapter.Prologue.Demo.html#4356" class="Function">lemma</a> <a id="4859" class="Number">0</a> <a id="4861" href="Chapter.Prologue.Demo.html#4794" class="Bound">k</a> <a id="4863" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">⟩</a>
    <a id="4869" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4874" class="Symbol">(</a><a id="4875" href="Chapter.Prologue.Demo.html#4794" class="Bound">k</a> <a id="4877" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4879" class="Number">0</a><a id="4880" class="Symbol">)</a>    <a id="4885" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">≡⟨</a> <a id="4888" href="Relation.Binary.PropositionalEquality.Core.html#1481" class="Function">cong</a> <a id="4893" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4898" class="Symbol">(</a><a id="4899" href="Data.Nat.Properties.html#15779" class="Function">+-identityʳ</a> <a id="4911" href="Chapter.Prologue.Demo.html#4794" class="Bound">k</a><a id="4912" class="Symbol">)</a> <a id="4914" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">⟩</a>
    <a id="4920" href="Chapter.Prologue.Demo.html#1094" class="Function">fibo</a> <a id="4925" href="Chapter.Prologue.Demo.html#4794" class="Bound">k</a>
  <a id="4929" href="Relation.Binary.Reasoning.Syntax.html#12345" class="Function Operator">∎</a>
</pre>
By checking that these functions adhere to the types we've given
them, Agda certifies that `fibo` and `fast-fibo` are equivalent. So,
from now on we can safely use whichever function is more convenient,
preferring `fibo` or `fast-fibo` depending on whether readability or
performance is more important.

## Homework

1. Let $F_i$ be the $i$-th Fibonacci number, defined by the equations

   $$
     F_0 = 0
     \qquad
     F_1 = 1
     \qquad
     F_{i+2} = F_i + F_{i+1}
   $$

   Using pencil and paper, prove that `fibo-from` $F_i$ $F_{i+1}$ $k$
   = $F_{i+k}$ by induction on $k$.

   > By induction on $k$. There are two base cases: when $k = 0$,
   > then `fibo-from` $F_i$ $F_{i+1}$ $0$ = $F_i$ = $F_{i+k}$; In
   > the inductive case we have $k > 0$. By definition of
   > `fibo-from` we have `fibo-from` $F_i$ $F_{i+1}$ $k$ =
   > `fibo-from` $F_{i+1}$ $F_{i+2}$ $(k-1)$. Using the induction
   > hypothesis we conclude `fibo-from` $F_{i+1}$ $F_{i+2}$ $(k-1)$
   > = $F_{i+k}$.
   {:.solution}
