---
title: A taste of Agda
next:  Chapter.Preamble.Setup
---

<pre class="Agda"><a id="67" class="Keyword">module</a> <a id="74" href="Chapter.Preamble.Demo.html" class="Module">Chapter.Preamble.Demo</a> <a id="96" class="Keyword">where</a>
</pre>
## Imports

The program described in this chapter makes use of natural numbers
and of the equality predicate, whose definitions must be imported
from Agda's standard library. The directives shown below import the
necessary definitions from the Agda library. For the time being, we
will use natural numbers and equality as black boxes; we will see
how they can be defined in Agda later on.

<pre class="Agda"><a id="501" class="Keyword">open</a> <a id="506" class="Keyword">import</a> <a id="513" href="Data.Nat.html" class="Module">Data.Nat</a>
<a id="522" class="Keyword">open</a> <a id="527" class="Keyword">import</a> <a id="534" href="Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a>
<a id="554" class="Keyword">open</a> <a id="559" class="Keyword">import</a> <a id="566" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
<a id="604" class="Keyword">open</a> <a id="609" href="Relation.Binary.PropositionalEquality.Properties.html#6850" class="Module">≡-Reasoning</a>
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

<pre class="Agda"><a id="fibo"></a><a id="1133" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="1138" class="Symbol">:</a> <a id="1140" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1142" class="Symbol">-&gt;</a> <a id="1145" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="1147" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="1152" class="Number">0</a>             <a id="1166" class="Symbol">=</a> <a id="1168" class="Number">0</a>
<a id="1170" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="1175" class="Number">1</a>             <a id="1189" class="Symbol">=</a> <a id="1191" class="Number">1</a>
<a id="1193" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="1198" class="Symbol">(</a><a id="1199" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1203" class="Symbol">(</a><a id="1204" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1208" href="Chapter.Preamble.Demo.html#1208" class="Bound">k</a><a id="1209" class="Symbol">))</a> <a id="1212" class="Symbol">=</a> <a id="1214" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="1219" href="Chapter.Preamble.Demo.html#1208" class="Bound">k</a> <a id="1221" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="1223" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="1228" class="Symbol">(</a><a id="1229" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1233" href="Chapter.Preamble.Demo.html#1208" class="Bound">k</a><a id="1234" class="Symbol">)</a>
</pre>
Once this script is loaded, we can ask Agda to compute the result of
applying `fibo` to some numbers. By pressing `C-c C-n` and then
entering `fibo 10` we obtain 55, as expected. 

It is a known fact that the shown implementation of `fibo` is very
inefficient. In fact, the time for computing the k-th Fibonacci
number is exponential in k. We can propose a more efficient,
albeit slightly more complex function that computes the k-th
Fibonacci number in linear time, as follows.

<pre class="Agda"><a id="fibo-from"></a><a id="1725" href="Chapter.Preamble.Demo.html#1725" class="Function">fibo-from</a> <a id="1735" class="Symbol">:</a> <a id="1737" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1739" class="Symbol">-&gt;</a> <a id="1742" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1744" class="Symbol">-&gt;</a> <a id="1747" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1749" class="Symbol">-&gt;</a> <a id="1752" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="1754" href="Chapter.Preamble.Demo.html#1725" class="Function">fibo-from</a> <a id="1764" href="Chapter.Preamble.Demo.html#1764" class="Bound">m</a> <a id="1766" href="Chapter.Preamble.Demo.html#1766" class="Bound">n</a> <a id="1768" class="Number">0</a>       <a id="1776" class="Symbol">=</a> <a id="1778" href="Chapter.Preamble.Demo.html#1764" class="Bound">m</a>
<a id="1780" href="Chapter.Preamble.Demo.html#1725" class="Function">fibo-from</a> <a id="1790" href="Chapter.Preamble.Demo.html#1790" class="Bound">m</a> <a id="1792" href="Chapter.Preamble.Demo.html#1792" class="Bound">n</a> <a id="1794" class="Symbol">(</a><a id="1795" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1799" href="Chapter.Preamble.Demo.html#1799" class="Bound">k</a><a id="1800" class="Symbol">)</a> <a id="1802" class="Symbol">=</a> <a id="1804" href="Chapter.Preamble.Demo.html#1725" class="Function">fibo-from</a> <a id="1814" href="Chapter.Preamble.Demo.html#1792" class="Bound">n</a> <a id="1816" class="Symbol">(</a><a id="1817" href="Chapter.Preamble.Demo.html#1790" class="Bound">m</a> <a id="1819" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="1821" href="Chapter.Preamble.Demo.html#1792" class="Bound">n</a><a id="1822" class="Symbol">)</a> <a id="1824" href="Chapter.Preamble.Demo.html#1799" class="Bound">k</a>

<a id="fast-fibo"></a><a id="1827" href="Chapter.Preamble.Demo.html#1827" class="Function">fast-fibo</a> <a id="1837" class="Symbol">:</a> <a id="1839" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1841" class="Symbol">-&gt;</a> <a id="1844" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="1846" href="Chapter.Preamble.Demo.html#1827" class="Function">fast-fibo</a> <a id="1856" class="Symbol">=</a> <a id="1858" href="Chapter.Preamble.Demo.html#1725" class="Function">fibo-from</a> <a id="1868" class="Number">0</a> <a id="1870" class="Number">1</a>
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

<pre class="Agda"><a id="lemma"></a><a id="4400" href="Chapter.Preamble.Demo.html#4400" class="Function">lemma</a> <a id="4406" class="Symbol">:</a> <a id="4408" class="Symbol">∀(</a><a id="4410" href="Chapter.Preamble.Demo.html#4410" class="Bound">k</a> <a id="4412" href="Chapter.Preamble.Demo.html#4412" class="Bound">i</a> <a id="4414" class="Symbol">:</a> <a id="4416" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="4417" class="Symbol">)</a> <a id="4419" class="Symbol">-&gt;</a> <a id="4422" href="Chapter.Preamble.Demo.html#1725" class="Function">fibo-from</a> <a id="4432" class="Symbol">(</a><a id="4433" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4438" href="Chapter.Preamble.Demo.html#4410" class="Bound">k</a><a id="4439" class="Symbol">)</a> <a id="4441" class="Symbol">(</a><a id="4442" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4447" class="Symbol">(</a><a id="4448" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4452" href="Chapter.Preamble.Demo.html#4410" class="Bound">k</a><a id="4453" class="Symbol">))</a> <a id="4456" href="Chapter.Preamble.Demo.html#4412" class="Bound">i</a> <a id="4458" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4460" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4465" class="Symbol">(</a><a id="4466" href="Chapter.Preamble.Demo.html#4412" class="Bound">i</a> <a id="4468" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4470" href="Chapter.Preamble.Demo.html#4410" class="Bound">k</a><a id="4471" class="Symbol">)</a>
<a id="4473" href="Chapter.Preamble.Demo.html#4400" class="Function">lemma</a> <a id="4479" href="Chapter.Preamble.Demo.html#4479" class="Bound">k</a> <a id="4481" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="4486" class="Symbol">=</a> <a id="4488" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="4493" href="Chapter.Preamble.Demo.html#4400" class="Function">lemma</a> <a id="4499" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a> <a id="4501" class="Symbol">(</a><a id="4502" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4506" href="Chapter.Preamble.Demo.html#4506" class="Bound">i</a><a id="4507" class="Symbol">)</a> <a id="4509" class="Symbol">=</a>
  <a id="4513" href="Relation.Binary.Reasoning.Syntax.html#1572" class="Function Operator">begin</a>
    <a id="4523" href="Chapter.Preamble.Demo.html#1725" class="Function">fibo-from</a> <a id="4533" class="Symbol">(</a><a id="4534" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4539" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a><a id="4540" class="Symbol">)</a> <a id="4542" class="Symbol">(</a><a id="4543" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4548" class="Symbol">(</a><a id="4549" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4553" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a><a id="4554" class="Symbol">))</a> <a id="4557" class="Symbol">(</a><a id="4558" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4562" href="Chapter.Preamble.Demo.html#4506" class="Bound">i</a><a id="4563" class="Symbol">)</a> <a id="4565" href="Relation.Binary.Reasoning.Syntax.html#11079" class="Function">≡⟨⟩</a>
    <a id="4573" href="Chapter.Preamble.Demo.html#1725" class="Function">fibo-from</a> <a id="4583" class="Symbol">(</a><a id="4584" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4589" class="Symbol">(</a><a id="4590" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4594" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a><a id="4595" class="Symbol">))</a> <a id="4598" class="Symbol">(</a><a id="4599" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4604" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a> <a id="4606" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4608" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4613" class="Symbol">(</a><a id="4614" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4618" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a><a id="4619" class="Symbol">))</a> <a id="4622" href="Chapter.Preamble.Demo.html#4506" class="Bound">i</a> <a id="4624" href="Relation.Binary.Reasoning.Syntax.html#11079" class="Function">≡⟨⟩</a>
    <a id="4632" href="Chapter.Preamble.Demo.html#1725" class="Function">fibo-from</a> <a id="4642" class="Symbol">(</a><a id="4643" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4648" class="Symbol">(</a><a id="4649" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4653" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a><a id="4654" class="Symbol">))</a> <a id="4657" class="Symbol">(</a><a id="4658" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4663" class="Symbol">(</a><a id="4664" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4668" class="Symbol">(</a><a id="4669" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4673" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a><a id="4674" class="Symbol">)))</a> <a id="4678" href="Chapter.Preamble.Demo.html#4506" class="Bound">i</a>
      <a id="4686" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">≡⟨</a> <a id="4689" href="Chapter.Preamble.Demo.html#4400" class="Function">lemma</a> <a id="4695" class="Symbol">(</a><a id="4696" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4700" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a><a id="4701" class="Symbol">)</a> <a id="4703" href="Chapter.Preamble.Demo.html#4506" class="Bound">i</a> <a id="4705" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">⟩</a>
    <a id="4711" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4716" class="Symbol">(</a><a id="4717" href="Chapter.Preamble.Demo.html#4506" class="Bound">i</a> <a id="4719" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4721" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4725" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a><a id="4726" class="Symbol">)</a>
      <a id="4734" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">≡⟨</a> <a id="4737" href="Relation.Binary.PropositionalEquality.Core.html#1481" class="Function">cong</a> <a id="4742" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4747" class="Symbol">(</a><a id="4748" href="Data.Nat.Properties.html#15415" class="Function">+-suc</a> <a id="4754" href="Chapter.Preamble.Demo.html#4506" class="Bound">i</a> <a id="4756" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a><a id="4757" class="Symbol">)</a> <a id="4759" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">⟩</a>
    <a id="4765" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4770" class="Symbol">(</a><a id="4771" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="4775" href="Chapter.Preamble.Demo.html#4506" class="Bound">i</a> <a id="4777" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4779" href="Chapter.Preamble.Demo.html#4499" class="Bound">k</a><a id="4780" class="Symbol">)</a>
  <a id="4784" href="Relation.Binary.Reasoning.Syntax.html#12345" class="Function Operator">∎</a>

<a id="theorem"></a><a id="4787" href="Chapter.Preamble.Demo.html#4787" class="Function">theorem</a> <a id="4795" class="Symbol">:</a> <a id="4797" class="Symbol">∀(</a><a id="4799" href="Chapter.Preamble.Demo.html#4799" class="Bound">k</a> <a id="4801" class="Symbol">:</a> <a id="4803" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="4804" class="Symbol">)</a> <a id="4806" class="Symbol">-&gt;</a> <a id="4809" href="Chapter.Preamble.Demo.html#1827" class="Function">fast-fibo</a> <a id="4819" href="Chapter.Preamble.Demo.html#4799" class="Bound">k</a> <a id="4821" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4823" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4828" href="Chapter.Preamble.Demo.html#4799" class="Bound">k</a>
<a id="4830" href="Chapter.Preamble.Demo.html#4787" class="Function">theorem</a> <a id="4838" href="Chapter.Preamble.Demo.html#4838" class="Bound">k</a> <a id="4840" class="Symbol">=</a>
  <a id="4844" href="Relation.Binary.Reasoning.Syntax.html#1572" class="Function Operator">begin</a>
    <a id="4854" href="Chapter.Preamble.Demo.html#1827" class="Function">fast-fibo</a> <a id="4864" href="Chapter.Preamble.Demo.html#4838" class="Bound">k</a>     <a id="4870" href="Relation.Binary.Reasoning.Syntax.html#11079" class="Function">≡⟨⟩</a>
    <a id="4878" href="Chapter.Preamble.Demo.html#1725" class="Function">fibo-from</a> <a id="4888" class="Number">0</a> <a id="4890" class="Number">1</a> <a id="4892" href="Chapter.Preamble.Demo.html#4838" class="Bound">k</a> <a id="4894" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">≡⟨</a> <a id="4897" href="Chapter.Preamble.Demo.html#4400" class="Function">lemma</a> <a id="4903" class="Number">0</a> <a id="4905" href="Chapter.Preamble.Demo.html#4838" class="Bound">k</a> <a id="4907" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">⟩</a>
    <a id="4913" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4918" class="Symbol">(</a><a id="4919" href="Chapter.Preamble.Demo.html#4838" class="Bound">k</a> <a id="4921" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4923" class="Number">0</a><a id="4924" class="Symbol">)</a>    <a id="4929" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">≡⟨</a> <a id="4932" href="Relation.Binary.PropositionalEquality.Core.html#1481" class="Function">cong</a> <a id="4937" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4942" class="Symbol">(</a><a id="4943" href="Data.Nat.Properties.html#15779" class="Function">+-identityʳ</a> <a id="4955" href="Chapter.Preamble.Demo.html#4838" class="Bound">k</a><a id="4956" class="Symbol">)</a> <a id="4958" href="Relation.Binary.Reasoning.Syntax.html#11048" class="Function">⟩</a>
    <a id="4964" href="Chapter.Preamble.Demo.html#1133" class="Function">fibo</a> <a id="4969" href="Chapter.Preamble.Demo.html#4838" class="Bound">k</a>
  <a id="4973" href="Relation.Binary.Reasoning.Syntax.html#12345" class="Function Operator">∎</a>
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
