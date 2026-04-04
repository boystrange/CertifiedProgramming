---
title: Polymorphic functions and implicit arguments
next:  Chapter.Intro.Lists
prev:  Chapter.Intro.NaturalNumbers
---

<pre class="Agda"><a id="129" class="Keyword">module</a> <a id="136" href="Chapter.Intro.Polymorphism.html" class="Module">Chapter.Intro.Polymorphism</a> <a id="163" class="Keyword">where</a>
</pre>
In this chapter we study Agda's support for **polymorphism**, namely
the ability of some functions to be applied to arguments of
different types.

## Imports

<pre class="Agda"><a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="Data.Bool.html" class="Module">Data.Bool</a>
<a id="359" class="Keyword">open</a> <a id="364" class="Keyword">import</a> <a id="371" href="Data.Nat.html" class="Module">Data.Nat</a>
</pre>
## Polymorphic functions

The behavior of some functions does not depend on any particular
property of their argument. The simplest example of function with
such property is that of the **identity function**, which always
yields the value of its argument. We may conceive several versions
of the identity function, depending on the type of its argument.

<pre class="Agda"><a id="id₁"></a><a id="744" href="Chapter.Intro.Polymorphism.html#744" class="Function">id₁</a> <a id="748" class="Symbol">:</a> <a id="750" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a> <a id="755" class="Symbol">-&gt;</a> <a id="758" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a>
<a id="763" href="Chapter.Intro.Polymorphism.html#744" class="Function">id₁</a> <a id="767" href="Chapter.Intro.Polymorphism.html#767" class="Bound">x</a> <a id="769" class="Symbol">=</a> <a id="771" href="Chapter.Intro.Polymorphism.html#767" class="Bound">x</a>

<a id="id₂"></a><a id="774" href="Chapter.Intro.Polymorphism.html#774" class="Function">id₂</a> <a id="778" class="Symbol">:</a> <a id="780" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="782" class="Symbol">-&gt;</a> <a id="785" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="787" href="Chapter.Intro.Polymorphism.html#774" class="Function">id₂</a> <a id="791" href="Chapter.Intro.Polymorphism.html#791" class="Bound">x</a> <a id="793" class="Symbol">=</a> <a id="795" href="Chapter.Intro.Polymorphism.html#791" class="Bound">x</a>

<a id="id₃"></a><a id="798" href="Chapter.Intro.Polymorphism.html#798" class="Function">id₃</a> <a id="802" class="Symbol">:</a> <a id="804" class="Symbol">(</a><a id="805" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="807" class="Symbol">-&gt;</a> <a id="810" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="814" class="Symbol">)</a> <a id="816" class="Symbol">-&gt;</a> <a id="819" class="Symbol">(</a><a id="820" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="822" class="Symbol">-&gt;</a> <a id="825" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="829" class="Symbol">)</a>
<a id="831" href="Chapter.Intro.Polymorphism.html#798" class="Function">id₃</a> <a id="835" href="Chapter.Intro.Polymorphism.html#835" class="Bound">x</a> <a id="837" class="Symbol">=</a> <a id="839" href="Chapter.Intro.Polymorphism.html#835" class="Bound">x</a>
</pre>
Depending on the type of the argument, we would use one version or
the other: if we want to apply the identity function to a boolean
value, then we would use `id₁`; if we want to apply the identity
function to a natural number, then we would use `id₂`; and so on and
so forth.

<pre class="Agda"><a id="1128" href="Chapter.Intro.Polymorphism.html#1128" class="Function">_</a> <a id="1130" class="Symbol">:</a> <a id="1132" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a>
<a id="1137" class="Symbol">_</a> <a id="1139" class="Symbol">=</a> <a id="1141" href="Chapter.Intro.Polymorphism.html#744" class="Function">id₁</a> <a id="1145" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>

<a id="1151" href="Chapter.Intro.Polymorphism.html#1151" class="Function">_</a> <a id="1153" class="Symbol">:</a> <a id="1155" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="1157" class="Symbol">_</a> <a id="1159" class="Symbol">=</a> <a id="1161" href="Chapter.Intro.Polymorphism.html#774" class="Function">id₂</a> <a id="1165" class="Number">42</a>
</pre>
The definitions `id₁`, `id₂`, ... of the identity function differ in
the type of their argument, but behave in exactly the same
way. Clearly, it would be desirable to define the identity function
once and for all, and make it applicable to arguments of different
types. In Agda this is made possible by the dependent arrow type.

<pre class="Agda"><a id="id₄"></a><a id="1507" href="Chapter.Intro.Polymorphism.html#1507" class="Function">id₄</a> <a id="1511" class="Symbol">:</a> <a id="1513" class="Symbol">∀(</a><a id="1515" href="Chapter.Intro.Polymorphism.html#1515" class="Bound">A</a> <a id="1517" class="Symbol">:</a> <a id="1519" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="1522" class="Symbol">)</a> <a id="1524" class="Symbol">-&gt;</a> <a id="1527" href="Chapter.Intro.Polymorphism.html#1515" class="Bound">A</a> <a id="1529" class="Symbol">-&gt;</a> <a id="1532" href="Chapter.Intro.Polymorphism.html#1515" class="Bound">A</a>
<a id="1534" href="Chapter.Intro.Polymorphism.html#1507" class="Function">id₄</a> <a id="1538" href="Chapter.Intro.Polymorphism.html#1538" class="Bound">A</a> <a id="1540" href="Chapter.Intro.Polymorphism.html#1540" class="Bound">x</a> <a id="1542" class="Symbol">=</a> <a id="1544" href="Chapter.Intro.Polymorphism.html#1540" class="Bound">x</a>
</pre>
Note that the domain of `id₄` is some `Set` `A` (that is, `A` is a
type in Agda's terminology) and the codomain of `id₄` is the type `A
-> A`. Basically, we have turned the one-argument, monomorphic
identity function into a two-arguments, polymorphic identity
function where the first argument is the type of the second
argument. We can now use `id₄` in different places with different
argument types.

<pre class="Agda"><a id="1958" href="Chapter.Intro.Polymorphism.html#1958" class="Function">_</a> <a id="1960" class="Symbol">:</a> <a id="1962" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a>
<a id="1967" class="Symbol">_</a> <a id="1969" class="Symbol">=</a> <a id="1971" href="Chapter.Intro.Polymorphism.html#1507" class="Function">id₄</a> <a id="1975" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a> <a id="1980" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>

<a id="1986" href="Chapter.Intro.Polymorphism.html#1986" class="Function">_</a> <a id="1988" class="Symbol">:</a> <a id="1990" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="1992" class="Symbol">_</a> <a id="1994" class="Symbol">=</a> <a id="1996" href="Chapter.Intro.Polymorphism.html#1507" class="Function">id₄</a> <a id="2000" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="2002" class="Number">42</a>
</pre>
## Implicit arguments

You may have noticed that the argument `A` in the definition of
`id₄` plays no role in the definition of `id₄`. In fact, that
argument is somewhat *redundant* since it must coincide with the
type of `x`, the second argument of `id₄`. We can verify this
redundancy in practice by observing that Agda can automatically
*infer* the type of the first argument whenever we provide the
second one.

<pre class="Agda"><a id="2430" href="Chapter.Intro.Polymorphism.html#2430" class="Function">_</a> <a id="2432" class="Symbol">:</a> <a id="2434" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a>
<a id="2439" class="Symbol">_</a> <a id="2441" class="Symbol">=</a> <a id="2443" href="Chapter.Intro.Polymorphism.html#1507" class="Function">id₄</a> <a id="2447" class="Symbol">_</a> <a id="2449" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>

<a id="2455" href="Chapter.Intro.Polymorphism.html#2455" class="Function">_</a> <a id="2457" class="Symbol">:</a> <a id="2459" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="2461" class="Symbol">_</a> <a id="2463" class="Symbol">=</a> <a id="2465" href="Chapter.Intro.Polymorphism.html#1507" class="Function">id₄</a> <a id="2469" class="Symbol">_</a> <a id="2471" class="Number">42</a>
</pre>
In these definitions, the underscore `_` stands for an expression
that we ask Agda to automatically infer. Of course, not everything
can be inferred automatically, or else there would be no point in
learning how to program in Agda. In the particular case of `id₄`,
however, the term that is meant to replace the underscore is
uniquely determined by the second argument: since `true` has type
`Bool`, the first underscore must be replaced by `Bool`; since `42`
has type `ℕ`, the second underscore must be replaced by `ℕ`. This
fact makes `id₄` slightly annoying to use, since the programmer is
required to systematically provide an argument that Agda can infer
by itself. In the end, the programmer will typically apply `id₄` to
an underscore followed by the actual argument. We can spare this
burden to the programmer by declaring that the first argument of
`id₄` is **implicit**. As the name suggests, implicit arguments can
be omitted in the program since they are supposed to be inferred
automatically. An implicit argument is declared using braces `{...}`
instead of parentheses `(...)`. So, the final version of the
polymorphic identity function with implicit arguments is the
following.

<pre class="Agda"><a id="id"></a><a id="3677" href="Chapter.Intro.Polymorphism.html#3677" class="Function">id</a> <a id="3680" class="Symbol">:</a> <a id="3682" class="Symbol">∀{</a><a id="3684" href="Chapter.Intro.Polymorphism.html#3684" class="Bound">A</a> <a id="3686" class="Symbol">:</a> <a id="3688" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3691" class="Symbol">}</a> <a id="3693" class="Symbol">-&gt;</a> <a id="3696" href="Chapter.Intro.Polymorphism.html#3684" class="Bound">A</a> <a id="3698" class="Symbol">-&gt;</a> <a id="3701" href="Chapter.Intro.Polymorphism.html#3684" class="Bound">A</a>
<a id="3703" href="Chapter.Intro.Polymorphism.html#3677" class="Function">id</a> <a id="3706" href="Chapter.Intro.Polymorphism.html#3706" class="Bound">x</a> <a id="3708" class="Symbol">=</a> <a id="3710" href="Chapter.Intro.Polymorphism.html#3706" class="Bound">x</a>
</pre>
Notice that the implicit argument is also omitted in the very
definition of `id`. Now, we can apply `id` to whatever argument we
like, without explicitly supplying its type.

<pre class="Agda"><a id="3896" href="Chapter.Intro.Polymorphism.html#3896" class="Function">_</a> <a id="3898" class="Symbol">:</a> <a id="3900" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a>
<a id="3905" class="Symbol">_</a> <a id="3907" class="Symbol">=</a> <a id="3909" href="Chapter.Intro.Polymorphism.html#3677" class="Function">id</a> <a id="3912" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>

<a id="3918" href="Chapter.Intro.Polymorphism.html#3918" class="Function">_</a> <a id="3920" class="Symbol">:</a> <a id="3922" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="3924" class="Symbol">_</a> <a id="3926" class="Symbol">=</a> <a id="3928" href="Chapter.Intro.Polymorphism.html#3677" class="Function">id</a> <a id="3931" class="Number">42</a>
</pre>
There are cases in which Agda is not able to automatically infer an
implicit. In these cases, we can supply it explicitly, by placing
the implicit argument within braces.

<pre class="Agda"><a id="4115" href="Chapter.Intro.Polymorphism.html#4115" class="Function">_</a> <a id="4117" class="Symbol">:</a> <a id="4119" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a>
<a id="4124" class="Symbol">_</a> <a id="4126" class="Symbol">=</a> <a id="4128" href="Chapter.Intro.Polymorphism.html#3677" class="Function">id</a> <a id="4131" class="Symbol">{</a><a id="4132" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="4136" class="Symbol">}</a> <a id="4138" href="Agda.Builtin.Bool.html#198" class="InductiveConstructor">true</a>

<a id="4144" href="Chapter.Intro.Polymorphism.html#4144" class="Function">_</a> <a id="4146" class="Symbol">:</a> <a id="4148" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a>
<a id="4150" class="Symbol">_</a> <a id="4152" class="Symbol">=</a> <a id="4154" href="Chapter.Intro.Polymorphism.html#3677" class="Function">id</a> <a id="4157" class="Symbol">{</a><a id="4158" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="4159" class="Symbol">}</a> <a id="4161" class="Number">42</a>
</pre>
Similarly, we can name the implicit argument when defining the
function, in case it is needed in the body of the function.

<pre class="Agda"><a id="id₅"></a><a id="4297" href="Chapter.Intro.Polymorphism.html#4297" class="Function">id₅</a> <a id="4301" class="Symbol">:</a> <a id="4303" class="Symbol">∀{</a><a id="4305" href="Chapter.Intro.Polymorphism.html#4305" class="Bound">A</a> <a id="4307" class="Symbol">:</a> <a id="4309" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4312" class="Symbol">}</a> <a id="4314" class="Symbol">-&gt;</a> <a id="4317" href="Chapter.Intro.Polymorphism.html#4305" class="Bound">A</a> <a id="4319" class="Symbol">-&gt;</a> <a id="4322" href="Chapter.Intro.Polymorphism.html#4305" class="Bound">A</a>
<a id="4324" href="Chapter.Intro.Polymorphism.html#4297" class="Function">id₅</a> <a id="4328" class="Symbol">{</a><a id="4329" href="Chapter.Intro.Polymorphism.html#4329" class="Bound">A</a><a id="4330" class="Symbol">}</a> <a id="4332" href="Chapter.Intro.Polymorphism.html#4332" class="Bound">x</a> <a id="4334" class="Symbol">=</a> <a id="4336" href="Chapter.Intro.Polymorphism.html#4332" class="Bound">x</a>
</pre>
There is no general guideline to establish whether an argument
should be explicit or implicit. As a rule of thumb, an argument can
be declared implicit if it also occurs later in the same type. We
will see systematic applications of this rule in the next chapters,
as we make greater use of dependent types.

## Exercises

1. Implement the function `flip : ∀{A B C : Set} -> (A -> B -> C) -> B -> A -> C`.
2. Implement the function `_∘_ : ∀{A B C : Set} -> (B -> C) -> (A -> B) -> A -> C`.
3. Provide two syntactically different (but equivalent)
   implementations of the function `apply : ∀{A B : Set} -> (A -> B) -> A -> B`.

<pre class="Agda"><a id="flip"></a><a id="4979" href="Chapter.Intro.Polymorphism.html#4979" class="Function">flip</a> <a id="4984" class="Symbol">:</a> <a id="4986" class="Symbol">∀{</a><a id="4988" href="Chapter.Intro.Polymorphism.html#4988" class="Bound">A</a> <a id="4990" href="Chapter.Intro.Polymorphism.html#4990" class="Bound">B</a> <a id="4992" href="Chapter.Intro.Polymorphism.html#4992" class="Bound">C</a> <a id="4994" class="Symbol">:</a> <a id="4996" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4999" class="Symbol">}</a> <a id="5001" class="Symbol">-&gt;</a> <a id="5004" class="Symbol">(</a><a id="5005" href="Chapter.Intro.Polymorphism.html#4988" class="Bound">A</a> <a id="5007" class="Symbol">-&gt;</a> <a id="5010" href="Chapter.Intro.Polymorphism.html#4990" class="Bound">B</a> <a id="5012" class="Symbol">-&gt;</a> <a id="5015" href="Chapter.Intro.Polymorphism.html#4992" class="Bound">C</a><a id="5016" class="Symbol">)</a> <a id="5018" class="Symbol">-&gt;</a> <a id="5021" href="Chapter.Intro.Polymorphism.html#4990" class="Bound">B</a> <a id="5023" class="Symbol">-&gt;</a> <a id="5026" href="Chapter.Intro.Polymorphism.html#4988" class="Bound">A</a> <a id="5028" class="Symbol">-&gt;</a> <a id="5031" href="Chapter.Intro.Polymorphism.html#4992" class="Bound">C</a>
<a id="5033" href="Chapter.Intro.Polymorphism.html#4979" class="Function">flip</a> <a id="5038" class="Symbol">=</a> <a id="5040" class="Symbol">λ</a> <a id="5042" href="Chapter.Intro.Polymorphism.html#5042" class="Bound">f</a> <a id="5044" href="Chapter.Intro.Polymorphism.html#5044" class="Bound">x</a> <a id="5046" href="Chapter.Intro.Polymorphism.html#5046" class="Bound">y</a> <a id="5048" class="Symbol">-&gt;</a> <a id="5051" href="Chapter.Intro.Polymorphism.html#5042" class="Bound">f</a> <a id="5053" href="Chapter.Intro.Polymorphism.html#5046" class="Bound">y</a> <a id="5055" href="Chapter.Intro.Polymorphism.html#5044" class="Bound">x</a>

<a id="_∘_"></a><a id="5058" href="Chapter.Intro.Polymorphism.html#5058" class="Function Operator">_∘_</a> <a id="5062" class="Symbol">:</a> <a id="5064" class="Symbol">∀{</a><a id="5066" href="Chapter.Intro.Polymorphism.html#5066" class="Bound">A</a> <a id="5068" href="Chapter.Intro.Polymorphism.html#5068" class="Bound">B</a> <a id="5070" href="Chapter.Intro.Polymorphism.html#5070" class="Bound">C</a> <a id="5072" class="Symbol">:</a> <a id="5074" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5077" class="Symbol">}</a> <a id="5079" class="Symbol">-&gt;</a> <a id="5082" class="Symbol">(</a><a id="5083" href="Chapter.Intro.Polymorphism.html#5068" class="Bound">B</a> <a id="5085" class="Symbol">-&gt;</a> <a id="5088" href="Chapter.Intro.Polymorphism.html#5070" class="Bound">C</a><a id="5089" class="Symbol">)</a> <a id="5091" class="Symbol">-&gt;</a> <a id="5094" class="Symbol">(</a><a id="5095" href="Chapter.Intro.Polymorphism.html#5066" class="Bound">A</a> <a id="5097" class="Symbol">-&gt;</a> <a id="5100" href="Chapter.Intro.Polymorphism.html#5068" class="Bound">B</a><a id="5101" class="Symbol">)</a> <a id="5103" class="Symbol">-&gt;</a> <a id="5106" href="Chapter.Intro.Polymorphism.html#5066" class="Bound">A</a> <a id="5108" class="Symbol">-&gt;</a> <a id="5111" href="Chapter.Intro.Polymorphism.html#5070" class="Bound">C</a>
<a id="5113" href="Chapter.Intro.Polymorphism.html#5113" class="Bound">f</a> <a id="5115" href="Chapter.Intro.Polymorphism.html#5058" class="Function Operator">∘</a> <a id="5117" href="Chapter.Intro.Polymorphism.html#5117" class="Bound">g</a> <a id="5119" class="Symbol">=</a> <a id="5121" class="Symbol">λ</a> <a id="5123" href="Chapter.Intro.Polymorphism.html#5123" class="Bound">x</a> <a id="5125" class="Symbol">-&gt;</a> <a id="5128" href="Chapter.Intro.Polymorphism.html#5113" class="Bound">f</a> <a id="5130" class="Symbol">(</a><a id="5131" href="Chapter.Intro.Polymorphism.html#5117" class="Bound">g</a> <a id="5133" href="Chapter.Intro.Polymorphism.html#5123" class="Bound">x</a><a id="5134" class="Symbol">)</a>

<a id="5137" class="Comment">-- the first version of apply follows from the definition of</a>
<a id="5198" class="Comment">-- function application</a>

<a id="apply₁"></a><a id="5223" href="Chapter.Intro.Polymorphism.html#5223" class="Function">apply₁</a> <a id="5230" class="Symbol">:</a> <a id="5232" class="Symbol">∀{</a><a id="5234" href="Chapter.Intro.Polymorphism.html#5234" class="Bound">A</a> <a id="5236" href="Chapter.Intro.Polymorphism.html#5236" class="Bound">B</a> <a id="5238" class="Symbol">:</a> <a id="5240" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5243" class="Symbol">}</a> <a id="5245" class="Symbol">-&gt;</a> <a id="5248" class="Symbol">(</a><a id="5249" href="Chapter.Intro.Polymorphism.html#5234" class="Bound">A</a> <a id="5251" class="Symbol">-&gt;</a> <a id="5254" href="Chapter.Intro.Polymorphism.html#5236" class="Bound">B</a><a id="5255" class="Symbol">)</a> <a id="5257" class="Symbol">-&gt;</a> <a id="5260" href="Chapter.Intro.Polymorphism.html#5234" class="Bound">A</a> <a id="5262" class="Symbol">-&gt;</a> <a id="5265" href="Chapter.Intro.Polymorphism.html#5236" class="Bound">B</a>
<a id="5267" href="Chapter.Intro.Polymorphism.html#5223" class="Function">apply₁</a> <a id="5274" href="Chapter.Intro.Polymorphism.html#5274" class="Bound">f</a> <a id="5276" href="Chapter.Intro.Polymorphism.html#5276" class="Bound">x</a> <a id="5278" class="Symbol">=</a> <a id="5280" href="Chapter.Intro.Polymorphism.html#5274" class="Bound">f</a> <a id="5282" href="Chapter.Intro.Polymorphism.html#5276" class="Bound">x</a>

<a id="5285" class="Comment">-- the second version of apply is just a specialized identity</a>
<a id="5347" class="Comment">-- function</a>

<a id="apply₂"></a><a id="5360" href="Chapter.Intro.Polymorphism.html#5360" class="Function">apply₂</a> <a id="5367" class="Symbol">:</a> <a id="5369" class="Symbol">∀{</a><a id="5371" href="Chapter.Intro.Polymorphism.html#5371" class="Bound">A</a> <a id="5373" href="Chapter.Intro.Polymorphism.html#5373" class="Bound">B</a> <a id="5375" class="Symbol">:</a> <a id="5377" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5380" class="Symbol">}</a> <a id="5382" class="Symbol">-&gt;</a> <a id="5385" class="Symbol">(</a><a id="5386" href="Chapter.Intro.Polymorphism.html#5371" class="Bound">A</a> <a id="5388" class="Symbol">-&gt;</a> <a id="5391" href="Chapter.Intro.Polymorphism.html#5373" class="Bound">B</a><a id="5392" class="Symbol">)</a> <a id="5394" class="Symbol">-&gt;</a> <a id="5397" href="Chapter.Intro.Polymorphism.html#5371" class="Bound">A</a> <a id="5399" class="Symbol">-&gt;</a> <a id="5402" href="Chapter.Intro.Polymorphism.html#5373" class="Bound">B</a>
<a id="5404" href="Chapter.Intro.Polymorphism.html#5360" class="Function">apply₂</a> <a id="5411" href="Chapter.Intro.Polymorphism.html#5411" class="Bound">x</a> <a id="5413" class="Symbol">=</a> <a id="5415" href="Chapter.Intro.Polymorphism.html#5411" class="Bound">x</a>
</pre>{:.solution}
