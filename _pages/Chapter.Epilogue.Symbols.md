---
title: Summary of symbols
prev:  Chapter.Epilogue.Emacs
---

<pre class="Agda"><a id="70" class="Keyword">module</a> <a id="77" href="Chapter.Epilogue.Symbols.html" class="Module">Chapter.Epilogue.Symbols</a> <a id="102" class="Keyword">where</a>
</pre>
## Ligatures

These pages make use of the [Fira
Code](https://github.com/tonsky/FiraCode) font to display Agda
code. This font is particularly well suited for writing programs
since it supports a number of **ligatures** that make it possible to
display certain character sequences as if they were a single
glyph. A recurring example of ligature is that combining the
character `-` (the minus sign) followed by the character `>` (the
"greater than" sign), which in most fonts is displayed simply as
`-``>` whereas using Fira Code it is displayed as `->`. In other
circumstances, when there is no sequence of characters that produces
the desired ligature, we will use **Unicode characters**. A typical
example is that of the character U+2115 corresponding to the glyph
`ℕ`, which normally denotes the set of natural numbers.

## Unicode characters

The use of ligatures and of Unicode characters makes the code easier
and more pleasant to read, but it may make it more difficult to type
as it is not always clear which sequence of characters may produce a
given ligature or glyph. One possibility is to **cut and paste** the
desired symbols from these pages. Alternatively, when editing Agda
scripts in an editor that supports Agda (and that is possibly
configured to use Fira Code), special symbols can be entered by
typing particular sequences of characters. Below is a summary of the
ligatures and Unicode symbols that occur most frequently in these
pages. The [Fira Code](https://github.com/tonsky/FiraCode) page
contains a full table listing all of the ligatures supported by the
font.

| **Symbol**         | **Typed with**           |
|:-------------------|--------------------------|
| `->`               | `-``>` or `\to`          |
| `≡` and `≢`        | `\==` and `\==n`         |
| `ℕ`                | `\bN`                    |
| `∀` and `∃`        | `\all` and `\ex`         |
| `⟨` and `⟩`        | `\<` or `\langle` and `\>` or `\rangle` |
| `λ`                | `\lambda`                |
| `₀`, `₁`, `₂`, ... | `\_0`, `\_1`, `\_2`, ... |
| `∘`                | `\circ`                  |
| `∷`                | `\::`                    |
| `++`               | `+``+`                   |
| `∧` and `∨`        | `\and` and `\or`         |
| `⊤` and `⊥`        | `\top` and `\bot`        |
| `¬`                | `\neg`                   |
| `Σ`                | `\Sigma`                 |
| `×`                | `\x`                     |
<<<<<<< HEAD
| `⁺`                | `\^+`                    |
| `ʳ`                | `\^r`                    |
| `∷`                | `\::`                    |
=======
| `⁺` and `⁻`        | `\^+` and `\^-`          |
| `ʳ` and `ˡ`        | `\^r` and `\^l`          |
| `∎`                | `\qed`                   |
>>>>>>> a71c8968fa56a996de41c1d12c86fc8e63140fcb
