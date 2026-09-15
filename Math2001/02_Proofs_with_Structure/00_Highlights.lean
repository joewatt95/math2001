/- Which examples in Chapter 2 are worth time.  Not part of Macbeth's text. -/
import Library.Basic

math2001_init

/-! # Chapter 2: what to slow down on

The sections are mechanical once the pattern is clear, so most of them can be skimmed.  What
follows is the short list of places where either the problem is genuinely hard, or the proof here
looks nothing like what the book does or what a first attempt produces.  Each entry says which of
those it is.

## 2.1 `x * y = 1`, `x ≥ 1`, therefore `y ≤ 1`  (last exercise)

*Style.*  The best single illustration of what `have` is for.  The proof opens with
`have : y > 0`, and `y > 0` is then never mentioned again, so it reads as dead code.  Delete it and
the `rel [h2]` step fails with `0 ≤ y`.  It exists to put a side condition where `rel` can find it.

Worth doing live: comment the line out, run it, read the error.  The lesson generalises to every
tactic in the book that quietly consults the context.

## 2.2 `a ^ 2 + b ^ 2 = 0`, therefore `a ^ 2 = 0`

*Style.*  The `show` lines.  A first attempt omits them, since Lean does not need them.  Swap the
two around and the error names exactly what went wrong.  This is the place to say that a `show` is
documentation the compiler checks, which is the idea the rest of the course leans on.

## 2.3 `le_or_succ_le`

*Content, and surprising.*  It looks like a lemma and is a macro, expanding to `le_or_gt` plus the
step from `n < a` to `n + 1 ≤ a`.  That step is the discreteness of the integers, and it is the
reason case analysis over `ℤ` works at all.  Try it over `ℝ` and watch it fail.

Five minutes here buys the whole of `mod_cases` later.

## 2.3 `n ^ 2 ≠ 2` over `ℤ`

*Hard, and the biggest structural contrast in the chapter.*  Two nested splits, four leaves, and at
any leaf two assumptions are live while only one is nearby.  Compare it with the `ℕ` version a page
earlier, which needs one split, and ask why the type changed the shape.

Then compare the annotated version here with an unannotated one.  This is the example that makes
the case for case labels better than any argument does.

## 2.4 `a * b = a`, `a * b = b`, therefore both are `0` or both are `1`  (last exercise)

*Hard, and a large gap from a first attempt.*  Both hypotheses have the same left side, so `a = b`
falls out in two lines, and that single fact collapses the problem.  Without it the two halves of
each conjunction are separate obligations and the proof roughly doubles.

The transferable habit is to spend a moment on the cheap consequences of the hypotheses before
choosing a strategy.

## 2.5 the taxicab example, against the last exercise

*Style, and a direct before-and-after.*  Same construction, written both ways in one file.  Four
conjuncts via `constructor` gives three levels of nesting for an argument with no depth in it.  Six
conjuncts via `⟨...⟩` stays flat.

This is where to make the general point: `constructor` imposes a layer per conjunct whether the
maths deserves one or not, and that is the clearest reason to prefer the forward order.

## 2.5 `∃ a, a * t < 0`, therefore `t ≠ 0`

*Style.*  Two things at once.  `cancel` wants the shape `0 < c * t` and refuses `x * t < 0`, which
is the general lesson that a tactic often wants the same fact in a different shape rather than a
different fact.  And the nesting follows the argument, so each branch reads as the case, the fact
that case gives, and the conclusion, with the sign manipulation tucked inside.
-/
