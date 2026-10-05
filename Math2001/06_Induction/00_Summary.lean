/- A summary of Chapter 6, written for this course.  Not part of Macbeth's text. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Chapter 6 on one page

## One idea, five packagings

    simple_induction n with k IH                      base `0`, step `k` to `k + 1`
    induction_from_starting_point n, hn with k hk IH  base `C`, and `hk : C ≤ k` in the step
    two_step_induction n with k IH1 IH2               bases `0` and `1`, step reaches back two
    two_step_induction_from_starting_point            the same, from `C`
    the theorem quoting itself at a smaller argument  reach back as far as you like

The last line is the whole subject.  A proof may use the statement it is proving at any smaller
argument, and the four tactics are prepackaged cases of that.  Section 6.4 drops the packaging,
which is what lets `exists_prime_factor` recurse on a factor whose size it does not control.

## The shape of an inductive step

Peel, substitute, tidy.  The goal mentions `k + 1` and the hypothesis mentions `k`, so the first
`calc` step separates one factor off, `2 ^ (k + 1) = 2 * 2 ^ k`, which is what gives `rel [IH]`
something to act on.  The rest is algebra.

Write the chain from both ends and find the middle by subtracting on paper.  `extra` closes
exactly the goals of the form "what I want, plus something nonnegative", so the step before it is
always a `ring` that puts the goal on the left and the slack on the right.

## Picking a starting point

`forall_sufficiently_large n, P n` is `∃ C, ∀ n ≥ C, P n`, so you choose `C`.  Two things
constrain it and the second is easy to forget: the base case has to hold, *and* the inductive step
has to go through from `C ≤ k`.  The `#eval`s in the text are there to find the crossover.  With a
two-step induction you owe two base cases, at `C` and `C + 1`.

## A statement that is too weak to prove

The best idea in the chapter, from Section 6.3.  `a m ≡ 1 ∨ a m ≡ 5 [ZMOD 6]` cannot be proved by
induction: knowing that each of `a k` and `a (k + 1)` lies in `{1, 5}` leaves combinations that put
`a (k + 2)` outside it.  What is true, and provable, is that the *pair* is `(1, 5)` or `(5, 1)`.

The stronger statement is the easier one, because it gives more to work with as well as more to
prove.  Finding it means computing the first several terms and watching the pairs cycle.  In one
of the exercises the cycle has length three.

## A recursive definition is a rewrite rule

`rw [b]` replaces `b (k + 1)` by its defining right-hand side.  That move opens nearly every proof
in Sections 6.2 and 6.5 to 6.7.

Termination comes with it.  `pascal` recurses on two arguments and neither shrinks alone, so
`termination_by a b => a + b` names the quantity that does, and every proof by the same recursion
repeats it.  `fmod` needs a `decreasing_by` block as well, which each proof copies from the
definition.  `gcd` needs none, because the four `@[decreasing]` lemmas above it put the bounds on
`fmod` where the termination checker looks.

## Five traps

**`ℕ` subtraction is truncated.**  `3 - 5` is `0`.  Never write a slack term as a difference.
Bound the larger quantity below first, so that the slack comes out as a numeral.

**`rw [f]` takes the first clause that matches anywhere.**  `rw [factorial]` on
`(0 + 1)! = (0 + 1) * 0 !` fires on the `0 !` you wrote on the right, not the term on the left.
Unfold all the way to a numeral instead.

**`n !` reads past the end of the line.**  `use k !` followed by a line starting `rw` parses as
`k` applied to `!rw [...]`.  Write `use (k !)`.

**One bullet where you expected two.**  The induction tactics run `push_cast` on every goal, and
on a numerical base case that sometimes finishes it.

**Coercions.**  `F n` is an integer and `0.5 * 1.7 ^ n` is a rational, so the real goal has a `↑`
in it.  `ring`, `rel` and `extra` work around it.  `rw` has to happen underneath it, so unfold in
a `have` of its own and let `norm_cast` move the coercion.
-/
