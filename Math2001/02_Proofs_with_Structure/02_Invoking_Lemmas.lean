/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  The new move, and the one the section is named for.  Until now every goal was closed by
computing.  Here you instead find a library lemma whose conclusion has the shape of your goal,
`apply` it, and are left proving that lemma's hypotheses.  `ne_of_lt` says `a < b → a ≠ b`, so
`apply ne_of_lt` turns the goal `x ≠ 1` into `x < 1`.

Two practical things the text does not tell you.

You can usually guess the name.  Mathlib names read as `conclusion_of_hypothesis`, so a lemma
concluding `≠` from `<` is `ne_of_lt`, and from `>` it is `ne_of_gt`.  Names for properties read
as `relation_property`, which is why antisymmetry of `≤` is `le_antisymm`.  Once you have the
pattern you can write down a plausible name and let Lean tell you whether it exists.

When guessing fails, ask.  Put `exact?` where the proof should go and Lean searches the library
for something closing the goal, then prints what it found:

    example {x : ℚ} (h : x < 1) : x ≠ 1 := by exact?
    -- Try this: exact Rat.ne_of_lt h

`apply?` does the same for lemmas that leave subgoals behind.  Both are slow and neither belongs
in a finished proof.  They are how you find out what the library calls a thing.

One more point.  `apply ne_of_lt` commits you to a direction before you have proved anything, so
you have to know which side of `1` the value sits on in order to choose between `ne_of_lt` and
`ne_of_gt`.  Settle that on paper first. -/

-- Book, annotated.
example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  show x < 1
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  show y ^ 2 + 1 > 0
  extra

/- Note.  `le_antisymm` says `a ≤ b → b ≤ a → a = b`, so applying it leaves two goals rather than
one.  That is the other thing `apply` does, and it is where the bullets start.

The `show` lines are the habit worth taking from here.  Lean does not need them, since the two
goals arrive in a fixed order.  What they buy is that guessing that order wrong fails on the spot:

    'show' tactic failed, pattern
      a ^ 2 ≥ 0
    is not definitionally equal to target
      a ^ 2 ≤ 0

rather than letting you write a whole branch that answers the other question.  Part 2 of the
summary has more on documentation that Lean checks. -/

-- Book.
example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := h1
  extra

-- Book, annotated.
example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  · show a^2 ≤ 0
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := h1
  · show a^2 ≥ 0
    extra

/-! # Exercises -/

/- Note.  Both orders typecheck.  You can `apply` the lemma first and prove whatever it leaves, as
the examples above do, or establish the fact first and apply the lemma at the end:

    have h : 3 * m > 6 := by ...
    apply ne_of_gt
    apply h

Either is fine so long as the reader can see what is being proved after the `apply`.  Backwards
needs the `show` line for that, forwards gets it from the name.  Part 2 of the summary has the
choice in full. -/


example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  show 3 * m > 6
  have : m = 4 := by addarith [hm]
  rw [this]
  numbers

example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm
  · show s ≤ -2
    have : 3 * s ≤ 3 * -2 := by addarith [h1]
    cancel 3 at this
  · show s ≥ -2
    have : 2 * s ≥ 2 * -2 := by addarith [h2]
    cancel 2 at this
