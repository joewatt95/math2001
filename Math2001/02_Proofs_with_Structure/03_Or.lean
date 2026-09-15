/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


/- Note.  The book writes `obtain hx | hy := h`.  Spelling the cases out as
`obtain (hx : x = 1) | (hy : y = -1) := h` costs nothing and lets you see what each branch may
assume without reconstructing it from the statement of `h`.  Write the two cases down in the wrong
order and Lean says so at once.

The branches get different names, `hx` and `hy` rather than `h` twice, because the two cases here
are about different variables. -/

example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain (hx : x = 1) | (hy : y = -1) := h
  · calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  · calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

/- Note.  `le_or_succ_le n 1` produces `n ≤ 1 ∨ n ≥ 2` and is the standard way to case-split a
whole number.  It repays a closer look, because the name makes it look like an ordinary lemma and
it is not one.  In this project it is a macro, defined in `Library/Theory/Comparison.lean` as

    le_or_succ_le a n  ==>  show a ≤ n ∨ n + 1 ≤ a from le_or_gt ..

So the actual content is `le_or_gt`, namely `a ≤ n` or `n < a`.  Everything interesting is in the
step from `n < a` to `n + 1 ≤ a`, and that step is available only because there is no whole number
strictly between `n` and `n + 1`.

That is the discreteness of ℕ and ℤ being spent, and it is why this whole style of argument has no
counterpart over ℝ.  Ask for it there and Lean objects:

    example (x : ℝ) : x ≤ 1 ∨ x ≥ 2 := le_or_succ_le x 1
    -- Type mismatch: le_or_gt ... has type   x ≤ 1 ∨ 1 < x
    --                but is expected to have type   x ≤ 1 ∨ 2 ≤ x

Worth internalising early.  "Split into finitely many cases and check each one" is a move you are
given for whole numbers and are not given for real numbers.

A gotcha from the same source.  Being a macro, its second argument must be a literal number.
`le_or_succ_le n k` for a variable `k` does not even parse, and reports
`unexpected identifier; expected numeral`. -/

example {n : ℕ} : n ^ 2 ≠ 2 := by
  -- have hn := le_or_succ_le n 0
  obtain (hn : n ≤ 1) | (hn : n ≥ 2) := le_or_succ_le n 1

  · have : n ≤ 1 := hn
    apply ne_of_lt
    show n ^ 2 < 2
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers

  · have : n ≥ 2 := hn
    apply ne_of_gt
    show n ^ 2 > 2
    calc
      n ^ 2 ≥ 2 ^ 2 := by rel [hn]
          _ > 2 := by numbers

/- Note.  `left` and `right` make you commit to which disjunct you are proving before you have
proved anything, exactly as choosing between `ne_of_lt` and `ne_of_gt` did in Section 2.2.  Decide
which side is true before typing either word.

They are ordinary tactics though, so they need not come first.  One exercise below rewrites the
goal with `rw [h]` before saying `left`, because the rewrite makes it obvious which side is
provable.  The general lesson is that the order of your steps is yours to choose, and when a
choice looks hard, doing the easy rewriting first often makes it easy. -/

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


/- Note.  A recipe worth learning as a recipe, because it handles every goal of the shape
`x = a ∨ x = b`.

Arrange the hypothesis so it reads `something = 0`.  Factor that something.  Feed the factored
equation to `eq_zero_or_eq_zero_of_mul_eq_zero`, which says a product vanishes only if one of its
factors does, and `obtain` the two cases.  Each case is then a linear equation and `addarith`
finishes it.

Notice the `calc` runs from the factored product back to the hypothesis rather than the other way
about.  You write down the product you want and let `ring` certify that it equals what you
actually have, which is the same manoeuvre as Section 1.3. -/

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  -- have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain (h : x - 1 = 0) | (h : x - 2 = 0) := eq_zero_or_eq_zero_of_mul_eq_zero this
  · left
    show x = 1
    addarith [h]
  · right
    show x = 2
    addarith [h]

/- Note.  Compare this with the same statement for `n : ℕ` further up.  That one needed one split.
This one needs two, nested.

The type is the reason.  A natural number is already at least `0`, so `n ≤ 1 ∨ n ≥ 2` exhausts the
possibilities.  An integer may be negative, so you split on the sign first, and only then run the
earlier argument on whichever of `n` or `-n` is the nonnegative one.

Letting the type tell you how much case analysis you owe is a habit worth building.  When a proof
suddenly wants twice the cases you expected, the usual reason is that the type admits something
you were not picturing.

This is also the chapter's clearest case for annotating.  Four leaves, each two levels deep, and
at any one of them two assumptions are live, an outer one about the sign of `n` and an inner one
about size.  Only the inner one appears anywhere near the calculation you are reading.  The
`have : n ≤ 0 := hn0` and `have : n ≥ 1 := hn0` lines opening the outer branches are what let you
drop into a single leaf and read it without counting bullets back up the tree. -/

example {n : ℤ} : n ^ 2 ≠ 2 := by
  obtain (hn0 : n ≤ 0) | (hn0 : n ≥ 1) := le_or_succ_le n 0
  · have : n ≤ 0 := hn0
    have : -n ≥ 0 := by addarith [hn0]
    obtain (hn : -n ≤ 1) | (hn : -n ≥ 2) := le_or_succ_le (-n) 1
    · have : -n ≤ 1 := hn
      apply ne_of_lt
      show n ^ 2 < 2
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · have : -n ≥ 2 := hn
      apply ne_of_gt
      show n ^ 2 > 2
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring

  · have : n ≥ 1 := hn0
    obtain (hn : n ≤ 1) | (hn : n ≥ 2) := le_or_succ_le n 1
    · have : n ≤ 1 := hn
      apply ne_of_lt
      show n ^ 2 < 2
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · have : n ≥ 2 := hn
      apply ne_of_gt
      show n ^ 2 > 2
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain hx | hx := h
  · rw [hx]
    ring
  · rw [hx]
    ring

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain hx | hx := h
  · rw [hx]
    ring
  · rw [hx]
    ring

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain ht | ht := h
  · rw [ht]
    ring
  · rw [ht]
    ring

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hx | hy := h
  · rw [hx]
    ring
  · rw [hy]
    ring

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  show s + t = 3
  rw [h]
  ring

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  show b < - a / 2
  addarith [h]

-- can rw before left.
example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  rw [h]
  left
  addarith []

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have :=
    calc
      (x + 3) * (x - 1)
    _ = x ^ 2 + 2 * x - 3 := by ring
    _ = 0 := by rw [hx]
  obtain (h : x + 3 = 0) | (h : x - 1 = 0) := eq_zero_or_eq_zero_of_mul_eq_zero this
  · left
    show x = -3
    addarith [h]
  · right
    show x = 1
    addarith [h]

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have :=
    calc
      (a - b) * (a - 2*b)
    _ = a^2 - 3*a*b + 2*b^2 := by ring
    _ = 0 := by addarith [hab]
  obtain (h : a - b = 0) | (h : a - 2*b = 0) := eq_zero_or_eq_zero_of_mul_eq_zero this
  · left
    show a = b
    addarith [h]
  · right
    show a = 2 * b
    addarith [h]

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have :=
    calc
      t^2 * (t - 1)
    _ = t^3 - t^2 := by ring
    _ = 0 := by addarith [ht]
  obtain (h : t^2 = 0) | (h : t - 1 = 0) := eq_zero_or_eq_zero_of_mul_eq_zero this
  · right
    show t = 0
    cancel 2 at h
  · left
    show t = 1
    addarith [h]

/- Note.  Two habits from Part 2 of the summary appear together in these exercises.

Each branch opens by restating the case it is in, as `have : n ≤ 2 := h`.  Nothing requires it,
since `h` already says exactly that, and it records what you are entitled to use in the way a
`show` records what you are proving.

Each branch also builds the inequality as a named fact before applying `ne_of_lt` or `ne_of_gt`.
The worked examples at the top of the file go the other way, applying the lemma first and saying
what the goal became with `show`.  Both are readable, and Part 2 of the summary says when to reach
for which. -/

example {n : ℕ} : n ^ 2 ≠ 7 := by
  obtain (h : n ≤ 2) | (h : n ≥ 3) := le_or_succ_le n 2

  · have : n ≤ 2 := h
    have :=
      calc
        n^2 ≤ 2^2 := by rel [h]
          _ < 7 := by numbers
    apply ne_of_lt
    apply this

  · have : n ≥ 3 := h
    have :=
      calc
        n^2 ≥ 3^2 := by rel [h]
          _ > 7 := by numbers
    apply ne_of_gt
    apply this

example {x : ℤ} : 2 * x ≠ 3 := by
  obtain (h : x ≤ 1) | (h : x ≥ 2) := le_or_succ_le x 1

  · have : x ≤ 1 := h
    have :=
      calc
        2*x ≤ 2*1 := by rel [h]
          _ < 3 := by numbers
    apply ne_of_lt
    apply this

  · have : x ≥ 2 := h
    have :=
      calc
        2*x ≥ 2*2 := by rel [h]
          _ > 3 := by numbers
    apply ne_of_gt
    apply this

example {t : ℤ} : 5 * t ≠ 18 := by
  obtain (h : t ≤ 3) | (h : t ≥ 4) := le_or_succ_le t 3

  · have : t ≤ 3 := h
    have :=
      calc
        5*t ≤ 5*3 := by rel [h]
          _ < 18 := by numbers
    apply ne_of_lt
    apply this

  · have : t ≥ 4 := h
    have :=
      calc
        5*t ≥ 5*4 := by rel [h]
          _ > 18 := by numbers
    apply ne_of_gt
    apply this

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  obtain (h : m ≤ 5) | (h : m ≥ 6) := le_or_succ_le m 5

  · have : m ≤ 5 := h
    have :=
      calc
        m ^ 2 + 4 * m
      _ ≤ 5^2 + 4*5 := by rel [h]
      _ < 46 := by numbers
    apply ne_of_lt
    apply this

  · have : m ≥ 6 := h
    have :=
      calc
        m ^ 2 + 4 * m
      _ ≥ 6^2 + 4*6 := by rel [h]
      _ > 46 := by numbers
    apply ne_of_gt
    apply this
