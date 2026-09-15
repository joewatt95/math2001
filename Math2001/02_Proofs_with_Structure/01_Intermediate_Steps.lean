/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


/- Note.  This first example is Example 1.3.3 from Section 1.3, word for word.  Worth putting the
two side by side.  The Chapter 1 proof had to smuggle `b = 1` into the middle of a calc chain,
because there was nowhere else for it to live.  Here it is stated, named and proved on a line of
its own.  That is what `have` buys, and the gain is shape rather than brevity. -/

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring


/- Note.  A second form of `have`, with no statement written after the name.  `have h3 := calc ...`
takes whatever the chain happens to conclude, so here `h3 : m + 3 ≤ 9`.  That saves repeating a
long statement you have just written as a chain, at the price of having to work out for yourself
what you are now holding.  The closing `addarith [h3]` is what turns it into the goal. -/

example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
    calc
      m + 3 ≤ 2 * n - 1 := by rel [h1]
      _ ≤ 2 * 5 - 1 := by rel [h2]
      _ = 9 := by numbers
  addarith [h3]


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith [h1]
  have h4 : r ≤ 3 - s := by addarith [h2]
  calc
    r = (r + r) / 2 := by ring
    -- Both rel and addarith work for the step below.
    _ ≤ (3 - s + (3 + s)) / 2 := by rel [h3, h4]
    _ = 3 := by ring

/- Note.  `cancel` is the genuinely new power in this section.  Nothing in Chapter 1 could get
from a fact about `t * t` to a fact about `t`.

It appears in three guises.  `cancel t at h3` cancels a factor.  `cancel 2 at h3`, in the next
example, cancels an exponent, which is to say it takes a square root.  And in the exercises
`cancel x + 2 at this` cancels a compound factor, which is why that chain deliberately ends
`_ = (x + 2) * 0` rather than `_ = 0`, so both sides visibly carry the factor being removed.

All three need to know a sign, and none of them mentions it.  `cancel t` here needs `t > 0` and
takes it from `h2 : t ≥ 1` without being asked, exactly as `rel` and `extra` did in Section 1.4. -/

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
    calc t * t = t ^ 2 := by ring
      _ = 3 * t := by rw [h1]
  cancel t at h3
  addarith [h3]


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
    calc
      a ^ 2 = b ^ 2 + 1 := by rw [h1]
      _ ≥ 1 := by extra
      _ = 1 ^ 2 := by ring
  cancel 2 at h3


/- Note.  An unnamed `have` is called `this`.  The example below has one of them, and the example
after that has two, where the second shadows the first.  The shadowed one shows up in the goal
display as `this✝` and can no longer be written down by name.

It is still usable, though.  The `extra` step there finds both facts even though only one of them
has a name you could type.  So leaving a `have` unnamed is fine when the next tactic consumes it
immediately, or when you are handing it to automation that will go hunting anyway.  Name them as
soon as you need to point at a particular one. -/

example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  -- Unnamed intermediate "have" steps are implicitly named "this".
  have : x ≤ -1 := by addarith [hx]
  calc
    y ≥ 3 - 2 * x := by addarith [hy]
    -- "this" refers to the most recent unnamed intermediate step, which is the one above.
    _ ≥ 3 - 2 * -1 := by rel [this]
    _ > 3 := by numbers

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have : b + a ≥ 0 := by addarith [h1]
  have : b - a ≥ 0 := by addarith [h2]
  calc
    -- extra automatically uses both steps above.
    a ^ 2 ≤ a^2 + (b + a) * (b - a) := by extra
    _ = b ^ 2 := by ring

/- Note.  There is real content hiding in this one, namely the factorisation

    b ^ 3 - a ^ 3 = (b - a) * ((b - a) ^ 2 + 3 * (b + a) ^ 2) / 4

The honest factor is `b ^ 2 + a * b + a ^ 2`, which is not visibly nonnegative, so it gets
rewritten as a sum of two squares over 4.  That is completing the square in two variables, and it
is the same manoeuvre as Example 1.4.10, where the entire proof was finding a sum-of-squares
certificate and handing it to `extra`. -/

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  -- extra works here too
  have : b - a ≥ 0 := by addarith [h]
  have : (b - a)*((b - a)^2 + 3*(b + a)^2) / 4 ≥ 0 := by extra
  calc
    a^3 ≤ a^3 + (b - a)*((b - a)^2 + 3*(b + a)^2) / 4 := by extra
      _ = b^3 := by ring

/-! # Exercises -/


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have :=
    calc
      (x + 2) * (x - 2) = x ^ 2 - 4 := by ring
                      _ = 0 := by addarith [h1]
                      _ = (x + 2) * 0 := by ring
  cancel x + 2 at this
  addarith [this]

/- Note.  Small thing worth spotting.  The `cancel 2 at this` below also closes the goal.  It
rewrites `this` into `n - 2 = 0`, and since that is exactly what was being proved, nothing is
left over.  A tactic ending in `at h` usually only touches the hypothesis, so this is an
exception. -/

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have :=
    calc
      (n - 2)^2 = n^2 - 4*n + 2^2 := by ring
              _ = 0 := by addarith [hn]
  have : n - 2 = 0 := by cancel 2 at this
  addarith [this]

/- Note.  The `have : y > 0` line looks decorative, since nothing after it mentions `y > 0`.  It
is not.  Delete it and the `rel [h2]` step fails with

    The steps which could not be automatically justified were:
      0 ≤ y

`1 * y ≤ x * y` follows from `x ≥ 1` only when `y` is nonnegative, and `rel` will not take that on
trust.  The `have` is there purely to put that fact somewhere `rel` can find it.

This is the Section 1.4 observation turned into a working technique.  When automation refuses over
a side condition, read the condition off the error message and `have` it into existence. -/

example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have : x * y > 0 := by addarith [h]
  have : y > 0 := by cancel x at this
  calc
    y = 1 * y := by ring
    _ ≤ x * y := by rel [h2]
    _ = 1 := by rw [h]
