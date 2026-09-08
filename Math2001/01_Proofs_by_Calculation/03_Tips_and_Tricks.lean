/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.3: Tips and tricks

Exercise: choose some of these examples and type out the whole proofs printed in the text as Lean
proofs. -/


-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring

-- Example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x = (x + 4) - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h1]
    _ = -6 + 5 * (b + 2) := by ring
    _ = -6 + 5 * 3 := by rw [h2]
    _ = 9 := by ring

-- Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w = (3 * w + 1) / 3 - 1 / 3 := by ring
    _ = 4/3 - 1/3 := by rw [h1]
    _ = 1 := by ring

-- Example 1.3.5
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  calc
    x = (2 * x + 3) - x - 3 := by ring
    _ = x - x - 3 := by rw [h1]
    _ = -3 := by ring

-- Example 1.3.6
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
    x = (2 * x - y) + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring

-- Example 1.3.7
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
    u = ((u + 2 * v) + (u - 2 * v)) / 2 := by ring
    _ = (4 + 6) / 2 := by rw [h1, h2]
    _ = 5 := by ring

-- Example 1.3.8
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
    x = (5 * x - 3 * y + 3 * (x + y)) / 8 := by ring
    _ = (4 + 3 * 4) / 8 := by rw [h1, h2]
    _ = 2 := by ring

-- Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a ^ 2 - a + 3 = ((a - 3) + 3) ^ 2 - ((a - 3) + 3) + 3 := by ring
    _ = (2 * b + 3) ^ 2 - (2 * b + 3) + 3 := by rw [h1]
    _ = 4 * b ^ 2 + 12 * b + 9 - (2 * b + 3) + 3 := by ring
    _ = 4 * b ^ 2 + 10 * b + 9 := by ring

-- Example 1.3.10
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
    z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1
      = (z ^ 2 - z + 1) * (z ^ 2 - 2) + 3 := by ring
    _ = (z ^ 2 - z + 1) * 0 + 3 := by rw [h1]
    _ = 3 := by ring

/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/


/- Note.  Nearly every exercise below is the recipe from Examples 1.3.6 and 1.3.7:

1. a `ring` step rewriting the goal's left side as the exact combination of hypotheses you need,
2. one `rw` firing all of those hypotheses at once,
3. a closing `ring` for the arithmetic.

Step 1 is where the thinking happens, and it is worth doing on paper first.  Solve the linear
system by hand, note which multiple of each hypothesis you used, then write that combination down.

`addarith` would close most of these in a single line, but it only arrives in Section 1.5.  So
everything here is `calc` with nothing but `ring` and `rw`.  That restriction is the point of the
section. -/


example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
    y = 4 * x - 3 := by rw [h2]
    _ = 4 * 3 - 3 := by rw [h1]
    _ = 9 := by ring

example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
    a = a - b + b := by ring
    _ = 0 + b := by rw [h]
    _ = b := by ring

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
    x = (x - 3 * y) + 3 * y := by ring
    _ = 5 + 3 * y := by rw [h1]
    _ = 5 + 3 * 3 := by rw [h2]
    _ = 14 := by ring

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  calc
    p = (p - 2 * q) + 2 * q := by ring
    _ = 1 + 2 * q := by rw [h1]
    _ = 1 + 2 * (-1) := by rw [h2]
    _ = -1 := by ring

/- Note.  `rw` matches syntactically.  A hypothesis fires only where its left side appears
literally in the goal, so the middle expression has to be *written* with `x + 2 * y` and `y + 1`
left intact.

This is a real constraint, not a formality.  `x + 2 * y - 2 * y - 2 + 2` is the same number and
`ring` proves the first step just as happily, but then `rw [h1]` reports

  Did not find an occurrence of the pattern
    y + 1

because nothing in the expression is literally `y + 1` any more.  Choosing the middle expression
is therefore not only about getting the arithmetic right.  It is about leaving the hypotheses
visible. -/

example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  calc
    x = (x + 2 * y) - 2 * (y + 1) + 2 := by ring
    _ = 3 - 2 * 3 + 2 := by rw [h1, h2]
    _ = -1 := by ring

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  calc
    p = (p + 4 * q) - 4 * (q - 1) - 4 := by ring
    _ = 1 - 4 * 2 - 4 := by rw [h1, h2]
    _ = -11 := by ring

/- Note.  The order inside `rw [h1, h2, h3]` matters here.  `h3 : c = 1` rewrites *every* `c` in
the goal, so it has to go last, once `h1` and `h2` have already swallowed the `c`s sitting inside
them.  Put `h3` first and the other two hypotheses no longer match anything. -/

example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  calc
    a = (a + 2 * b + 3 * c) - 2 * (b + 2 * c) + c := by ring
    _ = 7 - 2 * 3 + 1 := by rw [h1, h2, h3]
    _ = 2 := by ring

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  calc
    u = ((4 * u + v) - v) / 4 := by ring
    _ = (3 - v) / 4 := by rw [h1]
    _ = (3 - 2) / 4 := by rw [h2]
    _ = 1 / 4 := by ring

/- Note.  When the unknown sits on both sides of the hypothesis, the combination to reach for is
"left side minus right side".  Here `(4 * c + 1) - (3 * c - 2)` is `c + 3`, so `c` is that
difference minus 3.  The next two exercises are the same move. -/

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 :=
  calc
    c = (4 * c + 1) - (3 * c - 2) - 3 := by ring
    _ = (3 * c - 2) - (3 * c - 2) - 3 := by rw [h1]
    _ = -3 := by ring

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
  calc
    p = ((5 * p - 3) - (3 * p + 1)) / 2 + 2 := by ring
    _ = ((3 * p + 1) - (3 * p + 1)) / 2 + 2 := by rw [h1]
    _ = 2 := by ring

example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 :=
  calc
    x = (2 * x + y) - (x + y) := by ring
    _ = 4 - 1 := by rw [h1, h2]
    _ = 3 := by ring

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 :=
  calc
    a = ((a + 2 * b) + 2 * (a - b)) / 3 := by ring
    _ = (4 + 2 * 1) / 3 := by rw [h1, h2]
    _ = 2 := by ring

/- Note.  Two lines, because a single `rw [h1]` replaces *both* copies of `u + 1` at once.  Again
the whole trick is writing the middle expression so that `u + 1` is visible as a subterm. -/

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  calc
    u ^ 2 + 3 * u + 1 = (u + 1) ^ 2 + (u + 1) - 1 := by ring
    _ = v ^ 2 + v - 1 := by rw [h1]

/- Note.  Same shape as Example 1.3.10, and the same way of finding it.  Divide the difference of
the two sides, `t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 12 * t - 4`, by the left side of the hypothesis,
`t ^ 2 - 4`, and read off the quotient `t ^ 2 + 3 * t + 1`.

Polynomial division is not just a way to guess the factorisation, it also tells you whether the
hypothesis is usable at all.  A nonzero remainder means no amount of `rw` will finish the job. -/

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  calc
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2
      = (t ^ 2 + 3 * t + 1) * (t ^ 2 - 4) + 10 * t + 2 := by ring
    _ = (t ^ 2 + 3 * t + 1) * 0 + 10 * t + 2 := by rw [ht]
    _ = 10 * t + 2 := by ring

/- Note.  This is the odd one out, and it is worth seeing why.

On paper the argument is three sentences.  `h1` gives `x = 2`.  Substituting that into `h2` gives
`4 - 2 * y = 0`.  Hence `y = 2`.

Lean cannot record the middle sentence yet.  A `calc` block proves one chain of equalities, so
`x = 2` has nowhere to live as a fact of its own.  It has to be smuggled into the chain instead,
which is what the first and the last two steps below are doing.  Every step is `ring` or `rw` and
the proof is correct, but it reads as a trick rather than as the argument above. -/

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  calc
    y = (y * x + y * (5 - (x + 3))) / 2 := by ring
    _ = (y * x + y * (5 - 5)) / 2 := by rw [h1]
    _ = (2 * x - (2 * x - y * x)) / 2 := by ring
    _ = (2 * x - 0) / 2 := by rw [h2]
    _ = (x + 3) - 3 := by ring
    _ = 5 - 3 := by rw [h1]
    _ = 2 := by ring

/- The same problem again, written the way you would say it out loud.  Two new pieces of syntax
are doing the work, and both are previews rather than things you are expected to produce yet.

`have hx : x = 2 := by ...` proves a side fact and gives it the name `hx`.  That is the subject of
Section 2.1.

`rw [hx] at h2` rewrites a *hypothesis* instead of the goal, turning `h2` into
`2 * 2 - y * 2 = 0`.  Every `rw` so far has acted on the goal.  This form first appears in
Section 4.4.

Compare the two proofs.  The point of `have` is not that it is shorter, although here it is.  It
is that the Lean proof now has the same three-sentence shape as the proof on paper, with the
intermediate fact named and stated rather than hidden inside an algebraic identity.  Section 2.1
opens by revisiting Example 1.3.3 from this very file in exactly this way. -/

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 := by
  have hx : x = 2 :=
    calc
      x = (x + 3) - 3 := by ring
      _ = 5 - 3 := by rw [h1]
      _ = 2 := by ring
  rw [hx] at h2
  -- `h2 : 2 * 2 - y * 2 = 0`
  calc
    y = (2 * 2 - (2 * 2 - y * 2)) / 2 := by ring
    _ = (2 * 2 - 0) / 2 := by rw [h2]
    _ = 2 := by ring

/- Note.  The only exercise here that needs an idea rather than a calculation.  Squaring
`p + q + r` gives `p ^ 2 + q ^ 2 + r ^ 2` plus exactly twice the left side of `h2`, so the
combination to write down is `(p + q + r) ^ 2 - 2 * (p * q + p * r + q * r)`.  Nothing about the
two hypotheses individually suggests this.  You have to recognise the square. -/

example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  calc
    p ^ 2 + q ^ 2 + r ^ 2
      = (p + q + r) ^ 2 - 2 * (p * q + p * r + q * r) := by ring
    _ = 0 ^ 2 - 2 * 2 := by rw [h1, h2]
    _ = -4 := by ring
