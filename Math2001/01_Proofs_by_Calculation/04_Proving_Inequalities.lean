/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.4: Proving inequalities -/


/- Note.  Three tactics carry this whole section.

`rel [h]` is the inequality counterpart of `rw`.  It substitutes a bound into part of the goal.
Unlike `rw` it also has to check a direction, and it sorts out any sign flip itself.

`extra` discards a term that is neutral for the relation, proving `a ≤ a + s` when `s` is
nonnegative and `a < a + s` when `s` is positive.

`numbers` closes a step whose two sides are concrete numbers.

A proof is then a `calc` chain running from the left side of the goal down to the right side.  The
`ring` steps in between are not tidying up.  Each one is there to reshape the expression so that
the next `rel` or `extra` has something to act on.  That is the discipline of Section 1.3 again,
with a direction constraint added on top. -/

/- Note.  Worth going through slowly, since it sets the pattern for everything after it.

`hy : y + 2 * x ≥ 3` is a lower bound and is used as one.  But `hx : x + 3 ≤ 2` is an *upper*
bound, and the goal `y > 3` is a lower bound, and `hx` is still exactly what is needed.  The
reason is the third step, which puts `x + 3` behind a minus sign.  Making a subtracted quantity
smaller makes the whole expression larger, so an upper bound on `x + 3` is a lower bound on
`9 - 2 * (x + 3)`, and `rel` performs that flip without being told.

The direction of a hypothesis therefore does not have to match the direction of the goal.  What
decides the matter is where in the expression you apply it. -/

-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by numbers

-- Example 1.4.2
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by rel [h1, h2]
    _ = 3 := by ring

-- Example 1.4.3
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  calc
    x + y ≤ x + (x + 5) := by rel [h1]
    _ = 2 * x + 5 := by ring
    _ ≤ 2 * (-2) + 5 := by rel [h2]
    _ < 2 := by numbers

/- Note.  The most instructive example here, for a reason the text does not show.

The first step is `rel [h4, h5]`, replacing `y` and `x` by `B`.  That is legitimate only because
the step multiplies through by `u` and by `v`, which are nonnegative, and `rel` takes `h6` and
`h7` from the context without being asked.  Delete those two from the statement and the very same
step fails with

    rel failed, cannot prove goal by 'substituting' the listed relationships.
    The steps which could not be automatically justified were:
      0 ≤ u
      0 ≤ v

That message is the best debugging tool in this section.  When `rel` refuses, it names the side
conditions it could not establish, which usually tells you either which sign fact is missing or
which direction you have backwards.

Also worth pointing at is the pace.  Six steps, each changing exactly one thing, for what reads
as a single line of ordinary mathematics. -/

-- Example 1.4.4
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by rel [h4, h5]
    _ ≤ A * B + A * B + A * v := by rel [h8, h9]
    _ ≤ A * B + A * B + 1 * v := by rel [h2]
    _ ≤ A * B + A * B + B * v := by rel [h3]
    _ < A * B + A * B + B * A := by rel [h8, h9]
    _ = 3 * A * B := by ring

-- Example 1.4.5
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by ring
    _ ≥ 10 * t - 3 * t - 17 := by rel [ht]
    _ = 7 * t - 17 := by ring
    _ ≥ 7 * 10 - 17 := by rel [ht]
    _ ≥ 5 := by numbers

-- Example 1.4.6
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc
    n ^ 2 = n * n := by ring
    _ ≥ 5 * n := by rel [hn]
    _ = 2 * n + 3 * n := by ring
    _ ≥ 2 * n + 3 * 5 := by rel [hn]
    _ = (2 * n + 11) + 4 := by ring
    _ > 2 * n + 11 := by extra

/- Note.  `extra` in its simplest form.  `m ^ 2` is nonnegative whatever `m` is, so adding it can
only push the expression up, and the first step deliberately goes up before the hypothesis brings
it back down. -/

-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
  calc
    n ≤ m ^ 2 + n := by extra
    _ ≤ 2 := by rel [h]


/- Note.  The key trick of the section, and it looks like a blunder the first time you meet it.

To bound `(x + y) ^ 2` from above, the first step makes the expression *bigger*, by adding
`(x - y) ^ 2`.  Enlarging the quantity you are trying to bound above seems to throw away the
slack you need.  It works because the enlarged expression is exactly `2 * (x ^ 2 + y ^ 2)`, which
is the shape the hypothesis speaks about, and `(x + y) ^ 2` on its own is not.

Adding a square you have no use for, in order to reach an expression the hypothesis can act on,
is the move to remember.  Examples 1.4.9 and 1.4.10 are both this, and 1.4.10 is the pure form of
it, where the entire proof is `extra` and then `ring`. -/

-- Example 1.4.8
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 1 := by rel [h]
    _ < 3 := by numbers

/- Note.  The same move, and here you can watch where the added squares come from.

The hypothesis is about `a + b`, so what you want is an expression in which `a + b` appears as a
factor.  Fix the target shape as `2 * ((a + b) * b) + (a + b) * a + a`, expand it, and compare
with `3 * a * b + a`.  The difference is `2 * b ^ 2 + a ^ 2`, which is precisely what the first
step adds.  So the squares are found by deciding where you want to end up and subtracting, not by
inspiration. -/

-- Example 1.4.9
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by extra
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _ ≤ 2 * (8 * b) + 8 * a + a := by rel [h3]
    _ = 7 * b + 9 * (a + b) := by ring
    _ ≤ 7 * b + 9 * 8 := by rel [h3]
    _ = 7 * b + 72 := by ring

-- Example 1.4.10
example {a b c : ℝ} :
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 :=
  calc
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)
      ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2
          + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2
          + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) := by extra
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by ring


/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/


/- Note.  One check worth making before you start any of these.  A `calc` chain proves the
strongest relation its steps support, so a chain built from `=` and `≥` steps proves `≥`, and a
goal stated with `>` needs at least one genuinely strict step somewhere in it.  Decide in advance
where that strict step is going to come from. -/


example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
    x = (x + 3) - 3 := by ring
    _ ≥ 2 * y - 3 := by rel [h1]
    _ ≥ 2 * 1 - 3 := by rel [h2]
    _ = -1 := by ring

/- Note.  The chain does not have to land exactly on the target.  Here it reaches `4 / 2 + 3 / 2`,
which is `7 / 2`, and `numbers` closes the gap to `3`.  Slack at the end is fine, and trying to
make the arithmetic come out exact usually costs you a step for nothing. -/

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = (a + 2 * b) / 2 + a / 2 := by ring
    _ ≥ 4 / 2 + a / 2 := by rel [h2]
    _ ≥ 4 / 2 + 3 / 2 := by rel [h1]
    _ ≥ 3 := by numbers

/- Note.  `hx` is used twice, at two different points in the chain, which is normal.

The first `ring` step rewrites `x ^ 3` as `x ^ 2 * x`.  That is what produces a lone `x` to
replace by `9`, and it leaves `x ^ 2` as the factor being multiplied through, whose sign is
visible without any help from the hypothesis. -/

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x ^ 2 * x - 8 * x ^ 2 + 2 * x := by ring
    _ ≥ x ^ 2 * 9 - 8 * x ^ 2 + 2 * x := by rel [hx]
    _ = x ^ 2 + 2 * x := by ring
    _ ≥ 9 ^ 2 + 2 * 9 := by rel [hx]
    _ ≥ 3 := by numbers

/- Note.  The trickiest one here, for two reasons.

The goal is strict, so by the remark above the chain needs a strict step, and the final one is it.
Everything before it is `=` or `≥`.

That final step asks `extra` to prove `3 * n ^ 3 + 68 * n ^ 2 > 3 * n ^ 3`, which needs
`68 * n ^ 2` to be strictly positive rather than merely nonnegative.  `n ^ 2 > 0` is false at
`n = 0`, so the step really does depend on `hn`, and `extra` goes and finds `hn` in the context by
itself.  Delete `hn` from the statement and it fails.

That is the general point.  Both `rel` and `extra` read everything in scope, and the bracketed
list in `rel [...]` is only the part you are pointing at, not the full set of facts being used. -/

example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  calc
    n ^ 4 - 2 * n ^ 2 = n * n ^ 3 - 2 * n ^ 2 := by ring
    _ ≥ 10 * n ^ 3 - 2 * n ^ 2 := by rel [hn]
    _ = 3 * n ^ 3 + 7 * n * n ^ 2 - 2 * n ^ 2 := by ring
    _ ≥ 3 * n ^ 3 + 7 * 10 * n ^ 2 - 2 * n ^ 2 := by rel [hn]
    _ = 3 * n ^ 3 + 68 * n ^ 2 := by ring
    _ > 3 * n ^ 3 := by extra

/- Note.  There is a shorter proof of this one, because `n ^ 2 - 2 * n + 3` is `(n - 1) ^ 2 + 2`:

    calc
      n ^ 2 - 2 * n + 3 = (n - 1) ^ 2 + 2 := by ring
      _ ≥ (5 - 1) ^ 2 + 2 := by rel [h1]
      _ > 14 := by numbers

Two steps rather than four, and `h1` is used once rather than twice.  Completing the square is
often the shorter route when the goal is quadratic.  For the two exercises after this one it is
the only route, since there is no hypothesis to substitute at all. -/

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  calc
    n ^ 2 - 2 * n + 3 = n * n - 2 * n + 3 := by ring
    _ ≥ 5 * n - 2 * n + 3 := by rel [h1]
    _ = 3 * n + 3 := by ring
    _ ≥ 3 * 5 + 3 := by rel [h1]
    _ > 14 := by numbers

/- Note.  These last two have no hypotheses, so `rel` has nothing to substitute and the entire
proof has to come from a square being nonnegative.  Both follow one pattern.  Use `ring` to write
the left side as the right side plus a square, then let `extra` throw the square away.

Finding the square is just completing the square, and the two needed here are `(x - 1) ^ 2` and
`(a - b) ^ 2`.  The second is the arithmetic mean-geometric mean inequality for two terms, which
is worth recognising, since it turns up constantly and this is the whole proof of it. -/

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  calc
    x ^ 2 - 2 * x = -1 + (x - 1) ^ 2 := by ring
    _ ≥ -1 := by extra

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  calc
    a ^ 2 + b ^ 2 = 2 * a * b + (a - b) ^ 2 := by ring
    _ ≥ 2 * a * b := by extra
