/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/


/- Note.  `obtain ⟨b, hb⟩ := h` unpacks an existential hypothesis into two pieces, a value `b` and
a fact `hb` about it.  The angle brackets are the same ones used for `∧` in Section 2.4, and for
the same reason, namely that you receive everything inside at once.

The thing to be careful about is that `b` is a genuinely new and completely unknown quantity.  All
you ever learn about it is what `hb` says.  You cannot compute with it, you cannot case on what it
"really is", and any later step has to go through `hb`.  That is exactly how you would use "let b
be such that ..." on paper. -/

-- Book, annotated.
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb : a = b ^ 2 + 1⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


/- Note.  The pattern here is worth extracting, because it recurs whenever a hypothesis gives you
a product with a known sign.

`cancel` is fussy about shape.  It wants the comparison written against `0` with the factor
visible, as in `0 < c * t`, and it then needs `0 ≤ c` to conclude `0 < t`.  Handing it
`x * t < 0` directly fails with `cancel failed: no 'x' to cancel`, because there is no `x` on the
right-hand side to cancel against.

That is why the second branch below builds `0 < x * -t` first rather than working with `hxt` as it
stands.  When a tactic refuses, it is often asking for the same fact in a different shape rather
than for a different fact. -/

example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt : x * t < 0⟩ := h
  have : x ≤ 0 ∨ x > 0 := le_or_gt x 0
  obtain (hx : x ≤ 0) | (hx : x > 0) := this

  · have : x ≤ 0 := hx
    have : t > 0 := by
      have hxt' : 0 < -x * t := by addarith [hxt]
      have : 0 ≤ -x := by addarith [hx]
      cancel -x at hxt'
    apply ne_of_gt
    apply this

  · have : x > 0 := hx
    have : t < 0 := by
      have hxt' : 0 < x * -t := by
        calc
          0 < -(x * t) := by addarith [hxt]
          _ = x * -t := by ring
      have : 0 ≤ x := by addarith [hx]
      have : 0 < -t := by cancel x at hxt'
      addarith [this]
    apply ne_of_lt
    apply this

/- Note.  Proving an `∃` is the opposite job.  Rather than being handed an unknown, you have to
supply a specific value with `use`, after which the goal is the ordinary statement about that
value.

This is where Lean is harsher than a lecture.  On paper "such an `n` clearly exists" often passes.
Here you must produce one, and the search for it happens entirely outside Lean, on paper or by
trial.  `use` records the answer, it does not help you find it. -/

-- Book.
example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


-- Book.
example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


/- Note.  The witness may depend on the things already fixed, and here it must.  No single real
number exceeds every `x`, so `y` has to be built from `x`, and `x + 1` is the obvious choice.

Reading `∃ m n : ℤ, ...` as two nested existentials explains why `use 6, 5` supplies both at once,
and why the later `use a + 1, a` may mention `a`, which is fixed before the existentials are
reached. -/

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

/- Note.  The previous exercise asked for one pair.  This one asks for a recipe covering every
`a` at once, and the difference is worth dwelling on.  `6, 5` was found by trying things.  Here
the identity `(a + 1) ^ 2 - a ^ 2 = 2 * a + 1` has to be spotted, and once spotted the proof is
`ring` rather than `numbers`, because there is nothing left to compute. -/

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

/- Note.  `addarith` is weaker than it looks, and this is a good place to find that out.  It works
with the hypotheses as linear facts about whatever it treats as atoms, so `p < (p + q) / 2` is
beyond it even though the arithmetic is trivial.  The fix is the Chapter 1 move.  Write `p` as
`(p + p) / 2` with `ring`, then `rel [h]` replaces one `p` by `q`.

When a tactic that "should" work does not, reaching for a two-step `calc` is usually faster than
arguing with it. -/

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  · show p < (p + q) / 2
    calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  · show (p + q) / 2 < q
    calc
      (p + q) / 2 < (q + q) / 2 := by rel [h]
      _ = q := by ring

/- Note.  Four witnesses and four conjuncts.  `constructor` only ever splits a conjunction in two,
so a chain of four becomes three nested splits.  Both versions below are the same proof.  In the
first, four bare `numbers` calls sit in a flat list and nothing says which claim each one settles.
The bullets and `show` lines in the second say it.

Notice that the nesting here is imposed rather than chosen.  Nothing about the argument is three
levels deep, only the shape of `constructor`.  The last exercise in this section shows the way
out, namely proving the parts first and assembling them at the end.

The taxicab number is 1729, and this is Ramanujan's observation that it is the smallest number
expressible as a sum of two cubes in two different ways.  Lean checks the arithmetic instantly and
contributes nothing whatever to finding it. -/

-- Book.
example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

-- Restyled.
example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  · show 1 ^ 3 + 12 ^ 3 = 1729
    numbers
  · constructor
    · show 9 ^ 3 + 10 ^ 3 = 1729
      numbers
    · constructor
      · show 1 ≠ 9
        numbers
      · show 1 ≠ 10
        numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9, 2
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -1/2
  constructor
  · show -1/2 < 0
    numbers
  · show (-1/2) ^ 2 < 1
    numbers

/- Note.  `use 0, 0` also works here, since `2 ^ 0 = 1 = 5 * 0 + 1`.  Nothing rules out the
degenerate answer, and part of the skill is noticing when the cheapest witness is legitimate
rather than casting about for an interesting one. -/

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  numbers

/- Note.  The witness has to work for every `x`, including large ones, so no constant will do.
`x + 1` is the natural guess, and checking it means showing `(x + 1) ^ 2 - x > 0`, which is
`x ^ 2 + x + 1 > 0`.  That is not visibly positive as written, so complete the square as in
Section 1.4 and hand `(x + 1/2) ^ 2 + 3/4` to `extra`. -/

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1
  calc
    (x + 1) ^ 2 = x + ((x + 1/2) ^ 2 + 3/4) := by ring
    _ > x := by extra

/- Note.  Same shape as the `t ≠ 0` example at the top, and the same trick.  Rearranged, the
hypothesis says `0 < (1 - a) * (t - 1)`, a product of two things whose signs are unknown.  Split
on the sign of `a`, and in each case the sign of one factor is known, so `cancel` yields the sign
of the other.

`addarith` cannot reach the factored form on its own, since expanding the product is not a linear
step, so a two-line `calc` does the rearranging and `ring` certifies it. -/

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha : a * t + 1 < a + t⟩ := h
  obtain (hx : a ≤ 1) | (hx : a > 1) := le_or_gt a 1

  · have : a ≤ 1 := hx
    have : t > 1 := by
      have h1 : 0 < (1 - a) * (t - 1) := by
        calc
          0 < (a + t) - (a * t + 1) := by addarith [ha]
          _ = (1 - a) * (t - 1) := by ring
      have : 0 ≤ 1 - a := by addarith [hx]
      have : 0 < t - 1 := by cancel 1 - a at h1
      addarith [this]
    apply ne_of_gt
    apply this

  · have : a > 1 := hx
    have : t < 1 := by
      have h1 : 0 < (a - 1) * (1 - t) := by
        calc
          0 < (a + t) - (a * t + 1) := by addarith [ha]
          _ = (a - 1) * (1 - t) := by ring
      have : 0 ≤ a - 1 := by addarith [hx]
      have : 0 < 1 - t := by cancel a - 1 at h1
      addarith [this]
    apply ne_of_lt
    apply this

/- Note.  An existential hypothesis and a `≠` goal, so both halves of this section appear at once.
`obtain` turns `h` into a concrete `a` with `2 * a = m`, and then `le_or_succ_le` splits the
integers either side of the gap where `5` would have to sit.  Since `m` is even it lands at most
on `4` or at least on `6`, and never on `5`. -/

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha : 2 * a = m⟩ := h
  obtain (hx : a ≤ 2) | (hx : a ≥ 3) := le_or_succ_le a 2

  · have : a ≤ 2 := hx
    have : m < 5 :=
      calc
        m = 2 * a := by rw [ha]
        _ ≤ 2 * 2 := by rel [hx]
        _ < 5 := by numbers
    apply ne_of_lt
    apply this

  · have : a ≥ 3 := hx
    have : m > 5 :=
      calc
        m = 2 * a := by rw [ha]
        _ ≥ 2 * 3 := by rel [hx]
        _ > 5 := by numbers
    apply ne_of_gt
    apply this

/- Note.  The useful lesson here is that `use` does not have to come first.  Splitting on the sign
of `n` before choosing lets each branch pick its own witness, and no single simple witness works
for both.

For `n ≤ 0` the term `n * a` is a help rather than a hindrance, so a constant `2` suffices.  For
`n ≥ 1` the witness has to grow with `n`, and `n + 2` is chosen so that the leftover
`2 * n ^ 3 + 11 * n ^ 2 + 22 * n + 9` has no negative coefficients, which is what lets `extra`
finish in one step.  Picking the witness to make the final algebra pleasant is a real part of the
job. -/

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  obtain (hn : n ≤ 0) | (hn : n ≥ 1) := le_or_succ_le n 0

  · have : n ≤ 0 := hn
    use 2
    calc
      (2 : ℤ) * 2 ^ 3 = 16 := by numbers
      _ ≥ 0 * 2 + 7 := by numbers
      _ ≥ n * 2 + 7 := by rel [hn]

  · have : n ≥ 1 := hn
    use n + 2
    calc
      2 * (n + 2) ^ 3
        = n * (n + 2) + 7 + (2 * n ^ 3 + 11 * n ^ 2 + 22 * n + 9) := by ring
      _ ≥ n * (n + 2) + 7 := by extra

/- Note.  Six conjuncts, and nesting `constructor` five deep would be unreadable.  So this is the
place to meet the other half of the angle-bracket notation.

`⟨h1, h2, ...⟩` builds a conjunction exactly as `obtain ⟨h1, h2, ...⟩` takes one apart, and it
flattens the nesting for you, so one `exact ⟨hx, hy, hz, hA, hB, hC⟩` replaces five `constructor`s
and six bullets.  Compare it with the taxicab example above, which is the same construction
written the long way, five levels deep for an argument with no depth in it at all.

Note the order.  `use` comes first, so the reader knows which three numbers are on offer before
meeting six facts about them.  The six `have` lines then spell those facts out, which is why no
`show` is needed at the end. -/

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b + c - a) / 2, (a + c - b) / 2, (a + b - c) / 2
  have hx : (b + c - a) / 2 ≥ 0 := by addarith [ha]
  have hy : (a + c - b) / 2 ≥ 0 := by addarith [hb]
  have hz : (a + b - c) / 2 ≥ 0 := by addarith [hc]
  have hA : a = (a + c - b) / 2 + (a + b - c) / 2 := by ring
  have hB : b = (b + c - a) / 2 + (a + b - c) / 2 := by ring
  have hC : c = (b + c - a) / 2 + (a + c - b) / 2 := by ring
  exact ⟨hx, hy, hz, hA, hB, hC⟩
