/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  Almost every inductive step in this chapter has the same shape, and it is worth seeing
it once rather than rediscovering it eight times.

The goal talks about `k + 1` and the only fact you have talks about `k`, so the first `calc` step
peels one factor off: `2 ^ (k + 1) = 2 * 2 ^ k`.  That exposes `2 ^ k`, which is what `rel [IH]`
needs in order to substitute.  Everything after that is tidying up.

Write the chain from both ends.  The first line is forced (peel), the last line is the goal, and
the middle is whatever algebra joins them.  Subtracting on paper finds it: if you have reached
`k ^ 2 + 2 * k + 9` and the goal is `(k + 1) ^ 2`, the slack is `8`, so the step before the end
is `_ = (k + 1) ^ 2 + 8 := by ring`.  `extra` closes exactly the goals of the form "the thing I
want, plus something nonnegative", so that `ring` step is there to put the goal on the left and
the slack on the right. -/

-- Book.
example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left
    use 0
    numbers
  · -- inductive step
    obtain ⟨x, hx : k = 2 * x⟩ | ⟨x, hx : k = 2 * x + 1⟩ := IH
    · right
      use x
      rw [hx]
    · left
      use x + 1
      calc k + 1 = 2 * x + 1 + 1 := by rw [hx]
        _ = 2 * (x + 1) := by ring

/- Note.  This is `Int.ModEq.pow`, which Section 3.3 stated and left with a `sorry` because the
proof needs induction.  Compare it with `Int.ModEq.pow_two` and `pow_three` there, which were
proved one at a time by factoring `a ^ 2 - b ^ 2` and `a ^ 3 - b ^ 3` by hand.  Induction is what
lets one proof cover every exponent. -/

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · -- base case
    rel [h]
  · -- inductive step
    calc a ^ (k + 1) = a * a ^ k := by ring
      _ ≡ b * b ^ k [ZMOD d] := by rel [h, IH]
      _ = b ^ (k + 1) := by ring

-- Book.
example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


/- Note.  `simple_induction` and `induction_from_starting_point` run `push_cast` on every goal
they produce, and on a base case that is pure arithmetic that is sometimes enough to finish it.
Only the inductive step is then left, which is why the proof below has one bullet where you might
expect two.  A `· -- base case` bullet reporting "no goals to be solved" has met the same thing. -/

-- Book.
example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


/- Note.  `forall_sufficiently_large n, P n` unfolds to `∃ C, ∀ n ≥ C, P n`, so `use` has to
supply the threshold and nothing will tell you what it is.  Two things constrain it, and only the
first is obvious: the base case `P C` has to be true, and the inductive step has to go through
from `hk : C ≤ k`.  So try small values until the base case holds, then write the inductive step
and look at the bounds you actually used on `k`.  If one of them needed `k` larger than `C`, go
back and raise `C`. -/

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH]
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 3 ^ (k + 1) = 3 * 3 ^ k := by ring
      _ ≥ 3 * (k ^ 2 + k + 1) := by rel [IH]
      _ = (k + 1) ^ 2 + (k + 1) + 1 + 2 * k ^ 2 := by ring
      _ ≥ (k + 1) ^ 2 + (k + 1) + 1 := by extra

/- Note.  Anything that does not mention `n` belongs above the `simple_induction`, not inside the
inductive step.  Here `rel` needs to know that `1 + a` is nonnegative before it will multiply an
inequality by it, and that fact is the same in every case, so it is established once.  The same
goes for taking a hypothesis apart: see `Odd.pow` at the end of the file, where `ha` is
`obtain`ed before the induction starts. -/

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  have h1 : (0:ℝ) ≤ 1 + a := by addarith [ha]
  simple_induction n with k IH
  · -- base case
    have : (1 + a) ^ 0 = 1 + 0 * a := by ring
    rw [this]  -- `rw` finishes once the two sides are identical, for `≥` as for `=`
  · -- inductive step
    calc (1 + a) ^ (k + 1) = (1 + a) * (1 + a) ^ k := by ring
      _ ≥ (1 + a) * (1 + k * a) := by rel [IH]
      _ = 1 + (k + 1) * a + k * a ^ 2 := by ring
      _ ≥ 1 + (k + 1) * a := by extra

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (5:ℤ) ^ (k + 1) = 5 * 5 ^ k := by ring
        _ ≡ 5 * 1 [ZMOD 8] := by rel [hk]
        _ = 5 := by numbers
    · left
      calc (5:ℤ) ^ (k + 1) = 5 * 5 ^ k := by ring
        _ ≡ 5 * 5 [ZMOD 8] := by rel [hk]
        _ = 8 * 3 + 1 := by numbers
        _ ≡ 1 [ZMOD 8] := by extra

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (6:ℤ) ^ (k + 1) = 6 * 6 ^ k := by ring
        _ ≡ 6 * 1 [ZMOD 7] := by rel [hk]
        _ = 6 := by numbers
    · left
      calc (6:ℤ) ^ (k + 1) = 6 * 6 ^ k := by ring
        _ ≡ 6 * 6 [ZMOD 7] := by rel [hk]
        _ = 7 * 5 + 1 := by numbers
        _ ≡ 1 [ZMOD 7] := by extra

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk | hk := IH
    · right
      right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 7] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 2 [ZMOD 7] := by rel [hk]
        _ = 7 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 7] := by extra
    · right
      left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 7] := by rel [hk]
        _ = 7 * 2 + 2 := by numbers
        _ ≡ 2 [ZMOD 7] := by extra

example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 100) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 100 + (100 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 100 := by extra

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k ^ 2 + 4) := by rel [IH]
      _ = k ^ 2 + k * k + 8 := by ring
      _ ≥ k ^ 2 + 5 * k + 8 := by rel [hk]
      _ = (k + 1) ^ 2 + 4 + (3 * k + 3) := by ring
      _ ≥ (k + 1) ^ 2 + 4 := by extra

/- Note.  Two things about the proof below.

These calculations live in `ℕ`, where subtraction is truncated: `3 - 5` is `0`, not `-2`.  So a
slack term must never be written as a difference.  `_ = (k + 1) ^ 3 + (67 * k - 1) := by ring`
fails, and the repair is to bound `67 * k` below by a number first, so that the slack comes out
as a plain numeral.  Splitting a quantity up with `ring` is always safe; subtracting is not.

The bound `k ^ 3 ≥ 3 * k ^ 2 + 3 * k + 1` is pulled out into a `have` of its own rather than
spliced into the middle of the main chain.  It is a fact about `k` with nothing to do with
induction, and separating it leaves a five-line argument that reads as "double the inductive
hypothesis, and the spare copy of `k ^ 3` covers the rest of `(k + 1) ^ 3`". -/

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    have h1 : k ^ 3 ≥ 3 * k ^ 2 + 3 * k + 1 :=
      calc k ^ 3 = k * k ^ 2 := by ring
        _ ≥ 10 * k ^ 2 := by rel [hk]
        _ = 3 * k ^ 2 + 7 * k * k := by ring
        _ ≥ 3 * k ^ 2 + 7 * 10 * k := by rel [hk]
        _ = 3 * k ^ 2 + 3 * k + 67 * k := by ring
        _ ≥ 3 * k ^ 2 + 3 * k + 67 * 10 := by rel [hk]
        _ = 3 * k ^ 2 + 3 * k + 1 + 669 := by ring
        _ ≥ 3 * k ^ 2 + 3 * k + 1 := by extra
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 3 := by rel [IH]
      _ = k ^ 3 + k ^ 3 := by ring
      _ ≥ k ^ 3 + (3 * k ^ 2 + 3 * k + 1) := by rel [h1]
      _ = (k + 1) ^ 3 := by ring

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  obtain ⟨y, hy : a = 2 * y + 1⟩ := ha
  simple_induction n with k IH
  · -- base case
    use 0
    calc a ^ 0 = 1 := by ring
      _ = 2 * 0 + 1 := by numbers
  · -- inductive step
    obtain ⟨x, hx : a ^ k = 2 * x + 1⟩ := IH
    use 2 * x * y + x + y
    calc a ^ (k + 1) = a * a ^ k := by ring
      -- `hx` first: rewriting `a` first would leave no `a ^ k` for `hx` to match
      _ = (2 * y + 1) * (2 * x + 1) := by rw [hx, hy]
      _ = 2 * (2 * x * y + x + y) + 1 := by ring

theorem even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  obtain (h : Even a) | (h : Odd a) := Nat.even_or_odd_lib a
  · apply h
  · have : Odd (a ^ n) := Odd.pow h n
    rw [Nat.odd_iff_not_even] at this
    contradiction
