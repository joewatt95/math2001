/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/


/- Note.  Two more rows for the table in the Chapter 2 summary, and they behave like the ones
already there.

                    to prove it              to use it
    ∀ x, P x        intro x                  apply h   (or `h t` for a chosen `t`)
    P → Q           intro h                  apply h

To prove "for all `x`", say `intro x` and then prove the statement for that one arbitrary `x`.  To
use a "for all", pick a value and apply it.  Implication works the same way, which is why Lean
uses the same tactic for both.

The asymmetry is the familiar one.  Proving a `∀` means you may assume nothing about `x`.  Using
one means you get to choose, and choosing well is most of the work in this section.  The first
example uses `h` at `1` because `1` is where `x ^ 2 - 2 * x` bottoms out, and no other choice
proves the goal. -/


-- Book.
example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by numbers


-- Book.
example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  have h1 : n ∣ 1 := by apply hn
  have h2 : 0 < 1 := by numbers
  apply le_antisymm
  · apply Nat.le_of_dvd h2 h1
  · apply Nat.pos_of_dvd_of_pos h1 h2


/- Note.  `h` holds for every `x`, so the whole proof is choosing the right one.  The midpoint
`(a + b) / 2` works because whichever side of the disjunction comes back, rearranging it gives
`a ≤ b` directly, so neither branch is a dead end.

`addarith` cannot finish either branch, since the division puts it out of reach, so each rearranges
by hand in three lines.

Note where the `_` goes.  The pattern states both cases in full, and the argument to `h` is left
blank.  Lean recovers it from the annotations, so `(a + b) / 2` is written once, in the position
where it reads as a statement about the two branches rather than as an argument being passed.

Writing `h ((a + b) / 2)` instead and shortening the annotations works equally well for Lean.  It
just puts the interesting term in the least interesting place. -/

example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  obtain (hx : ((a + b) / 2) ≥ a) | (hx : ((a + b) / 2) ≤ b) := h _

  · calc
      a = 2 * a - a := by ring
      _ ≤ 2 * ((a + b) / 2) - a := by rel [hx]
      _ = b := by ring

  · calc
      a = 2 * ((a + b) / 2) - b := by ring
      _ ≤ 2 * b - b := by rel [hx]
      _ = b := by ring

example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by
  apply le_antisymm
  · apply hb2
    apply ha1
  · apply ha2
    apply hb1

-- Book.
example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by extra
    _ = x ^ 2 - 2 * x := by ring


/- Note.  Any `c` below the true minimum will do, and `-3` is both valid and easy to reach.  The
bound comes from `(x + 1) ^ 2 ≥ 0`, which rearranges to `x ≥ -(x ^ 2 + 1) / 2`, and the same for
`y`.  Adding the two and using the hypothesis gives `-3`.

Finding a witness that is generous enough to be provable but still correct is the skill here.
Chasing the exact minimum, `-2 * √2`, would be much more work for no extra credit. -/

example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y h
  calc
    x + y = -((x ^ 2 + y ^ 2 + 2) / 2) + ((x + 1) ^ 2 + (y + 1) ^ 2) / 2 := by ring
    _ ≥ -((x ^ 2 + y ^ 2 + 2) / 2) := by extra
    _ ≥ -((4 + 2) / 2) := by rel [h]
    _ = -3 := by numbers

-- Book.
example : forall_sufficiently_large n : ℤ, n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  dsimp
  use 5
  intro n hn
  calc
    n ^ 3 = n * n ^ 2 := by ring
    _ ≥ 5 * n ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + n ^ 2 := by ring
    _ ≥ 4 * n ^ 2 + 5 ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + 7 + 18 := by ring
    _ ≥ 4 * n ^ 2 + 7 := by extra


-- Book.
example : Prime 2 := by
  constructor
  · numbers -- show `2 ≤ 2`
  intro m hmp
  have hp : 0 < 2 := by numbers
  have hmp_le : m ≤ 2 := Nat.le_of_dvd hp hmp
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp
  interval_cases m
  · left
    numbers -- show `1 = 1`
  · right
    numbers -- show `2 = 2`


-- Book.
example : ¬ Prime 6 := by
  apply not_prime 2 3
  · numbers -- show `2 ≠ 1`
  · numbers -- show `2 ≠ 6`
  · numbers -- show `6 = 2 * 3`

/-! # Exercises -/


/- Note.  Again the whole proof is the choice of `b`.  The right-hand side is largest at `b = 2`,
where it equals `1`, so that is the only value of `b` that gives the bound asked for.  Complete the
square on paper before typing anything. -/

example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 :=
  calc
    a ≥ -3 + 4 * 2 - 2 ^ 2 := by apply h
    _ = 1 := by numbers

/- Note.  `hn` has two hypotheses as well as the `∀`, so `apply hn` leaves both of them as goals,
one bullet each.

Of the five divisors available, only `3` and `5` are wanted.  After that it is the Bezout argument
from Section 3.5, with `2 * 3 - 1 * 5 = 1`. -/

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have : 3 ∣ n := by
    apply hn
    · numbers
    · numbers
  obtain ⟨a, ha : n = 3 * a⟩ := this
  have : 5 ∣ n := by
    apply hn
    · numbers
    · numbers
  obtain ⟨b, hb : n = 5 * b⟩ := this
  use 2 * b - a
  calc
    n = 6 * n - 5 * n := by ring
    _ = 6 * (5 * b) - 5 * n := by rw [hb]
    _ = 6 * (5 * b) - 5 * (3 * a) := by rw [ha]
    _ = 15 * (2 * b - a) := by ring

/- Note.  A rare case where the answer is easier than it looks.  Over `ℕ` every number is at least
`0`, so `0` is a least element and `extra` closes it.  The same statement over `ℤ` is false, which
is worth saying out loud. -/

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0
  intro m
  extra

/- Note.  Three quantifiers alternating, which is where reading the order carefully starts to
matter.  `a` is fixed once and for all, `b` is then handed to you, and only after seeing `b` do you
choose `c`.  So `c` may mention `b`, and `a` may mention neither.

Any `a` works, since `c` is chosen last and can always be made large enough. -/

example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  use 0
  intro b
  use b + 1
  calc
    0 + b = b := by ring
    _ < b + 1 := by extra

/- Note.  `forall_sufficiently_large x, P x` is `∃ C, ∀ x ≥ C, P x`, so `dsimp` reveals it, `use`
supplies the threshold and `intro` takes an `x` past it.

`8` is chosen so the leftovers are comfortably positive.  There is nothing special about it, and
any larger threshold works just as well.  Picking a generous one makes the inequalities easier,
which is the same lesson as the `c = -3` exercise above. -/

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 8
  intro x hx
  calc
    x ^ 3 + 3 * x = x * x ^ 2 + 3 * x := by ring
    _ ≥ 8 * x ^ 2 + 3 * x := by rel [hx]
    _ = 7 * x ^ 2 + x ^ 2 + 3 * x := by ring
    _ ≥ 7 * x ^ 2 + 8 ^ 2 + 3 * 8 := by rel [hx]
    _ = 7 * x ^ 2 + 12 + 76 := by ring
    _ ≥ 7 * x ^ 2 + 12 := by extra

example : ¬(Prime 45) := by
  apply not_prime 5 9
  · numbers
  · numbers
  · numbers
