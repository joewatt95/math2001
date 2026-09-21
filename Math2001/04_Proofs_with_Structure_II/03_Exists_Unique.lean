/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

namespace Int


/- Note.  `∃! a, P a` is shorthand.  Underneath it is

    ∃ a, P a ∧ ∀ y, P y → y = a

so it is the `∃` row of the Chapter 2 table with a second component bolted on.  That shape
dictates every proof here.  `use` supplies the candidate, `dsimp` reveals the conjunction,
`constructor` splits it, and the two halves are quite different jobs.  Existence is usually a
calculation.  Uniqueness starts `intro y hy` and has to drive an arbitrary `y` back to your
candidate.

Uniqueness is the half that needs thought, because you only get to use `P y`.  If the candidate
is pinned down by one consequence of `P`, use that one.  If it takes two, as in the first exercise
below, you have to find a combination of them that forces `y`. -/


-- Book.
example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


/- Note.  The hardest one here.  The candidate is `2`, the midpoint of the interval, and both
halves need an idea.

Existence rests on `1 - (a - 2) ^ 2 = (a - 1) * (3 - a)`, a product of two things the hypotheses
make nonnegative.  `positivity` cannot see that, since it does not read hypotheses, so
`mul_nonneg` is applied by hand to the two bounds.

Uniqueness is the interesting half.  `hy` holds for every `a` in the interval, and neither
endpoint alone pins `y` down: `a = 1` gives `0 ≤ y ≤ 2` and `a = 3` gives `2 ≤ y ≤ 4`.  Adding the
two squares is what collapses it, since `(1 - y) ^ 2 + (3 - y) ^ 2 - 2` is exactly `2 * (y - 2) ^ 2`.
That forces `(y - 2) ^ 2 ≤ 0`, and a square that is at most zero is zero. -/

example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  constructor
  · intro (a : ℚ) (ha1 : a ≥ 1) (ha3 : a ≤ 3)
    have : 0 ≤ (a - 1) * (3 - a) := mul_nonneg (by addarith [ha1]) (by addarith [ha3])
    calc
      (a - 2) ^ 2 = 1 - (a - 1) * (3 - a) := by ring
      _ ≤ 1 - 0 := by rel [this]
      _ = 1 := by ring
  · intro (y : ℚ) (hy : ∀ a, a ≥ 1 → a ≤ 3 → (a - y) ^ 2 ≤ 1)
    have h1 : (1 - y) ^ 2 ≤ 1 := hy 1 (by numbers) (by numbers)
    have h3 : (3 - y) ^ 2 ≤ 1 := hy 3 (by numbers) (by numbers)
    have : (y - 2) ^ 2 ≤ 0 :=
      calc
        (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
        _ ≤ (1 + 1 - 2) / 2 := by rel [h1, h3]
        _ = 0 := by numbers
    have : (y - 2) ^ 2 = 0 := le_antisymm this (by positivity)
    have : y - 2 = 0 := by cancel 2 at this
    addarith [this]

-- Book.
example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1 : a ^ 2 = x, ha2 : ∀ y, y ^ 2 = x → y = a⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


-- Book.
example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1 : 0 ≤ r, hr2 : r < 5, q, hr3 : 14 - r = 5 * q⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  constructor
  · numbers
  · intro (y : ℚ) (hy : 4 * y - 3 = 9)
    calc
      y = (4 * y - 3 + 3) / 4 := by ring
      _ = (9 + 3) / 4 := by rw [hy]
      _ = 3 := by numbers

/- Note.  The uniqueness half is where `∃!` differs from the plain `∃` version of this statement
in Section 4.1.  There `0` only had to be *a* lower bound.  Here any other lower bound `y` must
equal it, and the way to see that is to feed `0` to `hy`, giving `y ≤ 0`. -/

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  · intro a
    extra
  · intro (y : ℕ) (hy : ∀ a, y ≤ a)
    apply le_antisymm
    · show y ≤ 0
      apply hy 0
    · show 0 ≤ y
      extra

/- Note.  Same shape as the `14` example above, and this is the uniqueness of the remainder on
division by `3`.

The hypothesis unpacks four deep, since `∃! r, A ∧ B ∧ C` gives two conjuncts and then the
existential hidden inside the congruence.  Squeezing `q` between `2` and `4` leaves one value, and
`interval_cases` supplies it.

Three conjuncts on the existence side, so the parts are proved separately and assembled with
`⟨...⟩` rather than nesting `constructor` twice. -/

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  constructor
  · have h1 : (0:ℤ) ≤ 2 := by numbers
    have h2 : (2:ℤ) < 3 := by numbers
    have h3 : (11:ℤ) ≡ 2 [ZMOD 3] := by
      use 3
      numbers
    exact ⟨h1, h2, h3⟩
  · intro (r : ℤ) (hr : 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3])
    obtain ⟨hr1 : 0 ≤ r, hr2 : r < 3, q, hr3 : 11 - r = 3 * q⟩ := hr
    have :=
      calc
        3 * 2 < 11 - r := by addarith [hr2]
        _ = 3 * q := by rw [hr3]
    cancel 3 at this
    have :=
      calc
        3 * q = 11 - r := by rw [hr3]
        _ < 3 * 4 := by addarith [hr1]
    cancel 3 at this
    interval_cases q
    addarith [hr3]
