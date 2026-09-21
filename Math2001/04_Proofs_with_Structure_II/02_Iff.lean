/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

namespace Int


/- Note.  The last row of the table from the Chapter 2 summary.

                    to prove it              to use it
    P ↔ Q           constructor              rw [h]   (or `apply h.mp` / `h.mpr`)

`constructor` splits an `↔` into the two implications, so every proof here opens the same way and
has two bullets.  Each of those starts with `intro`, since an implication is proved by assuming
its hypothesis.

The second half of the section is the payoff.  Once `Odd n ↔ n ≡ 1 [ZMOD 2]` is available, `rw`
can trade one for the other, and a statement about parity becomes a calculation in modular
arithmetic.  An `↔` is a licence to rewrite, which is what makes it worth more than two separate
implications. -/


-- Book.
example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


-- Book, annotated.
example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha : 5 * n = 8 * a⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha : n = 8 * a⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk : n = 2 * k + 1⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk : n - 1 = 2 * k⟩ := h
    use k
    addarith [hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk : n = 2 * k⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk : n - 0 = 2 * k⟩ := h
    use k
    addarith [hk]

/- Note.  The two directions are quite different in character, which is normal for an `↔`.  Going
right needs the factorisation and a case split; coming back is two rewrites.  Expect one side to
carry most of the weight. -/

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have :=
      calc
        (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
        _ = 0 := h
    obtain (hx : x + 3 = 0) | (hx : x - 2 = 0) := eq_zero_or_eq_zero_of_mul_eq_zero this
    · left
      show x = -3
      addarith [hx]
    · right
      show x = 2
      addarith [hx]
  · intro h
    obtain (hx : x = -3) | (hx : x = 2) := h
    · rw [hx]
      ring
    · rw [hx]
      ring

/- Note.  The hardest exercise in the section.  The idea is to squeeze the inequality down to a
finite list of candidates, which `interval_cases` then enumerates.

Two things bite.  `addarith` will not divide by `2` over `ℤ`, since halving is not a ring
operation there, so `cancel` does it.  And the square is completed on `2 * a - 5` rather than
`a - 5 / 2` for the same reason. -/

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    have :=
      calc
        (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
        _ ≤ 4 * (-1) + 5 := by rel [h]
        _ = 1 ^ 2 := by numbers
    obtain ⟨h2 : -1 ≤ 2 * a - 5, h3 : 2 * a - 5 ≤ 1⟩ :=
      abs_le_of_sq_le_sq' this (by numbers)
    have ha2 : 2 ≤ a := by
      have : 2 * 2 ≤ 2 * a := by addarith [h2]
      cancel 2 at this
    have ha3 : a ≤ 3 := by
      have : 2 * a ≤ 2 * 3 := by addarith [h3]
      cancel 2 at this
    interval_cases a
    · left
      numbers
    · right
      numbers
  · intro h
    obtain (ha : a = 2) | (ha : a = 3) := h
    · rw [ha]
      numbers
    · rw [ha]
      numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain (hn3 : n - 4 = 0) | (hn3 : n - 6 = 0) := hn2
  · use 2
    addarith [hn3]
  · use 3
    addarith [hn3]

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain (hn2 : n - 4 = 0) | (hn2 : n - 6 = 0) := hn1
  · use 2
    addarith [hn2]
  · use 3
    addarith [hn2]

-- Book.
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


/- Note.  `addarith` cannot close the forward direction, because getting from `2 * x - 1 = 11` to
`x = 6` means halving, and that is outside what it does.  Three `calc` lines do it instead.  The
reverse direction is a rewrite. -/

example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    calc
      x = (2 * x - 1 + 1) / 2 := by ring
      _ = (11 + 1) / 2 := by rw [h]
      _ = 6 := by numbers
  · intro h
    rw [h]
    numbers

/- Note.  Both directions have appeared before.  Going right is the easy split, since `63 = 7 * 9`.
Coming back is the Bezout argument from Section 3.5, and it is the direction that needs `7` and `9`
to be coprime. -/

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h
    obtain ⟨k, hk : n = 63 * k⟩ := h
    constructor
    · show 7 ∣ n
      use 9 * k
      calc
        n = 63 * k := hk
        _ = 7 * (9 * k) := by ring
    · show 9 ∣ n
      use 7 * k
      calc
        n = 63 * k := hk
        _ = 9 * (7 * k) := by ring
  · intro h
    obtain ⟨h7 : 7 ∣ n, h9 : 9 ∣ n⟩ := h
    obtain ⟨a, ha : n = 7 * a⟩ := h7
    obtain ⟨b, hb : n = 9 * b⟩ := h9
    use 4 * b - 3 * a
    calc
      n = 28 * n - 27 * n := by ring
      _ = 28 * (9 * b) - 27 * n := by rw [hb]
      _ = 28 * (9 * b) - 27 * (7 * a) := by rw [ha]
      _ = 63 * (4 * b - 3 * a) := by ring

/- Note.  Both sides are the same existential once unfolded, and the whole proof is `addarith`
moving a `- 0` around.  Worth doing anyway, because it is the bridge that lets the next exercise
be a modular calculation rather than an algebraic one. -/

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  · intro h
    obtain ⟨k, hk : a = n * k⟩ := h
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk : a - 0 = n * k⟩ := h
    use k
    addarith [hk]

/- Note.  This is the exercise from Section 3.2, done the other way round.  There it meant
unpacking the divisibility, substituting and factoring by hand.  Here `dvd_iff_modEq` turns both
the hypothesis and the goal into congruences, after which `rel` substitutes `0` for `b` and the
arithmetic is trivial.

Comparing the two proofs is the point of the section. -/

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  rw [Int.dvd_iff_modEq] at *
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b ≡ 2 * 0 ^ 3 - 0 ^ 2 + 3 * 0 [ZMOD a] := by rel [hab]
    _ = 0 := by numbers

/- Note.  Three disjuncts, so `left` and `right` have to be combined: the second case is `right`
then `left`, the third is `right` twice.  An `∨` of three is really two nested `∨`s.

The forward direction splits at `2` and rules out everything above by arithmetic.  Deriving a
false numeric statement and letting `numbers at` close the branch is the subject of Section 4.4,
and this is a first sighting.

`interval_cases k` substitutes the value, so the branches carry no case hypothesis.  Where the
branches are one-liners that say which case they are, as here, that is fine.  When it is not,
`interval_cases hk : k` names the hypothesis the way `mod_cases` does, and each branch can open by
restating it. -/

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    obtain (hk : k ≤ 2) | (hk : k ≥ 3) := le_or_succ_le k 2

    · interval_cases k
      · left
        numbers
      · right
        left
        numbers
      · right
        right
        numbers

    · have :=
        calc
          9 = 3 ^ 2 := by numbers
          _ ≤ k ^ 2 := by rel [hk]
          _ ≤ 6 := h
      numbers at this
  · intro h
    obtain (hk : k = 0) | (hk : k = 1) | (hk : k = 2) := h
    · rw [hk]
      numbers
    · rw [hk]
      numbers
    · rw [hk]
      numbers
