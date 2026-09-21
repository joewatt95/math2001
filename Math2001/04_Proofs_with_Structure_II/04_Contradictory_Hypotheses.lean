/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  A hypothesis can be false.  When it is, the goal no longer matters, and there are two
ways to cash that in.

`contradiction` closes the goal once the context holds both `h` and `¬h`.

`numbers at h` closes it once `h` is a numeric statement that is simply false, such as `7 < 3` or
`0 ≡ 1 [ZMOD 3]`.  That is usually the shorter route, since it skips manufacturing the negation,
and the two examples below show the same proof written each way.

In practice the work is not the contradiction, it is arranging for a false hypothesis to exist.
Most proofs here split into cases and then rule the impossible ones out. -/



-- Book.
example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_gt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


-- Book.
example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


-- Book.
example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


-- Book.
example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · -- the case `1 < m`
    obtain (hm : m = p) | (hm : m < p) := eq_or_lt_of_le (Nat.le_of_dvd hp' hmp)
    · right
      apply hm
    · have : ¬m ∣ p := H m hm_left hm
      contradiction

-- Book.
example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


/- Note.  The longest proof in the chapter, and the shape is worth seeing before the detail.
Split on `a ≤ 2` against `a ≥ 3`.  The second case is the goal.  The whole proof is squeezing the
first case until it collapses.

The squeeze runs on one inequality.  Since `a > 0`, we get `b < c`, so `c ≥ b + 1`, so
`c ^ 2 ≥ b ^ 2 + 2 * b + 1`, which combined with the hypothesis gives `2 * b + 1 ≤ a ^ 2`.  With
`a ≤ 2` that caps `b` at `1`, and `b = 1` then caps `c` at `2`.  Nothing is left but
`a ^ 2 + 1 = 4`, which `numbers at` rejects for both remaining values of `a`.

Pinning `b` and `c` to single values before the final `interval_cases` is deliberate.  Left as
inequalities they feed `interval_cases` extra branches, several of which it discharges silently,
and the bullet structure then stops matching anything you can predict from reading. -/

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain (ha2 : a ≤ 2) | (ha3 : a ≥ 3) := le_or_succ_le a 2

  · have hbc : b + 1 ≤ c := by
      have : b ^ 2 < c ^ 2 :=
        calc
          b ^ 2 < a ^ 2 + b ^ 2 := by extra
          _ = c ^ 2 := h_pyth
      cancel 2 at this
    have key : 2 * b + 1 ≤ a ^ 2 := by
      have :=
        calc
          b ^ 2 + (2 * b + 1) = (b + 1) ^ 2 := by ring
          _ ≤ c ^ 2 := by rel [hbc]
          _ = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ = b ^ 2 + a ^ 2 := by ring
      addarith [this]
    have hb1 : b = 1 := by
      have hup : b ≤ 1 := by
        obtain (h : b ≤ 1) | (h : b ≥ 2) := le_or_succ_le b 1
        · apply h
        · have :=
            calc
              5 = 2 * 2 + 1 := by numbers
              _ ≤ 2 * b + 1 := by rel [h]
              _ ≤ a ^ 2 := key
              _ ≤ 2 ^ 2 := by rel [ha2]
          numbers at this
      apply le_antisymm hup hb
    have hc2 : c = 2 := by
      have hup : c ≤ 2 := by
        obtain (h : c ≤ 2) | (h : c ≥ 3) := le_or_succ_le c 2
        · apply h
        · have :=
            calc
              9 = 3 ^ 2 := by numbers
              _ ≤ c ^ 2 := by rel [h]
              _ = a ^ 2 + b ^ 2 := by rw [h_pyth]
              _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [ha2, hb1.le]
          numbers at this
      apply le_antisymm hup (by addarith [hbc, hb1])
    have hp : a ^ 2 + 1 ^ 2 = 2 ^ 2 := by
      rw [hb1, hc2] at h_pyth
      apply h_pyth
    interval_cases a
    · numbers at hp
    · numbers at hp

  · apply ha3

/-! # Exercises -/


/- Note.  Split on the conclusion itself.  One case is the goal; the other makes `rel` produce
`x ^ n < y ^ n`, which contradicts the hypothesis outright. -/

example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  obtain (hxy : y ≤ x) | (hxy : y > x) := le_or_gt y x
  · apply hxy
  · have hlt : x ^ n < y ^ n := by rel [hxy]
    have : ¬(y ^ n ≤ x ^ n) := by
      apply not_le_of_gt
      apply hlt
    contradiction

/- Note.  Five residues, of which `2` and `3` are the answer and the other three have to be ruled
out.  The squares are `0, 1, 4, 4, 1` modulo `5`, so the surviving cases are exactly those whose
square is `4`.

Each contradiction is built the same way, by chaining a numeral up to `n ^ 2` with `rel` and then
down to `4` with the hypothesis.  Note the `1 ≡ 1 + 5 * 3` opening in the last case: `numbers at`
wants both sides reduced, and will not reject `16 ≡ 4 [ZMOD 5]` on its own. -/

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5

  · have : n ≡ 0 [ZMOD 5] := h
    have H :=
      calc
        (0:ℤ) = 0 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
        _ ≡ 4 [ZMOD 5] := hn
    numbers at H

  · have : n ≡ 1 [ZMOD 5] := h
    have H :=
      calc
        (1:ℤ) = 1 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
        _ ≡ 4 [ZMOD 5] := hn
    numbers at H

  · have : n ≡ 2 [ZMOD 5] := h
    left
    apply h

  · have : n ≡ 3 [ZMOD 5] := h
    right
    apply h

  · have : n ≡ 4 [ZMOD 5] := h
    have H :=
      calc
        (1:ℤ) ≡ 1 + 5 * 3 [ZMOD 5] := by extra
        _ = 4 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
        _ ≡ 4 [ZMOD 5] := hn
    numbers at H

example : Prime 7 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 3
    constructor
    · numbers
    · numbers
  · use 2
    constructor
    · numbers
    · numbers
  · use 1
    constructor
    · numbers
    · numbers
  · use 1
    constructor
    · numbers
    · numbers
  · use 1
    constructor
    · numbers
    · numbers

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain (h4 : x + 2 = 0) | (h4 : x - 2 = 0) := h3
  · have :=
      calc
        (1:ℚ) < x := h2
        _ = -2 := by addarith [h4]
    numbers at this
  · addarith [h4]

namespace Nat

/- Note.  `Prime p` unfolds to `2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`, so `h.2` is the divisor
condition and can be applied to any divisor.  Feeding it `2` is the whole idea: if `p` is even
then `2 ∣ p`, and primality leaves only `2 = 1`, which is false, or `2 = p`. -/

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain (hp : Nat.Even p) | (hp : Nat.Odd p) := Nat.even_or_odd_lib p
  · left
    obtain ⟨k, hk : p = 2 * k⟩ := hp
    have h2 : 2 ∣ p := by
      use k
      apply hk
    obtain (h3 : 2 = 1) | (h3 : 2 = p) := h.2 2 h2
    · numbers at h3
    · addarith [h3]
  · right
    apply hp
