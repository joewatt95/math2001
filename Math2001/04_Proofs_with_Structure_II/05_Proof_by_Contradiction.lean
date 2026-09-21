/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  `¬ P` is notation for `P → False`, so `intro h` works on it exactly as on any other
implication.  Assume the thing you want to refute, then derive something false.

That makes every proof here two halves.  The `intro` is free; the work is manufacturing a false
statement, and the tools for that are Section 4.4's.  Most often it is a numeric absurdity closed
by `numbers at`, sometimes a hypothesis sitting beside its own negation, closed by
`contradiction`.

One habit worth picking up early.  `numbers at h` only rejects statements built from numerals, so
`p < 0` with `p` a variable is not enough even over `ℕ`.  Chain it against a numeric bound first
and give `numbers` something like `2 < 0` to reject. -/



-- Book.
example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro (h : ∀ x : ℝ, x ^ 2 ≥ x)
  have : (0.5 : ℝ) ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro (H : 3 ∣ 13)
  obtain ⟨k, hk : 13 = 3 * k⟩ := H
  obtain (h4 : k ≤ 4) | (h5 : k ≥ 5) := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
      calc
        15 = 3 * 5 := by numbers
        _ ≤ 3 * k := by rel [h5]
        _ = 13 := by rw [hk]
    numbers at h

-- Book.
example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


/- Note.  Refuting an existential means taking the witness apart and cornering it.  Split at the
only interesting place, `n ≤ 1` against `n ≥ 2`, and both sides overshoot `2`. -/

example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, hn : n ^ 2 = 2⟩ := h
  obtain (h1 : n ≤ 1) | (h2 : n ≥ 2) := le_or_succ_le n 1
  · have :=
      calc
        2 = n ^ 2 := by rw [hn]
        _ ≤ 1 ^ 2 := by rel [h1]
    numbers at this
  · have :=
      calc
        4 = 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [h2]
        _ = 2 := hn
    numbers at this

-- Book.
example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro (h1 : Int.Even n) (h2 : Int.Odd n)
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain (h1 : Int.Even n) | (h2 : Int.Odd n) := Int.even_or_odd_lib n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro (h1 : Int.Odd n) (h2 : Int.Even n)
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have h :=
      calc
        (1:ℤ) ≡ n [ZMOD 2] := by rel [h1]
        _ ≡ 0 [ZMOD 2] := by rel [h2]
    numbers at h
  · intro h
    obtain (h1 : Int.Even n) | (h2 : Int.Odd n) := Int.even_or_odd_lib n
    · contradiction
    · apply h2

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h' :=
      calc
        (1:ℤ) = 1 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h'
  · have h' :=
      calc
        (1:ℤ) ≡ 1 + 3 * 1 [ZMOD 3] := by extra
        _ = 2 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h'

-- Book.
example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2 : 2 ≤ p, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk : a = b * k⟩ := H
  obtain ⟨q, hq₁ : b * q < a, hq₂ : a < b * (q + 1)⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  have h2 :=
    calc
      b * q < a := hq₁
      _ = b * k := hk
  cancel b at h2
  have h3 : q + 1 ≤ k := by addarith [h2]
  have : ¬(k < q + 1) := by
    apply not_lt_of_ge
    apply h3
  contradiction

example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m (hm1 : 1 < m) (hmp : m < p)
  obtain (hmT : m < T) | (hmT : T ≤ m) := lt_or_ge m T
  · apply H m hm1 hmT
  intro (h_div : m ∣ p)
  obtain ⟨l, hl : p = m * l⟩ := h_div
  have : l ∣ p
  · use m
    calc
      p = m * l := hl
      _ = l * m := by ring
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · have hT : 0 < T := by
      obtain (h : T = 0) | (h : 1 ≤ T) := Nat.eq_zero_or_pos T
      · have :=
          calc
            2 ≤ p := hp
            _ < T ^ 2 := hTp
            _ = 0 ^ 2 := by rw [h]
            _ = 0 := by numbers
        numbers at this
      · apply h
    have key :=
      calc
        T * l ≤ m * l := by rel [hmT]
        _ = p := by rw [hl]
        _ < T ^ 2 := hTp
        _ = T * T := by ring
    cancel T at key
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain ⟨t, ht4 : t ≤ 4, ht5 : t ≥ 5⟩ := h
  have :=
    calc
      (5:ℝ) ≤ t := ht5
      _ ≤ 4 := ht4
  numbers at this

/- Note.  The two hypotheses are about different powers, so neither contradicts the other
directly.  Raising both to reach `a ^ 6` is what lets them meet: `a ^ 3 ≥ 30` gives `a ^ 6 ≥ 900`
and `a ^ 2 ≤ 8` gives `a ^ 6 ≤ 512`.

Finding the common power is the idea here.  Everything after it is `rel` and `ring`. -/

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro h
  obtain ⟨a, h2 : a ^ 2 ≤ 8, h3 : a ^ 3 ≥ 30⟩ := h
  have :=
    calc
      (900:ℝ) = 30 ^ 2 := by numbers
      _ ≤ (a ^ 3) ^ 2 := by rel [h3]
      _ = (a ^ 2) ^ 3 := by ring
      _ ≤ 8 ^ 3 := by rel [h2]
      _ = 512 := by numbers
  numbers at this

example : ¬ Int.Even 7 := by
  intro h
  obtain ⟨k, hk : 7 = 2 * k⟩ := h
  obtain (h1 : k ≤ 3) | (h2 : k ≥ 4) := le_or_succ_le k 3
  · have :=
      calc
        (7:ℤ) = 2 * k := hk
        _ ≤ 2 * 3 := by rel [h1]
    numbers at this
  · have :=
      calc
        (8:ℤ) = 2 * 4 := by numbers
        _ ≤ 2 * k := by rel [h2]
        _ = 7 := by rw [hk]
    numbers at this

/- Note.  The parity half of the conjunction is a red herring.  `hn` pins `n` to `4` and
`4 ^ 2 = 16` settles it, so `Int.Even n` is never unpacked at all.  The `-` in the `obtain`
pattern throws that component away, which says so on the page. -/

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro h
  obtain ⟨-, hsq : n ^ 2 = 10⟩ := h
  have hn4 : n = 4 := by addarith [hn]
  have :=
    calc
      (10:ℤ) = n ^ 2 := by rw [hsq]
      _ = 4 ^ 2 := by rw [hn4]
      _ = 16 := by numbers
  numbers at this

/- Note.  The negative branch needs care.  `rel` will not square `x ≤ -3` directly, since
squaring reverses for negatives, so flip it to `-x ≥ 3` first and use `(-x) ^ 2 = x ^ 2`. -/

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro h
  obtain (h1 : x ≤ -3) | (h2 : x ≥ 3) := h
  · have h1' : -x ≥ 3 := by addarith [h1]
    have :=
      calc
        (9:ℝ) = 3 ^ 2 := by numbers
        _ ≤ (-x) ^ 2 := by rel [h1']
        _ = x ^ 2 := by ring
        _ < 9 := hx
    numbers at this
  · have :=
      calc
        (9:ℝ) = 3 ^ 2 := by numbers
        _ ≤ x ^ 2 := by rel [h2]
        _ < 9 := hx
    numbers at this

/- Note.  To refute "everything past some point is even", produce one odd number past that point.
`2 * N + 1` works for any `N`, and showing it exceeds `N` is itself a small step, since `extra`
needs the goal in the shape `N < N + something`.

`le_or_succ_le` is unavailable here because its second argument must be a literal and `N` is a
variable, so `le_or_gt` does the split instead. -/

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro h
  obtain ⟨N, hN : ∀ k > N, Nat.Even k⟩ := h
  have hgt : 2 * N + 1 > N := by
    calc
      N < N + (N + 1) := by extra
      _ = 2 * N + 1 := by ring
  obtain ⟨m, hm : 2 * N + 1 = 2 * m⟩ := hN (2 * N + 1) hgt
  obtain (h2 : m ≤ N) | (h3 : N + 1 ≤ m) := le_or_gt m N
  · have :=
      calc
        2 * N + 1 = 2 * m := hm
        _ ≤ 2 * N := by rel [h2]
    have h4 : (1:ℕ) ≤ 0 := by addarith [this]
    numbers at h4
  · have :=
      calc
        2 * N + 2 = 2 * (N + 1) := by ring
        _ ≤ 2 * m := by rel [h3]
        _ = 2 * N + 1 := by rw [hm]
    have h4 : (2:ℕ) ≤ 1 := by addarith [this]
    numbers at h4

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro h
  mod_cases hn : n % 4
  · have H :=
      calc
        (0:ℤ) = 0 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at H
  · have H :=
      calc
        (1:ℤ) = 1 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at H
  · have H :=
      calc
        (0:ℤ) ≡ 0 + 4 * 1 [ZMOD 4] := by extra
        _ = 2 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at H
  · have H :=
      calc
        (1:ℤ) ≡ 1 + 4 * 2 [ZMOD 4] := by extra
        _ = 3 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
        _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at H

example : ¬ Prime 1 := by
  intro h
  obtain ⟨h2 : 2 ≤ 1, -⟩ := h
  numbers at h2

example : Prime 97 := by
  apply better_prime_test (T := 10)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 48
    constructor <;> numbers
  · use 32
    constructor <;> numbers
  · use 24
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 16
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 12
    constructor <;> numbers
  · use 10
    constructor <;> numbers
