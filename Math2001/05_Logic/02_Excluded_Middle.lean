/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  `by_cases h : P` splits on whether `P` holds, for any proposition at all, with no
obligation to decide which.  That is the law of the excluded middle, and it is the first thing in
this course that is not constructive.

The pattern it enables is worth seeing clearly.  In the `Superpowered` example below, nobody knows
whether `2` is superpowered, and the proof does not find out.  It says: if it is, take `k = 2`; if
it is not, take `k = 1`.  Either way a `k` exists, and the proof never produces one.

Compare with Section 2.5, where proving `∃` always meant handing over a witness.  Here the
existence claim is settled without a witness ever being named, which is exactly what a
constructive logic forbids and what the summary's optional background was pointing at. -/



-- Book.
def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)


#eval 0 ^ 0 ^ 0 + 1 -- 1
#eval 0 ^ 0 ^ 1 + 1 -- 2
#eval 0 ^ 0 ^ 2 + 1 -- 2


-- Book.
theorem not_superpowered_zero : ¬ Superpowered 0 := by
  intro h
  have one_prime : Prime (0 ^ 0 ^ 0 + 1) := h 0
  conv at one_prime => numbers -- simplifies that statement to `Prime 1`
  have : ¬ Prime 1 := not_prime_one
  contradiction


#eval 1 ^ 1 ^ 0 + 1 -- 2
#eval 1 ^ 1 ^ 1 + 1 -- 2
#eval 1 ^ 1 ^ 2 + 1 -- 2


-- Book.
theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two


#eval 2 ^ 2 ^ 0 + 1 -- 3
#eval 2 ^ 2 ^ 1 + 1 -- 5
#eval 2 ^ 2 ^ 2 + 1 -- 17
#eval 2 ^ 2 ^ 3 + 1 -- 257
#eval 2 ^ 2 ^ 4 + 1 -- 65537


#eval 3 ^ 3 ^ 0 + 1 -- 4
#eval 3 ^ 3 ^ 1 + 1 -- 28
#eval 3 ^ 3 ^ 2 + 1 -- 19684


-- Book.
theorem not_superpowered_three : ¬ Superpowered 3 := by
  intro h
  dsimp [Superpowered] at h
  have four_prime : Prime (3 ^ 3 ^ 0 + 1) := h 0
  conv at four_prime => numbers -- simplifies that statement to `Prime 4`
  have four_not_prime : ¬ Prime 4
  · apply not_prime 2 2
    · numbers -- show `2 ≠ 1`
    · numbers -- show `2 ≠ 4`
    · numbers -- show `4 = 2 * 2`
  contradiction


-- Book.
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  by_cases h2 : Superpowered 2
  · use 2
    constructor
    · apply h2
    · apply not_superpowered_three
  · use 1
    constructor
    · apply superpowered_one
    · apply h2


-- Book.
example {P : Prop} (hP : ¬¬P) : P := by
  by_cases hP : P
  · apply hP
  · contradiction

/-! # Exercises -/


-- Book.
def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

/- Note.  The same manoeuvre as the `Superpowered` example, on a question nobody here is going to
settle: is `1` tribalanced?  Split on it and both answers give a witness.

The `rw [hx]` at the end is bookkeeping.  `0 + 1` and `1` are equal but not syntactically the
same, so `apply h` will not match until one is rewritten into the other. -/

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h : Tribalanced 1
  · use 1
    constructor
    · apply h
    · intro (h2 : Tribalanced (1 + 1))
      have := h2 1
      numbers at this
  · use 0
    constructor
    · intro n
      calc
        (1 + (0:ℝ) / n) ^ n = 1 ^ n := by ring
        _ = 1 := by ring
        _ < 3 := by numbers
    · have hx : (0:ℝ) + 1 = 1 := by numbers
      rw [hx]
      apply h

/- Note.  Contraposition, and the direction that needs excluded middle is the first one.  Given
`Q`, there is no way to extract `P` from `¬P → ¬Q` directly.  You have to split on `P` and rule
out the case where it fails.  The other direction needs nothing. -/

example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  · intro (h : ¬P → ¬Q) (hQ : Q)
    by_cases hP : P
    · apply hP
    · have : ¬ Q := h hP
      contradiction
  · intro (h : Q → P) (hnP : ¬P) (hQ : Q)
    have : P := h hQ
    contradiction

-- Book.
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  by_cases h2 : Superpowered 2
  · use 2
    constructor
    · apply h2
    · apply not_superpowered_three
  · use 1
    constructor
    · apply superpowered_one
    · apply h2
