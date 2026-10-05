/- Live-coding statements: Chapter 6.  Not part of Macbeth's text.

This set covers Chapter 6 (Induction).  Other chapters get their own directory alongside this one.

Just the statements, in the order to run them.  Notes, drafting skeletons and finished proofs
are in `Notes.lean`, meant to be open in a second window.

Ordered by priority: work down, and stop wherever the time runs out. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Rel

math2001_init


-- 1.  A recurrence that stays in `{2, 3}` mod 7.  (Section 6.3, exercise.  ~20 min)

def p : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 6 * p (n + 1) - p n

example (m : ℕ) : p m ≡ 2 [ZMOD 7] ∨ p m ≡ 3 [ZMOD 7] := by
  sorry


-- 2.  Fibonacci, between two exponentials.  (Section 6.3, last exercise.  ~20 min)

def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

example : forall_sufficiently_large n : ℕ,
    (0.4:ℚ) * 1.6 ^ n < F n ∧ F n < (0.5:ℚ) * 1.7 ^ n := by
  sorry


-- 3.  `2 ^ n` eventually beats `n ^ 3`.  (Section 6.1, exercise.  ~12 min)

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  sorry


-- 4.  Every positive integer is a power of two times an odd number.  (Section 6.4, exercise.
--     ~12 min)

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Nat.Odd x ∧ n = 2 ^ a * x := by
  sorry
