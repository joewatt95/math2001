/- Live-coding statements: Chapters 4 and 5.  Not part of Macbeth's text.

This set covers Chapter 4 (Proofs with Structure II) and Chapter 5 (Logic).  Other chapters get
their own directory alongside this one.

Just the statements, in the order to run them.  Notes, drafting skeletons and finished proofs
are in `Notes.lean`, meant to be open in a second window.

Ordered by priority: work down, and stop wherever the time runs out. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Rel

math2001_init


-- 1.  A composite number has a proper divisor.  (Section 5.3, last exercise.  ~10 min)

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have : ¬ (∀ m, 2 ≤ m → m < p → ¬ m ∣ p) := by
    intro h
    apply hp
    apply prime_test
    · apply hp2
    · intro m (h0 : 1 < m)
      have : 2 ≤ m := by rel [h0]
      apply h
      apply this
  push_neg at this
  apply this

-- 2.  A Pythagorean triple has no leg smaller than 3.  (Section 4.4.  ~20 min)

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  sorry


-- 3.  `not_forall`, by hand.  (Section 5.3, third exercise.  ~12 min)

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · sorry
  · sorry


-- 4.  Exactly one point is within 1 of everything in [1, 3].  (Section 4.3.  ~12 min)

example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  sorry
