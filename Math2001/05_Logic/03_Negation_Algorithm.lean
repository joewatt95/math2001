/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  Pushing a negation inwards is mechanical, and the section shows it twice over.

By hand, each step is one equivalence applied with `rel`: `not_forall`, `not_exists`,
`Classical.not_imp`, `not_and_or`, `not_or`, `not_lt`, `not_le`.  The `calc` chains below are
that algorithm written out.

`push_neg` runs the whole algorithm at once.  Use `#push_neg` on a statement to see where it
lands before committing to it, which is worth doing, because the result is not always the shape
you expected.  Negating `∃ t, t ≤ 4 ∧ t ≥ 5` gives `∀ t, 4 < t ∨ t < 5`, a disjunction rather
than the implication `t ≤ 4 → t < 5` you might have written by hand.  The two are equivalent, but
only one of them is what `intro` will accept. -/



example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro (h : ¬(P ∧ Q))
    by_cases hP : P
    · right
      intro (hQ : Q)
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro (h : ¬ P ∨ ¬ Q) (hPQ : P ∧ Q)
    obtain ⟨hP : P, hQ : Q⟩ := hPQ
    obtain (hnP : ¬ P) | (hnQ : ¬ Q) := h
    · contradiction
    · contradiction

-- Book.
example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [Classical.not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


/- Note.  The same algorithm as the example above, one equivalence per step.  `not_and_or` and
`not_lt` go in separate steps rather than one `rel [not_and_or, not_lt]`, because with both at
once Lean cannot work out which ordered type `not_lt` is about and reports a stuck instance. -/

example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
  calc ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
      ↔ ∃ n : ℤ, ¬(∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_forall]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬(n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_exists]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬(n ^ 2 < m) ∨ ¬(m < (n + 1) ^ 2) := by rel [not_and_or]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by rel [not_lt]

#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain (hn : n ≤ 1) | (hn : n ≥ 2) := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      2 < 2 ^ 2 := by numbers
      _ ≤ n ^ 2 := by rel [hn]

/-! # Exercises -/


/- Note.  Going right is where excluded middle is needed.  From `¬¬P` there is no direct route to
`P`, so split on `P` and let the negative case collide with the hypothesis. -/

example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  · intro (h : ¬¬P)
    by_cases hP : P
    · apply hP
    · contradiction
  · intro (hP : P) (hnP : ¬ P)
    contradiction

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro (h : ¬(P → Q))
    constructor
    · by_cases hP : P
      · apply hP
      · have : P → Q := by
          intro (hP' : P)
          contradiction
        contradiction
    · intro (hQ : Q)
      have : P → Q := by
        intro (_ : P)
        apply hQ
      contradiction
  · intro (h : P ∧ ¬ Q) (hPQ : P → Q)
    obtain ⟨hP : P, hnQ : ¬ Q⟩ := h
    have : Q := hPQ hP
    contradiction

/- Note.  This is `not_forall`, proved from scratch.  The right-hand direction is the one that
needs excluded middle, twice over: once to ask whether the required `x` exists, and again inside
to ask whether `P x` holds for an arbitrary `x`.  That is why `push_neg` is not constructive. -/

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro (h : ¬ ∀ x, P x)
    by_cases hex : ∃ x, ¬ P x
    · apply hex
    · have : ∀ x, P x := by
        intro x
        by_cases hx : P x
        · apply hx
        · have : ∃ x, ¬ P x := by
            use x
            apply hx
          contradiction
      contradiction
  · intro (h : ∃ x, ¬ P x) (h' : ∀ x, P x)
    obtain ⟨x, hx : ¬ P x⟩ := h
    have : P x := h' x
    contradiction

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  calc (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
      ↔ ∃ a : ℤ, ¬ ∀ b : ℤ, a * b = 1 → a = 1 ∨ b = 1 := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, ¬(a * b = 1 → a = 1 ∨ b = 1) := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ ¬(a = 1 ∨ b = 1) := by rel [Classical.not_imp]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ (a ≠ 1 ∧ b ≠ 1) := by rel [not_or]

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  calc (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x)
      ↔ ∀ x : ℝ, ¬ ∀ y : ℝ, y ≤ x := by rel [not_exists]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, ¬ (y ≤ x) := by rel [not_forall]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, y > x := by rel [not_le]

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  calc ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5)
      ↔ ∀ m : ℤ, ¬ ∀ n : ℤ, m = n + 5 := by rel [not_exists]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by rel [not_forall]

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers

/- Note.  Look at what `push_neg` produced before writing anything.  The goal is
`∀ t, 4 < t ∨ t < 5`, a disjunction, so `intro t` then `intro ht` will not work.  Split on where
`t` sits and pick the disjunct that holds. -/

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  obtain (h : t ≤ 4) | (h : 4 < t) := le_or_gt t 4
  · right
    calc
      t ≤ 4 := h
      _ < 5 := by numbers
  · left
    apply h

/- Note.  Compare with the proof of the same statement in Section 4.5.  There it opened with
`intro h` and unpacked the existential by hand.  Here `dsimp` exposes the definition and
`push_neg` turns the goal straight into `∀ k, 7 ≠ 2 * k`, which is the same work with the
bookkeeping done for you. -/

example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro k
  obtain (h1 : k ≤ 3) | (h2 : k ≥ 4) := le_or_succ_le k 3
  · apply ne_of_gt
    calc
      2 * k ≤ 2 * 3 := by rel [h1]
      _ < 7 := by numbers
  · apply ne_of_lt
    calc
      (7:ℤ) < 2 * 4 := by numbers
      _ ≤ 2 * k := by rel [h2]

/- Note.  Another shape worth checking before writing.  `Prime p` is a conjunction, so its
negation is a disjunction, and the goal after `push_neg` is
`p < 2 ∨ ∃ m, m ∣ p ∧ m ≠ 1 ∧ m ≠ p`.  Nothing here says anything about `p < 2`, so the second
disjunct is the one to take. -/

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  right
  use k
  exact ⟨hk, hk1, hkp⟩

/- Note.  After `push_neg` the goal is `∀ a, ∃ n, 2 * a ^ 3 < n * a + 7`, so `n` may depend on
`a` and must be chosen after seeing it.

No single formula works for every `a`, because multiplying by `a` reverses the inequality when
`a` is negative.  Split on the sign and pick `2 * a ^ 2 - 1` or `2 * a ^ 2 + 1` accordingly; each
leaves a slack of `-a` or `+a` that the case assumption makes harmless. -/

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  obtain (ha : a ≤ 0) | (ha : a ≥ 1) := le_or_succ_le a 0
  · use 2 * a ^ 2 - 1
    calc
      2 * a ^ 3 = (2 * a ^ 2 - 1) * a + a := by ring
      _ ≤ (2 * a ^ 2 - 1) * a + 0 := by rel [ha]
      _ = (2 * a ^ 2 - 1) * a := by ring
      _ < (2 * a ^ 2 - 1) * a + 7 := by extra
  · use 2 * a ^ 2 + 1
    calc
      2 * a ^ 3 = (2 * a ^ 2 + 1) * a - a := by ring
      _ < (2 * a ^ 2 + 1) * a + 7 := by addarith [ha]

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro (H : ∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
    have : Prime p := by
      apply prime_test hp2
      intro m (hm1 : 1 < m) (hmp : m < p)
      apply H m hm1 hmp
    contradiction
  push_neg at H
  obtain ⟨m, hm2 : 2 ≤ m, hmp : m < p, hmdvd : m ∣ p⟩ := H
  use m
  exact ⟨hm2, hmp, hmdvd⟩
