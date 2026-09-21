/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/


/- Note.  Taking an `∧` apart uses the same tactic as taking an `∨` apart, with different
punctuation.  Angle brackets for "and", `obtain ⟨h1, h2⟩ := h`, because you get both at once.  A
vertical bar for "or", `obtain h1 | h2 := h`, because you get one branch or the other.  The
brackets are typed `\langle` and `\rangle`, or `\<>` for the pair.

Annotation works here too, and is worth the space for the same reason as in Section 2.3:

    obtain ⟨h1 : 2 * x - y = 4, h2 : y - x + 1 = 2⟩ := h

Lean checks those statements, so they cannot drift out of step with what `h` actually says. -/

-- Book.
example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


/- Note.  Two things here are typical of working with the library.

`abs_le_of_sq_le_sq'` hands back a conjunction, `-3 ≤ p ∧ p ≤ 3`, which is then immediately taken
apart by `obtain`.  Lemmas package several conclusions together like this fairly often, and
`have` followed by `obtain` is the ordinary way to unwrap one.  The `_` in `obtain ⟨h1, _⟩ := this`
says you are deliberately discarding the other half.  Naming it and never using it would compile
just as well, but the underscore records the intent, so nobody goes hunting for where it was used.

The other thing is a readability warning rather than a technique.  `apply abs_le_of_sq_le_sq'`
leaves two goals, the `calc` and the `numbers` after it, because the lemma has two hypotheses.
They are written here as a flat sequence, which is legal but makes it genuinely hard to see where
the first ends and the second begins.  Bullets, as used everywhere else in this chapter, would
show the structure at a glance.  It is worth adopting them as soon as a tactic leaves more than
one goal, even when Lean is happy without. -/

example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have : -3 ≤ p ∧ p ≤ 3 := by
    apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  obtain ⟨h1, _⟩ := this
  calc
    p ≥ -3 := h1
    _ ≥ -5 := by numbers

/- Note.  The next two examples prove the same statement twice, which is easy to skim past.  The
difference is where `b = 1` gets established.

The first works it out inside the calc chain, going through `_ = -6 + 5 * (b + 2)` so that
`rw [h2]` has something to act on.  The second hoists it into `have hb : b = 1` before
`constructor`, after which both halves of the conjunction simply use it.

The second is the better habit as proofs grow.  The fact is stated once, carries a name, and is
available to both branches, instead of being re-derived inside whichever branch happens to want
it.  That matters more here than usual, because `constructor` splits the proof in two and anything
proved before the split is shared, while anything proved after it is not. -/

-- Book, annotated.
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · show a = 9
    calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · show b = 1
    addarith [h2]


-- Book, annotated.
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · show a = 9
    calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · show b = 1
    apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  constructor
  · show a = 0
    have : a ^ 2 = 0 := by
      apply le_antisymm
      · calc
        a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
        _ = 0 := by rw [h1]
      · extra
    cancel 2 at this
  · show b = 0
    have : b ^ 2 = 0 := by
      apply le_antisymm
      · calc
        b ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
        _ = 0 := by rw [h1]
      · extra
    cancel 2 at this

/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2*a + b = a + (a + b) := by ring
          _ ≤ 1 + 3 := by rel [h1, h2]
          _ = 4 := by ring

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2*r = (r + s) + (r - s) := by ring
          _ ≤ 1 + 5 := by rel [h1, h2]
          _ = 6 := by ring

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  calc
    m = (m + 5) - 5 := by ring
    _ ≤ n - 5 := by rel [h2]
    _ ≤ 8 - 5 := by rel [h1]
    _ = 3 := by ring

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have : p ≥ 7 := by addarith [hp]
  constructor
  · calc
      p^2 ≥ 7^2 := by rel [this]
        _ = 49 := by ring
  · apply this

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have : a ≥ 6 := by addarith [h]
  constructor
  · show a ≥ 6
    apply this
  · show 3 * a ≥ 10
    calc
      3 * a ≥ 3 * 6 := by rel [this]
          _ ≥ 10 := by numbers

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have :=
    calc
      y = (x + 2*y) - (x + y) := by ring
      _ = 2 := by rw [h1, h2]; ring
  constructor
  · show x = 3
    addarith [h1, this]
  · show y = 2
    apply this

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  have hab : a = b := by rw [h1] at h2; apply h2
  have :=
    calc
      a * (a*b - 1)
      _ = a * (a * b) - a := by ring
      _ = a*b - a := by rw [h2, h2]
      _ = 0 := by addarith [h1]
  obtain (h3 : a = 0) | (h3 : a*b - 1 = 0) := eq_zero_or_eq_zero_of_mul_eq_zero this

  · have : b = 0 := by rw [hab] at h3; apply h3
    left
    show a = 0 ∧ b = 0
    constructor; apply h3; apply this

  · have : a*b = 1 := by addarith [h3]
    have ha : a = 1 := by rw [h1] at this; apply this
    have hb : b = 1 := by rw [hab] at ha; apply ha
    right
    show a = 1 ∧ b = 1
    constructor; apply ha; apply hb
