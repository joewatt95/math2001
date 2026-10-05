/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init

open Nat

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  `pascal` recurses on two arguments at once, and neither of them gets smaller on its own:
`pascal (a + 1) (b + 1)` calls `pascal (a + 1) b`, where the first argument has not moved.  What
does get smaller is the sum, which is what `termination_by a b => a + b` records.  Every proof by
the same recursion has to repeat that measure, which is why `pascal_le`, `pascal_eq` and
`pascal_symm` all end with a `termination_by` line of their own. -/

def pascal : ℕ → ℕ → ℕ
  | a, 0 => 1
  | 0, b + 1 => 1
  | a + 1, b + 1 => pascal (a + 1) b + pascal a (b + 1)
termination_by a b => a + b


#eval pascal 2 4 -- infoview displays `15`


-- Book.
theorem pascal_le (a b : ℕ) : pascal a b ≤ (a + b)! := by
  match a, b with
  | a, 0 =>
      calc pascal a 0 = 1 := by rw [pascal]
        _ ≤ (a + 0)! := by apply factorial_pos
  | 0, b + 1 =>
      calc pascal 0 (b + 1) = 1 := by rw [pascal]
        _ ≤ (0 + (b + 1))! := by apply factorial_pos
  | a + 1, b + 1 =>
      have IH1 := pascal_le (a + 1) b -- inductive hypothesis
      have IH2 := pascal_le a (b + 1) -- inductive hypothesis
      calc pascal (a + 1) (b + 1) = pascal (a + 1) b + pascal a (b + 1) := by rw [pascal]
        _ ≤ (a + 1 + b) ! + (a + (b + 1)) ! := by rel [IH1, IH2]
        _ ≤ (a + b) * (a + b + 1) ! + (a + 1 + b) ! + (a + (b + 1)) !  := by extra
        _ = ((a + b + 1) + 1) * (a + b + 1)! := by ring
        _ = ((a + b + 1) + 1)! := by rw [factorial, factorial, factorial]
        _ = (a + 1 + (b + 1))! := by ring
termination_by a + b


-- Book.
theorem pascal_eq (a b : ℕ) : pascal a b * a ! * b ! = (a + b)! := by
  match a, b with
  | a, 0 =>
    calc pascal _ 0 * a ! * 0! = 1 * a ! * 0! := by rw [pascal]
      _ = 1 * a ! * 1 := by rw [factorial]
      _ = (a + 0)! := by ring
  | 0, b + 1 =>
    calc pascal 0 (b + 1) * 0 ! * (b + 1)! = 1 * 0 ! * (b + 1)! := by rw [pascal]
      _ = 1 * 1 * (b + 1)! := by rw [factorial, factorial]
      _ = (0 + (b + 1))! := by ring
  | a + 1, b + 1 =>
    have IH1 := pascal_eq (a + 1) b -- inductive hypothesis
    have IH2 := pascal_eq a (b + 1) -- inductive hypothesis
    calc
      pascal (a + 1) (b + 1) * (a + 1)! * (b + 1)!
        = (pascal (a + 1) b + pascal a (b + 1)) * (a + 1)! * (b + 1)! := by rw [pascal]
      _ = pascal (a + 1) b * (a + 1)! * (b + 1)!
          + pascal a (b + 1) * (a + 1)! * (b + 1)! := by ring
      _ = pascal (a + 1) b * (a + 1)! * ((b + 1) * b !)
          + pascal a (b + 1) * ((a + 1) * a !) * (b + 1)! := by rw [factorial, factorial]
      _ = (b + 1) * (pascal (a + 1) b * (a + 1)! * b !)
          + (a + 1) * (pascal a (b + 1) * a ! * (b + 1)!) := by ring
      _ = (b + 1) * ((a + 1) + b) !
          + (a + 1) * (a + (b + 1)) ! := by rw [IH1, IH2]
      _ = ((1 + a + b) + 1) * (1 + a + b) ! := by ring
      _ = ((1 + a + b) + 1) ! := by rw [factorial]
      _ = ((a + 1) + (b + 1)) ! := by ring
termination_by a + b


-- Book.
example (a b : ℕ) : (pascal a b : ℚ) = (a + b)! / (a ! * b !) := by
  have ha := factorial_pos a
  have hb := factorial_pos b
  field_simp [ha, hb]
  norm_cast
  -- `field_simp` and `norm_cast` leave the goal in exactly this form, so the
  -- reassociation step the proof used to open with is no longer needed.
  apply pascal_eq

/-! # Exercises -/


/- Note.  The definition has three clauses but the proof below needs four cases, and the extra
one is not padding.  `pascal m n = pascal n m` at `(a + 1, 0)` reads `pascal (a + 1) 0 =
pascal 0 (a + 1)`, where the two sides are covered by *different* clauses, the first and the
second.  Matching on `a, 0` in one go would leave `pascal 0 a` with `a` of no particular shape and
nothing to unfold it with, so `(0, 0)` is separated out. -/

theorem pascal_symm (m n : ℕ) : pascal m n = pascal n m := by
  match m, n with
  | 0, 0 => rfl
  | a + 1, 0 =>
      calc pascal (a + 1) 0 = 1 := by rw [pascal]
        _ = pascal 0 (a + 1) := by rw [pascal]
  | 0, b + 1 =>
      calc pascal 0 (b + 1) = 1 := by rw [pascal]
        _ = pascal (b + 1) 0 := by rw [pascal]
  | a + 1, b + 1 =>
      have IH1 := pascal_symm (a + 1) b -- inductive hypothesis
      have IH2 := pascal_symm a (b + 1) -- inductive hypothesis
      calc pascal (a + 1) (b + 1) = pascal (a + 1) b + pascal a (b + 1) := by rw [pascal]
        _ = pascal b (a + 1) + pascal (b + 1) a := by rw [IH1, IH2]
        _ = pascal (b + 1) a + pascal b (a + 1) := by ring
        _ = pascal (b + 1) (a + 1) := by rw [pascal]
termination_by m + n


/- Note.  The first step below unfolds twice in one `rw`, and writing the intermediate form out
as its own step does not work.  As with `factorial` in Section 6.2, `rw [pascal]` uses the first
clause that matches anywhere in the goal, and `pascal (a + 1) 0 = 1` would match the
`pascal (k + 1) 0` you had just written on the right rather than the term on the left. -/

example (a : ℕ) : pascal a 1 = a + 1 := by
  simple_induction a with k IH
  · calc pascal 0 1 = 1 := by rw [pascal]
      _ = 0 + 1 := by numbers
  · calc pascal (k + 1) 1 = 1 + pascal k 1 := by rw [pascal, pascal]
      _ = 1 + (k + 1) := by rw [IH]
      _ = k + 1 + 1 := by ring
