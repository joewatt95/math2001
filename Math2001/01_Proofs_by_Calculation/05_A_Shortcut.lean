/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/-! # Section 1.5: A shortcut -/

-- Book.
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by addarith [h1]

-- Book.
example {a b : ℤ} (ha : a - 2 * b = 1) : a = 2 * b + 1 := by addarith [ha]

example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 := by addarith [hx, hy]

-- Book.
example {s t : ℝ} (h : t = 4 - s * t) : t + s * t > 0 := by addarith [h]

-- Book.
example {m n : ℝ} (h1 : m ≤ 8 - n) : 10 > m + n := by addarith [h1]


-- Check that `addarith` can't verify this deduction!
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
  have : 3 * w = 3 * 1 := by addarith [h1]
  cancel 3 at this
