/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  Everything here is the recursion of Section 6.4 again, now over `ℤ`, and every
proof has the same three parts.

`rw [fmod]` unfolds the definition, which is a nest of `if`s, so the goal arrives with the `if`s
still in it.  `split_ifs with h1 h2 h3` then makes one goal per branch and names the conditions,
and `push_neg at *` puts the negated ones into usable shape, turning `¬ (n * d < 0)` into
`0 ≤ n * d`.  After that the cases match the definition's branches one for one, and the two
recursive branches each get their inductive hypothesis by quoting the theorem at the smaller
argument.

The `termination_by` and `decreasing_by` blocks are copied from the definition, with the case
names changed where the theorem has already taken them.  A proof that recurses the same way owes
the same termination argument, and that argument does not depend on what is being proved, so there
is nothing in them to work out. -/

def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by 2 * n - d
decreasing_by
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_neg_iff.mp ‹n * d < 0› with ⟨hn, hd⟩ | ⟨hn, hd⟩
    · left; constructor <;> omega
    · right; constructor <;> omega
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_pos_iff.mp ‹(0 : ℤ) < d * (n - d)› with ⟨hd, hn⟩ | ⟨hd, hn⟩
    · left; constructor <;> omega
    · right; constructor <;> omega

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by 2 * n - d
decreasing_by
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_neg_iff.mp ‹n * d < 0› with ⟨hn, hd⟩ | ⟨hn, hd⟩
    · left; constructor <;> omega
    · right; constructor <;> omega
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_pos_iff.mp ‹(0 : ℤ) < d * (n - d)› with ⟨hd, hn⟩ | ⟨hd, hn⟩
    · left; constructor <;> omega
    · right; constructor <;> omega


#eval fmod 11 4 -- infoview displays `3`
#eval fdiv 11 4 -- infoview displays `2`


-- Book.
theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> try push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by 2 * n - d
decreasing_by
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_neg_iff.mp ‹n * d < 0› with ⟨hn, hd'⟩ | ⟨hn, hd'⟩
    · left; constructor <;> omega
    · right; constructor <;> omega
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_pos_iff.mp ‹(0 : ℤ) < d * (n - d)› with ⟨hd', hn⟩ | ⟨hd', hn⟩
    · left; constructor <;> omega
    · right; constructor <;> omega


-- Book.
theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> try push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by 2 * n - d
decreasing_by
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_neg_iff.mp ‹n * d < 0› with ⟨hn, hd'⟩ | ⟨hn, hd'⟩
    · left; constructor <;> omega
    · right; constructor <;> omega
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_pos_iff.mp ‹(0 : ℤ) < d * (n - d)› with ⟨hd', hn⟩ | ⟨hd', hn⟩
    · left; constructor <;> omega
    · right; constructor <;> omega


-- Book.
theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> try push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by 2 * n - d
decreasing_by
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_neg_iff.mp ‹n * d < 0› with ⟨hn, hd'⟩ | ⟨hn, hd'⟩
    · left; constructor <;> omega
    · right; constructor <;> omega
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_pos_iff.mp ‹(0 : ℤ) < d * (n - d)› with ⟨hd', hn⟩ | ⟨hd', hn⟩
    · left; constructor <;> omega
    · right; constructor <;> omega


-- Book.
example (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]

/-! # Exercises -/


/- Note.  This mirrors `fmod_lt_of_pos` line for line, and the one thing that changes is which
factor is positive: there it was `d`, here it is `-d`.  `cancel` divides an inequality by a factor
and has to know that factor is positive, so `have hd' : 0 < -d` goes in before the `cancel` rather
than being left for it to discover. -/

theorem lt_fmod_of_neg (n : ℤ) {d : ℤ} (hd : d < 0) : d < fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> try push_neg at *
  · -- case `n * d < 0`
    have IH := lt_fmod_of_neg (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := lt_fmod_of_neg (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have hd' : 0 < -d := by addarith [hd]
    have h4 :=
    calc 0 ≤ - (d * (n - d)) := by addarith [h2]
      _ = -d * (n - d) := by ring
    cancel -d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · intro (hdn : d = n)
      apply h3
      addarith [hdn]
termination_by 2 * n - d
decreasing_by
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_neg_iff.mp ‹n * d < 0› with ⟨hn, hd'⟩ | ⟨hn, hd'⟩
    · left; constructor <;> omega
    · right; constructor <;> omega
  · rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]
    rcases mul_pos_iff.mp ‹(0 : ℤ) < d * (n - d)› with ⟨hd', hn⟩ | ⟨hd', hn⟩
    · left; constructor <;> omega
    · right; constructor <;> omega

def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by 3 * n - 1
decreasing_by
  all_goals (simp_wf; rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]; omega)

theorem T_eq (n : ℤ) : T n = n ^ 2 := by
  rw [T]
  split_ifs with h1 h2 <;> try push_neg at *
  · -- case `0 < n`
    have IH := T_eq (1 - n) -- inductive hypothesis
    calc T (1 - n) + 2 * n - 1 = (1 - n) ^ 2 + 2 * n - 1 := by rw [IH]
      _ = n ^ 2 := by ring
  · -- case `0 < -n`
    have IH := T_eq (-n) -- inductive hypothesis
    calc T (-n) = (-n) ^ 2 := by rw [IH]
      _ = n ^ 2 := by ring
  · -- last case: `n ≤ 0` and `-n ≤ 0`, so `n = 0`
    have h3 : n = 0 := by addarith [h1, h2]
    rw [h3]
    numbers
termination_by 3 * n - 1
decreasing_by
  all_goals (simp_wf; rw [Int.sizeOf_lt_sizeOf_iff, abs_lt_abs_iff]; omega)

/- Note.  The argument is that `r - s` is a multiple of `b` strictly between `-b` and `b`, so the
multiple is `0`.  Two things in it are worth pointing at.

`a ≡ r [ZMOD b]` is by definition `∃ x, a - r = b * x`, so the `obtain` takes the conjunction and
that existential apart in one go, `⟨hr1, hr2, x, hx⟩`, and the witness `x` is available
immediately.

The finish uses the fact that `ℤ` has no room between integers.  The two `cancel`s leave
`y - x < 1` and `-1 < y - x`, and `addarith` closes `y - x = 0` from them.  Over `ℚ` or `ℝ` that
would be false, and there is nothing in the written proof to show where the difference lies, which
is worth remembering when a proof will not go through over `ℝ`. -/

theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
    (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]) : r = s := by
  obtain ⟨hr1 : 0 ≤ r, hr2 : r < b, x, hx : a - r = b * x⟩ := hr
  obtain ⟨hs1 : 0 ≤ s, hs2 : s < b, y, hy : a - s = b * y⟩ := hs
  have hrs : r - s = b * (y - x) :=
    calc r - s = (a - s) - (a - r) := by ring
      _ = b * y - b * x := by rw [hx, hy]
      _ = b * (y - x) := by ring
  have h1 : b * (y - x) < b * 1 :=
    calc b * (y - x) = r - s := by rw [hrs]
      _ < b := by addarith [hr2, hs1]
      _ = b * 1 := by ring
  cancel b at h1
  have h2 : b * (-1) < b * (y - x) :=
    calc b * (-1) = -b := by ring
      _ < r - s := by addarith [hs2, hr1]
      _ = b * (y - x) := by rw [hrs]
  cancel b at h2
  have h3 : y - x = 0 := by addarith [h1, h2]
  calc r = s + b * (y - x) := by addarith [hrs]
    _ = s + b * 0 := by rw [h3]
    _ = s := by ring

/- Note.  Nothing new is proved below.  Existence and uniqueness are already done, and the only
question is how to say so.  Stating the three facts about `fmod a b` once, as `H`, lets them serve
twice: as the witness half of the `∃!`, and as the second argument to `uniqueness`.  Writing them
inline would mean writing them out again. -/

example (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  have H : 0 ≤ fmod a b ∧ fmod a b < b ∧ a ≡ fmod a b [ZMOD b]
  · constructor
    · apply fmod_nonneg_of_pos a h
    constructor
    · apply fmod_lt_of_pos a h
    · use fdiv a b
      have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
      addarith [Hab]
  use fmod a b
  constructor
  · apply H
  · intro y (hy : 0 ≤ y ∧ y < b ∧ a ≡ y [ZMOD b])
    apply uniqueness a b h hy H
