/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init

namespace Euclid
open Int

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  `gcd a b` recurses on `gcd b (fmod a b)`, and what gets smaller is the second argument,
so `termination_by b` is the whole measure.  Lean still has to know that `fmod a b` is squeezed
between `0` and `b`, and the four lemmas below say exactly that.  The `@[decreasing]` attribute
puts them where the termination checker will find them, which is why `gcd` needs no
`decreasing_by` block at all, unlike every definition in Section 6.6.

Tagging a lemma so that a tactic finds it by itself, rather than being handed it, is a habit worth
noticing.  It is how `rel` and `extra` already work. -/

@[decreasing] theorem lower_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : -b < fmod a b := by
  have H : 0 ≤ fmod a b := by
    apply fmod_nonneg_of_pos
    apply h1
  calc -b < 0 := by addarith [h1]
    _ ≤ _ := H

@[decreasing] theorem lower_bound_fmod2 (a b : ℤ) (h1 : b < 0) : b < fmod a (-b) := by
  have H : 0 ≤ fmod a (-b) := by
    apply fmod_nonneg_of_pos
    addarith [h1]
  have h2 : 0 < -b := by addarith [h1]
  calc b < 0 := h1
    _ ≤ fmod a (-b) := H

@[decreasing] theorem upper_bound_fmod2 (a b : ℤ) (h1 : b < 0) : fmod a (-b) < -b := by
  apply fmod_lt_of_pos
  addarith [h1]

@[decreasing] theorem upper_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : fmod a b < b := by
  apply fmod_lt_of_pos
  apply h1

def gcd (a b : ℤ) : ℤ :=
  if 0 < b then
    gcd b (fmod a b)
  else if b < 0 then
    gcd b (fmod a (-b))
  else if 0 ≤ a then
    a
  else
    -a
termination_by b


#eval gcd (-21) 15 -- infoview displays `3`


-- Book.
theorem gcd_nonneg (a b : ℤ) : 0 ≤ gcd a b := by
  rw [gcd]
  split_ifs with h1 h2 ha <;> try push_neg at *
  · -- case `0 < b`
    have IH := gcd_nonneg b (fmod a b) -- inductive hypothesis
    apply IH
  · -- case `b < 0`
    have IH := gcd_nonneg b (fmod a (-b)) -- inductive hypothesis
    apply IH
  · -- case `b = 0`, `0 ≤ a`
    apply ha
  · -- case `b = 0`, `a < 0`
    addarith [ha]
termination_by b


/- Note.  Watch what the second half of the first case below needs.  To show `gcd a b ∣ a` it uses
`IH_left` *and* `IH_right`, both halves of the inductive hypothesis.  Proving the two statements
together is what makes both available, so the conjunction is not an accident of presentation.

The `mutual` block after it proves the same two facts as two separate theorems, and each one calls
the other: `gcd_dvd_right` finishes its first case with `apply gcd_dvd_left`.  That is what
`mutual … end` is for, two definitions or theorems that recurse into each other, and it is why the
split is possible at all.  Having them separate means a later proof can cite the half it wants
instead of taking the conjunction apart. -/

theorem gcd_dvd (a b : ℤ) : gcd a b ∣ b ∧ gcd a b ∣ a := by
  rw [gcd]
  split_ifs with h1 h2 <;> try push_neg at *
  · -- case `0 < b`
    have IH : _ ∧ _ := gcd_dvd b (fmod a b) -- inductive hypothesis
    obtain ⟨IH_right : gcd b (fmod a b) ∣ fmod a b, IH_left : gcd b (fmod a b) ∣ b⟩ := IH
    constructor
    · -- prove that `gcd a b ∣ b`
      apply IH_left
    · -- prove that `gcd a b ∣ a`
      obtain ⟨k, hk : b = gcd b (fmod a b) * k⟩ := IH_left
      obtain ⟨l, hl : fmod a b = gcd b (fmod a b) * l⟩ := IH_right
      have H : fmod a b + b * fdiv a b = a := fmod_add_mul_fdiv a b
      set q := fdiv a b
      set r := fmod a b
      use l + k * q
      calc a = r + b * q := by rw [H]
        _ = gcd b r * l + (gcd b r * k) * q := by rw [← hk, ← hl]
        _ = gcd b r * (l + k * q) := by ring
  · -- case `b < 0`
    have IH : _ ∧ _ := gcd_dvd b (fmod a (-b)) -- inductive hypothesis
    obtain ⟨IH_right : gcd b (fmod a (-b)) ∣ fmod a (-b),
      IH_left : gcd b (fmod a (-b)) ∣ b⟩ := IH
    constructor
    · -- prove that `gcd a b ∣ b`
      apply IH_left
    · -- prove that `gcd a b ∣ a`
      obtain ⟨k, hk : b = gcd b (fmod a (-b)) * k⟩ := IH_left
      obtain ⟨l, hl : fmod a (-b) = gcd b (fmod a (-b)) * l⟩ := IH_right
      have H : fmod a (-b) + (-b) * fdiv a (-b) = a := fmod_add_mul_fdiv a (-b)
      set q := fdiv a (-b)
      set r := fmod a (-b)
      use l - k * q
      calc a = r + (-b) * q := by rw [H]
        _ = gcd b r * l + (- (gcd b r * k)) * q := by rw [← hk, ← hl]
        _ = gcd b r * (l - k * q) := by ring
  · -- case `b = 0`, `0 ≤ a`
    have hb : b = 0 := le_antisymm h1 h2
    constructor
    · -- prove that `gcd a b ∣ b`
      use 0
      calc b = 0 := hb
        _ = a * 0 := by ring
    · -- prove that `gcd a b ∣ a`
      use 1
      ring
  · -- case `b = 0`, `a < 0`
    have hb : b = 0 := le_antisymm h1 h2
    constructor
    · -- prove that `gcd a b ∣ b`
      use 0
      calc b = 0 := hb
        _ = -a * 0 := by ring
    · -- prove that `gcd a b ∣ a`
      use -1
      ring
termination_by b


/- Note.  `set q := fdiv a b` gives a long term a short name and replaces it everywhere it occurs,
in the hypotheses as well as the goal.  Nothing is proved by it.  It is there because the `calc`
chains below are about the shape of the identity `a = r + b * q`, and that shape is invisible when
`r` and `q` are written out in full. -/

-- Book.
mutual
theorem gcd_dvd_right (a b : ℤ) : gcd a b ∣ b := by
  rw [gcd]
  split_ifs with h1 h2 <;> try push_neg at *
  · -- case `0 < b`
    apply gcd_dvd_left b (fmod a b) -- inductive hypothesis
  · -- case `b < 0`
    apply gcd_dvd_left b (fmod a (-b)) -- inductive hypothesis
  · -- case `b = 0`, `0 ≤ a`
    have hb : b = 0 := le_antisymm h1 h2
    use 0
    calc b = 0 := hb
      _ = a * 0 := by ring
  · -- case `b = 0`, `a < 0`
    have hb : b = 0 := le_antisymm h1 h2
    use 0
    calc b = 0 := hb
      _ = -a * 0 := by ring
termination_by b

theorem gcd_dvd_left (a b : ℤ) : gcd a b ∣ a := by
  rw [gcd]
  split_ifs with h1 h2 <;> try push_neg at *
  · -- case `0 < b`
    have IH1 := gcd_dvd_left b (fmod a b) -- inductive hypothesis
    have IH2 := gcd_dvd_right b (fmod a b) -- inductive hypothesis
    obtain ⟨k, hk⟩ := IH1
    obtain ⟨l, hl⟩ := IH2
    have H : fmod a b + b * fdiv a b = a := fmod_add_mul_fdiv a b
    set q := fdiv a b
    set r := fmod a b
    use l + k * q
    calc a = r + b * q := by rw [H]
      _ = gcd b r * l + (gcd b r * k) * q := by rw [← hk, ← hl]
      _ = gcd b r * (l + k * q) := by ring
  · -- case `b < 0`
    have IH1 := gcd_dvd_left b (fmod a (-b)) -- inductive hypothesis
    have IH2 := gcd_dvd_right b (fmod a (-b)) -- inductive hypothesis
    obtain ⟨k, hk⟩ := IH1
    obtain ⟨l, hl⟩ := IH2
    have H := fmod_add_mul_fdiv a (-b)
    set q := fdiv a (-b)
    set r := fmod a (-b)
    use l - k * q
    calc a = r + (-b) * q := by rw [H]
      _ = gcd b r * l + (- (gcd b r * k)) * q := by rw [← hk, ← hl]
      _ = gcd b r * (l - k * q) := by ring
  · -- case `b = 0`, `0 ≤ a`
    use 1
    ring
  · -- case `b = 0`, `a < 0`
    use -1
    ring
termination_by b

end


mutual

def L (a b : ℤ) : ℤ :=
  if 0 < b then
    R b (fmod a b)
  else if b < 0 then
    R b (fmod a (-b))
  else if 0 ≤ a then
    1
  else
    -1
termination_by b

def R (a b : ℤ) : ℤ :=
  if 0 < b then
    L b (fmod a b) - (fdiv a b) * R b (fmod a b)
  else if b < 0 then
    L b (fmod a (-b)) + (fdiv a (-b)) * R b (fmod a (-b))
  else
    0
termination_by b

end


#eval L (-21) 15 -- infoview displays `2`
#eval R (-21) 15 -- infoview displays `3`


-- Book.
theorem L_mul_add_R_mul (a b : ℤ) : L a b * a + R a b * b = gcd a b := by
  rw [R, L, gcd]
  split_ifs with h1 h2 <;> try push_neg at *
  · -- case `0 < b`
    have IH := L_mul_add_R_mul b (fmod a b) -- inductive hypothesis
    have H : fmod a b + b * fdiv a b = a := fmod_add_mul_fdiv a b
    set q := fdiv a b
    set r := fmod a b
    calc R b r * a + (L b r - q * R b r) * b
        = R b r * (r + b * q) + (L b r - q * R b r) * b:= by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := IH
  · -- case `b < 0`
    have IH := L_mul_add_R_mul b (fmod a (-b)) -- inductive hypothesis
    have H : fmod a (-b) + (-b) * fdiv a (-b) = a := fmod_add_mul_fdiv a (-b)
    set q := fdiv a (-b)
    set r := fmod a (-b)
    calc  R b r * a + (L b r + q * R b r) * b
        =  R b r * (r + -b * q) + (L b r + q * R b r) * b := by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := IH
  · -- case `b = 0`, `0 ≤ a`
    ring
  · -- case `b = 0`, `a < 0`
    ring
termination_by b


#eval L 7 5 -- infoview displays `-2`
#eval R 7 5 -- infoview displays `3`
#eval gcd 7 5 -- infoview displays `1`


-- Book.
theorem bezout (a b : ℤ) : ∃ x y : ℤ, x * a + y * b = gcd a b := by
  use L a b, R a b
  apply L_mul_add_R_mul

/-! # Exercises -/


/- Note.  This one looks as though it needs an induction of its own, and it does not.  `bezout`
says `gcd a b` is an integer combination of `a` and `b`, and anything dividing `a` and `b` divides
every such combination.  So the proof is one `calc`, and the only thing to spot is that the work
has already been done.  Reading the theorems above before starting is part of the method. -/

theorem gcd_maximal {d a b : ℤ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ gcd a b := by
  obtain ⟨x, hx : a = d * x⟩ := ha
  obtain ⟨y, hy : b = d * y⟩ := hb
  use L a b * x + R a b * y
  calc gcd a b = L a b * a + R a b * b := by rw [L_mul_add_R_mul]
    _ = L a b * (d * x) + R a b * (d * y) := by rw [hx, hy]
    _ = d * (L a b * x + R a b * y) := by ring
