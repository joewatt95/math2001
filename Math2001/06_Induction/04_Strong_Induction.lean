/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init

open Nat

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  There is no `strong_induction` tactic, and there does not need to be.  A theorem may be
quoted at a smaller argument inside its own proof, which is what `have IH1 := F_bound k` below
does: it is the statement being proved, applied to `k`.  That is all induction ever was, and the
tactics of the earlier sections were packaging it.

Writing it this way means you may reach back as far as you like rather than one or two steps, and
you may reach back by an amount that depends on the case you are in.  `exists_prime_factor` uses
a factor `m` of `n` whose size it does not control, and `extract_pow_two` halves.  That freedom is
what "strong" refers to.

The price is that Lean has to see the argument get smaller, and it works that out from what is in
the context.  In `extract_pow_two` the call is on `m` with `n = 2 * m` and `0 < m` to hand, which
is enough.  Where it is not, state the decrease as a `have` and it will be found. -/

def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

/- Note.  The cases are laid out with `match` rather than with bullets, so that they line up one
for one with the clauses of the definition of `F`.  Reading the two side by side is the point: the
proof has a case wherever the definition has one. -/

-- Book.
theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  match n with
  | 0 =>
      calc F 0 = 1 := by rw [F]
        _ ≤ 2 ^ 0 := by numbers
  | 1 =>
      calc F 1 = 1 := by rw [F]
        _ ≤ 2 ^ 1 := by numbers
  | k + 2  =>
      have IH1 := F_bound k -- first inductive hypothesis
      have IH2 := F_bound (k + 1) -- second inductive hypothesis
      calc F (k + 2) = F (k + 1) + F k := by rw [F]
        _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
        _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
        _ = 2 ^ (k + 2) := by ring


namespace Nat

-- Book.
theorem exists_prime_factor {n : ℕ} (hn2 : 2 ≤ n) : ∃ p : ℕ, Prime p ∧ p ∣ n := by
  by_cases hn : Prime n
  . -- case 1: `n` is prime
    use n
    constructor
    · apply hn
    · use 1
      ring
  . -- case 2: `n` is not prime
    obtain ⟨m, hmn, _, ⟨x, hx⟩⟩ := exists_factor_of_not_prime hn hn2
    have IH : ∃ p, Prime p ∧ p ∣ m := exists_prime_factor hmn -- inductive hypothesis
    obtain ⟨p, hp, y, hy⟩ := IH
    use p
    constructor
    · apply hp
    · use x * y
      calc n = m * x := hx
        _ = (p * y) * x := by rw [hy]
        _ = p * (x * y) := by ring

/-! # Exercises -/


theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain (hn' : Nat.Even n) | (hn' : Nat.Odd n) := Nat.even_or_odd_lib n
  · -- case 1: `n` is even, so strip off one factor of 2 and recurse on the half
    obtain ⟨m, hm : n = 2 * m⟩ := hn'
    have hm1 : 0 < m := by
      rw [hm] at hn
      cancel 2 at hn
    obtain ⟨a, x, hx : Nat.Odd x, hmx : m = 2 ^ a * x⟩ := extract_pow_two m hm1
    use a + 1, x
    constructor
    · apply hx
    · calc n = 2 * m := hm
        _ = 2 * (2 ^ a * x) := by rw [hmx]
        _ = 2 ^ (a + 1) * x := by ring
  · -- case 2: `n` is odd, so it is already `2 ^ 0` times an odd number
    use 0, n
    constructor
    · apply hn'
    · ring
