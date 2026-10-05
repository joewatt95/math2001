/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  The new move in this section is that the name of a recursive definition is also a
rewrite rule.  `b` is defined by two clauses, and `rw [b]` replaces `b (k + 1)` by `b k ^ 2 - 2`,
which is the whole point: it is what makes `b k` appear, and only then is there something for the
inductive hypothesis to act on.

So every proof below has the same three beats as the ones in Section 6.1.  `rw [defn]`
unfolds one step, `rw [IH]` or `rel [IH]` uses the inductive hypothesis on what that exposed, and
`ring` or `numbers` tidies up.  The base case is the same with `0` in place of `k + 1`. -/

def a (n : ℕ) : ℕ := 2 ^ n


#eval a 20 -- infoview displays `1048576`


def b : ℕ → ℤ
  | 0 => 3
  | n + 1 => b n ^ 2 - 2


#eval b 7 -- infoview displays `316837008400094222150776738483768236006420971486980607`


-- Book.
example (n : ℕ) : Odd (b n) := by
  simple_induction n with k hk
  · -- base case
    use 1
    calc b 0 = 3 := by rw [b]
      _ = 2 * 1 + 1 := by numbers
  · -- inductive step
    obtain ⟨x, hx⟩ := hk
    use 2 * x ^ 2 + 2 * x - 1
    calc b (k + 1) = b k ^ 2 - 2 := by rw [b]
      _ = (2 * x + 1) ^ 2 - 2 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 2 * x - 1) + 1 := by ring


def x : ℕ → ℤ
  | 0 => 5
  | n + 1 => 2 * x n - 1


example (n : ℕ) : x n ≡ 1 [ZMOD 4] := by
  simple_induction n with k IH
  · -- base case
    calc x 0 = 5 := by rw [x]
      _ = 4 * 1 + 1 := by numbers
      _ ≡ 1 [ZMOD 4] := by extra
  · -- inductive step
    calc x (k + 1) = 2 * x k - 1 := by rw [x]
      _ ≡ 2 * 1 - 1 [ZMOD 4] := by rel [IH]
      _ = 1 := by numbers

-- Book.
example (n : ℕ) : x n = 2 ^ (n + 2) + 1 := by
  simple_induction n with k IH
  · -- base case
    calc x 0 = 5 := by rw [x]
      _ = 2 ^ (0 + 2) + 1 := by numbers
  · -- inductive step
    calc x (k + 1) = 2 * x k - 1 := by rw [x]
      _ = 2 * (2 ^ (k + 2) + 1) - 1 := by rw [IH]
      _ = 2 ^ ((k + 1) + 2) + 1 := by ring


def A : ℕ → ℚ
  | 0 => 0
  | n + 1 => A n + (n + 1)


-- Book.
example (n : ℕ) : A n = n * (n + 1) / 2 := by
  simple_induction n with k IH
  · -- base case
    calc A 0 = 0 := by rw [A]
      _ = 0 * (0 + 1) / 2 := by numbers
  · -- inductive step
    calc
      A (k + 1) = A k + (k + 1) := by rw [A]
      _ = k * (k + 1) / 2 + (k + 1) := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) / 2 := by ring



def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n


/- Note.  Two things in the proof below are worth slowing down for.

The base case is `∀ d, 1 ≤ d → d ≤ 0 → d ∣ 0 !`, and after `intro` the hypotheses say `1 ≤ k`
and `k ≤ 0`.  No natural number satisfies both, so `interval_cases k` enumerates an empty range
and the goal is finished without a single case being written.  A case split with nothing in it is
a perfectly good proof.

`n !` is postfix notation declared at a very high precedence, and the parser will happily read on
past the end of a line looking for what comes after it.  `use k !` followed by a line beginning
`rw` is read as `k` applied to `!rw [factorial]`, with a confusing error about `k` not being a
function.  Bracketing it, `use (k !)`, settles the matter. -/

example (n : ℕ) : ∀ d, 1 ≤ d → d ≤ n → d ∣ n ! := by
  simple_induction n with k IH
  · -- base case
    intro k hk1 hk
    interval_cases k
  · -- inductive step
    intro d hk1 hk
    obtain hk | hk : d = k + 1 ∨ d < k + 1 := eq_or_lt_of_le hk
    · -- case 1: `d = k + 1`
      rw [hk]
      use (k !)
      rw [factorial]
    · -- case 2: `d < k + 1`
      have hdk : d ≤ k := by addarith [hk]
      obtain ⟨c, hc : k ! = d * c⟩ := IH d hk1 hdk
      use (k + 1) * c
      calc (k + 1)! = (k + 1) * k ! := by rw [factorial]
        _ = (k + 1) * (d * c) := by rw [hc]
        _ = d * ((k + 1) * c) := by ring

/- Note.  `rw [factorial]` tries the definition's clauses in order and uses the first one that
matches anywhere in the goal, which is not always the one you meant.  Writing the base case as

    calc (0 + 1)! = (0 + 1) * 0 ! := by rw [factorial]

fails, because the `0 !` you just wrote on the right matches the clause `factorial 0 = 1`, and
that fires instead of the one unfolding `(0 + 1)!` on the left.  Unfolding all the way down to a
numeral in one step avoids the problem. -/

example (n : ℕ) : (n + 1)! ≥ 2 ^ n := by
  simple_induction n with k IH
  · -- base case
    calc (0 + 1)! = 1 := by rw [factorial, factorial]
      _ ≥ 2 ^ 0 := by numbers
  · -- inductive step
    have h1 : 2 ≤ k + 1 + 1 := by extra
    calc (k + 1 + 1)! = (k + 1 + 1) * (k + 1)! := by rw [factorial]
      _ ≥ 2 * (k + 1)! := by rel [h1]
      _ ≥ 2 * 2 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) := by ring


/-! # Exercises -/


def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

/- Note.  `c` takes values in `ℤ`, so `3 * p - 4` below is a legitimate witness even though it is
negative for small `p`.  Over `ℕ` the same calculation would have to be rearranged to avoid the
subtraction, as in Section 6.1. -/

example (n : ℕ) : Odd (c n) := by
  simple_induction n with k IH
  · -- base case
    use 3
    calc c 0 = 7 := by rw [c]
      _ = 2 * 3 + 1 := by numbers
  · -- inductive step
    obtain ⟨p, hp : c k = 2 * p + 1⟩ := IH
    use 3 * p - 4
    calc c (k + 1) = 3 * c k - 10 := by rw [c]
      _ = 3 * (2 * p + 1) - 10 := by rw [hp]
      _ = 2 * (3 * p - 4) + 1 := by ring

example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k IH
  · -- base case
    calc c 0 = 7 := by rw [c]
      _ = 2 * 3 ^ 0 + 5 := by numbers
  · -- inductive step
    calc c (k + 1) = 3 * c k - 10 := by rw [c]
      _ = 3 * (2 * 3 ^ k + 5) - 10 := by rw [IH]
      _ = 2 * 3 ^ (k + 1) + 5 := by ring

def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with k IH
  · -- base case
    calc y 0 = 2 := by rw [y]
      _ = 2 ^ 2 ^ 0 := by numbers
  · -- inductive step
    calc y (k + 1) = y k ^ 2 := by rw [y]
      _ = (2 ^ 2 ^ k) ^ 2 := by rw [IH]
      _ = 2 ^ 2 ^ (k + 1) := by ring

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  · -- base case
    calc B 0 = 0 := by rw [B]
      _ = 0 * (0 + 1) * (2 * 0 + 1) / 6 := by numbers
  · -- inductive step
    calc B (k + 1) = B k + (k + 1 : ℚ) ^ 2 := by rw [B]
      _ = k * (k + 1) * (2 * k + 1) / 6 + (k + 1) ^ 2 := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) / 6 := by ring

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

example (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  · -- base case
    calc S 0 = 1 := by rw [S]
      _ = 2 - 1 / 2 ^ 0 := by numbers
  · -- inductive step
    calc S (k + 1) = S k + 1 / 2 ^ (k + 1) := by rw [S]
      _ = 2 - 1 / 2 ^ k + 1 / 2 ^ (k + 1) := by rw [IH]
      _ = 2 - 1 / 2 ^ (k + 1) := by ring

example (n : ℕ) : 0 < n ! := by
  simple_induction n with k IH
  · -- base case
    calc 0 ! = 1 := by rw [factorial]
      _ > 0 := by numbers
  · -- inductive step
    have h1 : 1 ≤ k ! := by addarith [IH]
    calc (k + 1)! = (k + 1) * k ! := by rw [factorial]
      _ ≥ (k + 1) * 1 := by rel [h1]
      _ = k + 1 := by ring
      _ > 0 := by extra

example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    use 1
    calc 2 ! = 2 := by rw [factorial, factorial, factorial]
      _ = 2 * 1 := by numbers
  · -- inductive step
    obtain ⟨p, hp : k ! = 2 * p⟩ := IH
    use (k + 1) * p
    calc (k + 1)! = (k + 1) * k ! := by rw [factorial]
      _ = (k + 1) * (2 * p) := by rw [hp]
      _ = 2 * ((k + 1) * p) := by ring

example (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with k IH
  · -- base case
    calc (0 + 1)! = 1 := by rw [factorial, factorial]
      _ ≤ (0 + 1) ^ 0 := by numbers
  · -- inductive step
    have h1 : k + 1 ≤ k + 1 + 1 := by extra
    calc (k + 1 + 1)! = (k + 1 + 1) * (k + 1)! := by rw [factorial]
      _ ≤ (k + 1 + 1) * (k + 1) ^ k := by rel [IH]
      _ ≤ (k + 1 + 1) * (k + 1 + 1) ^ k := by rel [h1]
      _ = (k + 1 + 1) ^ (k + 1) := by ring
