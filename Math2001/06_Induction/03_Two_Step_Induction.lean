/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  `two_step_induction n with k IH1 IH2` leaves three goals: the statement at `0`, the
statement at `1`, and the statement at `k + 2` given both `IH1`, the statement at `k`, and `IH2`,
the statement at `k + 1`.  Two base cases, because a recurrence that reaches back two places needs
two values before it can get started.

Nothing says both inductive hypotheses have to be used.  The exercise on `c` below has the
recurrence `c (n + 2) = 4 * c n`, which skips a term, so its proof never mentions `IH2`. -/

def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n


#eval a 5 -- infoview displays `31`


-- Book.
example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  two_step_induction n with k IH1 IH2
  . calc a 0 = 2 := by rw [a]
      _ = 2 ^ 0 + (-1) ^ 0 := by numbers
  . calc a 1 = 1 := by rw [a]
      _ = 2 ^ 1 + (-1) ^ 1 := by numbers
  calc
    a (k + 2)
      = a (k + 1) + 2 * a k := by rw [a]
    _ = (2 ^ (k + 1) + (-1) ^ (k + 1)) + 2 * (2 ^ k + (-1) ^ k) := by rw [IH1, IH2]
    _ = (2 : ℤ) ^ (k + 2) + (-1) ^ (k + 2) := by ring


/- Note.  This is the most important idea in the section, and it is easy to miss because the
proof below spends most of its length on bookkeeping.

The statement `a m ≡ 1 ∨ a m ≡ 5` cannot be proved by induction as it stands.  Suppose you knew
only that each of `a k` and `a (k + 1)` is `1` or `5` mod `6`.  That is four combinations, and
some of them put `a (k + 2) = a (k + 1) + 2 * a k` outside `{1, 5}` altogether.  There is simply
not enough in the hypothesis to get the conclusion.

What is true is that the *pair* `(a n, a (n + 1))` is always `(1, 5)` or `(5, 1)`, never `(1, 1)`
or `(5, 5)`.  That is a stronger statement, so there is more to prove, but there is also more to
use, and it is the stronger one that carries itself forward.  Proving something harder because it
is easier to prove is the trick worth remembering.

Finding the right strengthening is a matter of computing the first several terms, writing down
the pairs, and watching for the cycle.  Two of the exercises below are this same shape, and in one
of them the cycle has length three rather than two. -/

-- Book.
example {m : ℕ} (hm : 1 ≤ m) : a m ≡ 1 [ZMOD 6] ∨ a m ≡ 5 [ZMOD 6] := by
  have H : ∀ n : ℕ, 1 ≤ n →
      (a n ≡ 1 [ZMOD 6] ∧ a (n + 1) ≡ 5 [ZMOD 6])
    ∨ (a n ≡ 5 [ZMOD 6] ∧ a (n + 1) ≡ 1 [ZMOD 6])
  · intro n hn
    induction_from_starting_point n, hn with k hk IH
    · left
      constructor
      calc a 1 = 1 := by rw [a]
        _ ≡ 1 [ZMOD 6] := by extra
      calc a (1 + 1) = 1 + 2 * 2 := by rw [a, a, a]
        _ = 5 := by numbers
        _ ≡ 5 [ZMOD 6] := by extra
    · obtain ⟨IH1, IH2⟩ | ⟨IH1, IH2⟩ := IH
      · right
        constructor
        · apply IH2
        calc a (k + 1 + 1) = a (k + 1) + 2 * a k := by rw [a]
          _ ≡ 5 + 2 * 1 [ZMOD 6] := by rel [IH1, IH2]
          _ = 6 * 1 + 1 := by numbers
          _ ≡ 1 [ZMOD 6] := by extra
      · left
        constructor
        · apply IH2
        calc a (k + 1 + 1) = a (k + 1) + 2 * a k := by rw [a]
          _ ≡ 1 + 2 * 5 [ZMOD 6] := by rel [IH1, IH2]
          _ = 6 * 1 + 5 := by numbers
          _ ≡ 5 [ZMOD 6] := by extra
  obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m hm
  · left
    apply H1
  · right
    apply H1


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n


-- Book.
example (n : ℕ) : F n ≤ 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · calc F 0 = 1 := by rw [F]
      _ ≤ 2 ^ 0 := by numbers
  · calc F 1 = 1 := by rw [F]
      _ ≤ 2 ^ 1 := by numbers
  · calc F (k + 2) = F (k + 1) + F k := by rw [F]
      _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
      _ = 2 ^ (k + 2) := by ring


-- Book.
example (n : ℕ) : F (n + 1) ^ 2 - F (n + 1) * F n - F n ^ 2 = - (-1) ^ n := by
  simple_induction n with k IH
  · calc F 1 ^ 2 - F 1 * F 0 - F 0 ^ 2 = 1 ^ 2 - 1 * 1 - 1 ^ 2 := by rw [F, F]
      _ = - (-1) ^ 0 := by numbers
  · calc F (k + 2) ^ 2 - F (k + 2) * F (k + 1) - F (k + 1) ^ 2
        = (F (k + 1) + F k) ^ 2 - (F (k + 1) + F k) * F (k + 1)
            - F (k + 1) ^ 2 := by rw [F]
      _ = - (F (k + 1) ^ 2 - F (k + 1) * F k - F k ^ 2) := by ring
      _ = - -(-1) ^ k := by rw [IH]
      _ = -(-1) ^ (k + 1) := by ring


def d : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | k + 2 => 3 * d (k + 1) + 5 * d k


#eval d 2 -- infoview displays `18`
#eval d 3 -- infoview displays `59`
#eval d 4 -- infoview displays `267`
#eval d 5 -- infoview displays `1096`
#eval d 6 -- infoview displays `4623`
#eval d 7 -- infoview displays `19349`


#eval 4 ^ 2 -- infoview displays `16`
#eval 4 ^ 3 -- infoview displays `64`
#eval 4 ^ 4 -- infoview displays `256`
#eval 4 ^ 5 -- infoview displays `1024`
#eval 4 ^ 6 -- infoview displays `4096`
#eval 4 ^ 7 -- infoview displays `16384`


/- Note.  The `#eval`s above are not decoration.  They are how you find the threshold: print the
sequence beside the bound and look for where one overtakes the other.  With a two-step induction
you then have to check *two* base cases, at `C` and at `C + 1`, and `by rfl` evaluates a
recursively defined term at a numeral in one go, where `rw [d]` would take four steps. -/

-- Book.
example : forall_sufficiently_large n : ℕ, d n ≥ 4 ^ n := by
  dsimp
  use 4
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · calc d 4 = 267 := by rfl
      _ ≥ 4 ^ 4 := by numbers
  · calc d 5 = 1096 := by rfl
      _ ≥ 4 ^ 5 := by numbers
  calc d (k + 2) = 3 * d (k + 1) + 5 * d k := by rw [d]
    _ ≥ 3 * 4 ^ (k + 1) + 5 * 4 ^ k := by rel [IH1, IH2]
    _ = 16 * 4 ^ k + 4 ^ k := by ring
    _ ≥ 16 * 4 ^ k := by extra
    _ = 4 ^ (k + 2) := by ring

/-! # Exercises -/


def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · calc b 0 = 0 := by rw [b]
      _ = 3 ^ 0 - 2 ^ 0 := by numbers
  · calc b 1 = 1 := by rw [b]
      _ = 3 ^ 1 - 2 ^ 1 := by numbers
  · calc b (k + 2) = 5 * b (k + 1) - 6 * b k := by rw [b]
      _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1)) - 6 * (3 ^ k - 2 ^ k) := by rw [IH1, IH2]
      _ = 3 ^ (k + 2) - 2 ^ (k + 2) := by ring

def c : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c n

example (n : ℕ) : c n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  · calc c 0 = 3 := by rw [c]
      _ = 2 * 2 ^ 0 + (-2) ^ 0 := by numbers
  · calc c 1 = 2 := by rw [c]
      _ = 2 * 2 ^ 1 + (-2) ^ 1 := by numbers
  · calc c (k + 2) = 4 * c k := by rw [c]
      _ = 4 * (2 * 2 ^ k + (-2) ^ k) := by rw [IH1]
      _ = 2 * 2 ^ (k + 2) + (-2) ^ (k + 2) := by ring

def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k IH1 IH2
  · calc t 0 = 5 := by rw [t]
      _ = 2 * 0 + 5 := by numbers
  · calc t 1 = 7 := by rw [t]
      _ = 2 * 1 + 5 := by numbers
  · calc t (k + 2) = 2 * t (k + 1) - t k := by rw [t]
      _ = 2 * (2 * (k + 1) + 5) - (2 * k + 5) := by rw [IH1, IH2]
      _ = 2 * (k + 2) + 5 := by ring

def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

example (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  · calc q 0 = 1 := by rw [q]
      _ = (0:ℤ) ^ 3 + 1 := by numbers
  · calc q 1 = 2 := by rw [q]
      _ = (1:ℤ) ^ 3 + 1 := by numbers
  · calc q (k + 2) = 2 * q (k + 1) - q k + 6 * k + 6 := by rw [q]
      _ = 2 * ((k + 1) ^ 3 + 1) - (k ^ 3 + 1) + 6 * k + 6 := by rw [IH1, IH2]
      _ = (k + 2) ^ 3 + 1 := by ring

def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

/- Note.  The next two are the strengthening trick again.  For `s` the pairs mod `5` run
`(2, 3), (3, 2), (2, 3), …`, so two cases suffice.  For `p` mod `7` they run
`(2, 3), (3, 2), (2, 2), (2, 3), …`, a cycle of length three, so the auxiliary statement needs
three disjuncts.  Compute a few terms before writing anything.

Both proofs are then ordinary `simple_induction`s on the paired statement, not two-step
inductions: carrying `(s n, s (n + 1))` along already remembers everything the recurrence needs. -/

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  have H : ∀ n : ℕ, (s n ≡ 2 [ZMOD 5] ∧ s (n + 1) ≡ 3 [ZMOD 5])
      ∨ (s n ≡ 3 [ZMOD 5] ∧ s (n + 1) ≡ 2 [ZMOD 5])
  · intro n
    simple_induction n with k IH
    · left
      constructor
      · calc s 0 = 2 := by rw [s]
          _ ≡ 2 [ZMOD 5] := by extra
      · calc s (0 + 1) = 3 := by rw [s]
          _ ≡ 3 [ZMOD 5] := by extra
    · obtain ⟨IH1 : s k ≡ 2 [ZMOD 5], IH2 : s (k + 1) ≡ 3 [ZMOD 5]⟩
        | ⟨IH1 : s k ≡ 3 [ZMOD 5], IH2 : s (k + 1) ≡ 2 [ZMOD 5]⟩ := IH
      · right
        constructor
        · apply IH2
        · calc s (k + 1 + 1) = 2 * s (k + 1) + 3 * s k := by rw [s]
            _ ≡ 2 * 3 + 3 * 2 [ZMOD 5] := by rel [IH1, IH2]
            _ = 5 * 2 + 2 := by numbers
            _ ≡ 2 [ZMOD 5] := by extra
      · left
        constructor
        · apply IH2
        · calc s (k + 1 + 1) = 2 * s (k + 1) + 3 * s k := by rw [s]
            _ ≡ 2 * 2 + 3 * 3 [ZMOD 5] := by rel [IH1, IH2]
            _ = 5 * 2 + 3 := by numbers
            _ ≡ 3 [ZMOD 5] := by extra
  obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m
  · left
    apply H1
  · right
    apply H1

def p : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 6 * p (n + 1) - p n

example (m : ℕ) : p m ≡ 2 [ZMOD 7] ∨ p m ≡ 3 [ZMOD 7] := by
  have H : ∀ n : ℕ, (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 3 [ZMOD 7])
      ∨ (p n ≡ 3 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7])
      ∨ (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7])
  · intro n
    simple_induction n with k IH
    · left
      constructor
      · calc p 0 = 2 := by rw [p]
          _ ≡ 2 [ZMOD 7] := by extra
      · calc p (0 + 1) = 3 := by rw [p]
          _ ≡ 3 [ZMOD 7] := by extra
    · obtain ⟨IH1 : p k ≡ 2 [ZMOD 7], IH2 : p (k + 1) ≡ 3 [ZMOD 7]⟩
        | ⟨IH1 : p k ≡ 3 [ZMOD 7], IH2 : p (k + 1) ≡ 2 [ZMOD 7]⟩
        | ⟨IH1 : p k ≡ 2 [ZMOD 7], IH2 : p (k + 1) ≡ 2 [ZMOD 7]⟩ := IH
      · right
        left
        constructor
        · apply IH2
        · calc p (k + 1 + 1) = 6 * p (k + 1) - p k := by rw [p]
            _ ≡ 6 * 3 - 2 [ZMOD 7] := by rel [IH1, IH2]
            _ = 7 * 2 + 2 := by numbers
            _ ≡ 2 [ZMOD 7] := by extra
      · right
        right
        constructor
        · apply IH2
        · calc p (k + 1 + 1) = 6 * p (k + 1) - p k := by rw [p]
            _ ≡ 6 * 2 - 3 [ZMOD 7] := by rel [IH1, IH2]
            _ = 7 * 1 + 2 := by numbers
            _ ≡ 2 [ZMOD 7] := by extra
      · left
        constructor
        · apply IH2
        · calc p (k + 1 + 1) = 6 * p (k + 1) - p k := by rw [p]
            _ ≡ 6 * 2 - 2 [ZMOD 7] := by rel [IH1, IH2]
            _ = 7 * 1 + 3 := by numbers
            _ ≡ 3 [ZMOD 7] := by extra
  obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m
  · left
    apply H1
  · right
    apply H1
  · left
    apply H1

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  dsimp
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · calc r 7 = 140 := by rfl
      _ ≥ 2 ^ 7 := by numbers
  · calc r 8 = 338 := by rfl
      _ ≥ 2 ^ 8 := by numbers
  · calc r (k + 2) = 2 * r (k + 1) + r k := by rw [r]
      _ ≥ 2 * 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ = 4 * 2 ^ k + 2 ^ k := by ring
      _ ≥ 4 * 2 ^ k := by extra
      _ = 2 ^ (k + 2) := by ring

/- Note.  `F n` is an integer and the bounds are rationals, so what the goal really says is
`↑(F n) < …`, with a coercion.  `ring`, `rel` and `extra` work around a coercion without
complaint, but `rw [F]` has to happen underneath it, so the unfolding is stated once as its own
`have` and `norm_cast` is what moves the coercion across the sum.

The slack terms come from the same subtraction as before.  `1.6 ^ (k + 2)` is `2.56` copies of
`1.6 ^ k`, while the recurrence supplies `1.6 ^ (k + 1) + 1.6 ^ k`, which is `2.6` of them.  The
gap of `0.04`, scaled by the leading `0.4`, is the `0.016 * 1.6 ^ k`.  The upper bound is the same
sum with `2.89` against `2.7`. -/

example : forall_sufficiently_large n : ℕ,
    (0.4:ℚ) * 1.6 ^ n < F n ∧ F n < (0.5:ℚ) * 1.7 ^ n := by
  dsimp
  use 8
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · have h8 : (F 8 : ℚ) = 34 := by norm_cast
    constructor
    · calc (0.4:ℚ) * 1.6 ^ 8 < 34 := by numbers
        _ = F 8 := by rw [h8]
    · calc (F 8 : ℚ) = 34 := by rw [h8]
        _ < 0.5 * 1.7 ^ 8 := by numbers
  · have h9 : (F 9 : ℚ) = 55 := by norm_cast
    constructor
    · calc (0.4:ℚ) * 1.6 ^ 9 < 55 := by numbers
        _ = F 9 := by rw [h9]
    · calc (F 9 : ℚ) = 55 := by rw [h9]
        _ < 0.5 * 1.7 ^ 9 := by numbers
  · obtain ⟨IH1a : (0.4:ℚ) * 1.6 ^ k < F k, IH1b : (F k : ℚ) < 0.5 * 1.7 ^ k⟩ := IH1
    obtain ⟨IH2a : (0.4:ℚ) * 1.6 ^ (k + 1) < F (k + 1),
      IH2b : (F (k + 1) : ℚ) < 0.5 * 1.7 ^ (k + 1)⟩ := IH2
    have hF : (F (k + 2) : ℚ) = F (k + 1) + F k := by
      rw [F]
      norm_cast
    constructor
    · calc (0.4:ℚ) * 1.6 ^ (k + 2) < 0.4 * 1.6 ^ (k + 2) + 0.016 * 1.6 ^ k := by extra
        _ = 0.4 * 1.6 ^ (k + 1) + 0.4 * 1.6 ^ k := by ring
        _ < F (k + 1) + F k := by rel [IH1a, IH2a]
        _ = F (k + 2) := by rw [hF]
    · calc (F (k + 2) : ℚ) = F (k + 1) + F k := by rw [hF]
        _ < 0.5 * 1.7 ^ (k + 1) + 0.5 * 1.7 ^ k := by rel [IH1b, IH2b]
        _ < 0.5 * 1.7 ^ (k + 1) + 0.5 * 1.7 ^ k + 0.095 * 1.7 ^ k := by extra
        _ = 0.5 * 1.7 ^ (k + 2) := by ring
