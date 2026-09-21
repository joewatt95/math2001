/- Live-demo notes: Chapters 4 and 5.  Not part of Macbeth's text.

This set covers Chapter 4 (Proofs with Structure II) and Chapter 5 (Logic).  Other chapters get
their own directory alongside this one.

Companion to `Demo.lean`, meant to be open in a second window.  For each problem: what it
demonstrates, what to settle before touching Lean, the skeleton to type first, where it goes
wrong, and the finished proof.

The proofs here are live code rather than comments, so they are checked on every build and
cannot drift away from what actually works.

# Priority

Ordered so that you can stop anywhere.  Each one shows a different part of drafting, so the
order is by what is lost if it is dropped, not by difficulty.

  1. Composite divisor        5.3   ~10 min   inventing the statement you need
  2. Pythagorean triple       4.4   ~20 min   writing the skeleton before the mathematics
  3. `not_forall` by hand     5.3   ~12 min   deferring a subgoal when you are stuck
  4. Unique midpoint          4.3   ~12 min   combining instances of a `∀`

If only one fits, do 1: it is the shortest and the point lands hardest.  If two, add 2, which is
the centrepiece and the only long one.  Numbers 3 and 4 repeat parts of the first two on smaller
problems.

This is priority order, not chapter order.  To follow the book instead, run 2, 4, 1, 3.
-/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Rel

math2001_init


/-! # 1.  A composite number has a proper divisor

Section 5.3, last exercise.

## What it demonstrates

Choosing to introduce a statement that is nowhere in the problem, purely so that a later tactic
has something to work on.  That is a design decision rather than a step, and it never shows up in
the finished proof.

## Before any Lean

Read the goal, `∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p`, then read `hp : ¬ Prime p`.  The gap between them is
the demo.  `hp` is the negation of a conjunction buried inside a definition, and nothing in it
hands you an `m`.

## The false start worth showing

Try `push_neg at hp` directly.  You get `Prime` unfolded and negated, which is not the shape of
the goal and does not help.

## The move

Notice the goal is almost exactly the negation of "no divisor works":

    ¬ (∀ m, 2 ≤ m → m < p → ¬ m ∣ p)

That statement appears nowhere in the problem.  Write it down as a `have` anyway, with a `sorry`,
and check that `push_neg` turns it into the goal.  Now there are two separate jobs.

    have H : ¬ (∀ m, 2 ≤ m → m < p → ¬ m ∣ p) := by sorry
    push_neg at H
    obtain ⟨m, hm2, hmp, hmdvd⟩ := H
    use m
    exact ⟨hm2, hmp, hmdvd⟩

## Filling the hole

`intro H` and you are assuming no divisor works, which is precisely `prime_test`'s hypothesis.
Apply it, get `Prime p`, collide with `hp`.

## What to draw out

The proof turned on writing down a statement nobody asked for.  You found it by looking at the
goal and asking what it is the negation of, then checking the guess with `push_neg`.  Working
backwards from the goal to something you can actually prove is the skill; the tactics are
incidental.
-/

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


/-! # 2.  A Pythagorean triple has no leg smaller than 3

Section 4.4, last worked example.  The long one, and the centrepiece.

## What it demonstrates

Drafting a proof whose shape is not visible from its statement, and which collapses into a tangle
if written linearly.

## Before any Lean

On paper: if `a ≤ 2` something must go wrong, so split there.  Do that split first and notice
that the `a ≥ 3` branch *is* the goal, one line.  Everything else lives in the branch you are
trying to destroy.  Write that much and run it:

    obtain (ha2 : a ≤ 2) | (ha3 : a ≥ 3) := le_or_succ_le a 2
    · sorry
    · apply ha3

## The skeleton

Ask what would finish the first branch.  If `a`, `b` and `c` were each pinned to a single value,
`numbers` could check the equation directly.  So the job is a chain of bounds, and it is worth
writing that chain as `have`s with `sorry` bodies before proving any of them:

    have hbc : b + 1 ≤ c := by sorry
    have key : 2 * b + 1 ≤ a ^ 2 := by sorry
    have hb1 : b = 1 := by sorry
    have hc2 : c = 2 := by sorry
    sorry

This is the demo.  It typechecks, it states the whole argument, and each hole is now a small
self-contained problem that can be filled in any order.

## Where it goes wrong

My first version left `b` and `c` as inequalities and threw all three at nested `interval_cases`.
On paper that is four branches; in Lean it was two, because `hbc` silently discharged the others,
and the bullet structure then matched nothing predictable from reading the proof.  Pinning `b`
and `c` to single values first is what makes the ending two clean branches.

Worth showing rather than describing.  It is the moment where organisation stops being cosmetic.

## What to draw out

The skeleton was writable before any of the mathematics was done, because it came from asking
what would finish rather than from working forwards.
-/

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain (ha2 : a ≤ 2) | (ha3 : a ≥ 3) := le_or_succ_le a 2

  · have hbc : b + 1 ≤ c := by
      have : b ^ 2 < c ^ 2 :=
        calc
          b ^ 2 < a ^ 2 + b ^ 2 := by extra
          _ = c ^ 2 := h_pyth
      cancel 2 at this
    have key : 2 * b + 1 ≤ a ^ 2 := by
      have :=
        calc
          b ^ 2 + (2 * b + 1) = (b + 1) ^ 2 := by ring
          _ ≤ c ^ 2 := by rel [hbc]
          _ = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ = b ^ 2 + a ^ 2 := by ring
      addarith [this]
    have hb1 : b = 1 := by
      have hup : b ≤ 1 := by
        obtain (h : b ≤ 1) | (h : b ≥ 2) := le_or_succ_le b 1
        · apply h
        · have :=
            calc
              5 = 2 * 2 + 1 := by numbers
              _ ≤ 2 * b + 1 := by rel [h]
              _ ≤ a ^ 2 := key
              _ ≤ 2 ^ 2 := by rel [ha2]
          numbers at this
      apply le_antisymm hup hb
    have hc2 : c = 2 := by
      have hup : c ≤ 2 := by
        obtain (h : c ≤ 2) | (h : c ≥ 3) := le_or_succ_le c 2
        · apply h
        · have :=
            calc
              9 = 3 ^ 2 := by numbers
              _ ≤ c ^ 2 := by rel [h]
              _ = a ^ 2 + b ^ 2 := by rw [h_pyth]
              _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [ha2, hb1.le]
          numbers at this
      apply le_antisymm hup (by addarith [hbc, hb1])
    have hp : a ^ 2 + 1 ^ 2 = 2 ^ 2 := by
      rw [hb1, hc2] at h_pyth
      apply h_pyth
    interval_cases a
    · numbers at hp
    · numbers at hp

  · apply ha3


/-! # 3.  `not_forall`, by hand

Section 5.3, third exercise.  `push_neg` does this for you; here you do it yourself.

## What it demonstrates

A goal with no arithmetic at all whose structure still defeats a linear attempt.  Everything is
`P`, `¬P`, `∀`, `∃`, and it is still possible to go round in circles.  Worth demonstrating
precisely because the instinct is that pure logic must be easy.

## Before any Lean

It is an `↔`, so two halves, and they are not equally hard.  Write `constructor` and two `sorry`s
and find out which.

## The easy half

Right to left.  You have `∃ x, ¬ P x` and `∀ x, P x`, and they collide at the witness.  Four
lines, nothing to decide.  Do it first so the board has a win on it.

## The hard half, and where the circling happens

Left to right you have `h : ¬ ∀ x, P x` and the goal `∃ x, ¬ P x`.  Try the direct route live:
`use ?` needs a specific `x`, and `h` tells you nothing about which.  There is no `x` to be had.
Let that dead end sit for a moment.

## The move

Since no witness can be produced, ask instead whether one exists.

    by_cases hex : ∃ x, ¬ P x
    · apply hex
    · have : ∀ x, P x := by sorry
      contradiction

The positive branch is immediate.  The negative branch is the interesting one, and that `have` is
a second, smaller problem needing its own `by_cases` on `P x`.

## What to draw out

Two things.  Nesting `by_cases` inside `by_cases` is not a failure of planning: the inner one
appears because the outer one changed what you were trying to prove.  And the
`have : ∀ x, P x := by sorry` line is the organisational trick, naming what you need, deferring
it, and letting you check the outer argument before committing to the inner one.

Worth closing with: this is the equivalence `push_neg` applies that needs excluded middle, which
is why `push_neg` is not a constructive tactic.
-/

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


/-! # 4.  Exactly one point is within 1 of everything in [1, 3]

Section 4.3, first exercise.

## What it demonstrates

A goal that decomposes cleanly at the top and then needs separate thinking in each half.  Also a
case where the obvious first attempt at the second half is not wrong, only insufficient, which is
a common and demoralising experience worth having in public.

## Before any Lean

`∃!` is an existence claim and a uniqueness claim glued together, so the skeleton is forced:

    use 2
    constructor
    · sorry   -- 2 works
    · sorry   -- nothing else does

The witness is the midpoint of the interval, which someone will guess.  Write the skeleton, run
it, and there are now two unrelated problems on the board.

## First half

Show `(a - 2) ^ 2 ≤ 1` for `a` between `1` and `3`.  The identity is
`1 - (a - 2) ^ 2 = (a - 1) * (3 - a)`, a product the hypotheses make nonnegative.  Try
`positivity` and watch it fail: it does not read hypotheses, so a product of two things you know
to be nonnegative is invisible to it.  `mul_nonneg` applied to the two bounds is the fix.

## Second half, and the interesting bit

Take an arbitrary `y` that works and force `y = 2`.  The natural move is to feed `hy` an
endpoint.  Do it live.  `hy 1` gives `0 ≤ y ≤ 2`, which does not pin `y`; `hy 3` gives
`2 ≤ y ≤ 4`, which also does not.  Each alone is insufficient and together they are exactly
enough.

Adding the two squares collapses it, since `(1 - y) ^ 2 + (3 - y) ^ 2 - 2` is `2 * (y - 2) ^ 2`.
That forces `(y - 2) ^ 2 ≤ 0`, and a square that is at most zero is zero.

## What to draw out

When one instance of a `∀` hypothesis is not enough, the question is not which instance is the
right one but which combination of instances.  That reframing is invisible in the finished proof,
which is exactly why it is worth doing live.
-/

example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  constructor
  · intro (a : ℚ) (ha1 : a ≥ 1) (ha3 : a ≤ 3)
    have : 0 ≤ (a - 1) * (3 - a) := mul_nonneg (by addarith [ha1]) (by addarith [ha3])
    calc
      (a - 2) ^ 2 = 1 - (a - 1) * (3 - a) := by ring
      _ ≤ 1 - 0 := by rel [this]
      _ = 1 := by ring
  · intro (y : ℚ) (hy : ∀ a, a ≥ 1 → a ≤ 3 → (a - y) ^ 2 ≤ 1)
    have h1 : (1 - y) ^ 2 ≤ 1 := hy 1 (by numbers) (by numbers)
    have h3 : (3 - y) ^ 2 ≤ 1 := hy 3 (by numbers) (by numbers)
    have :=
      calc
        (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
        _ ≤ (1 + 1 - 2) / 2 := by rel [h1, h3]
        _ = 0 := by numbers
    have : (y - 2) ^ 2 = 0 := le_antisymm this (by positivity)
    have : y - 2 = 0 := by cancel 2 at this
    addarith [this]
