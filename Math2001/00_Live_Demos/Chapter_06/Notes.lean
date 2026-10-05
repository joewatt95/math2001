/- Live-demo notes: Chapter 6.  Not part of Macbeth's text.

This set covers Chapter 6 (Induction).  Other chapters get their own directory alongside this one.

Companion to `Demo.lean`, meant to be open in a second window.  For each problem: what it
demonstrates, what to settle before touching Lean, the skeleton to type first, where it goes
wrong, and the finished proof.

The proofs here are live code rather than comments, so they are checked on every build and
cannot drift away from what actually works.

# Priority

Ordered so that you can stop anywhere.  Each one shows a different part of drafting, so the
order is by what is lost if it is dropped, not by difficulty.

  1. Recurrence mod 7         6.3   ~20 min   strengthening a statement that will not induct
  2. Fibonacci sandwich       6.3   ~20 min   six holes before any mathematics
  3. `2 ^ n` beats `n ^ 3`    6.1   ~12 min   pulling a step out when the chain turns ugly
  4. Powers of two            6.4   ~12 min   recursion where no induction tactic fits

If only one fits, do 1.  It is the one idea in the chapter that cannot be reached by pattern
matching on the worked examples, and it fails twice in public before it works.  If two, add 2,
which is the long one and the only place where organising comes before thinking.  Numbers 3 and 4
are smaller and each makes a single point.

This is priority order.  To follow the book instead, run 3, 1, 2, 4, which is nearly the same
list read the other way up.
-/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Rel

math2001_init


/-! # 1.  A recurrence that stays in `{2, 3}` mod 7

Section 6.3, exercise.

## What it demonstrates

That a true statement can be unprovable by induction, that the repair is to prove something
*harder*, and that finding the right harder statement is arithmetic rather than inspiration.

It is worth doing live because it fails twice.  The first failure kills the obvious approach and
the second kills the obvious repair, and neither failure is visible in the finished proof.

## Before any Lean

Read the recurrence, `p (n + 2) = 6 * p (n + 1) - p n`, and note that it reaches back two places.
So the instinct is `two_step_induction`, and the base cases are `p 0 = 2` and `p 1 = 3`, both
immediate.

## First failure: the direct induction

Type it:

    two_step_induction m with k IH1 IH2

In the step you have `IH1 : p k ≡ 2 ∨ p k ≡ 3` and `IH2 : p (k + 1) ≡ 2 ∨ p (k + 1) ≡ 3`, so four
combinations.  Take them in turn and the fourth kills you: if `p k ≡ 3` and `p (k + 1) ≡ 3` then

    p (k + 2) = 6 * 3 - 3 = 15 ≡ 1  (mod 7)

which is in neither class.  Say plainly what has happened.  The sequence never actually visits
that combination, but the inductive hypothesis cannot tell you so, because all it remembers is
which class each term is in and not how they are paired.

## The diagnosis, and the computation

Pairs are what the hypothesis forgets, so compute the pairs.  Type these live:

    #eval p 0 % 7   #eval p 1 % 7   #eval p 2 % 7   #eval p 3 % 7
    #eval p 4 % 7   #eval p 5 % 7   #eval p 6 % 7

and read off `2, 3, 2, 2, 3, 2, 2`.  Consecutive pairs are `(2, 3), (3, 2), (2, 2)` and then it
repeats.

## Second failure: the obvious strengthening

Everyone guesses two cases first, by analogy with the worked example earlier in the section:

    (p n ≡ 2 ∧ p (n + 1) ≡ 3) ∨ (p n ≡ 3 ∧ p (n + 1) ≡ 2)

Try it.  The base case is fine and so is the first branch, since `6 * 3 - 2 = 16 ≡ 2` moves
`(2, 3)` to `(3, 2)`.  The second branch has `6 * 2 - 3 = 9 ≡ 2`, which moves `(3, 2)` to
`(2, 2)`, and that pair is not on the list.  The invariant is still too weak.

Point back at the `#eval` output: the cycle has length three, so two cases were never going to be
enough.  The arithmetic was on the screen before the guess was made.

## The skeleton that works

    have H : ∀ n : ℕ, (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 3 [ZMOD 7])
        ∨ (p n ≡ 3 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7])
        ∨ (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7])
    · sorry
    obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m
    · left
      apply H1
    · right
      apply H1
    · left
      apply H1

Run that before proving `H`.  It shows that the strengthened statement really does give the one
you were asked for, which is worth checking before spending twenty minutes on it.

One more thing to point out when filling `H`: it is a `simple_induction`, not a two-step one.
Carrying the pair `(p n, p (n + 1))` along already remembers everything the recurrence asks for,
so reaching back two places is no longer needed.

## What to draw out

Proving more can be easier, because a stronger statement hands you more to work with as well as
asking more of you.  And the shape of the strengthening came from seven `#eval`s, not from
staring at the recurrence.
-/

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


/-! # 2.  Fibonacci, between two exponentials

Section 6.3, last exercise.  The long one.

## What it demonstrates

Laying out six independent holes and checking that they add up, before proving any of them.  By
the time the mathematics starts there is nothing left to decide.

## Before any Lean

`forall_sufficiently_large n, P n` is `∃ C, ∀ n ≥ C, P n`, so you owe a threshold and nothing in
the statement suggests one.  Run `dsimp` first so that the `∃ C` is visible rather than hidden
behind notation.

Then compute.  `F` is `1, 1, 2, 3, 5, 8, 13, 21, 34, 55`.  The lower bound `0.4 * 1.6 ^ n` starts
at `0.4` and never catches up, so it is free.  The upper bound is the one that bites:
`0.5 * 1.7 ^ 7` is about `20.5`, below `F 7 = 21`, and `0.5 * 1.7 ^ 8` is about `34.9`, just above
`F 8 = 34`.  So `C = 8`, and it is close.

Say out loud that this was found by arithmetic and could not have been guessed.

## The skeleton

Two base cases, because the recurrence reaches back two places, and each goal is a conjunction:

    use 8
    intro n hn
    two_step_induction_from_starting_point n, hn with k hk IH1 IH2
    · constructor
      · sorry
      · sorry
    · constructor
      · sorry
      · sorry
    · constructor
      · sorry
      · sorry

Six holes, all independent.  This is the demo: it typechecks, it is the entire structure of the
proof, and from here the room can be asked which hole to do first.

## The base cases, and the coercion

`numbers` will not close `0.4 * 1.6 ^ 8 < F 8`, because `F 8` means nothing to it.  Worse, `F 8`
is an integer while the bounds are rationals, so there is a coercion in the goal that is easy to
miss.  Pin the value once, in the form the goal actually uses:

    have h8 : (F 8 : ℚ) = 34 := by norm_cast

and then both halves are `numbers` with an `rw` either side of them.

## The inductive step

Unpack the two inductive hypotheses with their types written out.  There are four facts in play
and they are about different arguments, so `IH1a`, `IH1b`, `IH2a`, `IH2b` with bare names would
be unreadable within a minute.

Unfolding `F (k + 2)` has to happen underneath the coercion, so it goes in a `have` of its own
with `norm_cast` doing the moving.  Write that line before you need it.

## The slack, derived on the board

The only arithmetic in the problem.  `1.6 ^ (k + 2)` is `2.56` copies of `1.6 ^ k`, while the
recurrence hands you `1.6 ^ (k + 1) + 1.6 ^ k`, which is `2.6` of them.  The gap is `0.04` copies,
and the leading `0.4` scales it to `0.016 * 1.6 ^ k`.  That is where the magic constant in the
first `extra` step comes from.  The upper bound is the same sum with `2.89` against `2.7`, giving
`0.095`.

Deriving these in front of the room is the difference between a proof that looks arbitrary and one
that looks forced.

## What to draw out

The skeleton was writable knowing only the shape of the statement.  Everything hard came
afterwards, and each piece was small because the structure had already absorbed the complexity.
-/

def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

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


/-! # 3.  `2 ^ n` eventually beats `n ^ 3`

Section 6.1, exercise.

## What it demonstrates

A `calc` chain that grows past the point of being readable, and what to do about it.  Also the
one trap in the chapter that stops a correct proof dead: truncated subtraction in `ℕ`.

## Before any Lean

Find the threshold by computing, as in the previous problem.  `2 ^ 9 = 512` against `9 ^ 3 = 729`
is a loss, and `2 ^ 10 = 1024` against `10 ^ 3 = 1000` is a win.  So `C = 10`, and again it is
close.

## The step, written forwards

Open the chain the usual way and see how far it goes on its own:

    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 3 := by rel [IH]
      _ = k ^ 3 + k ^ 3 := by ring

Now `(k + 1) ^ 3` is `k ^ 3 + 3 * k ^ 2 + 3 * k + 1`, so the spare copy of `k ^ 3` has to cover
`3 * k ^ 2 + 3 * k + 1`, and that is the whole problem.

## Where it goes wrong

Carry on in the same chain and you will want to write the slack as a difference:

    _ = (k + 1) ^ 3 + (67 * k - 1) := by ring

`ring` refuses.  In `ℕ` that subtraction is truncated rather than genuine, so `3 - 5` is `0` and
the identity you wrote is simply false.  This is worth hitting live, because the error message is
about `ring` and says nothing about subtraction.

Two repairs, and both are needed.  Bound `67 * k` below by `670` first, so the slack is a plain
numeral.  And stop trying to do it in one chain.

## The repair

The bound on `k ^ 3` has nothing to do with induction.  It is a fact about `k`, so it becomes a
`have` of its own above the chain, and the chain shrinks to five lines that say exactly what the
argument is: double the inductive hypothesis, and spend the spare `k ^ 3`.

## What to draw out

When a `calc` chain stops being readable, the question is not how to shorten it but which part of
it was never about the main argument.  Pull that part out and name it.
-/

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    have h1 : k ^ 3 ≥ 3 * k ^ 2 + 3 * k + 1 :=
      calc k ^ 3 = k * k ^ 2 := by ring
        _ ≥ 10 * k ^ 2 := by rel [hk]
        _ = 3 * k ^ 2 + 7 * k * k := by ring
        _ ≥ 3 * k ^ 2 + 7 * 10 * k := by rel [hk]
        _ = 3 * k ^ 2 + 3 * k + 67 * k := by ring
        _ ≥ 3 * k ^ 2 + 3 * k + 67 * 10 := by rel [hk]
        _ = 3 * k ^ 2 + 3 * k + 1 + 669 := by ring
        _ ≥ 3 * k ^ 2 + 3 * k + 1 := by extra
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 3 := by rel [IH]
      _ = k ^ 3 + k ^ 3 := by ring
      _ ≥ k ^ 3 + (3 * k ^ 2 + 3 * k + 1) := by rel [h1]
      _ = (k + 1) ^ 3 := by ring


/-! # 4.  Every positive integer is a power of two times an odd number

Section 6.4, exercise.

## What it demonstrates

A proof whose recursion matches none of the tactics, and what to do when the thing you want to
reach back to is neither `k` nor `k + 1`.

## Before any Lean

Say what the proof is, in one sentence, before typing: if `n` is odd it is `2 ^ 0` times itself,
and if it is even then `n = 2 * m` and whatever works for `m` works for `n` with one more factor
of two.

Now notice that `m` is `n / 2`.  None of `simple_induction`, `induction_from_starting_point` or
`two_step_induction` reaches back that far, so none of them applies.

## The skeleton

Since this is a `theorem` rather than an `example`, it has a name, and a proof may quote its own
name at a smaller argument.  That is the whole mechanism.

    obtain (hn' : Nat.Even n) | (hn' : Nat.Odd n) := Nat.even_or_odd_lib n
    · obtain ⟨m, hm : n = 2 * m⟩ := hn'
      sorry
    · sorry

Do the odd branch first.  It is four lines and gets a win on the board.

## The even branch

The recursive call is `extract_pow_two m _`, and the hole is `0 < m`.  State it as a `have` with
`sorry`, make the call, finish the branch, and only then come back and fill it.  Deferring the
small obligation keeps the shape of the branch visible while you are still deciding it.

Filling it is two lines and worth doing slowly.  `hn : 0 < n` becomes `0 < 2 * m` once you rewrite
with `hm`, and `cancel 2` divides it through.

## Termination, which nobody asked about

Lean has to know the recursion stops, and nothing in the proof says so.  It works it out from
`hm : n = 2 * m` and `0 < m`, both of which are in the context for other reasons.  Worth a
sentence: had they not been there, the fix would be to state `m < n` as a `have`.

## What to draw out

Induction is not a tactic, it is permission to use the statement at a smaller argument.  The
tactics in the earlier sections were packaging that permission into the two most common shapes.
When neither shape fits, drop the packaging.
-/

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Nat.Odd x ∧ n = 2 ^ a * x := by
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
