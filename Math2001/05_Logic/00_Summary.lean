/- A summary of Chapter 5, written for this course.  Not part of Macbeth's text. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Chapter 5 on one page

## Nothing new, except two things

Section 5.1 introduces no tactics at all.  Every proof is the table from the Chapter 2 summary,
applied to statements with no arithmetic in them, so the connectives are the only thing to read.
That makes it good practice and a poor source of surprises.

The two genuinely new things are `by_cases` in 5.2 and `push_neg` in 5.3, and they are related:
both are ways of using the law of the excluded middle.

## `by_cases`, and proving something without finding it

`by_cases h : P` splits on whether `P` holds, for any proposition, with no obligation to decide
which.  Nothing before this chapter could do that.

What it buys is worth stating plainly.  In the `Superpowered` example nobody knows whether `2` is
superpowered, and the proof does not find out.  It says: if it is, take `k = 2`; if it is not,
take `k = 1`.  Either way some `k` exists, and no `k` is ever produced.

Compare Section 2.5, where proving `∃` always meant handing over a witness.  A logic that refuses
this move is called *constructive*, and the difference is not a technicality: it is the reason
`by_cases` has to be introduced as a new thing rather than having been available all along.

## Negation is an algorithm

Pushing a negation inwards is mechanical.  Each step is one equivalence:

    not_forall          ¬∀ x, P x      ↔  ∃ x, ¬ P x
    not_exists          ¬∃ x, P x      ↔  ∀ x, ¬ P x
    Classical.not_imp   ¬(P → Q)       ↔  P ∧ ¬ Q
    not_and_or          ¬(P ∧ Q)       ↔  ¬P ∨ ¬Q
    not_or              ¬(P ∨ Q)       ↔  ¬P ∧ ¬Q
    not_lt, not_le      ¬(a < b)       ↔  b ≤ a,  and so on

Applied by hand with `rel`, one per `calc` step.  `push_neg` runs the lot.

Three things to know about it.

**Look before you leap.**  `#push_neg <statement>` shows where it lands without committing.  The
result is often not the shape you would have written: negating `∃ t, t ≤ 4 ∧ t ≥ 5` gives
`∀ t, 4 < t ∨ t < 5`, a disjunction, so `intro t ht` will not work on it.

**It is not constructive.**  `not_forall` is exactly the step that needs excluded middle, which
is why Section 5.3 can prove it only with `by_cases`, twice over.

**One equivalence per `rel` step.**  Combining them can leave a type undetermined:
`rel [not_and_or, not_lt]` reports a stuck instance, while the same two in separate steps work.

## Annotate more here than anywhere else

These proofs carry five or six hypotheses at once, named `h`, `h'`, `hP`, `hnQ`, with no
arithmetic anywhere to hint at what any of them says.  Nothing is individually hard; it is that
every name is a bare letter.  `intro (h : ¬(P ∨ Q))` and `obtain ⟨hnP : ¬P, hnQ : ¬Q⟩ := h` are
worth the characters.

The measure is how many things are in scope at once, not how complicated any one of them looks.
-/
