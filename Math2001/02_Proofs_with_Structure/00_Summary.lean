/- A summary of Chapter 2, written for this course.  Not part of Macbeth's text.

Read this first, then the sections, then come back to it.  Part 1 is what the chapter is about.
Part 2 is how to write the proofs so that you can still read them next week. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


/-! # Part 1: proving and using logical statements

Sections 2.3 to 2.5 each introduce one logical symbol, and each time there are exactly two
questions.  How do I prove a statement built with this symbol, and how do I use one I have been
given?  Each question gets its own tactic:

                    to prove it              to use it
    A ∧ B           constructor              obtain ⟨h1, h2⟩ := h
    A ∨ B           left   or   right        obtain h1 | h2 := h
    ∃ x, P x        use                      obtain ⟨x, hx⟩ := h

Three sections, six tactics, one idea.  Once the pattern is clear you can usually guess the tactic
for a symbol you have not met yet, which is worth more than memorising the table.  Chapter 4 adds
the next two rows, with `intro` to prove an implication or a "for all" and `apply` to use one.

The interesting part is that every row is lopsided.

To prove `A ∨ B` you must pick a side and prove it.  To use `A ∨ B` you must handle both sides,
because you were never told which one holds.  Proving is a commitment, using is a case analysis.

To prove `∃ x, P x` you must produce an actual value.  To use one you receive a value you know
nothing about beyond the single fact attached to it.  Proving is construction, using is accepting
something opaque.

`∧` is the easy row, since both directions hand over everything at once.  That is why the same
angle brackets appear on both sides of it.

The `∃` row is the one you will use most, and often without noticing.  Many things that look like
new ideas turn out to be existentials wearing a name.  In Chapter 3, `Int.Even n` is
`∃ k, n = 2 * k`, `a ∣ b` is `∃ c, b = a * c`, and `a ≡ b [ZMOD n]` is `a - b` divisible by `n`,
so an existential two layers down.  Each time, proving one means producing a witness with `use`
and using one means `obtain`.  Nothing new is needed, which is the point of learning the row
rather than the three tactics.
-/

/-! ## `∧`, "and" -/

-- To prove one.  `constructor` splits the goal into its two halves.
example {x : ℝ} (hx : x = 2) : x = 2 ∧ x ^ 2 = 4 := by
  constructor
  · show x = 2
    apply hx

  · show x ^ 2 = 4
    calc
      x ^ 2 = 2 ^ 2 := by rw [hx]
      _ = 4 := by numbers

-- To use one.  `obtain` hands you both halves at once.
example {x : ℝ} (h : x > 1 ∧ x < 3) : x < 3 := by
  obtain ⟨h1 : x > 1, h2 : x < 3⟩ := h
  apply h2

/-! ## `∨`, "or" -/

-- To prove one.  Choose a side.  You have to know which side is true before you start.
example {x : ℝ} (hx : x = 2) : x = 1 ∨ x = 2 := by
  right
  show x = 2
  apply hx

-- To use one.  Handle both sides.  One bullet per case, proving the same goal in each.
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain (hx : x = 1) | (hx : x = 2) := h
  · rw [hx]
    ring
  · rw [hx]
    ring

/-! ## `∃`, "there exists" -/

-- To prove one.  Supply a witness.  Finding it is your job, not Lean's.
example : ∃ n : ℤ, 3 * n = 12 := by
  use 4
  numbers

-- To use one.  `obtain` names the value and the fact about it.  Both directions appear here.
example {a : ℤ} (h : ∃ b : ℤ, a = 2 * b) : ∃ c : ℤ, a = c + c := by
  obtain ⟨b, hb : a = 2 * b⟩ := h
  use b
  calc
    a = 2 * b := hb
    _ = b + b := by ring


/-! # Part 2: writing a proof someone can read

From Chapter 2 onwards a proof is no longer a single chain, and it becomes possible to write
something Lean accepts and nobody can follow.  What follows is not required by Lean.  It is the
habit of writing proofs that survive being read later, and most of it is folklore rather than
anything you will find in a textbook.

**One principle, from which the rest follows.**  Reading a run of tactics, can you picture what
each one does to the proof state?  If so, leave it alone.  If not, break it up and name the
intermediate results, since a named fact is a state nobody has to imagine.

That asks what the run does, not how long it is.  `obtain` then `rw` then `ring` is just "consider
the cases, substitute, simplify", so several exercises in Section 2.3 leave it bare.  A shorter run
doing something less familiar may well need pulling apart.

Most of what follows is this question in another costume.  How small should a step be, do I need
another `have`, how simple must the closing chain be: small enough, and simple enough, to picture.
The answer depends on who is reading, so err towards breaking things up.

**Say what the goal became.**  A tactic like `apply ne_of_lt` replaces the goal with a different
statement, and from then on a reader has to know that lemma to know what is being proved.  There
are two ways to keep it visible.  Carry on backwards and say the new goal outright:

    apply ne_of_lt
    show n ^ 2 < 2
    calc ...

Or work forwards, proving the fact under its own name and applying the lemma at the end:

    have h : n ^ 2 < 2 := by calc ...
    apply ne_of_lt
    apply h

Both leave the reader with something to read.  Neither is the house style.  Backwards is shorter,
so reach for it when the fact is wanted once and the proof of it is short.  What is not worth
doing is applying a lemma and carrying on with nothing on the page to say what you are proving.

There is one case where the choice is made for you.  `constructor` splits a conjunction in two, so
a goal with three or four parts costs you a level of nesting per part before you have proved
anything.  Establishing each part as a named fact and assembling them at the end with `⟨...⟩` stays
flat, and whatever nesting is left is nesting the argument actually asked for.  Compare the
taxicab example in Section 2.5 with the exercise that closes it.

**Keep runs of tactics together.**  Tactics that change the goal or a hypothesis in place, such as
`rw ... at` and `cancel ... at`, are fine at the start of a proof and fine at the end.  What causes
trouble is sandwiching one between `have` steps, because a name then means one thing above the
line and something else below it.  The two proofs below are both accepted.  Only the second says
what it is doing. -/

-- Harder to read: after `cancel`, `h2` no longer says what its own line says.
example {s : ℚ} (h1 : 3 * s ≤ -6) : s + 1 ≤ -1 := by
  have h2 : 3 * s ≤ 3 * -2 := by addarith [h1]
  cancel 3 at h2
  have h3 : s + 1 ≤ -1 := by addarith [h2]
  apply h3

-- Clearer: the result of `cancel` is given a name and a statement, so every line stands alone.
example {s : ℚ} (h1 : 3 * s ≤ -6) : s + 1 ≤ -1 := by
  have h2 : 3 * s ≤ 3 * -2 := by addarith [h1]
  have h3 : s ≤ -2 := by cancel 3 at h2
  have h4 : s + 1 ≤ -1 := by addarith [h3]
  apply h4

/-! **Nest along the structure of the argument.**  When a proof has real shape, one step deserving
several lines of its own, put those lines inside the `have` that needs them.  The reader then sees
the outline first and the detail only on request, and the scaffolding cannot be mistaken for
something used later.  The first two proofs in Section 2.5 are laid out this way.

On a short proof the extra layer costs more than it saves, and flat is better.  A proof may be
flat in one part and nested in another.

**Write documentation that Lean checks.**  Several things in these files are ignored by the
compiler and aimed at the reader:

    show x = 2                                   -- what this branch is proving
    obtain (hx : x = 1) | (hx : x = 2) := h      -- what each case gives you
    have : n ≤ 2 := hn                           -- which case you are now in

Each is checked, so unlike a comment none of them can quietly fall out of step with the proof.  A
wrong `show` fails on the spot rather than letting you write a branch that answers the other
question.

**Where it earns its place.**  Annotate once terms get complicated, the case analysis nests, or
named facts have to be threaded between steps.  The `n ^ 2 ≠ 2` proof over `ℤ` in Section 2.3 is
the clearest case in this chapter.  A short proof carrying none of that is better left bare, as
several exercises in the same section are.

**Use bullets whenever a tactic leaves more than one goal.**  Lean does not require them.  Without
them, several goals in a row read as one flat list and there is no way to see where one ends.

**Name things, or deliberately don't.**  An unnamed `have` is called `this`, and a second one
shadows the first, which is fine when the next line consumes it and a nuisance otherwise.  If two
cases are about different variables, give them different names, `hx` and `hy` rather than `h`
twice.  Use `_` for a component you are deliberately discarding, as in `obtain ⟨h1, _⟩ := this`,
so nobody hunts for where it was used.
-/


/-! # Optional background

None of this is needed for the exercises.  It is here so that the tactics look less like an
arbitrary list, and so that you know what to search for if you want to go further.

The two columns of the table in Part 1 have standard names.  The left-hand one is the
*introduction rule* for a symbol and the right-hand one is its *elimination rule*, and a proof
system built out of such pairs is called *natural deduction*.  If a first logic course showed you
proof trees or a sequent calculus, this is that material with a keyboard interface.

Two more phrases worth knowing.

Insisting that a proof of `∃ x, P x` actually produce an `x`, rather than merely showing that its
non-existence would be absurd, is the point at which *constructive* (or *intuitionistic*) logic
departs from classical logic.  Section 5.2 confronts that difference directly.

The fact that a proof of `A ∧ B` is literally a pair of proofs, which is why `⟨_, _⟩` both builds
one and takes one apart, is the *Curry-Howard correspondence*.  It is the reason one language can
be a programming language and a proof checker at the same time.

The structured style in Part 2 is not specific to Lean.  It is close to how proofs are written in
Isabelle's *Isar* language, where the structure is enforced by the syntax rather than left to the
author's discipline.  Lean gives you the tools and lets you choose, which is why it is worth
choosing deliberately.
-/
