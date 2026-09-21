/- A summary of Chapter 4, written for this course.  Not part of Macbeth's text. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Chapter 4 on one page

## The table, completed

Chapter 2 gave three rows.  Chapter 4 adds the rest, and the pattern does not change.

                    to prove it                  to use it
    A ∧ B           constructor                  obtain ⟨h1, h2⟩ := h
    A ∨ B           left  or  right              obtain h1 | h2 := h
    ∃ x, P x        use                          obtain ⟨x, hx⟩ := h
    ∀ x, P x        intro x                      h t   for a chosen t
    P → Q           intro h                      apply h
    P ↔ Q           constructor                  rw [h]
    ∃! x, P x       use, then constructor        obtain ⟨x, hx, huniq⟩ := h
    ¬ P             intro h, derive False        collide it with a proof of P

Two of those rows deserve more than a line.

**Using a `∀` means choosing.**  That choice is the whole content of most of Section 4.1.  The
statement tells you nothing about which value to pick, so the work happens on paper first, and
picking wrong sends you down a branch that cannot close.

**`¬ P` is notation for `P → False`.**  Nothing special is going on, which is why `intro` works
on it.  The work is never the `intro`; it is manufacturing something false afterwards.

## Making a contradiction

Two tools, and they are not interchangeable.

`contradiction` wants `h` and `¬h` both in context.

`numbers at h` wants `h` to be a false statement built from numerals: `7 < 3`, `0 ≡ 1 [ZMOD 3]`,
`2 < 0`.  It will not reject `p < 0` with `p` a variable, even over `ℕ` where that is false.
Chain such a thing against a numeric bound first and hand `numbers` something it can see.

Usually `numbers at` is shorter, since it skips building the negation.  Section 4.4 proves the
same statement both ways so you can compare.

## Turning a statement into finitely many cases

A recurring move, and the one worth practising.  An inequality or a congruence gets squeezed
until only a handful of values survive, and then each is checked.

- `le_or_succ_le a n` splits at a literal.  Its second argument must be a literal.
- `mod_cases h : n % k` splits into the `k` residues.
- `interval_cases a` enumerates between bounds already in context, and
  `interval_cases h : a` names the case hypothesis as well.

Two cautions from Section 4.4.  Leave surplus inequalities in context and `interval_cases` will
discharge some branches silently, so the bullets stop matching what you predicted from reading;
pin values down first if you want a predictable shape.  And `numbers at` wants both sides of a
congruence reduced, so `16 ≡ 4 [ZMOD 5]` is not rejected until you write it as `1 ≡ 4 [ZMOD 5]`.

## Where the tactics run out

Worth knowing before you fight one of them.

`addarith` does linear arithmetic over atoms and will not divide.  Over `ℤ` that is principled,
since halving is not a ring operation, and `cancel` is the way through.  Over `ℝ` it is simply a
limit of the tactic, and a three-line `calc` does it.

`positivity` does not read hypotheses.  A product of two things your assumptions make nonnegative
is invisible to it, and `mul_nonneg` applied by hand is the fix.

`rel` and `extra` do read the whole context, not just the list in brackets.  That is why a step
can work for reasons nothing on the line mentions, and why deleting an apparently unused
hypothesis can break a proof three lines later.
-/
