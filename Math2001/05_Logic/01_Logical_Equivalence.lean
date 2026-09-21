/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/

/- Note.  Nothing new arrives in this section.  Every proof is the Chapter 2 table applied to
statements with no arithmetic in them at all, so the connectives are all there is to go on and the
proofs write themselves once you read the goal.

Two conveniences worth knowing.

An `obtain` pattern can nest, so `obtain ⟨h1, h2 | h2⟩ := h` unpacks a conjunction and splits the
disjunction inside it in one step, and `obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h` splits a disjunction and
unpacks each side.  The punctuation mirrors the statement.

Both `intro` and `obtain` take type ascriptions, and this is the section where they earn their
keep.  A proof here can have five or six hypotheses live at once, all named `h`, `h'`, `hP`,
`hnQ`, and unlike every earlier chapter there is no arithmetic anywhere to hint at what they say.
Nothing individually is hard.  It is just that every name is a bare letter and what it stands for
is off the screen.

So `intro (h : ¬(P ∨ Q))` and `obtain ⟨hnP : ¬P, hnQ : ¬Q⟩ := h` rather than the bare versions.
The measure is how many things are in scope at once, not how complicated any single one of them
looks: one hypothesis called `h` is usually fine, six are not.

(For anyone who has written code in a language with anonymous functions, the parallel is exact.
`intro` binds a name the way a parameter does, and annotating it is writing the type signature.)

An `↔` can be rewritten with.  Given `h : P ↔ Q`, `rw [h]` turns a `P` in the goal into `Q` and
`rw [← h]` goes the other way, so an equivalence between propositions behaves like an equation
between numbers.
 -/



-- Book.
example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain (hP : P) | (hQ : Q) := h1
  · apply hP
  · contradiction


-- Book.
example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro (hP : P)
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)


-- Book.
example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro (h : P ∨ P)
    obtain (h1 : P) | (h2 : P) := h
    · apply h1
    · apply h2
  · intro (h : P)
    left
    apply h


example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro (h : P ∧ (Q ∨ R))
    obtain ⟨h1 : P, (h2 : Q) | (h2 : R)⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro (h : (P ∧ Q) ∨ (P ∧ R))
    obtain ⟨h1 : P, h2 : Q⟩ | ⟨h1 : P, h2 : R⟩ := h
    · constructor
      · apply h1
      · left
        apply h2
    · constructor
      · apply h1
      · right
        apply h2

#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


-- Book.
example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2


-- Book.
example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx : ∀ y : β, P x y⟩ := h
  intro y
  use x
  apply hx


-- Book.
example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro (h : ¬ ∃ x, P x) a (ha : P a)
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro (h : ∀ x, ¬ P x) (h' : ∃ x, P x)
    obtain ⟨x, hx : P x⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨hP : P, -⟩ := h
  left
  apply hP

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  · apply h1
    apply h3
  · apply h2
    apply h3

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro (h : P ∧ ¬ P)
  obtain ⟨hP : P, hnP : ¬ P⟩ := h
  contradiction

/- Note.  `rw [h1] at hP` turns the assumed `P` into `¬ Q`, which then sits beside `h2 : Q`.
Rewriting a hypothesis with an `↔` is the same move as rewriting one with an equation. -/

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  intro (hP : P)
  rw [h1] at hP
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain (hP : P) | (hQ : Q) := h1
  · apply hP
  · apply h2
    apply hQ

example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  constructor
  · intro (hpr : P ∧ R)
    obtain ⟨hP : P, hR : R⟩ := hpr
    constructor
    · rw [← h]
      apply hP
    · apply hR
  · intro (hqr : Q ∧ R)
    obtain ⟨hQ : Q, hR : R⟩ := hqr
    constructor
    · rw [h]
      apply hQ
    · apply hR

example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  · intro (h : P ∧ P)
    obtain ⟨h1 : P, -⟩ := h
    apply h1
  · intro (h : P)
    constructor
    · apply h
    · apply h

example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro (h : P ∨ Q)
    obtain (hP : P) | (hQ : Q) := h
    · right
      apply hP
    · left
      apply hQ
  · intro (h : Q ∨ P)
    obtain (hQ : Q) | (hP : P) := h
    · right
      apply hQ
    · left
      apply hP

/- Note.  One of De Morgan's laws.  Going right, the only way to use `¬(P ∨ Q)` is to build a
`P ∨ Q` and let it collide, which is why each half assumes its own disjunct and then supplies the
disjunction.  Section 5.3 automates this with `push_neg`. -/

example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro (h : ¬(P ∨ Q))
    constructor
    · intro (hP : P)
      have : P ∨ Q := by
        left
        apply hP
      contradiction
    · intro (hQ : Q)
      have : P ∨ Q := by
        right
        apply hQ
      contradiction
  · intro (h : ¬P ∧ ¬Q) (h' : P ∨ Q)
    obtain ⟨hnP : ¬P, hnQ : ¬Q⟩ := h
    obtain (hP : P) | (hQ : Q) := h'
    · contradiction
    · contradiction

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  apply h1
  apply h2

/- Note.  `h` is a family of equivalences, so it has to be applied at a point before it can be
rewritten with.  `rw [h x]` uses the one at the witness just obtained; plain `rw [h]` has no `x`
to work with. -/

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro (hp : ∃ x, P x)
    obtain ⟨x, hx : P x⟩ := hp
    use x
    rw [← h x]
    apply hx
  · intro (hq : ∃ x, Q x)
    obtain ⟨x, hx : Q x⟩ := hq
    use x
    rw [h x]
    apply hx

/- Note.  Two existentials commute, and the proof is pure bookkeeping: unpack both witnesses,
supply them in the other order.  Compare with the next exercise, where two `∀`s commute for the
same reason, and then with Section 4.1's `∃ a, ∀ b, ∃ c`, where the order genuinely matters.
Swapping is free only between quantifiers of the same kind. -/

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro (h : ∃ x y, P x y)
    obtain ⟨x, y, hxy : P x y⟩ := h
    use y, x
    apply hxy
  · intro (h : ∃ y x, P x y)
    obtain ⟨y, x, hxy : P x y⟩ := h
    use x, y
    apply hxy

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro (h : ∀ x y, P x y) y x
    apply h
  · intro (h : ∀ y x, P x y) x y
    apply h

/- Note.  This one needs `Q` not to mention `x`, which is why it is stated with `Q : Prop` rather
than `Q : α → Prop`.  Worth pausing on: the statement would be false otherwise, since the `x`
witnessing `P` and the `x` making `Q` true need not be the same. -/

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro (h : (∃ x, P x) ∧ Q)
    obtain ⟨hp : (∃ x, P x), hQ : Q⟩ := h
    obtain ⟨x, hx : P x⟩ := hp
    use x
    constructor
    · apply hx
    · apply hQ
  · intro (h : ∃ x, P x ∧ Q)
    obtain ⟨x, hx : P x, hQ : Q⟩ := h
    constructor
    · use x
      apply hx
    · apply hQ
