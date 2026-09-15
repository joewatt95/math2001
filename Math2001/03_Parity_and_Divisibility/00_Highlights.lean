/- Which examples in Chapter 3 are worth time.  Not part of Macbeth's text. -/
import Library.Basic

math2001_init

/-! # Chapter 3: what to slow down on

Most of this chapter is one move repeated: unpack a disguised existential, substitute, factor,
read the witness off.  Once that is clear the exercises are practice rather than instruction.  The
entries below are the exceptions, either because the problem is hard or because the proof here
departs sharply from the book or from a first attempt.

## 3.1 the opening note, and any annotated `obtain`

*Style, and the foundation for the whole chapter.*  `Int.Even n` is `∃ k, n = 2 * k`.  Nothing on
the face of `Int.Even n` says so, which is why every `obtain` in these three files carries its
type.  Show `obtain ⟨k, hk⟩ := hn` beside `obtain ⟨k, hk : n = 2 * k + 1⟩ := hn` and ask what the
first one tells a reader.

Worth establishing here, because 3.2 and 3.3 both depend on it and each adds a layer.

## 3.1 `∃ m ≥ n, Int.Odd m`

*Moderately hard, and a first attempt usually stalls.*  There is no single witness that works for
every `n`, so the case split has to come before the `use`, and each branch picks its own.  If `n`
is odd take `n`, otherwise take `n + 1`.

The habit is that `use` does not have to be the first thing you do.

## 3.1 `Int.Even (a - b) ∨ Int.Even (a + c) ∨ Int.Even (b - c)`

*The hardest in the chapter.*  On paper it is the pigeonhole principle in one line: three integers,
two parities, so some pair matches.  Lean cannot say "some pair", so it becomes a case analysis,
and the craft is splitting on `c` only where `a` and `b` disagree, which gives six leaves instead
of eight.

Good for showing that a one-line human argument and a short Lean proof are different things.

## 3.3 the twelve `apply` calls, bulleted

*Style, and a sharp contrast with the book.*  The book writes this as a flat run.  Each `add` and
`mul` leaves two goals, so it is really a tree four levels deep, and flat it is unreadable even
though it compiles.

Pair it with the same statement proved by `rel` at the start of 3.4 to show what the section was
for.

## 3.3 `show ∃ k, a - b = n * k` before each `use`

*Style, and the best place for a remark to the stronger students.*  Congruence has several
equivalent pictures: same remainder, same class in `ℤ/nℤ`, difference in the ideal.  Anyone who has
met rings will be carrying one of the later ones.  Lean has to pick, and picks `n ∣ a - b`, so the
`show` is what says which picture is on screen.

## 3.4 `mod_cases`, and the residue labels

*Style.*  Cheap to cover and pays off immediately.  The branch count is the modulus, `hx` is called
the same thing in every branch and means something different in each, and the last exercise has
five of them.  With three you can count; the point of the labels is that with eleven you cannot.

## 3.5 the two rewrites that will not merge

*A gotcha worth pre-empting.*  Everyone tries `rw [ha, hb]` here.  Both hypotheses are about `m`,
`rw` replaces every occurrence at once, so the first consumes both copies and the second has
nothing to match.

Contrast with 3.1, where `rw [ha, hb]` is correct because the two hypotheses are about different
variables.  Stating the rule both ways is what makes it stick.

## 3.5 the same statement proved with two different Bezout pairs

*Style.*  `8 ∣ 5 * n → 8 ∣ n` appears twice, and the two proofs share no coefficients, because
`(u, v)` is only determined up to multiples of `(b, -a)`.  Useful for heading off the assumption
that a Lean proof has one right answer.
-/
