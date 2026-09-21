/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Tactic.ModEq

math2001_init

/- Proofs marked `-- Book` are Macbeth's, either unchanged or with annotations added.  The rest
are written for this course. -/


/- Note.  Section 3.3 proved a handful of lemmas about congruences, unfolding the definition every
time.  This section is the payoff.  `rel` now understands `≡ [ZMOD n]`, so a congruence can be
substituted into an expression exactly as an inequality was in Section 1.4, and the definition
never has to surface again.  The first example below is the one that took twelve `apply` lines at
the end of Section 3.3.

Two idioms do most of the work.

`rel [h]` replaces a subterm using the congruence `h`.

Reducing a number modulo `n` is done in two steps: write it as `c + n * k` with `numbers`, then
drop the multiple of `n` with `extra`.  That is what the `_ = 2 + 5 * 8` and `_ ≡ 2 [ZMOD 5]`
lines below are doing, and the pattern recurs in every exercise. -/


-- Book.
example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  rel [ha]


-- Book.
example {a b : ℤ} (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 2 [ZMOD 5] :=
  calc
    a * b + b ^ 3 + 3 ≡ 4 * b + b ^ 3 + 3 [ZMOD 5] := by rel [ha]
    _ ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by rel [hb]
    _ = 2 + 5 * 8 := by numbers
    _ ≡ 2 [ZMOD 5] := by extra


-- Book.
example : ∃ a : ℤ, 6 * a ≡ 4 [ZMOD 11] := by
  use 8
  calc
    (6:ℤ) * 8 = 4 + 4 * 11 := by numbers
    _ ≡ 4 [ZMOD 11] := by extra


/- Note.  `mod_cases hx : x % 3` splits the proof into the cases `x ≡ 0`, `x ≡ 1` and `x ≡ 2`
modulo `3`.  It is the congruence counterpart of `le_or_succ_le`, and it works for the same reason,
namely that every integer is congruent to exactly one of finitely many residues.

The number of branches is the modulus, so this is a tool for small moduli.  The last exercise in
this section needs five.

Both versions below are the same proof.  In the first, three `calc` blocks sit in a row with
nothing between them, since `mod_cases` leaves one goal per residue and does not bullet them for
you.

Each also opens by naming the residue it is about, as `have : x ≡ 0 [ZMOD 3] := hx`.  The
hypothesis is called `hx` in every branch and says something different in each, so with three
branches you can count, and with eleven you cannot.  This is the same case label used after
`obtain` in Section 2.3, and it costs one line to stop a reader counting bullets. -/

-- Book.
example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by
  mod_cases hx : x % 3
  calc
    x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 1 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 2 + 3 * 2 := by numbers
    _ ≡ 2 [ZMOD 3] := by extra
    _ ≡ x [ZMOD 3] := by rel [hx]

-- Restyled.
example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by
  mod_cases hx : x % 3

  · have : x ≡ 0 [ZMOD 3] := hx
    calc
      x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by rel [hx]
      _ = 0 := by numbers
      _ ≡ x [ZMOD 3] := by rel [hx]

  · have : x ≡ 1 [ZMOD 3] := hx
    calc
      x ^ 3 ≡ 1 ^ 3 [ZMOD 3] := by rel [hx]
      _ = 1 := by numbers
      _ ≡ x [ZMOD 3] := by rel [hx]

  · have : x ≡ 2 [ZMOD 3] := hx
    calc
      x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by rel [hx]
      _ = 2 + 3 * 2 := by numbers
      _ ≡ 2 [ZMOD 3] := by extra
      _ ≡ x [ZMOD 3] := by rel [hx]

/-! # Exercises -/


example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] :=
  calc
    n ^ 3 + 7 * n ≡ 1 ^ 3 + 7 * 1 [ZMOD 3] := by rel [hn]
    _ = 2 + 3 * 2 := by numbers
    _ ≡ 2 [ZMOD 3] := by extra

example {a : ℤ} (ha : a ≡ 3 [ZMOD 4]) :
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 1 [ZMOD 4] :=
  calc
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 3 ^ 3 + 4 * 3 ^ 2 + 2 [ZMOD 4] := by rel [ha]
    _ = 1 + 4 * 16 := by numbers
    _ ≡ 1 [ZMOD 4] := by extra

/- Note.  Expanding `(a + b) ^ 3` gives two cross terms, `3 * a ^ 2 * b` and `3 * a * b ^ 2`, and
both carry a factor of `3`.  So no hypothesis is needed here.  The congruence holds for every `a`
and `b`, and `ring` followed by `extra` is the whole proof.

The same happens modulo any prime `p`, since `p` divides every binomial coefficient strictly
between the two ends.  It is sometimes called the freshman's dream, being what a first-year
algebra student wishes were true over ℤ. -/

example (a b : ℤ) : (a + b) ^ 3 ≡ a ^ 3 + b ^ 3 [ZMOD 3] :=
  calc
    (a + b) ^ 3 = a ^ 3 + b ^ 3 + 3 * (a ^ 2 * b + a * b ^ 2) := by ring
    _ ≡ a ^ 3 + b ^ 3 [ZMOD 3] := by extra

/- Note.  These two ask for a modular inverse, or something close to one.  There is an algorithm
for finding them, the extended Euclidean algorithm, which is the subject of Section 3.5.  For
moduli this small, running through `a = 0, 1, 2, ...` until `4 * a` lands one more than a multiple
of `7` is quicker. -/

example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] := by
  use 2
  calc
    4 * 2 = 1 + 7 * 1 := by numbers
    _ ≡ 1 [ZMOD 7] := by extra

example : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
  use 6
  calc
    5 * 6 = 6 + 8 * 3 := by numbers
    _ ≡ 6 [ZMOD 8] := by extra

example (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  mod_cases hn : n % 2

  · have : n ≡ 0 [ZMOD 2] := hn
    calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 0 ^ 2 + 3 * 0 + 7 [ZMOD 2] := by rel [hn]
      _ = 1 + 2 * 3 := by numbers
      _ ≡ 1 [ZMOD 2] := by extra

  · have : n ≡ 1 [ZMOD 2] := hn
    calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 1 ^ 2 + 3 * 1 + 7 [ZMOD 2] := by rel [hn]
      _ = 1 + 2 * 7 := by numbers
      _ ≡ 1 [ZMOD 2] := by extra

/- Note.  Five residues, so five branches, each the same three or four lines.  This is Fermat's
little theorem for `p = 5`, which says `x ^ p ≡ x [ZMOD p]` for every prime `p`.  Checking it case
by case works because `5` is small.  A proof for general `p` needs induction and a good deal
more. -/

example {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases hx : x % 5

  · have : x ≡ 0 [ZMOD 5] := hx
    calc
      x ^ 5 ≡ 0 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 0 := by numbers
      _ ≡ x [ZMOD 5] := by rel [hx]

  · have : x ≡ 1 [ZMOD 5] := hx
    calc
      x ^ 5 ≡ 1 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 1 := by numbers
      _ ≡ x [ZMOD 5] := by rel [hx]

  · have : x ≡ 2 [ZMOD 5] := hx
    calc
      x ^ 5 ≡ 2 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 2 + 5 * 6 := by numbers
      _ ≡ 2 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [hx]

  · have : x ≡ 3 [ZMOD 5] := hx
    calc
      x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 3 + 5 * 48 := by numbers
      _ ≡ 3 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [hx]

  ·
    calc
      x ^ 5 ≡ 4 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 4 + 5 * 204 := by numbers
      _ ≡ 4 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [hx]
