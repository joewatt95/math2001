/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init


/- Note.  Every proof in this section runs on one fact.  When `a` and `b` are coprime there are
integers `u` and `v` with

    u * a + v * b = 1

This is Bezout's identity, and the extended Euclidean algorithm is how you find `u` and `v`.  For
the small numbers here, trial and a little arithmetic is quicker.

Once you have the pair, the proof writes itself.  To get `8 ∣ n` from `8 ∣ 5 * n`, find `u` and
`v` with `u * 5 + v * 8 = 1`, so that

    n = 1 * n = u * (5 * n) + v * 8 * n

The first summand is a multiple of `8` because of the hypothesis, the second because of the `8`
sitting in it, and `ring` collects them.  The whole content of each proof is the opening `ring`
step, which is where the Bezout coefficients appear.

For the two-hypothesis exercises the shape is the same, with `u * a + v * b = 1` for the two
divisors and `n` split as `u * a * n + v * b * n`.

There is more than one valid pair, since `(u, v)` can be shifted by multiples of `(b, -a)`.  The
first two examples below prove the same statement using different pairs, and both are correct. -/


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha : 5 * n = 8 * a⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha : 5 * n = 8 * a⟩ := hn
  use 5 * a - 3 * n
  calc
    n = 5 * (5 * n) - 24 * n := by ring
    _ = 5 * (8 * a) - 24 * n := by rw [ha]
    _ = 8 * (5 * a - 3 * n) := by ring

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨a, ha : 3 * n = 5 * a⟩ := h1
  use 2 * a - n
  calc
    n = 2 * (3 * n) - 5 * n := by ring
    _ = 2 * (5 * a) - 5 * n := by rw [ha]
    _ = 5 * (2 * a - n) := by ring

/- Note.  The two rewrites below cannot be merged into `rw [ha, hb]`, and it is worth knowing why,
because the natural instinct is to try.

Both hypotheses are about `m`, and `rw` replaces every occurrence of its pattern at once.  So
`rw [ha]` turns both copies of `m` into `8 * a`, after which `hb` has nothing left to match and
the step fails with

    Did not find an occurrence of the pattern
      m

Keeping them in separate steps is what leaves one copy of `m` alive for the second rewrite.  The
general rule is that `rw [h1, h2]` is fine when the two hypotheses are about different terms, as
in the parity proofs of Section 3.1, and has to be split when they are about the same one. -/

example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha : m = 8 * a⟩ := h1
  obtain ⟨b, hb : m = 5 * b⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨a, ha : 11 * n = 6 * a⟩ := hn
  use -a + 2 * n
  calc
    n = -(11 * n) + 12 * n := by ring
    _ = -(6 * a) + 12 * n := by rw [ha]
    _ = 6 * (-a + 2 * n) := by ring

/- Note.  `a` is the variable here, so the witness needs a different name. -/

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨b, hb : 5 * a = 7 * b⟩ := ha
  use 3 * b - 2 * a
  calc
    a = 3 * (5 * a) - 14 * a := by ring
    _ = 3 * (7 * b) - 14 * a := by rw [hb]
    _ = 7 * (3 * b - 2 * a) := by ring

/- Note.  Here `4 * 7 - 3 * 9 = 1`, so `n = 28 * n - 27 * n`.  The first term becomes a multiple
of `63` using `9 ∣ n`, the second using `7 ∣ n`, and they carry the `7` and `9` that the `28` and
`27` are missing.

Note that `63 = 7 * 9` matters.  Coprimality is what makes this work, and `7 ∣ n` together with
`9 ∣ n` would not give `63 ∣ n` if the two divisors shared a factor. -/

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨a, ha : n = 7 * a⟩ := h1
  obtain ⟨b, hb : n = 9 * b⟩ := h2
  use 4 * b - 3 * a
  calc
    n = 28 * n - 27 * n := by ring
    _ = 28 * (9 * b) - 27 * n := by rw [hb]
    _ = 28 * (9 * b) - 27 * (7 * a) := by rw [ha]
    _ = 63 * (4 * b - 3 * a) := by ring

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨a, ha : n = 5 * a⟩ := h1
  obtain ⟨b, hb : n = 13 * b⟩ := h2
  use 8 * b - 3 * a
  calc
    n = 40 * n - 39 * n := by ring
    _ = 40 * (13 * b) - 39 * n := by rw [hb]
    _ = 40 * (13 * b) - 39 * (5 * a) := by rw [ha]
    _ = 65 * (8 * b - 3 * a) := by ring
