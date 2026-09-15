/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


/- Note.  `Int.Even` and `Int.Odd` are definitions rather than primitive notions, and each one is
an existential underneath:

    def Int.Even (n : ℤ) : Prop := ∃ k, n = 2 * k
    def Int.Odd  (n : ℤ) : Prop := ∃ k, n = 2 * k + 1

So `Int.Even n` is a `∃` wearing a disguise, and everything from Section 2.5 applies.  To prove
one, supply the witness with `use`.  To use one, take it apart with `obtain`.

This is where annotating an `obtain` stops being a nicety.  Written bare, `obtain ⟨k, hk⟩ := hn`
tells a reader nothing at all, because `Int.Odd n` does not say on its face that there is an
integer `k` with `n = 2 * k + 1`.  Written as

    obtain ⟨k, hk : n = 2 * k + 1⟩ := hn

the assumption you have just gained is on the page.  Do the same for the divisibility relation in
the next section, where `a ∣ b` hides its existential just as thoroughly.

You do not need to look anything up to write these.  For the basic predicates in this chapter the
definition unfolds to exactly what you would write on paper, so guess it and let Lean confirm.  If
you want to check, control-click (or F12) on `Int.Odd` to jump to the definition. -/


example : Int.Odd (7 : ℤ) := by
  dsimp [Int.Odd]
  use 3
  numbers


example : Int.Odd (-3 : ℤ) := by
  dsimp [Int.Odd]
  use -2
  numbers

example {n : ℤ} (hn : Int.Odd n) : Int.Odd (3 * n + 2) := by
  dsimp [Int.Odd] at *
  obtain ⟨k, hk : n = 2 * k + 1⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Int.Odd n) : Int.Odd (7 * n - 4) := by
  obtain ⟨k, hk : n = 2 * k + 1⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring

example {x y : ℤ} (hx : Int.Odd x) (hy : Int.Odd y) : Int.Odd (x + y + 1) := by
  obtain ⟨a, ha : x = 2 * a + 1⟩ := hx
  obtain ⟨b, hb : y = 2 * b + 1⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Int.Odd x) (hy : Int.Odd y) : Int.Odd (x * y + 2 * y) := by
  obtain ⟨a, ha : x = 2 * a + 1⟩ := hx
  obtain ⟨b, hb : y = 2 * b + 1⟩ := hy
  use 2 * a * b + a + 3 * b + 1
  calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + a + 3 * b + 1) + 1 := by ring

example {m : ℤ} (hm : Int.Odd m) : Int.Even (3 * m - 5) := by
  obtain ⟨k, hk : m = 2 * k + 1⟩ := hm
  use 3 * k - 1
  calc
    3 * m - 5 = 3 * (2 * k + 1) - 5 := by rw [hk]
    _ = 2 * (3 * k - 1) := by ring

example {n : ℤ} (hn : Int.Even n) : Int.Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hk : n = 2 * k⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  calc
    n ^ 2 + 2 * n - 5 = (2 * k) ^ 2 + 2 * (2 * k) - 5 := by rw [hk]
    _ = 2 * (2 * k ^ 2 + 2 * k - 3) + 1 := by ring

example (n : ℤ) : Int.Even (n ^ 2 + n + 4) := by
  obtain (hn : Int.Even n) | (hn : Int.Odd n) := Int.even_or_odd_lib n
  · obtain ⟨x, hx : n = 2 * x⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx : n = 2 * x + 1⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Int.Odd (-9 : ℤ) := by
  dsimp [Int.Odd]
  use -5
  numbers

example : Int.Even (26 : ℤ) := by
  dsimp [Int.Even]
  use 13
  numbers

example {m n : ℤ} (hm : Int.Odd m) (hn : Int.Even n) : Int.Odd (n + m) := by
  obtain ⟨a, ha : m = 2 * a + 1⟩ := hm
  obtain ⟨b, hb : n = 2 * b⟩ := hn
  use a + b
  calc
    n + m = 2 * b + (2 * a + 1) := by rw [ha, hb]
    _ = 2 * (a + b) + 1 := by ring

example {p q : ℤ} (hp : Int.Odd p) (hq : Int.Even q) : Int.Odd (p - q - 4) := by
  obtain ⟨a, ha : p = 2 * a + 1⟩ := hp
  obtain ⟨b, hb : q = 2 * b⟩ := hq
  use a - b - 2
  calc
    p - q - 4 = 2 * a + 1 - 2 * b - 4 := by rw [ha, hb]
    _ = 2 * (a - b - 2) + 1 := by ring

example {a b : ℤ} (ha : Int.Even a) (hb : Int.Odd b) : Int.Even (3 * a + b - 3) := by
  obtain ⟨x, hx : a = 2 * x⟩ := ha
  obtain ⟨y, hy : b = 2 * y + 1⟩ := hb
  use 3 * x + y - 1
  calc
    3 * a + b - 3 = 3 * (2 * x) + (2 * y + 1) - 3 := by rw [hx, hy]
    _ = 2 * (3 * x + y - 1) := by ring

example {r s : ℤ} (hr : Int.Odd r) (hs : Int.Odd s) : Int.Even (3 * r - 5 * s) := by
  obtain ⟨a, ha : r = 2 * a + 1⟩ := hr
  obtain ⟨b, hb : s = 2 * b + 1⟩ := hs
  use 3 * a - 5 * b - 1
  calc
    3 * r - 5 * s = 3 * (2 * a + 1) - 5 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (3 * a - 5 * b - 1) := by ring

example {x : ℤ} (hx : Int.Odd x) : Int.Odd (x ^ 3) := by
  obtain ⟨k, hk : x = 2 * k + 1⟩ := hx
  use 4 * k ^ 3 + 6 * k ^ 2 + 3 * k
  calc
    x ^ 3 = (2 * k + 1) ^ 3 := by rw [hk]
    _ = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by ring

example {n : ℤ} (hn : Int.Odd n) : Int.Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨k, hk : n = 2 * k + 1⟩ := hn
  use 2 * k ^ 2 - k
  calc
    n ^ 2 - 3 * n + 2 = (2 * k + 1) ^ 2 - 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (2 * k ^ 2 - k) := by ring

example {a : ℤ} (ha : Int.Odd a) : Int.Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨k, hk : a = 2 * k + 1⟩ := ha
  use 2 * k ^ 2 + 4 * k - 1
  calc
    a ^ 2 + 2 * a - 4 = (2 * k + 1) ^ 2 + 2 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (2 * k ^ 2 + 4 * k - 1) + 1 := by ring

example {p : ℤ} (hp : Int.Odd p) : Int.Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨k, hk : p = 2 * k + 1⟩ := hp
  use 2 * k ^ 2 + 5 * k - 1
  calc
    p ^ 2 + 3 * p - 5 = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 5 := by rw [hk]
    _ = 2 * (2 * k ^ 2 + 5 * k - 1) + 1 := by ring

example {x y : ℤ} (hx : Int.Odd x) (hy : Int.Odd y) : Int.Odd (x * y) := by
  obtain ⟨a, ha : x = 2 * a + 1⟩ := hx
  obtain ⟨b, hb : y = 2 * b + 1⟩ := hy
  use 2 * a * b + a + b
  calc
    x * y = (2 * a + 1) * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + a + b) + 1 := by ring

example (n : ℤ) : Int.Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain (hn : Int.Even n) | (hn : Int.Odd n) := Int.even_or_odd_lib n

  · obtain ⟨k, hk : n = 2 * k⟩ := hn
    use 6 * k ^ 2 + 3 * k - 1
    calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (2 * k) ^ 2 + 3 * (2 * k) - 1 := by rw [hk]
      _ = 2 * (6 * k ^ 2 + 3 * k - 1) + 1 := by ring

  · obtain ⟨k, hk : n = 2 * k + 1⟩ := hn
    use 6 * k ^ 2 + 9 * k + 2
    calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 1 := by rw [hk]
      _ = 2 * (6 * k ^ 2 + 9 * k + 2) + 1 := by ring

/- Note.  `∃ m ≥ n, Int.Odd m` is shorthand for `∃ m, m ≥ n ∧ Int.Odd m`, so after `use` the goal
is a conjunction and `constructor` splits it.

There is no single witness that works for every `n`, so split on the parity of `n` first and let
each case choose its own.  If `n` is already odd, take `n` itself.  If not, take `n + 1`.  Picking
the witness after the case split, rather than before, is the same move as the cubic exercise at
the end of Section 2.5. -/

example (n : ℤ) : ∃ m ≥ n, Int.Odd m := by
  obtain (hn : Int.Even n) | (hn : Int.Odd n) := Int.even_or_odd_lib n

  · obtain ⟨k, hk : n = 2 * k⟩ := hn
    use n + 1
    constructor
    · show n + 1 ≥ n
      extra
    · show Int.Odd (n + 1)
      use k
      rw [hk]

  · use n
    constructor
    · show n ≥ n
      extra
    · show Int.Odd n
      apply hn
/- Note.  On paper this is the pigeonhole principle.  Three integers, two parities, so some two of
them share a parity, and whichever pair it is gives you one of the three disjuncts.

Lean has no way to say "some two of them" directly, so the argument becomes a case analysis.
Split on `a`, then on `b`, and only split on `c` in the two cases where `a` and `b` already
disagree.  That gives six leaves rather than eight.

Long, but every leaf is the same three lines: name the two witnesses, pick the disjunct with
`left` or `right`, and finish with `use` and `ring`.  The `show` lines are what stop the six from
blurring together. -/

example (a b c : ℤ) : Int.Even (a - b) ∨ Int.Even (a + c) ∨ Int.Even (b - c) := by
  obtain (ha : Int.Even a) | (ha : Int.Odd a) := Int.even_or_odd_lib a

  · obtain (hb : Int.Even b) | (hb : Int.Odd b) := Int.even_or_odd_lib b

    · obtain ⟨x, hx : a = 2 * x⟩ := ha
      obtain ⟨y, hy : b = 2 * y⟩ := hb
      left
      show Int.Even (a - b)
      use x - y
      calc
        a - b = 2 * x - 2 * y := by rw [hx, hy]
        _ = 2 * (x - y) := by ring

    · obtain (hc : Int.Even c) | (hc : Int.Odd c) := Int.even_or_odd_lib c

      · obtain ⟨x, hx : a = 2 * x⟩ := ha
        obtain ⟨z, hz : c = 2 * z⟩ := hc
        right
        left
        show Int.Even (a + c)
        use x + z
        calc
          a + c = 2 * x + 2 * z := by rw [hx, hz]
          _ = 2 * (x + z) := by ring

      · obtain ⟨y, hy : b = 2 * y + 1⟩ := hb
        obtain ⟨z, hz : c = 2 * z + 1⟩ := hc
        right
        right
        show Int.Even (b - c)
        use y - z
        calc
          b - c = 2 * y + 1 - (2 * z + 1) := by rw [hy, hz]
          _ = 2 * (y - z) := by ring

  · obtain (hb : Int.Even b) | (hb : Int.Odd b) := Int.even_or_odd_lib b

    · obtain (hc : Int.Even c) | (hc : Int.Odd c) := Int.even_or_odd_lib c

      · obtain ⟨y, hy : b = 2 * y⟩ := hb
        obtain ⟨z, hz : c = 2 * z⟩ := hc
        right
        right
        show Int.Even (b - c)
        use y - z
        calc
          b - c = 2 * y - 2 * z := by rw [hy, hz]
          _ = 2 * (y - z) := by ring

      · obtain ⟨x, hx : a = 2 * x + 1⟩ := ha
        obtain ⟨z, hz : c = 2 * z + 1⟩ := hc
        right
        left
        show Int.Even (a + c)
        use x + z + 1
        calc
          a + c = 2 * x + 1 + (2 * z + 1) := by rw [hx, hz]
          _ = 2 * (x + z + 1) := by ring

    · obtain ⟨x, hx : a = 2 * x + 1⟩ := ha
      obtain ⟨y, hy : b = 2 * y + 1⟩ := hb
      left
      show Int.Even (a - b)
      use x - y
      calc
        a - b = 2 * x + 1 - (2 * y + 1) := by rw [hx, hy]
        _ = 2 * (x - y) := by ring
