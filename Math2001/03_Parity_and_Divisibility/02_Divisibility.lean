/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init


/- Note.  `a ∣ b` is the same kind of disguise as `Int.Even` in Section 3.1.  Underneath it is

    a ∣ b   means   ∃ c, b = a * c

so `use` proves one and `obtain` takes one apart, exactly as in Section 2.5.  Note that the bar
is a symbol of its own and not the keyboard `|`.  Hovering over it in VS Code shows how to type
it, which works for any symbol you meet.

Annotating matters here even more than for parity, because `a ∣ b` gives no hint that a second
number is involved at all.  `obtain ⟨k, hk : b = a * k⟩ := hab` puts the witness and its equation
on the page.

The shape of nearly every proof below is the same.  Take the divisibility you were given, so that
`b = a * k`.  Substitute it into the expression you care about.  Factor out `a` with `ring`, and
whatever is left over is the witness to hand to `use`.  Finding that witness is a matter of doing
the algebra on paper first and reading it off. -/


example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  dsimp [(· ∣ ·)]
  use -3
  numbers

example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk : b = a * k⟩ := hab
  use k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring


example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  obtain ⟨k, hk : b = a * k⟩ := hab
  obtain ⟨m, hm : c = b ^ 2 * m⟩ := hbc
  use k ^ 2 * m
  calc
    c = b ^ 2 * m := hm
    _ = (a * k) ^ 2 * m := by rw [hk]
    _ = a ^ 2 * (k ^ 2 * m) := by ring

example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  obtain ⟨k, hk : z = x * y * k⟩ := h
  use y * k
  calc
    z = x * y * k := hk
    _ = x * (y * k) := by ring

example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers -- show `5 * 2 < 12`
  · numbers -- show `12 < 5 * (2 + 1)`


example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk : b = a * k⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]


/- Note.  The example above cancels `a` from `0 < a * k` to get `0 < k`.  This one wants the other
factor, and `cancel k at H` obliges.  `cancel` will remove whichever factor you name, provided it
can see that the one left behind has the sign the conclusion needs. -/

example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨k, hk : b = a * k⟩ := hab
  have : 0 < a * k :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel k at this

/-! # Exercises -/


example (t : ℤ) : t ∣ 0 := by
  use 0
  ring

example : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  · show 3 * -4 < -10
    numbers
  · show -10 < 3 * (-4 + 1)
    numbers

example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨k, hk : y = x * k⟩ := h
  use 3 * k - 4 * x * k ^ 2
  calc
    3 * y - 4 * y ^ 2 = 3 * (x * k) - 4 * (x * k) ^ 2 := by rw [hk]
    _ = x * (3 * k - 4 * x * k ^ 2) := by ring

example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨k, hk : n = m * k⟩ := h
  use 2 * m ^ 2 * k ^ 3 + k
  calc
    2 * n ^ 3 + n = 2 * (m * k) ^ 3 + m * k := by rw [hk]
    _ = m * (2 * m ^ 2 * k ^ 3 + k) := by ring

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk : b = a * k⟩ := hab
  use 2 * a ^ 2 * k ^ 3 - a * k ^ 2 + 3 * k
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b = 2 * (a * k) ^ 3 - (a * k) ^ 2 + 3 * (a * k) := by rw [hk]
    _ = a * (2 * a ^ 2 * k ^ 3 - a * k ^ 2 + 3 * k) := by ring

/- Note.  `k`, `l` and `m` are taken, so the witnesses need other names.  Worth a moment's care:
reusing a bound name here would shadow one of the variables the statement is about. -/

example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨a, ha : l = k * a⟩ := h1
  obtain ⟨b, hb : m = l ^ 3 * b⟩ := h2
  use a ^ 3 * b
  calc
    m = l ^ 3 * b := hb
    _ = (k * a) ^ 3 * b := by rw [ha]
    _ = k ^ 3 * (a ^ 3 * b) := by ring

example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨a, ha : q = p ^ 3 * a⟩ := hpq
  obtain ⟨b, hb : r = q ^ 2 * b⟩ := hqr
  use a ^ 2 * b
  calc
    r = q ^ 2 * b := hb
    _ = (p ^ 3 * a) ^ 2 * b := by rw [ha]
    _ = p ^ 6 * (a ^ 2 * b) := by ring

/- Note.  Two existentials, one inside the other.  The outer `use 6` fixes `n`, and the inner
`use 7` is the witness for `9 ∣ 63`.  Nothing here tells you that `6` works.  You find it by
trying `n = 1, 2, 3, ...` until `2 ^ n - 1` lands on a multiple of `9`. -/

example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  use 6
  constructor
  · show 0 < 6
    numbers
  · show 9 ∣ 2 ^ 6 - 1
    use 7
    numbers

/- Note.  Three conjuncts, so `constructor` would nest two deep before reaching the last of them.
Proving each part separately and assembling with `⟨...⟩` keeps the proof flat, and the nesting
that remains is the nesting the argument actually calls for.  `constructor` imposes a layer per
conjunct whether or not the content deserves one.

`exact ⟨h1, h2, h3⟩` is the reverse of the `obtain ⟨h1, h2⟩ := h` of Section 2.4.  There the brackets
took a conjunction apart, here they build one out of the pieces you list, in order.  It last
appeared at the end of Section 2.5.

Note the order.  `use 3, 1` comes first, so the reader knows which numbers are being offered
before meeting the three facts about them.  Put the `have` lines first and they arrive with
nothing to attach to, leaving the reader to guess what they are for. -/

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  use 3, 1
  have h1 : (0:ℤ) < 1 := by numbers
  have h2 : (1:ℤ) < 3 := by numbers
  have h3 : (3:ℤ) - 1 ∣ 3 + 1 := by
    use 2
    numbers
  exact ⟨h1, h2, h3⟩
