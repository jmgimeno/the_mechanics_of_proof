/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int

example : Odd (7 : ℤ) := by
  -- dsimp [Odd]
  use 3
  numbers

example : Odd (-3 : ℤ) := by
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  -- dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  obtain ⟨k,hk⟩ := hn
  have res := calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring
  use 7 * k + 1
  apply res

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, hx⟩ := hx
  obtain ⟨b, hy⟩ := hy
  have res := calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * y := by rw [hx, hy]
    _ = 2 * (2 * a * b + a + b + y) + 1 := by ring
  use 2 * a * b + a + b + y
  apply res

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨a, ha⟩ := hm
  have res := calc
    3 * m - 5 = 3 * (2 * a + 1) - 5 := by rw [ha]
    _ = 2 * (3 * a - 1) := by ring
  use 3 * a - 1
  apply res

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hk⟩ := hn
  have res := calc
    n ^ 2 + 2 * n - 5 = (2 * k) ^ 2 + 2 * (2 * k) - 5 := by rw [hk]
    _ = 2 * (2 * k ^ 2 + 2 * k - 3) + 1 := by ring
  use 2 * k ^ 2 + 2 * k - 3
  apply res

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/

example : Odd (-9 : ℤ) := by
  use -5
  numbers

example : Even (26 : ℤ) := by
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  have res := calc
    n + m = (2 * b) + (2 * a + 1) := by rw [hb, ha]
    _ = 2 * (a + b) + 1 := by ring
  use a + b
  apply res

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  have res := calc
    p - q - 4 = (2 * a + 1) - (2 * b) - 4 := by rw [ha, hb]
    _ = 2 * (a - b - 2) + 1 := by ring
  use a - b - 2
  apply res

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨l, hl⟩ := hb
  have res := calc
    3 * a + b - 3 = 3 * (2 * k) + (2 * l + 1) - 3 := by rw [hk, hl]
    _ = 2 * (3 * k + l - 1) := by ring
  use 3 * k + l - 1
  apply res

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hs
  have res := calc
    3 * r - 5 * s = 3 * (2 * a + 1) - 5 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (3 * a - 5 * b - 1) := by ring
  use 3 * a - 5 * b - 1
  apply res

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨a, ha⟩ := hx
  have res := calc
    x ^ 3 = (2 * a + 1) ^ 3 := by rw [ha]
    _ = 2 * (4 * a ^ 3 + 6 * a ^ 2 + 3 * a) + 1 := by ring
  use 4 * a ^ 3 + 6 * a ^ 2 + 3 * a
  apply res

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨k, hk⟩ := hn
  have res := calc
    n ^ 2 - 3 * n + 2 = (2 * k + 1) ^ 2 - 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (2 * k ^ 2 - k) := by ring
  use 2 * k ^ 2 - k
  apply res

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨k, hk⟩ := ha
  have res := calc
    a ^ 2 + 2 * a - 4 = (2 * k + 1) ^ 2 + 2 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (2 * k ^ 2 + 4 * k - 1) + 1 := by ring
  use 2 * k ^ 2 + 4 * k - 1
  apply res

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨k, hk⟩ := hp
  have res := calc
    p ^ 2 + 3 * p - 5 = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 5 := by rw [hk]
    _ = 2 * (2 * k ^ 2 + 5 * k - 1) + 1 := by ring
  use 2 * k ^ 2 + 5 * k - 1
  apply res

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  have res := calc
    x * y = (2 * k + 1) * (2 * l + 1) := by rw [hk, hl]
    _ = 2 * (2 * k * l + k + l) + 1 := by ring
  use 2 * k * l + k + l
  apply res

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain hn | hn := even_or_odd n
  · obtain ⟨k, hk⟩ := hn
    have res := calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (2 * k) ^ 2 + 3 * (2 * k) - 1 := by rw [hk]
      _ = 2 * (6 * k ^ 2 + 3 * k - 1) + 1 := by ring
    use 6 * k ^ 2 + 3 * k - 1
    use res
  · obtain ⟨k, hk⟩ := hn
    have res := calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 1 := by rw [hk]
      _ = 2 * (6 * k ^ 2 + 9 * k + 2) + 1 := by ring
    use 6 * k ^ 2 + 9 * k + 2
    use res

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain hn | hn := even_or_odd n
  · obtain ⟨k, hk⟩ := hn
    use n + 1
    constructor
    · extra
    · use k
      rw [hk]
  . obtain ⟨k, hk⟩ := hn
    use n
    constructor
    · extra
    · use k
      rw [hk]

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain aEven | aOdd := even_or_odd a
  · obtain ⟨k, hk⟩ := aEven
    obtain bEven | bOdd := even_or_odd b
    · obtain ⟨l, hl⟩ := bEven
      left
      use k - l
      rw [hk, hl]
      ring
    · obtain ⟨l, hl⟩ := bOdd
      obtain cEven | cOdd := even_or_odd c
      · obtain ⟨m, hm⟩ := cEven
        right
        left
        use k + m
        rw [hk, hm]
        ring
      · obtain ⟨m, hm⟩ := cOdd
        right
        right
        use l - m
        rw [hl, hm]
        ring
  · obtain ⟨k, hk⟩ := aOdd
    obtain bEven | bOdd := even_or_odd b
    · obtain ⟨l, hl⟩ := bEven
      obtain cEven | cOdd := even_or_odd c
      · obtain ⟨m, hm⟩ := cEven
        right
        right
        use l - m
        rw [hl, hm]
        ring
      · obtain ⟨m, hm⟩ := cOdd
        right
        left
        use k + m + 1
        rw [hk, hm]
        ring
    · obtain ⟨l, hl⟩ := bOdd
      left
      use k - l
      rw [hk, hl]
      ring

-- Branching on the differences in the goal (by opus 5.5)
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain h1 | ⟨k, hk⟩ := even_or_odd (a - b)
  · left
    apply h1
  · obtain h2 | ⟨l, hl⟩ := even_or_odd (b - c)
    · right
      right
      apply h2
    · right
      left
      use k + l + c + 1
      calc
        a + c = (a - b) + (b - c) + 2 * c := by ring
        _ = (2 * k + 1) + (2 * l + 1) + 2 * c := by rw [hk, hl]
        _ = 2 * (k + l + c + 1) := by ring

-- You do not need to fully nest the branches (some people prefer it)
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain h1 | ⟨k, hk⟩ := even_or_odd (a - b)
  · left
    apply h1
  obtain h2 | ⟨l, hl⟩ := even_or_odd (b - c)
  · right
    right
    apply h2
  right
  left
  use k + l + c + 1
  calc
    a + c = (a - b) + (b - c) + 2 * c := by ring
    _ = (2 * k + 1) + (2 * l + 1) + 2 * c := by rw [hk, hl]
    _ = 2 * (k + l + c + 1) := by ring
