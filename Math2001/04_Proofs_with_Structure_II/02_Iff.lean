/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers

example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring

theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    -- dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    dsimp [Int.ModEq] at h
    obtain ⟨k, hk⟩ := h
    -- dsimp [Odd]
    use k
    addarith [hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    -- dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    dsimp [Int.ModEq] at h
    obtain ⟨k, hk⟩ := h
    -- dsimp [Even]
    use k
    addarith [hk]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have H := calc
      (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
      _ = 0 := h
    obtain hx | hx := eq_zero_or_eq_zero_of_mul_eq_zero H
    · left
      addarith [hx]
    · right
      addarith [hx]
  · intro h
    obtain hx | hx := h
    · rw [hx]
      numbers
    · rw [hx]
      numbers

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    have H:= calc
      (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 * -1 + 5 := by rel [h]
      _ = 1 ^ 2 := by numbers
    obtain ⟨ha1, ha2⟩ := abs_le_of_sq_le_sq' H (by numbers)
    have H2 := calc
      2 * 2 = -1 + 5 := by numbers
      _ ≤ 2 * a - 5 + 5 := by rel [ha1]
      _ = 2 * a := by ring
    have H3 : 2 ≤ a := by cancel 2 at H2
    have H4 := calc
      2 * 3 = 1 + 5 := by numbers
      _ ≥ 2 * a - 5 + 5 := by rel [ha2]
      _ = 2 * a := by ring
    have H5 : a ≤ 3 := by cancel 2 at H4
    interval_cases a
    · left
      numbers
    · right
      numbers
  · intro h
    obtain ha | ha := h <;> rw [ha] <;> numbers

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    have H:= calc
      (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 * -1 + 5 := by rel [h]
      _ = 1 ^ 2 := by numbers
    obtain ⟨ha1, ha2⟩ := abs_le_of_sq_le_sq' H (by numbers)
    have H2 := calc
      2 * 2 = -1 + 5 := by numbers
      _ ≤ 2 * a - 5 + 5 := by rel [ha1]
      _ = 2 * a := by ring
    have H3 : 2 ≤ a := by cancel 2 at H2
    have H4 := calc
      2 * 3 = 1 + 5 := by numbers
      _ ≥ 2 * a - 5 + 5 := by rel [ha2]
      _ = 2 * a := by ring
    have H5 : a ≤ 3 := by cancel 2 at H4
    obtain ha3 | ha4 := le_or_succ_le a 2
    · left
      apply le_antisymm ha3 H3
    · right
      apply le_antisymm H5 ha4
  · intro h
    obtain ha | ha := h <;> rw [ha] <;> numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain hn | hn := hn2
  · have hn' : n = 4 := by addarith [hn]
    rw [hn']
    use 2
    numbers
  · have hn' : n = 6 := by addarith [hn]
    rw [hn']
    use 3
    numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain hn | hn := hn1
  · have hn' : n = 4 := by addarith [hn]
    rw [hn']
    use 2
    numbers
  · have hn' : n = 6 := by addarith [hn]
    rw [hn']
    use 3
    numbers

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra

example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/

example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    calc
      x = (2 * x - 1) / 2 + 1 / 2:= by ring
      _ = 11 / 2 + 1 / 2 := by rw [h]
      _ = 6 := by numbers
  · intro hx
    rw [hx]
    numbers

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    constructor
    · use 9 * k
      rw [hk]
      ring
    · use 7 * k
      rw [hk]
      ring
  · intro h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    have H := calc
      n = (7 * 4) * n - (9 * 3) * n := by ring
      _ = (7 * 4) * (9 * b) - (9 * 3) * n := by rw [hb]
      _ = (7 * 4) * (9 * b) - (9 * 3) * (7 * a) := by rw [ha]
      _ = 63 * (4 * b - 3 * a) := by ring
    use 4 * b - 3 * a
    exact H

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor <;> intro h <;> obtain ⟨k, hk⟩ := h <;> use k <;> addarith [hk]

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk⟩ := hab
  have H := calc
    2 * b ^ 3 - b ^ 2 + 3 * b = 2 * (a * k) ^ 3 - (a * k) ^ 2 + 3 * (a * k) := by rw [hk]
    _ = a * (2 * a ^ 2 * k ^ 3 - a * k ^ 2 + 3 * k) := by ring
  use 2 * a ^ 2 * k ^ 3 - a * k ^ 2 + 3 * k
  exact H

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    have h1 : k ≤ 2 := by
      obtain hk | hk := le_or_succ_le k 2
      · exact hk
      · have H := calc
          k ^ 2 ≥ 3 ^ 2 := by rel [hk]
          _ > 6 := by numbers
        have H2 : 6 < 6 := lt_of_lt_of_le H h
        numbers at H2
    interval_cases k
    · left
      rfl
    · right
      left
      rfl
    · right
      right
      rfl
  · intro h
    obtain hk | hk | hk := h <;> rw [hk] <;> numbers

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    have h' : k ^ 2 < 3 ^ 2 := by addarith [h]
    cancel 2 at h'
    interval_cases k <;> norm_num
  · intro h
    obtain hk | hk | hk := h <;> rw [hk] <;> numbers
