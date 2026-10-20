/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int

example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this

example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h := calc
      13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h := calc
      13 = 3 * k := hk
      _ ≥ 3 * 5 := by rel [h5]
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H

example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  rintro ⟨n, hn⟩
  obtain h1 | h2 := le_or_succ_le n 1
  · have := calc
      2 = n ^ 2 := by rw [hn]
      _ ≤ 1 ^ 2 := by rel [h1]
      _ = 1 := by numbers
    numbers at this
  · have := calc
      2 = n ^ 2 := by rw [hn]
      _ ≥ 2 ^ 2 := by rel [h2]
      _ = 4 := by numbers
    numbers at this

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction

example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have := calc
      1 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 0 [ZMOD 2] := by rel [h2]
    numbers at this
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have := calc
      0 = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at this
  · have := calc
      1 = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at this
  · have := calc
      1 ≡ 1 + 3 * 1 [ZMOD 3] := by extra
      _ = 2 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at this

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) : ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  rintro ⟨h2, hfact⟩
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction

example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  rintro ⟨k, hk⟩
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb : 0 < b := calc
    0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 : b * k < b * (q + 1) := calc
    b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1 -- k < q + 1
  have h2 : b * q < b * k := calc
    b * q < a := hq₁
    _ = b * k := by rw [hk]
  cancel b at h2 -- q < k
  addarith [h1, h2]

example {p : ℕ} (hp : 2 ≤ p) (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  · rintro ⟨l, hl⟩
    have : l ∣ p
    · use m
      rw [hl]
      ring
    have hl1 := calc
        m * 1 = m := by ring
        _ < p := hmp
        _ = m * l := hl
    cancel m at hl1 -- 1 < l
    have hl2 := calc
      T * l ≤ m * l := by rel [hmT]
      _ = p := by rw [hl]
      _ < T ^ 2 := by rel [hTp]
      _ = T * T := by ring
    cancel T at hl2 -- l < T
    have : ¬ l ∣ p := H l hl1 hl2
    contradiction

example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  · intro m hm1 hm2
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 39
      constructor <;> numbers
    · use 26
      constructor <;> numbers
    · use 19
      constructor <;> numbers
    · use 15
      constructor <;> numbers
    · use 13
      constructor <;> numbers
    · use 11
      constructor <;> numbers
    · use 9
      constructor <;> numbers

example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  · intro m hm1 hm2
    apply Nat.not_dvd_of_exists_lt_and_lt
    use Nat.div 79 m -- we solve by the integer division of 79 by n before casing
    interval_cases m <;> constructor <;> numbers

/-! # Exercises -/

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  rintro ⟨t, h1, h2⟩
  addarith [h1, h2]

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  rintro ⟨a, h1, h2⟩
  have h3 := calc
    a ^ 2 ≤ 8 := h1
    _ < 3 ^ 2 := by numbers
  cancel 2 at h3
  have ha2pos : a ^ 2 > 0 := by
    obtain ha2 | ha2 := le_or_gt (a ^ 2) 0
    · have ha0 := by
        have ha2' : a ^ 2 ≥ 0 := by extra
        apply le_antisymm ha2 ha2'
      cancel 2 at ha0
      have ha'' := calc
        a ^ 3 = 0 ^ 3 := by rw [ha0]
        _ < 30 := by numbers
      addarith [h2, ha'']
    · exact ha2
  have h5 := calc
    a ^ 3 = (a ^ 2) * a := by ring
    _ < (a ^ 2) * 3 := by rel [h3]
    _ ≤ 8 * 3 := by rel [h1]
    _ = 24 := by numbers
  addarith [h2, h5]

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  rintro ⟨a, h1, h2⟩
  have h3 : a < 3 := by
    have : a ^ 2 < 3 ^ 2 := by addarith [h1]
    cancel 2 at this
  have h4 : a ^ 3 < 30 := calc
    a ^ 3 = a ^ 2 * a := by ring
    _ ≤ a ^ 2 * 3 := by rel [h3]
    _ ≤ 8 * 3 := by rel [h1]
    _ < 30 := by numbers
  addarith [h2, h4]

example : ¬ Int.Even 7 := by
  apply not_dvd_of_exists_lt_and_lt
  use 3
  constructor <;> numbers

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  rintro ⟨h1, h2⟩
  have h3 : n = 4 := by addarith [hn]
  rw [h3] at h2
  numbers at h2

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  rintro (hx3 | hx3)
  · have hx3' : (-x) ≥ 3 := by addarith [hx3]
    have := calc
      x ^ 2 = (-x) ^ 2 := by ring
      _ ≥ 3 ^ 2 := by rel [hx3']
      _ = 9 := by numbers
    addarith [hx, this]
  · have := calc
      x ^ 2 ≥ 3 ^ 2 := by rel [hx3]
      _ = 9 := by numbers
    addarith [hx, this]

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  have h : x ^ 2 < 3 ^ 2 := by addarith [hx]
  obtain ⟨h1, h2⟩ := abs_lt_of_sq_lt_sq' h (by numbers)
  rintro (h3 | h3)
  · addarith [h1, h3]
  · addarith [h2, h3]

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  rintro ⟨N, hN⟩
  obtain ⟨k1, h1⟩ := hN (N + 1) (by extra)
  obtain ⟨k2, h2⟩ := hN (N + 2) (by extra)
  have h : 2 * k2 = 2 * k1 + 1 := by
    calc 2 * k2 = N + 2 := by rw [h2]
      _ = (N + 1) + 1 := by ring
      _ = 2 * k1 + 1 := by rw [h1]
  obtain h3 | h3 := le_or_lt k2 k1
  · have :=
      calc 2 * k1 + 1 = 2 * k2 := by rw [h]
        _ ≤ 2 * k1 := by rel [h3]
    addarith [this]
  · have h4 : k1 + 1 ≤ k2 := h3
    have :=
      calc 2 * k1 + 1 = 2 * k2 := by rw [h]
        _ ≥ 2 * (k1 + 1) := by rel [h4]
        _ = 2 * k1 + 2 := by ring
    addarith [this]

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  rintro ⟨N, hN⟩
  obtain ⟨k, hk⟩ := hN (N + 1) (by extra)
  have H1 : Nat.Odd (N + 2) := by
    use k
    calc N + 2 = (N + 1) + 1 := by ring
      _ = 2 * k + 1 := by rw [hk]
  have H2 : Nat.Even (N + 2) := hN (N + 2) (by extra)
  rw [Nat.even_iff_not_odd] at H2
  contradiction

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  sorry

example : ¬ Prime 1 := by
  sorry

example : Prime 97 := by
  sorry
