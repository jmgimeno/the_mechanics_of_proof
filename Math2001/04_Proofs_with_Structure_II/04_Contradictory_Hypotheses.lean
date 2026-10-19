/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos

example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
    calc
      7 = t := by addarith [h]
      _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction

example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
    calc
      7 = t := by addarith [h]
      _ < 3 := h2
  numbers at H -- this is a contradiction!

example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h

example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp
  · intro m hmp
    have hp' : 0 < p := by extra
    have h1m := Nat.pos_of_dvd_of_pos hmp hp'
    obtain hm | hm : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
    · left
      addarith [hm]
    · right
      have hmp' := Nat.le_of_dvd hp' hmp
      obtain hm' | hm' : m = p ∨ m < p := eq_or_lt_of_le hmp'
      · apply hm'
      · have := H m hm hm'
        contradiction

example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain ha' | ha' := le_or_succ_le a 2
  · obtain hb' | hb' := le_or_succ_le b 1
    · have H := calc
        c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
        _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [ha', hb']
        _ < 3 ^ 2 := by numbers
      cancel 2 at H
      interval_cases a <;> interval_cases b <;> interval_cases c <;> numbers at h_pyth
    · have H1 := calc
        b ^ 2 < a ^ 2 + b ^ 2 := by extra
        _ = c ^ 2 := by rw [h_pyth]
      cancel 2 at H1
      have H2 := calc
        c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
        _ ≤ 2 ^ 2 + b ^ 2 := by rel [ha']
        _ = b ^ 2 + 2 * 2 := by ring
        _ ≤ b ^ 2 + b * 2 := by rel [hb']
        _ < b ^ 2 + b * 2 + 1 := by extra
        _ = (b + 1) ^ 2 := by ring
      cancel 2 at H2
      addarith [H1, H2] -- b < c < b + 1 impossible for nats (addarith finds contradiction)
  · exact ha'

/-! # Exercises -/

example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  cancel n at h

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5
  · have H := calc
      0 ≡ 0 [ZMOD 5] := by extra
      _ = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at H
  · have H := calc
      1 ≡ 1 [ZMOD 5] := by extra
      _ = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at H
  · left
    exact h
  · right
    exact h
  · have H := calc
      1 ≡ 1 + 5 * 3 [ZMOD 5] := by extra
      _ = 4 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at H

example : Prime 7 := by
  apply prime_test
  · numbers
  · intro m h1 h2
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 3 ; constructor <;> numbers
    · use 2 ; constructor <;> numbers
    · use 1 ; constructor <;> numbers
    · use 1 ; constructor <;> numbers
    · use 1 ; constructor <;> numbers

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain hx | hx := h3
  · have hx' : x = -2 := by addarith [hx]
    rw [hx'] at h2
    numbers at h2
  · addarith [hx]

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨h1, h2⟩ := h
  obtain hp | hp := le_or_succ_le p 2
  · left
    apply le_antisymm hp h1
  · right
    have h2' := h2 2
    obtain hp' | hp' := even_or_odd p
    · obtain ⟨k, hk⟩ := hp'
      have H2 : 2 ∣ p := by
        use k
        addarith [hk]
      obtain H4 | H4 := h2' H2
      · numbers at H4
      · addarith [hp, H4]
    · apply hp'
