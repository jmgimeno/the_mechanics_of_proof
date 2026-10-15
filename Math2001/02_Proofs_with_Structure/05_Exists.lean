/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : 0 < x * (-t) := by
      calc
        0 < -(x * t) := by addarith [hxt]
        _ = x * (-t) := by ring
    cancel x at hxt'
    apply ne_of_lt
    addarith [hxt']

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers

example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  · calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  · calc
      (p + q) / 2 < (q + q) / 2 := by rel [h]
      _ = q := by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  · numbers
  · constructor
    · numbers
    · constructor
      · numbers
      · numbers

/-! # Exercises -/

example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9, 2
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  · numbers
  · numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 0, 0
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1/2
  calc
    (x + 1/2) ^ 2 = x ^ 2 + 1/4 + x := by ring
    _ > x := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨ a, hat ⟩ := h

  obtain ha | ha := le_or_gt a 1
  · have hat' : 0 < (1 - a) * (t - 1) := by
      calc
        0 < a + t - a * t - 1 := by addarith [hat]
        _ = (1 - a) * (t - 1) := by ring
    have ha' : 0 ≤ 1 - a := by addarith [ha]
    apply ne_of_gt
    cancel (1 - a) at hat'
    addarith [hat']
  · have hat' : 0 < (a - 1) * (1 - t) := by
      calc
        0 < a + t - a * t - 1 := by addarith [hat]
        _ = (a - 1) * (1 - t) := by ring
    have ha' : 0 < (a - 1) := by addarith [ha]
    apply ne_of_lt
    cancel (a - 1) at hat'
    addarith [hat']

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨ a, h ⟩ := h
  obtain ha | ha := le_or_succ_le a 2
  · apply ne_of_lt
    calc
      m = 2 * a := by rw [h]
      _ ≤ 2 * 2 := by rel [ha]
      _ < 5 := by numbers
  · apply ne_of_gt
    calc
      m = 2 * a := by rw [h]
      _ ≥ 2 * 3 := by rel [ha]
      _ > 5 := by numbers

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  obtain hn | hn := le_or_succ_le n 0
  · use 2
    calc
      2 * 2 ^ 3 = 16 := by numbers
      _ ≥ 2 * n + 7 := by addarith [hn]
      _ = n * 2 + 7 := by ring
  · use n + 1
    have h : 2 * n ^ 3 + 5 * n ^ 2 + 5 * n - 5 > 0 := by
      calc
        2 * n ^ 3 + 5 * n ^ 2 + 5 * n - 5 ≥ 2 * 1 ^ 3 + 5 * 1 ^ 2 + 5 * 1 - 5 := by rel [hn]
        _ > 0 := by numbers
    calc
      2 * (n + 1) ^ 3 = n * (n + 1) + 7 + (2 * n ^ 3 + 5 * n ^ 2 + 5 * n - 5) := by ring
      _ ≥ n * (n + 1) + 7 :=by extra

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  exists (b + c - a) / 2, (a + c - b) / 2 , (a + b - c) / 2
  constructor
  · addarith [ha]
  · constructor
    · addarith [hb]
    · constructor
      · addarith [hc]
      · constructor
        · ring
        · constructor
          · ring
          · ring
