/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring

example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  have H := calc
    n = 5 * (5 * n) - 24 * n := by ring
    _ = 5 * (8 * a) - 24 * n := by rw [ha]
    _ = 8 * (5 * a - 3 * n) := by ring
  use 5 * a - 3 * n
  exact H

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  have H := calc
    n = 2 * (3 * n) - 5 * n := by ring
    _ = 2 * (5 * a) - 5 * n := by rw [ha]
    _ = 5 * (2 * a - n) := by ring
  use 2 * a - n
  exact H

example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/

example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  have H := calc
    n = 5 * (11 * n) - 54 * n := by ring
    _ = 5 * (6 * a) - 54 * n := by rw [ha]
    _ = 6 * (5 * a - 9 * n) := by ring
  use 5 * a - 9 * n
  exact H

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨k, hk⟩ := ha
  have H := calc
    a = 3 * (5 * a) - 14 * a := by ring
    _ = 3 * (7 * k) - 14 * a := by rw [hk]
    _ = 7 * (3 * k - 2 * a) := by ring
  use 3 * k - 2 * a
  exact H

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have H := calc
    n = (9 * 4) * n - (7 * 5) * n := by ring
    _ = (9 * 4) * (7 * a) - (7 * 5) * n := by rw [ha]
    _ = (9 * 4) * (7 * a) - (7 * 5) * (9 * b) := by rw [hb]
    _ = 63 * (4 * a - 5 * b) := by ring
  use 4 * a - 5 * b
  exact H


example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have H := calc
    n = (5 * 8) * n - (13 * 3) * n := by ring
    _ = (5 * 8) * (13 * b) - (13 * 3) * n := by rw [hb]
    _ = (5 * 8) * (13 * b) - (13 * 3) * (5 * a) := by rw [ha]
    _ = 65 * (8 * b - 3 * a) := by ring
  use 8 * b - 3 * a
  exact H
