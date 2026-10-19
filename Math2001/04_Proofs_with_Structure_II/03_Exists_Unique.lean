/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int

example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  · intro y hy
    calc
      y = (3 * y + 1 - 1) / 3 := by ring
      _ = (7 - 1) / 3 := by rw [hy]
      _ = 2 := by numbers

example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro a h1 h2
    have h1' : -1 ≤ a - 2 := by addarith [h1]
    have h2' : a - 2 ≤ 1 := by addarith [h2]
    have H := sq_le_sq' h1' h2'
    calc
      (a - 2) ^ 2 ≤ 1 ^ 2 := H
      _ = 1 := by numbers
  · intro y
    intro h
    have h1 := h 1 (by numbers) (by numbers)
    have h2 := h 3 (by numbers) (by numbers)
    have H1 : (y - 2) ^ 2 ≤ 0 := calc
      (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2)/ 2 := by ring
      _ ≤ (1 + 1 - 2) / 2 := by rel [h1, h2]
      _ = 0 := by numbers
    have H2 : 0 ≤ (y - 2) ^ 2 := by extra
    have H3 : (y - 2) ^ 2 = 0 := le_antisymm H1 H2
    cancel 2 at H3
    calc
      y = y - 2 + 2 := by ring
      _ = 0 + 2 := by rw [H3]
      _ = 2 := by numbers

example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro a h1 h2
    have H : (a - 2) ^ 2 ≤ 1 ^ 2 := sq_le_sq' (by addarith [h1]) (by addarith [h2])
    addarith [H]
  · intro y h
    have h1 := h 1 (by numbers) (by numbers)
    have h2 := h 3 (by numbers) (by numbers)
    have H1 : (y - 2) ^ 2 ≤ 0 := calc
      (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
      _ ≤ (1 + 1 - 2) / 2 := by rel [h1, h2]
      _ = 0 := by numbers
    have H2 : (y - 2) ^ 2 = 0 := le_antisymm H1 (by extra)
    cancel 2 at H2
    addarith [H2]

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring

example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/

example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  · intro y hy
    calc
      y = (4 * y - 3) / 4 + 3 / 4 := by ring
      _ = 9 / 4 + 3 / 4 := by rw [hy]
      _ = 3 := by numbers

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · intro a
    extra
  · intro y hy
    apply le_antisymm (hy 0) (by extra)

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  constructor
  · constructor
    · numbers
    · constructor
      · numbers
      · use 3
        numbers
  · intro y hy
    obtain ⟨h1, h2, k, hk⟩ := hy
    have H1 := calc
      3 * 2 < 11 - y := by addarith [h2]
      _ = 3 * k := by rw [hk]
    cancel 3 at H1
    have H2 := calc
      3 * k = 11 - y := by rw [hk]
      _ < 3 * 4 := by addarith [h1]
    cancel 3 at H2
    interval_cases k
    addarith [hk]
