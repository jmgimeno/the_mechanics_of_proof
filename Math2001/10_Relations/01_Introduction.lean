/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

example : Reflexive ((·:ℕ) ∣ ·) := by
  dsimp [Reflexive]
  intro x
  use 1
  ring

example : ¬ Symmetric ((·:ℕ) ∣ ·) := by
  dsimp [Symmetric]
  push_neg
  use 1, 2
  constructor
  · use 2
    numbers
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor
    · numbers
    · numbers

example : AntiSymmetric ((·:ℕ) ∣ ·) := by
  have H : ∀ {m n}, m = 0 → m ∣ n → m = n
  · intro m n h1 h2
    obtain ⟨k, hk⟩ := h2
    calc m = 0 := h1
      _ = 0 * k := by ring
      _ = m * k := by rw [h1]
      _ = n := by rw [hk]
  dsimp [AntiSymmetric]
  intro x y h1 h2
  obtain hx | hx := Nat.eq_zero_or_pos x
  · apply H hx h1
  · obtain hy | hy := Nat.eq_zero_or_pos y
    · have : y = x := by apply H hy h2
      rw [this]
    · apply le_antisymm
      · apply Nat.le_of_dvd hy h1
      · apply Nat.le_of_dvd hx h2

example : Transitive ((·:ℕ) ∣ ·) := by
  dsimp [Transitive]
  intro a b c hab hbc
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  use k * l
  calc c = b * l := by rw [hl]
    _ = (a * k) * l := by rw [hk]
    _ = a * (k * l) := by ring

example : Reflexive ((·:ℝ) = ·) := by
  dsimp [Reflexive]
  intro x
  ring

example : Symmetric ((·:ℝ) = ·) := by
  dsimp [Symmetric]
  intro x y h
  rw [h]

example : AntiSymmetric ((·:ℝ) = ·) := by
  dsimp [AntiSymmetric]
  intro x y h1 h2
  rw [h1]

example : Transitive ((·:ℝ) = ·) := by
  dsimp [Transitive]
  intro x y z h1 h2
  rw [h1, h2]

section
local infix:50 "∼" => fun (x y : ℝ) ↦ (x - y) ^ 2 ≤ 1

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro x
  calc (x - x) ^ 2 = 0 := by ring
    _ ≤ 1 := by numbers

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  calc (y - x) ^ 2 = (x - y) ^ 2 := by ring
    _ ≤ 1 := by rel [h]

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 1.1
  constructor
  · numbers
  · constructor
    · numbers
    · numbers

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 1.9, 2.5
  constructor
  · numbers
  · constructor
    · numbers
    · numbers
end

section

inductive Hand
  | rock
  | paper
  | scissors

open Hand

@[reducible] def r : Hand → Hand → Prop
  | rock, rock => False
  | rock, paper => True
  | rock, scissors => False
  | paper, rock => False
  | paper, paper => False
  | paper, scissors => True
  | scissors, rock => True
  | scissors, paper => False
  | scissors, scissors => False

local infix:50 " ≺ " => r

example : ¬ Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  push_neg
  use rock
  exhaust

example : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]
  push_neg
  use rock, paper
  exhaust

example : AntiSymmetric (· ≺ ·) := by
  dsimp [AntiSymmetric]
  intro x y
  cases x <;> cases y <;> exhaust

example : ¬ Transitive (· ≺ ·) := by
  dsimp [Transitive]
  push_neg
  use rock, paper, scissors
  exhaust
end

/-! # Exercises -/

example : ¬ Symmetric ((·:ℝ) < ·) := by
  dsimp [Symmetric]
  push_neg
  use 0, 1
  constructor <;> numbers

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x ≡ y [ZMOD 2]

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 2, 4
  constructor
  · use -1
    numbers
  · constructor
    · use 1
      numbers
    · numbers
end

section
inductive Little
  | meg
  | jo
  | beth
  | amy
  deriving DecidableEq

open Little

@[reducible] def s : Little → Little → Prop
  | meg, meg => True
  | meg, jo => True
  | meg, beth => True
  | meg, amy => True
  | jo, meg => True
  | jo, jo => True
  | jo, beth => True
  | jo, amy => False
  | beth, meg => True
  | beth, jo => True
  | beth, beth => False
  | beth, amy => True
  | amy, meg => True
  | amy, jo => False
  | amy, beth => True
  | amy, amy => True

local infix:50 " ∼ " => s

-- example : Reflexive (· ∼ ·) := by
--   sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use beth
  exhaust

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y
  cases x <;> cases y <;> exhaust

-- example : ¬ Symmetric (· ∼ ·) := by
--   sorry

-- example : AntiSymmetric (· ∼ ·) := by
--   sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use beth, jo
  exhaust

-- example : Transitive (· ∼ ·) := by
--   sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use beth, jo, beth
  exhaust
end

section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

-- example : Reflexive (· ∼ ·) := by
--   sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 0
  numbers

-- example : Symmetric (· ∼ ·) := by
--   sorry

example : ¬ Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  push_neg
  use 3, 4
  constructor
  · numbers
  · intro h
    have := calc
      3 ≡ 4 + 1 [ZMOD 5] := h
      _ = 0 + 5 * 1 := by numbers
      _ ≡ 0 [ZMOD 5] := by extra
    numbers at this

example : AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  intro x y ⟨a, ha⟩ ⟨b, hb⟩
  have h1 := calc
    2 - 0 = -((y - (x + 1)) + (x - (y + 1))) := by ring
    _ = -(5 * a + 5 * b) := by rw [ha, hb]
    _ = 5 * (-(a + b)) := by ring
  have h2 : 2 ≡ 0 [ZMOD 5]
  · use - (a + b)
    apply h1
  numbers at h2

-- example : ¬ AntiSymmetric (· ∼ ·) := by
--   sorry

-- example : Transitive (· ∼ ·) := by
--   sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 2, 3
  constructor
  · numbers
  · constructor
    · numbers
    · intro h
      have := calc
        3 ≡ 1 + 1 [ZMOD 5] := h
        _ = 2 + 5 * 0 := by numbers
        _ ≡ 2 [ZMOD 5] := by extra
      numbers at this
end

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

-- example : Reflexive (· ∼ ·) := by
--   sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 1
  numbers

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y hxy
  calc
    y + x = x + y := by ring
    _ ≡ 0 [ZMOD 3] := by rel [hxy]

-- example : ¬ Symmetric (· ∼ ·) := by
--   sorry

-- example : AntiSymmetric (· ∼ ·) := by
--   sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 2
  constructor
  · use 1
    numbers
  · constructor
    · use 1
      numbers
    · numbers

-- example : Transitive (· ∼ ·) := by
--   sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 2, 1
  constructor
  · use 1
    numbers
  · constructor
    · use 1
      numbers
    · intro h
      numbers at h
end

example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Reflexive, Set.subset_def]
  intro s x hxs
  apply hxs

-- example : ¬ Reflexive ((· : Set ℕ) ⊆ ·) := by
--   sorry

-- example : Symmetric ((· : Set ℕ) ⊆ ·) := by
--   sorry

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [Symmetric]
  push_neg
  use ∅, {1}
  dsimp [Set.subset_def]
  constructor
  · intro x h
    contradiction
  · push_neg
    use 1
    exhaust

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [Symmetric]
  push_neg
  use ∅, {1}
  constructor
  · intro x h
    contradiction
  · intro h
    exact h (a := 1) rfl

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  intro h
  have h1 : (∅ : Set ℕ) ⊆ {1} := Set.empty_subset {1}
  exact h h1 (a := 1) rfl

example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [AntiSymmetric]
  intro x y hxy hyx
  ext a
  constructor
  · apply hxy
  · apply hyx

-- example : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
--   sorry

example : Transitive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Transitive]
  intro x y z hxy hyz a hax
  apply hyz (hxy hax)

-- example : ¬ Transitive ((· : Set ℕ) ⊆ ·) := by
--   sorry

section
local infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)

example : Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  intro (x, y)
  dsimp
  constructor <;> extra

-- example : ¬ Reflexive (· ≺ ·) := by
--   sorry

-- example : Symmetric (· ≺ ·) := by
--   sorry

example : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]
  push_neg
  use (0, 0), (1, 1)
  dsimp
  constructor
  · constructor <;> numbers
  · left ; numbers

example : AntiSymmetric (· ≺ ·) := by
  dsimp [AntiSymmetric]
  intro (x1, y1) (x2, y2) ⟨hx12, hy12⟩ ⟨hx21, hy21⟩
  dsimp at *
  have hx : x1 = x2 := le_antisymm hx12 hx21
  have hy : y1 = y2 := le_antisymm hy12 hy21
  rw [hx, hy]

-- example : ¬ AntiSymmetric (· ≺ ·) := by
--   sorry

example : Transitive (· ≺ ·) := by
  dsimp [Transitive]
  intro (x1, y1) (x2, y2) (x3, y3) ⟨hx12, hy12⟩ ⟨hx23, hy23⟩
  dsimp at *
  constructor
  · calc
      x1 ≤ x2 := hx12
      _ ≤ x3 := hx23
  · calc
      y1 ≤ y2 := hy12
      _ ≤ y3 := hy23

example : Transitive (· ≺ ·) := by
  dsimp [Transitive]
  intro (x1, y1) (x2, y2) (x3, y3) ⟨hx12, hy12⟩ ⟨hx23, hy23⟩
  dsimp at *
  constructor
  · apply le_trans hx12 hx23
  · apply le_trans hy12 hy23

example : Transitive (· ≺ ·) := by
  intro (x1, y1) (x2, y2) (x3, y3) ⟨hx12, hy12⟩ ⟨hx23, hy23⟩
  exact ⟨hx12.trans hx23, hy12.trans hy23⟩

-- example : ¬ Transitive (· ≺ ·) := by
--   sorry
end
