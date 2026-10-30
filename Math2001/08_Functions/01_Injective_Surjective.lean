/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int

def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

#eval F 5 -- infoview displays `8`
#check @F -- infoview displays `F : ℕ → ℤ`

def q (x : ℝ) : ℝ := x + 3

#check @q -- infoview displays `q : ℝ → ℝ`
#check fun (x : ℝ) ↦ x ^ 2 -- infoview displays `fun x ↦ x ^ 2 : ℝ → ℝ`

example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  dsimp [q] at h
  addarith [h]

example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  use -1, 1
  constructor
  · numbers
  · numbers

def s (a : ℚ) : ℚ := 3 * a + 2

example : Surjective s := by
  dsimp [Surjective]
  intro y
  use (y - 2) / 3
  calc s ((y - 2) / 3) = 3 * ((y - 2) / 3) + 2 := by rw [s]
    _ = y := by ring

example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  calc -1 < 0 := by numbers
    _ ≤ x ^ 2 := by extra

inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer

def f : Musketeer → Musketeer
  | athos => aramis
  | porthos => aramis
  | aramis => athos

example : ¬ Injective f := by
  dsimp [Injective]
  push_neg
  use athos, porthos
  dsimp [f] -- optional
  exhaust

example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a
  · exhaust
  · exhaust
  · exhaust

-- better (more automated) version of the previous proof
example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a <;> exhaust

def g : Musketeer → Musketeer
  | athos => porthos
  | porthos => aramis
  | aramis => athos

example : Injective g := by
  dsimp [Injective]
  intro x1 x2 hx
  cases x1 <;> cases x2 <;> exhaust

example : Surjective g := by
  dsimp [Surjective]
  intro y
  cases y
  · use aramis
    exhaust
  · use athos
    exhaust
  · use porthos
    exhaust

example : Injective (fun (x:ℝ) ↦ x ^ 3) := by
  intro x1 x2 hx
  dsimp at hx
  have H : (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = 0
  · calc (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = x1 ^ 3 - x2 ^ 3 := by ring
      _ = x1 ^ 3 - x1 ^ 3 := by rw [hx]
      _ = 0 := by ring
  rw [mul_eq_zero] at H
  obtain H1 | H2 := H
  · -- case 1: x1 - x2 = 0
    addarith [H1]
  · -- case 2: x1 ^2 + x1 * x2 + x2 ^ 2  = 0
    by_cases hx1 : x1 = 0
    · -- case 2a: x1 = 0
      have hx2 :=
        calc x2 ^ 3 = x1 ^ 3 := by rw [hx]
          _ = 0 ^ 3 := by rw [hx1]
          _ = 0 := by numbers
      cancel 3 at hx2
      calc x1 = 0 := by rw [hx1]
        _ = x2 := by rw [hx2]
    · -- case 2b: x1 ≠ 0
      have :=
        calc 0 < x1 ^ 2 + ((x1 + x2) ^ 2 + x2 ^ 2) := by extra
            _ = 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) := by ring
            _ = 2 * 0 := by rw [H2]
            _ = 0 := by ring
      numbers at this -- contradiction!

/-! # Exercises -/

example : Injective (fun (x : ℚ) ↦ x - 12) := by
  dsimp [Injective]
  intro x1 x2 hx
  addarith [hx]

-- example : ¬ Injective (fun (x : ℚ) ↦ x - 12) := by
--   sorry

-- example : Injective (fun (x : ℝ) ↦ 3) := by
--   sorry

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 0, 1
  constructor <;> numbers

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x1 x2 hx
  have : 3 * x1 = 3 * x2 := by addarith [hx]
  cancel 3 at this

-- example : ¬ Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
--   sorry

example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x1 x2 hx
  have : 3 * x1 = 3 * x2 := by addarith [hx]
  cancel 3 at this

-- example : ¬ Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
--   sorry

example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Surjective]
  intro x
  use x / 2
  ring

-- example : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
--   sorry

-- example : Surjective (fun (x : ℤ) ↦ 2 * x) := by
--   sorry

example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  dsimp [Surjective]
  push_neg
  use 1
  intro x
  obtain hx | hx := le_or_succ_le x 0
  · apply ne_of_lt
    calc
      2 * x ≤ 2 * 0 := by rel [hx]
      _ < 1 := by numbers
  · apply ne_of_gt
    calc
      2 * x ≥ 2 * 1 := by rel [hx]
      _ > 1 := by numbers

example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  intro h
  obtain ⟨x, hx⟩ := h 1
  have h1 : Int.Even 1 := by
    use x
    rw [← hx]
  have h2 : Int.Odd 1 := by
    use 0
    numbers
  rw [Int.even_iff_not_odd] at h1
  contradiction

example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  intro h
  obtain ⟨x, hx⟩ := h 1
  have h1 : Int.Even 1 := ⟨x, hx.symm⟩
  rw [Int.even_iff_not_odd] at h1
  apply h1
  use 0
  numbers

-- example : Surjective (fun (n : ℕ) ↦ n ^ 2) := by
--   sorry

example : ¬ Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  dsimp [Surjective]
  push_neg
  use 3
  intro n
  obtain hn | hn := le_or_succ_le n 1
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 3 := by numbers
  · apply ne_of_gt
    calc
      n ^ 2 ≥ 2 ^2 := by rel [hn]
      _ > 3 := by numbers

inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

-- example : Injective h := by
--   sorry

example : ¬ Injective h := by
  dsimp [Injective]
  push_neg
  use athos, aramis
  constructor <;> exhaust

example : Surjective h := by
  dsimp [Surjective]
  intro x
  cases x
  · use porthos
    exhaust
  · use athos
    exhaust

-- example : ¬ Surjective h := by
--   sorry

def l : White → Musketeer
  | meg => aramis
  | jack => porthos

example : Injective l := by
  dsimp [Injective]
  intro x1 x2 h
  cases x1 <;> cases x2 <;> exhaust

-- example : ¬ Injective l := by
--   sorry

-- example : Surjective l := by
--   sorry

example : ¬ Surjective l := by
  dsimp [Surjective]
  push_neg
  use athos
  intro x
  cases x <;> exhaust

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  constructor
  · intro hInj
    intro x1 x2 hx hEq
    have := hInj hEq
    contradiction
  · intro h
    intro x1 x2 hEq
    by_cases hx1x2 : x1 = x2
    · apply hx1x2
    · push_neg at hx1x2
      have := h x1 x2 hx1x2
      contradiction

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  intro f hInj
  dsimp [Injective] at *
  intro x1 x2 hEq
  have : f x1 = f x2 := by addarith [hEq]
  apply hInj this

-- example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
--   sorry

-- example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
--   sorry

example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  push_neg
  use fun (x: ℚ) ↦ -x
  dsimp [Injective] at *
  constructor
  · intro x1 x2 hx
    addarith [hx]
  · push_neg
    use 0, 1
    constructor <;> numbers

-- example : ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
--   sorry

example : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  push_neg
  use fun (x : ℤ) ↦ x
  constructor
  · intro x
    use x
    rfl
  · intro h
    obtain ⟨x, hx⟩ := h 1
    have h1 : Int.Even 1 := ⟨x, hx.symm⟩
    rw [Int.even_iff_not_odd] at h1
    apply h1
    use 0
    numbers

-- example : ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
--   sorry

example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  push_neg
  use 0
  dsimp [Surjective]
  push_neg
  use 1
  intro x
  apply ne_of_lt
  calc
    0 * x = 0 := by ring
    _ < 1 := by numbers

example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  intro h
  obtain ⟨x, hx⟩ := h 0 1
  have := calc
    0 = 0 * x := by ring
    _ = 1 := hx
  numbers at this

example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp [Injective]
  intro x1 x2 hfx
  obtain hx1x2 | hx1x2 := le_or_gt x1 x2
  · obtain hx1x2 | hx1x2 := eq_or_lt_of_le hx1x2
    · apply hx1x2
    · have := hf x1 x2 hx1x2
      apply ne_of_lt at this
      contradiction
  · have := hf x2 x1 hx1x2
    apply ne_of_gt at this
    contradiction

example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  intro x1 x2 hfx
  obtain h | h | h := lt_trichotomy x1 x2
  · have := ne_of_lt (hf x1 x2 h)
    contradiction
  · apply h
  · have := ne_of_gt (hf x2 x1 h)
    contradiction

example {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp [Surjective]
  intro n
  simple_induction n with k hk
  · use x0
    apply h0
  · obtain ⟨x, hx⟩ := hk
    use (i x)
    calc
      f (i x) = f x + 1 := by rw [hi]
      _ = k + 1 := by rw [hx]
