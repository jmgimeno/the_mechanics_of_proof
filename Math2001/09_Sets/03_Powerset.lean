/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Set Function

#check {3, 4, 5} -- `{3, 4, 5} : Set ℕ`
#check {n : ℕ | 8 < n} -- `{n | 8 < n} : Set ℕ`
#check {k : ℕ | ∃ a, a ^ 2 = k} -- `{k | ∃ a, a ^ 2 = k} : Set ℕ`

#check {{3, 4}, {4, 5, 6}} -- `{{3, 4}, {4, 5, 6}} : Set (Set ℕ)`
#check {s : Set ℕ | 3 ∈ s} -- `{s | 3 ∈ s} : Set (Set ℕ)`

example : {n : ℕ | Nat.Even n} ∉ {s : Set ℕ | 3 ∈ s} := by
  dsimp
  rw [← Nat.odd_iff_not_even]
  use 1
  numbers

def p (s : Set ℕ) : Set ℕ := {n : ℕ | n + 1 ∈ s}

#check @p -- `p : Set ℕ → Set ℕ`

example : ¬ Injective p := by
  dsimp [Injective, p]
  push_neg
  use {0}, ∅
  dsimp
  constructor
  · ext x
    dsimp
    suffices x + 1 ≠ 0 by exhaust
    apply ne_of_gt
    extra
  · ext
    push_neg
    use 0
    dsimp
    exhaust

def q (s : Set ℤ) : Set ℤ := {n : ℤ | n + 1 ∈ s}

example : Injective q := by
  dsimp [Injective, q]
  intro s t hst
  ext k
  have hk : k - 1 ∈ {n | n + 1 ∈ s} ↔ k - 1 ∈ {n | n + 1 ∈ t} := by rw [hst]
  dsimp at hk
  conv at hk => ring
  apply hk

example : ¬ ∃ f : X → Set X, Surjective f := by
  intro h
  obtain ⟨f, hf⟩ := h
  let s : Set X := {x | x ∉ f x}
  obtain ⟨x, hx⟩ := hf s
  by_cases hxs : x ∈ s
  · have hfx : x ∉ f x := hxs
    rw [hx] at hfx
    contradiction
  · have hfx : ¬ x ∉ f x := hxs
    rw [hx] at hfx
    contradiction

/-! # Exercises -/

def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  dsimp [Injective]
  push_neg
  use ∅, {3}
  constructor
  · ext k
    dsimp [r]
    exhaust
  · intro h
    have h1 : 3 ∈ {3} := by
      dsimp
    rw [← h] at h1
    have h2 : 3 ∉ ∅ := by
      dsimp
      exhaust
    contradiction

example : ¬ Injective r := by
  dsimp [Injective]
  push_neg
  use ∅, {3}
  constructor
  · ext k
    dsimp [r]
    exhaust
  · intro h
    have h1 : 3 ∈ ∅ := by
      rw [h]
      dsimp
    exact h1

namespace Int

def U : ℕ → Set ℤ
  | 0 => univ
  | n + 1 => {x : ℤ | ∃ y ∈ U n, x = 2 * y}

example (n : ℕ) : U n = {x : ℤ | (2:ℤ) ^ n ∣ x} := by
  simple_induction n with k hk
  · rw [U]
    ext x
    dsimp
    constructor
    · intro
      use x
      ring
    · intro
      exhaust
  · rw [U]
    ext x
    dsimp
    constructor
    · intro h
      obtain ⟨y, hy1, hy2⟩ := h
      rw [hk] at hy1
      dsimp at hy1
      obtain ⟨l, hl⟩ := hy1
      use l
      rw [hy2, hl]
      ring
    · intro h
      obtain ⟨l, hl⟩ := h
      use 2 ^ k * l
      constructor
      · rw [hk]
        dsimp
        use l
        ring
      · rw [hl]
        ring

example (n : ℕ) : U n = {x : ℤ | (2:ℤ) ^ n ∣ x} := by
  simple_induction n with k hk
  · rw [U]
    ext x
    dsimp
    constructor
    · intro
      use x
      ring
    · intro
      exhaust
  · rw [U, hk]
    ext x
    dsimp
    constructor
    · rintro ⟨y, ⟨l, rfl⟩, rfl⟩
      use l
      ring
    · rintro ⟨l, rfl⟩
      use 2 ^ k * l
      constructor
      · use l
        ring
      · ring
