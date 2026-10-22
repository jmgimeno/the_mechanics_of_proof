/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true

example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · rintro (hNotP | hNotQ) ⟨hP, hQ⟩ <;> contradiction

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]

example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
    calc ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
        ↔ ∃ n : ℤ, ¬ (∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_forall]
      _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬ (n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel [not_exists]
      _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬ (n ^ 2 < m) ∨ ¬ (m < (n + 1) ^ 2) := by rel [not_and_or]
      _ ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by rel [not_lt]

#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m

#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)

example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n ^ 2 ≥ 2 ^ 2 := by rel [hn]
      _ > 2 := by numbers

/-! # Exercises -/

-- do not use not_not or push_neg
example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  · intro h
    by_cases hp : P
    · exact hp
    · contradiction
  · intro hp hp'
    contradiction

-- do not use not_imp or push_neg
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro h
    constructor
    · by_cases hp : P
      · apply hp
      · have : P → Q := by
          intro hp'
          contradiction
        contradiction
    · intro hq -- not Q = Q -> False
      apply h  -- not (P -> Q) = (P -> Q) -> False
      intro hp
      apply hq
  · rintro ⟨hp, hq'⟩ h2
    have := h2 hp
    contradiction

-- do nou use for_all or push_neg
example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro h1
    by_cases h2 : ∃ x, ¬ P x
    · apply h2
    · have h3 : ∀ x, P x := by
        intro a
        by_cases h4 : P a
        · apply h4
        · have h5 : ∃ x, ¬ P x := by
            use a
            apply h4
          contradiction
      contradiction
  · intro h1 h2
    obtain ⟨a, ha⟩ := h1
    have := h2 a
    contradiction

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  calc (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
      ↔ ∃ a : ℤ, ¬ ∀ b : ℤ, (a * b = 1 → a = 1 ∨ b = 1) := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, ¬ (a * b = 1 → a = 1 ∨ b = 1) := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ ¬ (a = 1 ∨ b = 1) := by rel [not_imp]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by rel [not_or]

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  calc (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x)
      ↔ ∀ x : ℝ, ¬ ∀ y : ℝ, y ≤ x := by rel [not_exists]
    _ ↔  ∀ x : ℝ, ∃ y : ℝ, ¬ y ≤ x := by rel [not_forall]
    _ ↔  ∀ x : ℝ, ∃ y : ℝ, y > x := by rel [not_le]

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  calc ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5)
      ↔ ∀ m : ℤ, ¬ ∀ n : ℤ, m = n + 5 := by rel [not_exists]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by rel [not_forall]

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)

example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  obtain ht | ht := le_or_gt t 4
  · right
    addarith [ht]
  · left
    apply ht

example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro k
  obtain hk | hk := le_or_succ_le k 3
  · apply ne_of_gt
    calc
      2 * k ≤ 2 * 3 := by rel [hk]
      _ < 7 := by numbers
  · apply ne_of_lt
    calc
      2 * k ≥ 2 * 4 := by rel [hk]
      _ > 7 := by numbers

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  right
  use k
  constructor
  · apply hk
  · constructor
    · apply hk1
    · apply hkp

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2 * a ^ 2
  calc
    2 * a ^ 3 = 2 * a ^ 2 * a := by ring
    _ < 2 * a ^ 2 * a + 7 := by extra

example {p : ℕ} (hp : ¬ Prime p) (hp_ge_2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    dsimp [Prime] at hp
    push_neg at hp
    obtain hp_lt_2 | hm := hp
    · addarith [hp_lt_2, hp_ge_2]
    · obtain ⟨d, hd_div_p, hd_ne_1, hd_ne_p⟩ := hm
      have hd' := H d
      have hp_gt_0 := by calc
        0 < 2 := by numbers
        _ ≤ p := hp_ge_2
      have hd_gt_0 : 0 < d := Nat.pos_of_dvd_of_pos hd_div_p hp_gt_0
      have hd_ge_2 : 2 ≤ d := by
        obtain hd | hd := le_or_succ_le d 1
        · obtain hd_eq_1 | hd_le_1 := eq_or_lt_of_le hd
          · contradiction
          · addarith [hd_le_1, hd_gt_0]
        · apply hd
      have hd_le_p : d ≤ p := Nat.le_of_dvd hp_gt_0 hd_div_p
      have hd_lt_p : d < p := by
        obtain hd_eq_p | hd_lt_p := eq_or_lt_of_le hd_le_p
        · contradiction
        · apply hd_lt_p
      have hd_div_p' := hd' hd_ge_2 hd_lt_p
      contradiction
  push_neg at H
  apply H

example {p : ℕ} (hp : ¬ Prime p) (hp_ge_2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    have : Prime p := prime_test hp_ge_2 H
    contradiction
  push_neg at H
  apply H

example {p : ℕ} (hp : ¬ Prime p) (hp_ge_2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  dsimp [Prime] at hp
  push_neg at hp
  obtain hp_lt_2 | ⟨m, hmp, hm_ne_1, hm_ne_p⟩ := hp
  · addarith [hp_lt_2, hp_ge_2]
  · have hp_pos : 0 < p := by extra
    use m
    constructor
    · obtain hm | hm : 1 = m ∨ 1 < m := eq_or_lt_of_le (Nat.pos_of_dvd_of_pos hmp hp_pos)
      · rw [← hm] at hm_ne_1
        numbers at hm_ne_1
      · apply hm
    · constructor
      · obtain hm | hm := eq_or_lt_of_le (Nat.le_of_dvd hp_pos hmp)
        · contradiction
        · apply hm
      · apply hmp
