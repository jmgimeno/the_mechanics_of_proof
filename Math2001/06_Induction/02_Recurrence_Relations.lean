/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init

namespace Int

def a (n : ℕ) : ℕ := 2 ^ n

#eval a 20 -- infoview displays `1048576`

def b : ℕ → ℤ
  | 0 => 3
  | n + 1 => b n ^ 2 - 2

#eval b 7 -- infoview displays `316837008400094222150776738483768236006420971486980607`

example (n : ℕ) : Odd (b n) := by
  simple_induction n with k IH
  · -- base case
    use 1
    calc b 0 = 3 := by rw [b]
      _ = 2 * 1 + 1 := by numbers
  · -- inductive step
    obtain ⟨x, hx⟩ := IH
    use 2 * x ^ 2 + 2 * x - 1
    calc b (k + 1) = b k ^ 2 - 2 := by rw [b]
      _ = (2 * x + 1) ^ 2 - 2 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 2 * x - 1) + 1 := by ring

example (n : ℕ) : Odd (b n) := by
  rw [odd_iff_modEq]
  simple_induction n with k IH
  · calc
      b 0 = 3 := by rw [b]
      _ = 1 + 2 * 1 := by numbers
      _ ≡ 1 [ZMOD 2] := by extra
  · calc
      b (k + 1) = b k ^ 2 - 2 := by rw [b]
      _ ≡ 1 ^ 2 - 2 [ZMOD 2] := by rel [IH]
      _ = 1 - 2 * 1:= by numbers
      _ ≡ 1 [ZMOD 2] := by extra

def x : ℕ → ℤ
  | 0 => 5
  | n + 1 => 2 * x n - 1

example (n : ℕ) : x n ≡ 1 [ZMOD 4] := by
  simple_induction n with k IH
  · -- base case
    calc
      x 0 = 5 := by rw [x]
      _ = 1 + 4 * 1 := by numbers
      _ ≡ 1 [ZMOD 4] := by extra
  · -- inductive step
    calc
      x (k + 1) = 2 * x k - 1 := by rw [x]
      _ ≡ 2 * 1 - 1 [ZMOD 4] := by rel [IH]
      _ = 1 := by numbers

example (n : ℕ) : x n = 2 ^ (n + 2) + 1 := by
  simple_induction n with k IH
  · -- base case
    calc x 0 = 5 := by rw [x]
      _ = 2 ^ (0 + 2) + 1 := by numbers
  · -- inductive step
    calc x (k + 1) = 2 * x k - 1 := by rw [x]
      _ = 2 * (2 ^ (k + 2) + 1) - 1 := by rw [IH]
      _ = 2 ^ ((k + 1) + 2) + 1 := by ring

def A : ℕ → ℚ
  | 0 => 0
  | n + 1 => A n + (n + 1)

example (n : ℕ) : A n = n * (n + 1) / 2 := by
  simple_induction n with k IH
  · -- base case
    calc A 0 = 0 := by rw [A]
      _ = 0 * (0 + 1) / 2 := by numbers
  · -- inductive step
    calc
      A (k + 1) = A k + (k + 1) := by rw [A]
      _ = k * (k + 1) / 2 + (k + 1) := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) / 2 := by ring

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

example (n : ℕ) : ∀ d, 1 ≤ d → d ≤ n → d ∣ n ! := by
  simple_induction n with k IH
  · -- base case
    intro d I1 I
    interval_cases d
  · -- inductive step
    intro d I1 I
    rw [factorial]
    obtain h | h : d = k + 1 ∨ d < k + 1 := eq_or_lt_of_le I
    · -- case 1: `d = k + 1`
      use (k !)
      rw [h]
    · -- case 2: `d < k + 1`
      obtain ⟨x, hx⟩ := IH d I1 (by addarith [h])
      use (k + 1) * x
      rw [hx]
      ring

example (n : ℕ) : (n + 1)! ≥ 2 ^ n := by
  simple_induction n with k IH
  · calc
      (0 + 1)! = (0 + 1) * 0! := by rfl -- rw [factorial] fails because rewrites 0!
      _ = (0 + 1) * 1 := by rw [factorial]
      _ ≥ 2 ^ 0 := by numbers
  · calc
      (k + 1 + 1)! = (k + 1 + 1) * (k + 1)! := by rw [factorial]
      _ ≥ (k + 1 + 1) * 2 ^ k  := by rel [IH]
      _ = k * 2 ^ k + 2 * 2 ^ k  := by ring
      _ ≥ 2 * 2 ^ k := by extra
      _ = 2 ^ (k + 1) := by ring

/-! # Exercises -/

def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  simple_induction n with k IH
  · rw [c]
    use 3
    numbers
  · obtain ⟨d, nd⟩ := IH
    rw [c]
    rw [nd]
    use 3 * d - 4
    ring

example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k IH
  · rw [c]; numbers
  · rw [c, IH]; ring

def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with k IH
  · rw [y]; numbers
  · rw [y, IH]; ring

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  · calc
      B 0 = 0 := by rw [B]
      _ = 0 * (0 + 1) * (2 * 0 + 1) / 6 := by numbers
  · calc
      B (k + 1) = B k + (k + 1) ^ 2 := by rw [B]
      _ = k * (k + 1) * (2 * k + 1) / 6 + (k + 1) ^ 2 := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) / 6 := by ring

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

example (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  · rfl
  · rw [S, IH]; ring

-- eq_zero_or_eq_zero_of_mul_eq_zero

example (n : ℕ) : 0 < n ! := by
  simple_induction n with k IH
  · rw [factorial]; numbers
  · obtain hf | hf := Nat.eq_zero_or_pos (k + 1)!
    · rw [factorial] at hf
      obtain h | h := eq_zero_or_eq_zero_of_mul_eq_zero hf
      · addarith [h]
      · addarith [IH, h]
    · apply hf

example (n : ℕ) : 0 < n ! := by
  simple_induction n with k IH
  · rw [factorial]; numbers
  · calc
        (k + 1)! = (k + 1) * k ! := by rw [factorial]
        _ = k ! + k * k ! := by ring
        _ ≥ k ! := by extra
        _ > 0 := IH

example (n : ℕ) : 0 < n ! := by
  simple_induction n with k IH
  · rw [factorial]; numbers
  · rw [factorial]; extra

example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
  induction_from_starting_point n, hn with k hk IH
  · rw [factorial, factorial, factorial]
    use 1
    numbers
  · obtain ⟨d, hd⟩ := IH
    rw [factorial, hd]
    use d * (k + 1)
    ring

example (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with k IH
  · rw [factorial, factorial]; numbers
  · have H : (k + 1) < (k + 1 + 1) := by extra
    calc
      (k + 1 + 1)! = (k + 1 + 1) * (k + 1)! := by rw [factorial]
      _ ≤ (k + 1 + 1) * (k + 1) ^ k := by rel [IH]
      _ ≤ (k + 1 + 1) * (k + 1 + 1) ^ k := by rel [H]
      _ = (k + 1 + 1) ^ (k + 1) := by ring
