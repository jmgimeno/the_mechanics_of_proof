/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int

def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n

#eval a 5 -- infoview displays `31`

example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  two_step_induction n with k IH1 IH2
  . calc a 0 = 2 := by rw [a]
      _ = 2 ^ 0 + (-1) ^ 0 := by numbers
  . calc a 1 = 1 := by rw [a]
      _ = 2 ^ 1 + (-1) ^ 1 := by numbers
  calc
    a (k + 2)
      = a (k + 1) + 2 * a k := by rw [a]
    _ = (2 ^ (k + 1) + (-1) ^ (k + 1)) + 2 * (2 ^ k + (-1) ^ k) := by rw [IH1, IH2]
    _ = 2 ^ (k + 2) + (-1) ^ (k + 2) := by ring

example {m : ℕ} (hm : 1 ≤ m) : a m ≡ 1 [ZMOD 6] ∨ a m ≡ 5 [ZMOD 6] := by
  have H : ∀ n : ℕ, 1 ≤ n →
      (a n ≡ 1 [ZMOD 6] ∧ a (n + 1) ≡ 5 [ZMOD 6])
    ∨ (a n ≡ 5 [ZMOD 6] ∧ a (n + 1) ≡ 1 [ZMOD 6])
  · intro n hn
    induction_from_starting_point n, hn with k hk IH
    · left
      constructor
      calc a 1 = 1 := by rw [a]
        _ ≡ 1 [ZMOD 6] := by extra
      calc a (1 + 1) = 1 + 2 * 2 := by rw [a, a, a]
        _ = 5 := by numbers
        _ ≡ 5 [ZMOD 6] := by extra
    · obtain ⟨IH1, IH2⟩ | ⟨IH1, IH2⟩ := IH
      · right
        constructor
        · apply IH2
        · calc a (k + 1 + 1) = a (k + 1) + 2 * a k := by rw [a]
            _ ≡ 5 + 2 * 1 [ZMOD 6] := by rel [IH1, IH2]
            _ = 6 * 1 + 1 := by numbers
            _ ≡ 1 [ZMOD 6] := by extra
      · left
        constructor
        · apply IH2
        · calc a (k + 1 + 1) = a (k + 1) + 2 * a k := by rw [a]
            _ ≡ 1 + 2 * 5 [ZMOD 6] := by rel [IH1, IH2]
            _ = 6 * 1 + 5 := by numbers
            _ ≡ 5 [ZMOD 6] := by extra
  obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m hm
  · left
    apply H1
  · right
    apply H1

def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

example (n : ℕ) : F n ≤ 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · calc F 0 = 1 := by rw [F]
      _ ≤ 2 ^ 0 := by numbers
  · calc F 1 = 1 := by rw [F]
      _ ≤ 2 ^ 1 := by numbers
  · calc F (k + 2) = F (k + 1) + F k := by rw [F]
      _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
      _ = 2 ^ (k + 2) := by ring

example (n : ℕ) : F (n + 1) ^ 2 - F (n + 1) * F n - F n ^ 2 = - (-1) ^ n := by
  simple_induction n with k IH
  · calc F 1 ^ 2 - F 1 * F 0 - F 0 ^ 2 = 1 ^ 2 - 1 * 1 - 1 ^ 2 := by rw [F, F]
      _ = - (-1) ^ 0 := by numbers
  · calc F (k + 2) ^ 2 - F (k + 2) * F (k + 1) - F (k + 1) ^ 2
        = (F (k + 1) + F k) ^ 2 - (F (k + 1) + F k) * F (k + 1)
            - F (k + 1) ^ 2 := by rw [F]
      _ = - (F (k + 1) ^ 2 - F (k + 1) * F k - F k ^ 2) := by ring
      _ = - -(-1) ^ k := by rw [IH]
      _ = -(-1) ^ (k + 1) := by ring

def d : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | k + 2 => 3 * d (k + 1) + 5 * d k

#eval d 2 -- infoview displays `18`
#eval d 3 -- infoview displays `59`
#eval d 4 -- infoview displays `267`
#eval d 5 -- infoview displays `1096`
#eval d 6 -- infoview displays `4623`
#eval d 7 -- infoview displays `19349`

#eval 4 ^ 2 -- infoview displays `16`
#eval 4 ^ 3 -- infoview displays `64`
#eval 4 ^ 4 -- infoview displays `256`
#eval 4 ^ 5 -- infoview displays `1024`
#eval 4 ^ 6 -- infoview displays `4096`
#eval 4 ^ 7 -- infoview displays `16384`

example : forall_sufficiently_large n : ℕ, d n ≥ 4 ^ n := by
  dsimp
  use 4
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · calc d 4 = 267 := by rfl
      _ ≥ 4 ^ 4 := by numbers
  · calc d 5 = 1096 := by rfl
      _ ≥ 4 ^ 5 := by numbers
  · calc d (k + 2) = 3 * d (k + 1) + 5 * d k := by rw [d]
      _ ≥ 3 * 4 ^ (k + 1) + 5 * 4 ^ k := by rel [IH1, IH2]
      _ = 16 * 4 ^ k + 4 ^ k := by ring
      _ ≥ 16 * 4 ^ k := by extra
      _ = 4 ^ (k + 2) := by ring

/-! # Exercises -/

def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · calc
      b 0 = 0 := by rw [b]
      _ = 3 ^ 0 - 2 ^ 0 := by numbers
  · calc
      b 1 = 1 := by rw [b]
      _ = 3 ^ 1 - 2 ^ 1 := by numbers
  · calc
      b (k + 2) = 5 * b (k + 1) - 6 * b k := by rw [b]
      _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1)) - 6 * (3 ^ k - 2 ^ k) := by rw [IH1, IH2]
      _ = 15 * 3 ^ k - 10 * 2 ^ k - 6 * 3 ^ k + 6 * 2 ^ k := by ring
      _ = 9 * 3 ^ k - 4 * 2 ^ k := by ring
      _ = 3 ^ (k + 2) - 2 ^ (k + 2) := by ring

def c : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c n

example (n : ℕ) : c n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  · calc
      c 0 = 3 := by rw [c]
      _ = 2 * 2 ^ 0 + (-2) ^ 0 := by numbers
  · calc
      c 1 = 2 := by rw [c]
      _ = 2 * 2 ^ 1 + (-2) ^ 1 := by numbers
  · calc
      c (k + 2) = 4 * c k := by rw [c]
      _ = 4 * (2 * 2 ^ k + (-2) ^ k) := by rw [IH1]
      _  = 2 * 2 ^ (k + 2) + (-2) ^ (k + 2) := by ring

def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k IH1 IH2
  · calc
      t 0 = 5 := by rw [t]
      _ = 2 * 0 + 5 := by numbers
  · calc
      t 1 = 7 := by rw [t]
      _ = 2 * 1 + 5 := by numbers
  · calc
      t (k + 2) = 2 * t (k + 1) - t k := by rw [t]
      _ = 2 * (2 * (k + 1) + 5) - (2 * k + 5) := by rw [IH1, IH2]
      _ = 4 * k + 4 + 10 - 2 * k - 5 := by ring
      _  = 2 * (k + 2) + 5 := by ring

def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

example (n : ℕ) : q n = n ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  · calc
      q 0 = 1 := by rw [q]
      _ = 0 ^ 3 + 1 := by numbers
  · calc
      q 1 = 2 := by rw [q]
      _ = 1 ^ 3 + 1 := by numbers
  · calc
      q (k + 2) = 2 * q (k + 1) - q k + 6 * k + 6 := by rw [q]
      _ = 2 * ((k + 1) ^ 3 + 1) - (k ^ 3 + 1) + 6 * k + 6 := by rw [IH1, IH2]
      _ = 2 * (k ^ 3 + 3 * k ^ 2 + 3 * k + 1 + 1) - k ^ 3 - 1 + 6 * k + 6 := by ring
      _ = k ^ 3 + 3 * k ^ 2 * 2 ^ 1 + 3 * k * 2 ^ 2 + 2 ^ 3 + 1 := by ring
      _ = (k + 2) ^ 3 + 1 := by ring

def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  have H :
      (s m ≡ 2 [ZMOD 5] ∧ s (m + 1) ≡ 3 [ZMOD 5])
    ∨ (s m ≡ 3 [ZMOD 5] ∧ s (m + 1) ≡ 2 [ZMOD 5]) := by
    simple_induction m with k IH
    · left
      constructor
      · calc
          s 0 = 2 := by rw [s]
          _ = 2 + 5 * 0 := by numbers
          _ ≡ 2 [ZMOD 5] := by extra
      · calc
          s 1 = 3 := by rw [s]
          _ = 3 + 5 * 0 := by numbers
          _ ≡ 3 [ZMOD 5] := by extra
    · obtain ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩ := IH
      · right
        constructor
        · apply ih2
        · calc
            s (k + 2) = 2 * s (k + 1) + 3 * s k := by rw [s]
            _ ≡ 2 * 3 + 3 * 2 [ZMOD 5] := by rel [ih2, ih1]
            _ = 2 + 5 * 2 := by numbers
            _ ≡ 2 [ZMOD 5] := by extra
      · left
        constructor
        · apply ih2
        · calc
            s (k + 2) = 2 * s (k + 1) + 3 * s k := by rw [s]
            _ ≡ 2 * 2 + 3 * 3 [ZMOD 5] := by rel [ih2, ih1]
            _ = 3 + 5 * 2 := by numbers
            _ ≡ 3 [ZMOD 5] := by extra
  obtain ⟨H1, -⟩ | ⟨H1, -⟩ := H
  · left
    apply H1
  · right
    apply H1

def p : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 6 * p (n + 1) - p n

#eval p 0 % 7
#eval p 1 % 7
#eval p 2 % 7
#eval p 3 % 7
#eval p 4 % 7
#eval p 5 % 7
#eval p 6 % 7
#eval p 7 % 7
#eval p 8 % 7

-- 2 3 2 2 3 2 2 3 2
--   3 2 2 3 2 2 3 2 2
--     2 2 3 2 2 3 2 2 3

-- 2 3 2 | 3 2 2 | 2 2 3

example (m : ℕ) : p m ≡ 2 [ZMOD 7] ∨ p m ≡ 3 [ZMOD 7] := by
  have H :
      (p m ≡ 2 [ZMOD 7]
          ∧ ((p (m + 1) ≡ 3 [ZMOD 7] ∧ p (m + 2) ≡ 2 [ZMOD 7])
              ∨ (p (m + 1) ≡ 2 [ZMOD 7] ∧ p (m + 2) ≡ 3 [ZMOD 7])))
      ∨ (p m ≡ 3 [ZMOD 7] ∧ p (m + 1) ≡ 2 [ZMOD 7] ∧ p (m + 2) ≡ 2 [ZMOD 7]) := by
    simple_induction m with k IH
    · left
      constructor
      · calc
          p 0 = 2 := by rw [p]
          _ = 2 + 7 * 0 := by numbers
          _ ≡ 2 [ZMOD 7] := by extra
      · left
        constructor
        · calc
            p 1 = 3 := by rw [p]
            _ = 3 + 7 * 0 := by numbers
            _ ≡ 3 [ZMOD 7] := by extra
        · calc
            p 2 = 6 * 3 - 2 := by repeat rw [p]
            _ = 2 + 7 * 2 := by numbers
            _ ≡ 2 [ZMOD 7] := by extra
    · obtain ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ | ⟨h1, h2, h3⟩ := IH
      · right
        constructor
        · apply h2
        · constructor
          · apply h3
          · calc
              p (k + 3) = 6 * p (k + 2) - p (k + 1) := by rw [p]
              _ ≡ 6 * 2 - 3 [ZMOD 7] := by rel [h2, h3]
              _ = 2 + 7 * 1 := by numbers
              _ ≡ 2 [ZMOD 7] := by extra
      · left
        constructor
        · apply h2
        · left
          constructor
          · apply h3
          · calc
              p (k + 3) = 6 * p (k + 2) - p (k + 1) := by rw [p]
              _ ≡ 6 * 3 - 2 [ZMOD 7] := by rel [h2, h3]
              _ = 2 + 7 * 2 := by numbers
              _ ≡ 2 [ZMOD 7] := by extra
      · left
        constructor
        · apply h2
        · right
          constructor
          · apply h3
          · calc
              p (k + 3) = 6 * p (k + 2) - p (k + 1) := by rw [p]
              _ ≡ 6 * 2 - 2 [ZMOD 7] := by rel [h2, h3]
              _ = 3 + 7 * 1 := by numbers
              _ ≡ 3 [ZMOD 7] := by extra
  obtain ⟨H1, -⟩ | ⟨H1, -⟩ := H
  · left
    apply H1
  · right
    apply H1

-- 2 3 2 2 3 2 2 3 2
--   3 2 2 3 2 2 3 2 2
--     2 2 3 2 2 3 2 2 3

-- 2 3 | 3 2 | 2 2 => we only need to track two !!
example (m : ℕ) : p m ≡ 2 [ZMOD 7] ∨ p m ≡ 3 [ZMOD 7] := by
  have H : ∀ n : ℕ,
      (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 3 [ZMOD 7])
      ∨ (p n ≡ 3 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7])
      ∨ (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7])
  · intro n
    simple_induction n with k IH
    · left
      constructor
      · calc p 0 = 2 := by rw [p]
          _ ≡ 2 [ZMOD 7] := by extra
      · calc p (0 + 1) = 3 := by rw [p]
          _ ≡ 3 [ZMOD 7] := by extra
    · obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ := IH
      · right; left
        constructor
        · apply h2
        · calc p (k + 2) = 6 * p (k + 1) - p k := by rw [p]
            _ ≡ 6 * 3 - 2 [ZMOD 7] := by rel [h1, h2]
            _ = 2 + 7 * 2 := by numbers
            _ ≡ 2 [ZMOD 7] := by extra
      · right; right
        constructor
        · apply h2
        · calc p (k + 2) = 6 * p (k + 1) - p k := by rw [p]
            _ ≡ 6 * 2 - 3 [ZMOD 7] := by rel [h1, h2]
            _ = 2 + 7 * 1 := by numbers
            _ ≡ 2 [ZMOD 7] := by extra
      · left
        constructor
        · apply h2
        · calc p (k + 2) = 6 * p (k + 1) - p k := by rw [p]
            _ ≡ 6 * 2 - 2 [ZMOD 7] := by rel [h1, h2]
            _ = 3 + 7 * 1 := by numbers
            _ ≡ 3 [ZMOD 7] := by extra
  obtain ⟨H1, -⟩ | ⟨H1, -⟩ | ⟨H1, -⟩ := H m
  · left; apply H1
  · right; apply H1
  · left; apply H1

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

#eval r 0 ≥ 2 ^ 0
#eval r 1 ≥ 2 ^ 1
#eval r 2 ≥ 2 ^ 2
#eval r 3 ≥ 2 ^ 3
#eval r 4 ≥ 2 ^ 4
#eval r 5 ≥ 2 ^ 5
#eval r 6 ≥ 2 ^ 6
#eval r 7 ≥ 2 ^ 7
#eval r 8 ≥ 2 ^ 8
#eval r 9 ≥ 2 ^ 9
#eval r 10 ≥ 2 ^ 10

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  dsimp
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · repeat rw [r]
    numbers
  · repeat rw [r]
    numbers
  · calc
      r (k + 2) = 2 * r (k + 1) + r k := by rw [r]
      _ ≥ 2 * 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ ≥ 2 * 2 ^ (k + 1) := by extra
      _ = 2 ^ (k + 2) := by ring

#eval (0.4:ℚ) * 1.6 ^ 0 < F 0 ∧ F 0 < (0.5:ℚ) * 1.7 ^ 0
#eval (0.4:ℚ) * 1.6 ^ 1 < F 1 ∧ F 1 < (0.5:ℚ) * 1.7 ^ 1
#eval (0.4:ℚ) * 1.6 ^ 2 < F 2 ∧ F 2 < (0.5:ℚ) * 1.7 ^ 2
#eval (0.4:ℚ) * 1.6 ^ 3 < F 3 ∧ F 3 < (0.5:ℚ) * 1.7 ^ 3
#eval (0.4:ℚ) * 1.6 ^ 4 < F 4 ∧ F 4 < (0.5:ℚ) * 1.7 ^ 4
#eval (0.4:ℚ) * 1.6 ^ 5 < F 4 ∧ F 5 < (0.5:ℚ) * 1.7 ^ 5
#eval (0.4:ℚ) * 1.6 ^ 6 < F 4 ∧ F 6 < (0.5:ℚ) * 1.7 ^ 6
#eval (0.4:ℚ) * 1.6 ^ 7 < F 4 ∧ F 7 < (0.5:ℚ) * 1.7 ^ 7
#eval (0.4:ℚ) * 1.6 ^ 8 < F 4 ∧ F 8 < (0.5:ℚ) * 1.7 ^ 8
#eval (0.4:ℚ) * 1.6 ^ 9 < F 4 ∧ F 9 < (0.5:ℚ) * 1.7 ^ 9
#eval (0.4:ℚ) * 1.6 ^ 10 < F 10 ∧ F 10 < (0.5:ℚ) * 1.7 ^ 10
#eval (0.4:ℚ) * 1.6 ^ 11 < F 11 ∧ F 11 < (0.5:ℚ) * 1.7 ^ 11

#eval F 10

example : forall_sufficiently_large n : ℕ,
    (0.4:ℚ) * 1.6 ^ n < F n ∧ F n < (0.5:ℚ) * 1.7 ^ n := by
  dsimp
  use 10
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · repeat rw [F]
    constructor
    · numbers
    · numbers
  · repeat rw [F]
    constructor
    · numbers
    · numbers
  · obtain ⟨h1, h1'⟩ := IH1
    obtain ⟨h2, h2'⟩ := IH2
    have hF : (F (k + 2) : ℚ) = F (k + 1) + F k := by
      rw [F]
      push_cast
      ring
    constructor
    · calc
        (F (k + 2) : ℚ) = F (k + 1) + F k := hF
        _ > 0.4 * 1.6 ^ (k + 1) + 0.4 * 1.6 ^ k := by rel [h2, h1]
        _ = 0.4 * 1.6 * 1.6 ^ k + 0.4 * 1.6 ^ k := by ring
        _ = 0.4 * (1.6 + 1) * 1.6 ^ k := by ring
        _ = 1.04 * 1.6 ^ k := by ring
        _ = 1.024 * 1.6 ^ k + 0.016 * 1.6 ^ k := by ring
        _ > 1.024 * 1.6 ^ k := by extra
        _ = 0.4 * 1.6 ^ 2 * 1.6 ^ k := by ring
        _ = 0.4 * 1.6 ^ (k + 2) := by ring
    · calc
        (F (k + 2) : ℚ) = F (k + 1) + F k := hF
        _ < 0.5 * 1.7 ^ (k + 1) + 0.5 * 1.7 ^ k := by rel [h2', h1']
        _ = 0.5 * 1.7 * 1.7 ^ k + 0.5 * 1.7 ^ k := by ring
        _ = 0.5 * (1.7 + 1) * 1.7 ^ k := by ring
        _ = 1.35 * 1.7 ^ k := by ring
        _ < 1.35 * 1.7 ^ k + 0.095 * 1.7 ^ k := by extra
        _ = 1.445 * 1.7 ^ k := by ring
        _ = 0.5 * 1.7 ^ 2 * 1.7 ^ k := by ring
        _ = 0.5 * 1.7 ^ (k + 2) := by ring
