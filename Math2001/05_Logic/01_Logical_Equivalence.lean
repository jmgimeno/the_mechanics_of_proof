/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true

example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction

example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP

#truth_table ¬(P ∧ ¬ Q)

#truth_table P ↔ (¬ P ∨ Q)

example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h

example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h
    · constructor
      · apply h1
      · left
        apply h2
    · constructor
      · apply h1
      · right
        apply h2

#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)

example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1 -- exact h1 x
  · apply h2

example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx

example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/

example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨hP, -⟩ := h
  left
  apply hP

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  · apply h1 h3
  · apply h2 h3

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro ⟨hP, hNotP⟩
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  intro hP
  rw [h1] at hP
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain hP | hQ := h1
  · apply hP
  · apply h2 hQ

example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨hpq, hqp⟩ := h
  constructor
  · intro ⟨hP, hR⟩
    constructor
    · apply hpq hP
    · apply hR
  · intro ⟨hQ, hR⟩
    constructor
    · apply hqp hQ
    · apply hR

example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  · intro ⟨hP, hp'⟩
    apply hP
  · intro hP
    constructor <;> apply hP

example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor <;>
  · rintro (h | h)
    · right
      apply h
    · left
      apply h

example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro h
    constructor
    · intro hP
      have : P ∨ Q := by left ; apply hP
      contradiction
    · intro hQ
      have : P ∨ Q := by right ; apply hQ
      contradiction
  · rintro ⟨hNotP, hNotQ⟩ (hP | hQ) <;> contradiction

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro a
  apply h1 a (h2 a)

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro ⟨a, hPa⟩
    obtain ⟨hPQ, -⟩ := h a
    use a
    apply hPQ hPa
  · intro ⟨a, hQa⟩
    obtain ⟨-, hQP⟩ := h a
    use a
    apply hQP hQa

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro ⟨a, b, hPab⟩
    use b
    use a
    apply hPab
  · intro ⟨b, a, hPab⟩
    use a
    use b
    apply hPab

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor <;> intro ⟨x, y, hP⟩ <;> use y, x <;> apply hP

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor <;> intro h <;> intro x y <;> apply h

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro ⟨⟨x, h1⟩, h2⟩
    use x
    constructor
    · apply h1
    · apply h2
  · intro ⟨x, ⟨h1, h2⟩⟩
    constructor
    · use x
      apply h1
    · apply h2
