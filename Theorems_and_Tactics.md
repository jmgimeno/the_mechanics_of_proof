# Theorems and tactics in *The Mechanics of Proof*, by section

Every tactic and every named lemma in the book's text (`html/01_*.html` to
`html/10_*.html`) and in the Lean files (`Math2001/01_*` to `Math2001/10_*`,
including the solutions written so far), listed under the section where
the book **first** introduces it. If you only want to use what the book has
already introduced, use the entries up to the section you are working on.

Each tactic entry gives a short description, whether it is specific to this
book (marked ★, so you won't find help for it online), the uses listed in the
book's [Index of Lean tactics](html/Index_of_Tactics.html) when it has an
entry, and the later sections where it appears again.

Each theorem entry gives:

- the full Lean name and its statement, as printed by Lean (`{braces}` are
  implicit arguments, `[brackets]` say which number systems it applies to,
  and `_` marks an unnamed hypothesis);
- where it first appears: in the book text, in the Lean file for that
  section, or both;
- where it comes from: Mathlib / Lean core, the course library
  (`Library/`), or a proof in one of the section files;
- the later sections where it appears again.

Caveats:

- Entries are found by name. A result the book describes only in words,
  without naming the Lean lemma, is not listed.
- The Lean files for Chapters 1–4 contain your solutions. A tactic or lemma
  that appears there before the book introduces it is listed under the
  book's section, with a note. Items that appear only in your solutions are
  marked "only in your solutions".

## Definitions

The course library's definitions behind the book's notation. They explain
why tactics like `use` and `obtain` work on these goals.

| Name | Definition | First used |
| --- | --- | --- |
| `Int.Even n`, `Nat.Even n` | `∃ k, n = 2 * k` | 3.1 |
| `Int.Odd n`, `Nat.Odd n` | `∃ k, n = 2 * k + 1` | 3.1 |
| `a ∣ b` (`Dvd.dvd`) | `∃ c, b = a * c` | 3.2 |
| `a ≡ b [ZMOD n]` (`Int.ModEq n a b`) | `n ∣ a - b` | 3.3 |
| `Prime p` | `2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p` | 4.1 |
| `s ⊆ t` (`Set.Subset`) | `∀ x, x ∈ s → x ∈ t` | 9.1 |

Notes:

- `Even n` and `2 ∣ n` unfold to the same statement, so a proof of one is
  accepted as a proof of the other.
- In `ℕ`, `a < b` is defined as `a + 1 ≤ b`. In particular, `0 < m` and
  `1 ≤ m` are the same statement.

## Chapter 1

### 1.1 Proving equalities

Nothing new.

### 1.2 Proving equalities in Lean

**Tactics:** `calc`, `ring`, `rw`, `sorry`

#### `calc` (tactic)

Proves an equality or inequality as a chain of steps `a = b`, `_ ≤ c`, …, each with its own justification.

- First appears in: book text and Lean file.
- Used regularly from here on (37 later sections).

#### `ring` (tactic)

Solves algebraic equality goals such as `(x + y) ^ 2 = x ^ 2 + 2xy + y ^ 2`, when the proof is effectively “expand out both sides and rearrange”.

- Index of tactics: first use: Section 1.2.
- First appears in: book text and Lean file.
- Used regularly from here on (37 later sections).

#### `rw` (tactic)

Substitution: looks for the left-hand side of a specified equality fact in the goal, and replaces it with the right-hand side of that fact.

- Index of tactics: first use: Section 1.2; for ↔ hypotheses/lemmas: Section 4.2.
- First appears in: book text and Lean file.
- Used regularly from here on (35 later sections).

#### `sorry` (tactic)

Placeholder that closes any goal without proving it. Lean warns "declaration uses 'sorry'". The exercises use it to mark what you have to fill in.

- First appears in: book text.
- Used regularly from here on (36 later sections).

### 1.3 Tips and tricks

**Tactics:** `repeat`

#### `repeat` (tactic)

Runs a tactic again and again until it fails, e.g. `repeat rw [h]`.

- First appears in: Lean file (only in your solutions).

### 1.4 Proving inequalities

**Tactics:** `extra`, `numbers`, `rel`

#### `extra` (tactic) ★

A comparison tactic for inequalities, or other relations such as congruences: checks an inequality whose two sides differ by the addition of a positive quantity, a congruence mod 3 whose two sides differ by a multiple of 3, etc.

- Index of tactics: first use: Section 1.4; for congruences: Section 3.4.
- First appears in: book text and Lean file.
- Used regularly from here on (24 later sections).

#### `numbers` (tactic) ★

Proves numeric facts, like `3 · 12 < 13 + 25` or `3 · 5+1=4 · 4`.

- Index of tactics: first use: Section 1.4; with at for contradictions: Section 4.4.
- First appears in: book text and Lean file.
- Used regularly from here on (29 later sections).

#### `rel` (tactic)

A “substitution-like” tactic for inequalities, or other relations such as congruences: looks for the left-hand side of a specified inequality (or congruence, …) fact in the goal, and replaces it with the right-hand side of that fact, if that replacement is “obviously” a valid inequality (or modular arithmetic, …) deduction. Compare with rw.

- Index of tactics: first use: Section 1.4; for congruences: Section 3.4; for logical equivalences: Section 5.3.
- First appears in: book text and Lean file.
- Used regularly from here on (19 later sections).

### 1.5 A shortcut

**Tactics:** `addarith`

#### `addarith` (tactic) ★

Attempts to solve an equality or inequality by moving terms from the left-hand side to the right-hand side, or vice versa.

- Index of tactics: first use: Section 1.5.
- First appears in: book text and Lean file.
- Used regularly from here on (16 later sections).

## Chapter 2

### 2.1 Intermediate steps

**Tactics:** `cancel`, `have`

#### `cancel` (tactic) ★

Cancels a common factor from LHS/RHS of equality/inequality, cancels an exponentiation common to both sides, etc.

- Index of tactics: first use: Section 2.1.
- First appears in: book text and Lean file.
- Used regularly from here on (12 later sections).

#### `have` (tactic)

Records a fact (followed by the proof of that fact), which then becomes available as an extra hypothesis.

- Index of tactics: first use: Section 2.1; with a lemma: Section 2.3; introducing a new goal: Section 2.4.
- First appears in: book text and Lean file.
- Used earlier in your solutions: 1.3.
- Used regularly from here on (31 later sections).

### 2.2 Invoking lemmas

**Tactics:** `apply`

#### `apply` (tactic)

Invokes a specified lemma or hypothesis to modify the goal.

- Index of tactics: first use: Section 2.2; for ∀ and → hypotheses, Section 4.1.
- First appears in: book text and Lean file.
- Used regularly from here on (31 later sections).

**Theorems:** `le_antisymm`, `ne_of_gt`, `ne_of_lt`

#### `le_antisymm`

```lean
le_antisymm {α : Type u} [PartialOrder α] {a b : α} (_ : a ≤ b) (_ : b ≤ a) : a = b
```

Proves an equality from two inequalities.

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.
- Appears again in: 2.4, 4.1, 4.2, 4.3, 4.4, 6.7, 8.4, 10.1.

#### `ne_of_gt`

```lean
ne_of_gt {α : Type u} [Preorder α] {a b : α} (h : b < a) : a ≠ b
```

Note the order: `b < a` gives `a ≠ b`.

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.
- Appears again in: 2.3, 2.5, 7.3, 8.1, 8.2, 9.3.

#### `ne_of_lt`

```lean
ne_of_lt {α : Type u} [Preorder α] {a b : α} (h : a < b) : a ≠ b
```

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.
- Appears again in: 2.3, 2.5, 5.3.

### 2.3 “Or” and proof by cases

**Tactics:** `left`, `obtain`, `right`

#### `left` (tactic)

Selects the left alternative of an “or” goal (∨).

- Index of tactics: first use: Section 2.3.
- First appears in: book text and Lean file.
- Used regularly from here on (13 later sections).

#### `obtain` (tactic)

Takes apart a hypothesis of the form “or” (∨), “and” (∧) or “there exists” (∃).

- Index of tactics: first use for ∨: Section 2.3; for ∧: Section 2.4; for ∃: Section 2.5.
- First appears in: book text and Lean file.
- Used regularly from here on (30 later sections).

#### `right` (tactic)

Selects the right alternative of an “or” goal (∨).

- Index of tactics: first use: Section 2.3.
- First appears in: book text and Lean file.
- Used regularly from here on (14 later sections).

**Theorems:** `eq_zero_or_eq_zero_of_mul_eq_zero`, `sq_ne_two`

#### `eq_zero_or_eq_zero_of_mul_eq_zero`

```lean
eq_zero_or_eq_zero_of_mul_eq_zero {M₀ : Type u_4} [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀} (_ : a * b = 0) : a = 0 ∨ b = 0
```

Used after factoring, e.g. `(x + 3) * (x - 2) = 0`.

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.
- Appears again in: 2.4, 4.2.

#### `sq_ne_two`

```lean
sq_ne_two (n : ℤ) : n ^ 2 ≠ 2
```

No integer squares to 2. Recorded in the book for later use.

- First appears in: book text.
- Source: course library (`Library/Theory/NumberTheory.lean`).
- Appears again in: 7.3.

### 2.4 “And”

**Tactics:** `constructor`

#### `constructor` (tactic)

Splits an “and” goal (∧) into sub-goals for its left and right parts.

- Index of tactics: first use: Section 2.4; for ↔ goals: Section 4.2.
- First appears in: book text and Lean file.
- Used regularly from here on (25 later sections).

**Theorems:** `abs_le_of_sq_le_sq'`

#### `abs_le_of_sq_le_sq'`

```lean
abs_le_of_sq_le_sq' {R : Type u_2} [LinearOrderedRing R] {x y : R} (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : -y ≤ x ∧ x ≤ y
```

Needs `0 ≤ y`. The result is a conjunction, so it is usually followed by `obtain ⟨h1, h2⟩ := ...`.

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.
- Appears again in: 4.1, 4.2.

### 2.5 Existence proofs

**Tactics:** `exists`, `use`

#### `exists` (tactic)

Lean core's version of `use`: gives the witnesses for an `∃` goal and then tries to close what is left.

- First appears in: Lean file (only in your solutions).

#### `use` (tactic)

Provides a witness to an existential goal (∃).

- Index of tactics: first use: Section 2.5.
- First appears in: book text and Lean file.
- Used regularly from here on (29 later sections).

**Theorems:** `le_or_gt`

#### `le_or_gt`

```lean
le_or_gt {α : Type u} [LinearOrder α] (a b : α) : a ≤ b ∨ a > b
```

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.

## Chapter 3

### 3.1 Definitions; parity

**Tactics:** `dsimp`

#### `dsimp` (tactic)

Unfolds a definition. Typically used while working on a proof rather than in the final version; it is useful for inspecting a goal or hypothesis more carefully, but in most cases the proof will still work after a dsimp line is deleted.

- Index of tactics: first use: Section 3.1.
- First appears in: book text.
- Used regularly from here on (19 later sections).

**Theorems:** `Int.even_or_odd`

#### `Int.even_or_odd`

```lean
Int.even_or_odd (n : ℤ) : Int.Even n ∨ Int.Odd n
```

Written `even_or_odd n`; Lean picks the `ℤ` or `ℕ` version from the type of `n`.

Written in the book or code as `even_or_odd`.

- First appears in: book text and Lean file.
- Source: course library (`Library/Theory/Parity.lean`).
- Appears again in: 4.5.

### 3.2 Divisibility

**Tactics:** `exact`

#### `exact` (tactic)

Closes the goal with a term whose type is exactly the goal, e.g. `exact h`. The book itself uses `apply` for this.

- First appears in: Lean file (only in your solutions).
- Appears again in: 3.3, 3.5, 4.1, 4.2, 4.4.

**Theorems:** `Int.not_dvd_of_exists_lt_and_lt`, `Nat.le_of_dvd`, `Nat.pos_of_dvd_of_pos`

#### `Int.not_dvd_of_exists_lt_and_lt`

```lean
Int.not_dvd_of_exists_lt_and_lt (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a
```

Shows `b ∤ a` by finding `a` strictly between two consecutive multiples of `b`.

Written in the book or code as `not_dvd_of_exists_lt_and_lt`.

- First appears in: book text and Lean file.
- Source: course library (`Library/Theory/Division.lean`).
- Appears again in: 4.5.

#### `Nat.le_of_dvd`

```lean
Nat.le_of_dvd {m n : ℕ} (h : 0 < n) (_ : m ∣ n) : m ≤ n
```

The positivity argument comes first.

- First appears in: book text.
- Source: Mathlib / Lean core.
- Appears again in: 4.1, 4.4, 10.1.

#### `Nat.pos_of_dvd_of_pos`

```lean
Nat.pos_of_dvd_of_pos {m n : ℕ} (H1 : m ∣ n) (H2 : 0 < n) : 0 < m
```

In `ℕ`, `0 < m` is the same statement as `1 ≤ m`, so the result can be used where `1 ≤ m` is expected.

- First appears in: book text.
- Source: Mathlib / Lean core.
- Appears again in: 4.1, 4.4.

### 3.3 Modular arithmetic: theory

**Theorems:** `Int.ModEq.add`, `Int.ModEq.mul`, `Int.ModEq.neg`, `Int.ModEq.pow`, `Int.ModEq.pow_three`, `Int.ModEq.pow_two`, `Int.ModEq.refl`, `Int.ModEq.sub`, `Int.ModEq.symm`, `Int.ModEq.trans`

#### `Int.ModEq.add`

```lean
Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n]
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/03_Parity_and_Divisibility/03_Modular_Arithmetic_Theory.lean`); also in the course library.
- Appears again in: 3.4.

#### `Int.ModEq.mul`

```lean
Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n]
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/03_Parity_and_Divisibility/03_Modular_Arithmetic_Theory.lean`); also in the course library.
- Appears again in: 3.4.

#### `Int.ModEq.neg`

```lean
Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n]
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/03_Parity_and_Divisibility/03_Modular_Arithmetic_Theory.lean`); also in the course library.
- Appears again in: 3.4.

#### `Int.ModEq.pow`

```lean
Int.ModEq.pow {n a b : ℤ} (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n]
```

Written in the book or code as `Int.modEq.pow`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/03_Parity_and_Divisibility/03_Modular_Arithmetic_Theory.lean`); also in the course library.
- Appears again in: 3.4, 6.1.

#### `Int.ModEq.pow_three`

```lean
Int.ModEq.pow_three (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n]
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/03_Parity_and_Divisibility/03_Modular_Arithmetic_Theory.lean`).

#### `Int.ModEq.pow_two`

```lean
Int.ModEq.pow_two (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n]
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/03_Parity_and_Divisibility/03_Modular_Arithmetic_Theory.lean`).

#### `Int.ModEq.refl`

```lean
Int.ModEq.refl {n : ℤ} (a : ℤ) : a ≡ a [ZMOD n]
```

These `Int.ModEq` lemmas are what `rel` uses behind the scenes for congruences.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/03_Parity_and_Divisibility/03_Modular_Arithmetic_Theory.lean`); also in the course library.
- Appears again in: 3.4, 10.2.

#### `Int.ModEq.sub`

```lean
Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) : a - c ≡ b - d [ZMOD n]
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/03_Parity_and_Divisibility/03_Modular_Arithmetic_Theory.lean`); also in the course library.
- Appears again in: 3.4.

#### `Int.ModEq.symm`

```lean
Int.ModEq.symm {n a b : ℤ} (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n]
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/03_Parity_and_Divisibility/03_Modular_Arithmetic_Theory.lean`); also in the course library.
- Appears again in: 10.2.

#### `Int.ModEq.trans`

```lean
Int.ModEq.trans {n a b c : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n]
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/03_Parity_and_Divisibility/03_Modular_Arithmetic_Theory.lean`); also in the course library.
- Appears again in: 10.2.

### 3.4 Modular arithmetic: calculations

**Tactics:** `mod_cases`

#### `mod_cases` (tactic)

Introduces cases for a variable according to its residue modulo a specified number.

- Index of tactics: first use: Section 3.4.
- First appears in: book text and Lean file.
- Appears again in: 4.2, 4.3, 4.4, 4.5, 6.6.

### 3.5 Bézout’s identity

Nothing new.

## Chapter 4

### 4.1 “For all” and implication

**Tactics:** `interval_cases`, `intro`

#### `interval_cases` (tactic)

Given a natural-number or integer variable `n` for which numeric upper and lower bounds are available, produce cases for each of the numeric possibilities for `n`.

- Index of tactics: first use: Section 4.1.
- First appears in: book text and Lean file.
- Appears again in: 4.2, 4.3, 4.4, 4.5, 6.2, 9.2.

#### `intro` (tactic)

Introduces a universally quantified variable (∀) or the antecedent of an implication (→) from the goal, or assumes (for the sake of contradiction) the positive version of a negation (¬) goal.

- Index of tactics: first use: Section 4.1; for ¬ goals: Section 4.5.
- First appears in: book text and Lean file.
- Used regularly from here on (20 later sections).

**Theorems:** `not_prime`, `prime_two`

#### `not_prime`

```lean
not_prime {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) : ¬Prime p
```

Give a factorisation `p = k * l` with `k ≠ 1` and `k ≠ p`.

- First appears in: book text and Lean file.
- Source: course library (`Library/Theory/Prime.lean`).
- Appears again in: 5.2.

#### `prime_two`

```lean
prime_two : Prime 2
```

- First appears in: book text.
- Source: course library (`Library/Theory/Prime.lean`).
- Appears again in: 5.2.

### 4.2 “If and only if”

**Tactics:** `norm_num`

#### `norm_num` (tactic)

Mathlib's numeric normalisation tactic, on which `numbers` is built. It can do more than the book allows `numbers` to do, e.g. prove `0 = 0 ∨ 0 = 1`.

- First appears in: Lean file (only in your solutions).

**Theorems:** `Int.dvd_iff_modEq`, `Int.even_iff_modEq`, `Int.odd_iff_modEq`, `lt_of_lt_of_le`, `mul_eq_zero`

#### `Int.dvd_iff_modEq`

```lean
Int.dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n]
```

Proved in an exercise; not in the course library, so only available in that file.

Written in the book or code as `dvd_iff_modEq`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/04_Proofs_with_Structure_II/02_Iff.lean`).

#### `Int.even_iff_modEq`

```lean
Int.even_iff_modEq (n : ℤ) : Int.Even n ↔ n ≡ 0 [ZMOD 2]
```

Written in the book or code as `even_iff_modEq`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/04_Proofs_with_Structure_II/02_Iff.lean`); also in the course library.
- Appears again in: 4.5.

#### `Int.odd_iff_modEq`

```lean
Int.odd_iff_modEq (n : ℤ) : Int.Odd n ↔ n ≡ 1 [ZMOD 2]
```

Written in the book or code as `odd_iff_modEq`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/04_Proofs_with_Structure_II/02_Iff.lean`); also in the course library.
- Appears again in: 4.5.

#### `lt_of_lt_of_le`

```lean
lt_of_lt_of_le {α : Type u} [Preorder α] {a b c : α} (_ : a < b) (_ : b ≤ c) : a < c
```

- First appears in: Lean file (only in your solutions).
- Source: Mathlib / Lean core.

#### `mul_eq_zero`

```lean
mul_eq_zero {M₀ : Type u_1} [MulZeroClass M₀] [NoZeroDivisors M₀] {a b : M₀} : a * b = 0 ↔ a = 0 ∨ b = 0
```

The `↔` version of `eq_zero_or_eq_zero_of_mul_eq_zero`, convenient with `rw [mul_eq_zero] at h`.

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.
- Appears again in: 4.4, 8.1, 9.1.

### 4.3 “There exists a unique”

**Theorems:** `Int.existsUnique_modEq_lt`, `sq_le_sq'`

#### `Int.existsUnique_modEq_lt`

```lean
Int.existsUnique_modEq_lt (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃! r, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b]
```

The theory behind `mod_cases`.

- First appears in: book text.
- Source: course library (`Library/Theory/ModEq/Lemmas.lean`).
- Appears again in: 4.4, 6.6.

#### `sq_le_sq'`

```lean
sq_le_sq' {R : Type u_2} [LinearOrderedRing R] {x y : R} (h1 : -y ≤ x) (h2 : x ≤ y) : x ^ 2 ≤ y ^ 2
```

Squares a two-sided bound; the converse of `abs_le_of_sq_le_sq'`.

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.

### 4.4 Contradictory hypotheses

**Tactics:** `<;>`, `contradiction`

#### `<;>` (tactic)

Combinator: `t₁ <;> t₂` runs `t₂` on every goal produced by `t₁`.

- First appears in: book text and Lean file.
- Used earlier in your solutions: 4.2.
- Appears again in: 4.5, 6.6, 6.7, 8.1, 8.2, 8.3, 9.1, 9.2, 10.1.

#### `contradiction` (tactic)

If there are two contradictory hypotheses available, this concludes the proof.

- Index of tactics: first use: Section 4.4.
- First appears in: book text and Lean file.
- Appears again in: 4.5, 5.1, 5.2, 5.3, 7.1, 7.3, 8.2, 8.4, 9.2, 9.3.

**Theorems:** `eq_or_lt_of_le`, `le_or_lt`, `Nat.not_dvd_of_exists_lt_and_lt`, `not_lt_of_ge`, `prime_test`

#### `eq_or_lt_of_le`

```lean
eq_or_lt_of_le {α : Type u} [PartialOrder α] {a b : α} (h : a ≤ b) : a = b ∨ a < b
```

Splits a `≤` into the "equal" and "strictly less" cases.

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.
- Appears again in: 6.2.

#### `le_or_lt`

```lean
le_or_lt {α : Type u} [LinearOrder α] (a b : α) : a ≤ b ∨ b < a
```

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.
- Appears again in: 7.1, 8.4, 9.2.

#### `Nat.not_dvd_of_exists_lt_and_lt`

```lean
Nat.not_dvd_of_exists_lt_and_lt (a b : ℕ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a
```

- First appears in: book text and Lean file.
- Source: course library (`Library/Theory/Division.lean`).
- Appears again in: 4.5, 7.1, 9.1, 10.1.

#### `not_lt_of_ge`

```lean
not_lt_of_ge {α : Type u} [Preorder α] {a b : α} (h : a ≥ b) : ¬a < b
```

Turns an inequality into a negated one, for use with `contradiction`.

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.

#### `prime_test`

```lean
prime_test {p : ℕ} (hp : 2 ≤ p) (H : ∀ (m : ℕ), 1 < m → m < p → ¬m ∣ p) : Prime p
```

Usually combined with `interval_cases m` and `Nat.not_dvd_of_exists_lt_and_lt`.

- First appears in: book text and Lean file.
- Source: course library (`Library/Theory/Prime.lean`).
- Appears again in: 4.5, 5.3.

### 4.5 Proof by contradiction

**Theorems:** `better_prime_test`, `Int.even_iff_not_odd`, `lt_or_le`, `not_prime_one`

#### `better_prime_test`

```lean
better_prime_test {p : ℕ} (hp : 2 ≤ p) (T : ℕ) (hTp : p < T ^ 2) (H : ∀ (m : ℕ), 1 < m → m < T → ¬m ∣ p) : Prime p
```

Only checks divisors below `T`, where `T ^ 2 > p` (roughly `√p`).

- First appears in: book text and Lean file.
- Source: course library (`Library/Theory/Prime.lean`).
- Appears again in: 5.2.

#### `Int.even_iff_not_odd`

```lean
Int.even_iff_not_odd (n : ℤ) : Int.Even n ↔ ¬Int.Odd n
```

Written in the book or code as `even_iff_not_odd`.

- First appears in: book text.
- Source: course library (`Library/Theory/Parity.lean`).
- Appears again in: 9.1.

#### `lt_or_le`

```lean
lt_or_le {α : Type u} [LinearOrder α] (a b : α) : a < b ∨ b ≤ a
```

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.

#### `not_prime_one`

```lean
not_prime_one : ¬Prime 1
```

- First appears in: book text.
- Source: course library (`Library/Theory/Prime.lean`).
- Appears again in: 5.2.

## Chapter 5

### 5.1 Logical equivalence

**Tactics:** `#truth_table`

#### `#truth_table` (tactic) ★

Not a tactic: a command that prints the truth table of a propositional formula, e.g. `#truth_table ¬(P ∧ ¬Q)`.

- First appears in: book text and Lean file.

**Theorems:** `not_or`

#### `not_or`

```lean
not_or {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q
```

- First appears in: book text.
- Source: Mathlib / Lean core.
- Appears again in: 5.3.

### 5.2 The law of the excluded middle

**Tactics:** `by_cases`, `conv`

#### `by_cases` (tactic)

Case-splits on whether a given statement is true or false.

- Index of tactics: first use: Section 5.2.
- First appears in: book text and Lean file.
- Appears again in: 5.3, 6.4, 8.1, 9.3.

#### `conv` (tactic)

Works on part of a goal or hypothesis, e.g. `conv at h => numbers` simplifies only `h`.

- First appears in: book text and Lean file.
- Appears again in: 9.3.

**Theorems:** `not_superpowered_three`, `not_superpowered_zero`, `superpowered_one`

#### `not_superpowered_three`

```lean
not_superpowered_three : ¬ Superpowered 3
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/05_Logic/02_Excluded_Middle.lean`).

#### `not_superpowered_zero`

```lean
not_superpowered_zero : ¬ Superpowered 0
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/05_Logic/02_Excluded_Middle.lean`).

#### `superpowered_one`

```lean
superpowered_one : Superpowered 1
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/05_Logic/02_Excluded_Middle.lean`).

### 5.3 Normal form for negations

**Tactics:** `push_neg`

#### `push_neg` (tactic)

Converts a hypothesis or goal to a logically equivalent form with negations pushed inwards as far as possible.

- Index of tactics: first use: Section 5.3.
- First appears in: book text and Lean file.
- Appears again in: 6.6, 6.7, 8.1, 8.2, 8.4, 9.1, 9.3, 10.1.

**Theorems:** `Classical.not_forall`, `Classical.not_not`, `exists_factor_of_not_prime`, `not_and_or`, `not_exists`, `not_imp`, `not_lt`

#### `Classical.not_forall`

```lean
Classical.not_forall {α : Sort u_1} {p : α → Prop} : (¬∀ (x : α), p x) ↔ ∃ x, ¬p x
```

Written in the book or code as `not_forall`.

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.

#### `Classical.not_not`

```lean
Classical.not_not {a : Prop} : ¬¬a ↔ a
```

Written in the book or code as `not_not`.

- First appears in: book text.
- Source: Mathlib / Lean core.

#### `exists_factor_of_not_prime`

```lean
exists_factor_of_not_prime {p : ℕ} (hp : ¬Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p
```

- First appears in: book text.
- Source: course library (`Library/Theory/Prime.lean`).
- Appears again in: 6.4.

#### `not_and_or`

```lean
not_and_or {a b : Prop} : ¬(a ∧ b) ↔ ¬a ∨ ¬b
```

- First appears in: book text.
- Source: Mathlib / Lean core.

#### `not_exists`

```lean
not_exists {α : Sort u_1} {p : α → Prop} : (¬∃ x, p x) ↔ ∀ (x : α), ¬p x
```

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.

#### `not_imp`

```lean
not_imp {a b : Prop} : ¬(a → b) ↔ a ∧ ¬b
```

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.

#### `not_lt`

```lean
not_lt {α : Type u} [LinearOrder α] {a b : α} : ¬a < b ↔ b ≤ a
```

- First appears in: book text.
- Source: Mathlib / Lean core.
- Appears again in: 8.4.

## Chapter 6

### 6.1 Introduction

**Tactics:** `induction_from_starting_point`, `simple_induction`

#### `induction_from_starting_point` (tactic) ★

Induction starting at a given number `a`: prove the statement for `a`, then from `n` to `n + 1` for `n ≥ a`.

- First appears in: book text and Lean file.
- Appears again in: 6.3, 7.2, 8.4.

#### `simple_induction` (tactic) ★

Induction on a natural number: prove the statement for `0`, then from `n` to `n + 1`.

- First appears in: book text and Lean file.
- Appears again in: 6.2, 6.3, 9.3.

**Theorems:** `Nat.even_of_pow_even`, `Nat.Odd.pow`

#### `Nat.even_of_pow_even`

```lean
Nat.even_of_pow_even {a n : ℕ} (ha : Nat.Even (a ^ n)) : Nat.Even a
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/01_Induction.lean`); also in the course library.
- Appears again in: 7.3.

#### `Nat.Odd.pow`

```lean
Nat.Odd.pow {a : ℕ} (ha : Nat.Odd a) (n : ℕ) : Nat.Odd (a ^ n)
```

Written in the book or code as `Odd.pow`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/01_Induction.lean`); also in the course library.

### 6.2 Recurrence relations

**Theorems:** `Nat.dvd_factorial`, `Nat.factorial_pos`

#### `Nat.dvd_factorial`

```lean
Nat.dvd_factorial {m n : ℕ} (_ : 0 < m) (_ : m ≤ n) : m ∣ Nat.factorial n
```

Written in the book or code as `dvd_factorial`.

- First appears in: book text.
- Source: Mathlib / Lean core.
- Appears again in: 7.1.

#### `Nat.factorial_pos`

```lean
Nat.factorial_pos (n : ℕ) : 0 < Nat.factorial n
```

Written in the book or code as `factorial_pos`.

- First appears in: book text.
- Source: Mathlib / Lean core.
- Appears again in: 6.5, 7.1.

### 6.3 Two-step induction

**Tactics:** `rfl`, `two_step_induction`, `two_step_induction_from_starting_point`

#### `rfl` (tactic)

Closes a goal of the form `a = a`, also when both sides are equal by definition.

- First appears in: book text and Lean file.
- Used earlier in your solutions: 4.2.
- Appears again in: 8.2, 8.3, 8.4, 10.2.

#### `two_step_induction` (tactic) ★

Induction with two base cases, `0` and `1`, and a step that uses both `n` and `n + 1` to get `n + 2`.

- First appears in: book text and Lean file.

#### `two_step_induction_from_starting_point` (tactic) ★

Two-step induction starting at a given number instead of `0`.

- First appears in: book text and Lean file.

### 6.4 Strong induction

**Theorems:** `F_bound`, `Nat.even_or_odd`, `Nat.exists_prime_factor`, `Nat.extract_pow_two`

#### `F_bound`

```lean
F_bound (n : ℕ) : F n ≤ 2 ^ n
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/04_Strong_Induction.lean`).

#### `Nat.even_or_odd`

```lean
Nat.even_or_odd (n : ℕ) : Nat.Even n ∨ Nat.Odd n
```

Written in the book or code as `even_or_odd`.

- First appears in: book text.
- Source: course library (`Library/Theory/Parity.lean`).
- Used earlier in your solutions: 4.4.

#### `Nat.exists_prime_factor`

```lean
Nat.exists_prime_factor {n : ℕ} (hn2 : 2 ≤ n) : ∃ p : ℕ, Prime p ∧ p ∣ n
```

Written in the book or code as `exists_prime_factor`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/04_Strong_Induction.lean`).
- Appears again in: 7.1.

#### `Nat.extract_pow_two`

```lean
Nat.extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x
```

Written in the book or code as `extract_pow_two`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/04_Strong_Induction.lean`).

### 6.5 Pascal’s triangle

**Tactics:** `field_simp`, `norm_cast`, `termination_by`

#### `field_simp` (tactic)

Clears denominators in equalities with fractions.

- First appears in: book text and Lean file.

#### `norm_cast` (tactic)

Simplifies statements involving casts between number systems, e.g. moving `(↑(a + b) : ℤ)` to `↑a + ↑b`.

- First appears in: book text and Lean file.
- Appears again in: 7.2.

#### `termination_by` (tactic)

Not a tactic: a clause placed after a recursive definition or proof to say which quantity decreases, so Lean accepts the recursion.

- First appears in: book text and Lean file.
- Appears again in: 6.6, 6.7, 7.3.

**Theorems:** `pascal_eq`, `pascal_le`, `pascal_symm`

#### `pascal_eq`

```lean
pascal_eq (a b : ℕ) : pascal a b * a ! * b ! = (a + b)!
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/05_Pascal.lean`).

#### `pascal_le`

```lean
pascal_le (a b : ℕ) : pascal a b ≤ (a + b)!
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/05_Pascal.lean`).

#### `pascal_symm`

```lean
pascal_symm (m n : ℕ) : pascal m n = pascal n m
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/05_Pascal.lean`).

### 6.6 The Division Algorithm

**Tactics:** `split_ifs`

#### `split_ifs` (tactic)

Case-splits on the conditions of `if … then … else` expressions in the goal.

- First appears in: book text and Lean file.
- Appears again in: 6.7.

**Theorems:** `fmod_add_fdiv`, `fmod_lt_of_pos`, `fmod_nonneg_of_pos`, `lt_fmod_of_neg`, `lt_of_le_of_ne`, `T_eq`

#### `fmod_add_fdiv`

```lean
fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/06_Division_Algorithm.lean`).
- Appears again in: 6.7.

#### `fmod_lt_of_pos`

```lean
fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/06_Division_Algorithm.lean`).
- Appears again in: 6.7.

#### `fmod_nonneg_of_pos`

```lean
fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/06_Division_Algorithm.lean`).
- Appears again in: 6.7.

#### `lt_fmod_of_neg`

```lean
lt_fmod_of_neg (n : ℤ) {d : ℤ} (hd : d < 0) : d < fmod n d
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/06_Division_Algorithm.lean`).

#### `lt_of_le_of_ne`

```lean
lt_of_le_of_ne {α : Type u} [PartialOrder α] {a b : α} (_ : a ≤ b) (_ : a ≠ b) : a < b
```

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.

#### `T_eq`

```lean
T_eq (n : ℤ) : T n = n ^ 2
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/06_Division_Algorithm.lean`).

### 6.7 The Euclidean algorithm

**Tactics:** `set`

#### `set` (tactic)

Gives a name to an expression and replaces it everywhere, e.g. `set y := x + 1 with hy`.

- First appears in: book text and Lean file.
- Appears again in: 7.3, 10.2.

**Theorems:** `Euclid.gcd_dvd`, `Euclid.gcd_dvd_left`, `Euclid.gcd_dvd_right`, `Euclid.gcd_maximal`, `Euclid.gcd_nonneg`, `Euclid.L_mul_add_R_mul`, `Euclid.lower_bound_fmod1`, `Euclid.lower_bound_fmod2`, `Euclid.upper_bound_fmod1`, `Euclid.upper_bound_fmod2`

#### `Euclid.gcd_dvd`

```lean
Euclid.gcd_dvd (a b : ℤ) : gcd a b ∣ b ∧ gcd a b ∣ a
```

Written in the book or code as `gcd_dvd`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/07_Euclidean_Algorithm.lean`).

#### `Euclid.gcd_dvd_left`

```lean
Euclid.gcd_dvd_left (a b : ℤ) : gcd a b ∣ a
```

Written in the book or code as `gcd_dvd_left`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/07_Euclidean_Algorithm.lean`).
- Appears again in: 7.2, 7.3.

#### `Euclid.gcd_dvd_right`

```lean
Euclid.gcd_dvd_right (a b : ℤ) : gcd a b ∣ b
```

Written in the book or code as `gcd_dvd_right`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/07_Euclidean_Algorithm.lean`).
- Appears again in: 7.2, 7.3.

#### `Euclid.gcd_maximal`

```lean
Euclid.gcd_maximal {d a b : ℤ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ gcd a b
```

Written in the book or code as `gcd_maximal`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/07_Euclidean_Algorithm.lean`).

#### `Euclid.gcd_nonneg`

```lean
Euclid.gcd_nonneg (a b : ℤ) : 0 ≤ gcd a b
```

Written in the book or code as `gcd_nonneg`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/07_Euclidean_Algorithm.lean`).
- Appears again in: 7.2.

#### `Euclid.L_mul_add_R_mul`

```lean
Euclid.L_mul_add_R_mul (a b : ℤ) : L a b * a + R a b * b = gcd a b
```

Written in the book or code as `L_mul_add_R_mul`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/07_Euclidean_Algorithm.lean`).

#### `Euclid.lower_bound_fmod1`

```lean
Euclid.lower_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : -b < fmod a b
```

Written in the book or code as `lower_bound_fmod1`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/07_Euclidean_Algorithm.lean`).

#### `Euclid.lower_bound_fmod2`

```lean
Euclid.lower_bound_fmod2 (a b : ℤ) (h1 : b < 0) : b < fmod a (-b)
```

Written in the book or code as `lower_bound_fmod2`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/07_Euclidean_Algorithm.lean`).

#### `Euclid.upper_bound_fmod1`

```lean
Euclid.upper_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : fmod a b < b
```

Written in the book or code as `upper_bound_fmod1`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/07_Euclidean_Algorithm.lean`).

#### `Euclid.upper_bound_fmod2`

```lean
Euclid.upper_bound_fmod2 (a b : ℤ) (h1 : b < 0) : fmod a (-b) < -b
```

Written in the book or code as `upper_bound_fmod2`.

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/06_Induction/07_Euclidean_Algorithm.lean`).

## Chapter 7

### 7.1 Infinitely many primes

Nothing new.

### 7.2 Gauss’ and Euclid’s lemmas

**Tactics:** `lift`

#### `lift` (tactic)

Turns an integer variable known to be nonnegative into a natural number.

- First appears in: book text and Lean file.

**Theorems:** `euclid_lemma`, `euclid_lemma_pow`, `gauss_lemma`

#### `euclid_lemma`

```lean
euclid_lemma {a b p : ℕ} (hp : Prime p) (H : p ∣ a * b) : p ∣ a ∨ p ∣ b
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/07_Number_Theory/02_Euclid_Lemma.lean`).

#### `euclid_lemma_pow`

```lean
euclid_lemma_pow (a k p : ℕ) (hp : Prime p) (hk : 1 ≤ k) (H : p ∣ a ^ k) : p ∣ a
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/07_Number_Theory/02_Euclid_Lemma.lean`).

#### `gauss_lemma`

```lean
gauss_lemma {d a b : ℤ} (h1 : d ∣ a * b) (h2 : gcd a d = 1) : d ∣ b
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/07_Number_Theory/02_Euclid_Lemma.lean`).

### 7.3 The square root of two

**Theorems:** `irrat_aux`, `irrat_aux_wf`

#### `irrat_aux`

```lean
irrat_aux (a b : ℕ) (hb : b ≠ 0) : a ^ 2 ≠ 2 * b ^ 2
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/07_Number_Theory/03_Sqrt_Two.lean`).

#### `irrat_aux_wf`

```lean
irrat_aux_wf (b k : ℕ) (hb : k ≠ 0) (hab : b ^ 2 = 2 * k ^ 2) : k < b
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/07_Number_Theory/03_Sqrt_Two.lean`).

## Chapter 8

### 8.1 Injectivity and surjectivity

**Tactics:** `cases`, `exhaust`

#### `cases` (tactic)

Case analysis on a variable of a finite type or on a hypothesis, producing one goal per constructor.

- First appears in: book text and Lean file.
- Appears again in: 8.2, 8.3, 10.1.

#### `exhaust` (tactic) ★

Proves true statements built from `∧`, `∨`, `¬`, `→` and equalities between explicit values by checking all the cases.

- First appears in: book text and Lean file.
- Appears again in: 8.2, 8.3, 9.2, 9.3, 10.1.

**Theorems:** `lt_trichotomy`, `surjective_of_intertwining`

#### `lt_trichotomy`

```lean
lt_trichotomy {α : Type u} [LinearOrder α] (a b : α) : a < b ∨ a = b ∨ b < a
```

- First appears in: book text.
- Source: Mathlib / Lean core.

#### `surjective_of_intertwining`

```lean
surjective_of_intertwining {X : Sort u_1} {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X} (hi : ∀ (x : X), f (i x) = f x + 1) : Function.Surjective f
```

- First appears in: book text.
- Source: course library (`Library/Theory/InjectiveSurjective.lean`).
- Appears again in: 8.4.

### 8.2 Bijectivity

Nothing new.

### 8.3 Composition of functions

**Tactics:** `choose`, `ext`

#### `choose` (tactic)

From `h : ∀ x, ∃ y, P x y`, produces a function `g` with `∀ x, P x (g x)`.

- First appears in: book text and Lean file.

#### `ext` (tactic)

Proves two functions or two sets equal by showing they agree at every element.

- First appears in: book text and Lean file.
- Appears again in: 8.4, 9.1, 9.2, 9.3, 10.2.

**Theorems:** `bijective_iff_exists_inverse`, `bijective_of_inverse`, `exists_inverse_of_bijective`

#### `bijective_iff_exists_inverse`

```lean
bijective_iff_exists_inverse {X : Sort u_1} {Y : Sort u_2} (f : X → Y) : Function.Bijective f ↔ ∃ g, Inverse f g
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/08_Functions/03_Composition.lean`); also in the course library.
- Appears again in: 8.4, 10.2.

#### `bijective_of_inverse`

```lean
bijective_of_inverse {f : X → Y} {g : Y → X} (h : Inverse f g) : Bijective f
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/08_Functions/03_Composition.lean`).

#### `exists_inverse_of_bijective`

```lean
exists_inverse_of_bijective {f : X → Y} (hf : Bijective f) : ∃ g : Y → X, Inverse f g
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/08_Functions/03_Composition.lean`).

### 8.4 Product types

**Tactics:** `zify`

#### `zify` (tactic)

Moves a goal or hypotheses about natural numbers to the integers, where subtraction behaves normally.

- First appears in: book text and Lean file.

**Theorems:** `A_mono`, `of_A_add_mono`, `p_comp_i`

#### `A_mono`

```lean
A_mono {n m : ℕ} (h : n ≤ m) : A n ≤ A m
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/08_Functions/04_Product_Types.lean`).

#### `of_A_add_mono`

```lean
of_A_add_mono {a1 a2 b1 b2 : ℕ} (h : A (a1 + b1) + b1 ≤ A (a2 + b2) + b2) : a1 + b1 ≤ a2 + b2
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/08_Functions/04_Product_Types.lean`).

#### `p_comp_i`

```lean
p_comp_i (x : ℕ × ℕ) : p (i x) = p x + 1
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/08_Functions/04_Product_Types.lean`).

## Chapter 9

### 9.1 Introduction

**Theorems:** `Nat.even_iff_not_odd`, `Set.subset_def`

#### `Nat.even_iff_not_odd`

```lean
Nat.even_iff_not_odd (n : ℕ) : Nat.Even n ↔ ¬Nat.Odd n
```

Written in the book or code as `even_iff_not_odd`.

- First appears in: book text and Lean file.
- Source: course library (`Library/Theory/Parity.lean`).

#### `Set.subset_def`

```lean
Set.subset_def {α : Type u} {s t : Set α} : (s ⊆ t) = ∀ x ∈ s, x ∈ t
```

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.
- Appears again in: 9.2.

### 9.2 Set operations

**Tactics:** `check_equality_of_explicit_sets`, `suffices`

#### `check_equality_of_explicit_sets` (tactic) ★

Defined in the Section 9.2 file as `ext; dsimp; exhaust`: proves equalities between explicitly listed finite sets.

- First appears in: book text and Lean file.

#### `suffices` (tactic)

Replaces the goal by an intermediate statement that is enough to prove it, leaving that statement to prove next.

- First appears in: book text and Lean file.
- Appears again in: 9.3.

**Theorems:** `Int.odd_iff_not_even`

#### `Int.odd_iff_not_even`

```lean
Int.odd_iff_not_even (n : ℤ) : Int.Odd n ↔ ¬Int.Even n
```

Written in the book or code as `odd_iff_not_even`.

- First appears in: book text and Lean file.
- Source: course library (`Library/Theory/Parity.lean`).

### 9.3 The type of sets

**Tactics:** `let`

#### `let` (tactic)

Introduces a local definition inside a proof.

- First appears in: book text and Lean file.

**Theorems:** `Nat.odd_iff_not_even`

#### `Nat.odd_iff_not_even`

```lean
Nat.odd_iff_not_even (n : ℕ) : Nat.Odd n ↔ ¬Nat.Even n
```

- First appears in: book text and Lean file.
- Source: course library (`Library/Theory/Parity.lean`).

## Chapter 10

### 10.1 Reflexive, symmetric, antisymmetric, transitive

**Theorems:** `Nat.eq_zero_or_pos`

#### `Nat.eq_zero_or_pos`

```lean
Nat.eq_zero_or_pos (n : ℕ) : n = 0 ∨ n > 0
```

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.

### 10.2 Equivalence relations

**Theorems:** `EquivalenceClass.eq_of_rel`, `EquivalenceClass.mem_self`, `Function.Injective.comp`, `Function.Surjective.comp`

#### `EquivalenceClass.eq_of_rel`

```lean
EquivalenceClass.eq_of_rel (h_symm : @Symmetric α r) (h_trans : @Transitive α r) {a1 a2 : α} (ha : a1 ∼ a2) : ⦍a1⦐ = ⦍a2⦐
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/10_Relations/02_Equivalence_Relations.lean`).

#### `EquivalenceClass.mem_self`

```lean
EquivalenceClass.mem_self (h_refl : @Reflexive α r) (a : α) : a ∈ { b : α | a ∼ b }
```

- First appears in: book text and Lean file.
- Source: proved in this section (`Math2001/10_Relations/02_Equivalence_Relations.lean`).

#### `Function.Injective.comp`

```lean
Function.Injective.comp {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g : β → φ} {f : α → β} (hg : Function.Injective g) (hf : Function.Injective f) : Function.Injective (g ∘ f)
```

Written in the book or code as `Injective.comp`.

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.

#### `Function.Surjective.comp`

```lean
Function.Surjective.comp {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g : β → φ} {f : α → β} (hg : Function.Surjective g) (hf : Function.Surjective f) : Function.Surjective (g ∘ f)
```

Written in the book or code as `Surjective.comp`.

- First appears in: book text and Lean file.
- Source: Mathlib / Lean core.

## Lemmas behind the book's tactics

You never call these directly, but they explain what the tactics can and
cannot do.

The Introduction names three lemmas that the book's tactics let you avoid
calling by name, and says that fewer than fifty lemmas are invoked by name
in the whole book:

```lean
pow_pos {a : α} : 0 < a → ∀ (n : ℕ), 0 < a ^ n
mul_le_mul_of_nonneg_left {a b c : α} : b ≤ c → 0 ≤ a → a * b ≤ a * c
le_of_pow_le_pow {a b : R} (n : ℕ) : 0 ≤ b → 0 < n → a ^ n ≤ b ^ n → a ≤ b
```

`positivity` (inside `extra`) and `rel` do the work of the first two, and
`cancel` uses the third.

- `cancel` (`Library/Tactic/Cancel.lean`) tries, among others:
  - `pow_eq_zero : a ^ n = 0 → a = 0`
  - `le_of_pow_le_pow : a ^ n ≤ b ^ n → a ≤ b` (needs `0 ≤ b`)
  - `lt_of_pow_lt_pow : a ^ n < b ^ n → a < b` (needs `0 ≤ b`)
  - `mul_left_cancel₀ : c * a = c * b → a = b` (needs `c ≠ 0`)
  - `le_of_mul_le_mul_left` and `lt_of_mul_lt_mul_left` (need `0 < c`)
  - `pos_of_mul_pos_*` and `nonneg_of_mul_nonneg_*`

  It has no rule for `a ^ n = b ^ n → a = b`, because that is false in
  general.
- `extra` (`Library/Tactic/Extra/`) uses `le_add_of_nonneg_right`,
  `lt_add_of_pos_right` and their variants, together with `positivity`. For
  congruences it uses `Int.modEq_add_fac_self_symm : a ≡ a + n * t [ZMOD n]`
  and its variants, plus `Int.ModEq.refl`.
- `le_or_succ_le a n` (`Library/Theory/Comparison.lean`) is a macro, not a
  lemma. It gives `a ≤ n ∨ n + 1 ≤ a`, and `n` must be a literal number.
  It first appears in 2.3.
