import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat

/-! The following is Proposition 4 on the Induction Worksheet, and Example 6.1.5 from the book
-/
example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra

theorem Ind_Prop5 {s : ℕ} (hs : s ≥ 3) : s^2 > 2 * s + 1 := by
  sorry

theorem Ind_Prop6 {n : ℕ} (hn : n ≥ 5) : 2^n > n^2  := by
  sorry



/-! The following is Proposition 11 on the Induction Worksheet and Example 6.2.4 from the book.
-/

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

/-! The following is Proposition 12 on the Induction Worksheet and Exercise 6.2.7.4 from the book
-/

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n+1)^2


theorem Ind_Prop12 (n : ℕ) : B n = n * (n+1) * (2*n + 1) / 6 := by
  sorry

def C : ℕ → ℚ
  | 0 => 0
  | n+1 => C n + (n+1)^3

theorem Ind_Prop13 : C n = n^2 * (n+1)^2 / 4 := by
  sorry


def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem Ind_Prop15 (hn : n ≥ 4) : factorial n ≥ 2^n := by
  sorry
