/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import AutograderLib
import Library.Theory.ParityModular


math2001_init
set_option quotPrecheck false

open Set
open Function


/-! # Homework 4

Don't forget to compare with the text version,
available as 215HW4.pdf on blackboard.
 -/

@[autogradedProof 5]
theorem problem1  (A B C : Set X) (h1 : A ⊆ B) (h2: B ⊆ C) : A ⊆ C := by
sorry

@[autogradedProof 5]
theorem problem2 (A B C : Set X) (h : A ⊆ B) : A ∩ C ⊆ B ∩ C := by
sorry

@[autogradedProof 5]
theorem problem3 (A B C : Set X) (h : A ⊆ B) : A ∪ C ⊆ B ∪ C := by
sorry



@[autogradedProof 4]
theorem problem4a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry

@[autogradedProof 4]
theorem problem4b : { m : ℤ | m ≥ 10 } ⊈ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry


@[autogradedProof 4]
theorem problem5a : { t : ℝ | t ^ 2 - 5 * t + 4 = 0 } = { s : ℝ | s = 4 } := by
  sorry

@[autogradedProof 4]
theorem problem5b : { t : ℝ | t ^ 2 - 5 * t + 4 = 0 } ≠ { s : ℝ | s = 4 } := by
  sorry
