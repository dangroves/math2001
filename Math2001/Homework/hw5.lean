/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular
import AutograderLib


math2001_init
set_option quotPrecheck false

open Set
open Function


/-! # Homework 5

Don't forget to compare with the text version,
available as 215HW5.pdf on blackboard.
 -/

/- The following is Proposition 14 from the Functions Worksheet -/

@[autogradedProof 5]
theorem problem1 {f : X → Y} : (f ∘ id) = f := by
  sorry

@[autogradedProof 4]
theorem problem2a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry

@[autogradedProof 4]
theorem problem2b : ¬ Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry

@[autogradedProof 5]
theorem problem3 : ∀ ε > 0 , ∃ δ > 0, ∀ {x:ℝ}, |x+2|<δ → |(2*x-5)+9|<ε := by
  sorry



@[autogradedProof 5]
theorem problem4a : ∀ x , ∃ y , ∀ z,  3 * x + 2 * y = z := by
  sorry


@[autogradedProof 5]
theorem problem4b : ¬ ∀x , ∃ y, ∀ z, 3 * x + 2 * y = z := by
  sorry



@[autogradedProof 5]
theorem problem5a : ∃ x , ∀ y, ∃ z, 3 * x + 2*y = z := by
  sorry


@[autogradedProof 5]
theorem problem5b : ¬ ∃ x , ∀ y, ∃ z, 3 * x + 2*y = z := by
  sorry
