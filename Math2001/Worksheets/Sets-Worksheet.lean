import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

open Set

/- The following is Example 6.2.6 in the book -/

theorem Prop5 (A : Set X) : ∅ ⊆ A := by
  dsimp [Set.subset_def]
  intro x
  exhaust


theorem Lemma10 (A B : Set X) : A ∩ B ⊆ A := by
  dsimp [Set.subset_def]
  intro x hx
  exact hx.1

theorem Lemma11 (A B : Set X) : B ⊆ A ∪ B := by
  dsimp [Set.subset_def]
  intro x hx
  right
  exact hx





theorem Lemma12 (A B : Set X) : A ⊆ A ∪ B := by
  sorry

theorem Lemma13 (A B : Set X) : A ∩ B = B ∩ A := by
  sorry

theorem Lemma14 (A B C : Set X) : A ∪ (B ∪ C) = (A ∪ B) ∪ C := by
  sorry

theorem Lemma15 (A B C : Set X) : A ∩ (B ∩ C) = (A ∩ B) ∩ C := by
  sorry

theorem Lemma16 (A B C : Set X) : A ∪ (B ∩ C) ⊆ (A ∪ B) ∩ (A ∪ C) := by
  sorry

theorem Lemma17 (A B C : Set X) : (A ∪ B) ∩ (A ∪ C) ⊆ A ∪ (B ∩ C) := by
  sorry


theorem Lemma18 (A B C : Set X) : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by
  intro x hx
  have xA : x ∈ A := hx.1
  have xBC : x ∈ B ∪ C := hx.2
  rcases xBC with xB | xC
  · left
    show x ∈ A ∩ B
    exact ⟨xA, xB⟩
  · right
    show x ∈ A ∩ C
    exact ⟨xA, xC⟩

theorem Lemma19 (A B C : Set X) : (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C) := by
  sorry

theorem Lemma20 (A B C : Set X) (h : A ⊆ B) : A ∩ C ⊆ B ∩ C := by
  sorry

theorem Lemma21 (A B C : Set X) (h : A ⊆ B) : A ∪ C ⊆ B ∪ C := by
  sorry

theorem Lemma22 (A : Set X) : A ∪ A = A := by
  sorry

theorem Lemma23 (A : Set X) : A ∩ A = A := by
  sorry
