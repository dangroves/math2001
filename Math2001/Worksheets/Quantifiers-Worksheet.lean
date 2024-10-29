import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int



theorem Prop3 :
    ∀ {y:ℝ}, ∀ ε >0 , ∃ δ > 0 , ∀ {x : ℝ} , (0 < |x-y| ∧ |x-y| < δ) → |4*x + 2 - (4*y + 2)| < ε := by
    intro y ε he
    use ε/4
    constructor
    calc
      ε/4 = ε * 1/4 := by ring
      _> 0 * 1/4 := by rel [he]
      _= 0 := by numbers
    intro x hx
    rcases hx with ⟨h1,h2⟩
    have h5 : 0 ≤ (4 : ℝ) := by extra
    calc
      |4*x + 2 - (4*y + 2)| = |4*(x-y)| := by ring
      _= |4| * |x-y| := by apply abs_mul
      _= 4 * |x-y| := by rw [abs_of_nonneg h5]
      _< 4 * (ε/4) := by rel [h2]
      _= ε := by ring


theorem Prop4 :
  ∀ ε>0 , ∃ δ>0 , ∀ {x : ℝ } , (0 < |x+1| ∧ |x+1| < δ) → |4*x + 2 - (4*(-1) + 2)| < ε := by
  sorry

theorem Lemma5 : ∀ {x : ℝ}, ∃ y , |x-y| < 1 := by
  sorry


/- It might be useful for Prop6 to know about the tactic "field_simp"
If you have a hypothesis (h: b ≠ 0)
Then you can write something like:
  calc
    (a*b)/b = a := by field_simp [h]
(If you don't know that b is not 0, then (a*b)/b is 0/0, which is not a.)

In the proof, lean knew that 0 < |x-2|, and I had real trouble convincing it that x-2 ≠ 0.
I eventually figured this bit out, but if you have a nice proof of this, please let me know.
If you can't work it out, feel free to get in touch with me.  - Prof. Groves
-/


theorem Prop6 : ∀ ε > 0 , ∃ δ > 0 , ∀ {x:ℝ} , (0 < |x-2| ∧ |x-2| < δ) → |(x^2-4)/(x-2) - 4| < ε := by
  sorry

theorem Prop7 :
  ∀ ε > 0 , ∃ δ > 0 , ∀ {x:ℝ} , (0 < |x-4| ∧ |x-4| < δ) → |(3*x-5)-(3*4-5)| < ε := by
  sorry



theorem Prop9:
  ¬ ∀ ε , ∃ δ , ∀ {x:ℝ} , x < δ  ∧ x-2 < ε := by
  sorry
