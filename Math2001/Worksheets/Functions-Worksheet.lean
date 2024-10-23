import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int


theorem thm71 {f : X → Y} (hinj : Injective f) (hsur : Surjective f) : Bijective f := by
  sorry

theorem them72 {f : X → Y} (hbij : Bijective f) : (Surjective f) ∧ (Injective f) := by
  sorry

theorem Prop9 {f : X → Y} {g : Y → Z} (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  sorry

theorem Prop10 {f : X → Y} {g : Y → Z} (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  sorry

def id (x : X) : X := x

theorem Prop14 {f : X → Y} : (f ∘ id) = f := by
  sorry

theorem Prop15 {f : X → Y} : (id ∘ f) = f := by
  sorry

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

/- The following is Proposition 16 from the worksheet, and Example 8.3.7 from the book -/

theorem exists_inverse_of_bijective {f : X → Y} (hf : Bijective f) :
    ∃ g : Y → X, Inverse f g := by
  dsimp [Bijective] at hf
  obtain ⟨h_inj, h_surj⟩ := hf
  dsimp [Surjective] at h_surj
  choose g hg using h_surj
  use g
  dsimp [Inverse]
  constructor
  · -- prove `g ∘ f = id`
    ext x
    dsimp [Injective] at h_inj
    apply h_inj
    calc f ((g ∘ f) x) = f (g (f x)) := by rfl
      _ = f x := by apply hg
      _ = f (id x) := by rfl
  · -- prove `f ∘ g = id`
    ext y
    apply hg


/- The following is Proposition 17 from the worksheet and Example 8.3.8 from the book. -/

theorem bijective_of_inverse {f : X → Y} {g : Y → X} (h : Inverse f g) :
    Bijective f := by
  dsimp [Inverse] at h
  obtain ⟨hgf, hfg⟩ := h
  constructor
  · -- `f` is injective
    intro x1 x2 hx
    calc x1 = id x1 := by rfl
      _ = (g ∘ f) x1 := by rw [hgf]
      _ = g (f x1) := by rfl
      _ = g (f x2) := by rw [hx]
      _ = (g ∘ f) x2 := by rfl
      _ = id x2 := by rw [hgf]
      _ = x2 := by rfl
  · -- `f` is surjective
    intro y
    use g y
    calc f (g y) = (f ∘ g) y := by rfl
      _ = id y := by rw [hfg]
      _ = y := by rfl
