/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular
import Library.Theory.ModEq.Defs

import AutograderLib



math2001_init
set_option quotPrecheck false

open Set
open Function


/- Ignore from here down to where it says Homework 6, this is to include the definition of the gcd.
-/

def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d



theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d



theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d


theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d


def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

@[decreasing] theorem lower_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : -b < fmod a b := by
  have H : 0 ≤ fmod a b
  · apply fmod_nonneg_of_pos
    apply h1
  calc -b < 0 := by addarith [h1]
    _ ≤ _ := H

@[decreasing] theorem lower_bound_fmod2 (a b : ℤ) (h1 : b < 0) : b < fmod a (-b) := by
  have H : 0 ≤ fmod a (-b)
  · apply fmod_nonneg_of_pos
    addarith [h1]
  have h2 : 0 < -b := by addarith [h1]
  calc b < 0 := h1
    _ ≤ fmod a (-b) := H

@[decreasing] theorem upper_bound_fmod2 (a b : ℤ) (h1 : b < 0) : fmod a (-b) < -b := by
  apply fmod_lt_of_pos
  addarith [h1]

@[decreasing] theorem upper_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : fmod a b < b := by
  apply fmod_lt_of_pos
  apply h1

def gcd (a b : ℤ) : ℤ :=
  if 0 < b then
    gcd b (fmod a b)
  else if b < 0 then
    gcd b (fmod a (-b))
  else if 0 ≤ a then
    a
  else
    -a
termination_by _ a b => b


theorem gcd_nonneg (a b : ℤ) : 0 ≤ gcd a b := by
  rw [gcd]
  split_ifs with h1 h2 ha <;> push_neg at *
  · -- case `0 < b`
    have IH := gcd_nonneg b (fmod a b) -- inductive hypothesis
    apply IH
  · -- case `b < 0`
    have IH := gcd_nonneg b (fmod a (-b)) -- inductive hypothesis
    apply IH
  · -- case `b = 0`, `0 ≤ a`
    apply ha
  · -- case `b = 0`, `a < 0`
    addarith [ha]
termination_by _ a b => b



mutual
theorem gcd_dvd_right (a b : ℤ) : gcd a b ∣ b := by
  rw [gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    apply gcd_dvd_left b (fmod a b) -- inductive hypothesis
  · -- case `b < 0`
    apply gcd_dvd_left b (fmod a (-b)) -- inductive hypothesis
  · -- case `b = 0`, `0 ≤ a`
    have hb : b = 0 := le_antisymm h1 h2
    use 0
    calc b = 0 := hb
      _ = a * 0 := by ring
  · -- case `b = 0`, `a < 0`
    have hb : b = 0 := le_antisymm h1 h2
    use 0
    calc b = 0 := hb
      _ = -a * 0 := by ring

theorem gcd_dvd_left (a b : ℤ) : gcd a b ∣ a := by
  rw [gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    have IH1 := gcd_dvd_left b (fmod a b) -- inductive hypothesis
    have IH2 := gcd_dvd_right b (fmod a b) -- inductive hypothesis
    obtain ⟨k, hk⟩ := IH1
    obtain ⟨l, hl⟩ := IH2
    have H : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    set q := fdiv a b
    set r := fmod a b
    use l + k * q
    calc a = r + b * q := by rw [H]
      _ = gcd b r * l + (gcd b r * k) * q := by rw [← hk, ← hl]
      _ = gcd b r * (l + k * q) := by ring
  · -- case `b < 0`
    have IH1 := gcd_dvd_left b (fmod a (-b)) -- inductive hypothesis
    have IH2 := gcd_dvd_right b (fmod a (-b)) -- inductive hypothesis
    obtain ⟨k, hk⟩ := IH1
    obtain ⟨l, hl⟩ := IH2
    have H := fmod_add_fdiv a (-b)
    set q := fdiv a (-b)
    set r := fmod a (-b)
    use l - k * q
    calc a = r + (-b) * q := by rw [H]
      _ = gcd b r * l + (- (gcd b r * k)) * q := by rw [← hk, ← hl]
      _ = gcd b r * (l - k * q) := by ring
  · -- case `b = 0`, `0 ≤ a`
    use 1
    ring
  · -- case `b = 0`, `a < 0`
    use -1
    ring

end
termination_by gcd_dvd_right a b => b ; gcd_dvd_left a b => b


mutual

def L (a b : ℤ) : ℤ :=
  if 0 < b then
    R b (fmod a b)
  else if b < 0 then
    R b (fmod a (-b))
  else if 0 ≤ a then
    1
  else
    -1

def R (a b : ℤ) : ℤ :=
  if 0 < b then
    L b (fmod a b) - (fdiv a b) * R b (fmod a b)
  else if b < 0 then
    L b (fmod a (-b)) + (fdiv a (-b)) * R b (fmod a (-b))
  else
    0

end
termination_by L a b => b ; R a b => b



theorem L_mul_add_R_mul (a b : ℤ) : L a b * a + R a b * b = gcd a b := by
  rw [R, L, gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    have IH := L_mul_add_R_mul b (fmod a b) -- inductive hypothesis
    have H : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    set q := fdiv a b
    set r := fmod a b
    calc R b r * a + (L b r - q * R b r) * b
        = R b r * (r + b * q) + (L b r - q * R b r) * b:= by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := IH
  · -- case `b < 0`
    have IH := L_mul_add_R_mul b (fmod a (-b)) -- inductive hypothesis
    have H : fmod a (-b) + (-b) * fdiv a (-b) = a := fmod_add_fdiv a (-b)
    set q := fdiv a (-b)
    set r := fmod a (-b)
    calc  R b r * a + (L b r + q * R b r) * b
        =  R b r * (r + -b * q) + (L b r + q * R b r) * b := by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := IH
  · -- case `b = 0`, `0 ≤ a`
    ring
  · -- case `b = 0`, `a < 0`
    ring
termination_by L_mul_add_R_mul a b => b




/- This is 6.7.6 in the book, and also Theorem 36 in NT Worksheet 4.  -/

theorem bezout (a b : ℤ) : ∃ x y : ℤ, x * a + y * b = gcd a b := by
  use L a b, R a b
  apply L_mul_add_R_mul



/-! # Homework 6

Don't forget to compare with the text version,
available as 215HW5.pdf on blackboard.
 -/

/- The following is Proposition 14 from the Functions Worksheet -/

@[autogradedProof 5]
theorem problem1 {f : X → Y} {g:Y→Z} (h : Surjective (g∘f) ) : Surjective g := by
  sorry


@[autogradedProof 5]
theorem problem2 : ∀ ε > 0  , ∃ (N:ℝ) , ∀ (n : ℝ),   n > N → 1/n < ε := by
  sorry

@[autogradedProof 5]
theorem problem3 : ∃ (x : ℤ) , ∃ (y :ℤ) , 257*x + 1242*y = 1 := by
  sorry


@[autogradedProof 5]
theorem problem4 : ∃ (x:ℤ) , 15*x ≡ 1 [ZMOD 49] := by
  sorry


@[autogradedProof 5]
theorem problem5 {a b n : ℤ} (h: gcd a n = 1): ∃ x , a*x ≡ b [ZMOD n] := by
  sorry
