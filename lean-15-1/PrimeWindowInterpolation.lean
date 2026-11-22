import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Levent151

private theorem rampTerm_le_chord {a x b θ t : ℝ} (ht : 0 < t)
    (hθ : 0 ≤ θ) (hθ' : 0 ≤ 1 - θ) (hm : x = (1 - θ) * a + θ * b) :
    max (x / t - 1) 0 ≤ (1 - θ) * max (a / t - 1) 0 + θ * max (b / t - 1) 0 := by
  refine max_le ?_ (add_nonneg (mul_nonneg hθ' (le_max_right _ _))
    (mul_nonneg hθ (le_max_right _ _)))
  calc
    x / t - 1 = (1 - θ) * (a / t - 1) + θ * (b / t - 1) := by
      rw [hm]
      field_simp [ht.ne']
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hθ')
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hθ)

private theorem mulLog_chord_gap_le {a x b θ : ℝ} (ha : 0 < a) (hx : 0 < x) (hb : 0 < b)
    (hθ : 0 ≤ θ) (hθ' : 0 ≤ 1 - θ) (hm : x = (1 - θ) * a + θ * b) :
    (1 - θ) * (a * Real.log a) + θ * (b * Real.log b) - x * Real.log x ≤
      (x - a) * (b - x) / x := by
  have la := Real.log_le_sub_one_of_pos (div_pos ha hx)
  have lb := Real.log_le_sub_one_of_pos (div_pos hb hx)
  rw [Real.log_div ha.ne' hx.ne'] at la
  rw [Real.log_div hb.ne' hx.ne'] at lb
  calc
    _ = (1 - θ) * a * (Real.log a - Real.log x) + θ * b * (Real.log b - Real.log x) := by
      rw [hm]; ring
    _ ≤ (1 - θ) * a * (a / x - 1) + θ * b * (b / x - 1) :=
      add_le_add (mul_le_mul_of_nonneg_left la (mul_nonneg hθ' ha.le))
        (mul_le_mul_of_nonneg_left lb (mul_nonneg hθ hb.le))
    _ = (x - a) * (b - x) / x := by
      field_simp [hx.ne']
      rw [hm]; ring

/-- A nonnegative finite ramp with real thresholds and an arbitrary affine term,
after subtraction of `x * log x`, has this endpoint interpolation error. -/
theorem primeWindowInterpolation {ι : Type*} (s : Finset ι) (q t : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (ht : ∀ i ∈ s, 0 < t i) (slope intercept : ℝ)
    {a x b θ : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b)
    (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hm : x = (1 - θ) * a + θ * b) :
    let F (z : ℝ) := (∑ i ∈ s, q i * max (z / t i - 1) 0) + (slope * z + intercept) - z * Real.log z
    F x ≤ (1 - θ) * F a + θ * F b + (x - a) * (b - x) / x := by
  let R (z : ℝ) := ∑ i ∈ s, q i * max (z / t i - 1) 0
  have hθ' := sub_nonneg.mpr hθ₁
  have hR : R x ≤ (1 - θ) * R a + θ * R b := by
    simp only [R, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ ≤ q i * ((1 - θ) * max (a / t i - 1) 0 + θ * max (b / t i - 1) 0) :=
        mul_le_mul_of_nonneg_left (rampTerm_le_chord (ht i hi) hθ hθ' hm) (hq i hi)
      _ = _ := by ring
  have hline : slope * x + intercept =
      (1 - θ) * (slope * a + intercept) + θ * (slope * b + intercept) := by rw [hm]; ring
  have hlog := mulLog_chord_gap_le ha (ha.trans_le hax) (ha.trans_le (hax.trans hxb)) hθ hθ' hm
  change R x + (slope * x + intercept) - x * Real.log x ≤
    (1 - θ) * (R a + (slope * a + intercept) - a * Real.log a) +
    θ * (R b + (slope * b + intercept) - b * Real.log b) + (x - a) * (b - x) / x
  linarith only [hR, hline, hlog]

end Levent151
