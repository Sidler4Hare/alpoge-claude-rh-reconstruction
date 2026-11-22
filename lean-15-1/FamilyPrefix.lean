import PrimePrefix

open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace Levent151

open Deduction

def familyPrefixWeight (F : CharFamily) (n : ℕ) : ℝ :=
  Λ n * ∑ i, F.a i * (F.χ i n).re

open Classical in
def familyPrincipalWeight (F : CharFamily) : ℝ :=
  ∑ i, if F.χ i = 1 then F.a i else 0

open Classical in
def familyLinearCentre (F : CharFamily) : ℝ :=
  ∑ i, F.a i * (if F.χ i = 1 then 1 + Real.eulerMascheroniConstant else
    (deriv (DirichletCharacter.LFunction (F.χ i)) 1 /
      DirichletCharacter.LFunction (F.χ i) 1).re)

private theorem familyRamp_eq (F : CharFamily) (x : ℝ) :
    (∑ i, F.a i * (ramp (fun n => F.χ i n) x).re) =
      prefixRamp (familyPrefixWeight F) x := by
  unfold ramp prefixRamp familyPrefixWeight
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The original retained family is the centred floor prefix of its real prime weights. -/
theorem Gm_eq_centred_familyPrefix (F : CharFamily) {x : ℝ} (hx : 0 ≤ x) :
    Gm F x = prefixLine (familyPrefixWeight F) ⌊x⌋₊ x -
      familyPrincipalWeight F * (x * Real.log x) + familyLinearCentre F * x := by
  classical
  rw [prefixLine_floor_eq_prefixRamp (b := familyPrefixWeight F)
    (by simp [familyPrefixWeight]) hx, ← familyRamp_eq]
  unfold Gm familyPrincipalWeight familyLinearCentre
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : F.χ i = 1
  · simp only [Gchi, if_pos hi, Complex.add_re, Complex.sub_re, Complex.ofReal_re]
    ring
  · simp only [Gchi, if_neg hi, Complex.add_re, Complex.re_ofReal_mul, zero_mul, sub_zero]
    ring

/-- A nonnegative family prime weight makes each other prefix a lower supporting line. -/
theorem centred_familyPrefix_le_Gm (F : CharFamily) (hb : ∀ n, 0 ≤ familyPrefixWeight F n)
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    prefixLine (familyPrefixWeight F) k x -
      familyPrincipalWeight F * (x * Real.log x) + familyLinearCentre F * x ≤ Gm F x := by
  rw [Gm_eq_centred_familyPrefix F hx,
    prefixLine_floor_eq_prefixRamp (b := familyPrefixWeight F)
      (by simp [familyPrefixWeight]) hx]
  exact add_le_add (sub_le_sub_right (prefixLine_le_prefixRamp hb hx k) _) le_rfl

end Levent151
