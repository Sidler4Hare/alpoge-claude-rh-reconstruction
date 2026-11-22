import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily

open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace Levent151

/-- Prefixes include the zero term, which vanishes for the arithmetic data. -/
def prefixMass (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (k + 1), b n

def prefixReciprocal (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (k + 1), b n / n

def prefixLine (b : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  x * prefixReciprocal b k - prefixMass b k

def prefixRamp (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), b n * max (x / n - 1) 0

theorem prefixLine_eq_sum (b : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    prefixLine b k x = ∑ n ∈ Finset.range (k + 1), b n * (x / n - 1) := by
  unfold prefixLine prefixReciprocal prefixMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Every prefix gives a lower supporting line for the nonnegative ramp. -/
theorem prefixLine_le_prefixRamp {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : prefixLine b k x ≤ prefixRamp b x := by
  let q := max k ⌊x⌋₊
  have hpad : prefixRamp b x =
      ∑ n ∈ Finset.range (q + 1), b n * max (x / n - 1) 0 := by
    unfold prefixRamp
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (le_max_right _ _) 1))
    intro n _ hn
    have hnx : x < (n : ℝ) := (Nat.floor_lt hx).1 (by
      rw [Finset.mem_range] at hn
      omega)
    have hn0 := hx.trans_lt hnx
    have hh : x / (n : ℝ) ≤ 1 := (div_le_iff₀ hn0).2 (by simpa using hnx.le)
    rw [max_eq_right (sub_nonpos.mpr hh), mul_zero]
  rw [prefixLine_eq_sum, hpad]
  calc
    _ ≤ ∑ n ∈ Finset.range (k + 1), b n * max (x / n - 1) 0 :=
      Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hb n)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.add_le_add_right (le_max_left _ _) 1))
      (fun n _ _ => mul_nonneg (hb n) (le_max_right _ _))

/-- The prefix ending at the floor attains the ramp. -/
theorem prefixLine_floor_eq_prefixRamp {b : ℕ → ℝ} (hb0 : b 0 = 0)
    {x : ℝ} (hx : 0 ≤ x) : prefixLine b ⌊x⌋₊ x = prefixRamp b x := by
  rw [prefixLine_eq_sum, prefixRamp]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hn0 : n = 0
  · subst n
    simp [hb0]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx).1
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  have hh : 1 ≤ x / (n : ℝ) := (le_div_iff₀ hnpos).2 (by simpa using hnx)
  rw [max_eq_left (sub_nonneg.mpr hh)]

/-- The real prime-weighted ramp is the real part of the original ramp. -/
theorem prefixRamp_vonMangoldt (f : ℕ → ℝ) (x : ℝ) :
    prefixRamp (fun n => Λ n * f n) x =
      (Deduction.ramp (fun n => (f n : ℂ)) x).re := by
  unfold prefixRamp Deduction.ramp
  simp only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem primePrefixLine_le_ramp {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    prefixLine (fun n => Λ n * f n) k x ≤
      (Deduction.ramp (fun n => (f n : ℂ)) x).re := by
  rw [← prefixRamp_vonMangoldt]
  exact prefixLine_le_prefixRamp (fun n => mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg) (hf n)) hx k

theorem primePrefixLine_floor_eq_ramp (f : ℕ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    prefixLine (fun n => Λ n * f n) ⌊x⌋₊ x =
      (Deduction.ramp (fun n => (f n : ℂ)) x).re := by
  rw [← prefixRamp_vonMangoldt]
  exact prefixLine_floor_eq_prefixRamp (by simp) hx

/-- Nonnegative logarithmic deficit in the maximum of a centred line. -/
def logDeficit (v : ℝ) : ℝ := v - 1 - Real.log v

theorem logDeficit_nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ logDeficit v :=
  sub_nonneg.mpr (Real.log_le_sub_one_of_pos hv)

theorem centredLine_div_eq (M T c : ℝ) {x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    (x * M - T - x * Real.log x + c * x) / x =
      M + c - 1 - Real.log T - logDeficit (T / x) := by
  unfold logDeficit
  rw [Real.log_div hT.ne' hx.ne']
  field_simp
  ring

theorem centredLine_div_le (M T c : ℝ) {x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    (x * M - T - x * Real.log x + c * x) / x ≤ M + c - 1 - Real.log T := by
  rw [centredLine_div_eq M T c hT hx]
  exact sub_le_self _ (logDeficit_nonneg (div_pos hT hx))

theorem centredLine_div_at_mass (M T c : ℝ) (hT : 0 < T) :
    (T * M - T - T * Real.log T + c * T) / T = M + c - 1 - Real.log T := by
  rw [centredLine_div_eq M T c hT hT, div_self hT.ne']
  simp [logDeficit]

/-- The original zeta discrepancy is its centred floor prefix. -/
theorem G_eq_centred_primePrefix {x : ℝ} (hx : 0 ≤ x) :
    Deduction.G x = prefixLine (fun n => Λ n) ⌊x⌋₊ x -
      x * Real.log x + (1 + Real.eulerMascheroniConstant) * x := by
  unfold Deduction.G
  rw [show (Deduction.ramp (fun _ => 1) x).re = prefixLine (fun n => Λ n) ⌊x⌋₊ x by
    simpa using (primePrefixLine_floor_eq_ramp (fun _ => 1) hx).symm]

end Levent151
