import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily

open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace Levent151

/-- The finite prime-power sum for the two-scale ramp difference. -/
def primeWindowSum (f : ℕ → ℂ) (x V : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊V⌋₊ + 1), (Λ n : ℂ) * f n *
    ((min 1 (x / n) - x / V : ℝ) : ℂ)

/-- The sign corresponds to subtracting the larger-scale ramp from the smaller one. -/
theorem ramp_sub_scaled (f : ℕ → ℂ) {x V : ℝ} (hx : 0 ≤ x) (hxV : x ≤ V) :
    Deduction.ramp f x - ((x / V : ℝ) : ℂ) * Deduction.ramp f V =
      -primeWindowSum f x V := by
  unfold Deduction.ramp primeWindowSum
  have hV : 0 ≤ V := hx.trans hxV
  have hsum : (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
      (Λ n : ℂ) * f n * ((max (x / n - 1) 0 : ℝ) : ℂ)) =
      ∑ n ∈ Finset.range (⌊V⌋₊ + 1),
        (Λ n : ℂ) * f n * ((max (x / n - 1) 0 : ℝ) : ℂ) := by
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hxV) 1))
    intro n _ hn
    have hn' : ⌊x⌋₊ < n := by
      rw [Finset.mem_range] at hn
      omega
    have hnx : x < (n : ℝ) := (Nat.floor_lt hx).1 hn'
    have hn0 : (0 : ℝ) < n := hx.trans_lt hnx
    rw [max_eq_right (sub_nonpos.mpr ((div_le_iff₀ hn0).2 (by simpa using hnx.le)))]
    simp
  rw [hsum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hn0 : n = 0
  · subst n
    simp
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hnv : (n : ℝ) ≤ V := (Nat.le_floor_iff hV).1
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  have hVpos : 0 < V := hnpos.trans_le hnv
  have hker : max (x / n - 1) 0 - x / V * max (V / n - 1) 0 =
      -(min 1 (x / n) - x / V) := by
    have hqV : 1 ≤ V / (n : ℝ) := (le_div_iff₀ hnpos).2 (by simpa using hnv)
    rw [max_eq_left (sub_nonneg.mpr hqV)]
    by_cases hnx : (n : ℝ) ≤ x
    · have hq : 1 ≤ x / (n : ℝ) := (le_div_iff₀ hnpos).2 (by simpa using hnx)
      rw [max_eq_left (sub_nonneg.mpr hq), min_eq_left hq]
      field_simp
      ring
    · have hq : x / (n : ℝ) ≤ 1 := (div_le_iff₀ hnpos).2 (by simpa using (lt_of_not_ge hnx).le)
      rw [max_eq_right (sub_nonpos.mpr hq), min_eq_right hq]
      field_simp
      ring
  calc
    _ = (Λ n : ℂ) * f n * ((max (x / n - 1) 0 - x / V * max (V / n - 1) 0 : ℝ) : ℂ) := by
      push_cast
      ring
    _ = _ := by rw [hker]; push_cast; ring

/-- The nonprincipal logarithmic-derivative centre is linear and cancels exactly. -/
theorem Gchi_sub_scaled_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {x V : ℝ} (hx : 0 < x) (hxV : x ≤ V) :
    Deduction.Gchi χ x - ((x / V : ℝ) : ℂ) * Deduction.Gchi χ V =
      -primeWindowSum (fun n => χ n) x V := by
  have hV : (V : ℂ) ≠ 0 := by exact_mod_cast (hx.trans_le hxV).ne'
  simp only [Deduction.Gchi, if_neg hχ]
  rw [← ramp_sub_scaled (fun n => χ n) hx.le hxV]
  push_cast
  field_simp
  ring

/-- The principal centre leaves the real term (x \log(V/x)). -/
theorem Gchi_sub_scaled_of_eq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ = 1) {x V : ℝ} (hx : 0 < x) (hxV : x ≤ V) :
    Deduction.Gchi χ x - ((x / V : ℝ) : ℂ) * Deduction.Gchi χ V =
      ((x * Real.log (V / x) : ℝ) : ℂ) - primeWindowSum (fun n => χ n) x V := by
  have hV : 0 < V := hx.trans_le hxV
  have hV' : (V : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
  simp only [Deduction.Gchi, if_pos hχ]
  rw [Real.log_div hV.ne' hx.ne', sub_eq_add_neg ((x * (Real.log V - Real.log x) : ℝ) : ℂ),
    ← ramp_sub_scaled (fun n => χ n) hx.le hxV]
  push_cast
  field_simp
  ring

/-- The signed identity for the real character contribution, including the principal term. -/
theorem Gchi_re_sub_scaled {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x V : ℝ} (hx : 0 < x) (hxV : x ≤ V) :
    (Deduction.Gchi χ x).re - (x / V) * (Deduction.Gchi χ V).re =
      (if χ = 1 then x * Real.log (V / x) else 0) - (primeWindowSum (fun n => χ n) x V).re := by
  classical
  by_cases hχ : χ = 1
  · simpa only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re, if_pos hχ] using
      congrArg Complex.re (Gchi_sub_scaled_of_eq_one χ hχ hx hxV)
  · simpa only [Complex.sub_re, Complex.re_ofReal_mul, Complex.neg_re, if_neg hχ, zero_sub] using
      congrArg Complex.re (Gchi_sub_scaled_of_ne_one χ hχ hx hxV)

/-- Even prime powers away from the discriminant prime have quadratic sign one. -/
theorem jacobiSym_even_prime_power {p d : ℕ} (hp : p.Prime) (hd : d.Prime)
    (hpd : p ≠ d) (j : ℕ) : jacobiSym ((p : ℤ) ^ (2 * j)) d = 1 := by
  have hcop : p.Coprime d := (Nat.coprime_primes hp hd).2 hpd
  have hgcd : (p : ℤ).gcd d = 1 := by simpa [Int.gcd] using hcop
  rw [pow_mul, jacobiSym.pow_left, jacobiSym.sq_one' hgcd, one_pow]

end Levent151
