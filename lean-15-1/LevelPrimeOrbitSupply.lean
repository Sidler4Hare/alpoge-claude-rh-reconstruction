import Development.AutomorphicArithmetic.ShortNorms.Primes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneModEqOneAndOfDvd

noncomputable section

namespace Levent151

open GlobalTheory.Mem.An

open Classical in
/-- Original norm primes satisfying the additional level congruence. -/
def levelPrimeOrbitCandidates (d M L : ℕ) (U W : ℝ) : Finset ℕ :=
  (normPrimes d M U W).filter (fun T => T ≡ 1 [MOD L])

theorem mem_levelPrimeOrbitCandidates {d M L T : ℕ} {U W : ℝ}
    (hU : 0 ≤ U) (hW : 0 ≤ W) :
    T ∈ levelPrimeOrbitCandidates d M L U W ↔
      U < (T : ℝ) ∧ (T : ℝ) ≤ W ∧ T.Prime ∧ NormOne d M T ∧ T ≡ 1 [MOD L] := by
  classical
  simp only [levelPrimeOrbitCandidates, normPrimes, Finset.mem_filter, Finset.mem_Ioc,
    Nat.floor_lt hU, Nat.le_floor_iff hW, and_assoc]

/-- Use the original short-norm count at modulus \(ML\), then forget the
extra modulus in the norm condition while retaining its congruence. -/
theorem levelPrimeOrbitCardLower :
    ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧
      ∀ (d M L : ℕ) (U V : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d →
        3 ≤ M → 1 ≤ L → 1 < U → 1 ≤ V →
        Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) + 2 * Real.log (L : ℝ)
          ≤ c * Real.sqrt (Real.log U) →
        Real.log V ≤ c * Real.sqrt (Real.log U) →
        c' * U / (V * ((4 * (d : ℝ) * ((M * L : ℕ) : ℝ) ^ 2) ^ A * Real.log U))
          ≤ ((levelPrimeOrbitCandidates d M L U (U * (1 + 1 / V))).card : ℝ) := by
  classical
  obtain ⟨A, c, c', hA, hc, hc', hnorm⟩ := UpperTheory.T3.shortNorm
  refine ⟨A, c, c', hA, hc, hc', ?_⟩
  intro d M L U V hd hd4 hd100 hM hL hU hV hmod hwidth
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hV0 : 0 < V := zero_lt_one.trans_le hV
  have hML : 3 ≤ M * L := hM.trans (Nat.le_mul_of_pos_right M (by omega))
  have hmod' : Real.log (4 * (d : ℝ) * ((M * L : ℕ) : ℝ)^2)
      ≤ c * Real.sqrt (Real.log U) := by
    rw [show 4 * (d : ℝ) * ((M * L : ℕ) : ℝ)^2 =
      (4 * (d : ℝ) * (M : ℝ)^2) * (L : ℝ)^2 by push_cast; ring]
    rw [Real.log_mul (by positivity : (4 * (d : ℝ) * (M : ℝ)^2) ≠ 0)
      (by positivity : (L : ℝ)^2 ≠ 0), Real.log_pow]
    simpa using hmod
  have hVexp : V ≤ Real.exp (c * Real.sqrt (Real.log U)) := by
    rw [← Real.exp_log hV0]
    exact Real.exp_le_exp.mpr hwidth
  have hwidth' : Real.exp (-c * Real.sqrt (Real.log U)) ≤ 1 / V := by
    rw [neg_mul, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hV0 hVexp
  have hcount := hnorm d (M * L) U (1 / V) hd hd4 hd100 hML hU.le hmod' hwidth'
    (div_le_one_of_le₀ hV hV0.le)
  have hsubset : normPrimes d (M * L) U (U * (1 + 1 / V)) ⊆
      levelPrimeOrbitCandidates d M L U (U * (1 + 1 / V)) := by
    intro T hT
    obtain ⟨hI, hp, hn⟩ := Finset.mem_filter.mp hT
    obtain ⟨hmodT, hnormT⟩ := normOne_modEq_one_and_of_dvd d (M * L) T hd4 hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hI, hp, hnormT M (dvd_mul_right M L)⟩,
        hmodT.of_dvd (dvd_mul_left L M)⟩
  calc
    _ = c' * (1 / V) * U / ((4 * (d : ℝ) * ((M * L : ℕ) : ℝ)^2)^A * Real.log U) := by
      have hlog : 0 < Real.log U := Real.log_pos hU
      have hden : 0 < (4 * (d : ℝ) * ((M * L : ℕ) : ℝ)^2)^A * Real.log U := by
        positivity
      field_simp
    _ ≤ _ := hcount
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsubset

/-- Any exclusion set smaller than the certified count leaves a usable prime. -/
theorem exists_levelPrimeOrbitCandidate_of_card_lt
    {d M L : ℕ} {U V lower : ℝ} (hU : 1 < U) (hV : 1 ≤ V) (S : Finset ℕ)
    (hS : (S.card : ℝ) < lower)
    (hcount : lower ≤ ((levelPrimeOrbitCandidates d M L U (U * (1 + 1 / V))).card : ℝ)) :
    ∃ T ∉ S, U < (T : ℝ) ∧ (T : ℝ) ≤ U * (1 + 1 / V) ∧ T.Prime ∧
      NormOne d M T ∧ T ≡ 1 [MOD L] := by
  have hcard : S.card < (levelPrimeOrbitCandidates d M L U (U * (1 + 1 / V))).card := by
    exact_mod_cast hS.trans_le hcount
  obtain ⟨T, hT, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hU0 : 0 ≤ U := by linarith
  have hV0 : 0 ≤ V := by linarith
  exact ⟨T, hnot, (mem_levelPrimeOrbitCandidates hU0 (by positivity)).mp hT⟩

end Levent151
