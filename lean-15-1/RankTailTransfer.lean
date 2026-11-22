import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith

noncomputable section

namespace Levent151

open Finset MeasureTheory Set

/-- In the exact ramified rank formula, a common integral multiplicity
survives after cancelling the coprime powers of consecutive integers. -/
theorem levelRankMultiplicity (a f full kept : ℕ) (hfull : 0 < full)
    (h : (a + 1) ^ f * kept = a ^ f * full) :
    ∃ m : ℕ, 0 < m ∧ full = (a + 1) ^ f * m ∧ kept = a ^ f * m := by
  have hcop : Nat.Coprime ((a + 1) ^ f) (a ^ f) :=
    Nat.Coprime.pow _ _ (by simp : Nat.Coprime (a + 1) a)
  have hdvd : (a + 1) ^ f ∣ full := hcop.dvd_of_dvd_mul_left ⟨kept, h.symm⟩
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < (a + 1) ^ f := Nat.pow_pos (by omega)
  refine ⟨m, Nat.pos_of_ne_zero (fun hz => by simp [hm, hz] at hfull), hm, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h, hm]
  ac_rfl

/-- A word whose high-slope part lands in a target cutoff can detect
at most the complementary source rank in the quotient. -/
theorem projectedWordRank {K V R : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup R] [Module K R] (B : V →ₗ[K] R)
    (A : Submodule K V) (W : Submodule K R) (h : ∀ x ∈ A, B x ∈ W) :
    Module.finrank K (W.mkQ.comp B).range ≤ Module.finrank K V - Module.finrank K A := by
  have hker : A ≤ (W.mkQ.comp B).ker := by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero W).mpr (h x hx)
  have := Submodule.finrank_mono hker
  have := (W.mkQ.comp B).finrank_range_add_finrank_ker
  omega

/-- One set of spanning words detects at least the dimension of every quotient. -/
theorem spanningWordRanks {K R ι : Type*} [Field K] [AddCommGroup R] [Module K R]
    [FiniteDimensional K R] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module K (V i)] (B : ∀ i, V i →ₗ[K] R) (C : Finset ι)
    (hC : C.sup (fun i => (B i).range) = ⊤) (W : Submodule K R) :
    Module.finrank K (R ⧸ W) ≤ ∑ i ∈ C, Module.finrank K (W.mkQ.comp (B i)).range := by
  classical
  let A (i : ι) := (W.mkQ.comp (B i)).range
  have hr (D : Finset ι) :
      Module.finrank K ↥(D.sup A : Submodule K (R ⧸ W)) ≤
        ∑ i ∈ D, Module.finrank K (A i) := by
    induction D using Finset.induction_on with
    | empty => simp
    | @insert i D hi ih =>
      rw [Finset.sup_insert, Finset.sum_insert hi]
      have h := Submodule.finrank_sup_add_finrank_inf_eq (A i) (D.sup A)
      omega
  have htop : C.sup A = ⊤ := by
    have hmap := congrArg (Submodule.map W.mkQ) hC
    simpa [A, Finset.sup_eq_iSup, Submodule.map_iSup, LinearMap.range_comp,
      Submodule.map_top, LinearMap.range_eq_top.mpr W.mkQ_surjective] using hmap
  have hdim := hr C
  rwa [htop, finrank_top] at hdim

/-- Linear price of lost full-source ranks and of the diagonal Gram defect. -/
theorem fullFrameRankLoss {z η b e : ℝ} (hz : 0 ≤ z) (hη : 0 ≤ η) (hb : 0 ≤ b)
    (he : 0 ≤ e) (htrace : z - Real.sqrt (z * η) ≤ 2 * (b + Real.sqrt (b * e))) :
    z ≤ η + 5 * b + 4 * e := by
  rw [Real.sqrt_mul hz, Real.sqrt_mul hb] at htrace
  nlinarith [sq_nonneg (Real.sqrt z - Real.sqrt η),
    sq_nonneg (Real.sqrt b - 2 * Real.sqrt e),
    Real.sq_sqrt hz, Real.sq_sqrt hη, Real.sq_sqrt hb, Real.sq_sqrt he]

/-- A quotient above the exceptional codimension has uniform rank expansion. -/
theorem wideQuotientRank {ρ ζ η α e q : ℝ} (hα : 0 ≤ α) (hq : 0 ≤ q)
    (htrace : ρ * ζ ≤ η + 5 * (α + (1 - α) * q) + 4 * e)
    (hwide : 2 * (η + 5 * α + 4 * e) ≤ ρ * ζ) : ρ * ζ ≤ 10 * q := by
  nlinarith [mul_nonneg hα hq]

/-- The clipped negative part lies below the chord through -H and U. -/
theorem clippedSourceChord {H U s : ℝ} (hH : 0 ≤ H) (hU : 0 ≤ U) (hs : s ≤ U) :
    min H (max (-s) 0) * (H + U) ≤ H * (U - s) := by
  by_cases hlo : s ≤ -H
  · rw [max_eq_left (by linarith), min_eq_left (by linarith)]
    nlinarith [mul_nonneg hH (show 0 ≤ -H - s by linarith)]
  · by_cases hhi : 0 ≤ s
    · rw [max_eq_right (by linarith), min_eq_right hH, zero_mul]
      exact mul_nonneg hH (sub_nonneg.mpr hs)
    · rw [max_eq_left (by linarith), min_eq_right (by linarith)]
      nlinarith [mul_nonneg hU (show 0 ≤ H + s by linarith)]

private def slopeTail (U value weight : ℝ) : ℝ → ℝ :=
  (Ico 0 (U - value)).indicator (fun _ => weight)

private theorem integrable_slopeTail (U value weight : ℝ) :
    Integrable (slopeTail U value weight) := by
  apply (integrable_indicator_iff measurableSet_Ico).2
  exact integrableOn_const (measure_Ico_lt_top.ne)

private theorem integral_slopeTail (U value weight : ℝ) :
    ∫ t, slopeTail U value weight t = weight * max (U - value) 0 := by
  rw [slopeTail, integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico]
  simp [mul_comm]

/-- A lower-CDF comparison of finite rank laws gives a mean target bound.
Weights may be nonuniform and the target needs no supplied lower slope. -/
theorem meanTarget_of_rankCutoffs {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → ℝ) (t : κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) {U τ J : ℝ}
    (hτ : 0 < τ) (ha : ∑ i, a i = 1) (hb : ∑ j, b j = 1) (hb0 : ∀ j, 0 ≤ b j)
    (hs : ∀ i, s i ≤ U) (hmean : ∑ i, a i * s i = -J)
    (hcut : ∀ v : ℝ, τ * (∑ j, if t j < v then b j else 0) ≤
      ∑ i, if s i < v then a i else 0) :
    -(∑ j, b j * t j) ≤ (J + (1 - τ) * U) / τ := by
  classical
  have hit := fun i : ι => integrable_slopeTail U (s i) (a i)
  have hjt := fun j : κ => integrable_slopeTail U (t j) (b j)
  have hpoint (x : ℝ) : τ * (∑ j, slopeTail U (t j) (b j) x) ≤
      ∑ i, slopeTail U (s i) (a i) x := by
    by_cases hx : 0 ≤ x
    · simpa only [slopeTail, indicator_apply, Set.mem_Ico, hx, true_and,
        lt_sub_comm (a := x)] using hcut (U - x)
    · simp [slopeTail, hx]
  have hI := integral_mono
    ((integrable_finsetSum _ (fun j _ => hjt j)).const_mul τ)
    (integrable_finsetSum _ (fun i _ => hit i)) hpoint
  rw [integral_const_mul,
    integral_finsetSum _ (fun j _ => hjt j),
    integral_finsetSum _ (fun i _ => hit i)] at hI
  simp only [integral_slopeTail, max_eq_left (sub_nonneg.mpr (hs _))] at hI
  have hsmall : (∑ j, b j * (U - t j)) ≤ ∑ j, b j * max (U - t j) 0 :=
    sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hb0 j))
  have hlinear := (mul_le_mul_of_nonneg_left hsmall hτ.le).trans hI
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, ha, hb, one_mul, hmean] at hlinear
  apply (le_div_iff₀ hτ).2
  linarith only [hlinear]

end Levent151
