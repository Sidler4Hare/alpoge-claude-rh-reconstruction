import RankTailTransfer

noncomputable section

namespace Levent151

open Finset

/-- In the low-rank range we charge just the signed sum of the exceptional
target slopes. At every other cutoff the original source rank inequality suffices. -/
theorem meanTarget_of_exceptionalRows {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (s : ι → ℝ) (t : κ → ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (exceptional : Finset κ) {U τ J : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ha : ∑ i, a i = 1) (ha0 : ∀ i, 0 ≤ a i)
    (hb : ∑ j, b j = 1) (hb0 : ∀ j, 0 ≤ b j)
    (hs : ∀ i, s i ≤ U) (hmean : ∑ i, a i * s i = -J)
    (hcut : ∀ v ≤ U, (∀ j, t j < v → j ∈ exceptional) ∨
      τ * (∑ j, if t j < v then b j else 0) ≤ ∑ i, if s i < v then a i else 0) :
    -(∑ j, b j * t j) ≤ (J + (1 - τ) * U) / τ +
      ∑ j, (if j ∈ exceptional then b j * (U - t j) else 0) := by
  classical
  let t' (j : κ) := if j ∈ exceptional then U else t j
  have hcut' (v : ℝ) :
      τ * (∑ j, if t' j < v then b j else 0) ≤ ∑ i, if s i < v then a i else 0 := by
    by_cases hv : v ≤ U
    · have hUv : ¬ U < v := not_lt.mpr hv
      rcases hcut v hv with hsmall | hwide
      · have hz (j : κ) : ¬ t' j < v := by
          by_cases hj : j ∈ exceptional
          · simpa [t', hj] using hUv
          · simpa [t', hj] using mt (hsmall j) hj
        simp only [if_neg (hz _), sum_const_zero, mul_zero]
        exact sum_nonneg (fun i _ => by split_ifs <;> first | exact ha0 i | rfl)
      · apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum (g := fun j =>
            if t j < v then b j else 0) (fun j _ => ?_)) hτ.le) hwide
        by_cases hj : j ∈ exceptional
        · simp only [t', if_pos hj, if_neg hUv]
          split_ifs <;> first | exact hb0 j | rfl
        · simp [t', hj]
    · have hlarge (i : ι) := (hs i).trans_lt (lt_of_not_ge hv)
      simp only [if_pos (hlarge _), ha]
      have hcap : (∑ j, if t' j < v then b j else 0) ≤ 1 := by
        rw [← hb]
        exact sum_le_sum (fun j _ => by split_ifs <;> first | rfl | exact hb0 j)
      exact (mul_le_mul_of_nonneg_left hcap hτ.le).trans (by simpa using hτ1)
  have h := meanTarget_of_rankCutoffs s t' a b hτ ha hb hb0 hs hmean hcut'
  have heq : ∑ j, b j * t' j = (∑ j, b j * t j) +
      ∑ j, (if j ∈ exceptional then b j * (U - t j) else 0) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    by_cases hj : j ∈ exceptional
    · simp [t', hj]
      ring
    · simp [t', hj]
  rw [heq] at h
  linarith only [h]

/-- A comparison above one cutoff charges exactly the weighted deficit below it. -/
theorem meanTarget_of_clippedRankCutoffs {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → ℝ) (t : κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) {U τ J c : ℝ}
    (hτ : 0 < τ) (ha : ∑ i, a i = 1) (ha0 : ∀ i, 0 ≤ a i)
    (hb : ∑ j, b j = 1) (hb0 : ∀ j, 0 ≤ b j)
    (hs : ∀ i, s i ≤ U) (hmean : ∑ i, a i * s i = -J)
    (hcut : ∀ v > c, τ * (∑ j, if t j < v then b j else 0) ≤
      ∑ i, if s i < v then a i else 0) :
    -(∑ j, b j * t j) ≤ (J + (1 - τ) * U) / τ +
      ∑ j, b j * max (c - t j) 0 := by
  classical
  have hcut' (v : ℝ) :
      τ * (∑ j, if max c (t j) < v then b j else 0) ≤
        ∑ i, if s i < v then a i else 0 := by
    by_cases hv : c < v
    · simpa only [max_lt_iff, hv, true_and] using hcut v hv
    · simp only [max_lt_iff, hv, false_and, if_false, sum_const_zero, mul_zero]
      exact sum_nonneg (fun i _ => by split_ifs <;> first | exact ha0 i | rfl)
  have h := meanTarget_of_rankCutoffs s (fun j => max c (t j)) a b
    hτ ha hb hb0 hs hmean hcut'
  have heq : (∑ j, b j * max c (t j)) =
      (∑ j, b j * t j) + ∑ j, b j * max (c - t j) 0 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rcases le_total c (t j) with hj | hj
    · rw [max_eq_right hj, max_eq_right (sub_nonpos.mpr hj), mul_zero, add_zero]
    · rw [max_eq_left hj, max_eq_left (sub_nonneg.mpr hj)]
      ring
  rw [heq] at h
  linarith only [h]

end Levent151
