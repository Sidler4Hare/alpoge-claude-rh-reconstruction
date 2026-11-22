import Equation152
import MeanDeterminant

noncomputable section

namespace Levent151

open Formalism.HC Formalism.MainNotions
  Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds

namespace RealizedData

variable {ψ : PChar} {ε x : ℝ} {Fm : FamP ε} (R : RealizedData ψ Fm x)

/-- The original factor (2/(B\delta)) for the zero-coset overlap estimate. -/
def oneWordFactor : ℝ :=
  2 / (((Fm.D x R.i).host.TT.card : ℝ) * (R.m : ℝ) * R.b *
    ((R.T2.card : ℝ) / Fintype.card (Fm.D x R.i).R.A))

theorem oneWordFactor_pos (hx : 0 < x) : 0 < R.oneWordFactor := by
  have hn : (0 : ℝ) < Fintype.card (Fm.D x R.i).R.A := by
    exact_mod_cast Fintype.card_pos
  have ht := lt_of_lt_of_le
    (div_pos (mul_pos (Real.rpow_pos_of_pos hx (-(ε / 8))) hn) (by norm_num))
    R.rest.2.1
  have hd := (Real.rpow_pos_of_pos hx (-ε)).trans_le R.rest.2.2.1
  have hm := (Real.rpow_pos_of_pos hx ((1 : ℝ) / 2 - ε)).trans_le R.rest.2.2.2.1
  unfold oneWordFactor
  exact div_pos (by norm_num) (mul_pos (mul_pos (mul_pos ht hm) R.b_pos) hd)

/-- The four-term budget at the original exponent is strictly positive. -/
theorem oneWordBudget_pos (hx : 0 < x) : 0 < x ^ (5 * ε) * R.bracket := by
  have hn : (0 : ℝ) < Fintype.card (Fm.D x R.i).R.A := by
    exact_mod_cast Fintype.card_pos
  have hm := (Real.rpow_pos_of_pos hx ((1 : ℝ) / 2 - ε)).trans_le R.rest.2.2.2.1
  have hb := R.b_pos
  have hk := R.k_pos
  have ha := R.aE_nonneg
  unfold RealizedData.bracket paperBracket
  positivity



end RealizedData

/-- Transfer one actual word bound across two overlap estimates on the same
four-twist centre. The room hypothesis compares the normalized budgets. -/
theorem oneWordWindow {ψ : PChar} {ε x : ℝ} {Fm Fm' : FamP ε}
    (R : RealizedData ψ Fm x) (R' : RealizedData ψ Fm' x) (hx : 0 < x)
    {U : Type} [Fintype U] {W : U → Type} [∀ v, Fintype (W v)]
    [∀ v, Nonempty (W v)] {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U W Top m f) (C : Consts) (Xpp : ℝ)
    (u₀ : (Fm.D x R.i).R.A0) (v : U) (i : W v)
    (hLower : D.muM v i + D.Ga v + D.Fo v - D.Ee v i - Lo5 D C Xpp v i ≤ D.muN v i)
    (hASK : R.discrepancy u₀ = D.ASK v - D.Main v)
    (hword : D.ASK v - D.Ga v +
      (D.muN v i - D.muM v i + D.Ee v i - D.Fo v - D.Main v) +
      Lo5 D C Xpp v i ≤ x ^ (5 * ε) * R.bracket)
    {S r r' : ℝ}
    (hold : |R.oneWordFactor * R.discrepancy u₀ - S| ≤ r)
    (hnew : ∀ u : (Fm'.D x R'.i).R.A0, |R'.oneWordFactor * R'.discrepancy u - S| ≤ r')
    (hroom : R.oneWordFactor * (x ^ (5 * ε) * R.bracket) + r + r' ≤
      R'.oneWordFactor * (x ^ (5 * ε) * R'.bracket)) :
    (∀ u : (Fm'.D x R'.i).R.A0, R'.discrepancy u ≤ x ^ (5 * ε) * R'.bracket) ∧
      R'.cosetMean 0 ≤ x ^ (5 * ε) * R'.bracket := by
  have hpoint : R.discrepancy u₀ ≤ x ^ (5 * ε) * R.bracket := by
    rw [hASK]
    linarith only [hword, hLower]
  have hnorm := mul_le_mul_of_nonneg_left hpoint (R.oneWordFactor_pos hx).le
  have hcentre := (abs_le.mp hold).1
  have htransfer (u : (Fm'.D x R'.i).R.A0) :
      R'.discrepancy u ≤ x ^ (5 * ε) * R'.bracket := by
    apply le_of_mul_le_mul_left _ (R'.oneWordFactor_pos hx)
    linarith only [hnorm, hcentre, (abs_le.mp (hnew u)).2, hroom]
  refine ⟨htransfer, ?_⟩
  classical
  unfold RealizedData.cosetMean
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
    (0 : ℝ) < Fintype.card (Fm'.D x R'.i).R.A0)).2
  calc
    _ ≤ ∑ _u : (Fm'.D x R'.i).R.A0, x ^ (5 * ε) * R'.bracket := by
      exact Finset.sum_le_sum fun u _ => by simpa only [zero_add] using htransfer u
    _ = _ := by simp [mul_comm]

end Levent151

