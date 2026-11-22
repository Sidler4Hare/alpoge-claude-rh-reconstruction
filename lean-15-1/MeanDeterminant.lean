import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence

noncomputable section

namespace Levent151

open Formalism.RankGapBounds.WeightedMeanData
  Formalism.LFunctionChainParameters.WeightedSlopeBounds

/-- The two geometric errors can be measured by one target determinant term. -/
theorem gain_le_centred_determinant {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
    (hS : D.HidaSetting C) (hE : EComp5 D C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp)
    (u0 : U0) (u : W u0) :
    D.Ga u0 - D.Main u0 ≤
      (D.muN u0 u + D.sumA * Real.log (D.T u0 u) - D.Fo u0 - D.SDiv) +
      D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)) +
      C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k) +
      (m : ℝ) * C.cE * D.B0 + Lo5 D C Xpp u0 u := by
  have hA := D.sumA_nonneg C hS
  obtain ⟨-, -, -, -, -, hv, hf, -, hw, -⟩ := hS
  have hlog : D.sumA * Lam5 D C u0 ≤ D.sumA * Real.log (D.T u0 u) :=
    mul_le_mul_of_nonneg_left (hCount u0 u).1 hA
  have hMain := key_identity5 D C hv hf u0 (hw u0)
  have hExp := exponent_le_upper D C hE u0 u
  have hBase := (hSl u0 u).1
  have hLattice := (hSN u0 u).2
  linarith

/-- The quotient slope bounds alone bracket the relative determinant. -/
theorem gain_relative_determinant_bounds {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
    (hSN : QuotientSlopeBoundsWith D C Xpp) (u0 : U0) (u : W u0)
    (hOrder : D.muN u0 u ≤ D.muMaxN u0 u) :
    let P := D.muN u0 u - D.muM u0 u + D.Ee u0 u - D.Fo u0 - D.Main u0
    let V := D.muMaxM u0 u - D.muM u0 u
    P - V - C.cSl1 * (m : ℝ) * D.B0 ≤ D.Ga u0 - D.Main u0 ∧
      D.Ga u0 - D.Main u0 ≤ P + Lo5 D C Xpp u0 u := by
  dsimp only
  exact ⟨by linarith [(hSN u0 u).1], by linarith [(hSN u0 u).2]⟩

end Levent151
