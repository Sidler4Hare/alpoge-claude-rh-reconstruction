import Window

namespace Levent151

open Formalism.HC Formalism.MainNotions Deduction.CH UpperTheory.Comparison₂

/-- Use the same weights and the same discarded-character estimate in the
finite Fourier step. The final absorption costs any fixed positive δ. -/
theorem gm_windows_of_equation151 {ψ : PChar} {ε C δ : ℝ} (he : 0 < ε)
    (hC : 0 ≤ C) (hδ : 0 < δ) {Fm : FamP ε}
    (hw : Equation151Windows ψ Fm (fun x => x ^ (C * ε))) :
    HasWindows {x | Equation151At ψ Fm x (x ^ (C * ε)) ∧
      (Level.cyc ψ).Gm x ≤ x ^ ((1 : ℝ) / 2 + (C + 3 + δ) * ε)} (3 / 2) := by
  let Λ := Level.cyc ψ
  have ho : (0 : ℝ) ≤ Λ.o := Nat.cast_nonneg _
  have hc : |(3 * (Λ.o : ℝ) + 1)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith)
  obtain ⟨x₁, h₁⟩ := Deduction.ch_core C ε 4 (koOf Λ) (3 * (Λ.o : ℝ) + 1)⁻¹
    (4 * (Λ.o : ℝ)) hC he hc
  obtain ⟨x₂, h₂⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (mul_pos hδ he)).eventually_ge_atTop (1 + 4 * (Λ.o : ℝ)))
  intro Y₀
  obtain ⟨Y, hY, hwin⟩ := hw (max Y₀ (max x₁ x₂))
  refine ⟨Y, (le_max_left _ _).trans ((le_max_right _ _).trans hY), fun x hy hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans (hY.trans hy)
  have hxpos := zero_lt_one.trans_le hx1
  have hlate : max x₁ x₂ ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans (hY.trans hy))
  have harith := hwin x hy hx
  refine ⟨harith, ?_⟩
  obtain ⟨_, i, _, pw⟩ := harith
  let H := (Fm.D x i).host
  obtain ⟨_, hhost, m, ell, N, T₂, a, w, b, b', k, aE, η, X', θ, _, hb, ha, hk,
    hm, hxm, hs, hth, hcost, hrest, hT, hchars, hgm, hsig, hgap⟩ := pw
  have bound := h₁ x ((le_max_left _ _).trans hlate) _ m _ _ ell N H.TT T₂ a w b b' k aE
    η X' θ _ _ hhost hb ha hk hm hxm hs hth hcost hrest hT hchars (fun u hu => by
      rw [errorBracket_eq_paperBracket _ _ _ _ _ _ _ _ _ hxpos
        (by exact_mod_cast Fintype.card_pos) hk]
      exact hgap u hu)
  rw [hgm] at bound
  have hsmall : x ^ ((1 : ℝ) / 2 + ε) ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
  have hsum := bound.trans (add_le_add (le_refl _) hsig)
  change Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (C + 3 + δ) * ε)
  calc Λ.Gm x ≤ (1 + 4 * (Λ.o : ℝ)) * x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
          linarith only [hsum, mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 4 * (Λ.o : ℝ))]
       _ ≤ x ^ (δ * ε) * x ^ ((1 : ℝ) / 2 + (C + 3) * ε) :=
          mul_le_mul_of_nonneg_right (h₂ x ((le_max_right _ _).trans hlate)) (Real.rpow_nonneg hxpos.le _)
       _ = _ := by rw [← Real.rpow_add hxpos]; congr 1; ring

end Levent151
