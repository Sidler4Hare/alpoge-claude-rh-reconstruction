import Extraction
import Quadratic

namespace Levent151

open Formalism.HC Formalism.MainNotions Formalism.LFunctionChainParameters.LErr
  UpperTheory.Top UpperTheory.Comparison₂

/-- K, cHH and eK are selected before x. The constant multiplying x^(2ε)
is consequently uniform over all windows of this family and their translates. -/
theorem quadratic_windows_of_tied {ψ : PChar} {ε : ℝ} (he : 0 < ε) (Fm : FamP ε)
    (hc : (GChi ψ).cls (3 / 2) Fm) {K cHH eK CL x₀ : ℝ}
    (ht : ∀ x ≥ x₀, x ∈ Fm.Win → ChainTied Fm 2 0 K cHH eK CL x) :
    Equation151Windows ψ Fm (fun x => quadraticConstant K cHH eK * x ^ (2 * ε)) ∧
      ∀ δ : ℝ, 0 < δ → Equation151Windows ψ Fm (fun x => x ^ ((2 + δ) * ε)) := by
  obtain ⟨xL, hL⟩ := large_x_eventually ε K cHH eK he
  constructor
  · exact windows_of_tied_bound Fm hc ht (xL := xL) fun x hx _ _ _ hCore hE =>
      pointwiseAt_of_errorBound hCore (hL x hx) hE (quadraticErrorBound ε x K cHH eK) le_rfl
  · intro δ hδ
    obtain ⟨xB, hB⟩ := quadraticFactor_eventually K cHH eK he hδ
    exact windows_of_tied_bound Fm hc ht (xL := max xL xB) fun x hx _ _ _ hCore hE =>
      pointwiseAt_of_errorBound hCore (hL x (le_of_max_le_left hx)) hE
        (quadraticErrorBound ε x K cHH eK) (hB x (le_of_max_le_right hx))

theorem gm_windows_of_quadratic {ψ : PChar} {ε : ℝ} (he : 0 < ε) {Fm : FamP ε}
    (hw : ∀ δ : ℝ, 0 < δ → Equation151Windows ψ Fm (fun x => x ^ ((2 + δ) * ε))) :
    ∀ δ : ℝ, 0 < δ →
      HasWindows {x | Equation151At ψ Fm x (x ^ ((2 + δ / 2) * ε)) ∧
        (Level.cyc ψ).Gm x ≤ x ^ ((1 : ℝ) / 2 + (5 + δ) * ε)} (3 / 2) := by
  intro δ hδ
  have hd := half_pos hδ
  have h := gm_windows_of_equation151 he (show 0 ≤ 2 + δ / 2 by positivity) hd (hw _ hd)
  rwa [show 2 + δ / 2 + 3 + δ / 2 = 5 + δ by ring] at h

end Levent151
