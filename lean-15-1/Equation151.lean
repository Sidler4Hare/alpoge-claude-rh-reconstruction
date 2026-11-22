import Family
import Downstream

namespace Levent151

open Formalism.HC Formalism.MainNotions UpperTheory.Top

/-- Equation (15.1) for the primitive cyclic family of the original development. -/
theorem equation151 (ψ : PChar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ Fm : FamP ε, Equation151Windows ψ Fm := by
  obtain ⟨ε₀, h₀, supply⟩ := arithmeticFamily ψ
  refine ⟨ε₀, h₀, fun ε he hs => ?_⟩
  obtain ⟨Fm, hc, K, cHH, eK, CL, x₀, ht⟩ := supply ε he hs
  exact ⟨Fm, windows_of_tied he Fm hc ht⟩

/-- At fixed ε the same family works for all δ, with an explicit uniform
coefficient before the square power and an ensuing bound for the retained sum. -/
theorem equation151_strengthened (ψ : PChar) : StrengthenedWindows ψ := by
  obtain ⟨ε₀, h₀, supply⟩ := arithmeticFamily ψ
  refine ⟨ε₀, h₀, fun ε he hs => ?_⟩
  obtain ⟨Fm, hc, K, cHH, eK, CL, x₀, ht⟩ := supply ε he hs
  obtain ⟨hq, hp⟩ := quadratic_windows_of_tied he Fm hc ht
  exact ⟨Fm, quadraticConstant K cHH eK, one_le_pow₀ (le_max_left _ _), hq,
    fun δ hd => ⟨hp δ hd, gm_windows_of_quadratic he hp δ hd⟩⟩

theorem primitiveHalfPlane_via_equation151 (ψ : PChar) : ψ.ZeroFreeAbove (1 / 2) :=
  primitiveHalfPlane_of_strengthened (equation151_strengthened ψ)

theorem riemannHypothesis_via_equation151 : RiemannHypothesis :=
  riemannHypothesis_of_strengthened (equation151_strengthened PChar.one)

end Levent151
