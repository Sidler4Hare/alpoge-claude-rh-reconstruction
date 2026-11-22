import PowerWindows
import Development.AutomorphicArithmetic.PrimitiveCosets.Imports
import Formalism.ZetaNonvanishing.RHofHalfPlane

namespace Levent151

open Formalism.HC Formalism.MainNotions UpperTheory.Comparison₂

/-- Arbitrarily late complete intervals for a fixed cyclic level and a fixed δ. -/
def GmWindows (ψ : PChar) (δ : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    HasWindows {x | (Level.cyc ψ).Gm x ≤ x ^ ((1 : ℝ) / 2 + (5 + δ) * ε)} (3 / 2)

/-- The precise common-family output consumed from the arithmetic construction. -/
def StrengthenedWindows (ψ : PChar) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ (Fm : FamP ε) (A : ℝ), 1 ≤ A ∧
      Equation151Windows ψ Fm (fun x => A * x ^ (2 * ε)) ∧
      ∀ δ : ℝ, 0 < δ →
        Equation151Windows ψ Fm (fun x => x ^ ((2 + δ) * ε)) ∧
        HasWindows {x | Equation151At ψ Fm x (x ^ ((2 + δ / 2) * ε)) ∧
          (Level.cyc ψ).Gm x ≤ x ^ ((1 : ℝ) / 2 + (5 + δ) * ε)} (3 / 2)

theorem gmWindows_of_strengthened {ψ : PChar} (h : StrengthenedWindows ψ)
    {δ : ℝ} (hδ : 0 < δ) : GmWindows ψ δ := by
  obtain ⟨ε₀, h₀, supply⟩ := h
  refine ⟨ε₀, h₀, fun ε he hs => ?_⟩
  obtain ⟨_, _, _, _, hδs⟩ := supply ε he hs
  exact ((hδs δ hδ).2).mono (x0 := 1) fun _ _ hpoint => hpoint.2

/-- The signed Landau criterion applies to every retained primitive character. -/
theorem zeroFreeLevel_of_gmWindows {ψ : PChar} {δ : ℝ} (h : GmWindows ψ δ) :
    (Level.cyc ψ).ZeroFreeLevel := by
  obtain ⟨ε₀, h₀, supply⟩ := h
  intro χ hχ s hs
  let d := min (s.re - 1 / 2) (1 / 2)
  have hd : 0 < d := lt_min (by linarith) (by norm_num)
  have hd₁ : d ≤ s.re - 1 / 2 := min_le_left _ _
  have hd₂ : d ≤ 1 / 2 := min_le_right _ _
  obtain ⟨ε, he, hsmall, hmargin⟩ := exists_small_eps (5 + δ) (half_pos hd) h₀
  apply formB (Level.cyc ψ) (3 / 2) (by norm_num) (1 / 2 + d / 2) (by linarith) (by linarith)
    _ χ hχ s (by linarith)
  exact (supply ε he hsmall).mono (x0 := 1) fun x hx hw =>
    hw.trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hmargin]))

theorem primitiveHalfPlane_of_strengthened {ψ : PChar} (h : StrengthenedWindows ψ) :
    ψ.ZeroFreeAbove (1 / 2) :=
  zeroFreeLevel_of_gmWindows (gmWindows_of_strengthened h (δ := 1) zero_lt_one) ψ (Level.mem_cyc ψ)

/-- For the classical conclusion only the window supply at conductor one is required. -/
theorem riemannHypothesis_of_strengthened (h : StrengthenedWindows PChar.one) :
    RiemannHypothesis := by
  apply Formalism.riemannHypothesis_of_zero_free_halfPlane
  intro s hs
  have hz := primitiveHalfPlane_of_strengthened h s hs
  change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0 at hz
  simpa only [DirichletCharacter.LFunction_modOne_eq] using hz

end Levent151
