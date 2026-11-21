import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! This checks the deduction in the manuscript given the two explicit inputs.
    It imports Mathlib alone. -/

namespace PaperCertification

/-- A right-hand power window is available after every starting threshold. -/
def UpperWindows (G : ℝ → ℝ) (exponent δ : ℝ) : Prop :=
  ∀ Y₀ : ℝ, ∃ Y : ℝ, max 1 Y₀ ≤ Y ∧
    ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (1 + δ) → G x ≤ x ^ exponent

/-- Both parameters are chosen before requesting any window. -/
theorem chooseWindowParameters (β ε₀ : ℝ) (hβ : 1 / 2 < β) (hε₀ : 0 < ε₀) :
    ∃ θ ε : ℝ, 1 / 2 < θ ∧ θ < 1 ∧ θ < β ∧
      0 < ε ∧ ε < ε₀ ∧ 1 / 2 + 9 * ε < θ := by
  let a : ℝ := min (β - 1 / 2) (1 / 2)
  have ha : 0 < a := lt_min (by linarith) (by norm_num)
  have haβ : a ≤ β - 1 / 2 := min_le_left _ _
  have haHalf : a ≤ 1 / 2 := min_le_right _ _
  let θ : ℝ := 1 / 2 + a / 2
  have hθ : 1 / 2 < θ := by dsimp [θ]; linarith
  let b : ℝ := min ε₀ ((θ - 1 / 2) / 9)
  have hb : 0 < b := lt_min hε₀ (by linarith)
  have hb₀ : b ≤ ε₀ := min_le_left _ _
  have hbθ : b ≤ (θ - 1 / 2) / 9 := min_le_right _ _
  refine ⟨θ, b / 2, hθ, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [θ]; linarith
  · dsimp [θ]; linarith
  · linarith
  · linarith
  · linarith

/-- The loss in the exponent is absorbed pointwise on every full window. -/
theorem upperWindows_monoExponent {G : ℝ → ℝ} {a b δ : ℝ}
    (ha : UpperWindows G a δ) (hab : a ≤ b) : UpperWindows G b δ := by
  intro Y₀
  obtain ⟨Y, hY, hbound⟩ := ha Y₀
  refine ⟨Y, hY, ?_⟩
  intro x hYx hx
  have hx₁ : 1 ≤ x := (le_max_left 1 Y₀).trans (hY.trans hYx)
  exact (hbound x hYx hx).trans (Real.rpow_le_rpow_of_exponent_le hx₁ hab)

/-- The supply hypothesis and the analytic exclusion criterion concern the same G.
    Detects encodes a regular zero covered by the analytic family. -/
theorem excludeRightOfHalf (G : ℝ → ℝ) {Point : Type*} (realPart : Point → ℝ) (Detects : Point → Prop) (ε₀ : ℝ)
    (hε₀ : 0 < ε₀)
    (supply : ∀ ε : ℝ, 0 < ε → ε < ε₀ → UpperWindows G (1 / 2 + 9 * ε) (1 / 2))
    (exclusion : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → UpperWindows G θ (1 / 2) →
      ∀ ρ : Point, θ < realPart ρ → ¬ Detects ρ) :
    ∀ ρ : Point, 1 / 2 < realPart ρ → ¬ Detects ρ := by
  intro ρ hρ
  obtain ⟨θ, ε, hθ, hθ₁, hθρ, hε, hε₀', hexp⟩ := chooseWindowParameters (realPart ρ) ε₀ hρ hε₀
  exact exclusion θ hθ hθ₁ (upperWindows_monoExponent (supply ε hε hε₀') hexp.le) ρ hθρ


/-- A fixed positive residue at distance d dominates the Cauchy remainder
    with radius r > d at every sufficiently large integer order. -/
theorem residueDominates {c d r M : ℝ} (hc : 0 < c) (hd : 0 < d) (hdr : d < r) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → M / r ^ k < c / d ^ (k + 1) := by
  have hr : 0 < r := hd.trans hdr
  have hratio : 1 < r / d := (one_lt_div hd).2 hdr
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt (M / (c / d)) hratio
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hpow : (r / d) ^ k₀ ≤ (r / d) ^ k :=
    pow_le_pow_right₀ hratio.le hk
  have hM : M < (c / d) * (r / d) ^ k := by
    have hs := (div_lt_iff₀ (div_pos hc hd)).mp (hk₀.trans_le hpow)
    rwa [mul_comm] at hs
  apply (div_lt_iff₀ (pow_pos hr _)).2
  calc
    M < (c / d) * (r / d) ^ k := hM
    _ = c / d ^ (k + 1) * r ^ k := by
      rw [div_pow, pow_succ]
      ring

#print axioms residueDominates
#print axioms chooseWindowParameters
#print axioms upperWindows_monoExponent
#print axioms excludeRightOfHalf

end PaperCertification
