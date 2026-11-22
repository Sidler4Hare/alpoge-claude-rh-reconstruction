import TranslateUniformity
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes

namespace Levent151

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions
  Formalism.MainNotions.Inhab GlobalTheory.EX

/-- The replacement used by `hostGood_replaceSets` preserves the raw host and the
canonical auxiliary level. -/
theorem reselectHost_field_and_level {R : Ranks} (H : Host R) (T : Finset R.A)
    (U : Finset ℕ) (C₂ : ℝ) (hrange : ∀ a ∈ U, 4 * H.Lw * a < R.n0)
    (hrel : NoRel U H.Lw) :
    (replaceHostSets H T U C₂ hrange hrel).toHostAx = H.toHostAx ∧
    DC.q0H (replaceHostSets H T U C₂ hrange hrel) = DC.q0H H := ⟨rfl, rfl⟩

/-- This request retains the host witness actually used by `kitS`, even though the
level-prime list of the resulting D7 point is allowed to be larger. -/
def HasHostOrigin (C₈ C₅ c₆ Cb C₂ : ℝ) (s : Scale) (R : Ranks)
    (A : Formalism.HC.HostAx R.toFrame) (T : Finset R.A) (U : Finset ℕ) : Prop :=
  ∃ H : Host R, H.toHostAx = A ∧ H.TT = T ∧ H.T2 = U ∧ RankVal s R ∧
    H.CT2 = C₂ ∧ HostGood s C₈ C₅ c₆ Cb H (DC.q0H H)

theorem hostOrigin_of_from {C : FC} {p : Pt C} {R : Ranks} (H : Host R) {a b : R.A → ℤ}
    {M : ℕ} {c : Fin M → Fin (R.k - 2) → Bool} {u : ℕ} (h : p.From H a b c u)
    {C₈ C₅ c₆ Cb C₂ : ℝ} (hR : RankVal p.L.sc R) (hC : H.CT2 = C₂)
    (hH : HostGood p.L.sc C₈ C₅ c₆ Cb H (DC.q0H H)) :
    HasHostOrigin C₈ C₅ c₆ Cb C₂ p.L.sc p.D.R p.D.host.toHostAx p.D.host.TT p.D.host.T2 := by
  have hr := h.1
  have ha := h.field
  have ht := h.2.1
  have hu := h.2.2.1
  subst hr
  exact ⟨H, (eq_of_heq ha).symm, (Finset.image_injective (Formalism.HC.Frame.A.val_injective _) ht).symm,
    hu.symm, hR, hC, hH⟩

end Levent151
