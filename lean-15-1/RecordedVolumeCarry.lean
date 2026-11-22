import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAbsEntrySumNonneg

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj
open Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.CovHtCmp
open scoped ENNReal Classical

namespace Levent151.RecordedMixed

/-- Carry the recorded volume to the original Bergman volume on the same
component, with only the cost of the carrying section. -/
theorem recorded_compVol_le_volL {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
    {D : D7} (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ j, Frame ((U σ).X j).Ψ r)
    (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (cc t η : ℝ)
    (hM : Mult U x V dict Z u u' cc) (hη : 0 < η) :
    compVol U x 8 (recVals Xo c) Z (wtOf Dw u' 0) t ≤
      volL U x V dict 8 Z (wtOf Dw u 0) (t + cc + η) := by
  obtain ⟨hN, θ, e, s, ⟨_, hθ, hcar⟩, hF, ⟨hs, hI⟩, hcc⟩ := hM
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_elt_prescribed_valuations_balanced_archimedean c.F e s hs
  refine countVol_mono_eventually _ _ _ ((Filter.eventually_ge_atTop ⌈|C| / η⌉₊).mono fun k hk => ?_)
  have hCη : C ≤ ((8 * k : ℕ) : ℝ) * η := by
    have h1 := (div_le_iff₀ hη).1 (Nat.ceil_le.1 hk)
    have h2 : (0 : ℝ) ≤ k * η := mul_nonneg (Nat.cast_nonneg _) hη.le
    push_cast
    linarith [le_abs_self C]
  obtain ⟨α, hα, hfin, hinf⟩ := hC (8 * k)
  refine Set.encard_le_encard_of_injOn
    (f := fun f => ⟨α • (θ ^ k * f), Submodule.smul_mem _ _ (hcar k f f.2)⟩)
    (fun f hf => ⟨fun la v hv => ?_, ?_⟩) ?_
  · exact fin_bound hN hF f.2 hv hα (b := 0) (by simpa using hf.1 la v hv)
      (by simpa using hfin la)
  · intro σ hσ y hy
    show ENNReal.ofReal (homN (U σ) x _ (α • (θ ^ k * (f : Rul Xo c))) _) ^ 2 ≤ _
    have hEven := even_nsmul_snd (even_wtOf u' 0) (8 * k)
    rw [FlatLine.homN_smul, wt_split u u',
      homN_pow_mul_eq (U σ) x (even_wtOf _ 0) hEven θ f y.2.2]
    refine inf_bound (homN_nonneg _ _ _ _ _) (homN_nonneg _ _ _ _ _)
      (norm_pos_iff.2 ((map_ne_zero σ).2 hα)) (hI σ hσ y hy) (hf.2 σ hσ _ hy)
      ((hinf σ).trans ?_)
    nlinarith [mul_le_mul_of_nonneg_left hcc (Nat.cast_nonneg (α := ℝ) (8 * k))]
  · intro f _ g _ heq
    have hval := congrArg (genVal Z) (congrArg Subtype.val heq)
    simp only [map_smul, map_mul, map_pow] at hval
    have hfg := mul_left_cancel₀ (pow_ne_zero k hθ) (smul_right_injective _ hα hval)
    exact Subtype.ext (sub_eq_zero.1 (eq_zero_of_genVal (sub_mem f.2 g.2) (by rw [map_sub, hfg, sub_self])))

end Levent151.RecordedMixed

#print axioms Levent151.RecordedMixed.recorded_compVol_le_volL
