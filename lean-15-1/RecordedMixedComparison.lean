import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumAbsExOfLe

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped NNReal
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.Frames GlobalTheory.AllWt
open GlobalTheory.CompHt GlobalTheory.CovHt

namespace Levent151.RecordedMixed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Algebra c.F C] [StarRing (𝓞 E)] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- Compare one concrete Hodge--Tate test with its recorded integral frame,
including rules whose evaluation is zero. -/
theorem paired_frame_displacement {T : CDVR} {io : c.F →+* T.Fr}
    {y₀ : IntFr Xo c T io} (hy : y₀.IsAlg)
    {k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C} {y : FrPt Xo c C}
    (h : IsHTFrame p v O y₀ k y) {la : HeightOneSpectrum (𝓞 c.F)} {e : ℕ}
    (ho : OverLa la T.V io e) (u : Weight Dw) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c (exOf Dw u 0)) :
    ∃ d : ℝ, |d| ≤ (vLa la (p : c.F) : ℝ) * htEx E p * l1 u ∧
      val_vw la p v (evR Xo c f y) = nval T.V e (evI y₀ f) + (d : EReal) := by
  let _ := io.toAlgebra
  obtain ⟨z, t, hz, ht, h0, hs⟩ := FrameCmp.exists_frBor hy h
  have he : (0 : ℝ) ≤ vLa la (p : c.F) := by
    have hnat := vAdd_int_nonneg la (a := (p : 𝓞 c.F)) (by simpa using (Fact.out : p.Prime).ne_zero)
    exact_mod_cast (show (0 : ℤ) ≤ vLa la (p : c.F) by simpa [vLa, Formalism.BasicNotions.vAdd] using hnat)
  have hx : 0 ≤ htEx E p := by
    have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact add_nonneg (div_nonneg zero_le_one (by linarith)) (by positivity)
  rw [FlagTan.evR_frBor hf ht, FlagTan.evR_frMap hf.1 hz, val_vw_mul,
    h.val_vw_map ho, add_comm, val_vw_of_ne la p v (Units.ne_zero _)]
  refine ⟨_, ?_, rfl⟩
  rw [abs_mul, abs_of_nonneg he, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ he
  rw [Units.coe_prod, map_prod, NNReal.coe_prod, Real.log_prod fun i _ =>
    NNReal.coe_ne_zero.2 ((Valuation.ne_zero_iff v).2 (Units.ne_zero _)), Fintype.sum_option]
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, NNReal.coe_zpow, Real.log_zpow,
    h0, NNReal.coe_one, Real.log_one, mul_zero, zero_add, Finset.sum_div]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (FrameCmp.sum_abs_exOf_le u) hx)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [mul_div_assoc, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hs s) (abs_nonneg _)

end Levent151.RecordedMixed

#print axioms Levent151.RecordedMixed.paired_frame_displacement
