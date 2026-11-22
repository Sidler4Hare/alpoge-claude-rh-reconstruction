import Pointwise

/-! Separate the division term before bounding the remaining geometric error.
Only the error formula is evaluated at a second tuple of constants. The
lattices, the division inequality and the slope comparison use the original tuple. -/

noncomputable section

open Finset Deduction.CH Formalism Formalism.HC Formalism.D5
  Formalism.RankGapBounds.WeightedMeanData
  Formalism.LFunctionChainParameters.WeightedSlopeBounds
  Formalism.LFunctionChainParameters.characterSumData
  Formalism.LFunctionChainParameters.ThickSetMeanBounds
  Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LHost UpperTheory.Comparison₂

namespace Levent151

def sharpFactor (K x eps : ℝ) : ℝ :=
  x ^ (3 * eps) + K * (x ^ (2 * eps) - 1)

theorem errX5at_refined {U : Type} [Fintype U] {W : U → Type}
    [∀ u, Fintype (W u)] [∀ u, Nonempty (W u)] {Top : Type} [Fintype Top]
    {m f : ℕ} (D : Data U W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (hW : ErrWindows D C Xpp eK K) (hX : LargeX D.x D.ε K C.cHH eK)
    (hDiv : C.eDiv ≤ 2) (hLoss : C.eLoss ≤ 0) (u : U) :
    ErrX5at D C Xpp u ≤ sharpFactor K D.x D.ε * ErrText D := by
  let C₀ := { C with eDiv := 0 }
  obtain ⟨⟨hx, he, he1, hb, hxb, hnT, hm, hxm, heK, hk, hkx, hka, hL0, hL, hLa0, hLa,
    hb', hkb', hXp0, hXp, haT, hB, hN, hLog, hDel, hEta, hBar, hC⟩, hTail⟩ := hW
  obtain ⟨cD, cDK, cE, cEK, cH, cHK, cC, cCK, cS, cSK, c1, c1K, cL, cLK, ed, el, hh⟩ := hC
  have hW₀ : ErrWindows D C₀ Xpp eK K :=
    ⟨⟨hx, he, he1, hb, hxb, hnT, hm, hxm, heK, hk, hkx, hka, hL0, hL, hLa0, hLa,
      hb', hkb', hXp0, hXp, haT, hB, hN, hLog, hDel, hEta, hBar,
      cD, cDK, cE, cEK, cH, cHK, cC, cCK, cS, cSK, c1, c1K, cL, cLK,
      le_rfl, el, hh⟩, hTail⟩
  have hbase := errX5at_le D C₀ Xpp eK K hW₀ hX u
  have hExp : CErr C₀ = 3 := by simp [CErr, C₀, le_antisymm hLoss el]
  rw [hExp] at hbase
  have hid : ErrX5at D C Xpp u = ErrX5at D C₀ Xpp u +
      C.cDiv * ((m : ℝ) * (D.B0 + D.Nc)) * (D.x ^ (C.eDiv * D.ε) - 1) := by
    unfold ErrX5at
    rw [show D.LoP C₀ = D.LoP C from rfl, show MLo5 D C₀ Xpp = MLo5 D C Xpp from rfl,
      show UBar5 D C₀ Xpp = UBar5 D C Xpp from rfl]
    simp only [C₀, zero_mul, Real.rpow_zero, mul_one]
    ring
  have hK : 0 ≤ K := cD.trans cDK
  have ha : 0 ≤ D.a := (mul_nonneg (by linarith only [hx]) (by linarith only [hb])).trans hxb
  have hscale : 0 ≤ D.nT * D.a * (1 + (m : ℝ) ^ 2 / D.k) := by
    have : 0 ≤ D.nT := by linarith only [hnT]
    have : 0 ≤ D.k := by linarith only [hk]
    positivity
  have hM : 0 ≤ (m : ℝ) * (D.B0 + D.Nc) := by positivity
  have hME : (m : ℝ) * (D.B0 + D.Nc) ≤ ErrText D := by
    unfold ErrText
    linarith only [hscale]
  have hone := Real.one_le_rpow hx (mul_nonneg ed he.le)
  have hp := Real.rpow_le_rpow_of_exponent_le hx (mul_le_mul_of_nonneg_right hDiv he.le)
  have hcoeff := mul_le_mul cDK hME hM hK
  have hcorr := mul_le_mul hcoeff (sub_le_sub_right hp 1) (sub_nonneg.mpr hone)
    (mul_nonneg hK (hM.trans hME))
  rw [hid]
  calc _ ≤ D.x ^ (3 * D.ε) * ErrText D + K * ErrText D * (D.x ^ (2 * D.ε) - 1) :=
          add_le_add hbase hcorr
       _ = sharpFactor K D.x D.ε * ErrText D := by unfold sharpFactor; ring

theorem sharpFactor_nonneg {K x eps : ℝ} (hK : 0 ≤ K) (hx : 1 ≤ x) (he : 0 ≤ eps) :
    0 ≤ sharpFactor K x eps := by
  unfold sharpFactor
  exact add_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)
    (mul_nonneg hK (sub_nonneg.mpr (Real.one_le_rpow hx (by positivity))))

/-- The bound is uniform once the family's K and epsilon have been chosen. -/
theorem sharpFactor_eventually {K eps δ : ℝ} (he : 0 < eps) (hδ : 0 < δ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, sharpFactor K x eps ≤ x ^ ((3 + δ) * eps) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop he).eventually_ge_atTop (max 1 K)).and
      ((tendsto_rpow_atTop (mul_pos hδ he)).eventually_ge_atTop 2))
  refine ⟨max 1 x₀, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hxpos := zero_lt_one.trans_le hx1
  obtain ⟨hK, hδx⟩ := hx₀ x ((le_max_right _ _).trans hx)
  have htwo := Real.one_le_rpow hx1 (show 0 ≤ 2 * eps by positivity)
  have hsmall : K * (x ^ (2 * eps) - 1) ≤ x ^ (3 * eps) := by
    calc K * (x ^ (2 * eps) - 1) ≤ x ^ eps * (x ^ (2 * eps) - 1) :=
           mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hK) (sub_nonneg.mpr htwo)
         _ ≤ x ^ eps * x ^ (2 * eps) :=
           mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hxpos.le _)
         _ = x ^ (3 * eps) := by rw [← Real.rpow_add hxpos]; congr 1; ring
  have hlarge := mul_le_mul_of_nonneg_left hδx (Real.rpow_nonneg hxpos.le (3 * eps))
  unfold sharpFactor
  rw [show (3 + δ) * eps = 3 * eps + δ * eps by ring, Real.rpow_add hxpos]
  linarith only [hsmall, hlarge]

/-- A uniform numerical error bound after the family constants and scale are fixed. -/
def ErrorBoundAt (eps x K cHH eK bound : ℝ) : Prop :=
  ∀ {U : Type} [Fintype U] {W : U → Type} [∀ u, Fintype (W u)] [∀ u, Nonempty (W u)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U W Top m f) (C : Consts) (Xpp : ℝ),
    D.x = x → D.ε = eps → C.eDiv ≤ 2 → C.eLoss ≤ 0 → C.cHH ≤ cHH →
    ErrWindows D C Xpp eK K → LargeX D.x D.ε K C.cHH eK →
    0 ≤ bound ∧ ∀ u, ErrX5at D C Xpp u ≤ bound * ErrText D

/-- Convert a scalar estimate into the host's character data and all its translate bounds. -/
theorem pointwiseAt_of_errorBound {Λ : Level} {φ : Frame} {H : HostAx φ} {TT : Finset φ.A}
    {eps x K cHH eK bound factor : ℝ} (hCore : CoreAtH H.toHostRaw TT 2 0 K cHH eK eps x)
    (hLX : LargeX x eps K cHH eK) (hE : EAtH Λ H.toHostRaw TT x eps 4)
    (getBound : ErrorBoundAt eps x K cHH eK bound) (hFactor : bound ≤ factor) :
    PointwiseAt Λ H TT eps x factor := by
  obtain ⟨U, iU, tr, W, iW, nW, Top, iTop, m, f, Dd, C, Xpp, ell, N, T2, a, w, eT, eP,
    η, X', θ, hell, hxx, heps, hDiv, hLoss, hHH, hcov, hId, hSize, hWin, hBN, hSizes,
    hThin, hCost, hRest, hT2⟩ := hCore
  subst hxx heps
  obtain ⟨hx1, _, _, hb1, hxa, _, hm, hxm, heK, hk1, _⟩ := hWin.1
  have hx : 0 < Dd.x := zero_lt_one.trans_le hx1
  have hb : 0 < Dd.b := zero_lt_one.trans_le hb1
  have hk : 0 < Dd.k := zero_lt_one.trans_le hk1
  have ha : 0 ≤ Dd.a := (mul_nonneg hx.le hb.le).trans hxa
  have hLocal : LargeX Dd.x Dd.ε K C.cHH eK := by
    refine ⟨hLX.1, le_trans ?_ hLX.2⟩
    unfold KBig
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith only [hHH]) (by positivity)) (by linarith only [heK])
  have hnT : Dd.nT = (TT.card : ℝ) := by
    unfold Data.nT
    rw [Fintype.card_congr eT, Fintype.card_coe]
  have htext : ErrText Dd ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card φ.A)
      TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold ErrText errorBracketSizeWindows
    rw [hnT]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    gcongr
    · exact hBN.1
    · exact hBN.2
  have hBr : 0 ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card φ.A)
      TT.card T2.card m Dd.b Dd.k Dd.a := by unfold errorBracketSizeWindows; positivity
  refine ⟨hE, hostFactsS φ H, m, ell, N, T2, a, w, Dd.b, Dd.b', Dd.k, Dd.a, η, X', θ,
    hell, hb, ha, hk, hm, hxm, hSizes, hThin, hCost, hRest, hT2,
    charsA Λ φ H TT _ _ 4 ell hx hE hell, gmA_eq Λ φ H TT _ _ 4 ell hE hell,
    sigA_le Λ φ H TT _ _ 4 ell hx hE hell, ?_⟩
  intro u hu
  obtain ⟨v, rfl⟩ := hcov u hu
  have hmain := Deduction.ch_top_main_eq Dd tr (arith H.toHostRaw) N ell TT a w eT eP hId v
  have hid : gapA (arith H.toHostRaw) N ell TT a w (tr v) = Dd.ASK v - Dd.Main v := by
    rw [hId.2.2.2.2 v, hmain]
    simp only [gapA, Finset.sum_sub_distrib]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hSize
  have hGeom := each_unit_bound_statement Dd C Xpp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v
  obtain ⟨hNonneg, hErr⟩ := getBound Dd C Xpp rfl rfl hDiv hLoss hHH hWin hLocal
  have hErr' := mul_le_mul_of_nonneg_left htext hNonneg
  have hn : 0 < (Fintype.card φ.A : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [← errorBracket_eq_paperBracket _ _ _ _ _ _ _ _ _ hx hn hk]
  change gapA _ _ _ _ _ _ _ ≤ _
  rw [hid]
  exact (show Dd.ASK v - Dd.Main v ≤ ErrX5at Dd C Xpp v by linarith only [hGeom]).trans
    ((hErr v).trans (hErr'.trans (mul_le_mul_of_nonneg_right hFactor hBr)))

theorem pointwiseAt_of_sharpFactor {Λ : Level} {φ : Frame} {H : HostAx φ} {TT : Finset φ.A}
    {eps x K cHH eK factor : ℝ} (hCore : CoreAtH H.toHostRaw TT 2 0 K cHH eK eps x)
    (hLX : LargeX x eps K cHH eK) (hE : EAtH Λ H.toHostRaw TT x eps 4)
    (hFactor : sharpFactor K x eps ≤ factor) : PointwiseAt Λ H TT eps x factor := by
  apply pointwiseAt_of_errorBound hCore hLX hE ?_ hFactor
  intro U _ W _ _ Top _ m f D C Xpp hx he hDiv hLoss _ hW hX
  subst hx he
  obtain ⟨hx1, heps, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, hC⟩ := hW.1
  exact ⟨sharpFactor_nonneg (hC.1.trans hC.2.1) hx1 heps.le,
    errX5at_refined D C Xpp eK K hW hX hDiv hLoss⟩

end Levent151
