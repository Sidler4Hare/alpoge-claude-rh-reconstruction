import Family
import PowerWindows
import MeanExtraction

noncomputable section

namespace Levent151

open Formalism Formalism.HC Formalism.D5 Formalism.BasicNotions Formalism.MainNotions
  Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
  Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
  Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LHost UpperTheory.Comparison₂ UpperTheory.Top Deduction.CH

/-- Data used in the two inequalities, retaining the ties to actual family points
and to their local weights. The rank budget uses the displayed Fourier scale b. -/
structure RealizedData (ψ : PChar) {ε : ℝ} (Fm : FamP ε) (x : ℝ) where
  i : Fm.Ix x
  m : ℕ
  f : ℕ
  N : ℕ
  pt : (Fm.D x i).R.A → Fm.Ix x
  av : ℕ → ℤ
  bv : ℕ → ℤ
  ell : AddChar (E0 × (Fm.D x i).R.A) ℂ → ℂ
  T2 : Finset (Fm.D x i).R.A
  a : (Fm.D x i).R.A → ℝ
  w : (Fm.D x i).R.A → Fin m → E0 × (Fm.D x i).R.A → ℝ
  b : ℝ
  b' : ℝ
  k : ℝ
  aE : ℝ
  η : ℝ
  X' : ℝ
  θ : ℝ
  points : TiePts Fm x (Fm.D x i).R.toFrame m f (Fm.D x i).host.q (Fm.D x i).host.d pt av bv
  weights : TieArith Fm x pt av (arithOf (Fm.D x i).host.toHostRaw) ell (Fm.D x i).host.TT T2 a w
  scales : ∀ u, aE = (Fm.L x (pt u)).sc.a ∧ b = (Fm.L x (pt u)).sc.b ∧
    b' = (Fm.L x (pt u)).sc.b' ∧ k = ((Fm.D x (pt u)).R.k : ℝ)
  host : EAtH (Level.cyc ψ) (Fm.D x i).host.toHostRaw (Fm.D x i).host.TT x ε 4
  rankBudget : VVle (Fm.D x i).host.E (Fm.D x i).R.t (Real.sqrt b)
  b_pos : 0 < b
  aE_nonneg : 0 ≤ aE
  k_pos : 0 < k
  m_upper : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)
  xm_le_k : x * m ≤ k
  sizes : SizesA (Fm.D x i).R.A0 (Fm.D x i).host.TT T2 a w N x b b' η X' θ
  thin : ThinScales (arithOf (Fm.D x i).host.toHostRaw) ell X' θ
  cost : CostWindows x (fPl (Fm.D x i).R.A) b η θ
  rest : RestSize ε x (Fintype.card (Fm.D x i).R.A) (Fm.D x i).host.TT.card T2.card m b k aE
  thick_subset : ∀ s ∈ T2, s ∈ (Fm.D x i).R.A0

namespace RealizedData

variable {ψ : PChar} {ε x : ℝ} {Fm : FamP ε} (R : RealizedData ψ Fm x)

def discrepancy (u : (Fm.D x R.i).R.A) : ℝ :=
  gapA (arithOf (Fm.D x R.i).host.toHostRaw) R.N R.ell (Fm.D x R.i).host.TT R.a R.w u

def bracket : ℝ :=
  paperBracket x ε (Fintype.card (Fm.D x R.i).R.A) (Fm.D x R.i).host.TT.card
    R.T2.card R.m R.b R.k R.aE

open Classical in
def cosetMean (v : (Fm.D x R.i).R.A) : ℝ :=
  (∑ u : (Fm.D x R.i).R.A0, R.discrepancy (v + u)) / (Fintype.card (Fm.D x R.i).R.A0 : ℝ)

theorem cosetMean_zero : R.cosetMean 0 = signedMeanGap (Fm.D x R.i).R.A0
    (arithOf (Fm.D x R.i).host.toHostRaw) R.N R.ell (Fm.D x R.i).host.TT R.a R.w := by
  classical
  simp [cosetMean, discrepancy, signedMeanGap]

theorem cosetMean_le {E : ℝ} (h : ∀ u, R.discrepancy u ≤ E) (v : (Fm.D x R.i).R.A) :
    R.cosetMean v ≤ E := by
  classical
  unfold cosetMean
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card (Fm.D x R.i).R.A0)).2
  calc _ ≤ ∑ _u : (Fm.D x R.i).R.A0, E := Finset.sum_le_sum fun u _ => h (v + u)
       _ = _ := by simp [mul_comm]

end RealizedData

/-- On any realized window record a signed bound at the identity coset suffices.
The threshold is chosen before the family, scale and host. -/
theorem retained_le_of_mean (ψ : PChar) {ε C : ℝ} (he : 0 < ε) (hC : 0 ≤ C) :
    ∃ x₁ : ℝ, ∀ x ≥ x₁, ∀ {Fm : FamP ε} (R : RealizedData ψ Fm x),
      R.cosetMean 0 ≤ x ^ (C * ε) * R.bracket →
      (Level.cyc ψ).Gm x ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) +
        4 * ((Level.cyc ψ).o : ℝ) * x ^ ((1 : ℝ) / 2 + ε) := by
  let Λ := Level.cyc ψ
  have ho : (0 : ℝ) ≤ Λ.o := Nat.cast_nonneg _
  have hw : |(3 * (Λ.o : ℝ) + 1)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith)
  obtain ⟨x₀, extract⟩ := ch_core_of_signedMean C ε 4 (koOf Λ) (3 * (Λ.o : ℝ) + 1)⁻¹
    (4 * (Λ.o : ℝ)) hC he hw
  refine ⟨max 1 x₀, fun x hx Fm R hMean => ?_⟩
  let H := (Fm.D x R.i).host
  let φ := (Fm.D x R.i).R.toFrame
  have hxpos : 0 < x := zero_lt_one.trans_le ((le_max_left _ _).trans hx)
  have hell : HostAddCharCompatible H.toHostRaw R.ell := R.weights.2.2.2.2
  rw [R.cosetMean_zero] at hMean
  have hBr := errorBracket_eq_paperBracket x ε (Fintype.card φ.A) H.TT.card R.T2.card R.m
    R.b R.k R.aE hxpos (by exact_mod_cast Fintype.card_pos) R.k_pos
  have bound := extract x ((le_max_right _ _).trans hx) φ.A R.m (arith H.toHostRaw) _ R.ell R.N
    H.TT R.T2 R.a R.w R.b R.b' R.k R.aE R.η R.X' R.θ φ.A0 (keptA Λ H.toHostRaw)
    (hostFactsS φ H.toHostAx) R.b_pos R.aE_nonneg R.k_pos R.m_upper R.xm_le_k
    R.sizes R.thin R.cost R.rest R.thick_subset
    (charsA Λ φ H.toHostAx H.TT _ _ 4 R.ell hxpos R.host hell) (by rwa [hBr])
  rw [gmA_eq Λ φ H.toHostAx H.TT _ _ 4 R.ell R.host hell] at bound
  exact bound.trans (add_le_add (le_refl _) (sigA_le Λ φ H.toHostAx H.TT _ _ 4 R.ell hxpos R.host hell))

/-- The actual tied index type is the entire host group. Use the same witnesses
before projecting to the cyclic subgroup or averaging on any of its cosets. -/
private theorem bounds_of_tied {ψ : PChar} {ε x K cHH eK CL : ℝ} {Fm : FamP ε}
    (hc : (GChi ψ).cls (3 / 2) Fm) (hf : Fm.x1 < x)
    (tied : ChainTied Fm 2 0 K cHH eK CL x) (hX : LargeX x ε K cHH eK) :
    ∃ R : RealizedData ψ Fm x, ∀ u, R.discrepancy u ≤
      quadraticConstant K cHH eK * x ^ (2 * ε) * R.bracket := by
  classical
  obtain ⟨i, m, f, pt, av, bv, Top, iT, D, C, Xpp, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hPts, hGlobal, _, hArith, hxx, heps, hDiv, hLoss, hHH, hId, hSize, hWin, hBN,
    ⟨⟨s1, s2, s3, s4, s5, s6, ⟨n1, n2, n3⟩, s8⟩, th, _⟩, hCost, hRest⟩ := tied
  have hTT : TT = (Fm.D x i).host.TT := by
    ext t
    rw [hArith.1 t, ← Fm.TT_eq x i, Finset.mem_image]
    exact ⟨fun ⟨s, hs, e⟩ => (Frame.A.val_injective _ e) ▸ hs, fun ht => ⟨t, ht, rfl⟩⟩
  subst TT
  obtain ⟨hE, hV⟩ := hc.2 x hf i
  rw [Fm.L_x x i hf, Fm.L_eps x i] at hE
  have hbEq : D.b = (Fm.L x i).sc.b := by
    rw [(hGlobal 0).2.1]
    simp only [Scale.b, Scale.L, Fm.L_x x _ hf, Fm.L_eps]
  obtain ⟨hx1, _, _, hb1, hxa, _, hm, hxm, heK, hk1, _⟩ := hWin.1
  have hxD : 0 < D.x := zero_lt_one.trans_le hx1
  have hb : 0 < D.b := zero_lt_one.trans_le hb1
  have hk : 0 < D.k := zero_lt_one.trans_le hk1
  have hLocal : LargeX D.x D.ε K C.cHH eK := by
    rw [hxx, heps]
    refine ⟨hX.1, le_trans ?_ hX.2⟩
    unfold KBig
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith only [hHH]) (by positivity)) (by linarith only [heK])
  let R : RealizedData ψ Fm x :=
    { i, m, f, N, pt, av, bv, ell, T2, a, w, b := D.b, b' := D.b', k := D.k, aE := D.a, η, X', θ
      points := hPts, weights := hArith
      scales := fun u => ⟨(hGlobal u).1, (hGlobal u).2.1, (hGlobal u).2.2.1, (hGlobal u).2.2.2.1⟩
      host := hE, rankBudget := by simpa only [hbEq] using hV
      b_pos := hb, aE_nonneg := (mul_nonneg hxD.le hb.le).trans hxa, k_pos := hk
      m_upper := by simpa only [hxx, heps] using hm
      xm_le_k := by simpa only [hxx] using hxm
      sizes := ⟨s1, s2, s3, s4, s5, s6, fun u _ => n1 u, fun u _ => n2 u,
        fun u _ => n3 u, fun u _ => s8 u⟩
      thin := th, cost := hCost, rest := hRest
      thick_subset := fun s hs => by
        obtain ⟨j, _, rfl⟩ := (hArith.2.1 0 s).1 hs
        exact Frame.digit_mem_cyclic_subgroup _ j }
  refine ⟨R, fun u => ?_⟩
  have hMain := Deduction.ch_top_main_eq D id _ N ell _ a w eT eP hId u
  have hGap : R.discrepancy u = D.ASK u - D.Main u := by
    rw [hId.2.2.2.2 u, hMain]
    simp only [R, RealizedData.discrepancy, gapA, Finset.sum_sub_distrib, id_eq]
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩ := hSize
  have hGeom := each_unit_bound_statement D C Xpp t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 u
  have hText : ErrText D ≤ R.bracket := by
    have hnT : D.nT = ((Fm.D x i).host.TT.card : ℝ) := by
      unfold Data.nT
      rw [Fintype.card_congr eT, Fintype.card_coe]
    have hPoly : ErrText D ≤ errorBracketSizeWindows D.x D.ε (Fintype.card (Fm.D x i).R.A)
        (Fm.D x i).host.TT.card T2.card m D.b D.k D.a := by
      unfold ErrText errorBracketSizeWindows
      rw [hnT]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      gcongr
      · exact hBN.1
      · exact hBN.2
    have hEq := errorBracket_eq_paperBracket D.x D.ε (Fintype.card (Fm.D x i).R.A)
      (Fm.D x i).host.TT.card T2.card m D.b D.k D.a hxD (by exact_mod_cast Fintype.card_pos) hk
    simpa only [hxx, heps, R, RealizedData.bracket] using hPoly.trans_eq hEq
  have hCoef : 0 ≤ quadraticConstant K cHH eK * D.x ^ (2 * D.ε) :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) (Real.rpow_nonneg hxD.le _)
  have hBound := (errX5at_quadratic D C Xpp eK K cHH hWin hLocal hDiv hLoss hHH u).trans
    (mul_le_mul_of_nonneg_left hText hCoef)
  rw [hxx, heps] at hBound
  rw [hGap]
  exact (show D.ASK u - D.Main u ≤ ErrX5at D C Xpp u by linarith only [hGeom]).trans hBound

/-- Original (15.1) and (15.2) with the actual geometric data. The quadratic
bound holds on the same window and dominates every coset mean from above. -/
theorem equation152 (ψ : PChar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (Fm : FamP ε) (A CH : ℝ), ChosenE Fm 3 CH ∧ 1 ≤ A ∧ ∀ Y₀ : ℝ, ∃ Y : ℝ, max 1 Y₀ ≤ Y ∧
        ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (3 / 2 : ℝ) →
          x ∈ Fm.Win ∧ ∃ R : RealizedData ψ Fm x,
            (∀ u, R.discrepancy u ≤ A * x ^ (2 * ε) * R.bracket) ∧
            (∀ v, R.cosetMean v ≤ A * x ^ (2 * ε) * R.bracket) ∧
            A * x ^ (2 * ε) * R.bracket ≤ x ^ (5 * ε) * R.bracket := by
  obtain ⟨ε₀, h₀, supply⟩ := arithmeticFamilyWithSizes ψ
  refine ⟨ε₀, h₀, fun ε he hs => ?_⟩
  obtain ⟨Fm, CH, hc, _, _, hChosen, _, _, _, K, cHH, eK, CL, x₀, ht⟩ :=
    supply ε he hs ⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  obtain ⟨xL, hL⟩ := large_x_eventually ε K cHH eK he
  obtain ⟨xA, hA⟩ := quadraticFactor_eventually K cHH eK he (show (0 : ℝ) < 3 by norm_num)
  refine ⟨Fm, quadraticConstant K cHH eK, CH, hChosen, one_le_pow₀ (le_max_left _ _), fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hw⟩ := hc.1 (max (max 1 Y₀) (max (Fm.x1 + 1) (max x₀ (max xL xA))))
  refine ⟨Y, (le_max_left _ _).trans hY, fun x hy hx => ?_⟩
  obtain ⟨_, hxF, hx₀, hxL, hxA⟩ := (show
    max 1 Y₀ ≤ x ∧ Fm.x1 + 1 ≤ x ∧ x₀ ≤ x ∧ xL ≤ x ∧ xA ≤ x by
      simpa only [max_le_iff] using hY.trans hy)
  have hGood := hw x hy hx
  obtain ⟨R, hR⟩ := bounds_of_tied hc (by linarith only [hxF]) (ht x hx₀ hGood) (hL x hxL)
  refine ⟨hGood, R, hR, R.cosetMean_le hR, mul_le_mul_of_nonneg_right ?_ ?_⟩
  · simpa only [show (2 : ℝ) + 3 = 5 by norm_num] using hA x hxA
  · have hb := R.b_pos
    have ha := R.aE_nonneg
    have hk := R.k_pos
    have hxpos : 0 < x := zero_lt_one.trans_le ((le_max_left _ _).trans ((le_max_left _ _).trans (hY.trans hy)))
    unfold RealizedData.bracket paperBracket
    positivity

end Levent151
