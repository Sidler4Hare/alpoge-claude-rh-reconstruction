import Development.AutomorphicArithmetic.PrimitiveCosets.CoreGm

/-! Equation (15.1) on an actual arithmetic host in the Alpöge development.
The level, its host and its top set are fixed before the witnesses are chosen.
The same weights and logarithmic derivatives serve every translate. -/

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

/-- The four terms inside the parentheses in (15.1). -/
def paperBracket (x eps : ℝ) (n nT n2 m : ℕ) (b k aE : ℝ) : ℝ :=
  (nT : ℝ) * aE + nT * aE * (m : ℝ) ^ 2 / k +
    2 * (n : ℝ) * (m : ℝ) ^ 2 * b * x ^ eps +
    (m : ℝ) * b * n2 * k * x ^ (2 * eps) / (n : ℝ) ^ 2

theorem errorBracket_eq_paperBracket (x eps : ℝ) (n nT n2 m : ℕ) (b k aE : ℝ)
    (hx : 0 < x) (hn : 0 < (n : ℝ)) (hk : 0 < k) :
    errorBracketSizeWindows x eps n nT n2 m b k aE =
      paperBracket x eps n nT n2 m b k aE := by
  unfold errorBracketSizeWindows paperBracket
  rw [show 2 * eps = eps + eps by ring, Real.rpow_add hx, Real.rpow_neg hx.le]
  have hp := (Real.rpow_pos_of_pos hx eps).ne'
  field_simp [hn.ne', hk.ne', hp]
  ring

/-- The host assumptions needed by the Fourier extraction and the literal
pointwise inequality share a single existential witness. -/
def PointwiseAt (Λ : Level) {φ : Frame} (H : HostAx φ) (TT : Finset φ.A)
    (eps x : ℝ) (factor : ℝ := x ^ (5 * eps)) : Prop :=
  EAtH Λ H.toHostRaw TT x eps 4 ∧
  HostFactsS (arith H.toHostRaw) (insert H.q H.small) ∧
  ∃ (m : ℕ) (ell : AddChar (E0 × φ.A) ℂ → ℂ) (N : ℕ) (T2 : Finset φ.A)
    (a : φ.A → ℝ) (w : φ.A → Fin m → E0 × φ.A → ℝ) (b b' k aE η X' θ : ℝ),
    HostAddCharCompatible H.toHostRaw ell ∧
    0 < b ∧ 0 ≤ aE ∧ 0 < k ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + eps / 2) ∧ x * m ≤ k ∧
    SizesA φ.A0 TT T2 a w N x b b' η X' θ ∧ ThinScales (arith H.toHostRaw) ell X' θ ∧
    CostWindows x (fPl φ.A) b η θ ∧ RestSize eps x (Fintype.card φ.A) TT.card T2.card m b k aE ∧
    (∀ s ∈ T2, s ∈ φ.A0) ∧
    CharsA ell φ.A0 (keptA Λ H.toHostRaw) TT (3 * (Λ.o : ℝ) + 1)⁻¹ (4 * (Λ.o : ℝ))
      (koOf Λ) 4 eps x ∧
    (∀ y, GmA (arith H.toHostRaw) ell (keptA Λ H.toHostRaw) (3 * (Λ.o : ℝ) + 1)⁻¹ y = Λ.Gm y) ∧
    SigA (arith H.toHostRaw) ell φ.A0 (keptA Λ H.toHostRaw) x ≤
      4 * (Λ.o : ℝ) * x ^ ((1 : ℝ) / 2 + eps) ∧
    ∀ u ∈ φ.A0,
      (∑ t ∈ TT, ∑ j : Fin m,
        (ASK (arith H.toHostRaw) N (a t) t (w u j) - (MAIN ell (a t) (w u j)).re)) ≤
      factor * paperBracket x eps (Fintype.card φ.A) TT.card T2.card m b k aE

theorem pointwiseAt_of_core {Λ : Level} {φ : Frame} {H : HostAx φ} {TT : Finset φ.A}
    {eps x K cHH eK : ℝ}
    (hCore : CoreAtH H.toHostRaw TT 2 0 K cHH eK eps x) (hLX : LargeX x eps K cHH eK)
    (hE : EAtH Λ H.toHostRaw TT x eps 4) : PointwiseAt Λ H TT eps x := by
  obtain ⟨U, iU, tr, W, iW, nW, Top, iTop, m, f, Dd, C, Xpp, ell, N, T2, a, w, eT, eP,
    η, X', θ, hell, hxx, heps, hDiv, hLoss, hHH, hcov, hId, hSize, hWin, hBN, hSizes,
    hThin, hCost, hRest, hT2⟩ := hCore
  subst hxx heps
  obtain ⟨hx1, he, _, hb1, hxa, _, hm, hxm, heK, hk1, _⟩ := hWin.1
  have hx : 0 < Dd.x := lt_of_lt_of_le zero_lt_one hx1
  have hb : 0 < Dd.b := lt_of_lt_of_le zero_lt_one hb1
  have hk : 0 < Dd.k := lt_of_lt_of_le zero_lt_one hk1
  have ha : 0 ≤ Dd.a := (mul_nonneg hx.le hb.le).trans hxa
  have hLocal : LargeX Dd.x Dd.ε K C.cHH eK := by
    refine ⟨hLX.1, le_trans ?_ hLX.2⟩
    unfold KBig
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith only [hHH]) (by positivity)) (by linarith only [heK])
  have hPow : Dd.x ^ (CErr C * Dd.ε) ≤ Dd.x ^ (5 * Dd.ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hx1
    apply mul_le_mul_of_nonneg_right _ he.le
    unfold CErr
    linarith only [hDiv, hLoss]
  have hBr : 0 ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card φ.A)
      TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold errorBracketSizeWindows
    positivity
  refine ⟨hE, hostFactsS φ H, m, ell, N, T2, a, w, Dd.b, Dd.b', Dd.k, Dd.a, η, X', θ,
    hell, hb, ha, hk, hm, hxm, hSizes, hThin, hCost, hRest, hT2,
    charsA Λ φ H TT _ _ 4 ell hx hE hell, gmA_eq Λ φ H TT _ _ 4 ell hE hell,
    sigA_le Λ φ H TT _ _ 4 ell hx hE hell, ?_⟩
  intro u hu
  obtain ⟨v, rfl⟩ := hcov u hu
  have hn : 0 < (Fintype.card φ.A : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [← errorBracket_eq_paperBracket _ _ _ _ _ _ _ _ _ hx hn hk]
  exact (Deduction.ch_top Dd tr C Xpp eK K _ ell N TT T2 a w eT eP hId hSize hWin hBN
    hLocal v).trans (mul_le_mul_of_nonneg_right hPow hBr)

end Levent151
