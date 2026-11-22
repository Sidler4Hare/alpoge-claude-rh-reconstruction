import Sharper

/-! In the numerical inequality `core_ineq`, compare with fixed values for
the logarithms and the two lengths. In the actual error, at most two of
these scale factors occur in a monomial. -/

noncomputable section
open Formalism.RankGapBounds.WeightedMeanData
  Formalism.LFunctionChainParameters.WeightedSlopeBounds
  Formalism.LFunctionChainParameters.LErr

namespace Levent151

def quadraticConstant (K H eK : ℝ) : ℝ := (max 1 (KBig K H eK)) ^ 3

set_option maxHeartbeats 4000000 in
theorem errX5at_quadratic {U : Type} [Fintype U] {W : U → Type}
    [∀ u, Fintype (W u)] [∀ u, Nonempty (W u)] {Top : Type} [Fintype Top]
    {m f : ℕ} (D : Data U W Top m f) (C : Consts) (Xpp eK K H : ℝ)
    (hW : ErrWindows D C Xpp eK K) (hX : LargeX D.x D.ε K C.cHH eK)
    (hDiv : C.eDiv ≤ 2) (hLoss : C.eLoss ≤ 0) (hH : C.cHH ≤ H) (u : U) :
    ErrX5at D C Xpp u ≤ quadraticConstant K H eK * D.x ^ (2 * D.ε) * ErrText D := by
  obtain ⟨⟨hx, he, he1, hb, hxb, hnT, hm, hxm, heK, hk1, hkx, hka, hL0, hL, hLa0, hLa,
    hb', hkb', hXp0, hXp, haT, hB0, hNc, hWcard, hDel, hEta, hBar, hC⟩, hTail⟩ := hW
  obtain ⟨c1, c1', c2, c2', c3, c3', c4, c4', c5, c5', c6, c6', c7, c7', hD, hLs, hHH⟩ := hC
  let y := D.x ^ D.ε
  let S := max 1 (KBig K H eK)
  have hy : 1 ≤ y := Real.one_le_rpow hx he.le
  have hS : 1 ≤ S := le_max_left _ _
  have hK : 0 ≤ K := c1.trans c1'
  have hH0 : 0 ≤ H := hHH.trans hH
  have hx0 : 0 < D.x := zero_lt_one.trans_le hx
  have hb0 : 0 ≤ D.b := zero_le_one.trans hb
  have hn0 : 0 ≤ D.nT := zero_le_one.trans hnT
  have hba := (le_mul_of_one_le_left hb0 hx).trans hxb
  have ha1 := hb.trans hba
  have ha0 := zero_le_one.trans ha1
  have hM : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hk := zero_lt_one.trans_le hk1
  have hmx : (m : ℝ) ≤ D.x := hm.trans (calc
    D.x ^ ((1 : ℝ)/2 + D.ε/2) ≤ D.x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith only [he1])
    _ = D.x := Real.rpow_one _)
  have hMk := (le_mul_of_one_le_left hM hx).trans hxm
  have hMb := (mul_le_mul_of_nonneg_right hmx hb0).trans hxb
  have hs0 : 0 ≤ D.sumA := Finset.sum_nonneg fun t _ => (haT t).1
  have hs : D.sumA ≤ 2 * (D.nT * D.a) := by
    unfold Data.sumA Data.nT
    calc ∑ t, D.aT t ≤ ∑ _t : Top, 2 * D.a := Finset.sum_le_sum fun t _ => (haT t).2
         _ = _ := by simp; ring
  have hlW := ((hWcard u).trans (sub_three_mul_log_two_le hk.le)).trans hka
  have hlk := log_le_of_le_rpow hx heK hk hkx hX.1 hy
  have hlH : Real.log (1 + D.x ^ C.cHH) ≤ (1 + H) * y :=
    (log_one_add_rpow_le hx hHH hX.1 hy).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hH]) (zero_le_one.trans hy))
  have hlk0 := Real.log_nonneg hk1
  have hlH0 := Real.log_nonneg (show 1 ≤ 1 + D.x ^ C.cHH by
    linarith only [Real.rpow_nonneg hx0.le C.cHH])
  obtain ⟨hd0, hd⟩ := inv_one_sub_le_two hDel
  have h2 : D.x ^ (2 * D.ε) = y ^ 2 := by
    rw [mul_comm, Real.rpow_mul hx0.le, Real.rpow_ofNat]
  have hpow : D.x ^ (C.eDiv * D.ε) ≤ y ^ 2 :=
    h2 ▸ Real.rpow_le_rpow_of_exponent_le hx (mul_le_mul_of_nonneg_right hDiv he.le)
  have hzero : D.x ^ (C.eLoss * D.ε) = 1 := by simp [le_antisymm hLoss hLs]

  -- The same polynomial as ErrX5at, displaying just its varying factors.
  let P (l la div loss logW logk logH tail : ℝ) :=
    let lo := C.cLoss * D.nT * (m : ℝ) * D.b * loss
    let low := C.cSl1 * lo + C.cSl1 * D.nT * m * (D.a / D.k + D.b') * (C.cCount * m * l) + C.cSl1 * Xpp + 1
    let variation := 2 * (m : ℝ) * C.cE * D.B0 + C.cH * (D.nT * D.a * la + m * D.B0) + D.sumA * (C.cCount * logk)
    let upper := C.cSlope * D.nT * D.a * la * (2 + m / D.k) + variation + C.cSl1 * m * D.B0 + low
    D.sumA * (C.cCount * (la + (m : ℝ) ^ 2 * la / D.k)) +
      (C.cDiv * D.nT * D.a * la + C.cDiv * m * (D.B0 + D.Nc) * div) + m * C.cE * D.B0 +
      C.cSlope * D.nT * D.a * la * (1 + m / D.k) + logW + lo + low +
      (1 - D.delBar)⁻¹ * (4 * logH * (upper + D.b) + tail)
  let Q := P 2 2 1 1 D.a (1 + eK) (1 + H) (K * (D.nT * D.a))
  have hconstant : Q ≤ S ^ 3 * ErrText D := by
    have h := core_ineq (nT := D.nT) (a := D.a) (b := D.b) (b' := D.b') (k := D.k)
      (L := 2) (La := 2) (B0 := D.B0) (Nc := D.Nc) (M := (m : ℝ)) (sA := D.sumA)
      (lW := D.a) (lk := 1 + eK) (lH := 1 + H) (dI := (1 - D.delBar)⁻¹)
      (et := K * (D.nT * D.a)) (Xpp := Xpp) (y := S) (yD := 1) (yL := 1)
      (K := K) (h := 1 + H) (g := 1 + eK)
      hS le_rfl le_rfl hnT ha1 hb0 hba hM hk hMk hMb (by norm_num) (by linarith only [hS])
      (by norm_num) (by linarith only [hS]) hb' hkb' hXp0 hXp hs0 hs hB0 hNc le_rfl
      (by positivity) (le_mul_of_one_le_right (by positivity) hS)
      (by positivity) (le_mul_of_one_le_right (by positivity) hS) hd0 hd
      (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK hS) (mul_nonneg hn0 ha0))
      c1 c1' c2 c2' c3 c3' c4 c4' c5 c5' c6 c6' c7 c7' (by linarith) (by linarith)
      (le_max_right 1 (KBig K H eK))
    simpa only [Q, P, ErrText, one_mul, pow_succ, pow_zero] using h
  have major : ErrX5at D C Xpp u ≤
      P (2*y) (2*y) (y^2) 1 D.a ((1+eK)*y) ((1+H)*y) (K*y*(D.nT*D.a)) := by
    unfold ErrX5at UBar5 MLo5 Data.Vvar Data.LoP
    dsimp [P]
    rw [hzero]
    gcongr
  have scaled : P (2*y) (2*y) (y^2) 1 D.a ((1+eK)*y) ((1+H)*y) (K*y*(D.nT*D.a))
      ≤ y^2 * Q := by
    obtain ⟨z, hz, hz'⟩ : ∃ z : ℝ, 0 ≤ z ∧ y = 1 + z :=
      ⟨y-1, by linarith only [hy], by ring⟩
    dsimp only [Q, P]
    rw [hz']
    apply le_of_sub_nonneg
    ring_nf
    positivity
  calc _ ≤ y^2 * (S^3 * ErrText D) :=
        (major.trans scaled).trans (mul_le_mul_of_nonneg_left hconstant (sq_nonneg _))
       _ = _ := by rw [h2]; unfold quadraticConstant; dsimp only [S]; ring

theorem quadraticErrorBound (eps x K H eK : ℝ) :
    ErrorBoundAt eps x K H eK (quadraticConstant K H eK * x ^ (2*eps)) := by
  intro U _ W _ _ Top _ m f D C Xpp hxx he hD hL hH hW hX
  subst hxx he
  refine ⟨mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
    (Real.rpow_nonneg (zero_le_one.trans hW.1.1) _), fun u => ?_⟩
  exact errX5at_quadratic D C Xpp eK K H hW hX hD hL hH u

theorem quadraticFactor_eventually (K H eK : ℝ) {eps δ : ℝ} (he : 0 < eps) (hδ : 0 < δ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, quadraticConstant K H eK * x ^ (2*eps) ≤ x ^ ((2+δ)*eps) := by
  obtain ⟨x₀, h₀⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (mul_pos hδ he)).eventually_ge_atTop (quadraticConstant K H eK))
  refine ⟨max 1 x₀, fun x hx => ?_⟩
  have hx0 := zero_lt_one.trans_le ((le_max_left _ _).trans hx)
  rw [show (2+δ)*eps = δ*eps + 2*eps by ring, Real.rpow_add hx0]
  exact mul_le_mul_of_nonneg_right (h₀ x ((le_max_right _ _).trans hx)) (Real.rpow_nonneg hx0.le _)

end Levent151
