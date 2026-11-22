import Formalism.LocalToGlobal.GlobalTheory.LossRequirementsOfSmallShares
import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants
import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums

noncomputable section

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions
  Formalism.L2.GlobalTheoryTheory.Loss
  Formalism.LFunctionChainParameters.SmallOrderPrimeLosses

namespace Levent151

/-- The orbit-loss estimate at an actual point uses the numerical parameter
choice for the orbit mass and the weight inequality at this same point. -/
theorem selectedOrbitLossAt {eps : ℝ} (Fm : FamP eps) {x : ℝ} (hx : Fm.x1 < x)
    (h3 : 3 ≤ x) (i : Fm.Ix x) (hW : ChW_at (Fm.Gx x i) Fm.GK) :
    Lnk.IOsum (Fm.L x i) ≤
      ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b * x ^ (-8 : ℝ) := by
  classical
  let D := Fm.D x i
  let L := Fm.L x i
  let X := Fm.Gx x i
  let K := Fm.GK
  have H := ptH Fm hx h3 i
  have hS := G.svBound_of X K Fm.GK_nonneg (Fm.params x hx i)
  have hsum : lhsW (sAt L K) (L.sc.x ^ (-L.sc.eps))
      (fun p => G.Sig X K (G.aL L) (G.bL L) p) ≤ L.sc.x ^ (-9 : ℝ) := hW
  have hraw := io_discriminant_bound (sAt L K) (fun p => G.Sig X K (G.aL L) (G.bL L) p)
    (fun p => G.ioP X K (G.aL L) (G.bL L) p) (L.sc.x ^ (-L.sc.eps))
    (D.R.m : ℝ) (D.host.TT.card : ℝ) L.sc.a (L.sc.x ^ (-9 : ℝ))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Lnk.sc_a_pos _).le hsum
    (fun p _ => Lnk.ioP_le X K p (hS p) (Lnk.Sig_nonneg X K H.Knn H.kapI _ _ p))
  rw [IO_at X K Fm.Cr H] at hraw
  refine hraw.trans_eq ?_
  have hpos : 0 < L.sc.x := zero_lt_one.trans L.sc.one_lt_alt
  have hab : L.sc.a = L.sc.x * L.sc.b := rfl
  have heq : L.sc.x = x := Fm.L_x x i hx
  have hpow : L.sc.x * L.sc.x ^ (-9 : ℝ) = L.sc.x ^ (-8 : ℝ) := by
    calc
      _ = L.sc.x ^ (1 : ℝ) * L.sc.x ^ (-9 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hpos]; norm_num
  change _ = (D.host.TT.card : ℝ) * D.R.m * L.sc.b * x ^ (-8 : ℝ)
  have htarget : x ^ (-8 : ℝ) = L.sc.x * L.sc.x ^ (-9 : ℝ) :=
    (congrArg (fun z : ℝ => z ^ (-8 : ℝ)) heq).symm.trans hpow.symm
  rw [hab, htarget]
  ring

open G AuxBlock8 AuxBlock8.Pf

private theorem actualThresholdPositive {eps : ℝ} (Fm : FamP eps) {x : ℝ}
    (hx : Fm.x1 < x) (i : Fm.Ix x) : 0 < Fm.GK.La := by
  by_contra! hn
  have hz : Fm.GK.La = 0 := le_antisymm hn Fm.GK_nonneg.1
  obtain ⟨w⟩ := G.exists_place (Fm.D x i)
  obtain ⟨_, _, _, _, _, _, he⟩ := Fm.fills x hx i w
  rw [G.La, hz, zero_mul, zero_mul] at he
  have h := (Fm.sizes x hx i).2.2.2.2.2.2.2.2.1.1
  exact (Real.rpow_pos_of_pos (one_pos.trans (Fm.L x i).sc.one_lt_alt) _).not_ge (h.trans he.ge)

/-- The prime-by-prime served deficit inequality with the actual asks `askP`
holds for all in-window vectors on every original family. -/
theorem actualPrimeGain {eps : ℝ} (Fm : FamP eps) :
    ∃ C : ℝ, 3 ≤ C ∧ Ev Fm fun x i => GainBoundAllUniform (Fm.Gx x i) Fm.GK C
      ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) := by
  by_cases hLa : 0 < Fm.GK.La
  swap
  · exact ⟨3, le_rfl, Fm.x1 + 1, fun x hx i =>
      (hLa (actualThresholdPositive Fm ((lt_add_one Fm.x1).trans_le hx) i)).elim⟩
  have heps := Lnk.fam_eps_pos Fm
  obtain ⟨C31, hC31, x₁, h₁⟩ := family_first_lemma Fm
  obtain ⟨x₅, h₅⟩ := family_sizes_bound Fm hLa (eps / 48) (by linarith)
  obtain ⟨x₃, h₃⟩ := Filter.eventually_atTop.1
    ((St.numStar_ev eps Fm.GK Fm.GK_nonneg C31 hC31).and
      (St.B.facts_ev eps Fm.GK Fm.GK_nonneg C31 hC31))
  let Ce := Fm.cX.Ce
  have hCe : 0 ≤ Ce := by change 0 ≤ Fm.cX.Ce; rw [Fm.fixed.2.2.2.1]; norm_num
  let C := max (St.CStar eps Fm.GK C31)
    (max 3 (max (2 * Fm.GK.dl1 + (Ce + 1)) (4 * Fm.GK.dl2)))
  have hC₀ : St.CStar eps Fm.GK C31 ≤ C := le_max_left _ _
  have hC₃ : 3 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCd₁ : 2 * Fm.GK.dl1 + (Ce + 1) ≤ C :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCd₂ : 4 * Fm.GK.dl2 ≤ C :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨C, hC₃, max (max x₁ x₅) (max x₃ (Fm.x1 + 1)), fun x hx i => ?_⟩
  obtain ⟨hleft, hright⟩ := max_le_iff.mp hx
  obtain ⟨hx₁, hx₅⟩ := max_le_iff.mp hleft
  obtain ⟨hx₃, hxstart⟩ := max_le_iff.mp hright
  have hlate : Fm.x1 < x := by linarith
  have P := Fm.params x hlate i
  have S := Fm.sizes x hlate i
  have hxeq := Fm.L_x x i hlate
  have heq := Fm.L_eps x i
  have hF := (h₃ x hx₃).2 (Fm.D x i) (Fm.L x i) hxeq heq S P (h₅ x hx₅ i)
  have hN := (h₃ x hx₃).1 (Fm.D x i) (Fm.L x i) hxeq heq S P _
    ⟨hF.hkQ, hF.hDII, hF.hbo⟩ C hC₀
  have hStar := St.starAll_of (Fm.Gx x i) Fm.GK_nonneg P (h₁ x hx₁ i) hC31 hN
  have hXa : (Fm.L x i).sc.X'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.a := by
    obtain ⟨_, _, _, hw500, _⟩ := basics P
    unfold Scale.X''
    exact div_le_self (le_trans zero_le_one (Pf.sc_one_lt_a _).le) (by linarith)
  have hconst : GainBoundConstants Fm.GK (Ce + 1) C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) :=
    ⟨hC₃, hCd₁, hCd₂, bo_nonneg _ _⟩
  intro a b hab
  exact gain_bound_at_of_star P (Fm.Gx x i) Fm.GK Fm.GK_nonneg (Ce + 1) C _
    (by linarith) hconst
    (fun p hp hpX => (Fm.ex x hlate i).ep_def.le p hCe
      (Joints.fk_logb_ge_one _ _ p hp (hpX.trans hXa)))
    a b hab (fun p hc t ht j hj => hStar a b hab p hc t ht j hj)

open Formalism.LFunctionChainParameters.DeficitSplitLemmas
  Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
  Formalism.L2.GlobalTheoryTheory.Loss7

section AtRecord

variable {D : D7} {L : Formalism.BasicNotions.SizeData₂ D} {X : Inst D L}
  {K : G.Consts} {Cr C bo : ℝ}

/-- Convert the served-prime inequality on the computed functions into the
finite ledger used by the discriminant estimate. -/
private theorem servedLedger (H : PtH X K Cr) (hGain : GainBoundAllUniform X K C bo)
    {p : ℕ} (hP : p ∈ PsAt L) (hs : clAt X K p = PClass.served) :
    Formalism.LFunctionChainParameters.DeficitSplitLemmas.SizeData₂ (SizeData₂.lifts D) (TTv D)
      (ldAt X K (4 * |C| + 1) bo).TTp
      (fun j t q => askAt ((ldAt X K (4 * |C| + 1) bo).Iex j t q)
        ((ldAt X K (4 * |C| + 1) bo).at_ t) q ((ldAt X K (4 * |C| + 1) bo).wz j t q))
      (ldAt X K (4 * |C| + 1) bo).gain (ldAt X K (4 * |C| + 1) bo).tau
      (ldAt X K (4 * |C| + 1) bo).lo (ldAt X K (4 * |C| + 1) bo).fl p := by
  classical
  obtain ⟨hp, hin⟩ := mem_PsAt hP
  have hcut := served_le X K Cr H (T_not_inert D) p hP hs
  obtain ⟨w, hw⟩ := Lnk.place_over D p hp
  obtain ⟨_, hwpart, hT, _, _, _, hLa⟩ := H.fills w
  rw [hw] at hwpart hT
  have hlo := lo_le_loG K L H.Knn.1 hLa C bo p hp
  have hfl := fl_le_flG L C p hp
  have hnd := (pc_served_iff X K p).1 hs
  have hG := (hGain (aL L) (bL L) (inWin_sizeData L) p hp hin.symm hcut).2
  constructor
  · intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_image_of_mem
    rw [← hT, Finset.mem_map] at ht
    obtain ⟨s, _, rfl⟩ := ht
    exact s.2
  · have hsum : ∀ j ∈ SizeData₂.lifts D,
        ∑ t ∈ (ldAt X K (4 * |C| + 1) bo).TTp p,
          (askAt ((ldAt X K (4 * |C| + 1) bo).Iex j t p)
            ((ldAt X K (4 * |C| + 1) bo).at_ t) p ((ldAt X K (4 * |C| + 1) bo).wz j t p)
            - (ldAt X K (4 * |C| + 1) bo).lo p) ≤
        ∑ t ∈ TTP X K (aL L) (bL L) p, (askP X (aL L) (bL L) p j t - lo K L C bo p) := by
      intro j hj
      change ∑ t ∈ (TTP X K (aL L) (bL L) p).image Formalism.HC.Frame.A.val, _ ≤ _
      rw [Finset.sum_image (fun a _ b _ hab => Formalism.HC.Frame.A.val_injective _ hab)]
      apply Finset.sum_le_sum
      intro t ht
      have htop : t ∈ D.host.TT := by
        rw [← hT, Finset.mem_map] at ht
        obtain ⟨s, _, rfl⟩ := ht
        exact s.2
      let v : D.host.TT := ⟨t, htop⟩
      have he := (ask_at X K Cr (4 * |C| + 1) bo H j hj v p hp hin).trans
        (ask_eq_askP X p hp hwpart j v)
      exact sub_le_sub he.le hlo
    have htotal := Finset.sum_le_sum hsum
    have hfloor := mul_le_mul_of_nonneg_left hfl (Nat.cast_nonneg D.R.m : (0 : ℝ) ≤ _)
    have hG' := (sub_le_sub htotal hfloor).trans hG
    simpa only [ldAt, gainQ, if_neg hnd, Formalism.L2.GlobalTheoryTheory.Loss7.card_lifts] using hG'

private theorem selectedLossSetting (H : PtH X K Cr) (P : Par)
    (hGain : GainBoundAllUniform X K C bo) (hSv : SvBound X K)
    (tie : ParTie P L K (4 * |C| + 1) bo Cr) (hbo : 0 ≤ bo)
    (hLa : 0 ≤ L.LaG) (hp0 : L.sc.p0 D.R.k ≤ L.sc.X') (hTT : D.host.TT.Nonempty)
    (hB : ChBadp_at X) (hW : ChW_at X K) :
    PrimeClassLossHypotheses P (PsAt L) (sAt L K) (largeOrderResiduePrimes L) (SizeData₂.lifts D)
      (TTv D) (badAt X) (fun p => Sig X K (aL L) (bL L) p)
      (fun (_ : Unit) p => ioP X K (aL L) (bL L) p) (fun _ => ldAt X K (4 * |C| + 1) bo) := by
  let C' := 4 * |C| + 1
  obtain ⟨s1, s2, s3, s4, s5, s6, eX, ea, _, eθ⟩ := side_at X K Cr C' bo H P tie hbo hLa hp0
  have hSig p := Lnk.Sig_nonneg X K H.Knn H.kapI (aL L) (bL L) p
  refine ⟨hTT.image _, fun p hp => ?_, fun p _ => hSig p, ?_, ?_, ?_, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨h₁, h₂⟩ := mem_PsAt hp
    exact ⟨h₁, fun h => two_not_inert _ (h ▸ h₂)⟩
  · unfold lhsW
    rw [eθ, tie.x, ← cands_eq]
    have hx : 0 < L.sc.x := one_pos.trans L.sc.one_lt_alt
    have h₉ : L.sc.x ^ (-9 : ℝ) = (L.sc.x ^ 9)⁻¹ := by
      rw [Real.rpow_neg hx.le]; congr 1; exact_mod_cast Real.rpow_natCast L.sc.x 9
    rwa [← h₉]
  · unfold ChBadp_at at hB
    unfold badPrimeLogWeightedCount
    rw [card_TTv, tie.x, tie.ε]
    simp only [bad_card_at]
    exact hB
  · intro _ p _
    rw [Formalism.L2.GlobalTheoryTheory.Loss7.card_lifts, card_TTv, ea]
    exact Lnk.ioP_le X K p (hSv p) (hSig p)
  · refine ⟨unitRule_at X K C' bo, s1, s2, s3, ?_, ?_, fun _ hp hs => servedLedger H hGain hp hs,
      ?_, fun p hp _ => s4 p hp, fun p hp _ => s5 p hp, s6⟩
    · intro p hp h; rw [eX]; exact served_le X K Cr H (T_not_inert D) p hp h
    · intro p _ h; rw [eX]; exact high_gt X K p h
    · intro p hp h
      obtain ⟨a₁, a₂⟩ := nonserved_zero X K Cr H (T_not_inert D) p hp h
      exact ⟨fun j _ => a₁ j, a₂⟩
  · exact firstHyp_at X K Cr C' bo H (T_not_inert D) P tie
  · intro p _ h
    obtain ⟨h₁, h₂⟩ := second_spec X K p h
    rw [eθ]; exact ⟨(mem_sAt K).mpr h₁, h₂⟩
  · intro p hp h n hn
    have hn' : n ∈ TTv D ∧ n ∉ (ldAt X K C' bo).TTp p := by simpa only [Finset.mem_sdiff] using hn
    exact unserved_bad X K Cr C' bo H (T_not_inert D) p hp h n (Finset.mem_sdiff.mpr hn')

end AtRecord

/-- Every selected point of the original family has bounded total signed
prime deficit. Constants are uniform in the scale, the selected index, and
the tied ask representation. -/
theorem selectedPrimeLosses {eps : ℝ} (Fm : FamP eps) :
    ∃ c x₀ : ℝ, 0 ≤ c ∧ ∀ x ≥ x₀, ∀ i : Fm.Ix x, (Fm.D x i).host.TT.Nonempty →
      ChBadp_at (Fm.Gx x i) → ChW_at (Fm.Gx x i) Fm.GK → Lnk.Loss_at (Fm.L x i) c 0 := by
  classical
  obtain ⟨cg, _, xG, hg⟩ := actualPrimeGain Fm
  let C := 4 * |cg| + 1
  let δ := fun x : ℝ => x ^ (-(eps / 2))
  have heps := Lnk.fam_eps_pos Fm
  have hδ : Filter.Tendsto δ Filter.atTop (nhds 0) := tendsto_rpow_neg_atTop (half_pos heps)
  obtain ⟨cord, hcord, hj⟩ := joint_discriminant_eventually
  obtain ⟨xA, ha⟩ := Lnk.askIsF Fm
  obtain ⟨e, K, x₀, hw⟩ := windows_ev Fm C 0 cord hcord δ hδ
  have heps₄ : eps < 1 / 4 := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have h := (Fm.L 0 i).sc.eps_lt
    rw [Fm.L_eps] at h
    linarith
  obtain ⟨x₁, hj⟩ := hj eps e K heps heps₄
  refine ⟨3 * |K| + 13, max x₀ (max xG (max xA x₁)), by positivity,
    fun x hx i hne hbad hW => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨h₀, hG, hA, h₁⟩ := hx
  obtain ⟨hlate, h3, hn⟩ := hw x h₀
  obtain ⟨hn, hp₀⟩ := hn i
  let L := Fm.L x i
  let D := Fm.D x i
  let bo := L.sc.b ^ δ x
  let P : Par := par Fm x i C bo 0 cord
  have tie : ParTie P L Fm.GK C bo Fm.Cr := parTie (i0 := i) hlate i C bo 0 cord
  have H := ptH Fm hlate h3 i
  have hLaG : 0 ≤ L.LaG := (Real.rpow_nonneg (one_pos.trans L.sc.one_lt_alt).le _).trans
    (Fm.sizes x hlate i).2.2.2.2.2.2.2.2.1.1
  have hS := selectedLossSetting H P (hg x hG i) (svBound_of _ _ Fm.GK_nonneg (Fm.params x hlate i))
    tie (Real.rpow_nonneg (Real.exp_pos _).le _) hLaG hp₀ hne hbad hW
  have hxP : P.x = x := Fm.L_x x i hlate
  obtain ⟨hdef, hio⟩ := hj P (Fm.L_eps x i) rfl (hxP.symm ▸ h₁) (discriminant_windows_of P e K hn)
    ℕ ℕ ℕ Unit _ _ _ _ _ _ _ _ _ hS
  have hU : unitU P (SizeData₂.lifts D).card (TTv D).card = (D.host.TT.card : ℝ) * D.R.m * L.sc.b := by
    unfold unitU; rw [Formalism.L2.GlobalTheoryTheory.Loss7.card_lifts, card_TTv, pd_b tie]
  have hnP : 0 ≤ P.C := le_max_right _ _
  have hPK : P.C ≤ K := hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hB₀ : 0 ≤ (D.host.TT.card : ℝ) * D.R.m * L.sc.b :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hconv : (3 * P.C + 13) * ((D.host.TT.card : ℝ) * D.R.m * L.sc.b) ≤
      (3 * |K| + 13) * D.host.TT.card * D.R.m * L.sc.b * L.sc.x ^ ((0 : ℝ) * L.sc.eps) := by
    rw [zero_mul, Real.rpow_zero, mul_one]
    have h := mul_le_mul_of_nonneg_right
      (show 3 * P.C + 13 ≤ 3 * |K| + 13 by linarith [le_abs_self K]) hB₀
    simpa [mul_assoc] using h
  constructor
  · have h := hio ()
    rw [IO_at _ _ _ H, hU] at h
    exact h.trans ((le_mul_of_one_le_left hB₀ (by linarith : 1 ≤ 3 * P.C + 13)).trans hconv)
  · intro e' m' AD N TT' a w hr hAD hcut
    rw [ha x hA i e' m' AD N TT' a w hr hAD hcut]
    have h := hdef ()
    rw [Ga_at _ _ _ C bo H, hU, tie.d, ASK_at _ _ _ C bo H] at h
    linarith

end Levent151
