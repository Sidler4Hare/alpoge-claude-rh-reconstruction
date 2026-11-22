import Formalism.LocalToGlobal.GlobalTheory.LossRequirementsOfSmallShares
import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.SlopeEstimateOfLemmaBSlopeLine

noncomputable section

namespace Levent151

open Formalism.BasicNotions Formalism.MainNotions
  Formalism.L2.GlobalTheoryTheory.Loss
  Formalism.LFunctionChainParameters.DeficitSplitLemmas
  Formalism.LFunctionChainParameters.SmallOrderPrimeLosses

open Classical in
/-- In the prime ledger these are the missing tops at an otherwise served prime. -/
def omittedTopCharge {D : D7} {L : SizeData₂ D} (X : G.Inst D L)
    (K : G.Consts) (C bo : ℝ) : ℝ := by
  letI : DecidableEq ℕ := fun a b => Classical.propDecidable (a = b)
  exact ∑ p ∈ (PsAt L).filter (fun p => clAt X K p = PClass.served),
    4 * (D.R.m : ℝ) * L.sc.a * (Real.log p / p) *
      (((TTv D) \ (ldAt X K C bo).TTp p).card : ℝ)

/-- A geometric record realizing a top set with every qualifying orbit good
has no omitted-top charge at its served primes. -/
theorem omittedTopCharge_eq_zero {D : D7} {L : SizeData₂ D} (X : G.Inst D L)
    (K : G.Consts) (C bo : ℝ) {Cr : ℝ} (hP : PtH X K Cr)
    (hgood : ∀ p ∈ largeOrderResiduePrimes L, ∀ t ∈ TTv D, ¬ badAt X p t) :
    omittedTopCharge X K C bo = 0 := by
  classical
  unfold omittedTopCharge
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hp0, hserved⟩ := Finset.mem_filter.mp hp
  apply mul_eq_zero.mpr
  right
  rw [Nat.cast_eq_zero, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hm : t ∈ TTv D ∧ t ∉ (ldAt X K C bo).TTp p := by
    simpa only [Finset.mem_sdiff] using ht
  obtain ⟨hlarge, hbad⟩ := unserved_bad X K Cr C bo hP (T_not_inert _)
    p hp0 hserved t (Finset.mem_sdiff.mpr hm)
  exact hgood p hlarge t hm.1 hbad

/-- At an actual record the top count and the bad-top count control the full
omitted-top charge. -/
theorem omittedTopCharge_at {D : D7} {L : SizeData₂ D} (X : G.Inst D L)
    (K : G.Consts) (C bo : ℝ) {Cr Cb : ℝ} (hP : PtH X K Cr)
    (hCb : 0 ≤ Cb) (hT : ChTT_at L) (hBad : ChBad_at X Cb) :
    omittedTopCharge X K C bo ≤
      64 * Cb * ((D.host.TT.card : ℝ) * D.R.m * L.sc.b) *
        L.sc.x ^ (-1 + L.sc.eps / 3) := by
  classical
  let S := largeOrderResiduePrimes L
  have hcnt : badPrimeLogWeightedCount S (TTv D) (badAt X) =
      ∑ p ∈ S, Real.log p / p * ((badTops X p).card : ℝ) := by
    unfold badPrimeLogWeightedCount
    simp only [Formalism.L2.GlobalTheoryTheory.Loss7.bad_card_at X]
  have hout := out_discriminant_bound ℕ (PsAt L) S (clAt X K) (TTv D)
    (ldAt X K C bo).TTp (badAt X) D.R.m L.sc.a _ (Nat.cast_nonneg _)
    (Lnk.sc_a_pos _).le hcnt.le (fun p hp hc t ht => by
      have hh : t ∈ TTv D ∧ t ∉ (ldAt X K C bo).TTp p := by
        simpa only [Finset.mem_sdiff] using ht
      exact unserved_bad X K Cr C bo hP (T_not_inert _) p hp hc t (Finset.mem_sdiff.mpr hh))
  have hw : 4 * L.sc.a * D.R.m * (∑ p ∈ S, Real.log p / p * ((badTops X p).card : ℝ)) =
      ∑ p ∈ S, 4 * (D.R.m : ℝ) * L.sc.a * (Real.log p / p) * ((badTops X p).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hw] at hout
  have hraw := hout.trans (Lnk.tops_clause X Cb D.R.m hCb (Nat.cast_nonneg _) hT hBad)
  have hx : 0 < L.sc.x := zero_lt_one.trans L.sc.one_lt_alt
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hm := Formalism.L2.GlobalTheoryTheory.Places.mertens L.sc.X' hX
  have hpr : ∑ p ∈ S, Real.log p / p ≤ 2 * L.sc.x ^ (L.sc.eps/3) := by
    calc _ ≤ ∑ p ∈ (Finset.range ⌈L.sc.X'⌉₊).filter Nat.Prime, Real.log p / p := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p hp
              obtain ⟨hp1,hp2,_⟩ := Finset.mem_filter.mp hp
              exact Finset.mem_filter.mpr ⟨hp1,hp2⟩
            · intro p _ _
              exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
         _ ≤ 2 * Real.log L.sc.X' := hm
         _ = _ := by unfold Scale.X'; rw [Real.log_exp]
  have hcoef : 0 ≤ 32 * (Cb * L.sc.x ^ (-2 : ℝ)) * (D.R.m : ℝ) * L.sc.a * D.host.TT.card := by
    have := (Lnk.sc_a_pos L.sc).le
    positivity
  have hxpow : L.sc.x ^ (-2 : ℝ) * L.sc.x * L.sc.x ^ (L.sc.eps / 3) =
      L.sc.x ^ (-1 + L.sc.eps / 3) := by
    calc _ = L.sc.x ^ (-2 : ℝ) * L.sc.x ^ (1 : ℝ) * L.sc.x ^ (L.sc.eps/3) := by rw [Real.rpow_one]
         _ = _ := by rw [← Real.rpow_add hx, ← Real.rpow_add hx]; congr 1; ring
  have hrw : 32 * (Cb * L.sc.x ^ (-2 : ℝ)) * (D.R.m : ℝ) * L.sc.a * D.host.TT.card *
        (2 * L.sc.x ^ (L.sc.eps/3)) =
      64 * Cb * ((D.host.TT.card : ℝ) * D.R.m * L.sc.b) * L.sc.x ^ (-1 + L.sc.eps/3) := by
    rw [← hxpow]
    change _ * (L.sc.x * L.sc.b) * _ * _ = _
    ring
  have hh := hraw.trans ((mul_le_mul_of_nonneg_left hpr hcoef).trans_eq hrw)
  simpa only [omittedTopCharge] using hh

/-- The threshold and the chosen set work simultaneously for all actual points.
This conclusion only uses properties already carried by ChosenE and the family. -/
theorem omittedTopCharge_of_chosen {eps C0 CH : ℝ} (Fm : FamP eps) (hc : ChosenE Fm C0 CH) :
    ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀, ∀ i : Fm.Ix x, ∀ C bo : ℝ,
      omittedTopCharge (Fm.Gx x i) Fm.GK C bo ≤
        64 * Cb * (((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b) *
          x ^ (-1 + eps / 3) := by
  obtain ⟨_, _, Cb, _, _, hCb, _, ⟨xT, hT⟩, ⟨xB, hB⟩, _⟩ := hc
  refine ⟨Cb, max (max (Fm.x1 + 1) 3) (max xT xB), hCb, fun x hx i C bo => ?_⟩
  have hs := (le_max_left _ _).trans hx
  have hi := (le_max_right _ _).trans hx
  have hf : Fm.x1 < x := (lt_add_one Fm.x1).trans_le ((le_max_left _ _).trans hs)
  have h := omittedTopCharge_at (Fm.Gx x i) Fm.GK C bo
    (ptH Fm hf ((le_max_right _ _).trans hs) i) hCb.le
    (hT x ((le_max_left _ _).trans hi) i) (hB x ((le_max_right _ _).trans hi) i)
  rwa [Fm.L_x x i hf, Fm.L_eps x i] at h

/-- Below the local cutoff the share is independent of the two weights. The
good representative fibres are disjoint, so that each top is charged at most once. -/
theorem smallPrimeShare_le {D : D7} {L : SizeData₂ D} (X : G.Inst D L)
    (K : G.Consts) (hK : K.Nonneg) (a b : G.HH D → ℤ) (p : ℕ)
    (hres : G.IsResidueClassZero D p) (hp : (p : ℝ) < L.sc.p0 D.R.k) :
    G.Sig X K a b p ≤ (D.R.m : ℝ) * ((D.host.TT.card : ℝ) *
      (K.kII * (G.rG L.sc : ℝ)^2 * D.R.k * L.sc.x ^ (-Scale.A))) := by
  classical
  let c := K.kII * (G.rG L.sc : ℝ)^2 * D.R.k * L.sc.x ^ (-Scale.A)
  have hc : 0 ≤ c := by
    have : 0 ≤ K.kII := hK.2.2.1
    have : 0 < L.sc.x := zero_lt_one.trans L.sc.one_lt_alt
    dsimp [c]
    positivity
  unfold G.Sig
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc _ ≤ ∑ t ∈ G.goodReps X p, (G.Nv X p t : ℝ) * c := by
          refine Finset.sum_le_sum fun t ht => ?_
          unfold G.kapv G.kapLoc
          rw [if_pos hp, G.kapIIf, AuxBlock8.Pf.Nv_eq X p hres t (AuxBlock8.Pf.mem_goodReps ht).1]
          exact (min_le_right _ _).trans_eq (by dsimp [c]; ring)
       _ = ((∑ t ∈ G.goodReps X p, G.Nv X p t : ℕ) : ℝ) * c := by
          rw [Nat.cast_sum, Finset.sum_mul]
       _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast AuxBlock8.Pf.sum_Nv_le X p (G.goodReps X p)) hc

/-- Once the rank expression is below the share threshold, every prime
classified as second kind is at or above the local cutoff. -/
theorem secondPrime_ge_cutoff {D : D7} {L : SizeData₂ D} (X : G.Inst D L)
    (K : G.Consts) (hK : K.Nonneg) (p : ℕ) (hsecond : clAt X K p = PClass.second)
    (hsize : (D.R.m : ℝ) * ((D.host.TT.card : ℝ) *
      (K.kII * (G.rG L.sc : ℝ)^2 * D.R.k * L.sc.x ^ (-Scale.A))) ≤ L.sc.x ^ (-L.sc.eps)) :
    L.sc.p0 D.R.k ≤ (p : ℝ) := by
  by_contra! hp
  obtain ⟨hc, hsig⟩ := second_spec X K p hsecond
  exact (not_lt_of_ge ((smallPrimeShare_le X K hK _ _ p hc.2.2.1 hp).trans hsize)) hsig

end Levent151
