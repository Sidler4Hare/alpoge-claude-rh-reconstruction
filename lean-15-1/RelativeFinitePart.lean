import Formalism.LocalToGlobal.GlobalTheory.PlacesP

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IndexCalculation.DvIdxCalcMain

noncomputable section

namespace Levent151

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory
  Formalism.L2.GlobalTheoryTheory.Places Formalism.LFunctionChainParameters.UnitWeightPartition

/-- Integer valuation rounding for the fractional-ideal shift. -/
def finiteRoundingLoss {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) : ℝ :=
  ∑ w ∈ L.supp, 2 * SizeData₂.lwP w *
    (DV.ur D w (L.sg u w) - (⌊DV.ur D w (L.sg u w)⌋ : ℝ))

/-- Local index in excess of the normalization already deducted from the gain. -/
def finiteIndexExcess {D : D7} (L : SizeData₂ D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) : ℝ :=
  (L.lenMN u w : ℝ) / ((D.div.Nu u).rank : ℝ) - L.tau w

def levelArchLoss (D : D7) (u : D.what₂.Word) : ℝ :=
  (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2)

/-- Rounding has less than one unit of integer valuation at each place. -/
theorem finiteRoundingLoss_bounds {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) :
    0 ≤ finiteRoundingLoss L u ∧
    finiteRoundingLoss L u ≤
      ∑ w ∈ L.supp.filter (fun w =>
        DV.ur D w (L.sg u w) ≠ (⌊DV.ur D w (L.sg u w)⌋ : ℝ)), 2 * SizeData₂.lwP w := by
  classical
  unfold finiteRoundingLoss
  constructor
  · exact Finset.sum_nonneg fun w _ => mul_nonneg
      (mul_nonneg (by norm_num) (J.logWeight_nonneg w)) (sub_nonneg.mpr (Int.floor_le _))
  · rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun w _ => ?_
    by_cases he : DV.ur D w (L.sg u w) = (⌊DV.ur D w (L.sg u w)⌋ : ℝ)
    · have hz := sub_eq_zero.mpr he
      rw [if_neg (not_not_intro he), hz, mul_zero]
    rw [if_pos he]
    calc
      _ ≤ (2 * SizeData₂.lwP w) * 1 := mul_le_mul_of_nonneg_left
        (by linarith [Int.lt_floor_add_one (DV.ur D w (L.sg u w))])
        (mul_nonneg (by norm_num) (J.logWeight_nonneg w))
      _ = _ := mul_one _

/-- No local index remains at an unserved, non-level place when its normalization is zero. -/
theorem finiteIndexExcess_of_unserved {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hT : D.what₂.places.resChar w ≠ (D.mem u).A.T)
    (hdrop : D.what₂.places.resChar w ∈ L.drop ∨ ¬ DV.InertK D (D.what₂.places.resChar w))
    (htau : L.tau w = 0) : finiteIndexExcess L u w = 0 := by
  have hlen := LatCmp.lenMN_unserved hNu u w (hNu.2.1 u w hT hdrop)
  simp [finiteIndexExcess, hlen, htau]

/-- The actual fractional-ideal shift cancels the recorded exponents up to
integer rounding and the index of the descended lattice. -/
theorem relativeSlope_eq_localDefects {D : D7} {L : SizeData₂ D} {C : ℝ}
    (hN' : DV.NprimeDef D L) (hNu : DV.NuDef D L) (hc : Lnk.NuCommens D L)
    (h26 : LocalQuadraticParts.adm26 L C) (u : D.what₂.Word)
    (hr : 0 < (D.div.Nu u).rank)
    (hoff : ∀ w, w ∉ L.supp →
      DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) = 0 ∨ L.lenMN u w = 0) :
    (D.div.Nu u).mu - ((D.fm u).lat 0).mu + L.Ee u - L.Fo =
      L.Ga - levelArchLoss D u - finiteRoundingLoss L u -
        ∑ w ∈ L.supp, 2 * Lnk.lE w * finiteIndexExcess L u w := by
  classical
  have hAtT : Lnk.NuAtT D L := fun u' w hw => (h26 u').2.2.2.1 w hw
  have hmu := mu_eq hN' hNu hc u (Lnk.nu_le_mram hNu hAtT u) hr hoff
  have hArch : (LocalQuadraticParts.MuH D u).mu =
      ((D.fm u).lat 0).mu - levelArchLoss D u := (h26 u).2.1
  have hsg : Sg L.supp Lnk.lE (L.sg u) L.tau = L.Ga + L.Fo - L.Ee u := by
    rw [Lnk.Ga_eq L, Lnk.Fo_eq L, Lnk.Ee_eq' L u]
    exact weightedSlopeExcess_decomposition L.supp (SizeData₂.lifts D) Lnk.lE
      L.gainD L.F (L.E u) L.tau
  have hLedger :
      (∑ w ∈ L.supp, 2 * SizeData₂.lwP w * (⌊DV.ur D w (L.sg u w)⌋ : ℝ)) -
        (∑ w ∈ L.supp, 2 * SizeData₂.lwP w * ((L.lenMN u w : ℝ) * (D.what₂.places.ramIdx w : ℝ))) /
          ((D.div.Nu u).rank : ℝ) =
      Sg L.supp Lnk.lE (L.sg u) L.tau - finiteRoundingLoss L u -
        ∑ w ∈ L.supp, 2 * Lnk.lE w * finiteIndexExcess L u w := by
    unfold Sg finiteRoundingLoss
    rw [Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold Lnk.lE DV.ur finiteIndexExcess
    ring
  rw [hArch, add_sub_assoc, hLedger, hsg] at hmu
  linarith only [hmu]

/-- A local lower bound on the index gives the upper signed comparison
without the base lattice's maximum-slope variation. -/
theorem relativeSlope_le_gain_of_index_lower {D : D7} {L : SizeData₂ D} {C : ℝ}
    (hN' : DV.NprimeDef D L) (hNu : DV.NuDef D L) (hc : Lnk.NuCommens D L)
    (h26 : LocalQuadraticParts.adm26 L C) (u : D.what₂.Word)
    (hr : 0 < (D.div.Nu u).rank) (hT : (2 : ℝ) < (D.mem u).A.T)
    (hoff : ∀ w, w ∉ L.supp →
      DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) = 0 ∨ L.lenMN u w = 0)
    (hIndex : ∀ w ∈ L.supp, 0 ≤ finiteIndexExcess L u w) :
    (D.div.Nu u).mu - ((D.fm u).lat 0).mu + L.Ee u - L.Fo ≤ L.Ga := by
  rw [relativeSlope_eq_localDefects hN' hNu hc h26 u hr hoff]
  have hArch : 0 ≤ levelArchLoss D u := by
    unfold levelArchLoss
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))) (by linarith)
  have hRound := (finiteRoundingLoss_bounds L u).1
  have hSum := Finset.sum_nonneg fun w hw =>
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (lE_nonneg w)) (hIndex w hw)
  linarith

/-- The actual local containment and recorded length force a nonnegative index excess. -/
theorem finiteIndexExcess_nonneg {D : D7} {L : SizeData₂ D} {C : ℝ}
    (hN' : DV.NprimeDef D L) (hNu : DV.NuDef D L) (hc : Lnk.NuCommens D L)
    (h26 : LocalQuadraticParts.adm26 L C) (u : D.what₂.Word)
    (hr : 0 < (D.div.Nu u).rank)
    (hLoc : ∀ w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
      DV.LocLe (D.plEq w) ⌊DV.ur D w (L.tau w)⌋₊ (L.NuLat u) (DV.MramL D u))
    (htauN : ∀ w, ∃ n : ℕ, L.tau w = n)
    (htauT : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → L.tau w = 0)
    (w : D.what₂.places.Pl) : 0 ≤ finiteIndexExcess L u w := by
  classical
  unfold finiteIndexExcess
  have hAtT : Lnk.NuAtT D L := fun u' v hv => (h26 u').2.2.2.1 v hv
  have hle := Lnk.nu_le_mram hNu hAtT u
  have hFG := D.MramL_fg u
  have hSpan := (Lnk.mramSpan D u).trans (nuLat_span hc u).symm
  have hCalc := PI.Dv.IdxW.dvIdxCalc_main D.what₂.LL (D.div.Nu u).V
    (D.plEq w) (DV.MramL D u) (L.NuLat u) hFG (Submodule.FG.of_le hFG hle) hSpan
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hCalc.1
  have hj' : DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) = (j : ℕ∞) := hj.symm
  have hLen := hNu.2.2 u w j hj'
  have he : (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ) := by
    exact_mod_cast D.what₂.places.ramIdx_pos w
  by_cases hw : D.what₂.places.resChar w = (D.mem u).A.T
  · rw [htauT w hw, sub_zero]
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply nonneg_of_mul_nonneg_left _ he
    rw [← hLen]
    exact Nat.cast_nonneg _
  have hLower := hCalc.2.2.2.1 _ (hLoc w hw)
  unfold PI.Dv.idxAt at hLower
  rw [← hj, ENat.toNat_natCast, ← rk_nu hN' hc u] at hLower
  have hjLower : (⌊DV.ur D w (L.tau w)⌋₊ * (D.div.Nu u).rank : ℕ) ≤ j := by
    have h0 : (0 : ℤ) ≤ (PI.Dv.lenAt (D.plEq w) (L.NuLat u) (DV.MramL D u)).toNat := by positivity
    exact_mod_cast hLower.trans (sub_le_self _ h0)
  obtain ⟨n, hn⟩ := htauN w
  have hFloor : ⌊DV.ur D w (L.tau w)⌋₊ = D.what₂.places.ramIdx w * n := by
    unfold DV.ur
    rw [hn, ← Nat.cast_mul, Nat.floor_natCast]
  rw [hFloor] at hjLower
  have hjR : (D.what₂.places.ramIdx w : ℝ) * n * (D.div.Nu u).rank ≤ (j : ℝ) := by
    exact_mod_cast hjLower
  have hrR : (0 : ℝ) < (D.div.Nu u).rank := by exact_mod_cast hr
  apply sub_nonneg.mpr
  rw [le_div_iff₀ hrR, hn]
  apply le_of_mul_le_mul_left _ he
  rw [← mul_assoc, mul_comm (D.what₂.places.ramIdx w : ℝ) (L.lenMN u w : ℝ), ← hLen]
  exact hjR

/-- The archimedean correction can be retained in the actual signed comparison. -/
theorem relativeSlope_add_levelArch_le_gain {D : D7} {L : SizeData₂ D} {C : ℝ}
    (hN' : DV.NprimeDef D L) (hNu : DV.NuDef D L) (hc : Lnk.NuCommens D L)
    (h26 : LocalQuadraticParts.adm26 L C) (u : D.what₂.Word)
    (hr : 0 < (D.div.Nu u).rank)
    (hoff : ∀ w, w ∉ L.supp →
      DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) = 0 ∨ L.lenMN u w = 0)
    (hLoc : ∀ w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
      DV.LocLe (D.plEq w) ⌊DV.ur D w (L.tau w)⌋₊ (L.NuLat u) (DV.MramL D u))
    (htauN : ∀ w, ∃ n : ℕ, L.tau w = n)
    (htauT : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → L.tau w = 0) :
    (D.div.Nu u).mu - ((D.fm u).lat 0).mu + L.Ee u - L.Fo + levelArchLoss D u ≤ L.Ga := by
  rw [relativeSlope_eq_localDefects hN' hNu hc h26 u hr hoff]
  have hRound := (finiteRoundingLoss_bounds L u).1
  have hSum := Finset.sum_nonneg (s := L.supp) fun w _ =>
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (lE_nonneg w))
      (finiteIndexExcess_nonneg hN' hNu hc h26 u hr hLoc htauN htauT w)
  linarith


end Levent151
