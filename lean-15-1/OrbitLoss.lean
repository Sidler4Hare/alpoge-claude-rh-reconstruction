import Formalism.LocalToGlobal.GlobalTheory.LossRequirementsOfSmallShares

noncomputable section

namespace Levent151

open Formalism.BasicNotions Formalism.MainNotions
  Formalism.L2.GlobalTheoryTheory.Loss
  Formalism.LFunctionChainParameters.SmallOrderPrimeLosses

/-- On a single arithmetic record, keep the full ninth power in the small-share bound. -/
theorem orbitLoss_at {D : D7} {L : SizeData₂ D} {X : G.Inst D L}
    {K : G.Consts} {Cr C bo : ℝ} (hP : PtH X K Cr)
    (hG : LinkG_at X K C bo) (hW : ChW_at X K) :
    Lnk.IOsum L ≤ (D.host.TT.card : ℝ) * D.R.m * L.sc.b * L.sc.x ^ (-8 : ℝ) := by
  classical
  have hsum : lhsW (sAt L K) (L.sc.x ^ (-L.sc.eps))
      (fun p => G.Sig X K (G.aL L) (G.bL L) p) ≤ L.sc.x ^ (-9 : ℝ) := hW
  have hraw := io_discriminant_bound (sAt L K) (fun p => G.Sig X K (G.aL L) (G.bL L) p)
    (fun p => G.ioP X K (G.aL L) (G.bL L) p) (L.sc.x ^ (-L.sc.eps))
    (D.R.m : ℝ) (D.host.TT.card : ℝ) L.sc.a (L.sc.x ^ (-9 : ℝ))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Lnk.sc_a_pos _).le hsum
    (fun p _ => Lnk.ioP_le X K p (hG.2.1 p) (Lnk.Sig_nonneg X K hP.Knn hP.kapI _ _ p))
  rw [IO_at X K Cr hP] at hraw
  refine hraw.trans_eq ?_
  have hx : 0 < L.sc.x := zero_lt_one.trans L.sc.one_lt_alt
  have hab : L.sc.a = L.sc.x * L.sc.b := rfl
  have hpow : L.sc.x * L.sc.x ^ (-9 : ℝ) = L.sc.x ^ (-8 : ℝ) := by
    calc
      _ = L.sc.x ^ (1 : ℝ) * L.sc.x ^ (-9 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hx]; norm_num
  rw [hab, ← hpow]
  ring

/-- The already chosen weights work simultaneously on all indices of the same family. -/
theorem orbitLoss_of_chosenWall {eps : ℝ} (Fm : FamP eps)
    (hG : LinkG Fm) (hW : ChosenWall Fm) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ i : Fm.Ix x,
      Lnk.IOsum (Fm.L x i) ≤
        ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b * x ^ (-8 : ℝ) := by
  obtain ⟨C, xG, δ, _, hG⟩ := hG
  obtain ⟨xW, hW⟩ := hW
  refine ⟨max (max (Fm.x1 + 1) 3) (max xG xW), fun x hx i => ?_⟩
  have hstart := (le_max_left _ _).trans hx
  have hinputs := (le_max_right _ _).trans hx
  have hlate : Fm.x1 < x :=
    (lt_add_one Fm.x1).trans_le ((le_max_left _ _).trans hstart)
  have h := orbitLoss_at (ptH Fm hlate ((le_max_right _ _).trans hstart) i)
    (hG x ((le_max_left _ _).trans hinputs) i) (hW x ((le_max_right _ _).trans hinputs) i)
  rwa [Fm.L_x x i hlate] at h

end Levent151
