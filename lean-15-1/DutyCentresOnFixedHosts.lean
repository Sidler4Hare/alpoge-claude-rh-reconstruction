import ReselectedRealization
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProofStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightWindowRequirementHostOfPoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightRequirementOfValid
import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesSeven

noncomputable section

namespace Levent151

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
  GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc

/-- A fixed scale-indexed choice of the whole rank record and host, made before
the provisional kits. The common-duty conclusion retains those choices and
the originally supplied windows. -/
theorem dutyCentresOnFixedHosts :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ ∀ eps > 0, eps ≤ eps₀ → ∃ K : TransportedAlt,
      ∀ (κ : Par) (la x₀ : ℝ) (S : Scales la) (R : Scale → Ranks) (H : ∀ s, Host (R s))
        (Q : PtProp), eps < 1 / 52 → 1 ≤ la → 1 < x₀ → Std κ.C → κ.C.GK.Nonneg →
        κ.C.Large K κ.C.P.CF →
        (∀ s : Scale, s.eps = eps → x₀ ≤ s.x → S.Mem s →
          ∃ k : Kit κ.C κ.cD κ.ch s, RealizesHost κ Q s (H s) k) →
        ∃ x₁ : ℝ, ∀ s : Scale, s.eps = eps → x₁ ≤ s.x → S.Mem s →
          ∃ a b : (R s).A → ℤ, (∀ t, t ∉ (H s).TT → a t = 0 ∧ b t = 0) ∧
            WinOK s κ.C.GK (H s) a b ∧ WOK s κ.cD κ.ch κ.C.GK (H s) a b := by
  obtain ⟨eps₀, h₀, hw⟩ := GlobalTheory.T.windowShareRequirementClosedForm_proof
  refine ⟨eps₀, h₀, fun eps he hε => ?_⟩
  obtain ⟨K, hW⟩ := hw eps he hε
  refine ⟨K, fun κ la x₀ S R H Q h52 hla hx hstd hK hlarge supply => ?_⟩
  let duty (s : Scale) : Prop := ∃ a b : (R s).A → ℤ,
    (∀ t, t ∉ (H s).TT → a t = 0 ∧ b t = 0) ∧ WinOK s κ.C.GK (H s) a b ∧
      WOK s κ.cD κ.ch κ.C.GK (H s) a b
  let Q' : PtProp := fun D L _ X _ K _ _ _ => AuxBlock8.WeightVectorExists D L X K → duty L.sc
  choose k hk using supply
  have hnum : ∀ s h h' h'' i, Nonempty (NumAt κ.C ((k s h h' h'').pt i).L) := by
    intro s he hx hm i
    obtain ⟨_, _, _, _, _, _, hs, _⟩ := hk s he hx hm
    exact (hs i).2.2.2
  have hkit : ∀ s he hx hm i, ((k s he hx hm).pt i).Has Q' := by
    intro s he hx hm i hp
    let kₛ := k s he hx hm
    obtain ⟨a, b, M, c, _, _, hs, _⟩ := hk s he hx hm
    obtain ⟨⟨u, hfrom⟩, hcan, _, _⟩ := hs i
    obtain ⟨a', b', hoff, hwin, hw⟩ := weightWindowRequirement_host_of_point κ.C κ.cD κ.ch
      (kₛ.pt i) (R s) (H s) a b M c u hstd (kₛ.val i) hfrom hcan hp
    change duty (kₛ.pt i).L.sc
    rw [kₛ.sc_eq i] at hwin hw ⊢
    exact ⟨a', b', hoff, hwin, hw⟩
  obtain ⟨Fm, _, hpre, hout, hmid, hlast, _, hQ, _, hJ, hwin, _⟩ :=
    exists_famP_of_kits eps κ.C κ.cD κ.ch x₀ la S he h52 hx hla hstd hK k hnum
  have hL : Fm.Large K κ.C.P.CF := by
    unfold FamP.Large
    rw [hpre, hout, hmid, hlast]
    exact hlarge
  obtain ⟨xw, hw⟩ := hW Fm κ.C.P.CF trivial hL
  refine ⟨max (Fm.x1 + 1) xw, fun s hs h₁ hm => ?_⟩
  obtain ⟨ha, hb⟩ := max_le_iff.mp h₁
  have hlate : Fm.x1 < s.x := (lt_add_one Fm.x1).trans_le ha
  obtain ⟨i⟩ := Fm.Ix_win s.x (by rw [hwin]; exact hm.2)
  have hd : duty (Fm.L s.x i).sc := hQ Q' hkit s.x hlate i (hw s.x hb i)
  have hscale : (Fm.L s.x i).sc = s := by
    have h1 := Fm.L_x s.x i hlate
    have h2 := (Fm.L_eps s.x i).trans hs.symm
    have h3 := (Fm.L_J s.x i).trans (hJ.trans hm.1.symm)
    apply (show ∀ z z' : Scale, z.x = z'.x → z.eps = z'.eps → z.J = z'.J → z = z' from
      fun z z' => by cases z; cases z'; simp_all) <;> assumption
  rwa [hscale] at hd

/-- Rebuild the kit after choosing the duty weights.  Every translate in this
single kit satisfies the actual small-share predicate. -/
theorem dutyKitOnChosenHost (C : FC) (cD ch : ℝ) (s : Scale) (R : Ranks)
    (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (Q : PtProp)
    (hstd : Std C) (hoff : ∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0)
    (hw : WOK s cD ch C.GK H a b)
    (points : ∀ u < R.n, ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧
      p.From H a b c u ∧ CanonInst p.ta.Gx ∧ p.Has Q) :
    ∃ k : Kit C cD ch s, (∀ i, (k.pt i).Has Q ∧ ChW_at (k.pt i).ta.Gx C.GK) ∧
      ∀ u < R.n, ∃ i, (k.pt i).From H a b c u := by
  obtain ⟨k, hk⟩ := DC.kit_of_points Q C cD ch s R H a b M c points
  refine ⟨k, fun i => ?_, fun u hu => ?_⟩
  · obtain ⟨⟨u, hu⟩, hcan, hQ⟩ := hk i
    refine ⟨hQ, ?_⟩
    have hW := wreq_of_wok C cD ch (k.pt i) R H a b M c u hstd (k.val i) hu hcan hoff
      (by rw [k.sc_eq i]; exact hw)
    unfold AuxBlock8.WReq at hW
    unfold ChW_at
    refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) hW
    split_ifs <;> ring
  · let i₀ := Classical.choice k.ne
    obtain ⟨_, hinit⟩ := (hk i₀).1
    obtain ⟨i, hi⟩ := k.cover i₀ u (by rw [hinit.1]; exact hu)
    obtain ⟨v, hfrom⟩ := (hk i).1
    have hv : (k.pt i).D.host.u0.val = v := hfrom.2.2.2.2.2.2.2.2.2.1
    exact ⟨i, hv.symm.trans hi ▸ hfrom⟩

end Levent151
