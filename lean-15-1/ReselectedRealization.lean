import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitOfPoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFamPOfKits
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt

namespace Levent151

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
  GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc

/-- At any one scale the encoded top set and the literal integer thick set are fixed
throughout a pre-existing family, even when the point label is changed. -/
theorem fixedFamilySets {eps x : ℝ} (Fm : FamCore eps) (i j : Fm.Ix x) :
    (Fm.D x i).host.TT.image Formalism.HC.Frame.A.val =
        (Fm.D x j).host.TT.image Formalism.HC.Frame.A.val ∧
    (Fm.D x i).host.T2 = (Fm.D x j).host.T2 :=
  ⟨(Fm.TT_eq x i).trans (Fm.TT_eq x j).symm, Fm.realisedChain_torus_eq x i j⟩

/-- The two centres are chosen before the translate.  Every word is an original
HC parameter, including the root-of-unity product in HCVal. -/
theorem arithmeticWeightsForReselection (eps cD ch C8 : ℝ) (C : FC)
    (he : 0 < eps) (h52 : eps < 1 / 52) (hstd : Std C) (hD : 0 ≤ cD) (hh : 402 ≤ ch) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x →
      RankVal s R → HostVal s C8 H → ∃ a b : R.A → ℤ, WinOK s C.GK H a b ∧
      ∀ u : ℕ, ∃ hc : (Fin (R.k - 2) → Bool) → R.Psi → HCParam R,
        (∀ w, HCVal s cD ch (setUnipotentTranslate H u) (fun τ : R.Psi => (τ : R.GG))
          (hc w) (fun t => b t)) ∧
        (∀ w w' τ, (hc w τ).v = (hc w' τ).v ∧ (hc w τ).b = (hc w' τ).b ∧
          (hc w τ).e = (hc w' τ).e) ∧
        (∀ w τ (j : ℕ) (hj : j < R.k - 2), (hc w τ).u ⟨j + 1, by omega⟩ =
          (hc w τ).v ⟨j, by omega⟩ - 1 / 2 - (if w ⟨j, hj⟩ then (Delv s cD : ℚ) else 0)) ∧
        ∀ w (τ : R.Psi) (t : H.TT) (hk : 0 < R.k), (τ : R.GG) = R.tau1 t →
          (hc w τ).u ⟨0, hk⟩ = (a t : ℚ) + ((R.k : ℚ) - 1) / 2 ∧
          (hc w τ).u ⟨R.k - 1, by omega⟩ = -(b t : ℚ) - ((R.k : ℚ) - 1) / 2 := by
  obtain ⟨xw, centres⟩ := exists_weights_in_windows eps C he h52 hstd
  obtain ⟨xh, weights⟩ := exists_hc_family eps cD ch C8 he h52 hD hh
  refine ⟨max xw xh, fun s R H hs hx hR hH => ?_⟩
  obtain ⟨a, b, hab⟩ := centres s R H hs ((le_max_left _ _).trans hx) hR
  refine ⟨a, b, hab, fun u => ?_⟩
  obtain ⟨hc, hv, hagree, hcode, htop⟩ := weights s R (setUnipotentTranslate H u)
    (fun t => a t) (fun t => b t) hs ((le_max_right _ _).trans hx) hR hH
    (fun t => ⟨(hab t t.2).1.1, (hab t t.2).2.1⟩) R.Psi (Equiv.refl _)
  exact ⟨hc, hv, fun w w' τ => ⟨(hagree w w' τ).1, (hagree w w' τ).2.1,
    (hagree w w' τ).2.2.1⟩, hcode, htop⟩

/-- The canonical kit local to a prescribed host, with its common centres and word code.
Each of its points comes from this host.  Its cover contains every translate. -/
def RealizesHost (κ : Par) (Q : PtProp) (s : Scale) {R : Ranks} (H : Host R)
    (k : Kit κ.C κ.cD κ.ch s) : Prop :=
  ∃ (a b : R.A → ℤ) (M : ℕ) (code : Fin M → Fin (R.k - 2) → Bool),
    WinOK s κ.C.GK H a b ∧ Function.Injective code ∧
    (∀ i, (∃ u, (k.pt i).From H a b code u) ∧ CanonInst (k.pt i).ta.Gx ∧
      (k.pt i).Has Q ∧ Nonempty (NumAt κ.C (k.pt i).L)) ∧
    ∀ u < R.n, ∃ i, (k.pt i).From H a b code u

/-- The final threshold is uniform in the reselected host. No WOK, input centres,
word code, numerical witnesses, or translate-specific points are required. -/
theorem kitsForEveryHost {Q : Par → PtProp} (objects : ObjCP Q) :
    ParEv fun κ => ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R),
      s.eps = κ.eps → x0 ≤ s.x → RankVal s R → H.CT2 = κ.C.CT2 →
      HostGood s κ.C.P.Cpde κ.C5 κ.c6 κ.Cb H (DC.q0H H) →
      ∃ k : Kit κ.C κ.cD κ.ch s, RealizesHost κ (Q κ) s H k := by
  obtain ⟨ε0, hε, objects⟩ := objects
  refine ⟨ε0, hε, fun eps C8 C5 c6 Cb he hε0 h52 h8 => ?_⟩
  obtain ⟨K0, objects⟩ := objects eps C8 C5 c6 Cb he hε0 h52 h8
  refine ⟨K0, fun C hC h8eq hL => ?_⟩
  obtain ⟨xw, centres⟩ := exists_weights_in_windows eps C he h52 hC
  have hm := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨xc, codes⟩ := exists_injective_words eps C.CGam C.P.CF he h52
    (zero_le_one.trans (hm _ (by simp [FC.cMid]))) (zero_le_one.trans (hm _ (by simp [FC.cMid])))
  obtain ⟨do₀, objects⟩ := objects C hC h8eq hL
  obtain ⟨dn, number⟩ := szRow_numAt eps he h52 C hC
  refine ⟨max do₀ dn, fun cD hcD => ?_⟩
  obtain ⟨ho, objects⟩ := objects cD ((le_max_left _ _).trans hcD)
  obtain ⟨hn, number⟩ := number cD ((le_max_right _ _).trans hcD)
  refine ⟨max ho hn, fun ch hch => ?_⟩
  obtain ⟨xo, objects⟩ := objects ch ((le_max_left _ _).trans hch)
  obtain ⟨xn, number⟩ := number ch ((le_max_right _ _).trans hch)
  refine ⟨max (max xw xc) (max xo xn), fun s R H hs hx hR hCT hH => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨a, b, hab⟩ := centres s R H hs hx.1.1 hR
  obtain ⟨code, hi, _⟩ := codes s R hs hx.1.2 hR
  obtain ⟨k, hk⟩ := DC.kit_of_points _ C cD ch s R H a b _ code fun u hu =>
    objects s R H (DC.q0H H) a b _ code u hs hx.2.1 hR hCT hH rfl hab rfl hi hu
  refine ⟨k, a, b, _, code, hab, hi, fun i => ?_, fun u hu => ?_⟩
  · refine ⟨(hk i).1, (hk i).2.1, (hk i).2.2, ?_⟩
    exact (number _ _ (by rw [k.sc_eq i]; exact hs)
      (by rw [k.sc_eq i]; exact hx.2.2) (k.val i) (k.arith i)).1
  · let i0 := Classical.choice k.ne
    obtain ⟨_, hinit⟩ := (hk i0).1
    obtain ⟨i, hi⟩ := k.cover i0 u (by rw [hinit.1]; exact hu)
    obtain ⟨v, hfrom⟩ := (hk i).1
    have hv : (k.pt i).D.host.u0.val = v := hfrom.2.2.2.2.2.2.2.2.2.1
    exact ⟨i, hv.symm.trans hi ▸ hfrom⟩

/-- Assembly on externally fixed complete windows preserves an arbitrary condition
on the *actual* point data, including both finite sets together. -/
theorem existingWindowsOfKits {eps x0 la : ℝ} (κ : Par) (S : Scales la)
    (he : 0 < eps) (h52 : eps < 1 / 52) (hx : 1 < x0) (hla : 1 ≤ la)
    (hstd : Std κ.C) (hK : κ.C.GK.Nonneg) (Q : PtProp)
    (h : ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s →
      ∃ k : Kit κ.C κ.cD κ.ch s, ∀ i, (k.pt i).Has Q ∧ Nonempty (NumAt κ.C (k.pt i).L)) :
    ∃ Fm : FamP eps, Fm.x1 = x0 ∧ Fm.Win = S.Win ∧ classOf Q Fm := by
  choose k hk using h
  obtain ⟨Fm, hx', _, _, _, _, _, hQ, _, _, hWin, _⟩ :=
    exists_famP_of_kits eps κ.C κ.cD κ.ch x0 la S he h52 hx hla hstd hK k
      (fun s a b c i => (hk s a b c i).2)
  exact ⟨Fm, hx', hWin, hQ Q (fun s a b c i => (hk s a b c i).1)⟩

/-- A request may inspect the entire rank record, the original field and both selected sets. -/
abbrev HostSetCondition : Type 1 :=
  Scale → ∀ R : Ranks, Formalism.HC.HostAx R.toFrame → Finset R.A → Finset ℕ → Prop

def HostSetCondition.atPoint (P : HostSetCondition) : PtProp :=
  fun D L _ _ _ _ _ _ _ => P L.sc D.R D.host.toHostAx D.host.TT D.host.T2

def HostSetCondition.hostRequest (P : HostSetCondition) : HostReq :=
  fun _ s R H _ => P s R H.toHostAx H.TT H.T2

theorem realizesHost_carriesBothSets {κ : Par} {Q : PtProp} {s : Scale} {R : Ranks} {H : Host R}
    {k : Kit κ.C κ.cD κ.ch s} (h : RealizesHost κ Q s H k) (P : HostSetCondition)
    (hP : P s R H.toHostAx H.TT H.T2) (i : k.Ix) : (k.pt i).Has (P.atPoint) := by
  obtain ⟨_, _, _, _, _, _, hall, _⟩ := h
  obtain ⟨_, hf⟩ := (hall i).1
  have hr := hf.1
  have hfield := hf.field
  have htop := hf.2.1
  have hthick := hf.2.2.1
  change P (k.pt i).L.sc (k.pt i).D.R (k.pt i).D.host.toHostAx (k.pt i).D.host.TT (k.pt i).D.host.T2
  rw [k.sc_eq i]
  subst hr
  have ht := Finset.image_injective (Formalism.HC.Frame.A.val_injective _) htop
  rwa [eq_of_heq hfield, ht, hthick]

/-- The new family has exactly the prescribed window set and at each point it literally
satisfies the prescribed joint host condition. -/
theorem familyOnPrescribedHosts {eps x0 la : ℝ} (κ : Par) (S : Scales la)
    (he : 0 < eps) (h52 : eps < 1 / 52) (hx : 1 < x0) (hla : 1 ≤ la)
    (hstd : Std κ.C) (hK : κ.C.GK.Nonneg) (Q : PtProp) (P : HostSetCondition)
    (hs : ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s →
      ∃ (R : Ranks) (H : Host R) (k : Kit κ.C κ.cD κ.ch s),
        P s R H.toHostAx H.TT H.T2 ∧ RealizesHost κ Q s H k) :
    ∃ Fm : FamP eps, Fm.x1 = x0 ∧ Fm.Win = S.Win ∧ classOf (Q.and P.atPoint) Fm := by
  apply existingWindowsOfKits κ S he h52 hx hla hstd hK (Q.and P.atPoint)
  intro s he hx hm
  obtain ⟨R, H, k, hp, hk⟩ := hs s he hx hm
  refine ⟨k, fun i => ?_⟩
  have hsets := realizesHost_carriesBothSets hk P hp i
  obtain ⟨_, _, _, _, _, _, all, _⟩ := hk
  exact ⟨⟨(all i).2.2.1, hsets⟩, (all i).2.2.2⟩

end Levent151
