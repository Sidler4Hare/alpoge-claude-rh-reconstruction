import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShape
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShapeOf

/-! Extract the arithmetic family used in Alpöge's specialization. The two
existential exponents in `FamilyClassConnected` are made explicit at their
point of introduction (`DesWin`, `TopShape`). This keeps the original
selection of one family and its thresholds intact. -/

namespace Levent151

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions UpperTheory.Top

/-- The design request and five global comparison inputs hold on the same family. -/
def ArithmeticSupply (𝒞 : FamClass) (Cabs C0 eD eL : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ A : TransportedAlt,
    ∃ (Fm : FamP ε) (CH : ℝ), 𝒞 Fm ∧ 0 ≤ CH ∧ Fm.Large A CH ∧
      ChosenE Fm C0 CH ∧ TuSize Fm ∧ DGamSize Fm ∧ GlobalTheoremInputs Fm Cabs CH C0 ∧
      ∃ K cHH eK CL x₀ : ℝ, ∀ x ≥ x₀, x ∈ Fm.Win → ChainTied Fm eD eL K cHH eK CL x

open Formalism.HC GlobalTheory.EX in
private def ArithmeticGoal : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (Fm : FamP eps), G.cls la Fm → HypV Fm.toFamCore) →
    ArithmeticSupply (G.cls la) 2 3 2 0

/-- This is the selection in `UpperTheory.Top.topDesWin`, retaining both input exponents. -/
private theorem fixedDesign (𝒞 𝒞' ℰ : FamClass) (Cabs C0 eD eL : ℝ) (hEx : DesignExists (WithTw (WithSm 𝒞')) C0)
    (h1 : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm) (h2 : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → ℰ Fm)
    (hV : ∀ {eps : ℝ} (Fm : FamP eps), ℰ Fm → HypV Fm.toFamCore)
    (hN : Closed (Des 𝒞 C0) fun Fm _ => LinkN Fm)
    (hEta : Closed (Des 𝒞 C0) fun Fm _ => LinkEta Fm)
    (hIRR : Closed (Des 𝒞 C0) fun Fm _ => LinkIRR Fm)
    (hZ : Closed (Des 𝒞 C0) fun Fm _ => SmallLevelRankEq Fm)
    (hDIV : Closed (Des 𝒞 C0) fun Fm CH => TuSize Fm → DGamSize Fm → LinkDIVt Fm Cabs CH)
    (hRk : Closed (Des 𝒞 C0) fun Fm CH => ChosenE Fm C0 CH → NuFullF Fm ∧ J.MuRank Fm)
    (hG : Closed (Des 𝒞 C0) fun Fm _ => LinkG Fm)
    (hS : Closed (Des 𝒞 C0) fun Fm _ => TuSize Fm → LinkS Fm C0)
    (hGL : Closed (Des 𝒞 C0) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 eD eL) :
    ArithmeticSupply ℰ Cabs C0 eD eL := by
  obtain ⟨ε1, hε1, hA⟩ := hN.and (hDIV.and (hEta.and (hIRR.and (hZ.and (hRk.and (hG.and (hS.and hGL)))))))
  obtain ⟨ε3, hε3, hEx⟩ := hEx
  refine ⟨min ε1 ε3, lt_min hε1 hε3, fun ε h0 hlt A => ?_⟩
  obtain ⟨K, hK⟩ := hA ε h0 (le_of_lt (lt_of_lt_of_le hlt (min_le_left _ _)))
  obtain ⟨Fm, CH, hc, hCH, hBoth, hCh, hT, hDG⟩ :=
    hEx ε h0 (le_of_lt (lt_of_lt_of_le hlt (min_le_right _ _))) (K.sup A)
  obtain ⟨hL, hAreq⟩ := (Fm.large_sup K A CH).1 hBoth
  obtain ⟨aN, aD, aE, aI, aZ, aR, aG, aS, aGL⟩ := hK Fm CH ⟨⟨⟨h1 Fm hc.1.1, hc.1.2⟩, hc.2⟩, ⟨CH, hCh⟩, hT, hDG⟩ hL
  have hD := aD hT hDG aE (divinN_of_hypV Fm h0 (hV Fm (h2 Fm hc.1.1)) aN aZ)
  have inputs : GlobalTheoremInputs Fm Cabs CH C0 := ⟨aG, aS hT, aI, hD,
    J.linkMu_of_linkDIV Fm hD (aR hCh).1 (aR hCh).2 (muTu_of_tuSize Fm h0 hT) (J.muDGam_of_fact Fm hDG)⟩
  exact ⟨Fm, CH, h2 Fm hc.1.1, hCH, hAreq, hCh, hT, hDG, inputs, aGL hT hDG hCh inputs⟩

section

set_option synthInstance.maxHeartbeats 200000
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 2000000 in
/-- The geometric comparison uses division exponent 2 and loss exponent 0. -/
private theorem fixedShape : GlobalTheory.GLq.Green → _root_.GlobalTheory.Fc.TopShapeAlt True True (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) ArithmeticGoal := by
  intro hGreen 𝒜 cT hEx sel hduty selS selP selDH selC selB hRB hTw hPA hLamP hDivG hDcPtG hTu hn4 hLit hVC hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR selJ jOn hMt rRows aPt0 aPtTw aPer0 aPerTw aP10 aAtG aC2 hServ nR nRest cIc hcI irrC zL tie hU hG la G hla hH hV
  have hgl := GlobalTheory.Top.link_gl 𝒜 hduty tie hU hG
  have bRest := _root_.GlobalTheory.Top.link_brest_alt 𝒜 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie
  have hCsz : Closed (D3 3 𝒜) fun Fm _ => 0 ≤ Fm.Csz := Formalism.MainNotions.DIV.closed_Csz_ge_fn (D3 3 𝒜) fun _ => 0
  have oneMap : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm (d3_a hc) ((_root_.Formalism.L2.Top4.SingleMapCondition selB) Fm (d3_a hc)) :=
    Closed.of_class fun Fm _ _ hc => ⟨0, fun x hx h _ i j => (hRB Fm (d3_a hc) x hx h i).oneMap j⟩
  have hA2 := _root_.GlobalTheory.Top.closed_family_admissible_twist_link_alt 𝒜 sel aPt0 aPtTw aPer0 aPerTw aP10 aAtG hServ
  have hC5 := _root_.GlobalTheory.Top.selection_closed_of_wu_decay_alt 𝒜 sel selS selP selDH selC selB hWu hRF selJ jOn rRows
  have hBR : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, TuSize Fm → DGamSize Fm →
      _root_.Formalism.L2.DIV.DivisionKernelConstantBounds Fm (_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA Fm hc) 2 CH :=
    (bRest.and ((Closed.of_class fun Fm _ hc => cut_of_stable (hMt Fm (d3_a hc))).and (rRows.and (oneMap.and (hCsz.and (hA2.and (aC2.and hC5))))))).imp
      fun Fm CH _ ⟨r, o, rr, om, cz, a, c, c5⟩ hc hT hD =>
        (r hc hT hD).toRows_alt (fun hN => _root_.GlobalTheory.Top.wire_sel_alt 𝒜 sel selS selP selDH selC selB hTw hPA hDivG hDcPtG Fm hc CH cz hD (rr hc) (om hc) (r hc hT hD).bu hN) o a (complement_two_of_items c) c5
  have hDIV := _root_.Formalism.L2.DIV.closed_linkDIVt_of_closed_bridge_kernel (D3 3 𝒜) 2 (_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA) hBR
  have hsub : ∀ {eps : ℝ} (Fm : FamP eps), WithTw (WithSm (WithChN fun Fm => 𝒜 Fm ∧ G.cls la Fm)) Fm →
      WithTw (WithSm (WithChN 𝒜)) Fm := fun _ hc => ⟨⟨⟨hc.1.1.1.1, hc.1.1.2⟩, hc.1.2⟩, hc.2⟩
  have hE := _root_.GlobalTheory.Top.designExists_of_tuSize_aux4n_litThin (fun Fm => 𝒜 Fm ∧ G.cls la Fm) cT (fun hM => hEx hM la G hla hH) (fun Fm hc => sel Fm hc.1)
    (fun Fm hc => hduty Fm hc.1) (Pk.Closed.sub hTu hsub) (Pk.Closed.sub hn4 hsub) hLit
  exact fixedDesign (WithChN 𝒜) (WithChN fun Fm => 𝒜 Fm ∧ G.cls la Fm) (G.cls la) 2 3 2 0 hE
    (fun _ hc => ⟨hc.1.1, hc.2⟩) (fun _ hc => hc.1.2) hV nRest (_root_.GlobalTheory.Top.closed_linkEta_of_duty 𝒜 sel hduty)
    (_root_.GlobalTheory.Top.Irr.closed_linkIRR_of_join_count hGreen 𝒜 sel cIc hcI irrC) (_root_.GlobalTheory.Top.link_alt_alt_alt 𝒜 sel selS selP selDH selC selB hPA hLamP hDivG zL) hDIV hgl.1 (_root_.GlobalTheory.Top.closed_linkG_of_duty 𝒜 sel hduty)
    (_root_.GlobalTheory.Top.link_alt_alt_bis 𝒜 sel selS hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR) hgl.2

end

set_option synthInstance.maxHeartbeats 200000 in
/-- The three original arithmetic inputs suffice for this primitive character. -/
theorem arithmeticFamilyOfGeometry (ψ : Formalism.HC.PChar) (green : GlobalTheory.GLq.Green)
    (geometry : Nonempty (GlobalTheory.Fc.HypsAlt
      (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) GlobalTheory.Fc.DefiniteSideCondition))
    (host : GlobalTheory.EX.HostExW (3 / 2) (GChi ψ).req) :
    ArithmeticSupply ((GChi ψ).cls (3 / 2)) 2 3 2 0 := by
  obtain ⟨hyps⟩ := geometry
  have goal : ArithmeticGoal := GlobalTheory.Fc.forall_goal_of_shape_of_hyps
    _ _ _ _ (fixedShape green) trivial trivial hyps
  exact goal (3 / 2) (GChi ψ) (by norm_num) host (hypV_of_cls ψ (3 / 2))

end

end Levent151
