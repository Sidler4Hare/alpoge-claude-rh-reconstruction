import FamilyGeometry
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc

namespace Levent151

noncomputable section

open Formalism.MainNotions UpperTheory.Top

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 4000000 in
/-- The cyclic request and any staged size requirement can be imposed together. -/
theorem arithmeticFamilyWithSizes (ψ : Formalism.HC.PChar) :
    ArithmeticSupply ((GChi ψ).cls (3 / 2)) 2 3 2 0 := by
  let row := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let O : UpperTheory.LiteratureTheorems.OpenLiteratureStatements :=
    ⟨row, UpperTheory.Zero.LLC.recTExists, row⟩
  let P := UpperTheory.LiteratureTheorems.published_results_eigen O
  let F := UpperTheory.LiteratureTheorems.published_results_first O
  have matching := UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature O
  have covol := SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
    (UpperTheory.LiteratureTheorems.resolution_char_zero_of_literature O)
    (UpperTheory.LiteratureTheorems.principalisation_char_zero_of_literature O)
    (UpperTheory.LiteratureTheorems.poincare_lelong_inv_of_literature O)
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright
    (UpperTheory.LiteratureTheorems.fargues_exact_of_literature O)
    (UpperTheory.LiteratureTheorems.zarhin_statement O)
    (UpperTheory.LiteratureTheorems.nef_rr_of_literature O)
    (UpperTheory.LiteratureTheorems.siegel_toroidal_integral_of_literature O)
    (UpperTheory.LiteratureTheorems.toroidal_for_fan_ks_of_literature O)
    (UpperTheory.LiteratureTheorems.semi_abelian_lie_seminegative_of_literature O)
    (UpperTheory.LiteratureTheorems.point_separation_pair_of_literature O)
    (UpperTheory.LiteratureTheorems.ar_degree_of_literature O)
    (UpperTheory.LiteratureTheorems.published_results_arithmetic O)
    (UpperTheory.LiteratureTheorems.grothendieck_deformation_of_literature O)
  have recT := UpperTheory.LiteratureTheorems.local_langlands_gl_recT_exists_of_literature O
  have geometry := UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound
    P F matching.1 matching.2 covol recT (fun cDep =>
      UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink
        (GlobalTheory.Mem.Top.Bl.parametersOfDependence recT cDep))
  exact arithmeticFamilyOfGeometry ψ (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters)
    geometry (supplyChi ψ (UpperTheory.One.vwin_of_row row ψ))

/-- At fixed primitive character and small positive ε, one family supplies arbitrarily
late windows, the character and cohomological conditions on every host beyond its
threshold, and the geometric witnesses with the numeric exponents used in (15.1). -/
theorem arithmeticFamily (ψ : Formalism.HC.PChar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ Fm : FamP ε, (GChi ψ).cls (3 / 2) Fm ∧ ∃ K cHH eK CL x₀ : ℝ,
        ∀ x ≥ x₀, x ∈ Fm.Win → ChainTied Fm 2 0 K cHH eK CL x := by
  obtain ⟨ε₀, h₀, hFamily⟩ := arithmeticFamilyWithSizes ψ
  refine ⟨ε₀, h₀, fun ε he hs => ?_⟩
  obtain ⟨Fm, _, hclass, _, _, _, _, _, _, tied⟩ :=
    hFamily ε he hs ⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  exact ⟨Fm, hclass, tied⟩

end

end Levent151

