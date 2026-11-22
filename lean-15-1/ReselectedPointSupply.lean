import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatumStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrimeUnconditional
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProofStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberTopFinalContextParameters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowRatWOfRowTest
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
import Development.AutomorphicArithmetic.CharacterBoxes.HostWW
import Development.AutomorphicArithmetic.CharacterBoxes.ObjCTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FunctionalsSeparateOfHoweUnramOfSiegelWeil
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TestVectorAtDatumOfJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberBundlesLargeUnramifiedExponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithAtProperty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SiegelEisensteinSecondTermHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc

namespace Levent151

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
  GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

def AnyPoint : PtProp := fun _ _ _ _ _ _ _ _ _ => True

def ReselectedObject (κ : Par) : PtProp :=
  DC.withObj (ptO (DQ.withQD (fun _ _ => κ.Pos → True)))

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 4000000 in
/-- The upstream automorphic existence theorem supplies points on *each* admissible host
and at *each* translate. Its proof uses neither of the terminal discrepancy inequalities. -/
theorem reselectedPointSupply : ObjCP ReselectedObject := by
  let row := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let O : UpperTheory.LiteratureTheorems.OpenLiteratureStatements :=
    ⟨row, UpperTheory.Zero.LLC.recTExists, row⟩
  let P := UpperTheory.LiteratureTheorems.published_results_eigen O
  let F := UpperTheory.LiteratureTheorems.published_results_first O
  have matching := UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature O
  have hL := UpperTheory.LiteratureTheorems.local_langlands_gl_recT_exists_of_literature O
  have sep := UpperTheory.Lit.functionalsSeparate_of_howeUnram_of_siegelWeil F
    GlobalTheory.Hk3.howeUnram_holds P.siegelWeilUnitaryConvergent
  have hRat : GlobalTheory.Fc.S0.RowRat := GlobalTheory.Mem.LiteralAutomorphy.rowRatW_of_rowTest
    (GlobalTheory.T.test_vector_assembly_holds F.siegelSetUnitary F.howeDualityReal
      P.greenCuspidal F P.litN.join P.litN.fe matching.1 matching.2 sep)
  let A : GroupRetwisting.AtP := fun _ _ _ _ => True
  have hA : EvLgG A := GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall (by intros; trivial)
  have bundles := GlobalTheory.T.large_unramified_exponent_bundles_exist_alt P hRat hL 0 A hA
  have hm := bundles.2.1
  let QO : Par → ∀ D : D7, Obj D → Prop := fun _ _ _ => True
  have hRec := GlobalTheory.Fc.memberTop_final_contextParameters bundles.1
    (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio P.siegelWeilUnitaryConvergent2)
    _ _ _ QO hm.1 hm.2.1 hm.2.2.1 hm.2.2.2 (EvP.of_all fun _ _ _ _ _ => trivial)
  exact GlobalTheory.T.existsObjects_of_admissibleTwistDatum _
    GlobalTheory.EX.normPrimes_and_levelPrime_unconditional.2 hRec

theorem reselectedAnyPointSupply : ObjCP (fun _ => AnyPoint) :=
  ObjCP.imp reselectedPointSupply (fun _ _ _ => trivial)

/-- The duty centres can be imposed after a canonical auxiliary prime has been
chosen. The request here may depend on all of the host rather than on its top set alone. -/
theorem reselectedDutyCentres {la : ℝ} (P : HostReq) (hla : 1 < la) (h : DC.HostExQW la P) :
    DC.HostWW la P :=
  UpperTheory.Top.hostWW _ la P hla h (UpperTheory.Top.objC_true reselectedPointSupply)
    GlobalTheory.T.windowShareRequirementClosedForm_proof

end Levent151
