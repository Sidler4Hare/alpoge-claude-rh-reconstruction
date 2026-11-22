import Pointwise
import Development.AutomorphicArithmetic.CharacterBoxes.Supply
import Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales

namespace Levent151

open Formalism.HC Formalism.MainNotions Formalism.LFunctionChainParameters.LErr
  UpperTheory.Top UpperTheory.Comparison₂

/-- The cohomology budget and the Fourier estimate use a single host index. -/
def Equation151At (ψ : PChar) {ε : ℝ} (Fm : FamP ε) (x factor : ℝ) : Prop :=
  x ∈ Fm.Win ∧ ∃ i : Fm.Ix x,
      VVle (Fm.D x i).host.E (Fm.D x i).R.t (Real.sqrt (Fm.L x i).sc.b) ∧
      PointwiseAt (Level.cyc ψ) (Fm.D x i).host.toHostAx (Fm.D x i).host.TT ε x factor

def Equation151Windows (ψ : PChar) {ε : ℝ} (Fm : FamP ε)
    (factor : ℝ → ℝ := fun x => x ^ (5 * ε)) : Prop :=
  ∀ Y₀ : ℝ, ∃ Y : ℝ, max 1 Y₀ ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (3 / 2 : ℝ) →
    Equation151At ψ Fm x (factor x)

theorem windows_of_tied_bound {ψ : PChar} {ε : ℝ} (Fm : FamP ε)
    (hc : (GChi ψ).cls (3 / 2) Fm) {K cHH eK CL x₀ : ℝ}
    (ht : ∀ x ≥ x₀, x ∈ Fm.Win → ChainTied Fm 2 0 K cHH eK CL x)
    {factor : ℝ → ℝ} {xL : ℝ}
    (atHost : ∀ x ≥ xL, ∀ {φ : Frame} (H : HostAx φ) (TT : Finset φ.A),
      CoreAtH H.toHostRaw TT 2 0 K cHH eK ε x →
      EAtH (Level.cyc ψ) H.toHostRaw TT x ε 4 →
      PointwiseAt (Level.cyc ψ) H TT ε x (factor x)) :
    Equation151Windows ψ Fm factor := by
  intro Y₀
  obtain ⟨Y, hY, hw⟩ := hc.1 (max (max 1 Y₀) (max x₀ (max xL (Fm.x1 + 1))))
  refine ⟨Y, (le_max_left _ _).trans hY, fun x hy hx => ?_⟩
  have hg := hw x hy hx
  obtain ⟨_, hx₀, hxL, hxF⟩ := (show
    max 1 Y₀ ≤ x ∧ x₀ ≤ x ∧ xL ≤ x ∧ Fm.x1 + 1 ≤ x by
      simpa only [max_le_iff] using hY.trans hy)
  have hf : Fm.x1 < x := by linarith
  obtain ⟨i, hi⟩ := tiedCore_of_chainTied Fm 2 0 K cHH eK CL x (ht x hx₀ hg)
  obtain ⟨hE, hV⟩ := hc.2 x hf i
  rw [Fm.L_x x i hf, Fm.L_eps x i] at hE
  exact ⟨hg, i, hV, atHost x hxL _ _ hi hE⟩

theorem windows_of_tied {ψ : PChar} {ε : ℝ} (hε : 0 < ε) (Fm : FamP ε)
    (hc : (GChi ψ).cls (3 / 2) Fm) {K cHH eK CL x₀ : ℝ}
    (ht : ∀ x ≥ x₀, x ∈ Fm.Win → ChainTied Fm 2 0 K cHH eK CL x) :
    Equation151Windows ψ Fm := by
  obtain ⟨xL, hL⟩ := large_x_eventually ε K cHH eK hε
  exact windows_of_tied_bound Fm hc ht (xL := xL)
    fun x hx _ _ _ hCore hE => pointwiseAt_of_core hCore (hL x hx) hE

end Levent151
