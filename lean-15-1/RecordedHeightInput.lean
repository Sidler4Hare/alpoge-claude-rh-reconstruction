import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightNodesFarAndSpread

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Levent151.RecordedHeight

def mean {ι : Type*} (h : ι → ℝ) : ℝ :=
  (∑ᶠ i, h i) / (Nat.card ι : ℝ)

private theorem mean_mono {ι : Type*} [Finite ι] {h k : ι → ℝ}
    (hk : ∀ i, h i ≤ k i) : mean h ≤ mean k := by
  classical
  let _ := Fintype.ofFinite ι
  unfold mean
  simp only [finsum_eq_sum_of_fintype]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hk i) (Nat.cast_nonneg _)

private theorem mean_shift_div {ι : Type*} [Finite ι] [Nonempty ι] (h : ι → ℝ)
    (a d : ℝ) : mean (fun i => (h i + a) / d) = (mean h + a) / d := by
  classical
  let _ := Fintype.ofFinite ι
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [mean, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, ← Finset.sum_div,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  by_cases hd : d = 0
  · simp [hd]
  · field_simp

/-- Exact elimination of the auxiliary component slopes at a fixed cutoff. -/
theorem slopes_iff {ι : Type*} [Finite ι] [Nonempty ι] (h : ι → ℝ)
    {ρ s c X : ℝ} (hρ : ρ < 1) (hc : 0 ≤ c) (hf : ∀ i, 0 ≤ h i + s) :
    (∃ l : ι → ℝ, (∀ i, (1 - ρ) * max 0 (l i + s) ≤ h i + s + c) ∧ -X ≤ mean l) ↔
      0 ≤ mean h + ρ * s + c + (1 - ρ) * X := by
  have hd : 0 < 1 - ρ := by linarith
  let lmax : ι → ℝ := fun i => (h i + (ρ * s + c)) / (1 - ρ)
  have hav : mean lmax = (mean h + (ρ * s + c)) / (1 - ρ) := mean_shift_div h _ _
  constructor
  · rintro ⟨l, hl, hX⟩
    have hle : ∀ i, l i ≤ lmax i := fun i => (le_div_iff₀ hd).2 (by
      have h' := (mul_le_mul_of_nonneg_left (le_max_right 0 (l i + s)) hd.le).trans (hl i)
      linarith)
    have h' := hX.trans (mean_mono hle)
    rw [hav] at h'
    linarith [(le_div_iff₀ hd).1 h']
  · intro hm
    refine ⟨lmax, fun i => ?_, ?_⟩
    · have heq : (1 - ρ) * (lmax i + s) = h i + s + c := by
        dsimp [lmax]
        field_simp
        ring
      have hp : 0 ≤ lmax i + s := nonneg_of_mul_nonneg_right
        (heq.symm ▸ add_nonneg (hf i) hc) hd
      rw [max_eq_right hp, heq]
    · rw [hav, le_div_iff₀ hd]
      linarith

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj
open Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D}
  {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} {p : PtAt ex Csz}
  {i : Fin D.R.m} {Y : Cov p i}

/-- The original `HeightAt` with its exact three prices, reduced to the original
final-weight Chow heights. Both cutoff and mean prices are attained. -/
theorem heightAt_iff {PP C : ℝ} {u : Weight (dat p i)}
    [Finite (Comp Y.d.Xo₂ Y.d.c₂)] [Nonempty (Comp Y.d.Xo₂ Y.d.c₂)]
    (hr₀ : 0 ≤ rhoB (dat p i) u) (hr₁ : rhoB (dat p i) u < 1)
    (hTpos : 0 < (lenT p i PP : ℝ)) (hB : 0 ≤ C * unitE p)
    (hA : 0 < (6 * (dimFlag (dat p i) : ℝ) + 10 +
      lenT p i PP * (zed p i PP u + 2 * rhoB (dat p i) u))) :
    let A : ℝ := 6 * (dimFlag (dat p i) : ℝ) + 10 +
      lenT p i PP * (zed p i PP u + 2 * rhoB (dat p i) u)
    let B : ℝ := C * unitE p
    let T : ℝ := lenT p i PP
    let ρ := rhoB (dat p i) u
    HeightAt p i Y PP C u ↔
      (∀ Z, 0 ≤ Y.ht u Z + B / A) ∧
      0 ≤ mean (Y.ht u) + ρ * (B / A) + (2 - ρ) * (B / T) := by
  dsimp only
  set ρ := rhoB (dat p i) u
  set T := (lenT p i PP : ℝ)
  set B := C * unitE p
  set A : ℝ := 6 * (dimFlag (dat p i) : ℝ) + 10 + T * (zed p i PP u + 2 * ρ)
  change (∃ (s c X : ℝ) (l : Comp Y.d.Xo₂ Y.d.c₂ → ℝ),
    0 ≤ s ∧ 0 ≤ c ∧ 0 ≤ X ∧ (∀ Z, 0 ≤ Y.ht u Z + s) ∧
    (∀ Z, (1 - ρ) * max 0 (l Z + s) ≤ Y.ht u Z + s + c) ∧ -X ≤ mean l ∧
    T * X ≤ B ∧ T * c ≤ B ∧ s * A ≤ B) ↔ _
  constructor
  · rintro ⟨s, c, X, l, -, hc, -, hf, hl, hx, hX, hcb, hs⟩
    have hs' := (le_div_iff₀ hA).2 hs
    have hc' : c ≤ B / T := (le_div_iff₀ hTpos).2 (mul_comm T c ▸ hcb)
    have hX' : X ≤ B / T := (le_div_iff₀ hTpos).2 (mul_comm T X ▸ hX)
    refine ⟨fun Z => by linarith [hf Z], ?_⟩
    have hm := (slopes_iff (Y.ht u) hr₁ hc hf).1 ⟨l, hl, hx⟩
    linarith [mul_le_mul_of_nonneg_left hs' hr₀,
      mul_le_mul_of_nonneg_left hX' (sub_nonneg.mpr hr₁.le)]
  · rintro ⟨hf, hm⟩
    have hbt := div_nonneg hB hTpos.le
    obtain ⟨l, hl, hx⟩ := (slopes_iff (Y.ht u) (X := B / T) hr₁ hbt hf).2 (by linarith)
    have he : T * (B / T) = B := by field_simp
    exact ⟨_, _, _, l, div_nonneg hB hA.le, hbt, hbt, hf, hl, hx, he.le, he.le,
      (div_mul_cancel₀ _ hA.ne').le⟩

#print axioms heightAt_iff

section Rows

open GlobalTheory.MeanTop

/-- Every original cloud entry has this mandatory harmonic degree against a node. -/
theorem cloud_degree_lower {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N)
    (hW : W.Hyp) (hdiv : W.IsDiv) (τ : ι) (a b : Fin N)
    (ha : (a : ℕ) < W.kc) (hb : W.kc ≤ (b : ℕ)) :
    W.w τ / (2 * W.T) ≤ (W.u1 τ a : ℝ) - W.u1 τ b + 1 := by
  have hcloud : (0 : ℝ) ≤ W.u1 τ a := by
    exact_mod_cast (divided_entries ι N W hW hdiv τ a).2.2 ha
  linarith [((nodes_far_and_spread ι N W hW hdiv τ).1 b hb).1]

/-- Before taking absolute values, summing the original floor quotients between
two nodes bounds their divided difference by the width of the node interval. -/
theorem node_gap_upper {ι : Type} {N : ℕ} (W : Wts ι N)
    (hW : W.Hyp) (hdiv : W.IsDiv) (τ : ι) (a b : Fin N)
    (ha : W.kc ≤ (a : ℕ)) (hab : a ≤ b) :
    (W.T : ℝ) * ((W.u1 τ a : ℝ) - W.u1 τ b) ≤ 2 * (W.eta + W.S) + 4 * N := by
  let l := (b : ℕ) - a
  have hle : (a : ℕ) ≤ b := hab
  have hl : (b : ℕ) = a + l := by dsimp [l]; omega
  obtain ⟨hn, hu⟩ := W.div_gap_sum hW hdiv τ l a b hl
  have hn' : 0 ≤ (W.u1 τ a : ℝ) - W.u1 τ b := by exact_mod_cast hn
  have hu' : ((W.T : ℝ) + W.Dd + 1) * ((W.u1 τ a : ℝ) - W.u1 τ b) ≤
      W.u τ a - (W.u τ b : ℝ) + 2 * l := by exact_mod_cast hu
  have hT' : (W.T : ℝ) ≤ W.T + (W.Dd : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) W.Dd]
  have hl' : (l : ℝ) ≤ N := by
    exact_mod_cast (show l ≤ N from (Nat.sub_le _ _).trans b.isLt.le)
  have ha' := (abs_le.mp (hW.h3node τ a ha)).2
  have hb' := (abs_le.mp (hW.h3node τ b (ha.trans hle))).1
  linarith [mul_le_mul_of_nonneg_right hT' hn']

#print axioms cloud_degree_lower
#print axioms node_gap_upper

end Rows

end Levent151.RecordedHeight
