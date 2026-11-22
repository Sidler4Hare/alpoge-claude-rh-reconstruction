import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

/-! Changing the thick density before choosing the common geometric points. -/

noncomputable section

namespace Levent151

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.Inhab GlobalTheory.EX

/-- Thinning preserves the exact range and noncollinearity required by the host. -/
theorem thinSecondSet {R : Ranks} (H : Host R) (hsize : 64 ≤ H.T2.card) :
    ∃ U ⊆ H.T2, 32 * U.card ≤ H.T2.card ∧ H.T2.card ≤ 64 * U.card ∧
      (∀ s ∈ U, 4 * H.Lw * s < R.n0) ∧ NoRel U H.Lw := by
  obtain ⟨U, hU, hcard⟩ :=
    Finset.exists_subset_card_eq (s := H.T2) (Nat.div_le_self H.T2.card 32)
  refine ⟨U, hU, by omega, by omega, fun s hs => H.second_set_range s (hU hs), ?_⟩
  intro a ha b hb c hc
  exact H.second_set_no_relation a (hU ha) b (hU hb) c (hU hc)

/-- This replacement keeps the field, ranks, primes and the translate label. -/
def replaceHostSets {R : Ranks} (H : Host R) (T : Finset R.A) (U : Finset ℕ)
    (c : ℝ) (hrange : ∀ s ∈ U, 4 * H.Lw * s < R.n0) (hrel : NoRel U H.Lw) :
    Host R :=
  { H with
    TT := T
    T2 := U
    CT2 := c
    second_set_range := hrange
    second_set_no_relation := hrel }

/-- Increasing the original Behrend constant by one absorbs the fixed thinning. -/
theorem behrend_after_thinning {R : Ranks} {H : Host R} {T : Finset R.A}
    {U : Finset ℕ} (hrange : ∀ a ∈ U, 4 * H.Lw * a < R.n0) (hrel : NoRel U H.Lw)
    (h : H.secondSet_card_lower_bound) (hsize : H.T2.card ≤ 64 * U.card)
    (hscale : Real.log 64 ≤ Real.sqrt (Real.log (R.n0 : ℝ) * Real.log H.Lw)) :
    (replaceHostSets H T U (H.CT2+1) hrange hrel).secondSet_card_lower_bound := by
  let z := Real.sqrt (Real.log (R.n0 : ℝ) * Real.log H.Lw)
  let M := (R.n0 : ℝ) * Real.exp (-(H.CT2*z)) / H.Lw
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMle : M ≤ (H.T2.card : ℝ) := h
  have he : Real.exp (-z) ≤ (1 : ℝ)/64 := by
    have h' := Real.exp_le_exp.mpr (neg_le_neg hscale)
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 64), one_div] using h'
  have hc : (H.T2.card : ℝ) ≤ 64 * (U.card : ℝ) := by exact_mod_cast hsize
  change (R.n0 : ℝ) * Real.exp (-((H.CT2+1)*z)) / H.Lw ≤ U.card
  rw [show -((H.CT2+1)*z) = -(H.CT2*z) + -z by ring, Real.exp_add]
  calc _ = M * Real.exp (-z) := by dsimp [M]; ring
       _ ≤ M * (1/64) := mul_le_mul_of_nonneg_left he hM
       _ ≤ (H.T2.card : ℝ) * (1/64) := mul_le_mul_of_nonneg_right hMle (by norm_num)
       _ ≤ U.card := by linarith

/-- Only the explicitly displayed size and top-cost inputs change in HostGood. -/
theorem hostGood_replaceSets {R : Ranks} {H : Host R} {s : Scale}
    {C8 C5 c6 Cb : ℝ} {q0 : ℕ} (h : HostGood s C8 C5 c6 Cb H q0)
    {T : Finset R.A} {U : Finset ℕ} {c : ℝ}
    (hrange : ∀ a ∈ U, 4 * H.Lw * a < R.n0) (hrel : NoRel U H.Lw)
    (hTT : s.delta1 * R.n / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * s.delta1 * R.n)
    (hU : s.x ^ (-s.eps) * R.n ≤ (U.card : ℝ)) (hcap : U.card ≤ H.T2.card)
    (hBehrend : (replaceHostSets H T U c hrange hrel).secondSet_card_lower_bound)
    (hBad : BadOK s Cb (replaceHostSets H T U c hrange hrel)) :
    HostGood s C8 C5 c6 Cb (replaceHostSets H T U c hrange hrel) q0 := by
  obtain ⟨hval, harith, _, hhi, hqd, hbox, hlog, hthin, _, hother⟩ := h
  exact ⟨⟨hval.1, hTT, hU, hval.2.2.2⟩, harith, hBehrend,
    (Nat.mul_le_mul_left _ hcap).trans hhi, hqd, hbox, hlog, hthin, hBad, hother⟩

/-- Changing the top set only changes the coset shares in the analytic record. -/
theorem eAtH_replaceTop {Λ : Formalism.HC.Level} {φ : Formalism.HC.Frame}
    {H : Formalism.HC.HostRaw φ} {T T' : Finset φ.A} {x eps C : ℝ}
    (h : Formalism.HC.EAtH Λ H T x eps C) (hT : φ.Shares T' (x ^ (-1 + eps))) :
    Formalism.HC.EAtH Λ H T' x eps C :=
  ⟨h.o_eq, h.kept, h.ps, hT, h.bdG, h.bdL⟩

/-- The point's From datum transports the chosen thick set together with the top set. -/
theorem from_keeps_both_sets
    (P : Scale → ∀ (φ : Formalism.HC.Frame), Formalism.HC.HostAx φ →
      Finset φ.A → Finset ℕ → Prop)
    {C : FC} {p : Pt C} {R : Ranks} {H : Host R} {a b : R.A → ℤ}
    {M : ℕ} {c : Fin M → Fin (R.k - 2) → Bool} {u0 : ℕ} (h : p.From H a b c u0)
    (hp : P p.L.sc R.toFrame H.toHostAx H.TT H.T2) :
    P p.L.sc p.D.R.toFrame p.D.host.toHostAx p.D.host.TT p.D.host.T2 := by
  have hr := h.1
  have hf := h.field
  have ht := h.2.1
  have hu := h.2.2.1
  subst hr
  have ht' : p.D.host.TT = H.TT :=
    Finset.image_injective (Formalism.HC.Frame.A.val_injective _) ht
  rwa [eq_of_heq hf, ht', hu]

/-- Strip off the common factor 2 y^5 from the normalized four-term budget.
Here t is the top cardinality and s is the thick cardinality. -/
def translateAllowance (A B C t s : ℝ) : ℝ := A / s + B / (t*s) + C / t

/-- Exact normalization of the four displayed terms, with y = x^eps. -/
theorem fourTermAllowance {n m b k aE y t s : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hb : 0 < b) (hk : 0 < k) (ht : 0 < t) (hs : 0 < s) :
    2*y^5 * (t*aE + t*aE*m^2/k + 2*n*m^2*b*y + m*b*s*k*y^2/n^2) /
      (t*m*b*(s/n)) =
    2*y^5 * translateAllowance (n*aE*(1+m^2/k)/(m*b)) (2*n^2*m*y) (k*y^2/n) t s := by
  unfold translateAllowance
  field_simp [hn.ne', hm.ne', hb.ne', hk.ne', ht.ne', hs.ne']

/-- The fourth term is dominated by the third using the original rank estimates. -/
theorem fourth_absorbed {n m k y z s : ℝ} (hn : 0 < n) (hk : 0 ≤ k)
    (hm : 0 ≤ m) (hy : 0 ≤ y) (hs : s ≤ n)
    (hrank : k*y^2 ≤ n^2*z) (hroot : z ≤ m*y) :
    (k*y^2/n)*s ≤ 2*n^2*m*y := by
  calc _ ≤ (k*y^2/n)*n := mul_le_mul_of_nonneg_left hs (by positivity)
       _ = k*y^2 := div_mul_cancel₀ _ hn.ne'
       _ ≤ n^2*z := hrank
       _ ≤ n^2*(m*y) := mul_le_mul_of_nonneg_left hroot (sq_nonneg _)
       _ ≤ 2*n^2*m*y := by nlinarith [mul_nonneg (sq_nonneg n) (mul_nonneg hm hy)]

theorem translateAllowance_double {A B C t s t' s' : ℝ}
    (ha : 0 ≤ A) (hc : 0 ≤ C) (ht : 0 < t) (hs : 0 < s)
    (ht' : 0 < t') (hs' : 0 < s') (htop : t' ≤ 4*t) (hthick : 16*s' ≤ s)
    (hlast : C*s ≤ B) :
    2 * translateAllowance A B C t s ≤ translateAllowance A B C t' s' := by
  have hb : 0 ≤ B := (mul_nonneg hc hs.le).trans hlast
  have hA : 2 * (A/s) ≤ A/s' := by
    apply (le_div_iff₀ hs').2
    calc 2 * (A/s) * s' = A / s * (2*s') := by ring
         _ ≤ A / s * s := by gcongr; linarith
         _ = A := div_mul_cancel₀ _ hs.ne'
  have hprod : 4*(t'*s') ≤ t*s := by
    calc 4*(t'*s') = (4*t')*s' := by ring
         _ ≤ (16*t)*s' := mul_le_mul_of_nonneg_right (by linarith) hs'.le
         _ = t*(16*s') := by ring
         _ ≤ t*s := mul_le_mul_of_nonneg_left hthick ht.le
  have hB : 4*(B/(t*s)) ≤ B/(t'*s') := by
    apply (le_div_iff₀ (mul_pos ht' hs')).2
    calc 4*(B/(t*s))*(t'*s') = (B/(t*s))*(4*(t'*s')) := by ring
         _ ≤ (B/(t*s))*(t*s) := mul_le_mul_of_nonneg_left hprod (by positivity)
         _ = B := div_mul_cancel₀ _ (mul_pos ht hs).ne'
  have hC : C/t ≤ B/(t*s) := by
    rw [le_div_iff₀ (mul_pos ht hs)]
    rwa [show C/t*(t*s) = C*s by field_simp]
  unfold translateAllowance
  linarith [div_nonneg hc ht'.le]

/-- Thinning by 32g absorbs a multiplicative loss g in the old mean. -/
theorem translateAllowance_gain {A B C t s t' s' g : ℝ}
    (ha : 0 ≤ A) (hc : 0 ≤ C) (ht : 0 < t) (hs : 0 < s)
    (ht' : 0 < t') (hs' : 0 < s') (hg : 1 ≤ g)
    (htop : t' ≤ 4*t) (hthick : 32*g*s' ≤ s) (hlast : C*s ≤ B) :
    2*g*translateAllowance A B C t s ≤ translateAllowance A B C t' s' := by
  have hg' : 0 < g := by linarith
  have hb : 0 ≤ B := (mul_nonneg hc hs.le).trans hlast
  have hC : C/t ≤ B/(t*s) := by
    rw [le_div_iff₀ (mul_pos ht hs)]
    rwa [show C/t*(t*s) = C*s by field_simp]
  have hold : translateAllowance A B C t s ≤ 2*translateAllowance A B 0 t s := by
    unfold translateAllowance
    simp only [zero_div, add_zero]
    linarith [div_nonneg ha hs.le]
  have hthin : 16*(2*g*s') ≤ s := by linarith only [hthick]
  have hstep := translateAllowance_double ha (C := 0) (by rfl) ht hs ht'
    (by positivity : 0 < 2*g*s') htop hthin (by simpa using hb)
  have hnew : 2*g*translateAllowance A B 0 t' (2*g*s') =
      translateAllowance A B 0 t' s' := by
    unfold translateAllowance
    field_simp [hg'.ne', ht'.ne', hs'.ne']
    ring
  calc _ ≤ 2*g*(2*translateAllowance A B 0 t s) :=
          mul_le_mul_of_nonneg_left hold (by positivity)
       _ ≤ 2*g*translateAllowance A B 0 t' (2*g*s') :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
       _ = translateAllowance A B 0 t' s' := hnew
       _ ≤ translateAllowance A B C t' s' := by
          unfold translateAllowance
          simp only [zero_div, add_zero]
          linarith [div_nonneg hc ht'.le]

/-- An exact old mean bound transfers once the doubled allowance covers both
Fourier comparison errors. All new translates share the same four-twist value. -/
theorem pointwise_of_thinned_allowance {ι : Type*} {D : ι → ℝ} {M S W W' r r' : ℝ}
    (hMean : M ≤ W) (hOld : S ≤ M + r) (hNew : ∀ u, D u ≤ S + r')
    (hcomp : 2*W ≤ W') (herr : r+r' ≤ W) : ∀ u, D u ≤ W' := by
  intro u
  linarith [hNew u]

end Levent151
