import Pointwise
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.PageFix

/-! The four-term bracket on the ranks of the selected family. The
factor from the density of the thick set is kept separate. -/

noncomputable section

namespace Levent151

open Formalism.BasicNotions Formalism.MainNotions

/-- In the actual family the last term is small even before multiplication
by the geometric error factor. -/
theorem family_rank_fourth_scale {eps : ℝ} (Fm : FamP eps) {x : ℝ}
    (hx : Fm.x1 < x) (i : Fm.Ix x) :
    ((Fm.D x i).R.k : ℝ) * x ^ (2*eps) ≤
      ((Fm.D x i).R.n : ℝ)^2 * x ^ ((1:ℝ)/2) := by
  have hx1 := Fm.one_lt_family_threshold.trans hx
  have hx0 := zero_lt_one.trans hx1
  obtain ⟨hn, _, hk, _⟩ := Fm.sizes x hx i
  change SizeN (Fm.L x i) at hn
  change SizeK (Fm.L x i) at hk
  unfold SizeN szTh at hn
  unfold SizeK szTh at hk
  rw [Fm.L_x x i hx, Fm.L_eps x i] at hn hk
  have he : 0 < eps := Fm.L_eps x i ▸ (Fm.L x i).sc.eps_pos
  calc _ ≤ x ^ (9 / 2 + 10*eps + eps/100) * x ^ (2*eps) :=
          mul_le_mul_of_nonneg_right hk.2 (Real.rpow_nonneg hx0.le _)
       _ ≤ (x ^ (2 + 8*eps - eps/100)) ^ 2 * x ^ ((1:ℝ)/2) := by
          rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
          apply Real.rpow_le_rpow_of_exponent_le hx1.le
          push_cast
          linarith
       _ ≤ _ := by gcongr; exact hn.1

/-- The `eps/100` slack in the family rank record gives a loss of exactly
that amount in the leading term. A stronger rank record may use `slack=0`. -/
theorem paperBracket_le_rank_budget {x eps slack b k aE : ℝ} {n nT n2 m : ℕ}
    (hx : 1 ≤ x) (he : 0 ≤ eps) (hs : 0 ≤ slack)
    (hb : 0 < b) (hk : 0 < k) (hm : 0 < (m:ℝ)) (hn : 0 < (n:ℝ))
    (ha : aE ≤ 2*x*b)
    (hmlo : x ^ ((1:ℝ)/2 - eps/16 - slack) ≤ (m:ℝ))
    (hmup : (m:ℝ) ≤ 2*x ^ ((1:ℝ)/2 - eps/16 + slack))
    (ht : (n:ℝ) ≤ 2*(nT:ℝ)*x ^ (eps/8)) (h2 : n2 ≤ n)
    (hxm : x*(m:ℝ) ≤ k)
    (hfour : k * x ^ (2*eps) ≤ (n:ℝ)^2 * x ^ ((1:ℝ)/2)) :
    paperBracket x eps n nT n2 m b k aE ≤
      14 * ((nT:ℝ)*m*b) * x ^ ((1:ℝ)/2 + 17*eps/16 + slack) := by
  let Z := x ^ ((1:ℝ)/2 + 17*eps/16 + slack)
  let B := (nT:ℝ)*m*b
  have hx0 := zero_lt_one.trans_le hx
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 1 ≤ Z := Real.one_le_rpow hx (by linarith)
  have hX : x ≤ (m:ℝ)*Z := by
    calc x = x ^ (1:ℝ) := (Real.rpow_one _).symm
         _ ≤ x ^ (((1:ℝ)/2-eps/16-slack)+((1:ℝ)/2+17*eps/16+slack)) :=
           Real.rpow_le_rpow_of_exponent_le hx (by linarith)
         _ = x ^ ((1:ℝ)/2-eps/16-slack) * Z := Real.rpow_add hx0 _ _
         _ ≤ (m:ℝ)*Z := mul_le_mul_of_nonneg_right hmlo (zero_le_one.trans hZ)
  have h1 : (nT:ℝ)*aE ≤ 2*B*Z := calc
    _ ≤ (nT:ℝ)*(2*(m*Z)*b) := by gcongr; exact ha.trans (by gcongr)
    _ = _ := by dsimp [B]; ring
  have h2' : (nT:ℝ)*aE*(m:ℝ)^2/k ≤ 2*B*Z := by
    apply (div_le_iff₀ hk).mpr
    calc _ ≤ (nT:ℝ)*(2*x*b)*(m:ℝ)^2 := by gcongr
         _ = 2*B*(x*m) := by dsimp [B]; ring
         _ ≤ 2*B*k := mul_le_mul_of_nonneg_left hxm (by positivity)
         _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*B) hk.le) (sub_nonneg.mpr hZ)]
  have h3' : (n:ℝ)*(m:ℝ)*x^eps ≤ 4*(nT:ℝ)*Z := calc
    _ ≤ (2*(nT:ℝ)*x^(eps/8))*(2*x^((1:ℝ)/2-eps/16+slack))*x^eps := by
      gcongr
    _ = 4*(nT:ℝ)*(x^(eps/8)*x^((1:ℝ)/2-eps/16+slack)*x^eps) := by ring
    _ = _ := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      dsimp [Z]
      congr 2
      ring
  have h3 : 2*(n:ℝ)*(m:ℝ)^2*b*x^eps ≤ 8*B*Z := calc
     _ = 2*((n:ℝ)*m*x^eps)*(m*b) := by ring
     _ ≤ 2*(4*(nT:ℝ)*Z)*(m*b) := by gcongr
     _ = _ := by dsimp [B]; ring
  have h4' : (n:ℝ)*x^((1:ℝ)/2) ≤ 2*(nT:ℝ)*Z := calc
     _ ≤ (2*(nT:ℝ)*x^(eps/8))*x^((1:ℝ)/2) := by gcongr
     _ = 2*(nT:ℝ)*x^(eps/8+(1:ℝ)/2) := by rw [Real.rpow_add hx0]; ring
     _ ≤ _ := by
       gcongr
       exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h4 : (m:ℝ)*b*n2*k*x^(2*eps)/(n:ℝ)^2 ≤ 2*B*Z := by
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    calc _ = ((m:ℝ)*b*(n2:ℝ))*(k*x^(2*eps)) := by ring
         _ ≤ ((m:ℝ)*b*(n:ℝ))*((n:ℝ)^2*x^((1:ℝ)/2)) := by gcongr
         _ = ((m:ℝ)*b*(n:ℝ)^2)*((n:ℝ)*x^((1:ℝ)/2)) := by ring
         _ ≤ ((m:ℝ)*b*(n:ℝ)^2)*(2*(nT:ℝ)*Z) := by gcongr
         _ = _ := by dsimp [B]; ring
  change _ ≤ 14*B*Z
  unfold paperBracket
  linarith only [h1,h2',h3,h4]

/-- Use the point's actual ranks, top set, thick set and weights.
PageWin is supplied by the original design's Duty. -/
theorem paperBracket_on_page {eps : ℝ} (Fm : FamP eps) (hp : PageWin Fm)
    {x : ℝ} (hx : Fm.x1 < x) (hx2 : 2 ≤ x) (i : Fm.Ix x)
    (htop : ChTT_at (Fm.L x i)) :
    let D := Fm.D x i
    let s := (Fm.L x i).sc
    paperBracket x eps D.R.n D.host.TT.card D.host.T2.card D.R.m s.b D.R.k s.a ≤
      14 * ((D.host.TT.card:ℝ)*D.R.m*s.b) * x ^ ((1:ℝ)/2 + 17*eps/16) := by
  let D := Fm.D x i
  let s := (Fm.L x i).sc
  change paperBracket x eps D.R.n D.host.TT.card D.host.T2.card D.R.m s.b D.R.k s.a ≤ _
  have hx1 : 1 ≤ x := by linarith
  have hx0 := zero_lt_one.trans_le hx1
  have he : 0 < eps := Fm.L_eps x i ▸ (Fm.L x i).sc.eps_pos
  obtain ⟨hn, hm, hk⟩ := hp x hx i
  have hd : s.delta1 = x^(-(eps/8)) := by
    unfold s Scale.delta1
    rw [Fm.L_x x i hx, Fm.L_eps x i]
  have hroot : Real.sqrt (x*s.delta1) = x^((1:ℝ)/2-eps/16) := by
    have hmul : x*x^(-(eps/8)) = x^((1:ℝ) + -(eps/8)) := by rw [Real.rpow_add hx0, Real.rpow_one]
    rw [hd, Real.sqrt_eq_rpow, hmul, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  change Real.sqrt (x*s.delta1) ≤ (D.R.m:ℝ) ∧ (D.R.m:ℝ) ≤ 2*Real.sqrt (x*s.delta1) at hm
  rw [hroot] at hm
  have hn0 : 0 < (D.R.n:ℝ) := (Real.rpow_pos_of_pos hx0 _).trans_le hn.1
  have hm0 := (Real.rpow_pos_of_pos hx0 _).trans_le hm.1
  have hk0 := (Real.rpow_pos_of_pos hx0 _).trans_le hk.1
  have hxm : x*(D.R.m:ℝ) ≤ (D.R.k:ℝ) := calc
    _ ≤ x*(2*x^((1:ℝ)/2-eps/16)) := by gcongr; exact hm.2
    _ ≤ x*(x*x^((1:ℝ)/2)) := by
      gcongr
      linarith
    _ = x^((1:ℝ)+1+1/2) := by rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]; ring
    _ ≤ x^(9/2+10*eps) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    _ ≤ _ := hk.1
  have ht := htop.1
  change s.delta1 * (D.R.n:ℝ)/2 ≤ (D.host.TT.card:ℝ) at ht
  rw [hd, Real.rpow_neg hx0.le] at ht
  have htn : (D.R.n:ℝ) ≤ 2*(D.host.TT.card:ℝ)*x^(eps/8) := by
    field_simp [Real.rpow_pos_of_pos hx0 (eps/8)] at ht
    linarith
  have hsize := (Fm.L x i).thickDensity_le_one
  rw [(Fm.L x i).typeDensity_eq_card_div] at hsize
  have hreal : (D.host.T2.card:ℝ) ≤ D.R.n := by simpa only [one_mul] using (div_le_iff₀ hn0).mp hsize
  have hn₂ : D.host.T2.card ≤ D.R.n := by exact_mod_cast hreal
  have hb : 0 < s.b := Real.exp_pos _
  have ha : s.a ≤ 2*x*s.b := by
    change (Fm.L x i).sc.x*s.b ≤ _
    rw [Fm.L_x x i hx]; linarith [mul_nonneg hx0.le hb.le]
  simpa only [add_zero,sub_zero] using
    paperBracket_le_rank_budget (slack := 0) hx1 he.le (le_refl _) hb hk0 hm0 hn0 ha
      (by simpa using hm.1) (by simpa using hm.2) htn hn₂ hxm (family_rank_fourth_scale Fm hx i)

/-- At fixed family the full chosen-set bound makes the reciprocal thick
density smaller than every prescribed positive power, uniformly in the point. -/
theorem family_thick_subpower {eps : ℝ} (Fm : FamP eps) {C0 CH : ℝ}
    (hc : ChosenE Fm C0 CH) {eta : ℝ} (hη : 0 < eta) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ i : Fm.Ix x,
      ((Fm.D x i).R.n : ℝ) ≤ x ^ eta * (Fm.D x i).host.T2.card := by
  obtain ⟨_, _, _, _, _, _, ⟨T, hT⟩, _⟩ := hc
  let c := |Fm.CT2| + 1
  have hc0 : 0 < c := by dsimp [c]; positivity
  let a := eta / (4*c)
  have ha : 0 < a := div_pos hη (by positivity)
  let z := min (eta/4) (a^2/3)
  have hz : 0 < z := lt_min (by positivity) (by positivity)
  obtain ⟨X₁, h₁⟩ := Formalism.MainNotions.Lnk.ev_loglog z hz
  obtain ⟨X₂, h₂⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < eta/4)).eventually_ge_atTop Fm.Co)
  refine ⟨max (max T X₁) (max X₂ (Fm.x1+2)), fun x hx i => ?_⟩
  have ht := (le_max_left T X₁).trans ((le_max_left _ _).trans hx)
  have hX₁ := (le_max_right T X₁).trans ((le_max_left _ _).trans hx)
  have hX₂ := (le_max_left X₂ (Fm.x1+2)).trans ((le_max_right _ _).trans hx)
  have h₀ := (le_max_right X₂ (Fm.x1+2)).trans ((le_max_right _ _).trans hx)
  have hxF : Fm.x1 < x := by linarith
  have hx1 : 1 < x := Fm.one_lt_family_threshold.trans hxF
  have hx0 := zero_lt_one.trans hx1
  have hlog := Real.log_pos hx1
  let D := Fm.D x i
  let Lw : ℝ := D.host.Lw
  let n₀ : ℝ := D.R.n0
  have hn₀ : 0 < n₀ := by dsimp [n₀]; exact_mod_cast D.R.toFrame.n0_pos
  have hL : 0 < Lw := by dsimp [Lw]; exact_mod_cast (by have := D.host.two_le_Lw; omega : 0 < D.host.Lw)
  obtain ⟨sN, _, _, _, _, _, _, _, _, _, _, _, sLw, _⟩ := Fm.sizes x hxF i
  unfold SizeN szTh at sN
  unfold SizeLw at sLw
  rw [Fm.L_x x i hxF, Fm.L_eps x i] at sN
  rw [Fm.L_x x i hxF] at sLw
  have heps : eps < 1 / 52 := Fm.L_eps x i ▸ (Fm.L x i).sc.eps_lt
  have hnlog : Real.log n₀ ≤ 3*Real.log x := by
    have hn : n₀ ≤ (D.R.n:ℝ) := by dsimp [n₀]; exact_mod_cast D.R.toFrame.cyclic_order_le_exponent
    have h := Real.log_le_log hn₀
      ((hn.trans sN.2).trans (Real.rpow_le_rpow_of_exponent_le hx1.le (show 2 + 8*eps + eps/100 ≤ 3 by linarith)))
    rwa [Real.log_rpow hx0] at h
  have hll : Real.log Lw ≤ z*Real.log x := by
    have h := Real.log_le_log hL sLw
    rw [Real.log_pow] at h
    exact h.trans (h₁ x hX₁)
  have hln : 0 ≤ Real.log Lw := Real.log_nonneg (by
    dsimp [Lw]
    exact_mod_cast (by have := D.host.two_le_Lw; omega : 1 ≤ D.host.Lw))
  let S := Real.sqrt (Real.log n₀ * Real.log Lw)
  have hs : S ≤ a*Real.log x := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg ha.le hlog.le, ?_⟩
    calc Real.log n₀ * Real.log Lw ≤ (3*Real.log x)*(z*Real.log x) :=
           mul_le_mul hnlog hll hln (by positivity)
         _ ≤ (a*Real.log x)^2 := by
           have Hz := mul_le_mul_of_nonneg_right (min_le_right (eta/4) (a^2/3)) (sq_nonneg (Real.log x))
           dsimp only [z] at *
           linarith only [show 3*Real.log x*(min (eta/4) (a^2/3)*Real.log x) =
             3*(min (eta/4) (a^2/3)*Real.log x^2) by ring,
             show (a*Real.log x)^2 = 3*((a^2/3)*Real.log x^2) by ring, Hz]
  have hCt : D.host.CT2*S ≤ (eta/4)*Real.log x := by
    have hc' : D.host.CT2 ≤ c := by
      dsimp [D,c]; rw [Fm.secondConstant_eq]; linarith [le_abs_self Fm.CT2]
    calc _ ≤ c*(a*Real.log x) := mul_le_mul hc' hs (Real.sqrt_nonneg _) hc0.le
         _ = _ := by dsimp [a]; field_simp
  have hsum : D.host.CT2*S + Real.log Lw ≤ (eta/2)*Real.log x := by
    have Hz := mul_le_mul_of_nonneg_right (min_le_left (eta/4) (a^2/3)) hlog.le
    change z*Real.log x ≤ _ at Hz
    linarith
  have hF : Lw * Real.exp (D.host.CT2*S) ≤ x^(eta/2) := by
    rw [← Real.exp_log hL, ← Real.exp_add, Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    linarith only [hsum]
  have hcard := hT x ht i
  change n₀ * Real.exp (-(D.host.CT2*S)) / Lw ≤ (D.host.T2.card:ℝ) at hcard
  have hN : n₀ ≤ (Lw * Real.exp (D.host.CT2*S)) * (D.host.T2.card:ℝ) := by
    have h := (div_le_iff₀ hL).mp hcard
    rw [Real.exp_neg, ← div_eq_mul_inv] at h
    linarith only [(div_le_iff₀ (Real.exp_pos _)).mp h, show
      ↑D.host.T2.card * Lw * Real.exp (D.host.CT2*S) = (Lw * Real.exp (D.host.CT2*S)) * ↑D.host.T2.card by ring]
  change (D.R.n:ℝ) ≤ x^eta * ↑D.host.T2.card
  calc _ = (D.R.o:ℝ)*n₀ := by dsimp [n₀]; exact_mod_cast D.R.toFrame.exponent_eq_index_mul_cyclic_order
       _ ≤ x^(eta/4) * (x^(eta/2)*(D.host.T2.card:ℝ)) :=
         mul_le_mul ((Fm.o_le_Co x i hxF).trans (h₂ x hX₂))
           (hN.trans (mul_le_mul_of_nonneg_right hF (Nat.cast_nonneg _))) hn₀.le (Real.rpow_nonneg hx0.le _)
       _ ≤ x^eta * ↑D.host.T2.card := by
         rw [← mul_assoc, ← Real.rpow_add hx0]
         exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) (Nat.cast_nonneg _)

/-- After dividing by `B * (n₂/n) / 2`, the quadratic error budget
has exponent `1/2 + (49/16 + eta) * eps`. Clear the denominator to
express the bound directly on the selected family's host. -/
theorem normalized_quadratic_page_budget {eps : ℝ} (Fm : FamP eps) (hp : PageWin Fm)
    {C0 CH A eta : ℝ} (hc : ChosenE Fm C0 CH) (hA : 0 ≤ A) (he : 0 < eps) (hη : 0 < eta) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ i : Fm.Ix x,
      let D := Fm.D x i
      let s := (Fm.L x i).sc
      2*A*x^(2*eps) * paperBracket x eps D.R.n D.host.TT.card D.host.T2.card D.R.m s.b D.R.k s.a * D.R.n ≤
        ((D.host.TT.card:ℝ)*D.R.m*s.b) * D.host.T2.card * x^((1:ℝ)/2+(49/16+eta)*eps) := by
  let g := eta*eps/2
  have hg : 0 < g := by dsimp [g]; positivity
  obtain ⟨X₁, h₁⟩ := family_thick_subpower Fm hc hg
  obtain ⟨X₂, h₂⟩ := Filter.eventually_atTop.1 ((tendsto_rpow_atTop hg).eventually_ge_atTop (28*A))
  obtain ⟨_, _, _, _, _, _, _, ⟨X₃, h₃⟩, _⟩ := hc
  refine ⟨max (max X₁ X₂) (max X₃ (Fm.x1+2)), fun x hx i => ?_⟩
  have hx₁ := (le_max_left X₁ X₂).trans ((le_max_left _ _).trans hx)
  have hx₂ := (le_max_right X₁ X₂).trans ((le_max_left _ _).trans hx)
  have hx₃ := (le_max_left X₃ (Fm.x1+2)).trans ((le_max_right _ _).trans hx)
  have h₀ := (le_max_right X₃ (Fm.x1+2)).trans ((le_max_right _ _).trans hx)
  have hxF : Fm.x1 < x := by linarith
  have hx2 : 2 ≤ x := by linarith [Fm.one_lt_family_threshold]
  have hx0 : 0 < x := by linarith
  let D := Fm.D x i
  let s := (Fm.L x i).sc
  let B := (D.host.TT.card:ℝ)*D.R.m*s.b
  let Q := paperBracket x eps D.R.n D.host.TT.card D.host.T2.card D.R.m s.b D.R.k s.a
  let t := (1:ℝ)/2 + 17*eps/16
  have hB : 0 ≤ B := by dsimp only [B,Scale.b]; positivity
  have hQ : Q ≤ 14*B*x^t := paperBracket_on_page Fm hp hxF hx2 i (h₃ x hx₃ i)
  have hn : (D.R.n:ℝ) ≤ x^g*(D.host.T2.card:ℝ) := h₁ x hx₁ i
  change 2*A*x^(2*eps)*Q*(D.R.n:ℝ) ≤ B*(D.host.T2.card:ℝ)*_
  calc _ ≤ 2*A*x^(2*eps)*(14*B*x^t)*(D.R.n:ℝ) := by gcongr
       _ ≤ 2*A*x^(2*eps)*(14*B*x^t)*(x^g*(D.host.T2.card:ℝ)) := by gcongr
       _ = (B*(D.host.T2.card:ℝ))*(28*A)*(x^(2*eps)*x^t*x^g) := by ring
       _ ≤ (B*(D.host.T2.card:ℝ))*x^g*(x^(2*eps)*x^t*x^g) := by gcongr; exact h₂ x hx₂
       _ = _ := by
         rw [mul_assoc, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
         dsimp [t,g]
         congr 2
         ring

end Levent151
