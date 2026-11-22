import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundOfEdgeCount
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RestOIso
import Formalism.SharpRestriction.GrowthBounds.WittIdentPI
import Formalism.LocalToGlobal.GroupLattices.FockModels.LoBlockActComp
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero

/-! A finite-precision rank test for the actual pairing in `G.LPprimeAt`.
The columns may come from different edges.  Row combinations of their
evaluations are taken only after all of the source and off-edge conditions. -/

noncomputable section

namespace LargePrimePrecision

open Formalism.MainNotions.G
open Formalism.MainNotions.flipOneThree.Pf

section Rank

variable {O K V : Type*} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module O V] {I : Type*} [Fintype I]

/-- The original interpolation witnesses can be tested on a finite matrix
modulo the indicated power times the uniformizer. -/
theorem goodRankK_iff_last_digit (π w : O) (hw : w ∈ IsLocalRing.maximalIdeal O)
    (A : Submodule O V) (φ : I → V →ₗ[O] K) (n D : ℕ) :
    GoodRankK π A (fun i => φ i) n D ↔
      ∃ (y : Fin n → A) (C : Matrix (Fin n) I O) (err : Matrix (Fin n) (Fin n) O),
        ∀ j l, ∑ i, algebraMap O K (C j i) * φ i (y l : V) =
          algebraMap O K (π ^ D * ((1 : Matrix (Fin n) (Fin n) O) j l + w * err j l)) := by
  classical
  constructor
  · rintro ⟨u, C, hu⟩
    refine ⟨fun l => u (Pi.single l 1), C, 0, fun j l => ?_⟩
    convert hu (Pi.single l 1) j using 1
    by_cases h : j = l
    · subst l
      simp
    · simp [h]
  · rintro ⟨y, C, err, hc⟩
    let P : Matrix (Fin n) (Fin n) O := 1 + w • err
    have hP : IsUnit P.det := by
      apply isUnit_det_of_one_add
      intro j l
      have he : P j l - (1 : Matrix (Fin n) (Fin n) O) j l = w * err j l := by
        simp [P, Matrix.add_apply]
      rw [he, mul_comm]
      exact Ideal.mul_mem_left _ _ hw
    let ψ (j : Fin n) : V →ₗ[O] K := ∑ i, C j i • φ i
    have hψ (j : Fin n) (v : V) : ψ j v = ∑ i, algebraMap O K (C j i) * φ i v := by
      simp [ψ, LinearMap.sum_apply, Algebra.smul_def]
    have h := goodRank_core π A (fun j => (ψ j : V → K)) D
      (fun j x z => (ψ j).map_add x z)
      (fun j c x => by rw [map_smul, Algebra.smul_def])
      (fun l => (y l : V)) (fun l => (y l).property) P
      (fun _ => π ^ D) (fun _ => 1) (fun _ => one_mul _)
      (fun j l => by rw [hψ, hc]; simp [P, Matrix.add_apply, mul_comm]) hP
    obtain ⟨u, R, hR⟩ := h
    refine ⟨u, R * C, fun x j => ?_⟩
    rw [← hR x j]
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, hψ, Finset.mul_sum,
      mul_assoc]
    exact Finset.sum_comm

end Rank

/-- For a presented matrix with elementary divisors of orders `s i`,
the jump in truncated kernel length counts exactly the orders above `t`.
A missing diagonal entry can be recorded by any order at least `t+1`. -/
theorem clipped_length_succ {ι : Type*} [Fintype ι] (s : ι → ℕ) (t : ℕ) :
    (∑ i, min (s i) (t + 1)) =
      (∑ i, min (s i) t) + (Finset.univ.filter (fun i => t < s i)).card := by
  classical
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

section Local

variable {p n' m : ℕ} (R : RS p n') (lam : Fin n' → Fin (m + 1) → ℤ)

private def columnFunctional (f : Vsp R.Kf lam) :
    Module.Dual R.Kf (Vsp R.Kf lam) →ₗ[R.O] R.Kf where
  toFun := be p 1 lam f
  map_add' := be_add R lam f
  map_smul' c z := by rw [be_smul, Algebra.smul_def]; rfl

/-- Every entry of the actual evaluation matrix is integral, including when
its columns run through several edges with the same target. -/
theorem column_entry_integral (t c : ℕ) {e : Edge R.W R.Qq (m + 1)}
    (he : IsEdge p n' 1 e) {f : Vsp R.Kf lam} (hf : f ∈ CCL R lam t c e)
    {g : Module.Dual R.Kf (Vsp R.Kf lam)}
    (hg : g ∈ Ntgt p n' R.ι R.σ R.w 1 lam t e.tgt) :
    ∃ z : R.O, be p 1 lam f g = algebraMap R.O R.Kf z := by
  simp only [CCL, Submodule.mem_inf] at hf
  simp only [Ntgt, Submodule.mem_inf, Submodule.mem_iInf] at hg
  exact be_Re R lam e hf.1.2 (hg.2 e ⟨he, rfl⟩)

/-- The source columns still satisfy all exact off-edge conditions.  The
pairing test only needs their integral values modulo `w^(2*D+1)`. -/
def LocalMatrixTest (t D : ℕ) (κ : ℝ) (c : ℕ)
    (L : Submodule R.W (Fin (m + 1) → R.Qq)) : Prop :=
  ∃ (M : ℕ) (e : Fin M → Edge R.W R.Qq (m + 1)) (f : Fin M → Vsp R.Kf lam),
    (∀ i, IsEdge p n' 1 (e i) ∧ (e i).tgt = L ∧ f i ∈ CCL R lam t c (e i)) ∧
    ∃ n : ℕ, (1 - κ) * (dimV R.Kf lam : ℝ) ≤ n ∧
      ∃ (y : Fin n → Ntgt p n' R.ι R.σ R.w 1 lam t L)
        (C : Matrix (Fin n) (Fin M) R.O) (err : Matrix (Fin n) (Fin n) R.O),
        ∀ j l, ∑ i, algebraMap R.O R.Kf (C j i) * be p 1 lam (f i) (y l) =
          algebraMap R.O R.Kf ((p : R.O) ^ D *
            ((1 : Matrix (Fin n) (Fin n) R.O) j l + R.w * err j l))

theorem lpprimeAt_iff_matrix_test (t D : ℕ) (κ : ℝ) (c : ℕ)
    (L : Submodule R.W (Fin (m + 1) → R.Qq)) :
    LPprimeAt p n' R.ι R.σ R.w 1 lam t D κ c L ↔ LocalMatrixTest R lam t D κ c L := by
  constructor
  · rintro ⟨M, e, f, he, hf, hoff, n, hn, hgood⟩
    refine ⟨M, e, f, fun i => ⟨(he i).1, (he i).2, ?_⟩, n, hn,
      (goodRankK_iff_last_digit (p : R.O) R.w R.w_mem _ (fun i => columnFunctional R lam (f i)) n D).mp hgood⟩
    have hs := hf i
    simp only [Nsrc, Submodule.mem_inf, Submodule.mem_iInf] at hs
    simp only [CCL, Submodule.mem_inf, Submodule.mem_iInf]
    exact ⟨⟨hs.1, hs.2 (e i) ⟨(he i).1, rfl⟩⟩, fun e' h => hoff i e' h.1 h.2.1 h.2.2⟩
  · rintro ⟨M, e, f, he, n, hn, htest⟩
    exact ⟨M, e, f, fun i => ⟨(he i).1, (he i).2.1⟩,
      fun i => CCL_le_Nsrc R lam t c _ (he i).2.2,
      fun i e' h hsrc hne => CCL_other R lam t c _ e' h hsrc hne (he i).2.2, n, hn,
      (goodRankK_iff_last_digit (p : R.O) R.w R.w_mem _ (fun i => columnFunctional R lam (f i)) n D).mpr htest⟩

end Local

open Classical in
/-- A finite list contains exactly the dominant lifts of the given top
coordinates. Dominance bounds every entry on a top by the two endpoints. -/
def lifts {n' m : ℕ} (TT : Finset (Fin n')) (a b : Fin n' → ℤ) (c : ℕ) :
    Finset (Fin n' → Fin (m + 1) → ℤ) :=
  (Fintype.piFinset (fun s : Fin n' => Fintype.piFinset (fun _ : Fin (m + 1) =>
    Finset.Icc (min (-b s) (-(c : ℤ))) (max (a s) (c : ℤ))))).filter
    (fun lam => IsBaseWeight TT a b c lam ∧ IsDominant lam)

theorem mem_lifts {n' m : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ} {c : ℕ}
    {lam : Fin n' → Fin (m + 1) → ℤ} :
    lam ∈ lifts TT a b c ↔ IsBaseWeight TT a b c lam ∧ IsDominant lam := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨hb, hd⟩
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun s => ?_), hb, hd⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    by_cases hs : s ∈ TT
    · obtain ⟨h0, hm, _⟩ := (hb s).1 hs
      exact ⟨(min_le_left _ _).trans (hm ▸ hd s (Fin.le_last i)),
        (hd s (Fin.zero_le i)).trans (h0 ▸ le_max_left _ _)⟩
    · have h := abs_le.mp ((hb s).2 hs i)
      exact ⟨(min_le_right _ _).trans h.1, h.2.trans (le_max_right _ _)⟩

open Formalism.L2.GlobalTheoryTheory.Arith

/-- For the actual arithmetic infimum, one fixed admissible ring setting and
one prescribed lattice suffice for every top vector and every dominant lift. -/
theorem kapISet_iff_one_matrix_test (B : Base) (K : Consts) (p n' : ℕ)
    (R : RS p n') (TT : Finset (Fin n')) (a b : Fin n' → ℤ) (κ : ℝ)
    (L : Submodule R.W (Fin (B.R.k - 1 + 1) → R.Qq)) (hL : IsLattice R.W L) :
    κ ∈ Loc.kapISet B K p n' TT a b ↔
      0 ≤ κ ∧ ∀ lam ∈ lifts (m := B.R.k - 1) TT a b ⌊B.cG⌋₊,
        LocalMatrixTest R lam ⌈Loc.tIf B K p n' TT a b⌉₊ (Loc.DIf B K p n') κ
          (8 * (Loc.DIf B K p n' + 1)) L := by
  constructor
  · rintro ⟨hκ, h⟩
    refine ⟨hκ, fun lam hl => ?_⟩
    obtain ⟨hb, hd⟩ := mem_lifts.mp hl
    exact (lpprimeAt_iff_matrix_test R lam _ _ _ _ _).mp
      ((h R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std lam hb hd).2 L hL)
  · rintro ⟨hκ, h⟩
    refine ⟨hκ, ?_⟩
    intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd lam hb hd
    let R' : RS p n' := ⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩
    apply (lpRingIndep_of'' WittPI.wittIdentity_holds restOIso) p n' R R' _ _ _ _ _ _ _
    apply Formalism.L2.G.Model.lPOneEvery p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 _ _ _ _ _ _ _ hd
    exact ⟨by omega, L, hL, (lpprimeAt_iff_matrix_test R lam _ _ _ _ _).mpr
      (h lam (mem_lifts.mpr ⟨hb, hd⟩))⟩

section RootCount

/-- In a consecutive window, a single residue class occurs at most once
per complete block of length `q`, plus one final occurrence. -/
theorem residue_window_card {W q : ℕ} (s : Finset ℕ) (hs : s ⊆ Finset.range W)
    (hmod : ∀ i ∈ s, ∀ j ∈ s, i % q = j % q) : s.card ≤ W / q + 1 := by
  have h := Finset.card_le_card_of_injOn (s := s) (t := Finset.range (W / q + 1))
    (fun i => i / q) (by
      intro i hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_range.mp (hs hi)).le)))
    (by
      intro i hi j hj hij
      have h := hmod i hi j hj
      change i / q = j / q at hij
      calc i = i % q + q * (i / q) := (Nat.mod_add_div i q).symm
           _ = j % q + q * (j / q) := by rw [h, hij]
           _ = j := Nat.mod_add_div j q)
  simpa using h

private theorem truncated_le_indicators (v : ℝ) (m : ℕ) :
    min v (m : ℝ) ≤ ∑ j ∈ Finset.range m, if (j : ℝ) < v then (1 : ℝ) else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    split_ifs with h
    · rw [min_eq_right h.le] at ih
      linarith [min_le_right v ((m : ℝ) + 1)]
    · push Not at h
      rw [min_eq_left h] at ih
      simpa [min_eq_left (show v ≤ (m : ℝ) + 1 by linarith)] using ih

/-- A root in an algebraic extension may have fractional valuation. At
threshold `j`, any two integers closer than `p^(-j)` to it still agree
modulo `p^(j+1)`. The estimate also permits a zero at a sample point,
by using an already clipped valuation there. -/
theorem sum_truncated_root_window (p W m : ℕ) (hp : 1 < p) (v : ℕ → ℝ)
    (hball : ∀ j < m, ∀ a < W, ∀ b < W, (j : ℝ) < v a → (j : ℝ) < v b →
      a % p ^ (j + 1) = b % p ^ (j + 1)) :
    ∑ a ∈ Finset.range W, min (v a) (m : ℝ) ≤ (W : ℝ) / (p - 1) + m := by
  classical
  have hclass (j : ℕ) (hj : j < m) :
      (∑ a ∈ Finset.range W, if (j : ℝ) < v a then (1 : ℝ) else 0) ≤
        (W : ℝ) / (p : ℝ) ^ (j + 1) + 1 := by
    let s := (Finset.range W).filter fun a => (j : ℝ) < v a
    have hc := residue_window_card (q := p ^ (j+1)) s (Finset.filter_subset _ _)
      (fun a ha b hb => hball j hj a (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        b (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp ha).2
        (Finset.mem_filter.mp hb).2)
    have hq : 0 < (p : ℝ) ^ (j+1) := by positivity
    have hd : ((W / p^(j+1) : ℕ) : ℝ) ≤ (W : ℝ) / (p : ℝ)^(j+1) := by
      apply (le_div_iff₀ hq).mpr
      exact_mod_cast Nat.div_mul_le_self W (p^(j+1))
    have hs : (∑ a ∈ Finset.range W, if (j : ℝ) < v a then (1 : ℝ) else 0) = s.card := by
      simp [s, Finset.sum_boole]
    rw [hs]
    have hcR : (s.card : ℝ) ≤ (W / p ^ (j + 1) : ℕ) + (1 : ℝ) := by exact_mod_cast hc
    linarith
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp
  have hgeom (k : ℕ) : ((p : ℝ) - 1) * (∑ j ∈ Finset.range k, 1 / (p : ℝ) ^ (j + 1)) =
      1 - 1 / (p : ℝ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      have hpk : (p : ℝ) ^ k ≠ 0 := by positivity
      field_simp
      ring
  have hg : (∑ j ∈ Finset.range m, 1 / (p : ℝ) ^ (j + 1)) ≤ 1 / ((p : ℝ) - 1) := by
    apply (le_div_iff₀ (by linarith)).mpr
    rw [mul_comm, hgeom]
    have : 0 ≤ 1 / (p : ℝ) ^ m := by positivity
    linarith
  calc
    _ ≤ ∑ a ∈ Finset.range W, ∑ j ∈ Finset.range m, if (j : ℝ) < v a then (1 : ℝ) else 0 :=
      Finset.sum_le_sum fun a _ => truncated_le_indicators (v a) m
    _ = _ := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range m, ((W : ℝ) / (p : ℝ) ^ (j + 1) + 1) :=
      Finset.sum_le_sum fun j hj => hclass j (Finset.mem_range.mp hj)
    _ = (W : ℝ) * (∑ j ∈ Finset.range m, 1 / (p : ℝ) ^ (j + 1)) + m := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, mul_one_div]
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg W : 0 ≤ (W : ℝ))
      linarith [show (W : ℝ) * (1 / ((p : ℝ) - 1)) = W / (p - 1) by ring]

/-- Sum the individual root bounds, retaining the actual determinant degree
(the number of roots with multiplicity). -/
theorem sum_bad_rank_of_clipped_roots {ι : Type*} [Fintype ι] (p W m : ℕ) (hp : 1 < p)
    (cut lead : ℝ) (bad : ℕ → ℕ) (v : ι → ℕ → ℝ)
    (hball : ∀ r j, j < m → ∀ a < W, ∀ b < W, (j : ℝ) < v r a → (j : ℝ) < v r b →
      a % p ^ (j + 1) = b % p ^ (j + 1))
    (hdet : ∀ a < W, cut * (bad a : ℝ) ≤ lead + ∑ r, min (v r a) (m : ℝ)) :
    cut * (∑ a ∈ Finset.range W, (bad a : ℝ)) ≤
      W * lead + Fintype.card ι * ((W : ℝ) / (p - 1) + m) := by
  classical
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ a ∈ Finset.range W, (lead + ∑ r, min (v r a) (m : ℝ)) :=
      Finset.sum_le_sum fun a ha => hdet a (Finset.mem_range.mp ha)
    _ = W * lead + ∑ r, ∑ a ∈ Finset.range W, min (v r a) (m : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp
    _ ≤ W * lead + ∑ _r : ι, ((W : ℝ) / (p - 1) + m) :=
      add_le_add_right (Finset.sum_le_sum fun r _ =>
        sum_truncated_root_window p W m hp (v r) (hball r)) _
    _ = _ := by simp [mul_add]

section Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Divisibility in several rows multiplies in the determinant. -/
theorem powers_dvd_det_of_rows (q : R) (K : ℕ) (S : Finset ι) (A : Matrix ι ι R)
    (h : ∀ i ∈ S, ∀ j, q^K ∣ A i j) : q^(K * S.card) ∣ A.det := by
  classical
  let r (i : ι) := if i ∈ S then q^K else 1
  have hr (i j : ι) : r i ∣ A i j := by
    by_cases hi : i ∈ S
    · simpa [r, hi] using h i hi j
    · simp [r, hi]
  choose B hB using hr
  let B' : Matrix ι ι R := Matrix.of B
  have hA : A = Matrix.diagonal r * B' := by
    ext i j
    rw [Matrix.diagonal_mul]
    exact hB i j
  have hprod : (∏ i, r i) = q ^ (K * S.card) := by
    simp [r, ← pow_mul]
  rw [hA, Matrix.det_mul, Matrix.det_diagonal, hprod]
  exact dvd_mul_right _ _

/-- Integral changes of coordinates, including polynomial perturbations,
preserve the power contributed by every deep row at the sample. This
works also when some of the original Smith entries are zero. -/
theorem smith_perturbation_det (q : R) (K : ℕ) (S : Finset ι) (z : ι → R)
    (U V E : Matrix ι ι R) (h : ∀ i ∈ S, q^K ∣ z i) :
    q^(K * S.card) ∣ (U * (Matrix.diagonal z + q^K • E) * V).det := by
  classical
  have hd := powers_dvd_det_of_rows q K S (Matrix.diagonal z + q^K • E) (by
    intro i hi j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    apply dvd_add
    · by_cases he : i = j
      · subst j
        simpa using h i hi
      · simp [Matrix.diagonal_apply_ne _ he]
    · exact dvd_mul_right _ _)
  rw [Matrix.det_mul, Matrix.det_mul]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _

end Matrix

/-! For the inner Gram matrix `A(z) = ∑_{j≤δ} C_j binom(z,j)` in
`FockGramWindow/GramWindow2.lean`, put `K=k+1` and
`m=K+floor(log_p(max(1,δ)))`. The polynomial identity

    binom(p^m X,j) = (-1)^(j-1) (p^m X/j) ∏_{i=1}^{j-1}(1-p^m X/i)

gives coefficientwise divisibility by `p^K` for `1≤j≤δ`. Vandermonde's
identity then gives `A(z+p^m X) ≡ A(z) mod p^K`. Use the Smith bases at
`z` in the polynomial ring and apply `smith_perturbation_det`. For
`P=det A ≠ 0`, multiplicativity of the Gauss norm gives the valuation
of `P(z+p^m X)` as the leading coefficient valuation plus the sum of
`min(m,v_p(z-α))` over roots with multiplicity. For each root, including
a root at the sample, two integers at valuation greater than `j` differ
by a multiple of `p^(j+1)`. The preceding two window lemmas give

    average(bad rank) ≤ (lead + deg(P)/(p-1) + deg(P)*m/W)/K.

Since `deg(P) ≤ nδ`, this implies the source bound with the actual
degree in the last term and no restriction on the positive window size
`W`. The two polynomial identities and the passage to the Gauss norm
in this paragraph are the mathematical link to the formal lemmas above. -/

end RootCount

end LargePrimePrecision
