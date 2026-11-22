import Formalism.LocalRingCardinality.DataBu
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowE
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedRankEqFinrank

noncomputable section

namespace Levent151

open Formalism.BasicNotions
open Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

section Orbit

variable {ι H : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H]

/-- An integral ramified test on one free orbit, congruent to the orbit indicator
modulo the order of the single-place unit group. -/
def orbitWeight (A : Type*) [CommRing A] (a g : ι → H) : A :=
  ∏ v, (1 - if g v = a v then (Fintype.card H : A) else 0)

theorem orbitWeight_fiber_sum (A : Type*) [CommRing A] (a g : ι → H) (v : ι) :
    ∑ c : H, orbitWeight A a (Pi.mulSingle v c * g) = 0 := by
  classical
  let k (w : ι) (h : H) : A := 1 - if h = a w then (Fintype.card H : A) else 0
  have hfac (c : H) : orbitWeight A a (Pi.mulSingle v c * g) =
      k v (c * g v) * ∏ w ∈ Finset.univ.erase v, k w (g w) := by
    change (∏ w, k w (((Pi.mulSingle v c : ι → H) * g) w)) = _
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), mulSingle_mul_apply_self]
    congr 1
    exact Finset.prod_congr rfl fun w hw => congrArg (k w)
      (mulSingle_mul_apply_ne v w c g (Finset.ne_of_mem_erase hw))
  have hzero : (∑ c : H, k v (c * g v)) = 0 := by
    rw [show (∑ c : H, k v (c * g v)) = ∑ h : H, k v h from
      Equiv.sum_comp (Equiv.mulRight (g v)) (k v)]
    simp [k, Finset.sum_sub_distrib]
  simp_rw [hfac]
  rw [← Finset.sum_mul, hzero, zero_mul]

omit [DecidableEq ι] [Group H] in
theorem map_orbitWeight {A B : Type*} [CommRing A] [CommRing B]
    (π : A →+* B) (a g : ι → H) :
    π (orbitWeight A a g) = orbitWeight B a g := by
  unfold orbitWeight
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : g v = a v <;> simp [hv]

omit [Group H] in
/-- The orbit sum in residue characteristic dividing the local group order
certifies nonvanishing of the integral ramified test. -/
theorem orbitWeight_test_ne_zero {A k : Type*} [CommRing A] [CommRing k]
    (π : A →+* k) (hm : (Fintype.card H : k) = 0) (a : ι → H)
    (c : (ι → H) → A) (h : (∑ g, π (c g)) ≠ 0) :
    (∑ g, orbitWeight A a g * c g) ≠ 0 := by
  intro hz
  apply h
  have hπ := congrArg π hz
  have hw (g : ι → H) : orbitWeight k a g = 1 := by
    simp [orbitWeight, hm]
  simpa only [map_sum, map_mul, map_orbitWeight, hw, one_mul, map_zero] using hπ

omit [Group H] in
/-- Nondivisibility of the orbit sum in the integer span of its complex
coefficients detects every integral ramified test on that orbit. -/
theorem orbitWeight_test_ne_zero_of_not_mem_span_multiple (a : ι → H)
    (c : (ι → H) → ℂ)
    (h : (∑ g, c g) ∉ (Submodule.span ℤ (Set.range c)).map
      ((Fintype.card H : ℤ) • (LinearMap.id : ℂ →ₗ[ℤ] ℂ))) :
    (∑ g, orbitWeight ℂ a g * c g) ≠ 0 := by
  classical
  have hd (g : ι → H) : (Fintype.card H : ℤ) ∣ 1 - orbitWeight ℤ a g := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hw : orbitWeight (ZMod (Fintype.card H)) a g = 1 := by
      simp [orbitWeight]
    change (Int.castRingHom (ZMod (Fintype.card H))) (1 - orbitWeight ℤ a g) = 0
    rw [map_sub, map_one, map_orbitWeight, hw, sub_self]
  choose k hk using hd
  intro hz
  apply h
  refine ⟨∑ g, k g • c g, Submodule.sum_mem _ (fun g _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self g))), ?_⟩
  change (Fintype.card H : ℤ) • (∑ g, k g • c g) = ∑ g, c g
  calc
    _ = ∑ g, (c g - orbitWeight ℂ a g * c g) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro g _
      have hcast := congrArg (Int.castRingHom ℂ) (hk g)
      simp only [map_sub, map_one, map_orbitWeight, map_mul, map_natCast] at hcast
      change 1 - orbitWeight ℂ a g = (Fintype.card H : ℂ) * (k g : ℂ) at hcast
      simp only [← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Int.cast_natCast]
      calc
        _ = (1 - orbitWeight ℂ a g) * c g := by rw [hcast]; ring
        _ = _ := by ring
    _ = _ := by rw [Finset.sum_sub_distrib, hz, sub_zero]

end Orbit

/-- Transport a single orbit's test to the ramified space in the original
free rank model, including its identification with the local norm kernels. -/
theorem orbitWeight_mem_Mram {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R}
    {C : ColumnChain R ι hc} {A : ColumnsAtT R C} (M : FreeRankModel A)
    {Q : Type} [DecidableEq Q] [DecidableEq M.H] (e : Q × (A.vT → M.H) ≃ M.X)
    (he : ∀ (m : A.vT → M.H) (ω : Q) (g : A.vT → M.H), e (ω, m * g) = m • e (ω, g))
    (ω : Q) (a : A.vT → M.H) :
    ((M.E.symm (fun x => if (e.symm x).1 = ω then orbitWeight ℂ a (e.symm x).2 else 0) :
      A.Mu0) : C.cls 0 → C.Y 0 → ℂ) ∈ A.Mram := by
  classical
  rw [mem_ramified_iff_model A M, LinearEquiv.apply_symm_apply]
  intro v x
  obtain ⟨⟨ω', g⟩, rfl⟩ := e.surjective x
  simp_rw [← he, Equiv.symm_apply_apply]
  by_cases h : ω' = ω
  · simpa [h] using orbitWeight_fiber_sum ℂ a g v
  · simp [h]

/-- A nonzero extended period on an allowed ramified column for a fixed lift
is witnessed by an actual number-field basis column of this very word. -/
theorem descended_basis_of_ramified_period (D : D7) (i : D.what₂.Word)
    (F : D.what₂.Amb D.what₂.mu0) (hF : F ∈ D.what₂.V0 D.what₂.mu0)
    (hper : Rows.PeriodIdentityOnDegreeZero D.what₂)
    (φ : (D.mem i).A.Mram)
    (hn : (D.mem i).P.PtilCol φ ((D.eMt i).symm F) ≠ 0) :
    ∃ j, D.what₂.Bu i (D.jN i ((D.div.Nu i).b j)) (D.what₂.iota D.what₂.mu0 F) ≠ 0 := by
  classical
  let y := D.what₂.iota D.what₂.mu0 F
  let L : D.what₂.Mu i →ₗ[ℂ] ℂ := (D.Bu_linL i y).mk' _
  by_contra! h
  have hs : Submodule.span ℂ (Set.range fun j => D.jN i ((D.div.Nu i).b j)) ≤
      LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact h j
  rw [(D.jN_basis i).2] at hs
  have hz : L ((D.eMu i).symm φ) = 0 := hs (Submodule.mem_top)
  have hbase := D.perCol_base_eq_PtilCol i ((D.eMu i).symm φ) F
  rw [LinearEquiv.apply_symm_apply, hper i _ F hF] at hbase
  exact hn (hbase.symm.trans hz)

/-- Extend a function on one orbit by zero on the others. -/
def orbitSlice {Q G X : Type} [DecidableEq Q] (e : Q × G ≃ X) (ω : Q) :
    (G → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun f x := if (e.symm x).1 = ω then f (e.symm x).2 else 0
  map_add' f g := by funext x; by_cases h : (e.symm x).1 = ω <;> simp [h]
  map_smul' c f := by funext x; by_cases h : (e.symm x).1 = ω <;> simp [h]

/-- The extended period tests full level-zero columns before restriction to
the norm kernels. The row argument is transported by this word's own map. -/
def fullOrbitPeriod (D : D7) (i : D.what₂.Word) (M : FreeRankModel (D.mem i).A)
    (F : D.what₂.Amb D.what₂.mu0) : (M.X → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (D.mem i).P.PtilCol (M.E.symm f) ((D.eMt i).symm F)
  map_add' f g := by
    simp only [map_add, Submodule.coe_add, PeriodMap.PtilCol, PeriodMap.Ptil,
      Examples₂.NZ.col_add, LinearMap.add_apply]
  map_smul' c f := by
    simp only [map_smul, Submodule.coe_smul, PeriodMap.PtilCol, PeriodMap.Ptil,
      Examples₂.NZ.col_smul, LinearMap.smul_apply, RingHom.id_apply]

private theorem linearForm_eq_sum_deltas {G : Type} [Fintype G] [DecidableEq G]
    (L : (G → ℂ) →ₗ[ℂ] ℂ) (f : G → ℂ) :
    L f = ∑ g, f g * L (Pi.single g 1) := by
  calc
    L f = L (∑ g, Pi.single g (f g)) := congrArg L (Finset.univ_sum_single f).symm
    _ = _ := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hd : Pi.single g (f g) = f g • (Pi.single g 1 : G → ℂ) := by
        ext x
        by_cases hx : x = g
        · subst x; simp
        · simp [Pi.single_eq_of_ne hx]
      rw [hd, map_smul, smul_eq_mul]

open Classical in
/-- A nonzero residue of one full orbit sum detects this prescribed descended
row by an actual number-field basis vector. The common complex scale allows
primitive normalization of the orbit coefficients before reduction. -/
theorem descended_basis_of_orbit_residue (D : D7) (i : D.what₂.Word)
    (F : D.what₂.Amb D.what₂.mu0) (hF : F ∈ D.what₂.V0 D.what₂.mu0)
    (hper : Rows.PeriodIdentityOnDegreeZero D.what₂)
    (M : FreeRankModel (D.mem i).A) {Q : Type} [DecidableEq Q] [DecidableEq M.H]
    (e : Q × ((D.mem i).A.vT → M.H) ≃ M.X)
    (he : ∀ (m : (D.mem i).A.vT → M.H) (ω : Q) g, e (ω, m * g) = m • e (ω, g))
    (ω : Q) (a : (D.mem i).A.vT → M.H)
    {O k : Type*} [CommRing O] [CommRing k] (emb : O →+* ℂ) (hinj : Function.Injective emb)
    (red : O →+* k) (hm : (Fintype.card M.H : k) = 0)
    (c : ((D.mem i).A.vT → M.H) → O) (z : ℂ) (hz : z ≠ 0)
    (hcoeff : ∀ g, fullOrbitPeriod D i M F (orbitSlice e ω (Pi.single g 1)) = z * emb (c g))
    (htrace : (∑ g, red (c g)) ≠ 0) :
    ∃ j, D.what₂.Bu i (D.jN i ((D.div.Nu i).b j)) (D.what₂.iota D.what₂.mu0 F) ≠ 0 := by
  classical
  let L := (fullOrbitPeriod D i M F).comp (orbitSlice e ω)
  have hram := orbitWeight_mem_Mram M e he ω a
  apply descended_basis_of_ramified_period D i F hF hper ⟨_, hram⟩
  change L (orbitWeight ℂ a) ≠ 0
  have hs : L (orbitWeight ℂ a) = z * emb (∑ g, orbitWeight O a g * c g) := by
    rw [linearForm_eq_sum_deltas L, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [L, LinearMap.comp_apply, hcoeff, map_mul, map_orbitWeight]
    ring
  rw [hs]
  exact mul_ne_zero hz (fun h => orbitWeight_test_ne_zero red hm a c htrace (hinj (h.trans (map_zero emb).symm)))

open Classical in
/-- For one actual word and one prescribed row, use the integer span of the
actual complex delta periods, without a shared algebraic normalization. -/
theorem descended_basis_of_orbit_span_nondivisibility (D : D7) (i : D.what₂.Word)
    (F : D.what₂.Amb D.what₂.mu0) (hF : F ∈ D.what₂.V0 D.what₂.mu0)
    (hper : Rows.PeriodIdentityOnDegreeZero D.what₂)
    (M : FreeRankModel (D.mem i).A) {Q : Type} [DecidableEq Q] [DecidableEq M.H]
    (e : Q × ((D.mem i).A.vT → M.H) ≃ M.X)
    (he : ∀ (m : (D.mem i).A.vT → M.H) (ω : Q) g, e (ω, m * g) = m • e (ω, g))
    (ω : Q) (a : (D.mem i).A.vT → M.H)
    (htrace :
      let c (g : (D.mem i).A.vT → M.H) :=
        fullOrbitPeriod D i M F (orbitSlice e ω (Pi.single g 1))
      (∑ g, c g) ∉ (Submodule.span ℤ (Set.range c)).map
        ((Fintype.card M.H : ℤ) • (LinearMap.id : ℂ →ₗ[ℤ] ℂ))) :
    ∃ j, D.what₂.Bu i (D.jN i ((D.div.Nu i).b j)) (D.what₂.iota D.what₂.mu0 F) ≠ 0 := by
  classical
  let L := (fullOrbitPeriod D i M F).comp (orbitSlice e ω)
  have hram := orbitWeight_mem_Mram M e he ω a
  apply descended_basis_of_ramified_period D i F hF hper ⟨_, hram⟩
  change L (orbitWeight ℂ a) ≠ 0
  rw [linearForm_eq_sum_deltas]
  exact orbitWeight_test_ne_zero_of_not_mem_span_multiple a (fun g => L (Pi.single g 1)) htrace

end Levent151
