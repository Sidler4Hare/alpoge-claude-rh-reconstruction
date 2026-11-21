import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace PaperCertification

theorem translateProjection {A G K : Type*} [AddGroup A] [Fintype A]
    [AddGroup G] [Field K] (ι : A →+ G) (χ : AddChar G K) (t : G)
    [Decidable (χ.compAddMonoidHom ι = 0)] :
    (∑ u : A, χ (t + ι u)) =
      if χ.compAddMonoidHom ι = 0 then (Fintype.card A : K) * χ t else 0 := by
  simp_rw [AddChar.map_add_eq_mul]
  rw [← Finset.mul_sum]
  change χ t * (∑ u : A, (χ.compAddMonoidHom ι) u) = _
  rw [AddChar.sum_eq_ite]
  split <;> simp [mul_comm]

theorem meanError {U : Type*} [Fintype U] [Nonempty U]
    (D S : U → ℝ) (s e : ℝ) (h : ∀ u, |D u - S u| ≤ e)
    (hs : ∑ u, S u = Fintype.card U * s) :
    |(∑ u, D u) / Fintype.card U - s| ≤ e := by
  have hc : (0 : ℝ) < Fintype.card U := Nat.cast_pos.mpr Fintype.card_pos
  have hu : ∀ u, D u ≤ S u + e := fun u => by linarith [(abs_le.mp (h u)).2]
  have hl : ∀ u, S u - e ≤ D u := fun u => by linarith [(abs_le.mp (h u)).1]
  have up := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hu u)
  have lo := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hl u)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hs,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at up lo
  apply abs_le.mpr
  constructor
  · apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ hc).mpr
    convert lo using 1
    ring
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hc).mpr
    convert up using 1
    ring

end PaperCertification

#print axioms PaperCertification.translateProjection
#print axioms PaperCertification.meanError
