import Formalism.LocalRingCardinality.DataBu

namespace Levent151

open Formalism.BasicNotions

/-- The degree-zero rows killed by every allowed column of each actual word. -/
def periodRadical {R : Ranks} (D : Rows.Data R) (cols : ∀ u, Set (D.Mu u)) :
    Set (D.Amb D.mu0) :=
  {F | F ∈ D.V0 D.mu0 ∧ ∀ u φ, φ ∈ cols u → D.perCol u D.mu0 φ F = 0}

/-- Detection on a specified target subspace is equivalent to having only the
original descent kernel over that subspace. -/
theorem periodRadical_iff_detects {R : Ranks} (D : Rows.Data R)
    (cols : ∀ u, Set (D.Mu u)) (A : Submodule ℂ D.EE)
    (hper : Rows.PeriodIdentityOnDegreeZero D)
    (honto : ∀ y : D.EE, ∃ F ∈ D.V0 D.mu0, D.iota D.mu0 F = y)
    (hzero : ∀ u φ, D.perCol u D.mu0 φ 0 = 0) :
    (periodRadical D cols ∩ (D.iota D.mu0) ⁻¹' (A : Set D.EE) =
      (D.Usp D.mu0 : Set (D.Amb D.mu0))) ↔
    (∀ y ∈ A, y ≠ 0 → ∃ u φ, φ ∈ cols u ∧ D.Bu u φ y ≠ 0) := by
  classical
  constructor
  · intro heq y hy hy0
    obtain ⟨F, hF, hi⟩ := honto y
    by_contra! hmiss
    have hm : F ∈ periodRadical D cols ∩ (D.iota D.mu0) ⁻¹' (A : Set D.EE) :=
      ⟨⟨hF, fun u φ hφ => (hper u φ F hF).trans (hi.symm ▸ hmiss u φ hφ)⟩, (show D.iota D.mu0 F ∈ A by rwa [hi])⟩
    rw [heq] at hm
    have hz : D.iota D.mu0 F = 0 := (LinearMap.mem_ker.mp hm.2)
    exact hy0 (hi.symm.trans hz)
  · intro hdetect
    ext F
    constructor
    · rintro ⟨⟨hF, hz⟩, hA⟩
      refine ⟨hF, LinearMap.mem_ker.mpr ?_⟩
      by_contra hne
      obtain ⟨u, φ, hφ, hnz⟩ := hdetect (D.iota D.mu0 F) hA hne
      exact hnz ((hper u φ F hF).symm.trans (hz u φ hφ))
    · intro hF
      have hi : D.iota D.mu0 F = 0 := LinearMap.mem_ker.mp hF.2
      refine ⟨⟨hF.1, fun u φ _ => ?_⟩, ?_⟩
      · rw [hper u φ F hF.1, hi, ← map_zero (D.iota D.mu0)]
        exact (hper u φ 0 (D.V0 D.mu0).zero_mem).symm.trans (hzero u φ)
      · show D.iota D.mu0 F ∈ A
        rw [hi]
        exact A.zero_mem

/-- On the original division data the allowed columns are the images of the
actual number-field source. A word-coordinate equivalence does not change
this image. -/
theorem periodRadical_iff_detects_descended (D : D7) (A : Submodule ℂ D.what₂.EE)
    (hper : Rows.PeriodIdentityOnDegreeZero D.what₂)
    (honto : ∀ y : D.what₂.EE, ∃ F ∈ D.what₂.V0 D.what₂.mu0, D.what₂.iota D.what₂.mu0 F = y) :
    (periodRadical D.what₂ (fun u => Set.range (D.jN u)) ∩
      (D.what₂.iota D.what₂.mu0) ⁻¹' (A : Set D.what₂.EE) =
      (D.what₂.Usp D.what₂.mu0 : Set (D.what₂.Amb D.what₂.mu0))) ↔
    (∀ y ∈ A, y ≠ 0 → ∃ u, ∃ φ : (D.div.Nu u).V, D.what₂.Bu u (D.jN u φ) y ≠ 0) := by
  rw [periodRadical_iff_detects D.what₂ _ A hper honto (fun u φ => D.perCol_zero u φ)]
  constructor
  · intro h y hy hy0
    obtain ⟨u, _, ⟨φ, rfl⟩, hne⟩ := h y hy hy0
    exact ⟨u, φ, hne⟩
  · intro h y hy hy0
    obtain ⟨u, φ, hne⟩ := h y hy hy0
    exact ⟨u, D.jN u φ, ⟨φ, rfl⟩, hne⟩


end Levent151
