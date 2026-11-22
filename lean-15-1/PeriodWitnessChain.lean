import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern

noncomputable section

namespace Levent151

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.CayleySignature
open Formalism.MainNotions.ConjugationAmplitude

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem additive_sum {ι V : Type*} [Fintype ι] [AddCommMonoid V]
    (f : V → ℂ) (hf : ∀ a b, f (a + b) = f a + f b) (v : ι → V) :
    f (∑ i, v i) = ∑ i, f (v i) := by
  classical
  have h0 : f 0 = 0 := by
    have h := hf 0 0
    simp only [zero_add] at h
    exact (add_left_cancel ((add_zero (f 0)).trans h)).symm
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [h0]
  | insert i s hi ih => simp [Finset.sum_insert hi, hf, ih]

theorem periodNonzero_of_sum {D : D7} {X : ThetaX D} {t j : ℕ}
    {ι : Type*} [Fintype ι] (v : ι → X.AF (X.Xs t j))
    (F : X.cusp (X.Ys t j)) (h : PerNZ X t j (∑ i, v i) F) :
    ∃ i, PerNZ X t j (v i) F := by
  classical
  rcases h with ⟨hj, pos, s, hp⟩ | ⟨hj, hp⟩
  · have he := additive_sum (fun a => bB X t j pos s a F)
      (fun a b => by simp only [bB, X.conjAF_add, X.Bper_add_left, ThetaX.Bj]) v
    rw [he] at hp
    by_contra hn
    apply hp
    apply Finset.sum_eq_zero
    intro i _
    by_contra hi
    exact hn ⟨i, Or.inl ⟨hj, pos, s, hi⟩⟩
  · let f (a : X.AF (X.Xs t j)) :=
      X.Btop (X.Xs t j) (X.Ys t j) (hj ▸ X.iYXm t) (X.conjAF _ a) F
    change f (∑ i, v i) ≠ 0 at hp
    rw [additive_sum f (fun a b => by simp only [f, X.conjAF_add, X.Btop_add_left]) v] at hp
    by_contra hn
    apply hp
    apply Finset.sum_eq_zero
    intro i _
    by_contra hi
    exact hn ⟨i, Or.inr ⟨hj, hi⟩⟩

/-- Descend with the higher row fixed, constructing the next row and its test. -/
theorem periodWitness_step {D : D7} {X : ThetaX D}
    (hadm : AdmS D X) (P : TPar D) (hP : Hyp3 X P) (μ : ℕ → X.Chr)
    (hμ : IsMu X P μ)
    (π : ∀ j : ℕ, Submodule ℂ (X.AF (X.Xs P.t j)))
    (htype : ∀ j, j ≤ D.R.m → π j ≤ X.typeX P j)
    (hdecomp : ∀ j, j < D.R.m → ∀ φ ∈ π (j + 1),
      ∃ (N : ℕ) (Φ' : Fin N → X.Sch (X.Xs P.t j) (X.Xs P.t (j + 1)))
        (φ' : Fin N → X.cusp (X.Xs P.t j)),
        (∀ a, Φ' a ∈ X.fact _ _ ∧ Φ' a ∈ X.kfin _ _ ∧ (φ' a : X.AF _) ∈ π j) ∧
        φ = ∑ a, X.th _ _ (μ (j + 1)) (μ (j + 1)) (Φ' a) (φ' a))
    (j : ℕ) (hj : j < D.R.m) (F : X.cusp (X.Ys P.t (j + 1)))
    (hF : IsDv X P (j + 1) F) (φ : X.AF (X.Xs P.t (j + 1)))
    (hφ : φ ∈ π (j + 1)) (hNZ : PerNZ X P.t (j + 1) φ F) :
    ∃ (G : X.cusp (X.Ys P.t j)) (Φ : X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j))
      (ψ : X.AF (X.Xs P.t j)),
      Φ ∈ X.fact _ _ ∧ Φ ∈ X.kfin _ _ ∧ (G : X.AF _) = vth X P.t μ j Φ F ∧
      IsDv X P j G ∧ ψ ∈ π j ∧ PerNZ X P.t j ψ G := by
  obtain ⟨N, Φ', φ', ht, heq⟩ := hdecomp j hj φ hφ
  rw [heq] at hNZ
  obtain ⟨a, ha⟩ := periodNonzero_of_sum _ F hNZ
  obtain ⟨Φ, hfact, hkfin, hperiod⟩ :=
    hadm.2.2.1 P hP μ hμ j hj (φ' a) (Φ' a) (ht a).1 (ht a).2.1
      (htype j hj.le (ht a).2.2) F hF ha
  have hdv := hadm.2.2.2.2.2 P (j + 1) (Nat.succ_le_of_lt hj)
  have hstable : X.IsStable _ (dvSub X P (j + 1)) := by
    refine ⟨fun g f hf => ⟨X.actF_cusp _ g f hf.1, hdv.1 g f hf.2⟩,
      fun v g hg f hf => ⟨X.actR_cusp _ v g hg f hf.1, hdv.2 v g hg f hf.2⟩⟩
  have hreal := hadm.2.2.2.2.1 P hP μ hμ
  have hcusp : vth X P.t μ j Φ F ∈ X.cusp _ :=
    hadm.2.2.2.1 P hP μ hμ j hj (dvSub X P (j + 1)) hstable
      (fun _ hx => hx.1)
      (fun i hi hi' Ψ f hf => hreal.2 j hj i hi hi' Ψ f hf.2)
      Φ F ⟨F.2, hF⟩
  exact ⟨⟨_, hcusp⟩, Φ, φ' a, hfact, hkfin, rfl,
    hreal.1 j hj Φ F hkfin hF hcusp, (ht a).2.2, hperiod _ rfl⟩

/-- Install a preassigned top row with its supplied nonzero pairing. -/
theorem periodWitness_top {D : D7} {X : ThetaX D} (P : TPar D) (μ : ℕ → X.Chr)
    (π : ∀ j, Submodule ℂ (X.AF (X.Xs P.t j))) (F : X.cusp (X.Ys P.t D.R.m))
    (hF : IsDv X P D.R.m F) (φ : X.AF (X.Xs P.t D.R.m)) (hφ : φ ∈ π D.R.m)
    (hNZ : PerNZ X P.t D.R.m φ F) :
    Q X P μ π D.R.m := by
  let rows (j : ℕ) : X.cusp (X.Ys P.t j) :=
    Function.update (fun i => (0 : X.cusp (X.Ys P.t i))) D.R.m F j
  have htop : rows D.R.m = F := by simp [rows]
  refine ⟨rows, fun _ => 0, ?_, fun _ hge hlt => (not_lt_of_ge hge hlt).elim, ?_, ?_⟩
  · simpa only [htop] using hF
  · simpa only [htop] using hF
  · exact ⟨φ, hφ, by simpa only [htop] using hNZ⟩

/-- The dependent update touches only the row and kernel at the new index. -/
theorem periodWitness_extend {D : D7} {X : ThetaX D} (P : TPar D) (μ : ℕ → X.Chr)
    (π : ∀ i, Submodule ℂ (X.AF (X.Xs P.t i))) {j : ℕ} (hj : j < D.R.m)
    (F : ∀ i, X.cusp (X.Ys P.t i))
    (Φ : ∀ i, X.Sch (X.Ys P.t (i + 1)) (X.Ys P.t i))
    (hF : IsDv X P D.R.m (F D.R.m))
    (hchain : ∀ i, j + 1 ≤ i → i < D.R.m → Φ i ∈ X.fact _ _ ∧ Φ i ∈ X.kfin _ _ ∧
      (F i : X.AF _) = vth X P.t μ i (Φ i) (F (i + 1)) ∧ IsDv X P i (F i))
    (G : X.cusp (X.Ys P.t j)) (Ψ : X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j))
    (ψ : X.AF (X.Xs P.t j)) (hfact : Ψ ∈ X.fact _ _) (hkfin : Ψ ∈ X.kfin _ _)
    (hG : (G : X.AF _) = vth X P.t μ j Ψ (F (j + 1))) (hDv : IsDv X P j G)
    (hψ : ψ ∈ π j) (hNZ : PerNZ X P.t j ψ G) :
    Q X P μ π j := by
  let F' := Function.update F j G
  let Φ' := Function.update Φ j Ψ
  have hkeepF (i : ℕ) (hi : j < i) : F' i = F i :=
    Function.update_of_ne hi.ne' _ _
  have hkeepΦ (i : ℕ) (hi : j < i) : Φ' i = Φ i :=
    Function.update_of_ne hi.ne' _ _
  have hnewF : F' j = G := by simp [F']
  have hnewΦ : Φ' j = Ψ := by simp [Φ']
  refine ⟨F', Φ', by simpa only [hkeepF _ hj] using hF, ?_,
    by simpa only [hnewF] using hDv, ψ, hψ, by simpa only [hnewF] using hNZ⟩
  intro i hji hi
  rcases eq_or_lt_of_le hji with rfl | hji
  · simpa only [hnewF, hnewΦ, hkeepF _ (Nat.lt_succ_self j)] using
      And.intro hfact (And.intro hkfin (And.intro hG hDv))
  · simpa only [hkeepF _ hji, hkeepΦ _ hji, hkeepF _ (hji.trans (Nat.lt_succ_self i))] using
      hchain i hji hi

/-- Assemble the original Cayley-signature point witnesses from its six inputs. -/
theorem periodWitnessChain {D : D7} {X : ThetaX D} :
    TowerRallisLemma D X := by
  intro hadm P hP
  obtain ⟨μ, π, hμ, hrep, hdecomp⟩ := hadm.1 P hP
  obtain ⟨φ, hφ, F, hF, hNZ⟩ :=
    hadm.2.1 P hP (π D.R.m) (hrep D.R.m le_rfl).1 (hrep D.R.m le_rfl).2.2
  have hQ : ∀ n : ℕ, n ≤ D.R.m → Q X P μ π (D.R.m - n) := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa only [Nat.sub_zero] using periodWitness_top P μ π F hF φ hφ hNZ
    | succ n ih =>
      intro hn
      let j := D.R.m - (n + 1)
      have hj : j < D.R.m := by dsimp [j]; omega
      have heq : D.R.m - n = j + 1 := by dsimp [j]; omega
      have hprev := ih (by omega)
      rw [heq] at hprev
      obtain ⟨rows, kernels, htop, hchain, hdv, ψ, hψ, hp⟩ := hprev
      obtain ⟨G, Ψ, ξ, hfact, hkfin, hG, hdv', hξ, hp'⟩ :=
        periodWitness_step hadm P hP μ hμ π (fun i hi => (hrep i hi).2.2)
          hdecomp j hj (rows (j + 1)) hdv ψ hψ hp
      exact periodWitness_extend P μ π hj rows kernels htop hchain
        G Ψ ξ hfact hkfin hG hdv' hξ hp'
  have hbottom : Q X P μ π 0 := by simpa only [Nat.sub_self] using hQ D.R.m le_rfl
  obtain ⟨rows, kernels, htop, hchain, _, ψ, hψ, hp⟩ := hbottom
  have hm := D.R.two_le_m
  rcases hp with ⟨_, pos, s, hp⟩ | ⟨he, _⟩
  · have hodd : Odd ((X.Ys P.t 0).rank - (X.Xs P.t 0).rank) := by
      rw [X.Ys_rank P.t 0 (Nat.zero_le _), X.Xs_rank P.t 0 (Nat.zero_le _)]
      obtain ⟨m', hm'⟩ := D.R.m_even
      unfold Ranks.r
      exact ⟨m' - 1, by omega⟩
    have he : bB X P.t 0 pos s ψ (rows 0) = bB X P.t 0 pos 0 ψ (rows 0) :=
      X.Bper_odd _ _ _ pos hodd s 0 _ _
    rw [he] at hp
    exact ⟨μ, π 0, ψ, rows, kernels, pos, hμ, (hrep 0 (Nat.zero_le _)).1,
      (hrep 0 (Nat.zero_le _)).2.2, hψ, htop, fun i hi => hchain i (Nat.zero_le _) hi, hp⟩
  · omega

end Levent151
