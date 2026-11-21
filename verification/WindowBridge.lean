import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A self-contained interface check for finite exceptional-scale avoidance.
    No declaration from the RH submission is imported. -/

namespace PaperCertification

def GoodScale (η C : ℝ) (exceptional : Finset ℕ) (x : ℝ) : Prop :=
  ∀ k ∈ exceptional, (k : ℝ) ≤ x ^ C → (k : ℝ) ≤ x ^ η

theorem logarithmicWindow (R : ℕ) (exceptional : Finset ℝ) (B U : ℝ)
    (hB : 1 ≤ B) (hU : 0 < U) (hCard : exceptional.card ≤ R) :
    ∃ y, U / (4 * (2 * B) ^ R) ≤ y ∧ 2 * y ≤ U ∧
      ∀ a ∈ exceptional, ∀ u, y ≤ u → u ≤ 2 * y → a ≤ u → B * a ≤ u := by
  classical
  induction R generalizing exceptional U with
  | zero =>
    have empty : exceptional = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hCard)
    refine ⟨U / 2, ?_, by linarith, ?_⟩
    · simp only [pow_zero, mul_one]
      linarith
    · intro a ha
      simp [empty] at ha
  | succ R ih =>
    have h2B : 0 < 2 * B := by linarith
    by_cases bad : ∃ a ∈ exceptional, U / (2 * B) < a ∧ a ≤ U
    · obtain ⟨a, ha, haLower, _⟩ := bad
      have nextCard : (exceptional.erase a).card ≤ R := by
        rw [Finset.card_erase_of_mem ha]
        omega
      obtain ⟨y, hy, hyUpper, yGood⟩ :=
        ih (exceptional.erase a) (U / (2 * B)) (div_pos hU h2B) nextCard
      refine ⟨y, ?_, ?_, ?_⟩
      · calc
          U / (4 * (2 * B) ^ (R + 1)) =
              (U / (2 * B)) / (4 * (2 * B) ^ R) := by
                rw [div_div, pow_succ]
                congr 1
                ring
          _ ≤ y := hy
      · exact hyUpper.trans (div_le_self hU.le (by linarith))
      · intro a' ha' u hyu huY hau
        have hne : a' ≠ a := by
          intro eq
          subst a'
          exact (not_lt_of_ge (huY.trans hyUpper)) (haLower.trans_le hau)
        exact yGood a' (Finset.mem_erase.mpr ⟨hne, ha'⟩) u hyu huY hau
    · refine ⟨U / 2, ?_, by linarith, ?_⟩
      · have pd : 1 ≤ (2 * B) ^ (R + 1) := one_le_pow₀ (by linarith)
        exact div_le_div_of_nonneg_left hU.le (by norm_num) (by linarith)
      · intro a ha u hyu huY hau
        have aSmall : a ≤ U / (2 * B) := by
          by_contra! h
          exact bad ⟨a, ha, h, hau.trans (by linarith)⟩
        have := (le_div_iff₀ h2B).mp aSmall
        linarith

theorem exceptionalScaleWindow (R : ℕ) (exceptional : Finset ℕ) (η C X : ℝ)
    (hη : 0 < η) (hηC : η ≤ C) (hX : 1 < X) (hCard : exceptional.card ≤ R) :
    ∃ Y, X ^ (1 / (4 * (2 * (C / η)) ^ R)) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X ∧
      ∀ x, Y ≤ x → x ≤ Y ^ (2 : ℝ) → GoodScale η C exceptional x := by
  classical
  have hC : 0 < C := hη.trans_le hηC
  have hXpos : 0 < X := zero_lt_one.trans hX
  let T := exceptional.image (fun k : ℕ => Real.log k / C)
  have hT : T.card ≤ R := Finset.card_image_le.trans hCard
  obtain ⟨y, hy, hy2, good⟩ :=
    logarithmicWindow R T (C / η) (Real.log X) ((one_le_div hη).mpr hηC) (Real.log_pos hX) hT
  have hSquare : Real.exp y ^ (2 : ℝ) = Real.exp (2 * y) := by
    rw [← Real.exp_mul, mul_comm]
  refine ⟨Real.exp y, ?_, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hXpos, Real.exp_le_exp, mul_one_div]
    exact hy
  · rw [hSquare, ← Real.le_log_iff_exp_le hXpos]
    exact hy2
  · intro x hYx hxY k hk hSmall
    have hx : 0 < x := (Real.exp_pos y).trans_le hYx
    rcases Nat.eq_zero_or_pos k with rfl | hkPos
    · simpa using (Real.rpow_pos_of_pos hx η).le
    have hkPos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkPos
    have hyx : y ≤ Real.log x := (Real.le_log_iff_exp_le hx).mpr hYx
    have hxy : Real.log x ≤ 2 * y := by
      rw [Real.log_le_iff_le_exp hx, ← hSquare]
      exact hxY
    have logk : Real.log k / C ≤ Real.log x := by
      rw [div_le_iff₀ hC, mul_comm, ← Real.log_rpow hx]
      exact Real.log_le_log hkPos' hSmall
    have kIn : Real.log k / C ∈ T := Finset.mem_image_of_mem _ hk
    have bound := good (Real.log k / C) kIn (Real.log x) hyx hxy logk
    have factor : C / η * (Real.log k / C) = Real.log k / η := by
      field_simp
    rw [factor, div_le_iff₀ hη] at bound
    rw [Real.rpow_def_of_pos hx, ← Real.log_le_iff_le_exp hkPos']
    exact bound

#print axioms logarithmicWindow
#print axioms exceptionalScaleWindow

end PaperCertification

