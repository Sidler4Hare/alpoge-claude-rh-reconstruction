import Formalism.LocalRingCardinality.DataParams₂

namespace Levent151

open Formalism.BasicNotions

/-- Consecutive Fourier layer weights at the same embedding use both HC gaps. -/
theorem hcLayerSpacing {R : Ranks} (a : HCParam R) {j : ℕ} (hj : j + 1 < R.m) :
    (R.t : ℚ) + 3 ≤ a.e ⟨j + 1, hj⟩ - a.e ⟨j, by omega⟩ := by
  linarith only [a.gap_eb ⟨j, by omega⟩ hj, a.gap_be ⟨j + 1, hj⟩]

private theorem hcSpanFromFirst {R : Ranks} (a : HCParam R) (j : ℕ) (hj : j < R.m) :
    (j : ℚ) * ((R.t : ℚ) + 3) + ((R.t : ℚ) + 3) / 2 ≤
      a.e ⟨j, hj⟩ - a.b ⟨0, by have := R.two_le_m; omega⟩ := by
  induction j with
  | zero => simpa using a.gap_be ⟨0, hj⟩
  | succ j ih =>
    have prev := ih (by omega)
    have step := hcLayerSpacing a hj
    push_cast
    linarith only [prev, step]

/-- The first b-node and last e-node force this width on the actual size data. -/
theorem etaSz_ge_hcSpan {D : D7} (L : SizeData₂ D) (τ : D.what₂.Tau) :
    ((D.R.m : ℝ) - 1 / 2) * ((D.R.t : ℝ) + 3) ≤ L.etaSz := by
  have hm := D.R.two_le_m
  let k := D.R.m - 1
  have hk : k < D.R.m := by dsimp [k]; omega
  have hmk : D.R.m = k + 1 := by dsimp [k]; omega
  have span : (k : ℝ) * ((D.R.t : ℝ) + 3) + ((D.R.t : ℝ) + 3) / 2 ≤
      ((D.hc τ).e ⟨k, hk⟩ : ℝ) - ((D.hc τ).b ⟨0, by omega⟩ : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).2 (hcSpanFromFirst (D.hc τ) k hk)
    push_cast at h
    exact h
  have close := (abs_le.mp (L.be_close τ ⟨0, by omega⟩ ⟨k, hk⟩)).1
  push_cast at close
  have hmr : (D.R.m : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hmk
  rw [hmr]
  linarith only [span, close]

end Levent151
