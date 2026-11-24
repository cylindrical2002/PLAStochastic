import PLAStochastic.Index.CEPS.Reward.BoundedProbability

/-! # Local class bounds for renewal solutions of exponential overshoot tests -/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

variable {g φ : ℝ → ℂ} {D θ B κ : ℝ}

def rewardTestLocalBound (D θ κ x : ℝ) : ℝ :=
  D / (θ - κ) * (1 + D * Real.exp (D * x) * x)

theorem norm_rewardTestSolution_le (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    (hφ : Measurable φ) (hφB : ∀ y, 0 ≤ y → ‖φ y‖ ≤ B * Real.exp (κ * y))
    (hκ : κ < θ) {x : ℝ} (hx : 0 ≤ x) :
    ‖rewardSolution g (rewardTestSource g φ) x‖ ≤ B * rewardTestLocalBound D θ κ x := by
  let C := B * D / (θ - κ)
  have hB : 0 ≤ B := by
    have := hφB 0 le_rfl
    simpa using (norm_nonneg (φ 0)).trans this
  have hC : 0 ≤ C := by dsimp [C]; exact div_nonneg (mul_nonneg hB hg.nonneg_D) (by linarith)
  have hb := halfBdd_rewardTestSource hg hθ hφ hφB hκ
  have hbb : ∀ y, y ≤ x → ‖halfLine (rewardTestSource g φ) y‖ ≤ C := by
    intro y _hy
    rcases lt_or_ge y 0 with hy | hy
    · rw [halfLine_of_neg _ hy, norm_zero]; exact hC
    · rw [halfLine_of_nonneg _ hy]
      exact (norm_rewardTestSource_le hg hφ hφB hκ y).trans
        (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by nlinarith)))
  have hu := halfBdd_renewalDensity hg hθ
  have hU : 0 ≤ D * Real.exp (D * x) := mul_nonneg hg.nonneg_D (Real.exp_pos _).le
  have hc := hu.norm_convC_le hb hx hU (fun y hy => by
    simpa only [max_eq_left hx] using norm_renewalDensity_le_of_le hg hθ hy) hbb
  calc
    _ ≤ ‖halfLine (rewardTestSource g φ) x‖ +
        ‖convC (renewalDensity g) (halfLine (rewardTestSource g φ)) x‖ := norm_add_le _ _
    _ ≤ C + (D * Real.exp (D * x)) * C * x := add_le_add (hbb x le_rfl) hc
    _ = _ := by dsimp [C, rewardTestLocalBound]; ring

end PGM.WienerHopf
