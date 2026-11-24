import PLAStochastic.Index.CEPS.Final.TaylorRep
import PLAStochastic.ForMathlib.Analysis.Complex.FiniteBoxTaylor

/-! # Genuine finite-dimensional analytic models supply the exact CEPS coordinate-box format -/

noncomputable section
open Complex Finset
namespace PGM

/-- Restricting an actual finite-dimensional complex analytic model to real jet coordinates
produces one fixed family of Taylor coefficients for every CEPS box order. -/
theorem cepsJetScal_of_analytic_finite_model {d : ℕ} (p₀ : ℕ → ℝ)
    {F : (Fin d → ℂ) → ℂ}
    (hF : AnalyticAt ℂ F (fun i : Fin d => (p₀ i : ℂ))) :
    ∃ T : (Fin d → ℕ) → ℂ,
      CepsJetScal p₀ (fun p => F (fun i : Fin d => (p i : ℂ))) T := by
  obtain ⟨P, hP⟩ := hF
  refine ⟨finiteCoordinateTaylorCoeff P, fun N => ?_⟩
  obtain ⟨R, K, hR, H⟩ := HasFPowerSeriesAt.exists_coordinate_box_remainder hP N
  let ρ : ℝ := R / ((d : ℝ) + 1)
  have hd : 0 < (d : ℝ) + 1 := by positivity
  have hρ : 0 < ρ := div_pos hR hd
  refine ⟨ρ, K, hρ, fun p hp => ?_⟩
  let x : Fin d → ℂ := fun i => ((p i - p₀ i : ℝ) : ℂ)
  have hxnorm : ∀ i : Fin d, ‖x i‖ = |p i - p₀ i| := by
    intro i
    exact Complex.norm_real _
  have hx : (∑ i, ‖x i‖) ≤ R := by
    have hsum : (∑ i : Fin d, |p i - p₀ i|) ≤ (d : ℝ) * ρ := by
      calc
        _ ≤ ∑ _i : Fin d, ρ := sum_le_sum fun i _ => hp i
        _ = _ := by simp
    simp_rw [hxnorm]
    apply hsum.trans
    calc
      (d : ℝ) * ρ ≤ ((d : ℝ) + 1) * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ.le
      _ = R := by dsimp [ρ]; field_simp
  have heval : (fun i : Fin d => (p₀ i : ℂ)) + x = fun i : Fin d => (p i : ℂ) := by
    funext i
    simp only [Pi.add_apply, x, ofReal_sub]
    ring
  have hmono (α : Fin d → ℕ) : (∏ i, x i ^ α i) =
      (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) := by
    simp [x, cepsMonomial]
  have ht := H x hx
  rw [heval] at ht
  simp_rw [hmono, hxnorm] at ht
  exact ht

end PGM
