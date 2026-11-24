import PLAStochastic.Index.GEP.StrongApprox.Saddle.ExactTilting
import PLAStochastic.Index.GEP.StrongApprox.Tilt.Recentered
import PLAStochastic.Index.GEP.StrongApprox.Saddle.VariancePrefactor

/-! # WP5: the exact saddle formula for the actual smoothed iid sum -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal

/-- The density of the centered `l`-fold gap sum with independent `N(0,l s²)` noise. -/
def saCenteredSumDensity (ν : ProbabilityMeasure ℝ) (s : ℝ) (l : ℕ) (x : ℝ) : ℝ :=
  saGaussianDensity (convPow ((ν : Measure ℝ).map (fun y => y - 1)) l)
    ((l : ℝ≥0) * Real.toNNReal (s ^ 2)) x

/-- The normalized, recentered tilted sum evaluated at its center. -/
def saTiltedCenterDensity (ν : ProbabilityMeasure ℝ) (s : ℝ) (l : ℕ) (lam : ℝ) : ℝ :=
  saGaussianDensity ((convPow (saRecenteredTilt ν lam) l).map ((Real.sqrt l)⁻¹ * ·))
    (Real.toNNReal (s ^ 2)) 0

theorem sa_cgf_centered_map (ν : ProbabilityMeasure ℝ) (lam : ℝ) :
    cgf id ((ν : Measure ℝ).map (fun y => y - 1)) lam =
      cgf (fun y : ℝ => y - 1) (ν : Measure ℝ) lam := by
  unfold cgf mgf
  rw [integral_map (by fun_prop)
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Real.exp (lam * id x))
      ((ν : Measure ℝ).map (fun y => y - 1)))]
  rfl

theorem sa_recentered_tilt_centered_map (ν : ProbabilityMeasure ℝ) (lam : ℝ) :
    ((((ν : Measure ℝ).map (fun y => y - 1)).tilted (fun y => lam * y)).map
      (fun y => y - deriv (cgf (fun z : ℝ => z - 1) (ν : Measure ℝ)) lam)) =
      saRecenteredTilt ν lam := by
  rw [sa_tilted_map _ _ (by fun_prop), map_map (by fun_prop) (by fun_prop)]
  rfl

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

/-- Exact identity before the local CLT is used: every object is the density of
its specified actual probability law. -/
theorem UnivClass.saCenteredSumDensity_saddle (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {s : ℝ} (hs : 0 < s) {l : ℕ} (hl : 0 < l)
    {w : ℝ} (hw : |w| ≤ saMeanRadius vlo B θ) :
    saCenteredSumDensity ν s l (l * w) =
      Real.exp (-(l : ℝ) * saRate vlo B θ ν s w) / Real.sqrt l *
        saTiltedCenterDensity ν s l (saSaddle vlo B θ ν s w) := by
  let lam := saSaddle vlo B θ ν s w
  have hsaddle := h.saSaddle_spec hvlo hθ s (hw.trans (saMeanRadius_lt_full hvlo hθ).le)
  have hlam : |lam| < θ :=
    ((abs_le.mpr hsaddle.1).trans (saTiltRadius_le_half vlo B hθ)).trans_lt (by linarith)
  let μ := (ν : Measure ℝ).map (fun y => y - 1)
  let : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hM : Integrable (fun y : ℝ => Real.exp (lam * y)) μ := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact h.integrable_exp_centered hlam.le
  have ht := saGaussianDensity_convPow_tilt_at_mean μ hM
    (v := Real.toNNReal (s ^ 2)) (by simp [Real.toNNReal_eq_zero, (sq_pos_of_pos hs).not_ge]) hl
    (deriv (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ)) lam)
  have hm : deriv (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ)) lam + s ^ 2 * lam = w := by
    rw [← h.deriv_saSmoothCGF hlam s]
    exact hsaddle.2
  have hc : cgf id μ lam = cgf (fun y : ℝ => y - 1) (ν : Measure ℝ) lam :=
    sa_cgf_centered_map ν lam
  have hr : (μ.tilted (fun y => lam * y)).map
      (fun y => y - deriv (cgf (fun z : ℝ => z - 1) (ν : Measure ℝ)) lam) =
      saRecenteredTilt ν lam := sa_recentered_tilt_centered_map ν lam
  rw [Real.coe_toNNReal _ (sq_nonneg s), hm, hc, hr] at ht
  have he : (l : ℝ) * (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ) lam +
      s ^ 2 * lam ^ 2 / 2 - lam * w) = -(l : ℝ) * saRate vlo B θ ν s w := by
    unfold saRate saSmoothCGF
    dsimp [lam]
    ring
  rw [he] at ht
  exact ht

end

end PGM
