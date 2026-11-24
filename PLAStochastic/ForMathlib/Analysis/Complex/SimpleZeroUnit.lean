import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import Mathlib.Analysis.Complex.Schwarz

/-! # Uniform holomorphic units after removing a normalized simple zero -/

noncomputable section
open Complex Set Metric
namespace PGM

def simpleZeroUnitRadius (R M : ℝ) : ℝ := min (R / 2) (R ^ 2 / (8 * M))

theorem simpleZeroUnitRadius_pos {R M : ℝ} (hR : 0 < R) (hM : 0 < M) :
    0 < simpleZeroUnitRadius R M := by
  unfold simpleZeroUnitRadius
  positivity

theorem simpleZeroUnit_budget {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hf0 : f 0 = 0) (hdf : deriv f 0 = 1)
    (hbound : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) :
    DifferentiableOn ℂ (dslope f 0) (ball 0 R) ∧
    (∀ z ∈ ball (0 : ℂ) R, ‖dslope f 0 z‖ ≤ M / R) ∧
    (∀ z ∈ ball (0 : ℂ) (simpleZeroUnitRadius R M), ‖dslope f 0 z - 1‖ ≤ 1 / 2) := by
  have hd : DifferentiableOn ℂ (dslope f 0) (ball 0 R) :=
    (differentiableOn_dslope (ball_mem_nhds 0 hR)).mpr hf
  have hb : ∀ z ∈ ball (0 : ℂ) R, ‖dslope f 0 z‖ ≤ M / R := by
    intro z hz
    exact norm_dslope_le_div_of_mapsTo_ball hf
      (fun w hw => by simpa only [mem_closedBall, hf0, dist_zero_right] using hbound w hw) hz
  refine ⟨hd, hb, fun z hz => ?_⟩
  have hzR : z ∈ ball (0 : ℂ) (R / 2) :=
    ball_subset_ball (min_le_left _ _) hz
  have ht := norm_sub_le_of_ball_half hR hd hb hzR (mem_ball_self (half_pos hR))
  rw [dslope_same, hdf, sub_zero] at ht
  calc
    ‖dslope f 0 z - 1‖ ≤ 4 * (M / R) / R * ‖z‖ := ht
    _ = 4 * M * ‖z‖ / R ^ 2 := by field_simp
    _ ≤ 1 / 2 := by
      have hn : ‖z‖ ≤ R ^ 2 / (8 * M) :=
        (mem_ball_zero_iff.mp hz).le.trans (min_le_right _ _)
      have hn' := (le_div_iff₀ (by positivity : 0 < 8 * M)).mp hn
      rw [div_le_iff₀ (sq_pos_of_pos hR)]
      linarith

theorem simpleZeroUnit_inverse_budget {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hf0 : f 0 = 0) (hdf : deriv f 0 = 1)
    (hbound : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) :
    DifferentiableOn ℂ (fun z => (dslope f 0 z)⁻¹) (ball 0 (simpleZeroUnitRadius R M)) ∧
    ∀ z ∈ ball (0 : ℂ) (simpleZeroUnitRadius R M),
      1 / 2 ≤ ‖dslope f 0 z‖ ∧ ‖(dslope f 0 z)⁻¹‖ ≤ 2 := by
  obtain ⟨hd, _, hc⟩ := simpleZeroUnit_budget hR hM hf hf0 hdf hbound
  have hl : ∀ z ∈ ball (0 : ℂ) (simpleZeroUnitRadius R M), 1 / 2 ≤ ‖dslope f 0 z‖ := by
    intro z hz
    have hn := norm_sub_norm_le (1 : ℂ) (dslope f 0 z)
    rw [norm_one, norm_sub_rev] at hn
    linarith [hc z hz]
  have hz : ∀ z ∈ ball (0 : ℂ) (simpleZeroUnitRadius R M), dslope f 0 z ≠ 0 := by
    intro z hz
    exact norm_pos_iff.mp (by linarith [hl z hz])
  refine ⟨(hd.mono (ball_subset_ball ((min_le_left _ _).trans (half_le_self hR.le)))).inv hz,
    fun z hzb => ⟨hl z hzb, ?_⟩⟩
  rw [norm_inv]
  calc ‖dslope f 0 z‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
      (inv_le_inv₀ (by linarith [hl z hzb]) (by norm_num)).mpr (hl z hzb)
    _ = 2 := by norm_num

end PGM
