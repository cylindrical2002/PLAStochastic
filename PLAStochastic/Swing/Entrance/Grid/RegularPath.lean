import PLAStochastic.Swing.Entrance.Grid.Scaling

/-!
# Regular continuous paths for the macroscopic entrance limit

A continuous path `f` with `f 0 = 0` is *entrance regular* with pinch `σ` when its anchored
lifetime at tolerance one equals its first closed-budget hit, both equal to the finite `σ`.
Almost every Brownian path is entrance regular (`EntranceRegular.ae_brownian`); the
deterministic grid limits are proved for every entrance-regular path.

For such a path the Brownian first pinch of the entrance law is `entrancePinch f = σ > 0`, the
continuous cone at `σ` is the singleton `{entranceSlope f}`, that slope fits `f` on `[0, σ]`
within one, the terminal residual sign `entranceSign f` is `±1`, and the anchored error stays
strictly below one before `σ`.
-/

open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair

noncomputable section

/-- The pathwise regularity used by the grid limits of the entrance law. -/
structure EntranceRegular (f : C(ℝ, ℝ)) (σ : ℝ≥0) : Prop where
  zero : f 0 = 0
  lifetime : anchoredLifetime f 1 = σ
  reach : firstReach (fun t : ℝ≥0 => anchoredTimeError f t) 1 = σ

theorem offsetPath_zero_eq (f : C(ℝ, ℝ)) : offsetPath f 0 = f := by
  ext t
  simp

namespace EntranceRegular

variable {f : C(ℝ, ℝ)} {σ : ℝ≥0} (hr : EntranceRegular f σ)
include hr

theorem pos : 0 < σ := by
  have h := anchoredLifetime_pos f hr.zero zero_lt_one
  rw [hr.lifetime] at h
  exact ENNReal.coe_pos.mp h

theorem pos_real : 0 < (σ : ℝ) := by exact_mod_cast hr.pos

theorem abs_zero_lt : |f 0 - 0| < 1 := by simp [hr.zero]

theorem reach_offset :
    firstReach (fun t : ℝ≥0 => anchoredTimeError (offsetPath f 0) t) 1 = σ := by
  rw [offsetPath_zero_eq]
  exact hr.reach

theorem pinch_eq : entrancePinch f = σ := by
  unfold entrancePinch
  rw [firstContinuousConePinch_eq_firstReach f hr.abs_zero_lt hr.pos hr.reach_offset]
  rfl

/-- The anchored error stays strictly below one before the pinch. -/
theorem error_lt {T : ℝ≥0} (hT : T < σ) : anchoredTimeError f T < 1 := by
  by_contra h
  have hle := firstReach_le_of_reaches (D := fun t : ℝ≥0 => anchoredTimeError f t)
    (le_of_not_gt h)
  rw [hr.reach] at hle
  exact hT.not_ge (ENNReal.coe_le_coe.mp hle)

theorem lowerSlope_eq : continuousLowerSlope f 0 1 σ = entranceSlope f := by
  rw [entranceSlope, hr.pinch_eq]

theorem upperSlope_eq : continuousUpperSlope f 0 1 σ = entranceSlope f := by
  rw [← hr.lowerSlope_eq]
  exact (continuousCone_eq_at_firstReach f hr.abs_zero_lt hr.pos hr.reach_offset).symm

/-- The pinch slope fits the path within one on `[0, σ]`. -/
theorem slope_fit : ∀ t : Icc (0 : ℝ) (σ : ℝ), |f t - entranceSlope f * (t : ℝ)| ≤ 1 := by
  obtain ⟨a, ha⟩ := (le_anchoredLifetime_iff_exists_fit f hr.zero zero_le_one σ).mp
    hr.lifetime.ge
  have hfeas : continuousSlopeFeasible f 0 1 σ a := fun t => by
    simpa only [sub_zero] using ha t
  have hmem := (continuousSlopeFeasible_iff_mem_Icc hr.pos_real ⟨a, hfeas⟩
    (entranceSlope f)).mpr ⟨hr.lowerSlope_eq.le, hr.upperSlope_eq.ge⟩
  intro t
  simpa only [sub_zero] using hmem t

theorem sign_eq : entranceSign f = f σ - entranceSlope f * σ := by
  rw [entranceSign, hr.pinch_eq]

theorem abs_sign : |entranceSign f| = 1 := by
  rw [hr.sign_eq]
  have h := anchored_fit_terminal_boundary f (by simp [hr.zero]) hr.lifetime hr.slope_fit
  exact h

theorem sign_eq_one_or : entranceSign f = 1 ∨ entranceSign f = -1 := by
  rcases abs_eq (zero_le_one' ℝ) |>.mp hr.abs_sign with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem area_eq : entranceArea f =
    entranceSign f * ((∫ t in (0 : ℝ)..σ, t * f t) - entranceSlope f * (σ ^ 3 / 3 : ℝ)) := by
  rw [entranceArea, hr.pinch_eq]
  congr 1
  have h1 : IntervalIntegrable (fun t : ℝ => t * f t) volume 0 σ :=
    (continuous_id.mul f.continuous).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => entranceSlope f * t ^ 2) volume 0 σ :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  have hint : (∫ t in (0 : ℝ)..σ, t * (f t - entranceSlope f * t)) =
      ∫ t in (0 : ℝ)..σ, (t * f t - entranceSlope f * t ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    ring
  rw [hint, intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    integral_pow]
  norm_num

end EntranceRegular

/-- Almost every Brownian path is entrance regular. -/
theorem EntranceRegular.ae_brownian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Continuous (B · ω) ∧ B 0 ω = 0 ∧
      ∃ σ : ℝ≥0, EntranceRegular (processPath B ω) σ := by
  have hη : |(0 : ℝ)| < 1 := by simp
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero, continuousBrownianPath_ae_eq hB,
    brownianOffsetPinch_ae_ne_top hB hη, brownianOffsetPinch_ae_eq_lifetime hB hη]
    with ω hc hz hp hf heq
  refine ⟨hc, hz, ?_⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ≥0, brownianOffsetPinch hB 0 1 ω = (σ : ℝ≥0∞) :=
    ⟨(brownianOffsetPinch hB 0 1 ω).toNNReal, (ENNReal.coe_toNNReal hf).symm⟩
  have hzero : processPath B ω 0 = 0 := (processPath_apply_of_continuous hc 0).trans hz
  refine ⟨σ, hzero, ?_, ?_⟩
  · have h := heq.symm.trans hσ
    simpa only [offsetProcessLifetime, offsetPath_zero_eq] using h
  · have h := hσ
    simpa only [brownianOffsetPinch, hp, offsetPath_zero_eq] using h

end

end SwingRepair
