import PLAStochastic.Swing.Entrance.Brownian.BumpInvariance

/-!
# Measurability of the Brownian entrance quantities

On the Borel path space `C(ℝ, ℝ)` we define measurable functionals `pinchM`, `slopeM`, `signM` and
`areaM`. They coincide with `entrancePinch`, `entranceSlope`, `entranceSign` and `entranceArea` on
every path with `|f 0| < 1`:

* the pinch is the first time the anchored error reaches `1`, a hitting time of a family of
  continuous functionals with closed sublevel events;
* the cone endpoint `sup_{0 < t ≤ T} (f t - 1)/t` is the same supremum over the rational times
  `t = q T`, `q ∈ (0, 1] ∩ ℚ`, which is jointly measurable in the path and the horizon;
* the area integral is jointly continuous in the path, the slope and the horizon.

Since a Brownian path starts at `0` almost surely, the four quantities of `processPath B` are
almost everywhere measurable. Almost surely the pinch is finite and positive, the sign is `±1`,
and `m_*` is the unique feasible slope at the pinch.
-/

open MeasureTheory ProbabilityTheory Set Filter BrownianAffine
open scoped ENNReal NNReal Topology

namespace SwingRepair

noncomputable section

/-! ## The pinch -/

theorem continuous_anchoredTimeError_path (T : ℝ) :
    Continuous (fun f : C(ℝ, ℝ) => anchoredTimeError f T) :=
  (continuous_anchoredError 1).comp (continuous_unitPath_in_path T)

theorem measurable_entranceReach : Measurable entranceReach := by
  apply measurable_of_Iic
  intro x
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe T =>
    have h : entranceReach ⁻¹' Iic (T : ℝ≥0∞) = {f | 1 ≤ anchoredTimeError f T} := by
      ext f
      exact entranceReach_le_iff f T
    rw [h]
    exact measurableSet_le measurable_const (continuous_anchoredTimeError_path T).measurable

/-- Measurable version of the pinch. -/
def pinchM (f : C(ℝ, ℝ)) : ℝ := (entranceReach f).toReal

theorem measurable_pinchM : Measurable pinchM :=
  ENNReal.measurable_toReal.comp measurable_entranceReach

theorem entrancePinch_eq_pinchM {f : C(ℝ, ℝ)} (hf : |f 0| < 1) :
    entrancePinch f = pinchM f := by
  rw [entrancePinch, firstContinuousConePinch_eq_entranceReach hf, pinchM]

theorem entrancePinch_nonneg (f : C(ℝ, ℝ)) : 0 ≤ entrancePinch f := ENNReal.toReal_nonneg

/-! ## The cone endpoint on rational times -/

/-- Rational times in `(0, 1]`. -/
abbrev UnitRat := {q : ℚ // 0 < q ∧ q ≤ 1}

instance : Nonempty UnitRat := ⟨⟨1, one_pos, le_rfl⟩⟩

/-- The lower cone endpoint computed on the times `q T`, `q ∈ (0, 1] ∩ ℚ`. -/
def lowerSlopeQ (f : C(ℝ, ℝ)) (T : ℝ) : ℝ :=
  ⨆ q : UnitRat, (f ((q : ℝ) * T) - 0 - 1) / ((q : ℝ) * T)

theorem continuousLowerSlope_eq_lowerSlopeQ (f : C(ℝ, ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    continuousLowerSlope f 0 1 T = lowerSlopeQ f T := by
  rcases hT.eq_or_lt with h | h
  · subst h
    have hE : IsEmpty (Ioc (0 : ℝ) 0) := ⟨fun t => lt_irrefl _ (t.2.1.trans_le t.2.2)⟩
    rw [continuousLowerSlope, Set.range_eq_empty, Real.sSup_empty]
    simp [lowerSlopeQ]
  · let φ : UnitRat → Ioc (0 : ℝ) T := fun q =>
      ⟨(q : ℝ) * T, mul_pos (by exact_mod_cast q.2.1) h,
        mul_le_of_le_one_left h.le (by exact_mod_cast q.2.2)⟩
    have hdense : DenseRange φ := by
      rw [Metric.denseRange_iff]
      intro x ε hε
      have hx0 : 0 < (x : ℝ) / T := div_pos x.2.1 h
      have hx1 : (x : ℝ) / T ≤ 1 := (div_le_one h).mpr x.2.2
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
        (max_lt hx0 (by linarith [div_pos hε h] : (x : ℝ) / T - ε / T < (x : ℝ) / T))
      have hq0 : (0 : ℝ) < q := (le_max_left _ _).trans_lt hq1
      have hqε : (x : ℝ) / T - ε / T < q := (le_max_right _ _).trans_lt hq1
      refine ⟨⟨q, by exact_mod_cast hq0, by exact_mod_cast (hq2.le.trans hx1)⟩, ?_⟩
      rw [Subtype.dist_eq, Real.dist_eq]
      change |(x : ℝ) - (q : ℝ) * T| < ε
      have h1 : (q : ℝ) * T < x := by
        have := mul_lt_mul_of_pos_right hq2 h
        rwa [div_mul_cancel₀ _ h.ne'] at this
      have h2 : (x : ℝ) - ε < (q : ℝ) * T := by
        have := mul_lt_mul_of_pos_right hqε h
        rwa [sub_mul, div_mul_cancel₀ _ h.ne', div_mul_cancel₀ _ h.ne'] at this
      rw [abs_lt]
      constructor <;> linarith
    have hcont : Continuous (fun t : Ioc (0 : ℝ) T => (f t - 0 - 1) / (t : ℝ)) :=
      ((f.continuous.comp continuous_subtype_val).sub continuous_const).sub continuous_const
        |>.div continuous_subtype_val (fun t => t.2.1.ne')
    have h1 := hdense.ciSup' hcont
    rw [iSup_range' (fun t : Ioc (0 : ℝ) T => (f t - 0 - 1) / (t : ℝ)) φ] at h1
    exact h1.symm

/-- Measurable version of the slope. -/
def slopeM (f : C(ℝ, ℝ)) : ℝ := lowerSlopeQ f (pinchM f)

theorem measurable_eval_at {τ : C(ℝ, ℝ) → ℝ} (hτ : Measurable τ) :
    Measurable (fun f : C(ℝ, ℝ) => f (τ f)) :=
  continuous_eval.measurable.comp (measurable_id.prodMk hτ)

theorem measurable_slopeM : Measurable slopeM := by
  apply Measurable.iSup
  intro q
  have hτ : Measurable (fun f : C(ℝ, ℝ) => (q : ℝ) * pinchM f) :=
    measurable_const.mul measurable_pinchM
  exact (((measurable_eval_at hτ).sub measurable_const).sub measurable_const).div hτ

theorem entranceSlope_eq_lowerSlopeQ (f : C(ℝ, ℝ)) :
    entranceSlope f = lowerSlopeQ f (entrancePinch f) :=
  continuousLowerSlope_eq_lowerSlopeQ f (entrancePinch_nonneg f)

theorem entranceSlope_eq_slopeM {f : C(ℝ, ℝ)} (hf : |f 0| < 1) :
    entranceSlope f = slopeM f := by
  rw [entranceSlope_eq_lowerSlopeQ, entrancePinch_eq_pinchM hf, slopeM]

/-! ## Sign and area -/

/-- Measurable version of the sign. -/
def signM (f : C(ℝ, ℝ)) : ℝ := f (pinchM f) - slopeM f * pinchM f

theorem measurable_signM : Measurable signM :=
  (measurable_eval_at measurable_pinchM).sub (measurable_slopeM.mul measurable_pinchM)

theorem entranceSign_eq_signM {f : C(ℝ, ℝ)} (hf : |f 0| < 1) :
    entranceSign f = signM f := by
  rw [entranceSign, entranceSlope_eq_slopeM hf, entrancePinch_eq_pinchM hf, signM]

/-- Measurable version of the area. -/
def areaM (f : C(ℝ, ℝ)) : ℝ :=
  signM f * ∫ t in (0 : ℝ)..pinchM f, t * (f t - slopeM f * t)

theorem continuous_areaIntegral :
    Continuous (fun p : (C(ℝ, ℝ) × ℝ) × ℝ =>
      ∫ t in (0 : ℝ)..p.2, t * (p.1.1 t - p.1.2 * t)) := by
  apply intervalIntegral.continuous_parametric_primitive_of_continuous
    (f := fun (p : C(ℝ, ℝ) × ℝ) (t : ℝ) => t * (p.1 t - p.2 * t))
  have he : Continuous (fun q : (C(ℝ, ℝ) × ℝ) × ℝ => q.1.1 q.2) :=
    continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  exact continuous_snd.mul (he.sub ((continuous_snd.comp continuous_fst).mul continuous_snd))

theorem measurable_areaM : Measurable areaM := by
  have h : Measurable (fun f : C(ℝ, ℝ) =>
      ∫ t in (0 : ℝ)..pinchM f, t * (f t - slopeM f * t)) :=
    continuous_areaIntegral.measurable.comp
      ((measurable_id.prodMk measurable_slopeM).prodMk measurable_pinchM)
  exact measurable_signM.mul h

theorem entranceArea_eq_areaM {f : C(ℝ, ℝ)} (hf : |f 0| < 1) :
    entranceArea f = areaM f := by
  rw [entranceArea, entranceSign_eq_signM hf, entranceSlope_eq_slopeM hf,
    entrancePinch_eq_pinchM hf, areaM]

/-! ## Brownian paths -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem processPath_abs_zero_lt_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, |processPath B ω 0| < 1 := by
  filter_upwards [processPath_zero_ae hB] with ω hω
  simp only [Pi.zero_apply] at hω
  rw [hω, abs_zero]
  exact one_pos

theorem aemeasurable_entranceArea (hB : IsBrownianReal B μ) :
    AEMeasurable (fun ω => entranceArea (processPath B ω)) μ :=
  (measurable_areaM.comp_aemeasurable (aemeasurable_processPath hB)).congr (by
    filter_upwards [processPath_abs_zero_lt_ae hB] with ω hω
    exact (entranceArea_eq_areaM hω).symm)

/-- Almost surely the literal `ℝ≥0∞` pinch is finite and positive, so `0 < σ < ∞`. -/
theorem entrancePinch_finite_pos_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, 0 < firstContinuousConePinch (processPath B ω) 0 1 ∧
      firstContinuousConePinch (processPath B ω) 0 1 < ⊤ ∧
      0 < entrancePinch (processPath B ω) := by
  have hη : |(0 : ℝ)| < 1 := by simp
  filter_upwards [firstContinuousConePinch_ae_eq_offsetLifetime hB hη,
    offsetProcessLifetime_ae_ne_top hB hη, offsetProcessLifetime_ae_pos hB hη]
    with ω heq hne hpos
  rw [entrancePinch, heq]
  exact ⟨hpos, lt_top_iff_ne_top.mpr hne, ENNReal.toReal_pos hpos.ne' hne⟩

theorem entrancePinch_pos_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, 0 < entrancePinch (processPath B ω) := by
  filter_upwards [entrancePinch_finite_pos_ae hB] with ω hω
  exact hω.2.2

end

end SwingRepair
