import PLAStochastic.Brownian.Hitting.DriftedSuprema
import PLAStochastic.Affine.Error.Attainment
import PLAStochastic.ForMathlib.Probability.FirstExceedance.PositiveSublevelLaw
import PLAStochastic.Affine.Lifetime.InverseErrorLaw

/-!
# The exact expanding-strip event after time inversion

Attainment includes the boundary of the fitting event. Supremum values remain
extended nonnegative reals, so no separate finiteness assumption is needed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

/-- The expanding strip has a common intercept exactly when its two drifted
suprema have sum at most twice the tolerance. -/
theorem expandingStrip_iff_driftedSum {X : ℝ≥0 → ℝ} (h0 : X 0 = 0)
    {e : ℝ} (he : 0 ≤ e) :
    (∃ a : ℝ, ∀ u : ℝ≥0, |X u - a| ≤ e * (1 + (u : ℝ))) ↔
      driftedSum X e ≤ ENNReal.ofReal (2 * e) := by
  constructor
  · rintro ⟨a, ha⟩
    have ha0 := ha 0
    simp only [NNReal.coe_zero, add_zero, mul_one, h0, zero_sub, abs_neg] at ha0
    have hal : 0 ≤ a + e := by have := (abs_le.mp ha0).1; linarith
    have har : 0 ≤ e - a := by have := (abs_le.mp ha0).2; linarith
    have hA : driftedSup X e ≤ ENNReal.ofReal (a + e) := by
      apply iSup_le
      intro u
      apply ENNReal.ofReal_le_ofReal
      have := (abs_le.mp (ha u)).2
      linarith
    have hC : driftedSup (fun u => -X u) e ≤ ENNReal.ofReal (e - a) := by
      apply iSup_le
      intro u
      apply ENNReal.ofReal_le_ofReal
      have := (abs_le.mp (ha u)).1
      linarith
    calc
      driftedSum X e ≤ ENNReal.ofReal (a + e) + ENNReal.ofReal (e - a) :=
        add_le_add hA hC
      _ = ENNReal.ofReal (2 * e) := by rw [← ENNReal.ofReal_add hal har]; congr 1; ring
  · intro h
    let A := driftedSup X e
    let C := driftedSup (fun u => -X u) e
    have hsum : A + C ≤ ENNReal.ofReal (2 * e) := h
    have hA : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((le_add_right le_rfl).trans hsum)
    have hC : C ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((le_add_left le_rfl).trans hsum)
    have hreal : A.toReal + C.toReal ≤ 2 * e := by
      have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
      simpa only [ENNReal.toReal_add hA hC,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * e)] using hr
    refine ⟨A.toReal - e, fun u => abs_le.mpr ⟨?_, ?_⟩⟩
    · have hc : -X u - e * (u : ℝ) ≤ C.toReal :=
        (ENNReal.ofReal_le_iff_le_toReal hC).mp (le_iSup (fun u : ℝ≥0 =>
          ENNReal.ofReal (-X u - e * (u : ℝ))) u)
      linarith
    · have ha : X u - e * (u : ℝ) ≤ A.toReal :=
        (ENNReal.ofReal_le_iff_le_toReal hA).mp (le_iSup (fun u : ℝ≥0 =>
          ENNReal.ofReal (X u - e * (u : ℝ))) u)
      linarith

def unitAnchoredFeasible (X : ℝ≥0 → ℝ) (e : ℝ) : Prop :=
  ∃ a : ℝ, ∀ t : ℝ≥0, t ≤ 1 → |X t - a * (t : ℝ)| ≤ e

def invertedPath (X : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  (s : ℝ) * X (1 / s)

theorem invertedPath_residual (X : ℝ≥0 → ℝ) (a : ℝ) {s : ℝ≥0} (hs : s ≠ 0) :
    |invertedPath X s - a| =
      (s : ℝ) * |X (1 / s) - a * ((1 / s : ℝ≥0) : ℝ)| := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs
  have heq : invertedPath X s - a =
      (s : ℝ) * (X (1 / s) - a * ((1 / s : ℝ≥0) : ℝ)) := by
    simp only [invertedPath, NNReal.coe_div, NNReal.coe_one]
    field_simp
  rw [heq, abs_mul]
  simp

/-- The unit interval's slope constraints become intervals at all reciprocal
times at least one, with the zero endpoint handled separately. -/
theorem unitAnchoredFeasible_iff_invertedStrip {X : ℝ≥0 → ℝ} (h0 : X 0 = 0)
    {e : ℝ} (he : 0 ≤ e) :
    unitAnchoredFeasible X e ↔
      ∃ a : ℝ, ∀ s : ℝ≥0, 1 ≤ s → |invertedPath X s - a| ≤ e * (s : ℝ) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun s hs => ?_⟩
    have hspos : 0 < s := zero_lt_one.trans_le hs
    rw [invertedPath_residual X a hspos.ne']
    have hh := ha (1 / s) ((div_le_one₀ hspos).mpr hs)
    nlinarith [mul_le_mul_of_nonneg_left hh s.property]
  · rintro ⟨a, ha⟩
    refine ⟨a, fun t ht => ?_⟩
    by_cases ht0 : t = 0
    · simpa [ht0, h0] using he
    · have htpos : 0 < t := pos_of_ne_zero ht0
      have hspos : 0 < 1 / t := one_div_pos.mpr htpos
      have hh := ha (1 / t) ((one_le_div₀ htpos).mpr ht)
      rw [invertedPath_residual X a hspos.ne'] at hh
      simp only [one_div_one_div] at hh
      have hsR : 0 < ((1 / t : ℝ≥0) : ℝ) := by exact_mod_cast hspos
      nlinarith

/-- Subtracting the value at time one translates the common intercept. -/
theorem invertedStrip_iff_shiftedStrip (Y : ℝ≥0 → ℝ) (e : ℝ) :
    (∃ a : ℝ, ∀ s : ℝ≥0, 1 ≤ s → |Y s - a| ≤ e * (s : ℝ)) ↔
      ∃ a : ℝ, ∀ u : ℝ≥0,
        |(Y (1 + u) - Y 1) - a| ≤ e * (1 + (u : ℝ)) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a - Y 1, fun u => ?_⟩
    have h := ha (1 + u) (le_add_right le_rfl)
    simpa only [NNReal.coe_add, NNReal.coe_one, sub_sub_sub_cancel_right] using h
  · rintro ⟨a, ha⟩
    refine ⟨a + Y 1, fun s hs => ?_⟩
    have h := ha (s - 1)
    have heq : 1 + (s - 1) = s := add_tsub_cancel_of_le hs
    have heqR : 1 + ((s - 1 : ℝ≥0) : ℝ) = (s : ℝ) := by
      exact_mod_cast heq
    rw [heq, heqR] at h
    convert h using 1
    congr 1
    ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The future increments after time one of the inverted process. -/
def invertedIncrementProcess (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  timeInvertedProcess B (1 + u) ω - timeInvertedProcess B 1 ω

theorem isBrownianReal_invertedIncrement (hB : IsBrownianReal B μ) :
    IsBrownianReal (invertedIncrementProcess B) μ :=
  (isBrownianReal_timeInversion hB).shift 1

omit [MeasurableSpace Ω] in
theorem anchoredProcessError_le_iff_unitAnchoredFeasible {ω : Ω}
    (hω : Continuous (B · ω)) (e : ℝ) :
    anchoredProcessError B 1 ω ≤ e ↔ unitAnchoredFeasible (B · ω) e := by
  change anchoredError (unitPath (processPath B ω) 1) ≤ e ↔ _
  rw [anchoredError_le_iff_exists_fit (by norm_num : (0 : ℝ) ≤ 1)]
  have hun (t : Set.Icc (0 : ℝ) 1) : unitPath (processPath B ω) 1 t =
      B ⟨t.1, t.property.1⟩ ω := by
    simpa only [NNReal.coe_one, one_mul] using unitPath_processPath_apply hω (1 : ℝ≥0) t
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun t ht => ?_⟩
    have h := ha ⟨(t : ℝ), t.property, by exact_mod_cast ht⟩
    rw [hun] at h
    exact h
  · rintro ⟨a, ha⟩
    refine ⟨a, fun t => ?_⟩
    have h := ha (⟨t.1, t.property.1⟩ : ℝ≥0) (by exact_mod_cast t.property.2)
    rw [hun]
    exact h

/-- The exact closed fitting event is an expanding-strip event for one genuine
Brownian motion, the shifted time inversion. -/
theorem anchoredProcessError_le_iff_driftedSum_ae (hB : IsBrownianReal B μ)
    {e : ℝ} (he : 0 ≤ e) :
    ∀ᵐ ω ∂μ, anchoredProcessError B 1 ω ≤ e ↔
      driftedSum (invertedIncrementProcess B · ω) e ≤ ENNReal.ofReal (2 * e) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hω h0
  rw [anchoredProcessError_le_iff_unitAnchoredFeasible hω,
    unitAnchoredFeasible_iff_invertedStrip h0 he,
    invertedStrip_iff_shiftedStrip,
    expandingStrip_iff_driftedSum (by simp) he]
  rfl

/-- Brownian scaling is applied to the sum of the two dependent suprema.
This is the exact positive-threshold CDF identity from the manuscript. -/
theorem anchoredProcessError_sublevel_driftedSum (hB : IsBrownianReal B μ)
    {e : ℝ} (he : 0 < e) :
    μ {ω | anchoredProcessError B 1 ω ≤ e} =
      μ {ω | driftedSum (B · ω) 1 ≤ ENNReal.ofReal (2 * e ^ 2)} := by
  let a : ℝ≥0 := ⟨e, he.le⟩
  have ha : a ≠ 0 := by
    intro h
    have hv := congrArg (fun u : ℝ≥0 => (u : ℝ)) h
    change e = 0 at hv
    exact he.ne' hv
  have hscale : ENNReal.ofReal e * ENNReal.ofReal (2 * e) =
      ENNReal.ofReal (2 * e ^ 2) := by
    rw [← ENNReal.ofReal_mul he.le]
    congr 1
    ring
  calc
    μ {ω | anchoredProcessError B 1 ω ≤ e} =
        μ {ω | driftedSum (invertedIncrementProcess B · ω) e ≤ ENNReal.ofReal (2 * e)} := by
      apply measure_congr
      filter_upwards [anchoredProcessError_le_iff_driftedSum_ae hB he.le] with ω hω
      exact propext hω
    _ = μ {ω | driftedSum (B · ω) e ≤ ENNReal.ofReal (2 * e)} :=
      (identDistrib_driftedSum (isBrownianReal_invertedIncrement hB) hB e).measure_mem_eq
        measurableSet_Iic
    _ = μ {ω | ENNReal.ofReal e * driftedSum (B · ω) e ≤
        ENNReal.ofReal (2 * e ^ 2)} := by
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [← hscale, ENNReal.mul_le_mul_iff_right
        (ne_of_gt (ENNReal.ofReal_pos.mpr he)) ENNReal.ofReal_ne_top]
    _ = μ {ω | driftedSum (B · ω) 1 ≤ ENNReal.ofReal (2 * e ^ 2)} :=
      (identDistrib_scaled_driftedSum hB ha).measure_mem_eq measurableSet_Iic

/-- Twice the squared actual fitting error has the law of the two dependent
unit-drift suprema. Infinity is retained in the target until this law is proved. -/
theorem identDistrib_two_sq_anchoredError_driftedSum (hB : IsBrownianReal B μ) :
    IdentDistrib (fun ω => ENNReal.ofReal (2 * (anchoredProcessError B 1 ω) ^ 2))
      (fun ω => driftedSum (B · ω) 1) μ μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply identDistrib_of_positive_nnreal_sublevels
    ((by fun_prop : Measurable (fun d : ℝ => ENNReal.ofReal (2 * d ^ 2))).comp_aemeasurable
      (aemeasurable_anchoredProcessError hB 1))
    (aemeasurable_driftedSum hB 1)
  intro r hr
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast pos_of_ne_zero hr
  let e := Real.sqrt ((r : ℝ) / 2)
  have he : 0 < e := Real.sqrt_pos.mpr (by positivity)
  have hs : 2 * e ^ 2 = (r : ℝ) := by
    have h := Real.sq_sqrt (by positivity : 0 ≤ (r : ℝ) / 2)
    dsimp only [e]
    nlinarith
  calc
    μ {ω | ENNReal.ofReal (2 * (anchoredProcessError B 1 ω) ^ 2) ≤ (r : ℝ≥0∞)} =
        μ {ω | anchoredProcessError B 1 ω ≤ e} := by
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [← ENNReal.ofReal_coe_nnreal]
      apply (ENNReal.ofReal_le_ofReal_iff (p := 2 * (anchoredProcessError B 1 ω) ^ 2)
        r.property).trans
      have hd := anchoredTimeError_nonneg (processPath B ω) 1
      change 0 ≤ anchoredProcessError B 1 ω at hd
      have hsq := sq_le_sq₀ hd he.le
      have hrepl : (2 * (anchoredProcessError B 1 ω) ^ 2 ≤ (r : ℝ)) ↔
          (2 * (anchoredProcessError B 1 ω) ^ 2 ≤ 2 * e ^ 2) :=
        ⟨fun h => h.trans_eq hs.symm, fun h => h.trans_eq hs⟩
      exact hrepl.trans ((mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)).trans hsq)
    _ = μ {ω | driftedSum (B · ω) 1 ≤ (r : ℝ≥0∞)} := by
      simpa only [hs, ENNReal.ofReal_coe_nnreal] using
        anchoredProcessError_sublevel_driftedSum hB he

/-- The first inverse-sum identity, formulated in extended nonnegative reals. -/
theorem identDistrib_sq_anchoredError_half_driftedSum (hB : IsBrownianReal B μ) :
    IdentDistrib (fun ω => (ENNReal.ofReal (anchoredProcessError B 1 ω)) ^ 2)
      (fun ω => driftedSum (B · ω) 1 / 2) μ μ := by
  have h := (identDistrib_two_sq_anchoredError_driftedSum hB).comp
    (by fun_prop : Measurable (fun x : ℝ≥0∞ => x / 2))
  convert h using 1
  · funext ω
    change (ENNReal.ofReal (anchoredProcessError B 1 ω)) ^ 2 =
      ENNReal.ofReal (2 * (anchoredProcessError B 1 ω) ^ 2) / 2
    have hd : 0 ≤ anchoredProcessError B 1 ω := anchoredTimeError_nonneg (processPath B ω) 1
    calc
      (ENNReal.ofReal (anchoredProcessError B 1 ω)) ^ 2 =
          ENNReal.ofReal ((anchoredProcessError B 1 ω) ^ 2) := (ENNReal.ofReal_pow hd 2).symm
      _ = ENNReal.ofReal ((2 * (anchoredProcessError B 1 ω) ^ 2) / 2) := by congr 1; ring
      _ = ENNReal.ofReal (2 * (anchoredProcessError B 1 ω) ^ 2) / ENNReal.ofReal (2 : ℝ) :=
        ENNReal.ofReal_div_of_pos (by norm_num)
      _ = _ := by norm_num
  · rfl

/-- The second inverse-sum identity, including all possible zero/infinite values. -/
theorem identDistrib_anchoredLifetime_two_div_driftedSum (hB : IsBrownianReal B μ) :
    IdentDistrib (anchoredProcessLifetime B 1)
      (fun ω => 2 / driftedSum (B · ω) 1) μ μ := by
  have h := (identDistrib_sq_anchoredError_half_driftedSum hB).comp
    (by fun_prop : Measurable (fun x : ℝ≥0∞ => x⁻¹))
  have ht := (identDistrib_anchoredLifetime_unit hB).trans h
  convert ht using 1
  funext ω
  exact (ENNReal.inv_div (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))).symm

/-- Finiteness of the drifted sum follows from the proved distribution identity,
without invoking a separate one-sided hitting formula. -/
theorem driftedSum_ne_top_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, driftedSum (B · ω) 1 ≠ ⊤ := by
  apply (identDistrib_two_sq_anchoredError_driftedSum hB).ae_snd (p := fun x => x ≠ ⊤)
    (measurableSet_singleton (⊤ : ℝ≥0∞)).compl
  exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_ne_top)

theorem driftedPair_ne_top_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, driftedSup (B · ω) 1 ≠ ⊤ ∧ driftedSup (fun u => -B u ω) 1 ≠ ⊤ := by
  filter_upwards [driftedSum_ne_top_ae hB] with ω hω
  exact ENNReal.add_ne_top.mp hω

theorem driftedSum_toReal_ae (hB : IsBrownianReal B μ) :
    (fun ω => (driftedSum (B · ω) 1).toReal) =ᵐ[μ]
      (fun ω => realDriftedSum (B · ω) 1) := by
  filter_upwards [hB.eval_zero_ae_eq_zero, driftedPair_ne_top_ae hB] with ω h0 hfin
  exact driftedSum_toReal_eq_realDriftedSum h0 hfin.1 hfin.2

theorem aemeasurable_realDriftedSum (hB : IsBrownianReal B μ) :
    AEMeasurable (fun ω => realDriftedSum (B · ω) 1) μ :=
  (aemeasurable_driftedSum hB 1).ennreal_toReal.congr (driftedSum_toReal_ae hB)

/-- The manuscript's first identity with its literal real-valued suprema. -/
theorem identDistrib_sq_anchoredError_half_realDriftedSum (hB : IsBrownianReal B μ) :
    IdentDistrib (fun ω => (anchoredProcessError B 1 ω) ^ 2)
      (fun ω => realDriftedSum (B · ω) 1 / 2) μ μ := by
  have h := (identDistrib_sq_anchoredError_half_driftedSum hB).comp ENNReal.measurable_toReal
  change IdentDistrib (fun ω => ((ENNReal.ofReal (anchoredProcessError B 1 ω)) ^ 2).toReal)
    (fun ω => (driftedSum (B · ω) 1 / 2).toReal) μ μ at h
  have hl : (fun ω => ((ENNReal.ofReal (anchoredProcessError B 1 ω)) ^ 2).toReal) =
      (fun ω => (anchoredProcessError B 1 ω) ^ 2) := by
    funext ω
    have hd : 0 ≤ anchoredProcessError B 1 ω := anchoredTimeError_nonneg (processPath B ω) 1
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hd]
  rw [hl] at h
  apply h.trans (IdentDistrib.of_ae_eq h.aemeasurable_snd ?_)
  filter_upwards [driftedSum_toReal_ae hB] with ω hω
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, hω]

/-- The manuscript's lifetime identity on real-valued random variables. -/
theorem identDistrib_anchoredLifetime_real_two_div_realDriftedSum (hB : IsBrownianReal B μ) :
    IdentDistrib (fun ω => (anchoredProcessLifetime B 1 ω).toReal)
      (fun ω => 2 / realDriftedSum (B · ω) 1) μ μ := by
  have h := (identDistrib_anchoredLifetime_two_div_driftedSum hB).comp ENNReal.measurable_toReal
  change IdentDistrib (fun ω => (anchoredProcessLifetime B 1 ω).toReal)
    (fun ω => (2 / driftedSum (B · ω) 1).toReal) μ μ at h
  apply h.trans (IdentDistrib.of_ae_eq h.aemeasurable_snd ?_)
  filter_upwards [driftedSum_toReal_ae hB] with ω hω
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, hω]

end BrownianAffine
