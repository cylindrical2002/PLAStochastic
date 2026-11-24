import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.LadderMeanBound
import PLAStochastic.Swing.ConstantEvaluation.SlopeKernelReduction

/-! # The Lipschitz constant of the slope reward `h = 𝖡v` (roadmap 1.5)

`𝖡(b)` has the density `Φ_b(s) = P(0 < X₀ + s + I'_b) / b` on `(-∞, b]`
(`lintegral_swingOvershootMeasure`).  Two facts about `Φ` drive the Lipschitz
bound of `h(b) = ∫ v dB(b)`:

* `Φ_c ≤ Φ_a` pointwise for `0 < a ≤ c` (tilt monotonicity and Spitzer, the
  density form of the stochastic monotonicity of `𝖡`);
* `Φ_b(s) ≤ p_b / b ≤ √2` for `s ≤ b`, where `p_b = P(M_b = 0)` and `p_b ≤ √2 b`
  is `measure_posWalkSet_le_sqrt_two_mul`.

With `0 ≤ v(s) ≤ 4 (s₊ + C)` this gives, for `0 < a ≤ c`,

  `h(c) - h(a) ≤ ∫_{(a,c]} v Φ_c ≤ 4 (c + C) (p_c / c) (c - a)`,
  `h(a) - h(c) ≤ 4 (a + C) ∫_{(-∞,a]} (Φ_a - Φ_c) = 4 (a + C) 𝖡(c)((a, c]) ≤ 4 (a + C) (p_c / c) (c - a)`,

hence `|h(c) - h(a)| ≤ 4 (1 + √2 C) (c - a)`, using `p_c ≤ 1` and `p_c / c ≤ √2`.
The paper's `L_h = 4 + 8/√π` is the case `C = √(2/π)`; the library's proved
linear bound `marginLeadingReward_le_linear` has `C = gaussianExcessExpMomentBound 2`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open Fluctuation LeadingCoefficient

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- `Φ_b(s) = P(0 < X₀ + s + I'_b) / b`, the density of `𝖡(b)` at `s ≤ b`. -/
def overshootDensity (X : ℕ → Ω → ℝ) (μ : Measure Ω) (b s : ℝ) : ℝ≥0∞ :=
  μ {ω | 0 < X 0 ω + s + shiftInf X b ω} * (ENNReal.ofReal b)⁻¹

theorem measurable_measure_shiftInf_pos (X : ℕ → Ω → ℝ) (μ : Measure Ω) (b : ℝ) :
    Measurable fun s : ℝ => μ {ω | 0 < X 0 ω + s + shiftInf X b ω} := by
  refine Monotone.measurable fun s s' h => measure_mono fun ω hω => ?_
  simp only [mem_ofPred_eq] at hω ⊢
  linarith

theorem overshootDensity_measurable (X : ℕ → Ω → ℝ) (μ : Measure Ω) (b : ℝ) :
    Measurable (overshootDensity X μ b) :=
  (measurable_measure_shiftInf_pos X μ b).mul_const _

/-- The normalisation `p_b⁻¹ μ_b⁻¹ = b⁻¹`. -/
theorem inv_measure_posWalkSet_mul_inv_ladderMean (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {b : ℝ} (hb : 0 < b) :
    (μ (posWalkSet X b))⁻¹ * (ladderMeanENN (gaussianAscendingLadderLaw X μ b))⁻¹ =
      (ENNReal.ofReal b)⁻¹ := by
  have h1 := swingOvershootMeasure_Iic_aux hX hi hG hb le_rfl
  rw [swingOvershootMeasure_Iic_self hX hi hG hb, sub_self, dualPosPartLIntegral_zero hX hi hG hb]
    at h1
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1.symm)

/-- **Density representation of `𝖡(b)`**: `∫ f d𝖡(b) = ∫_{(-∞,b]} f(s) Φ_b(s) ds`. -/
theorem lintegral_swingOvershootMeasure (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {b : ℝ} (hb : 0 < b)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ r, f r ∂swingOvershootMeasure X μ b = ∫⁻ s in Iic b, f s * overshootDensity X μ b s := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hp0 : μ (posWalkSet X b) ≠ 0 := measure_posWalkSet_pos hX hi hG hb
  have hpt : μ (posWalkSet X b) ≠ ⊤ := measure_ne_top _ _
  have hK := inv_measure_posWalkSet_mul_inv_ladderMean hX hi hG hb
  have hdens_meas : Measurable fun o : ℝ => gaussianAscendingLadderLaw X μ b (Ioi o) /
      ladderMeanENN (gaussianAscendingLadderLaw X μ b) :=
    (measurable_ladderTail _).div_const _
  have hfb : Measurable fun o : ℝ => f (b - o) := hf.comp (measurable_const_sub_self b)
  rw [swingOvershootMeasure, lintegral_map hf (measurable_const_sub_self b), equilibriumOvershootLaw,
    lintegral_withDensity_eq_lintegral_mul _ hdens_meas hfb]
  -- rewrite the density on `[0, ∞)`
  set F : ℝ → ℝ≥0∞ := fun o => μ {ω | o < ladderDualVariable X b ω} * (ENNReal.ofReal b)⁻¹ *
    f (b - o) with hF
  have hdens : ∀ o ∈ Ici (0 : ℝ),
      ((fun o : ℝ => gaussianAscendingLadderLaw X μ b (Ioi o) /
        ladderMeanENN (gaussianAscendingLadderLaw X μ b)) * fun o => f (b - o)) o = F o := by
    intro o ho
    have ho0 : 0 ≤ o := mem_Ici.mp ho
    have hνo : gaussianAscendingLadderLaw X μ b (Ioi o) =
        μ {ω | o < ladderDualVariable X b ω} * (μ (posWalkSet X b))⁻¹ := by
      rw [← measure_posWalkSet_mul_ladderLaw_Ioi hX hi hG hb ho0, mul_comm (μ (posWalkSet X b)),
        mul_assoc, ENNReal.mul_inv_cancel hp0 hpt, mul_one]
    simp only [Pi.mul_apply, hF]
    rw [hνo, div_eq_mul_inv, ← hK]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ici hdens, ← lintegral_indicator measurableSet_Ici,
    ← lintegral_sub_left_eq_self (fun o => (Ici (0 : ℝ)).indicator F o) b,
    ← lintegral_indicator measurableSet_Iic]
  congr 1
  funext s
  by_cases hs : s ≤ b
  · rw [indicator_of_mem (show b - s ∈ Ici (0 : ℝ) from by simp [hs]),
      indicator_of_mem (show s ∈ Iic b from hs)]
    simp only [hF, overshootDensity, sub_sub_cancel]
    have hset : {ω | b - s < ladderDualVariable X b ω} = {ω | 0 < X 0 ω + s + shiftInf X b ω} := by
      ext ω
      simp only [mem_ofPred_eq, ladderDualVariable]
      constructor <;> intro h <;> linarith
    rw [hset]
    ring
  · rw [indicator_of_notMem (show b - s ∉ Ici (0 : ℝ) from by simp; linarith),
      indicator_of_notMem (show s ∉ Iic b from hs)]

/-- `𝖡(b)(A) = ∫_A Φ_b` for measurable `A ⊆ (-∞, b]`. -/
theorem swingOvershootMeasure_eq_setLIntegral_density (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {b : ℝ} (hb : 0 < b)
    {A : Set ℝ} (hA : MeasurableSet A) (hAb : A ⊆ Iic b) :
    swingOvershootMeasure X μ b A = ∫⁻ s in A, overshootDensity X μ b s := by
  rw [← lintegral_indicator_one hA,
    lintegral_swingOvershootMeasure hX hi hG hb (measurable_one.indicator hA)]
  rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator hA]
  congr 1
  funext s
  by_cases hs : s ∈ A
  · have hs' : s ∈ Iic b := hAb hs
    simp [indicator_of_mem hs, indicator_of_mem hs']
  · by_cases hs' : s ∈ Iic b
    · simp [indicator_of_notMem hs, indicator_of_mem hs']
    · simp [indicator_of_notMem hs, indicator_of_notMem hs']

/-- ENNReal helper: `x a ≤ y c` implies `x / c ≤ y / a` for positive real `a, c`. -/
theorem ENNReal_div_le_div_of_mul_le {x y : ℝ≥0∞} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (h : x * ENNReal.ofReal a ≤ y * ENNReal.ofReal c) :
    x * (ENNReal.ofReal c)⁻¹ ≤ y * (ENNReal.ofReal a)⁻¹ := by
  have ha0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have hat : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hct : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  calc x * (ENNReal.ofReal c)⁻¹
      = x * ENNReal.ofReal a * (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal c)⁻¹ := by
        rw [mul_assoc x, ENNReal.mul_inv_cancel ha0 hat, mul_one]
    _ ≤ y * ENNReal.ofReal c * (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal c)⁻¹ := by gcongr
    _ = y * (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal c * (ENNReal.ofReal c)⁻¹) := by ring
    _ = y * (ENNReal.ofReal a)⁻¹ := by rw [ENNReal.mul_inv_cancel hc0 hct, mul_one]

/-- **Density monotonicity**: `Φ_c ≤ Φ_a` for `0 < a ≤ c`. -/
theorem overshootDensity_antitone (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a c : ℝ} (ha : 0 < a)
    (hac : a ≤ c) (s : ℝ) : overshootDensity X μ c s ≤ overshootDensity X μ a s := by
  have hc : 0 < c := ha.trans_le hac
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set g : ℝ → ℝ → ℝ≥0∞ := fun x i => (Ioi (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞) (x + s + i) with hg
  have hgm : Measurable (Function.uncurry g) := by
    have : Function.uncurry g = fun p : ℝ × ℝ => (Ioi (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞)
        (p.1 + s + p.2) := by
      funext p; rfl
    rw [this]
    exact (measurable_one.indicator measurableSet_Ioi).comp
      ((measurable_fst.add_const s).add measurable_snd)
  have key : ∀ b : ℝ, ∫⁻ ω, g (X 0 ω) (shiftInf X b ω) ∂μ =
      μ {ω | 0 < X 0 ω + s + shiftInf X b ω} := by
    intro b
    have hmeas : MeasurableSet {ω | 0 < X 0 ω + s + shiftInf X b ω} :=
      measurableSet_lt measurable_const (((hX 0).add_const s).add (shiftInf_measurable hX b))
    rw [← lintegral_indicator_one hmeas]
    refine lintegral_congr fun ω => ?_
    by_cases h : 0 < X 0 ω + s + shiftInf X b ω <;> simp [hg, indicator, h]
  have htilt := lintegral_shiftInf_antitone hX hi hG ha hac hgm
  rw [key, key] at htilt
  have hsp := measure_posWalkSet_mul_ofReal_le hX hi hG ha hac
  set pa := μ (posWalkSet X a)
  set pc := μ (posWalkSet X c)
  set mc := μ {ω | 0 < X 0 ω + s + shiftInf X c ω}
  set ma := μ {ω | 0 < X 0 ω + s + shiftInf X a ω}
  have hpa0 : pa ≠ 0 := measure_posWalkSet_pos hX hi hG ha
  have hpat : pa ≠ ⊤ := measure_ne_top _ _
  have hpc0 : pc ≠ 0 := measure_posWalkSet_pos hX hi hG hc
  have hpct : pc ≠ ⊤ := measure_ne_top _ _
  have hprod : (pa * pc) * (mc * ENNReal.ofReal a) ≤ (pa * pc) * (ma * ENNReal.ofReal c) := by
    calc (pa * pc) * (mc * ENNReal.ofReal a) = (pa * mc) * (pc * ENNReal.ofReal a) := by ring
      _ ≤ (pc * ma) * (pa * ENNReal.ofReal c) := mul_le_mul' htilt hsp
      _ = (pa * pc) * (ma * ENNReal.ofReal c) := by ring
  have hcore : mc * ENNReal.ofReal a ≤ ma * ENNReal.ofReal c :=
    (ENNReal.mul_le_mul_iff_right (mul_ne_zero hpa0 hpc0) (ENNReal.mul_ne_top hpat hpct)).mp hprod
  exact ENNReal_div_le_div_of_mul_le ha hc hcore

/-- `Φ_b(s) ≤ p_b / b` for `s ≤ b`. -/
theorem overshootDensity_le (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {b : ℝ} (hb : 0 < b)
    {s : ℝ} (hs : s ≤ b) :
    overshootDensity X μ b s ≤ μ (posWalkSet X b) * (ENNReal.ofReal b)⁻¹ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hν := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi b
  unfold overshootDensity
  refine mul_le_mul_left ?_ _
  calc μ {ω | 0 < X 0 ω + s + shiftInf X b ω}
      ≤ μ {ω | 0 < ladderDualVariable X b ω} := by
        refine measure_mono fun ω hω => ?_
        simp only [mem_ofPred_eq, ladderDualVariable] at hω ⊢
        linarith
    _ = μ (posWalkSet X b) * gaussianAscendingLadderLaw X μ b (Ioi 0) :=
        (measure_posWalkSet_mul_ladderLaw_Ioi hX hi hG hb le_rfl).symm
    _ ≤ μ (posWalkSet X b) * 1 := mul_le_mul_right prob_le_one _
    _ = μ (posWalkSet X b) := mul_one _

/-- `𝖡(c)((a, c]) ≤ (p_c / c) (c - a)`. -/
theorem swingOvershootMeasure_Ioc_le (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a c : ℝ} (hc : 0 < c) :
    swingOvershootMeasure X μ c (Ioc a c) ≤
      μ (posWalkSet X c) * (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal (c - a) := by
  rw [swingOvershootMeasure_eq_setLIntegral_density hX hi hG hc measurableSet_Ioc
    Ioc_subset_Iic_self]
  calc ∫⁻ s in Ioc a c, overshootDensity X μ c s
      ≤ ∫⁻ _ in Ioc a c, μ (posWalkSet X c) * (ENNReal.ofReal c)⁻¹ := by
        refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
        exact overshootDensity_le hX hi hG hc hs.2
    _ = μ (posWalkSet X c) * (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal (c - a) := by
        rw [setLIntegral_const, Real.volume_Ioc]

/-- `h(b)` through the density. -/
theorem ofReal_slopeReward_eq_density (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {b : ℝ} (hb : 0 < b) :
    ENNReal.ofReal (slopeReward X μ b) =
      ∫⁻ s in Iic b, ENNReal.ofReal (marginLeadingReward X μ s) * overshootDensity X μ b s := by
  rw [ofReal_slopeReward hX hi hG b]
  exact lintegral_swingOvershootMeasure hX hi hG hb
    (marginLeadingReward_measurable' hX hi hG).ennreal_ofReal

/-- The Lipschitz constant `4 (1 + √2 C)` as a nonnegative real. -/
def slopeRewardLipschitzConst (C : ℝ) : ℝ≥0 := Real.toNNReal (4 * (1 + Real.sqrt 2 * C))

theorem coe_slopeRewardLipschitzConst {C : ℝ} (hC : 0 ≤ C) :
    ((slopeRewardLipschitzConst C : ℝ≥0) : ℝ) = 4 * (1 + Real.sqrt 2 * C) :=
  Real.coe_toNNReal _ (by positivity)

/-- The real-valued bound `(p_c / c)(c - a)` and its two elementary consequences. -/
theorem posWalk_ratio_bound (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a c C : ℝ} (hC : 0 ≤ C)
    (hac : a ≤ c) (hc : 0 < c) :
    4 * (c + C) * (μ.real (posWalkSet X c) / c * (c - a)) ≤ 4 * (1 + Real.sqrt 2 * C) * (c - a) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hp1 : μ.real (posWalkSet X c) ≤ 1 := by
    rw [Measure.real]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr prob_le_one
  have hp0 : 0 ≤ μ.real (posWalkSet X c) := measureReal_nonneg
  have hps := measureReal_posWalkSet_le_sqrt_two_mul hX hi hG hc
  have hratio : μ.real (posWalkSet X c) / c ≤ Real.sqrt 2 := by
    rw [div_le_iff₀ hc]; exact hps
  have hca : 0 ≤ c - a := by linarith
  have : 4 * (c + C) * (μ.real (posWalkSet X c) / c) =
      4 * (μ.real (posWalkSet X c) + C * (μ.real (posWalkSet X c) / c)) := by
    field_simp
  calc 4 * (c + C) * (μ.real (posWalkSet X c) / c * (c - a))
      = 4 * (c + C) * (μ.real (posWalkSet X c) / c) * (c - a) := by ring
    _ = 4 * (μ.real (posWalkSet X c) + C * (μ.real (posWalkSet X c) / c)) * (c - a) := by rw [this]
    _ ≤ 4 * (1 + C * Real.sqrt 2) * (c - a) := by
        gcongr
    _ = 4 * (1 + Real.sqrt 2 * C) * (c - a) := by ring

/-- **The Lipschitz bound of `h`**, parametrised by a linear bound on `v`. -/
theorem slopeReward_lipschitzOnWith_of_le [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ s : ℝ, marginLeadingReward X μ s ≤ 4 * (max s 0 + C)) :
    LipschitzOnWith (slopeRewardLipschitzConst C) (slopeReward X μ) (Ioi 0) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set v := marginLeadingReward X μ with hvdef
  have hvmeas : Measurable v := marginLeadingReward_measurable' hX hi hG
  have hvnn : ∀ s, 0 ≤ v s := fun s => marginLeadingReward_nonneg hX hi hG
  -- the one-sided estimate for `a ≤ c`
  have main : ∀ a c : ℝ, 0 < a → a ≤ c →
      |slopeReward X μ c - slopeReward X μ a| ≤ 4 * (1 + Real.sqrt 2 * C) * (c - a) := by
    intro a c ha hac
    have hc : 0 < c := ha.trans_le hac
    have : IsProbabilityMeasure (swingOvershootMeasure X μ c) :=
      swingOvershootMeasure_isProbability hX hi hG hc
    set Φa := overshootDensity X μ a
    set Φc := overshootDensity X μ c
    have hΦa : Measurable Φa := overshootDensity_measurable X μ a
    have hΦc : Measurable Φc := overshootDensity_measurable X μ c
    have hanti : ∀ s, Φc s ≤ Φa s := overshootDensity_antitone hX hi hG ha hac
    set w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (v s) with hw
    have hwm : Measurable w := hvmeas.ennreal_ofReal
    have hIa := ofReal_slopeReward_eq_density hX hi hG ha
    have hIc := ofReal_slopeReward_eq_density hX hi hG hc
    -- the boundary mass `R = (p_c / c)(c - a)`
    set R : ℝ≥0∞ := μ (posWalkSet X c) * (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal (c - a) with hR
    have hRt : R ≠ ⊤ := by
      rw [hR]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _)
        (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne')) ENNReal.ofReal_ne_top
    have hRreal : R.toReal = μ.real (posWalkSet X c) / c * (c - a) := by
      rw [hR, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hc.le,
        ENNReal.toReal_ofReal (by linarith), div_eq_mul_inv]
      rfl
    -- split `(-∞, c] = (-∞, a] ∪ (a, c]`
    have hsplit : ∫⁻ s in Iic c, w s * Φc s =
        (∫⁻ s in Iic a, w s * Φc s) + ∫⁻ s in Ioc a c, w s * Φc s := by
      rw [← Iic_union_Ioc_eq_Iic hac, lintegral_union measurableSet_Ioc (Iic_disjoint_Ioc le_rfl)]
    -- the tail term
    have hD : ∫⁻ s in Ioc a c, w s * Φc s ≤ ENNReal.ofReal (4 * (c + C)) * R := by
      calc ∫⁻ s in Ioc a c, w s * Φc s
          ≤ ∫⁻ _ in Ioc a c, ENNReal.ofReal (4 * (c + C)) *
              (μ (posWalkSet X c) * (ENNReal.ofReal c)⁻¹) := by
            refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
            refine mul_le_mul' ?_ (overshootDensity_le hX hi hG hc hs.2)
            refine ENNReal.ofReal_le_ofReal ((hv s).trans ?_)
            have : max s 0 ≤ c := max_le hs.2 hc.le
            linarith
        _ = ENNReal.ofReal (4 * (c + C)) * R := by
            rw [setLIntegral_const, Real.volume_Ioc, hR]; ring
    -- upper bound `h(c) - h(a) ≤ D`
    have hup : ENNReal.ofReal (slopeReward X μ c) ≤
        ENNReal.ofReal (slopeReward X μ a) + ENNReal.ofReal (4 * (c + C)) * R := by
      rw [hIc, hIa, hsplit]
      refine add_le_add ?_ hD
      exact lintegral_mono fun s => mul_le_mul_right (hanti s) _
    -- lower bound `h(a) - h(c) ≤ 4 (a + C) 𝖡(c)((a, c])`
    have hBc_Iic : swingOvershootMeasure X μ c (Iic a) = ∫⁻ s in Iic a, Φc s :=
      swingOvershootMeasure_eq_setLIntegral_density hX hi hG hc measurableSet_Iic
        (Iic_subset_Iic.mpr hac)
    have hBa_Iic : (1 : ℝ≥0∞) = ∫⁻ s in Iic a, Φa s := by
      rw [← swingOvershootMeasure_Iic_self hX hi hG ha]
      exact swingOvershootMeasure_eq_setLIntegral_density hX hi hG ha measurableSet_Iic
        subset_rfl
    have hBc_one : swingOvershootMeasure X μ c (Iic a) + swingOvershootMeasure X μ c (Ioc a c) = 1 := by
      rw [← measure_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc, Iic_union_Ioc_eq_Iic hac]
      exact swingOvershootMeasure_Iic_self hX hi hG hc
    have hΦc_fin : ∫⁻ s in Iic a, Φc s ≠ ⊤ := by
      rw [← hBc_Iic]; exact measure_ne_top _ _
    have hdiff : (∫⁻ s in Iic a, (Φa s - Φc s)) = swingOvershootMeasure X μ c (Ioc a c) := by
      rw [lintegral_sub hΦc hΦc_fin (ae_of_all _ fun s => hanti s), ← hBa_Iic, ← hBc_Iic]
      exact ENNReal.sub_eq_of_eq_add (measure_ne_top _ _) (by rw [add_comm]; exact hBc_one.symm)
    have hlow : ENNReal.ofReal (slopeReward X μ a) ≤
        ENNReal.ofReal (slopeReward X μ c) + ENNReal.ofReal (4 * (a + C)) * R := by
      rw [hIa, hIc, hsplit]
      have hpt : ∀ s ∈ Iic a,
          w s * Φa s ≤ w s * Φc s + ENNReal.ofReal (4 * (a + C)) * (Φa s - Φc s) := by
        intro s hs
        have hws : w s ≤ ENNReal.ofReal (4 * (a + C)) := by
          refine ENNReal.ofReal_le_ofReal ((hv s).trans ?_)
          have : max s 0 ≤ a := max_le (mem_Iic.mp hs) ha.le
          linarith
        calc w s * Φa s = w s * (Φc s + (Φa s - Φc s)) := by rw [add_tsub_cancel_of_le (hanti s)]
          _ = w s * Φc s + w s * (Φa s - Φc s) := mul_add _ _ _
          _ ≤ w s * Φc s + ENNReal.ofReal (4 * (a + C)) * (Φa s - Φc s) := by gcongr
      have h1 : ∫⁻ s in Iic a, w s * Φa s ≤
          (∫⁻ s in Iic a, w s * Φc s) +
            ENNReal.ofReal (4 * (a + C)) * ∫⁻ s in Iic a, (Φa s - Φc s) := by
        calc ∫⁻ s in Iic a, w s * Φa s
            ≤ ∫⁻ s in Iic a, (w s * Φc s + ENNReal.ofReal (4 * (a + C)) * (Φa s - Φc s)) :=
              setLIntegral_mono' measurableSet_Iic hpt
          _ = (∫⁻ s in Iic a, w s * Φc s) +
              ∫⁻ s in Iic a, ENNReal.ofReal (4 * (a + C)) * (Φa s - Φc s) :=
              lintegral_add_left' (hwm.mul hΦc).aemeasurable _
          _ = (∫⁻ s in Iic a, w s * Φc s) +
              ENNReal.ofReal (4 * (a + C)) * ∫⁻ s in Iic a, (Φa s - Φc s) := by
              have hm : Measurable fun s => Φa s - Φc s := hΦa.sub hΦc
              rw [lintegral_const_mul _ hm]
      refine h1.trans ?_
      rw [hdiff]
      refine add_le_add le_self_add ?_
      gcongr
      exact swingOvershootMeasure_Ioc_le hX hi hG hc
    -- pass to the reals
    have hha : 0 ≤ slopeReward X μ a := slopeReward_nonneg hX hi hG a
    have hhc : 0 ≤ slopeReward X μ c := slopeReward_nonneg hX hi hG c
    have hRr : 0 ≤ R.toReal := ENNReal.toReal_nonneg
    have hup' : slopeReward X μ c ≤ slopeReward X μ a + 4 * (c + C) * R.toReal := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRt⟩) hup
      rwa [ENNReal.toReal_ofReal hhc, ENNReal.toReal_add ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRt), ENNReal.toReal_ofReal hha,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    have hlow' : slopeReward X μ a ≤ slopeReward X μ c + 4 * (a + C) * R.toReal := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRt⟩) hlow
      rwa [ENNReal.toReal_ofReal hha, ENNReal.toReal_add ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRt), ENNReal.toReal_ofReal hhc,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    have hbound := posWalk_ratio_bound hX hi hG hC hac hc
    rw [← hRreal] at hbound
    have hac' : 4 * (a + C) * R.toReal ≤ 4 * (c + C) * R.toReal := by gcongr
    rw [abs_le]
    constructor <;> linarith
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [coe_slopeRewardLipschitzConst hC, Real.dist_eq, Real.dist_eq]
  rcases le_total x y with hxy | hxy
  · have := main x y hx hxy
    rw [abs_of_nonpos (by linarith : x - y ≤ 0), abs_sub_comm]
    linarith
  · have := main y x hy hxy
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith

/-- **`L_h` for the library's linear bound on `v`.** -/
theorem slopeReward_lipschitzOnWith [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    LipschitzOnWith (slopeRewardLipschitzConst (gaussianExcessExpMomentBound 2))
      (slopeReward X μ) (Ioi 0) :=
  slopeReward_lipschitzOnWith_of_le hX hi hG (gaussianExcessExpMomentBound_pos 2).le
    (fun _ => marginLeadingReward_le_linear hX hi hG)

end SwingRepair
