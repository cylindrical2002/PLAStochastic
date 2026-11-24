import PLAStochastic.Index.KEP.ReferenceScale.LongKernelBudgets
import PLAStochastic.Index.KEP.ReferenceScale.KernelSlope
import PLAStochastic.Index.GEP.Kernel.Row.Measurable

/-!
# Slope-averaged second derivatives of actual long killed rows

The two endpoint terms in the direct long-row estimate are paid by reciprocal
substitution. The remainder retains its extra geometric factor. The integral
uses the actual final convolution and is proved integrable before it is bounded.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepLongSecondSlopeBudget (D vlo vhi w : ℝ) (k : ℕ) (J1 J2 : ℝ) : ℝ :=
  2 * D * kepLongUniformVariation D vlo vhi w k * (3 + 2 * w) * J1 +
    6 * Real.sqrt (2 * D) * kepLongUniformRemainder D vlo vhi w k * J2

theorem krDens_second_long_uniform_bound
    (p : HellingerDensity (volume : Measure ℝ)) (ν : ProbabilityMeasure ℝ)
    {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν p.density w A a β a')
    {f' f'' : ℝ → ℝ}
    (hp : Continuous p.density) (hp' : Continuous f') (hp'' : Continuous f'')
    (hpi' : Integrable f' volume) (hpi'' : Integrable f'' volume)
    (hd : ∀ t, HasDerivAt p.density (f' t) t)
    (hdd : ∀ t, HasDerivAt f' (f'' t) t)
    (m k : ℕ) (hk : 8 ≤ k) (x y : ℝ) :
    |truncatedConvolution 0 w (kepStepSpatialSecond f'' β a')
        (fun z => krDens (Icc 0 w) ν p.density β a' (m + k + 2) x z) y| ≤
      2 * D * kepLongUniformVariation D vlo vhi w k *
        (2 * (∫ t, |f' t|) +
          w * (|kepStepSpatialFirst f' β a' y| +
            |kepStepSpatialFirst f' β a' (y - w)|)) +
      4 * (∫ t, |f'' t|) * Real.sqrt (2 * D) *
        kepLongUniformRemainder D vlo vhi w k := by
  have hDpos : 0 < D := H.hD
  have hwpos : 0 < w := H.hw0
  have hJ1 : (0 : ℝ) ≤ ∫ t, |f' t| := integral_nonneg (fun t => abs_nonneg (f' t))
  have hJ2 : (0 : ℝ) ≤ ∫ t, |f'' t| := integral_nonneg (fun t => abs_nonneg (f'' t))
  have hv := kepLongRowVarBudget_le_uniform ν H m k x
  have hr := kepLongRowRemBudget_le_uniform ν H m k x
  have hv0 := kepLongRowVarBudget_nonneg ν H m k x
  have hr0 : 0 ≤ kepLongRowRemBudget ν p.density D vlo vhi w β a' m k x := by
    unfold kepLongRowRemBudget kepLongRowEnergy
    positivity
  have ha : 1 / 2 ≤ |a'| := by rw [H.habs]; exact H.ha₁
  have ha0 : 0 < |a'| := by linarith
  have hD : D / |a'| ≤ 2 * D := (div_le_iff₀ ha0).mpr (by nlinarith [H.hD])
  have h1 : (∫ t, |f' t|) / |a'| ≤ 2 * (∫ t, |f' t|) := by
    apply (div_le_iff₀ ha0).mpr
    nlinarith
  have h2 : (∫ t, |f'' t|) / |a'| ^ 2 ≤ 4 * (∫ t, |f'' t|) := by
    apply (div_le_iff₀ (sq_pos_of_pos ha0)).mpr
    have hasq : 1 / 4 ≤ |a'| ^ 2 := by nlinarith
    nlinarith
  apply (krDens_second_long_bound p ν H hp hp' hp'' hpi' hpi'' hd hdd m k hk x y).trans
  apply add_le_add
  · apply mul_le_mul
    · exact mul_le_mul hD hv hv0 (by positivity)
    · exact add_le_add h1 le_rfl
    · positivity
    · exact mul_nonneg (by positivity) (kepLongUniformVariation_nonneg k H.hD H.hvlo H.hvhi)
  · apply mul_le_mul
    · exact mul_le_mul h2 (Real.sqrt_le_sqrt hD) (Real.sqrt_nonneg _) (by positivity)
    · exact hr
    · exact hr0
    · positivity

theorem measurable_kepLongSecond_slope
    (ν : ProbabilityMeasure ℝ) {f f'' : ℝ → ℝ}
    (hf : Measurable f) (hf'' : Measurable f'') (w σ : ℝ) (n : ℕ) (x y : ℝ) :
    Measurable (fun a => truncatedConvolution 0 w (kepStepSpatialSecond f'' σ (σ * a))
      (fun z => krDens (Icc 0 w) ν f σ (σ * a) n x z) y) := by
  have hp : Measurable (fun t : ℝ × ℝ =>
      kepStepSpatialSecond f'' σ (σ * t.1) (y - t.2)) := by
    unfold kepStepSpatialSecond
    fun_prop
  have hk : Measurable (fun t : ℝ × ℝ => krDens (Icc 0 w) ν f σ (σ * t.1) n x t.2) :=
    measurable_krDens_param ν measurableSet_Icc hf
    (measurable_const : Measurable (fun _ : ℝ × ℝ => σ))
    (measurable_const.mul measurable_fst)
    (measurable_const : Measurable (fun _ : ℝ × ℝ => x)) measurable_snd n
  exact (hp.mul hk).stronglyMeasurable.integral_prod_right'.measurable

theorem krDens_second_long_slope_budget
    (p : HellingerDensity (volume : Measure ℝ)) (ν : ProbabilityMeasure ℝ)
    {D θ vlo vhi K L w σ : ℝ}
    (H : ∀ a ∈ Icc (1 / 2 : ℝ) 2,
      KrBand D θ vlo vhi K L ν p.density w w a σ (σ * a))
    {f' f'' : ℝ → ℝ}
    (hp : Continuous p.density) (hp' : Continuous f') (hp'' : Continuous f'')
    (hpi' : Integrable f' volume) (hpi'' : Integrable f'' volume)
    (hd : ∀ t, HasDerivAt p.density (f' t) t)
    (hdd : ∀ t, HasDerivAt f' (f'' t) t)
    (hz : ∀ t, t ≤ 0 → f' t = 0)
    (hw : 2 ≤ w) (hσ : σ = 1 ∨ σ = -1)
    (m k : ℕ) (hk : 8 ≤ k) (x : ℝ) {y : ℝ} (hy : y = 0 ∨ y = w) :
    let F := fun a => truncatedConvolution 0 w (kepStepSpatialSecond f'' σ (σ * a))
      (fun z => krDens (Icc 0 w) ν p.density σ (σ * a) (m + k + 2) x z) y
    IntegrableOn (fun a => |F a|) (Icc (1 / 2 : ℝ) 2) ∧
      (∫ a in Icc (1 / 2 : ℝ) 2, |F a|) ≤
        kepLongSecondSlopeBudget D vlo vhi w k (∫ t, |f' t|) (∫ t, |f'' t|) := by
  let F := fun a => truncatedConvolution 0 w (kepStepSpatialSecond f'' σ (σ * a))
    (fun z => krDens (Icc 0 w) ν p.density σ (σ * a) (m + k + 2) x z) y
  have H0 := H 1 (by constructor <;> norm_num)
  have hDpos : 0 < D := H0.hD
  let V := kepLongUniformVariation D vlo vhi w k
  let R := kepLongUniformRemainder D vlo vhi w k
  let J1 := ∫ t, |f' t|
  let J2 := ∫ t, |f'' t|
  have hV : 0 ≤ V := kepLongUniformVariation_nonneg k H0.hD H0.hvlo H0.hvhi
  have hR : 0 ≤ R := kepLongUniformRemainder_nonneg D vlo vhi w k
  have hJ1 : 0 ≤ J1 := integral_nonneg (fun t => abs_nonneg (f' t))
  have hJ2 : 0 ≤ J2 := integral_nonneg (fun t => abs_nonneg (f'' t))
  have hb (b : ℝ) (hbm : b = 0 ∨ b = w) :
      IntegrableOn (fun a => |kepStepSpatialFirst f' σ (σ * a) (y - b)|)
        (Icc (1 / 2 : ℝ) 2) ∧
      (∫ a in Icc (1 / 2 : ℝ) 2, |kepStepSpatialFirst f' σ (σ * a) (y - b)|) ≤ J1 := by
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using kepStepSpatialFirst_endpoint_slope_budget
        hpi' hz hw hy hbm (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    · simpa only [neg_one_mul] using kepStepSpatialFirst_reverse_endpoint_slope_budget
        hpi' hz hw hy hbm (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  obtain ⟨hi0, h0⟩ := hb 0 (Or.inl rfl)
  simp only [sub_zero] at hi0 h0
  obtain ⟨hiw, hwB⟩ := hb w (Or.inr rfl)
  let G := fun a => 2 * D * V *
      (2 * J1 + w * (|kepStepSpatialFirst f' σ (σ * a) y| +
        |kepStepSpatialFirst f' σ (σ * a) (y - w)|)) +
      4 * J2 * Real.sqrt (2 * D) * R
  have hiMain : IntegrableOn (fun a => 2 * D * V *
      (2 * J1 + w * (|kepStepSpatialFirst f' σ (σ * a) y| +
        |kepStepSpatialFirst f' σ (σ * a) (y - w)|))) (Icc (1 / 2 : ℝ) 2) :=
    ((integrableOn_const (by simp : volume (Icc (1 / 2 : ℝ) 2) ≠ ⊤)).add
      ((hi0.add hiw).const_mul w)).const_mul (2 * D * V)
  have hiG : IntegrableOn G (Icc (1 / 2 : ℝ) 2) := hiMain.add
      (integrableOn_const (by simp : volume (Icc (1 / 2 : ℝ) 2) ≠ ⊤))
  have hFG (a : ℝ) (ha : a ∈ Icc (1 / 2 : ℝ) 2) : |F a| ≤ G a :=
    krDens_second_long_uniform_bound p ν (H a ha) hp hp' hp'' hpi' hpi'' hd hdd m k hk x y
  have hiF : IntegrableOn (fun a => |F a|) (Icc (1 / 2 : ℝ) 2) := by
    apply hiG.mono'
      (measurable_kepLongSecond_slope ν p.measurable hp''.measurable w σ (m + k + 2) x y).abs.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    simpa only [Real.norm_eq_abs, abs_abs] using hFG a ha
  refine ⟨hiF, ?_⟩
  calc
    _ ≤ ∫ a in Icc (1 / 2 : ℝ) 2, G a := by
      apply integral_mono_ae hiF hiG
      filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      exact hFG a ha
    _ = 2 * D * V * (3 * J1 + w *
        ((∫ a in Icc (1 / 2 : ℝ) 2, |kepStepSpatialFirst f' σ (σ * a) y|) +
         (∫ a in Icc (1 / 2 : ℝ) 2, |kepStepSpatialFirst f' σ (σ * a) (y - w)|))) +
        6 * J2 * Real.sqrt (2 * D) * R := by
      dsimp only [G]
      rw [integral_add hiMain (integrable_const _), integral_const_mul,
        integral_add (f := fun _ : ℝ => 2 * J1)
          (g := fun a => w * (|kepStepSpatialFirst f' σ (σ * a) y| +
            |kepStepSpatialFirst f' σ (σ * a) (y - w)|))
          (integrable_const _) ((hi0.add hiw).const_mul w)]
      simp only [integral_const_mul, integral_add hi0 hiw,
        integral_const, Measure.real]
      norm_num
      ring
    _ ≤ kepLongSecondSlopeBudget D vlo vhi w k J1 J2 := by
      unfold kepLongSecondSlopeBudget
      change _ ≤ 2 * D * V * (3 + 2 * w) * J1 + 6 * Real.sqrt (2 * D) * R * J2
      have hb' := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add h0 hwB) (by linarith : 0 ≤ w))
        (by positivity : 0 ≤ 2 * D * V)
      nlinarith

end

end PGM
