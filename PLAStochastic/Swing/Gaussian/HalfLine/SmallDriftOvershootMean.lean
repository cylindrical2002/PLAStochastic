import PLAStochastic.Swing.Gaussian.HalfLine.PrefixStability
import PLAStochastic.ForMathlib.MeasureTheory.Integral.GeometricTailUniformIntegrability

/-! Uniform integrability and actual small-drift overshoot means. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussianHalfLineOvershoot_lintegral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hf0 : f 0 = 0)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω, f (gaussianHalfLineOvershoot X x a ω) ∂μ) ≤ C := by
  have := hi.isProbabilityMeasure
  have hm : MeasurableSet {ω | gaussianHalfLineExit X x a ω ≠ ⊤} :=
    ((gaussianHalfLineExit_isStoppingTime hX x a).measurable' (measurableSet_singleton ⊤)).compl
  have he : ∀ ω, f (gaussianHalfLineOvershoot X x a ω) =
      {ω | gaussianHalfLineExit X x a ω ≠ ⊤}.indicator
        (fun ω => f (gaussianHalfLineOvershoot X x a ω)) ω := by
    intro ω
    by_cases hω : gaussianHalfLineExit X x a ω = ⊤
    · simp [hω, gaussianHalfLineOvershoot, hf0]
    · simp [hω]
  calc
    _ = ∫⁻ ω in {ω | gaussianHalfLineExit X x a ω ≠ ⊤},
        f (gaussianHalfLineOvershoot X x a ω) ∂μ := by
      calc
        _ = ∫⁻ ω, {ω | gaussianHalfLineExit X x a ω ≠ ⊤}.indicator
            (fun ω => f (gaussianHalfLineOvershoot X x a ω)) ω ∂μ := lintegral_congr he
        _ = _ := lintegral_indicator hm _
    _ ≤ C * μ {ω | gaussianHalfLineExit X x a ω ≠ ⊤} :=
      gaussianHalfLineFinite_lintegral_le hX hi hG hx ha hf hC hb
    _ ≤ C * 1 := by gcongr; exact prob_le_one
    _ = C := mul_one _


/-- Any uniform nonnegative excess moment transfers to the actual selected exit overshoot. -/
theorem gaussianHalfLineOvershoot_integral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : f 0 = 0)
    (hfn : ∀ u, 0 ≤ u → 0 ≤ f u) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r →
      Integrable f (gaussianExcessLaw r) ∧ (∫ u, f u ∂gaussianExcessLaw r) ≤ C) :
    Integrable (fun ω => f (gaussianHalfLineOvershoot X x a ω)) μ ∧
      (∫ ω, f (gaussianHalfLineOvershoot X x a ω) ∂μ) ≤ C := by
  have hfm : Measurable (fun ω => f (gaussianHalfLineOvershoot X x a ω)) :=
    hf.comp (gaussianHalfLineOvershoot_measurable hX x a)
  have hfn' : 0 ≤ᵐ[μ] (fun ω => f (gaussianHalfLineOvershoot X x a ω)) :=
    ae_of_all _ (fun ω => hfn _ (gaussianHalfLineOvershoot_nonneg X x a ω))
  have hle : (∫⁻ ω, ENNReal.ofReal (f (gaussianHalfLineOvershoot X x a ω)) ∂μ) ≤
      ENNReal.ofReal C := by
    apply gaussianHalfLineOvershoot_lintegral_le hX hi hG hx ha
      hf.ennreal_ofReal (by simp [hf0]) ENNReal.ofReal_ne_top
    intro r hr
    rw [← ofReal_integral_eq_lintegral_ofReal (hb r hr).1
      ((gaussianExcessLaw_positive_ae r).mono (fun u hu => hfn u hu.le))]
    exact ENNReal.ofReal_le_ofReal (hb r hr).2
  have hint := (lintegral_ofReal_ne_top_iff_integrable
    hfm.aestronglyMeasurable hfn').mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hfn'] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hle

/-- The first two moments of the actual selected overshoot are bounded independently of the strip. -/
theorem gaussianHalfLineOvershoot_uniform_moments
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) :
    (Integrable (gaussianHalfLineOvershoot X x a) μ ∧
      (∫ ω, gaussianHalfLineOvershoot X x a ω ∂μ) ≤ gaussianExcessExpMomentBound 2) ∧
    (Integrable (fun ω => (gaussianHalfLineOvershoot X x a ω)^2) μ ∧
      (∫ ω, (gaussianHalfLineOvershoot X x a ω)^2 ∂μ) ≤ gaussianExcessExpMomentBound 2) := by
  refine ⟨gaussianHalfLineOvershoot_integral_le hX hi hG hx ha measurable_id rfl
    (fun _ hu => hu) (gaussianExcessExpMomentBound_pos 2).le
    (fun _ hr => (gaussianExcessLaw_uniform_moments hr).1), ?_⟩
  exact gaussianHalfLineOvershoot_integral_le hX hi hG hx ha (by fun_prop) (by norm_num)
    (fun u _ => sq_nonneg u) (gaussianExcessExpMomentBound_pos 2).le
    (fun _ hr => (gaussianExcessLaw_uniform_moments hr).2.1)


/-- Every family of actual nonnegative-start, nonnegative-drift overshoots is uniformly integrable. -/
theorem gaussianHalfLineOvershoot_uniformIntegrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {x a : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (ha : ∀ i, 0 ≤ a i) :
    UniformIntegrable (fun i => gaussianHalfLineOvershoot X (x i) (a i)) 1 μ := by
  have := hi.isProbabilityMeasure
  apply uniformIntegrable_of_uniform_second_moment
    (fun i => (gaussianHalfLineOvershoot_measurable hX (x i) (a i)).aestronglyMeasurable)
    (gaussianExcessExpMomentBound_pos 2).le
  intro i
  exact gaussianHalfLineOvershoot_lintegral_le hX hi hG (hx i) (ha i)
    (f := fun u => ENNReal.ofReal (u^2)) (by fun_prop) (by norm_num) ENNReal.ofReal_ne_top
    (fun r hr => by
      have hm := (gaussianExcessLaw_uniform_moments hr).2.1
      rw [← ofReal_integral_eq_lintegral_ofReal hm.1 (ae_of_all _ (fun u => sq_nonneg u))]
      exact ENNReal.ofReal_le_ofReal hm.2)

/-- The actual small-drift overshoot converges in mean, justified by its uniform second moment. -/
theorem gaussianHalfLineOvershoot_mean_convergence
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℕ → ℝ} {w : ℝ} (hx : ∀ n, 0 ≤ x n) (ha : ∀ n, 0 ≤ a n)
    (hxlim : Tendsto x atTop (𝓝 w)) (halim : Tendsto a atTop (𝓝 0)) (hw : 0 ≤ w) :
    Integrable (gaussianHalfLineOvershoot X w 0) μ ∧
      Tendsto (fun n => ∫ ω, gaussianHalfLineOvershoot X (x n) (a n) ω ∂μ) atTop
        (𝓝 (∫ ω, gaussianHalfLineOvershoot X w 0 ω ∂μ)) := by
  have := hi.isProbabilityMeasure
  have hui := gaussianHalfLineOvershoot_uniformIntegrable hX hi hG hx ha
  have hc := (gaussianHalfLine_small_drift_ae hX hi hG hxlim halim (Eventually.of_forall hx) hw).mono
    (fun _ h => h.2)
  have hg := hui.integrable_of_ae_tendsto hc
  refine ⟨hg, tendsto_integral_of_L1' _ hg.aestronglyMeasurable
    (Eventually.of_forall (fun n => (hui.memLp n).integrable le_rfl)) ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl (by norm_num)
    (fun n => (gaussianHalfLineOvershoot_measurable hX (x n) (a n)).aestronglyMeasurable)
    (hui.memLp_of_ae_tendsto hc) hui.2.1 hc


/-- The actual Gaussian descending-overshoot renewal potential appearing in the paper. -/
def gaussianRenewalPotential (X : ℕ → Ω → ℝ) (μ : Measure Ω) (w : ℝ) : ℝ :=
  w + ∫ ω, gaussianHalfLineOvershoot X w 0 ω ∂μ

/-- Continuity of the true renewal potential on its nonnegative domain. -/
theorem gaussianRenewalPotential_continuousOn
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ContinuousOn (gaussianRenewalPotential X μ) (Ici 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_iff_seqContinuous.mpr
  intro x w hx
  have hc : Tendsto (fun n => (x n : ℝ)) atTop (𝓝 (w : ℝ)) :=
    continuous_subtype_val.tendsto w |>.comp hx
  have hm := (gaussianHalfLineOvershoot_mean_convergence hX hi hG (fun n => (x n).property)
    (fun _ => le_refl (0 : ℝ)) hc tendsto_const_nhds w.property).2
  exact hc.add hm

end SwingRepair
