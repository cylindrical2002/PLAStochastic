import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LadderHeight
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.StepClass
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Continuity of the ascending ladder density

Bounded continuity of the step density gives each ladder kernel's
continuity. The descending exponential ladder gap pays a uniform
summable majorant on the positive half-line, even at unit discount.
-/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {f : ℝ → ℝ}

theorem continuous_ladderKernel_of_bounded (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
    {B : ℝ} (hfB : ∀ y, f y ≤ B) (A : Set ℝ) (n : ℕ) :
    Continuous (ladderKernel ρ f A n) := by
  apply continuous_of_dominated (bound := fun _ => B)
  · intro h
    exact (hf.measurable.comp (measurable_const.sub (measurable_partialSum n))).aestronglyMeasurable
  · intro h
    exact Eventually.of_forall fun ω => by rw [Real.norm_of_nonneg (hf0 _)]; exact hfB _
  · exact integrable_const _
  · exact Eventually.of_forall fun ω => hf.comp (continuous_id.sub continuous_const)

theorem integral_survival_exp_Ioi_integrable {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) :
    IntegrableOn (fun ω => Real.exp (θ * partialSum n ω))
      {ω | (n : ℕ∞) < firstEntry (Ioi 0) ω} (pathLaw ρ) := by
  apply (integrable_const (1 : ℝ)).mono'
    (by fun_prop : AEStronglyMeasurable (fun ω => Real.exp (θ * partialSum n ω))
      ((pathLaw ρ).restrict {ω | (n : ℕ∞) < firstEntry (Ioi 0) ω}))
  refine (ae_restrict_iff' (measurableSet_coe_lt_firstEntry measurableSet_Ioi n)).mpr
    (Eventually.of_forall fun ω hω => ?_)
  have hS : partialSum n ω ≤ 0 := by
    rcases partialSum_mem_of_lt_firstEntry hω with h | h
    · exact not_lt.mp h
    · exact h.le
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonneg_of_nonpos hθ hS

theorem continuousOn_ladderDensity_asc (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
    {B D θ : ℝ} (hfB : ∀ y, f y ≤ B) (hD : 0 ≤ D) (hθ : 0 ≤ θ)
    (hfE : ∀ y, 0 < y → f y ≤ D * Real.exp (-θ * y))
    (hgap : expEntryMass ρ (Iic 0) θ < 1) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    ContinuousOn (ladderDensity ρ f (Ioi 0) s) (Ioi 0) := by
  let d : ℕ → ℝ := fun n => ∫ ω in {ω | (n : ℕ∞) < firstEntry (Ioi 0) ω},
    Real.exp (θ * partialSum n ω) ∂pathLaw ρ
  have hd0 : ∀ n, 0 ≤ d n := fun _ => integral_nonneg fun _ => (Real.exp_pos _).le
  have hd : Summable d := by
    apply summable_of_sum_range_le hd0
    intro N
    simpa only [compl_Iic] using sum_survival_exp_le (ρ := ρ) measurableSet_Iic isLadderSet_Iic
      (fun y hy => mul_nonpos_of_nonneg_of_nonpos hθ hy) hgap N
  have hb : ∀ n y, y ∈ Ioi (0 : ℝ) → ladderKernel ρ f (Ioi 0) n y ≤ D * d n := by
    intro n y hy
    change 0 < y at hy
    rw [ladderKernel, show D * d n = ∫ ω in {ω | (n : ℕ∞) < firstEntry (Ioi 0) ω},
      D * Real.exp (θ * partialSum n ω) ∂pathLaw ρ from (integral_const_mul _ _).symm]
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => hf0 _)
      ((integral_survival_exp_Ioi_integrable hθ n).const_mul D)
    refine (ae_restrict_iff' (measurableSet_coe_lt_firstEntry measurableSet_Ioi n)).mpr
      (Eventually.of_forall fun ω hω => ?_)
    have hS : partialSum n ω ≤ 0 := by
      rcases partialSum_mem_of_lt_firstEntry hω with h | h
      · exact not_lt.mp h
      · exact h.le
    calc
      _ ≤ D * Real.exp (-θ * (y - partialSum n ω)) := hfE _ (by linarith [hy])
      _ ≤ D * Real.exp (θ * partialSum n ω) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hy])) hD
  have hc : ContinuousOn (fun y => ∑' n : ℕ, s ^ (n + 1) *
      (ladderKernel ρ f (Ioi 0) n y : ℂ)) (Ioi 0) := by
    apply continuousOn_tsum (fun n => (continuous_const.mul
      (continuous_ofReal.comp (continuous_ladderKernel_of_bounded hf hf0 hfB (Ioi 0) n))).continuousOn)
      (hd.mul_left D)
    intro n y hy
    dsimp only [Pi.mul_apply, Function.comp_apply]
    rw [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg (ladderKernel_nonneg hf0 _ _)]
    calc
      _ ≤ 1 * ladderKernel ρ f (Ioi 0) n y :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hs) (ladderKernel_nonneg hf0 _ _)
      _ ≤ D * d n := by rw [one_mul]; exact hb n y hy
  apply hc.congr
  intro y hy
  exact indicator_of_mem hy _

end PGM.WienerHopf
