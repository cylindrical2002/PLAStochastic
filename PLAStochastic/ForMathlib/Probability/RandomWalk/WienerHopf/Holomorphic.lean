import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Strip
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphy of the ladder transforms in the space variable

`differentiableOn_entryTransform`: if the ladder series is dominated by a real exponential
ladder series `∑ E[e^{θ S_n}; τ_B = n] < ∞` uniformly over the real parts in an open set `I`,
then `z ↦ E[s^{τ_B} e^{z S_{τ_B}}; τ_B < ∞]` is complex differentiable (hence analytic) on
`{z | Re z ∈ I}`. Under the strip hypotheses of `Strip`:

* `differentiableOn_ascTransform`: `χ₊(s, ·)` is holomorphic on `{Re z < a}`;
* `differentiableOn_descTransform`: `χ₋(s, ·)` is holomorphic on `{Re z > -a}`;
* `differentiableOn_stepTransform`: `φ` is holomorphic on `{|Re z| < a}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Finset
open scoped ENNReal

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {B : Set ℝ}

theorem differentiableOn_entryTransform (hBm : MeasurableSet B) {s : ℂ} (hs : ‖s‖ ≤ 1)
    {I : Set ℝ} (hI : IsOpen I) {θ : ℝ} (hdom : ∀ t ∈ I, ∀ x ∈ B, t * x ≤ θ * x)
    (hM : Integrable (fun y : ℝ => Real.exp (θ * y)) ρ)
    (he : Summable fun n : ℕ => ∫ ω in {ω | firstEntry B ω = n},
      Real.exp (θ * partialSum n ω) ∂pathLaw ρ) :
    DifferentiableOn ℂ (fun z => entryTransform ρ B s z) {z | z.re ∈ I} := by
  set U : Set ℂ := {z | z.re ∈ I}
  have hU : IsOpen U := hI.preimage Complex.continuous_re
  have hθint : ∀ n : ℕ, IntegrableOn (fun ω => Real.exp (θ * partialSum n ω))
      {ω | firstEntry B ω = n} (pathLaw ρ) := fun n =>
    (integrable_exp_partialSum hM n).1.integrableOn
  -- each real exponent in `I` is integrable on `{τ_B = n}`
  have hexp : ∀ n : ℕ, ∀ t ∈ I, Integrable (fun ω => Real.exp (t * partialSum n ω))
      ((pathLaw ρ).restrict {ω | firstEntry B ω = n}) := by
    intro n t ht
    refine (hθint n).mono' (by fun_prop) ((ae_restrict_iff' (measurableSet_firstEntry_eq hBm n)).mpr
      (Filter.Eventually.of_forall fun ω hω => ?_))
    simp only [mem_ofPred_eq] at hω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    exact hdom t ht _ (firstEntry_eq_coe_iff.mp hω).2.1
  have hsub : ∀ n : ℕ, U ⊆ {z | z.re ∈ interior (integrableExpSet (partialSum n)
      ((pathLaw ρ).restrict {ω | firstEntry B ω = n}))} := by
    intro n z hz
    exact interior_maximal (fun t ht => hexp n t ht) hI hz
  have hF : ∀ n : ℕ, DifferentiableOn ℂ (fun z => s ^ n * entryCoeff ρ B z n) U := by
    intro n
    have h := (differentiableOn_complexMGF (X := partialSum n)
      (μ := (pathLaw ρ).restrict {ω | firstEntry B ω = n})).mono (hsub n)
    exact (h.const_mul (s ^ n)).congr fun z _ => rfl
  have hbound : ∀ (n : ℕ), ∀ z ∈ U, ‖s ^ n * entryCoeff ρ B z n‖ ≤
      ∫ ω in {ω | firstEntry B ω = n}, Real.exp (θ * partialSum n ω) ∂pathLaw ρ := by
    intro n z hz
    rw [norm_mul, norm_pow]
    calc ‖s‖ ^ n * ‖entryCoeff ρ B z n‖ ≤ 1 * ‖entryCoeff ρ B z n‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hs) (norm_nonneg _)
      _ ≤ ∫ ω in {ω | firstEntry B ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ := by
          rw [one_mul]; exact norm_integral_le_integral_norm _
      _ ≤ _ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (hθint n) ((ae_restrict_iff' (measurableSet_firstEntry_eq hBm n)).mpr
              (Filter.Eventually.of_forall fun ω hω => ?_))
          simp only [mem_ofPred_eq] at hω
          show ‖cexp (z * partialSum n ω)‖ ≤ Real.exp (θ * partialSum n ω)
          rw [norm_cexp_mul_ofReal, Real.exp_le_exp]
          exact hdom _ hz _ (firstEntry_eq_coe_iff.mp hω).2.1
  have hsum := differentiableOn_tsum_of_summable_norm he hF hU hbound
  refine hsum.congr fun z hz => ?_
  have hint : ∀ n : ℕ, IntegrableOn (fun ω => cexp (z * partialSum n ω))
      {ω | firstEntry B ω = n} (pathLaw ρ) := by
    intro n
    refine (integrable_norm_iff
      (by fun_prop : Measurable fun ω => cexp (z * partialSum n ω)).aestronglyMeasurable).mp ?_
    simp_rw [norm_cexp_mul_ofReal]
    exact hexp n z.re hz
  exact entryTransform_eq_tsum hBm hint
    (summable_entry_of_le hBm hs (fun x hx => hdom _ hz x hx) hM he)

/-- Under the strip hypotheses, `χ₊(s, ·)` is holomorphic on `{Re z < a}` for `‖s‖ ≤ 1`. -/
theorem differentiableOn_ascTransform {a : ℝ} (ha : 0 ≤ a)
    (hpos : Integrable (fun y : ℝ => Real.exp (a * y)) ρ)
    (hdesc : expEntryMass ρ (Iic 0) a < 1) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    DifferentiableOn ℂ (fun z => ascTransform ρ s z) {z | z.re ∈ Iio a} := by
  have hθ : ∀ x ∈ Iic (0 : ℝ), a * x ≤ 0 := fun x hx => mul_nonpos_of_nonneg_of_nonpos ha hx
  obtain ⟨he, -, -⟩ := expEntryMass_compl_le (ρ := ρ) measurableSet_Iic isLadderSet_Iic hθ
    hdesc hpos
  rw [compl_Iic] at he
  exact differentiableOn_entryTransform measurableSet_Ioi hs isOpen_Iio
    (fun t ht x hx => mul_le_mul_of_nonneg_right (le_of_lt (show t < a from ht))
      (le_of_lt (show (0 : ℝ) < x from hx))) hpos he

/-- Under the strip hypotheses, `χ₋(s, ·)` is holomorphic on `{Re z > -a}` for `‖s‖ ≤ 1`. -/
theorem differentiableOn_descTransform {a : ℝ} (ha : 0 ≤ a)
    (hneg : Integrable (fun y : ℝ => Real.exp (-a * y)) ρ)
    (hasc : expEntryMass ρ (Ioi 0) (-a) < 1) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    DifferentiableOn ℂ (fun z => descTransform ρ s z) {z | z.re ∈ Ioi (-a)} := by
  have hθ : ∀ x ∈ Ioi (0 : ℝ), -a * x ≤ 0 := fun x hx => by
    have := mul_nonneg ha (le_of_lt (show (0 : ℝ) < x from hx)); linarith
  obtain ⟨he, -, -⟩ := expEntryMass_compl_le (ρ := ρ) measurableSet_Ioi isLadderSet_Ioi hθ
    hasc hneg
  rw [compl_Ioi] at he
  exact differentiableOn_entryTransform measurableSet_Iic hs isOpen_Ioi
    (fun t ht x hx => mul_le_mul_of_nonpos_right (le_of_lt (show -a < t from ht))
      (show x ≤ 0 from hx)) hneg he

omit [IsProbabilityMeasure ρ] in
/-- `φ` is holomorphic on the strip `{|Re z| < a}` when `∫ e^{± a y} dρ < ∞`. -/
theorem differentiableOn_stepTransform {a : ℝ}
    (hpos : Integrable (fun y : ℝ => Real.exp (a * y)) ρ)
    (hneg : Integrable (fun y : ℝ => Real.exp (-a * y)) ρ) :
    DifferentiableOn ℂ (stepTransform ρ) {z | z.re ∈ Ioo (-a) a} := by
  have hsub : {z : ℂ | z.re ∈ Ioo (-a) a} ⊆ {z | z.re ∈ interior (integrableExpSet id ρ)} := by
    intro z hz
    refine interior_maximal (fun t ht => ?_) isOpen_Ioo hz
    have h := integrable_cexp_of_abs_re_le (ρ := ρ) hpos hneg (z := (t : ℂ))
      (by simpa [abs_le] using And.intro ht.1.le ht.2.le)
    have h' := integrable_cexp_iff_exp_re.mp h
    simpa [integrableExpSet] using h'
  exact (differentiableOn_complexMGF (X := id) (μ := ρ)).mono hsub

end PGM.WienerHopf
