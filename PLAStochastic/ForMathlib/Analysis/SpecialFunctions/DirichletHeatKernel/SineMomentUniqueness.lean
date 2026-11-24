import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.DirichletHeatKernel.SineSeries
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Uniqueness from Dirichlet sine moments

A positive sine weight converts sine observations into polynomial moments of a
cosine pushforward. Compact polynomial approximation identifies that pushforward;
the inverse cosine and the inverse positive weight then recover the original measure.
No positivity of a candidate density or completeness assertion is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem integrable_of_ae_mem_compact_interval {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f μ := by
  have h := hf.integrableOn_Icc (μ := μ) (a := a) (b := b)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h

/-- Finite measures with a common compact interval of support are determined by their moments. -/
theorem measure_eq_of_compact_moments {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) (hν : ∀ᵐ x ∂ν, x ∈ Icc a b)
    (hm : ∀ n : ℕ, ∫ x : ℝ, x ^ n ∂μ = ∫ x : ℝ, x ^ n ∂ν) : μ = ν := by
  have hp : ∀ p : Polynomial ℝ, ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [Polynomial.eval_add]
      rw [integral_add (integrable_of_ae_mem_compact_interval hμ (by fun_prop))
          (integrable_of_ae_mem_compact_interval hμ (by fun_prop)),
        integral_add (integrable_of_ae_mem_compact_interval hν (by fun_prop))
          (integrable_of_ae_mem_compact_interval hν (by fun_prop)), hp, hq]
    | monomial n c => simp only [Polynomial.eval_monomial, integral_const_mul, hm]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hbound : ∀ ε : ℝ, 0 < ε →
      |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ ε * (μ.real univ + ν.real univ) := by
    intro ε hε
    obtain ⟨p, hpa⟩ := exists_polynomial_near_of_continuousOn a b f f.continuous.continuousOn ε hε
    have hμb : |(∫ x, f x ∂μ) - ∫ x, p.eval x ∂μ| ≤ ε * μ.real univ := by
      rw [← integral_sub (f.integrable μ) (integrable_of_ae_mem_compact_interval hμ (by fun_prop))]
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le_const
      filter_upwards [hμ] with x hx
      simpa only [Real.norm_eq_abs, abs_sub_comm] using (hpa x hx).le
    have hνb : |(∫ x, p.eval x ∂ν) - ∫ x, f x ∂ν| ≤ ε * ν.real univ := by
      rw [← integral_sub (integrable_of_ae_mem_compact_interval hν (by fun_prop)) (f.integrable ν)]
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le_const
      filter_upwards [hν] with x hx
      simpa only [Real.norm_eq_abs] using (hpa x hx).le
    have ht := abs_sub_le ((∫ x, f x ∂μ)) (∫ x, p.eval x ∂μ) (∫ x, f x ∂ν)
    rw [hp p] at hμb ht
    nlinarith
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  by_contra hn
  have hd : 0 < |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| := lt_of_not_ge hn
  have hmass : 0 ≤ μ.real univ + ν.real univ := add_nonneg measureReal_nonneg measureReal_nonneg
  have hb := hbound (|(∫ x, f x ∂μ) - ∫ x, f x ∂ν| /
    (2 * (μ.real univ + ν.real univ + 1))) (by positivity)
  have he : |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| /
      (2 * (μ.real univ + ν.real univ + 1)) * (2 * (μ.real univ + ν.real univ + 1)) =
      |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| := by field_simp
  nlinarith

private theorem integrable_cos_pow_mul_sin (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ℝ) (n k : ℕ) :
    Integrable (fun x : ℝ => Real.cos (c * x) ^ n * Real.sin (k * (c * x))) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [] with x
  simp only [Real.norm_eq_abs, abs_mul, abs_pow]
  exact (mul_le_mul (pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _))
    (Real.abs_sin_le_one _) (abs_nonneg _) (by positivity)).trans_eq (one_mul 1)

private theorem cos_sin_nat_identity (y : ℝ) (k : ℕ) :
    Real.cos y * Real.sin (((k : ℝ) + 1) * y) =
      (Real.sin (((k : ℝ) + 2) * y) + Real.sin ((k : ℝ) * y)) / 2 := by
  rw [show ((k : ℝ) + 2) * y = ((k : ℝ) + 1) * y + y by ring,
    show (k : ℝ) * y = ((k : ℝ) + 1) * y - y by ring,
    Real.sin_add, Real.sin_sub]
  ring

private theorem cos_pow_sine_moments {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c : ℝ) (hm : ∀ k : ℕ, ∫ x, Real.sin (((k : ℝ) + 1) * (c * x)) ∂μ =
      ∫ x, Real.sin (((k : ℝ) + 1) * (c * x)) ∂ν) :
    ∀ n k : ℕ, ∫ x, Real.cos (c * x) ^ n * Real.sin ((k : ℝ) * (c * x)) ∂μ =
      ∫ x, Real.cos (c * x) ^ n * Real.sin ((k : ℝ) * (c * x)) ∂ν := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => simp
    | succ k => simpa using hm k
  | succ n ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      have he : (fun x : ℝ => Real.cos (c * x) ^ (n + 1) *
          Real.sin (((k + 1 : ℕ) : ℝ) * (c * x))) =
          (fun x : ℝ => (Real.cos (c * x) ^ n * Real.sin (((k + 2 : ℕ) : ℝ) * (c * x)) +
            Real.cos (c * x) ^ n * Real.sin ((k : ℝ) * (c * x))) / 2) := by
        funext x
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ]
        rw [mul_assoc, cos_sin_nat_identity]
        ring
      rw [he, integral_div, integral_div,
        integral_add (integrable_cos_pow_mul_sin μ c n (k + 2))
          (integrable_cos_pow_mul_sin μ c n k),
        integral_add (integrable_cos_pow_mul_sin ν c n (k + 2))
          (integrable_cos_pow_mul_sin ν c n k), ih (k + 2), ih k]

private def sineWeightedMeasure (μ : Measure ℝ) (c : ℝ) : Measure ℝ :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.sin (c * x)))

private theorem finite_sineWeightedMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) :
    IsFiniteMeasure (sineWeightedMeasure μ c) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc
    (∫⁻ x, ENNReal.ofReal (Real.sin (c * x)) ∂μ) ≤ ∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_one.mpr (Real.sin_le_one _)
    _ < ∞ := by simp

private theorem sineWeighted_cos_moment (μ : Measure ℝ) (c : ℝ)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ Real.sin (c * x)) (n : ℕ) :
    (∫ y : ℝ, y ^ n ∂(sineWeightedMeasure μ c).map (fun x => Real.cos (c * x))) =
      ∫ x : ℝ, Real.cos (c * x) ^ n * Real.sin (c * x) ∂μ := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  unfold sineWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hμ] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]

private theorem measure_eq_of_cos_map {μ ν : Measure ℝ} {c : ℝ} (hc : 0 < c)
    (hμ : ∀ᵐ x ∂μ, c * x ∈ Icc 0 Real.pi) (hν : ∀ᵐ x ∂ν, c * x ∈ Icc 0 Real.pi)
    (hm : μ.map (fun x => Real.cos (c * x)) = ν.map (fun x => Real.cos (c * x))) : μ = ν := by
  have hrec (ρ : Measure ℝ) (hρ : ∀ᵐ x ∂ρ, c * x ∈ Icc 0 Real.pi) :
      (ρ.map (fun x => Real.cos (c * x))).map (fun y => Real.arccos y / c) = ρ := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    calc
      _ = ρ.map id := by
        apply Measure.map_congr
        filter_upwards [hρ] with x hx
        dsimp only [Function.comp_apply, id_eq]
        rw [Real.arccos_cos hx.1 hx.2]
        field_simp
      _ = ρ := Measure.map_id
  rw [← hrec μ hμ, hm, hrec ν hν]

/-- All Dirichlet sine moments determine a finite measure supported inside the interval.
The open support condition excludes invisible atoms at the two endpoints. -/
theorem measure_eq_of_sine_moments {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {r : ℝ} (hr : 0 < r)
    (hμ : ∀ᵐ x ∂μ, x ∈ Ioo 0 r) (hν : ∀ᵐ x ∂ν, x ∈ Ioo 0 r)
    (hm : ∀ n : ℕ, ∫ x, Real.sin (heatFrequency r n * x) ∂μ =
      ∫ x, Real.sin (heatFrequency r n * x) ∂ν) : μ = ν := by
  let c := Real.pi / r
  have hc : 0 < c := div_pos Real.pi_pos hr
  have hangle {x : ℝ} (hx : x ∈ Ioo 0 r) : c * x ∈ Ioo 0 Real.pi := by
    constructor
    · exact mul_pos hc hx.1
    · calc
        c * x < c * r := mul_lt_mul_of_pos_left hx.2 hc
        _ = Real.pi := by dsimp [c]; field_simp
  have hsμ : ∀ᵐ x ∂μ, 0 < Real.sin (c * x) := hμ.mono (fun _ hx => Real.sin_pos_of_mem_Ioo (hangle hx))
  have hsν : ∀ᵐ x ∂ν, 0 < Real.sin (c * x) := hν.mono (fun _ hx => Real.sin_pos_of_mem_Ioo (hangle hx))
  have hm' : ∀ k : ℕ, ∫ x, Real.sin (((k : ℝ) + 1) * (c * x)) ∂μ =
      ∫ x, Real.sin (((k : ℝ) + 1) * (c * x)) ∂ν := by
    intro k
    simpa only [heatFrequency, mul_assoc] using hm k
  let := finite_sineWeightedMeasure μ c
  let := finite_sineWeightedMeasure ν c
  have hmap : (sineWeightedMeasure μ c).map (fun x => Real.cos (c * x)) =
      (sineWeightedMeasure ν c).map (fun x => Real.cos (c * x)) := by
    apply measure_eq_of_compact_moments (a := -1) (b := 1)
    · apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
      exact Eventually.of_forall (fun x => ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    · apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
      exact Eventually.of_forall (fun x => ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    · intro n
      rw [sineWeighted_cos_moment μ c (hsμ.mono (fun _ hx => hx.le)),
        sineWeighted_cos_moment ν c (hsν.mono (fun _ hx => hx.le))]
      simpa using cos_pow_sine_moments c hm' n 1
  have hweight : sineWeightedMeasure μ c = sineWeightedMeasure ν c := by
    apply measure_eq_of_cos_map hc _ _ hmap
    · exact (withDensity_absolutelyContinuous μ _).ae_le
        (hμ.mono (fun _ hx => Ioo_subset_Icc_self (hangle hx)))
    · exact (withDensity_absolutelyContinuous ν _).ae_le
        (hν.mono (fun _ hx => Ioo_subset_Icc_self (hangle hx)))
  have hundoμ := withDensity_inv_same (μ := μ)
    (show Measurable (fun x : ℝ => ENNReal.ofReal (Real.sin (c * x))) by fun_prop)
    (hsμ.mono (fun _ hx => (ENNReal.ofReal_pos.mpr hx).ne'))
    (Eventually.of_forall (fun _ => ENNReal.ofReal_ne_top))
  have hundoν := withDensity_inv_same (μ := ν)
    (show Measurable (fun x : ℝ => ENNReal.ofReal (Real.sin (c * x))) by fun_prop)
    (hsν.mono (fun _ hx => (ENNReal.ofReal_pos.mpr hx).ne'))
    (Eventually.of_forall (fun _ => ENNReal.ofReal_ne_top))
  rw [← hundoμ, ← hundoν]
  exact congrArg (fun ρ : Measure ℝ => ρ.withDensity
    (fun x => (ENNReal.ofReal (Real.sin (c * x)))⁻¹)) hweight

end BrownianAffine
