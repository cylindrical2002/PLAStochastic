import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Occupation
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Ladder-density envelopes uniform over a class of step laws

The consumers' class: increments `Y = 1 - X + μ` where `X > 0` has a density
`f_X ≤ D e^{-θ x}`, mean one and second central moment at most `v`, and `|μ| ≤ δ`
(`IsGapLaw ν f_X D θ v`, step law `shiftedStep ν μ = Law(1 - X + μ)`).

* `shiftedStep_eq_withDensity`: `Y` has the density `f(y) = f_X(1 + μ - y)`, with the envelopes
  `f(y) ≤ D e^{θ(1+δ)} e^{-θ y}` on `y > 0` and `f(y) ≤ D e^{θ δ} e^{θ y}` on `y ≤ 0`.
* `IsGapLaw.measureReal_Iic_ge`, `IsGapLaw.measureReal_Ici_ge`: with `c = 1/(16 D) - t > 0`,
  `P(X ≤ 1 - t) ≥ c` and `P(X ≥ 1 + t) ≥ c² / v` (from `E|X - 1| ≥ 1/(8D)`).
* `norm_ladderDensity_asc_le_of_gapLaw`, `norm_ladderDensity_desc_le_of_gapLaw`: if
  `δ ≤ 1/(64 D)`, the discounted (`‖s‖ ≤ 1`) strict ascending and weak descending ladder height
  densities of `Y` satisfy
  `‖g₊(h)‖ ≤ ‖s‖ · 1024 D³ v e^{θ(1+δ)} / (1 - e^{-θ/(64D)}) · e^{-θ h}` and
  `‖g₋(h)‖ ≤ ‖s‖ · 32 D² e^{θ δ} / (1 - e^{-θ/(64D)}) · e^{θ h}`.
  The lower variance bound of the class is not needed.
* `preEntryOccupation_asc_Ioc_le_of_gapLaw`: the pre-ladder occupation measure of `Y` has
  `u₋((x - 1, x]) ≤ e^{θ} · 1024 D² v / (1 - e^{-θ/(64D)})` for every `x`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Finset
open scoped ENNReal

namespace PGM.WienerHopf

/-- The class of gap laws: `ν` is a probability law with a density `fX` vanishing on `(-∞, 0]`,
`fX(x) ≤ D e^{-θ x}` on `(0, ∞)`, mean one and `∫ (x - 1)² dν ≤ v`. -/
structure IsGapLaw (ν : Measure ℝ) (fX : ℝ → ℝ) (D θ v : ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure ν
  eq_withDensity : ν = volume.withDensity fun x => ENNReal.ofReal (fX x)
  measurable : Measurable fX
  nonneg : ∀ x, 0 ≤ fX x
  eq_zero_of_nonpos : ∀ x, x ≤ 0 → fX x = 0
  le_exp : ∀ x, 0 < x → fX x ≤ D * Real.exp (-θ * x)
  integrable_sq : Integrable (fun x => (x - 1) ^ 2) ν
  integral_id : ∫ x, x ∂ν = 1
  integral_sq_le : ∫ x, (x - 1) ^ 2 ∂ν ≤ v

/-- The step law `Law(1 - X + μ)`. -/
def shiftedStep (ν : Measure ℝ) (μ : ℝ) : Measure ℝ :=
  ν.map fun x => 1 - x + μ

variable {ν : Measure ℝ} {fX : ℝ → ℝ} {D θ v : ℝ}

namespace IsGapLaw

theorem le_D (hX : IsGapLaw ν fX D θ v) (hθ : 0 ≤ θ) (hD : 0 ≤ D) (x : ℝ) : fX x ≤ D := by
  rcases le_or_gt x 0 with hx | hx
  · rw [hX.eq_zero_of_nonpos x hx]; exact hD
  · calc fX x ≤ D * Real.exp (-θ * x) := hX.le_exp x hx
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
          (by nlinarith)) hD
      _ = D := mul_one D

theorem ae_pos (hX : IsGapLaw ν fX D θ v) : ∀ᵐ x ∂ν, 0 < x := by
  rw [hX.eq_withDensity, ae_withDensity_iff (f := fun x => ENNReal.ofReal (fX x))
    (ENNReal.measurable_ofReal.comp hX.measurable)]
  refine Filter.Eventually.of_forall fun x hx => ?_
  by_contra hle
  push Not at hle
  exact hx (by rw [hX.eq_zero_of_nonpos x hle, ENNReal.ofReal_zero])

theorem integrable_sub_one (hX : IsGapLaw ν fX D θ v) : Integrable (fun x => x - 1) ν := by
  have := hX.isProbabilityMeasure
  refine ((integrable_const 1).add hX.integrable_sq).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  show |x - 1| ≤ 1 + (x - 1) ^ 2
  nlinarith [abs_nonneg (x - 1), sq_abs (x - 1), sq_nonneg (|x - 1| - 1)]

theorem integral_sub_one (hX : IsGapLaw ν fX D θ v) : ∫ x, (x - 1) ∂ν = 0 := by
  have := hX.isProbabilityMeasure
  have hid : Integrable (fun x : ℝ => x) ν :=
    (hX.integrable_sub_one.add (integrable_const (1 : ℝ))).congr
      (Filter.Eventually.of_forall fun x => by simp)
  rw [integral_sub hid (integrable_const 1), hX.integral_id]
  simp

/-- A density bounded by `D` puts mass at most `2 D η` near any point. -/
theorem measureReal_Ioo_le (hX : IsGapLaw ν fX D θ v) (hθ : 0 ≤ θ) (hD : 0 ≤ D) (a η : ℝ)
    (hη : 0 ≤ η) : ν.real (Ioo (a - η) (a + η)) ≤ 2 * D * η := by
  have h : ν (Ioo (a - η) (a + η)) ≤ ENNReal.ofReal (2 * D * η) := by
    rw [hX.eq_withDensity, withDensity_apply _ measurableSet_Ioo]
    calc ∫⁻ x in Ioo (a - η) (a + η), ENNReal.ofReal (fX x)
        ≤ ∫⁻ _ in Ioo (a - η) (a + η), ENNReal.ofReal D :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hX.le_D hθ hD x)
      _ = ENNReal.ofReal D * ENNReal.ofReal (2 * η) := by
          rw [setLIntegral_const, Real.volume_Ioo]
          congr 1; congr 1; ring
      _ = ENNReal.ofReal (2 * D * η) := by
          rw [← ENNReal.ofReal_mul hD]; congr 1; ring
  have hfin : ENNReal.ofReal (2 * D * η) ≠ ∞ := ENNReal.ofReal_ne_top
  calc ν.real (Ioo (a - η) (a + η)) ≤ (ENNReal.ofReal (2 * D * η)).toReal :=
        ENNReal.toReal_mono hfin h
    _ = 2 * D * η := ENNReal.toReal_ofReal (by positivity)

/-- `E|X - 1| ≥ 1/(8D)` for a density bounded by `D`. -/
theorem integral_abs_sub_one_ge (hX : IsGapLaw ν fX D θ v) (hθ : 0 ≤ θ) (hD : 0 < D) :
    1 / (8 * D) ≤ ∫ x, |x - 1| ∂ν := by
  have := hX.isProbabilityMeasure
  set η : ℝ := 1 / (4 * D)
  have hη : 0 < η := by positivity
  have hI : ν.real (Ioo (1 - η) (1 + η)) ≤ 1 / 2 := by
    have := hX.measureReal_Ioo_le hθ hD.le 1 η hη.le
    have h2 : 2 * D * η = 1 / 2 := by simp only [η]; field_simp; ring
    linarith
  have hcompl : ν.real (Ioo (1 - η) (1 + η))ᶜ = 1 - ν.real (Ioo (1 - η) (1 + η)) := by
    rw [measureReal_compl measurableSet_Ioo, probReal_univ]
  have hle : ∀ x, η * (Ioo (1 - η) (1 + η))ᶜ.indicator (fun _ => (1 : ℝ)) x ≤ |x - 1| := by
    intro x
    by_cases hx : x ∈ Ioo (1 - η) (1 + η)
    · rw [indicator_of_notMem (by simpa using hx), mul_zero]; exact abs_nonneg _
    · rw [indicator_of_mem (by simpa using hx), mul_one]
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
      rcases hx with hx | hx
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
  have hint : Integrable (fun x => |x - 1|) ν := hX.integrable_sub_one.abs
  calc 1 / (8 * D) = η * (1 / 2) := by simp only [η]; field_simp; ring
    _ ≤ η * ν.real (Ioo (1 - η) (1 + η))ᶜ := by
        rw [hcompl]; exact mul_le_mul_of_nonneg_left (by linarith) hη.le
    _ = ∫ x, η * (Ioo (1 - η) (1 + η))ᶜ.indicator (fun _ => (1 : ℝ)) x ∂ν := by
        rw [integral_const_mul, integral_indicator measurableSet_Ioo.compl, setIntegral_const,
          smul_eq_mul, mul_one]
    _ ≤ ∫ x, |x - 1| ∂ν :=
        integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Ioo.compl
          |>.const_mul η) hint hle

/-- `E (1 - X)⁺ = E (X - 1)⁺ ≥ 1/(16 D)`. -/
theorem integral_pos_part_ge (hX : IsGapLaw ν fX D θ v) (hθ : 0 ≤ θ) (hD : 0 < D) :
    1 / (16 * D) ≤ ∫ x, max (1 - x) 0 ∂ν ∧ 1 / (16 * D) ≤ ∫ x, max (x - 1) 0 ∂ν := by
  have := hX.isProbabilityMeasure
  have habs := hX.integral_abs_sub_one_ge hθ hD
  have h0 := hX.integral_sub_one
  have hint := hX.integrable_sub_one
  have e1 : (fun x : ℝ => max (1 - x) 0) = fun x => (|x - 1| - (x - 1)) / 2 := by
    funext x; rcases le_total x 1 with h | h
    · rw [max_eq_left (by linarith), abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_right (by linarith), abs_of_nonneg (by linarith)]; ring
  have e2 : (fun x : ℝ => max (x - 1) 0) = fun x => (|x - 1| + (x - 1)) / 2 := by
    funext x; rcases le_total x 1 with h | h
    · rw [max_eq_right (by linarith), abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith)]; ring
  rw [e1, e2, integral_div, integral_div, integral_sub hint.abs hint,
    integral_add hint.abs hint, h0]
  have h8 : 1 / (8 * D) = 2 * (1 / (16 * D)) := by field_simp; ring
  constructor <;> linarith

/-- `P(X ≤ 1 - t) ≥ 1/(16 D) - t` for `t ≥ 0`. -/
theorem measureReal_Iic_ge (hX : IsGapLaw ν fX D θ v) (hθ : 0 ≤ θ) (hD : 0 < D) {t : ℝ}
    (ht : 0 ≤ t) : 1 / (16 * D) - t ≤ ν.real (Iic (1 - t)) := by
  have := hX.isProbabilityMeasure
  have h := (hX.integral_pos_part_ge hθ hD).1
  have hle : ∀ᵐ x ∂ν, max (1 - x) 0 ≤ t + (Iic (1 - t)).indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hX.ae_pos] with x hx
    by_cases hxt : x ≤ 1 - t
    · rw [indicator_of_mem (show x ∈ Iic (1 - t) from hxt)]
      exact max_le (by linarith) (by linarith)
    · rw [indicator_of_notMem (show x ∉ Iic (1 - t) from hxt), add_zero]
      exact max_le (by push Not at hxt; linarith) ht
  have hint : Integrable (fun x => max (1 - x) 0) ν :=
    (hX.integrable_sub_one.abs).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (le_max_right _ _)]
      exact max_le (by rw [abs_sub_comm]; exact le_abs_self _) (abs_nonneg _))
  have hI : Integrable (fun x => (Iic (1 - t)).indicator (fun _ => (1 : ℝ)) x) ν :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hR : Integrable (fun x => t + (Iic (1 - t)).indicator (fun _ => (1 : ℝ)) x) ν :=
    (integrable_const t).add hI
  have := integral_mono_ae hint hR hle
  rw [integral_add (integrable_const t) hI, integral_const,
    integral_indicator measurableSet_Iic, setIntegral_const] at this
  simp only [probReal_univ, smul_eq_mul, mul_one, one_mul] at this
  linarith

/-- `P(X ≥ 1 + t) ≥ (1/(16 D) - t)² / v` for `0 ≤ t < 1/(16 D)` and `v > 0`. -/
theorem measureReal_Ici_ge (hX : IsGapLaw ν fX D θ v) (hθ : 0 ≤ θ) (hD : 0 < D) (hv : 0 < v)
    {t : ℝ} (ht : 0 ≤ t) (htD : t < 1 / (16 * D)) :
    (1 / (16 * D) - t) ^ 2 / v ≤ ν.real (Ici (1 + t)) := by
  have := hX.isProbabilityMeasure
  set c := 1 / (16 * D) - t
  have hc : 0 < c := by simp only [c]; linarith
  set lam := v / c
  have hlam : 0 < lam := div_pos hv hc
  have h := (hX.integral_pos_part_ge hθ hD).2
  have hle : ∀ x, max (x - 1) 0 ≤ t + (x - 1) ^ 2 / (2 * lam) +
      lam / 2 * (Ici (1 + t)).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    have hsq : 0 ≤ (x - 1) ^ 2 / (2 * lam) := by positivity
    by_cases hxt : 1 + t ≤ x
    · rw [indicator_of_mem (show x ∈ Ici (1 + t) from hxt), mul_one]
      have hamgm : x - 1 ≤ (x - 1) ^ 2 / (2 * lam) + lam / 2 := by
        rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (x - 1 - lam)]
      exact max_le (by linarith) (by positivity)
    · rw [indicator_of_notMem (show x ∉ Ici (1 + t) from hxt), mul_zero, add_zero]
      push Not at hxt
      exact max_le (by linarith) (by linarith)
  have hint : Integrable (fun x => max (x - 1) 0) ν :=
    (hX.integrable_sub_one.abs).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hSq : Integrable (fun x => (x - 1) ^ 2 / (2 * lam)) ν := hX.integrable_sq.div_const _
  have hR1 : Integrable (fun x => t + (x - 1) ^ 2 / (2 * lam)) ν := (integrable_const t).add hSq
  have hR2 : Integrable (fun x => lam / 2 * (Ici (1 + t)).indicator (fun _ => (1 : ℝ)) x) ν :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ici).const_mul _
  have hR : Integrable (fun x => t + (x - 1) ^ 2 / (2 * lam) +
      lam / 2 * (Ici (1 + t)).indicator (fun _ => (1 : ℝ)) x) ν := hR1.add hR2
  have := integral_mono hint hR hle
  rw [integral_add hR1 hR2, integral_add (integrable_const t) hSq, integral_const,
    integral_div, integral_const_mul, integral_indicator measurableSet_Ici, setIntegral_const]
    at this
  simp only [probReal_univ, smul_eq_mul, mul_one, one_mul] at this
  have hv' := hX.integral_sq_le
  set p := ν.real (Ici (1 + t))
  have hdiv : (∫ x, (x - 1) ^ 2 ∂ν) / (2 * lam) ≤ c / 2 := by
    rw [div_le_iff₀ (by positivity)]
    simp only [lam]
    rw [show c / 2 * (2 * (v / c)) = v by field_simp]
    exact hv'
  -- `c ≤ c/2 + (λ/2) p` with `λ = v / c`
  have hmain : c / 2 ≤ lam / 2 * p := by simp only [c] at *; linarith
  rw [div_le_iff₀ hv]
  have : c / 2 * c ≤ lam / 2 * p * c := mul_le_mul_of_nonneg_right hmain hc.le
  have hlc : lam / 2 * p * c = v * p / 2 := by simp only [lam]; field_simp
  nlinarith

end IsGapLaw

/-! ### The shifted step law -/

theorem isProbabilityMeasure_shiftedStep (hX : IsGapLaw ν fX D θ v) (μ : ℝ) :
    IsProbabilityMeasure (shiftedStep ν μ) := by
  have := hX.isProbabilityMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- `Y = 1 - X + μ` has the density `y ↦ fX(1 + μ - y)`. -/
theorem shiftedStep_eq_withDensity (hX : IsGapLaw ν fX D θ v) (μ : ℝ) :
    shiftedStep ν μ = volume.withDensity fun y => ENNReal.ofReal (fX (1 + μ - y)) := by
  have hT : Measurable fun x : ℝ => 1 - x + μ := by fun_prop
  have hfE : Measurable fun x => ENNReal.ofReal (fX x) :=
    ENNReal.measurable_ofReal.comp hX.measurable
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hgT : Measurable fun x => g (1 - x + μ) := hg.comp hT
  have hfE' : Measurable fun y => ENNReal.ofReal (fX (1 + μ - y)) :=
    ENNReal.measurable_ofReal.comp (hX.measurable.comp (by fun_prop))
  rw [shiftedStep, lintegral_map hg hT, hX.eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _ hfE hgT,
    lintegral_withDensity_eq_lintegral_mul _ hfE' hg]
  simp only [Pi.mul_apply]
  rw [← lintegral_sub_left_eq_self (fun y => ENNReal.ofReal (fX (1 + μ - y)) * g y) (1 + μ)]
  refine lintegral_congr fun x => ?_
  rw [show 1 + μ - (1 + μ - x) = x by ring, show 1 - x + μ = 1 + μ - x by ring]

theorem shiftedStep_density_le_pos (hX : IsGapLaw ν fX D θ v) (hθ : 0 ≤ θ) (hD : 0 ≤ D)
    {μ δ : ℝ} (hμ : |μ| ≤ δ) {y : ℝ} (hy : 0 < y) :
    fX (1 + μ - y) ≤ D * Real.exp (θ * (1 + δ)) * Real.exp (-θ * y) := by
  have hy0 := hy.le
  have hμδ := le_of_abs_le hμ
  rcases le_or_gt (1 + μ - y) 0 with h | h
  · rw [hX.eq_zero_of_nonpos _ h]; positivity
  · calc fX (1 + μ - y) ≤ D * Real.exp (-θ * (1 + μ - y)) := hX.le_exp _ h
      _ ≤ D * Real.exp (θ * (1 + δ) + -θ * y) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD
          nlinarith
      _ = _ := by rw [Real.exp_add]; ring

theorem shiftedStep_density_le_nonpos (hX : IsGapLaw ν fX D θ v) (hθ : 0 ≤ θ) (hD : 0 ≤ D)
    {μ δ : ℝ} (hμ : |μ| ≤ δ) {y : ℝ} (hy : y ≤ 0) :
    fX (1 + μ - y) ≤ D * Real.exp (θ * δ) * Real.exp (θ * y) := by
  have hy0 := hy
  have hμδ := neg_le_of_abs_le hμ
  rcases le_or_gt (1 + μ - y) 0 with h | h
  · rw [hX.eq_zero_of_nonpos _ h]; positivity
  · calc fX (1 + μ - y) ≤ D * Real.exp (-θ * (1 + μ - y)) := hX.le_exp _ h
      _ ≤ D * Real.exp (θ * δ + θ * y) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD
          nlinarith
      _ = _ := by rw [Real.exp_add]; ring

/-- The two first-step masses of `Y = 1 - X + μ`, with `b = 1/(64 D)` and `δ ≤ 1/(64 D)`:
`P(Y ≤ -b) ≥ 1/(1024 D² v)` and `P(Y ≥ b) ≥ 1/(32 D)`. -/
theorem shiftedStep_masses (hX : IsGapLaw ν fX D θ v) (hθ : 0 ≤ θ) (hD : 0 < D) (hv : 0 < v)
    {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D)) :
    1 / (1024 * D ^ 2 * v) ≤ (shiftedStep ν μ).real (Iic (-(1 / (64 * D)))) ∧
      1 / (32 * D) ≤ (shiftedStep ν μ).real (Ici (1 / (64 * D))) := by
  have := hX.isProbabilityMeasure
  have hT : Measurable fun x : ℝ => 1 - x + μ := by fun_prop
  have hμ1 := le_of_abs_le hμ
  have hμ2 := neg_le_of_abs_le hμ
  set t := 1 / (32 * D)
  have ht : 0 ≤ t := by positivity
  have htD : t < 1 / (16 * D) := by
    simp only [t]; rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hb : 1 / (64 * D) + δ ≤ t := by
    have : 1 / (64 * D) + 1 / (64 * D) = t := by simp only [t]; field_simp; ring
    linarith
  constructor
  · have hsub : Ici (1 + t) ⊆ (fun x : ℝ => 1 - x + μ) ⁻¹' Iic (-(1 / (64 * D))) := by
      intro x hx
      simp only [Set.mem_Ici] at hx
      simp only [Set.mem_preimage, Set.mem_Iic]
      linarith
    have h1 := hX.measureReal_Ici_ge hθ hD hv ht htD
    have h2 : (1 / (16 * D) - t) ^ 2 / v = 1 / (1024 * D ^ 2 * v) := by
      simp only [t]; field_simp; ring
    rw [shiftedStep, map_measureReal_apply hT measurableSet_Iic]
    calc 1 / (1024 * D ^ 2 * v) = (1 / (16 * D) - t) ^ 2 / v := h2.symm
      _ ≤ ν.real (Ici (1 + t)) := h1
      _ ≤ _ := measureReal_mono hsub
  · have hsub : Iic (1 - t) ⊆ (fun x : ℝ => 1 - x + μ) ⁻¹' Ici (1 / (64 * D)) := by
      intro x hx
      simp only [Set.mem_Iic] at hx
      simp only [Set.mem_preimage, Set.mem_Ici]
      linarith
    have h1 := hX.measureReal_Iic_ge hθ hD ht
    have h2 : 1 / (16 * D) - t = 1 / (32 * D) := by simp only [t]; field_simp; ring
    rw [shiftedStep, map_measureReal_apply hT measurableSet_Ici]
    calc 1 / (32 * D) = 1 / (16 * D) - t := h2.symm
      _ ≤ ν.real (Iic (1 - t)) := h1
      _ ≤ _ := measureReal_mono hsub

/-- The ladder gaps of `Y = 1 - X + μ` are bounded below uniformly over the class. -/
theorem shiftedStep_gaps (hX : IsGapLaw ν fX D θ v) (hθ : 0 < θ) (hD : 0 < D) (hv : 0 < v)
    {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D)) :
    haveI := isProbabilityMeasure_shiftedStep hX μ
    (1 - Real.exp (-(θ / (64 * D)))) / (1024 * D ^ 2 * v) ≤
        1 - expEntryMass (shiftedStep ν μ) (Iic 0) θ ∧
      (1 - Real.exp (-(θ / (64 * D)))) / (32 * D) ≤
        1 - expEntryMass (shiftedStep ν μ) (Ioi 0) (-θ) := by
  have := isProbabilityMeasure_shiftedStep hX μ
  obtain ⟨hm1, hm2⟩ := shiftedStep_masses hX hθ.le hD hv hμ hδ
  have he : 0 ≤ 1 - Real.exp (-(θ / (64 * D))) := by
    rw [sub_nonneg, Real.exp_le_one_iff]; have : 0 < θ / (64 * D) := by positivity
    linarith
  have hθb : θ * (1 / (64 * D)) = θ / (64 * D) := by ring
  constructor
  · have g := one_sub_expEntryMass_Iic_ge (ρ := shiftedStep ν μ) hθ.le
      (b := 1 / (64 * D)) (by positivity)
    rw [hθb] at g
    calc _ = (1 - Real.exp (-(θ / (64 * D)))) * (1 / (1024 * D ^ 2 * v)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm1 he
      _ ≤ _ := g
  · have g := one_sub_expEntryMass_Ioi_ge (ρ := shiftedStep ν μ) hθ.le
      (b := 1 / (64 * D)) (by positivity)
    rw [hθb] at g
    calc _ = (1 - Real.exp (-(θ / (64 * D)))) * (1 / (32 * D)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm2 he
      _ ≤ _ := g

/-- **Class-uniform envelope of the strict ascending ladder density** of `Y = 1 - X + μ`:
`‖g₊(s, h)‖ ≤ ‖s‖ · 1024 D³ v e^{θ(1+δ)} / (1 - e^{-θ/(64D)}) · e^{-θ h}`. -/
theorem norm_ladderDensity_asc_le_of_gapLaw (hX : IsGapLaw ν fX D θ v) (hθ : 0 < θ)
    (hD : 0 < D) (hv : 0 < v) {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D))
    {s : ℂ} (hs : ‖s‖ ≤ 1) (h : ℝ) :
    haveI := isProbabilityMeasure_shiftedStep hX μ
    ‖ladderDensity (shiftedStep ν μ) (fun y => fX (1 + μ - y)) (Ioi 0) s h‖ ≤
      ‖s‖ * (1024 * D ^ 3 * v * Real.exp (θ * (1 + δ)) /
        (1 - Real.exp (-(θ / (64 * D))))) * Real.exp (-θ * h) := by
  have := isProbabilityMeasure_shiftedStep hX μ
  have hgap := (shiftedStep_gaps hX hθ hD hv hμ hδ).1
  have he : 0 < 1 - Real.exp (-(θ / (64 * D))) := by
    rw [sub_pos, Real.exp_lt_one_iff]; have : 0 < θ / (64 * D) := by positivity
    linarith
  have hgap_pos : 0 < 1 - expEntryMass (shiftedStep ν μ) (Iic 0) θ :=
    lt_of_lt_of_le (by positivity) hgap
  have hbound := norm_ladderDensity_asc_le (ρ := shiftedStep ν μ) (f := fun y => fX (1 + μ - y))
    (D := D * Real.exp (θ * (1 + δ))) hθ.le (by linarith) (fun y => hX.nonneg _)
    (fun y hy => shiftedStep_density_le_pos hX hθ.le hD.le hμ hy) hs h
  refine hbound.trans ?_
  have hinv : (1 - expEntryMass (shiftedStep ν μ) (Iic 0) θ)⁻¹ ≤
      1024 * D ^ 2 * v / (1 - Real.exp (-(θ / (64 * D)))) := by
    rw [inv_le_comm₀ hgap_pos (by positivity), inv_div]
    exact hgap
  have hfinal : ‖s‖ * (D * Real.exp (θ * (1 + δ))) *
      (1 - expEntryMass (shiftedStep ν μ) (Iic 0) θ)⁻¹ * Real.exp (-θ * h) ≤
      ‖s‖ * (D * Real.exp (θ * (1 + δ))) *
        (1024 * D ^ 2 * v / (1 - Real.exp (-(θ / (64 * D))))) * Real.exp (-θ * h) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv (by positivity))
      (Real.exp_pos _).le
  refine hfinal.trans (le_of_eq ?_)
  ring

/-- **Class-uniform envelope of the weak descending ladder density** of `Y = 1 - X + μ`:
`‖g₋(s, h)‖ ≤ ‖s‖ · 32 D² e^{θ δ} / (1 - e^{-θ/(64D)}) · e^{θ h}`. -/
theorem norm_ladderDensity_desc_le_of_gapLaw (hX : IsGapLaw ν fX D θ v) (hθ : 0 < θ)
    (hD : 0 < D) (hv : 0 < v) {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D))
    {s : ℂ} (hs : ‖s‖ ≤ 1) (h : ℝ) :
    haveI := isProbabilityMeasure_shiftedStep hX μ
    ‖ladderDensity (shiftedStep ν μ) (fun y => fX (1 + μ - y)) (Iic 0) s h‖ ≤
      ‖s‖ * (32 * D ^ 2 * Real.exp (θ * δ) /
        (1 - Real.exp (-(θ / (64 * D))))) * Real.exp (θ * h) := by
  have := isProbabilityMeasure_shiftedStep hX μ
  have hgap := (shiftedStep_gaps hX hθ hD hv hμ hδ).2
  have he : 0 < 1 - Real.exp (-(θ / (64 * D))) := by
    rw [sub_pos, Real.exp_lt_one_iff]; have : 0 < θ / (64 * D) := by positivity
    linarith
  have hgap_pos : 0 < 1 - expEntryMass (shiftedStep ν μ) (Ioi 0) (-θ) :=
    lt_of_lt_of_le (by positivity) hgap
  have hbound := norm_ladderDensity_desc_le (ρ := shiftedStep ν μ) (f := fun y => fX (1 + μ - y))
    (D := D * Real.exp (θ * δ)) hθ.le (by linarith) (fun y => hX.nonneg _)
    (fun y hy => shiftedStep_density_le_nonpos hX hθ.le hD.le hμ hy) hs h
  refine hbound.trans ?_
  have hinv : (1 - expEntryMass (shiftedStep ν μ) (Ioi 0) (-θ))⁻¹ ≤
      32 * D / (1 - Real.exp (-(θ / (64 * D)))) := by
    rw [inv_le_comm₀ hgap_pos (by positivity), inv_div]
    exact hgap
  have hfinal : ‖s‖ * (D * Real.exp (θ * δ)) *
      (1 - expEntryMass (shiftedStep ν μ) (Ioi 0) (-θ))⁻¹ * Real.exp (θ * h) ≤
      ‖s‖ * (D * Real.exp (θ * δ)) *
        (32 * D / (1 - Real.exp (-(θ / (64 * D))))) * Real.exp (θ * h) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv (by positivity))
      (Real.exp_pos _).le
  refine hfinal.trans (le_of_eq ?_)
  ring

/-- **Class-uniform unit-interval bound** for the pre-ladder occupation measure of
`Y = 1 - X + μ`: `u₋((x - 1, x]) ≤ e^{θ} · 1024 D² v / (1 - e^{-θ/(64D)})`. -/
theorem preEntryOccupation_asc_Ioc_le_of_gapLaw (hX : IsGapLaw ν fX D θ v) (hθ : 0 < θ)
    (hD : 0 < D) (hv : 0 < v) {μ δ : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D)) (x : ℝ) :
    haveI := isProbabilityMeasure_shiftedStep hX μ
    preEntryOccupation (shiftedStep ν μ) (Ioi 0) (Ioc (x - 1) x) ≤
      ENNReal.ofReal (Real.exp θ * (1024 * D ^ 2 * v / (1 - Real.exp (-(θ / (64 * D)))))) := by
  have := isProbabilityMeasure_shiftedStep hX μ
  have hgap := (shiftedStep_gaps hX hθ hD hv hμ hδ).1
  have he : 0 < 1 - Real.exp (-(θ / (64 * D))) := by
    rw [sub_pos, Real.exp_lt_one_iff]; have : 0 < θ / (64 * D) := by positivity
    linarith
  have hgap_pos : 0 < 1 - expEntryMass (shiftedStep ν μ) (Iic 0) θ :=
    lt_of_lt_of_le (by positivity) hgap
  have hinv : (1 - expEntryMass (shiftedStep ν μ) (Iic 0) θ)⁻¹ ≤
      1024 * D ^ 2 * v / (1 - Real.exp (-(θ / (64 * D)))) := by
    rw [inv_le_comm₀ hgap_pos (by positivity), inv_div]
    exact hgap
  refine (preEntryOccupation_asc_Ioc_le hθ.le (by linarith) x).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le

end PGM.WienerHopf
