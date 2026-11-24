import PLAStochastic.Index.CEPS.Output.Tails
import PLAStochastic.ForMathlib.Analysis.Calculus.ScaleFisher
import PLAStochastic.ForMathlib.Probability.Moments.ProductNegativeMoment
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Track O: the input class and its first consequences

`OutInput r E κ f ν`: `ν` has the nonnegative density `f`, vanishing on `(-∞, 0]`, of class
`C^{max r 2}`, and the Mellin powers `mellinOp^[a] f` (`a ≤ r`) and `f''` have the envelope
`E e^{-κ|x|}`. Consequences used by the bound:

* smoothness of the Mellin powers (`OutInput.continuous`, `OutInput.differentiable`);
* the **scale Fisher package** (`output-closure.md` (O2)): the score `ρ = mellinScore f` has
  `E_ν ρ = 0`, `ρ² ∈ L¹(ν)` and `E_ν ρ² ≤ outFisher E κ` (`OutInput.fisher`), with no lower
  bound on `f`;
* negative moments `E_ν X^{-q} ≤ 1 + 8 E q` (`OutInput.negMoment`);
* the weighted masses `outWeight f (κ/2) a ≤ outWeightBound E κ` (`OutInput.outWeight_le`);
  the Mellin envelope is required up to order `max r 1`, so that `mellinOp f` is integrable
  also for `r = 0`;
* almost every point of `outMeasure f β` has positive coordinates (`OutInput.ae_pos`).
-/

noncomputable section

open MeasureTheory Set Finset Filter
open scoped ENNReal

namespace PGM

/-- The input class of track O. -/
structure OutInput (r : ℕ) (E κ : ℝ) (f : ℝ → ℝ) (ν : ProbabilityMeasure ℝ) : Prop where
  κpos : 0 < κ
  pos : ∀ x, 0 ≤ f x
  zero : ∀ x ≤ 0, f x = 0
  smooth : ContDiff ℝ (max r 2 : ℕ) f
  density : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x)
  env : ∀ a ≤ max r 1, ∀ x, |mellinOp^[a] f x| ≤ E * Real.exp (-κ * |x|)
  env2 : ∀ x, |deriv (deriv f) x| ≤ E * Real.exp (-κ * |x|)

/-- The scale Fisher bound `E ∫_0^∞ (34 + 16 x²) e^{-κx/2} dx`. -/
def outFisher (E κ : ℝ) : ℝ := E * ∫ x in Ioi (0 : ℝ), (34 + 16 * x ^ 2) * Real.exp (-(κ / 2) * x)

/-- The weighted mass bound `E e^{κ/2} ∫_0^∞ e^{-κx/2} dx`. -/
def outWeightBound (E κ : ℝ) : ℝ := E * Real.exp (κ / 2) * ∫ x in Ioi (0 : ℝ), Real.exp (-(κ / 2) * x)

variable {r : ℕ} {E κ : ℝ} {f : ℝ → ℝ} {ν : ProbabilityMeasure ℝ}

namespace OutInput

variable (h : OutInput r E κ f ν)
include h

theorem env0 : ∀ x, |f x| ≤ E * Real.exp (-κ * |x|) := by
  simpa using h.env 0 (Nat.zero_le _)

theorem env1 : ∀ x, |mellinOp f x| ≤ E * Real.exp (-κ * |x|) := by
  simpa using h.env 1 (le_max_right r 1)

theorem E_nonneg : 0 ≤ E := by
  have := (abs_nonneg _).trans (h.env0 0)
  exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)

theorem le_E (x : ℝ) : f x ≤ E := by
  refine (le_abs_self _).trans ((h.env0 x).trans ?_)
  exact mul_le_of_le_one_right h.E_nonneg (Real.exp_le_one_iff.mpr
    (by have := abs_nonneg x; nlinarith [h.κpos]))

theorem continuous : ∀ a ≤ r, Continuous (mellinOp^[a] f) := by
  intro a ha
  have := contDiff_mellinOp_iterate h.smooth a (ha.trans (le_max_left r 2))
  exact this.continuous

theorem differentiable : ∀ a < r, Differentiable ℝ (mellinOp^[a] f) := fun _ ha =>
  differentiable_mellinOp_iterate h.smooth (lt_of_lt_of_le ha (le_max_left r 2))

theorem measurable_f : Measurable f := by
  simpa using (h.continuous 0 (Nat.zero_le r)).measurable

theorem measurable_iterate (a : ℕ) : Measurable (mellinOp^[a] f) :=
  measurable_mellinOp_iterate h.measurable_f a

theorem contDiff_two : ContDiff ℝ 2 f := h.smooth.of_le (by exact_mod_cast le_max_right r 2)

theorem measure_Iic : (ν : Measure ℝ) (Iic 0) = 0 := by
  rw [h.density, withDensity_apply _ measurableSet_Iic]
  refine (setLIntegral_congr_fun measurableSet_Iic (g := fun _ => (0 : ℝ≥0∞)) ?_).trans
    (by simp)
  intro y hy
  simp [h.zero y hy]

/-- Negative moments of the input law. -/
theorem negMoment {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4) :
    ∫⁻ x, ENNReal.ofReal (x ^ (-q)) ∂(ν : Measure ℝ) ≤ ENNReal.ofReal (1 + 8 * E * q) :=
  lintegral_rpow_neg_le_of_density h.measurable_f h.E_nonneg h.density h.le_E h.measure_Iic hq0 hq

theorem integral_density (g : ℝ → ℝ) :
    ∫ x, g x ∂(ν : Measure ℝ) = ∫ x, f x * g x := by
  rw [h.density, integral_withDensity_eq_integral_toReal_smul h.measurable_f.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (h.pos x)]

omit h in
theorem integrableOn_Ioi_pow_exp (p : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ p * Real.exp (-b * x)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (p : ℝ)) (p := 1) (b := b)
    (by have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith) one_pos hb
  refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one]

/-- An envelope `E e^{-κ|x|}` of a function vanishing on `(-∞, 0]`, times `|x|^p`, is
integrable. -/
theorem integrable_pow_mul_of_env {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ x ≤ 0, g x = 0)
    (henv : ∀ x, |g x| ≤ E * Real.exp (-κ * |x|)) (p : ℕ) :
    Integrable fun x => x ^ p * g x := by
  have hκ := h.κpos
  have hi : Integrable ((Ioi (0 : ℝ)).indicator fun x => E * (x ^ p * Real.exp (-κ * x))) := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact (integrableOn_Ioi_pow_exp p hκ).const_mul E
  refine hi.mono' ((measurable_id.pow_const p).mul hg).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), abs_mul, abs_pow, abs_of_pos hx]
    have := henv x
    rw [abs_of_pos hx] at this
    calc x ^ p * |g x| ≤ x ^ p * (E * Real.exp (-κ * x)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = E * (x ^ p * Real.exp (-κ * x)) := by ring
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), hg0 x (not_lt.mp hx)]
    simp

theorem measurable_score : Measurable (mellinScore f) :=
  (measurable_mellinOp h.measurable_f).div h.measurable_f

theorem score_sq_mul (x : ℝ) : f x * mellinScore f x ^ 2 = mellinOp f x ^ 2 / f x := by
  rcases (h.pos x).eq_or_lt with hx | hx
  · rw [← hx]; simp
  · simp only [mellinScore]
    field_simp

/-- The pointwise Fisher envelope, `(mellinOp f)²/f ≤ E (34 + 16x²) e^{-κx/2} 1_{x>0}`. -/
theorem sq_div_le (x : ℝ) : mellinOp f x ^ 2 / f x ≤
    (Ioi (0 : ℝ)).indicator (fun x => E * ((34 + 16 * x ^ 2) * Real.exp (-(κ / 2) * x))) x := by
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    exact sq_mellinOp_div_le h.κpos h.contDiff_two h.pos (fun y => (le_abs_self _).trans (h.env0 y))
      h.env2 hx
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
      mellinOp_eq_zero_of_nonpos h.zero x (not_lt.mp hx)]
    simp

theorem integrable_fisherEnv : Integrable ((Ioi (0 : ℝ)).indicator
    fun x => E * ((34 + 16 * x ^ 2) * Real.exp (-(κ / 2) * x))) := by
  have hκ2 : 0 < κ / 2 := by have := h.κpos; positivity
  rw [integrable_indicator_iff measurableSet_Ioi]
  have h0 := (integrableOn_Ioi_pow_exp 0 hκ2).const_mul 34
  have h2 := (integrableOn_Ioi_pow_exp 2 hκ2).const_mul 16
  refine IntegrableOn.congr_fun (f := fun x => E * (34 * (x ^ 0 * Real.exp (-(κ / 2) * x)) +
    16 * (x ^ 2 * Real.exp (-(κ / 2) * x))))
    (by have := (h0.add h2).const_mul E; exact this) (fun x _ => ?_)
    measurableSet_Ioi
  simp only [pow_zero, one_mul]
  ring

/-- **The scale Fisher package** (`output-closure.md` (O2)). -/
theorem fisher :
    Measurable (mellinScore f) ∧ Integrable (fun x => mellinScore f x ^ 2) (ν : Measure ℝ) ∧
      ∫ x, mellinScore f x ∂(ν : Measure ℝ) = 0 ∧
      ∫ x, mellinScore f x ^ 2 ∂(ν : Measure ℝ) ≤ outFisher E κ := by
  have hρm := h.measurable_score
  have hdf : Differentiable ℝ f := h.contDiff_two.differentiable (by norm_num)
  have hmL : Measurable (mellinOp f) := measurable_mellinOp h.measurable_f
  have hI : Integrable fun x => f x * mellinScore f x ^ 2 := by
    refine h.integrable_fisherEnv.mono' (h.measurable_f.mul (hρm.pow_const 2)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h.pos x) (sq_nonneg _)), h.score_sq_mul]
    exact h.sq_div_le x
  refine ⟨hρm, ?_, ?_, ?_⟩
  · rw [h.density, integrable_withDensity_iff_integrable_smul' h.measurable_f.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine hI.congr (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (h.pos x)]
  · rw [h.integral_density]
    have e : (fun x => f x * mellinScore f x) = mellinOp f := by
      funext x; rw [mul_comm]; exact mellinScore_mul_self h.pos x
    rw [e]
    refine integral_mellinOp_eq_zero hdf ?_ ?_
    · simpa using h.integrable_pow_mul_of_env h.measurable_f h.zero h.env0 1
    · simpa using h.integrable_pow_mul_of_env hmL (mellinOp_eq_zero_of_nonpos h.zero) h.env1 0
  · rw [h.integral_density, outFisher, ← integral_const_mul, ← integral_indicator measurableSet_Ioi]
    refine integral_mono hI h.integrable_fisherEnv fun x => ?_
    rw [h.score_sq_mul]
    convert h.sq_div_le x using 2

/-- The weighted masses of the inserted factors. -/
theorem outWeight_le {a : ℕ} (ha : a ≤ max r 1) :
    outWeight f (κ / 2) a ≤ ENNReal.ofReal (outWeightBound E κ) := by
  have hκ2 : 0 < κ / 2 := by have := h.κpos; positivity
  have hpt : ∀ x, ENNReal.ofReal (|mellinOp^[a] f x| * Real.exp (κ / 2 * |x - 1|)) ≤
      (Ioi (0 : ℝ)).indicator (fun x => ENNReal.ofReal
        (E * Real.exp (κ / 2) * Real.exp (-(κ / 2) * x))) x := by
    intro x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := h.env a ha x
      rw [abs_of_pos hx] at h1
      have h2 : Real.exp (κ / 2 * |x - 1|) ≤ Real.exp (κ / 2) * Real.exp (κ / 2 * x) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have : |x - 1| ≤ x + 1 := by rw [abs_le]; constructor <;> linarith
        nlinarith
      calc |mellinOp^[a] f x| * Real.exp (κ / 2 * |x - 1|)
          ≤ (E * Real.exp (-κ * x)) * (Real.exp (κ / 2) * Real.exp (κ / 2 * x)) :=
            mul_le_mul h1 h2 (Real.exp_pos _).le (by have := h.E_nonneg; positivity)
        _ = E * Real.exp (κ / 2) * Real.exp (-(κ / 2) * x) := by
            rw [mul_mul_mul_comm, ← Real.exp_add]
            ring_nf
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
        mellinOp_iterate_eq_zero_of_nonpos h.zero a x (not_lt.mp hx)]
      simp
  have hint : IntegrableOn (fun x : ℝ => E * Real.exp (κ / 2) * Real.exp (-(κ / 2) * x))
      (Ioi 0) := (exp_neg_integrableOn_Ioi 0 hκ2).const_mul _
  calc outWeight f (κ / 2) a
      ≤ ∫⁻ x, (Ioi (0 : ℝ)).indicator (fun x => ENNReal.ofReal
          (E * Real.exp (κ / 2) * Real.exp (-(κ / 2) * x))) x := lintegral_mono hpt
    _ = ENNReal.ofReal (outWeightBound E κ) := by
        rw [lintegral_indicator measurableSet_Ioi, ← ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun x => by have := h.E_nonneg; positivity), outWeightBound,
          integral_const_mul]

theorem outWeightBound_nonneg : 0 ≤ outWeightBound E κ := by
  have := h.E_nonneg
  unfold outWeightBound
  exact mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun _ _ => by positivity)

/-- The exponential moment `∫ e^{(κ/2)|x-1|} dν` is the weighted mass of order zero. -/
theorem lintegral_exp_le :
    ∫⁻ x, ENNReal.ofReal (Real.exp (κ / 2 * |x - 1|)) ∂(ν : Measure ℝ) ≤
      ENNReal.ofReal (outWeightBound E κ) := by
  have e : ∫⁻ x, ENNReal.ofReal (Real.exp (κ / 2 * |x - 1|)) ∂(ν : Measure ℝ) =
      outWeight f (κ / 2) 0 := by
    rw [h.density, ← outWeight_eq_lintegral h.measurable_f]
    simp only [Function.iterate_zero, id, abs_of_nonneg (h.pos _)]
  rw [e]
  exact h.outWeight_le (Nat.zero_le _)

/-- Almost every point of `outMeasure f β` has positive coordinates. -/
theorem ae_pos {n : ℕ} (β : Fin n → ℕ) : ∀ᵐ x ∂(outMeasure f β), ∀ l, 0 < x l := by
  rw [ae_all_iff]
  intro l
  rw [ae_iff]
  have : {x : Fin n → ℝ | ¬ 0 < x l} = Function.eval l ⁻¹' Iic 0 := by
    ext x; simp [not_lt]
  rw [this, outMeasure]
  refine Measure.pi_eval_preimage_null _ ?_
  rw [withDensity_apply _ measurableSet_Iic]
  refine (setLIntegral_congr_fun measurableSet_Iic (g := fun _ => (0 : ℝ≥0∞)) ?_).trans
    (by simp)
  intro y hy
  simp [mellinOp_iterate_eq_zero_of_nonpos h.zero (β l) y hy]

end OutInput

end PGM
