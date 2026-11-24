import PLAStochastic.ForMathlib.Analysis.Calculus.MellinOperator
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Pointwise envelopes from weighted integrable derivatives

For `f ∈ C^m(ℝ)` vanishing on `(-∞, 0]` whose derivatives up to order `m` are integrable
against `e^{η|x|}`:

* `iteratedDeriv_eq_zero_of_nonpos`: all derivatives up to order `m` vanish on `(-∞, 0]`;
* `abs_iteratedDeriv_le_of_weighted`: for `i < m`,
  `|f^{(i)}(x)| ≤ (∫ e^{η|t|} |f^{(i+1)}(t)| dt) e^{-η|x|}`, from
  `f^{(i)}(x) = -∫_x^∞ f^{(i+1)}`;
* `mellinOp_iterate_eq_sum`: `mellinOp^[a] f = ∑_{j ≤ a} mellinCoeff a j · x^j f^{(j)}` for
  `a ≤ m`, with universal coefficients;
* `abs_mellinOp_iterate_le`: an envelope `|f^{(j)}| ≤ R e^{-η|x|}` (`j ≤ a`) gives
  `|mellinOp^[a] f| ≤ R (∑_j |mellinCoeff a j| j! (2/η)^j) e^{-(η/2)|x|}`.
-/

noncomputable section

open Set Filter Topology MeasureTheory Finset

namespace PGM

/-- Universal coefficients of `mellinOp^[a] = ∑_j c_{a,j} x^j ∂^j`. -/
def mellinCoeff : ℕ → ℕ → ℝ
  | 0, j => if j = 0 then 1 else 0
  | a + 1, 0 => mellinCoeff a 0
  | a + 1, j + 1 => ((j : ℝ) + 2) * mellinCoeff a (j + 1) + mellinCoeff a j

theorem mellinCoeff_eq_zero : ∀ {a j : ℕ}, a < j → mellinCoeff a j = 0
  | 0, j, h => by simp [mellinCoeff, Nat.pos_iff_ne_zero.mp h]
  | a + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | a + 1, j + 1, h => by
    rw [mellinCoeff, mellinCoeff_eq_zero (by omega : a < j + 1),
      mellinCoeff_eq_zero (by omega : a < j)]
    ring

/-- Derivatives of a function vanishing on `(-∞, 0]` vanish there. -/
theorem iteratedDeriv_eq_zero_of_nonpos {f : ℝ → ℝ} {m : ℕ} (hf : ContDiff ℝ m f)
    (h0 : ∀ x ≤ 0, f x = 0) : ∀ j ≤ m, ∀ x ≤ 0, iteratedDeriv j f x = 0 := by
  intro j
  induction j with
  | zero => intro _; simpa using h0
  | succ j ih =>
    intro hj x hx
    have ih' := ih (by omega)
    have hzero : ∀ y < 0, iteratedDeriv (j + 1) f y = 0 := by
      intro y hy
      have hev : iteratedDeriv j f =ᶠ[𝓝 y] fun _ => 0 :=
        Filter.eventually_of_mem (Iio_mem_nhds hy) fun z hz => ih' z (le_of_lt hz)
      rw [iteratedDeriv_succ, hev.deriv_eq, deriv_const]
    rcases hx.lt_or_eq with hlt | rfl
    · exact hzero x hlt
    · have hc : Continuous (iteratedDeriv (j + 1) f) :=
        hf.continuous_iteratedDeriv (j + 1) (by exact_mod_cast hj)
      have h1 : Tendsto (iteratedDeriv (j + 1) f) (𝓝[<] 0) (𝓝 (iteratedDeriv (j + 1) f 0)) :=
        hc.continuousAt.continuousWithinAt.tendsto
      have h2 : Tendsto (iteratedDeriv (j + 1) f) (𝓝[<] 0) (𝓝 0) :=
        tendsto_const_nhds.congr' (Filter.eventually_of_mem self_mem_nhdsWithin
          fun y hy => (hzero y hy).symm)
      exact tendsto_nhds_unique h1 h2

theorem integrable_of_weighted {g : ℝ → ℝ} {η : ℝ} (hη : 0 ≤ η) (hg : Measurable g)
    (hint : Integrable fun x => Real.exp (η * |x|) * g x) : Integrable g := by
  refine hint.norm.mono' hg.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have : 1 ≤ Real.exp (η * |x|) := Real.one_le_exp (by positivity)
  nlinarith [abs_nonneg (g x)]

/-- **Pointwise envelope of a derivative** from the weighted integrability of the next one. -/
theorem abs_iteratedDeriv_le_of_weighted {f : ℝ → ℝ} {m : ℕ} (hf : ContDiff ℝ m f) {η : ℝ}
    (hη : 0 ≤ η) (hint : ∀ j ≤ m, Integrable fun x => Real.exp (η * |x|) * iteratedDeriv j f x)
    (h0 : ∀ x ≤ 0, f x = 0) {i : ℕ} (hi : i < m) (x : ℝ) :
    |iteratedDeriv i f x| ≤
      (∫ t, Real.exp (η * |t|) * |iteratedDeriv (i + 1) f t|) * Real.exp (-η * |x|) := by
  have hz := iteratedDeriv_eq_zero_of_nonpos hf h0
  have hI0 : 0 ≤ ∫ t, Real.exp (η * |t|) * |iteratedDeriv (i + 1) f t| :=
    integral_nonneg fun t => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  rcases le_or_gt x 0 with hx | hx
  · rw [hz i hi.le x hx, abs_zero]; positivity
  set g := iteratedDeriv i f with hgdef
  set g' := iteratedDeriv (i + 1) f with hg'def
  have hd : Differentiable ℝ g := hf.differentiable_iteratedDeriv i (by exact_mod_cast hi)
  have hderiv : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    rw [hg'def, iteratedDeriv_succ]
    exact (hd t).hasDerivAt
  have hcg : Continuous g := hf.continuous_iteratedDeriv i (by exact_mod_cast hi.le)
  have hcg' : Continuous g' := hf.continuous_iteratedDeriv (i + 1) (by exact_mod_cast hi)
  have hgi : Integrable g := integrable_of_weighted hη hcg.measurable (hint i hi.le)
  have hg'i : Integrable g' := integrable_of_weighted hη hcg'.measurable (hint (i + 1) hi)
  have htend : Tendsto g atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := x) (fun t _ => hderiv t)
      hg'i.integrableOn hgi.integrableOn
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' (a := x) (fun t _ => hderiv t)
    hg'i.integrableOn htend
  have hgx : g x = -∫ t in Ioi x, g' t := by linarith
  have hw : Integrable fun t => Real.exp (η * |t|) * |g' t| := by
    have := (hint (i + 1) hi).norm
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rfl
  rw [hgx, abs_neg]
  calc |∫ t in Ioi x, g' t| ≤ ∫ t in Ioi x, |g' t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi x, Real.exp (-η * |x|) * (Real.exp (η * |t|) * |g' t|) := by
        refine setIntegral_mono_on hg'i.abs.integrableOn (hw.const_mul _).integrableOn
          measurableSet_Ioi fun t ht => ?_
        have ht' : x < t := ht
        have : 1 ≤ Real.exp (-η * |x|) * Real.exp (η * |t|) := by
          rw [← Real.exp_add]
          refine Real.one_le_exp ?_
          rw [abs_of_pos hx, abs_of_pos (hx.trans ht')]
          nlinarith
        calc |g' t| = 1 * |g' t| := (one_mul _).symm
          _ ≤ (Real.exp (-η * |x|) * Real.exp (η * |t|)) * |g' t| :=
              mul_le_mul_of_nonneg_right this (abs_nonneg _)
          _ = _ := by ring
    _ = Real.exp (-η * |x|) * ∫ t in Ioi x, Real.exp (η * |t|) * |g' t| := integral_const_mul _ _
    _ ≤ Real.exp (-η * |x|) * ∫ t, Real.exp (η * |t|) * |g' t| :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hw (Eventually.of_forall fun t =>
          mul_nonneg (Real.exp_pos _).le (abs_nonneg _))) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- **Expansion of the Mellin powers** in the derivatives. -/
theorem mellinOp_iterate_eq_sum {f : ℝ → ℝ} {m : ℕ} (hf : ContDiff ℝ m f) :
    ∀ a ≤ m, mellinOp^[a] f =
      fun x => ∑ j ∈ range (a + 1), mellinCoeff a j * (x ^ j * iteratedDeriv j f x) := by
  intro a
  induction a with
  | zero => intro _; funext x; simp [mellinCoeff]
  | succ a ih =>
    intro ha
    rw [Function.iterate_succ_apply', ih (by omega)]
    funext x
    set c := mellinCoeff a with hc
    set T : ℕ → ℝ := fun j => x ^ j * iteratedDeriv j f x with hT
    have hdiff : ∀ j ∈ range (a + 1), Differentiable ℝ (iteratedDeriv j f) := by
      intro j hj
      rw [Finset.mem_range] at hj
      exact hf.differentiable_iteratedDeriv j (by exact_mod_cast (show j < m by omega))
    have hD := HasDerivAt.fun_sum (u := range (a + 1)) (x := x)
      (A := fun j (y : ℝ) => c j * (y ^ j * iteratedDeriv j f y))
      (A' := fun j => c j * ((j : ℝ) * x ^ (j - 1) * iteratedDeriv j f x +
        x ^ j * iteratedDeriv (j + 1) f x)) fun j hj => by
        have h1 : HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x := by
          rw [iteratedDeriv_succ]; exact (hdiff j hj x).hasDerivAt
        exact ((hasDerivAt_pow j x).fun_mul h1).const_mul (c j)
    rw [mellinOp_apply, hD.deriv]
    have hx : ∀ j : ℕ, x * ((j : ℝ) * x ^ (j - 1)) = j * x ^ j := by
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · rw [mul_left_comm, mul_pow_sub_one hj.ne']
    have hlhs : (∑ j ∈ range (a + 1), c j * (x ^ j * iteratedDeriv j f x)) +
        x * ∑ j ∈ range (a + 1), c j * ((j : ℝ) * x ^ (j - 1) * iteratedDeriv j f x +
          x ^ j * iteratedDeriv (j + 1) f x) =
        ∑ j ∈ range (a + 1), ((j : ℝ) + 1) * c j * T j +
          ∑ j ∈ range (a + 1), c j * T (j + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hT, pow_succ]
      have := hx j
      linear_combination (c j * iteratedDeriv j f x) * this
    rw [hlhs]
    have hsplit : ∑ j ∈ range (a + 1), ((j : ℝ) + 1) * c j * T j =
        c 0 * T 0 + ∑ j ∈ range (a + 1), ((j : ℝ) + 2) * c (j + 1) * T (j + 1) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ (fun j => ((j : ℝ) + 2) * c (j + 1) *
        T (j + 1)), hc, mellinCoeff_eq_zero (by omega : a < a + 1)]
      push_cast
      ring_nf
    rw [hsplit, Finset.sum_range_succ' (fun j => mellinCoeff (a + 1) j * (x ^ j *
      iteratedDeriv j f x))]
    simp only [mellinCoeff, ← hc]
    rw [add_assoc, ← Finset.sum_add_distrib, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by simp only [hT]; ring

theorem pow_abs_mul_exp_le {η : ℝ} (hη : 0 < η) (j : ℕ) (x : ℝ) :
    |x| ^ j * Real.exp (-η * |x|) ≤ j.factorial * (2 / η) ^ j * Real.exp (-(η / 2) * |x|) := by
  have h := Real.pow_div_factorial_le_exp (x := η / 2 * |x|) (by positivity) j
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  have e : Real.exp (-η * |x|) = Real.exp (-(η / 2) * |x|) * (Real.exp (η / 2 * |x|))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  rw [e]
  have hpos := Real.exp_pos (η / 2 * |x|)
  have h2 : |x| ^ j ≤ j.factorial * (2 / η) ^ j * Real.exp (η / 2 * |x|) := by
    have h3 : (2 / η) ^ j * (η / 2) ^ j = 1 := by
      rw [← mul_pow]; field_simp; simp
    calc |x| ^ j = (2 / η) ^ j * ((η / 2) ^ j * |x| ^ j) := by rw [← mul_assoc, h3, one_mul]
      _ ≤ (2 / η) ^ j * (Real.exp (η / 2 * |x|) * j.factorial) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  calc |x| ^ j * (Real.exp (-(η / 2) * |x|) * (Real.exp (η / 2 * |x|))⁻¹)
      ≤ (j.factorial * (2 / η) ^ j * Real.exp (η / 2 * |x|)) *
          (Real.exp (-(η / 2) * |x|) * (Real.exp (η / 2 * |x|))⁻¹) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by field_simp

/-- The envelope constant of `mellinOp^[a] f`. -/
def mellinEnvConst (a : ℕ) (η : ℝ) : ℝ :=
  ∑ j ∈ range (a + 1), |mellinCoeff a j| * (j.factorial * (2 / η) ^ j)

theorem mellinEnvConst_nonneg (a : ℕ) {η : ℝ} (hη : 0 < η) : 0 ≤ mellinEnvConst a η :=
  Finset.sum_nonneg fun j _ => by positivity

/-- **Envelope of the Mellin powers** from envelopes of the derivatives. -/
theorem abs_mellinOp_iterate_le {f : ℝ → ℝ} {m : ℕ} (hf : ContDiff ℝ m f) {a : ℕ} (ha : a ≤ m)
    {R η : ℝ} (hη : 0 < η) (henv : ∀ j ≤ a, ∀ x, |iteratedDeriv j f x| ≤ R * Real.exp (-η * |x|))
    (x : ℝ) :
    |mellinOp^[a] f x| ≤ R * mellinEnvConst a η * Real.exp (-(η / 2) * |x|) := by
  have hR : 0 ≤ R := by
    have := (abs_nonneg _).trans (henv 0 (Nat.zero_le a) 0)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  rw [mellinOp_iterate_eq_sum hf a ha, mellinEnvConst, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hj : j ≤ a := by rw [Finset.mem_range] at hj; omega
  rw [abs_mul, abs_mul, abs_pow]
  have h1 := henv j hj x
  have h2 := pow_abs_mul_exp_le hη j x
  calc |mellinCoeff a j| * (|x| ^ j * |iteratedDeriv j f x|)
      ≤ |mellinCoeff a j| * (|x| ^ j * (R * Real.exp (-η * |x|))) := by gcongr
    _ = |mellinCoeff a j| * R * (|x| ^ j * Real.exp (-η * |x|)) := by ring
    _ ≤ |mellinCoeff a j| * R * (j.factorial * (2 / η) ^ j * Real.exp (-(η / 2) * |x|)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end PGM
