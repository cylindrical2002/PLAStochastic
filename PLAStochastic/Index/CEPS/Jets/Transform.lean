import PLAStochastic.Index.CEPS.Jets.Basic

/-!
# X8: the transform of signed densities

For a (signed) density `f` vanishing on `(-∞, 0)` and `Re s ≥ 0`,
`M^f(s) = ∫ e^{s(1-x)} f(x) dx` (`cepsJetTransform`) is an absolutely convergent integral with
`|e^{s(1-x)}| ≤ e^{Re s}` on the support:

* `integrable_cepsJetTransform_integrand`, `norm_cepsJetTransform_le`:
  `‖M^f(s)‖ ≤ e^{Re s} ∫ |f|`;
* linearity in `f` (`cepsJetTransform_add`, `_sub`, `_const_mul`, `_sum`, with `_of_integrable`
  versions assuming only integrability of the integrands);
* integration by parts on `ℝ` without boundary terms: `s^k M^φ(s) = M^{φ^{(k)}}(s)`
  (`cepsJetTransform_iteratedDeriv`), hence the Sobolev decay
  `(1 + ‖s‖)^N ‖M^φ(s)‖ ≤ 2^N e^{Re s} ‖φ‖_{N,η}` (`norm_cepsJetTransform_le_sobolev`);
* holomorphy on `Re s > 0` under a first moment (`differentiableAt_cepsJetTransform`),
  continuity on `Re s ≥ 0` (`continuousOn_cepsJetTransform`), and conjugation symmetry
  (`cepsJetTransform_conj`);
* for a step law with density `f_W(y) = f(1 - y)` the step transform is `M^f`
  (`stepTransform_eq_cepsJetTransform`);
* both the transform and the moments only see `f` up to null sets (`cepsJetTransform_congr_ae`,
  `cepsJetMoment_congr_ae`);
* the moments `∫ (1-x)^k φ(x) dx` of a Sobolev density are finite and bounded by
  `k!/η^k e^η ‖φ‖_{m,η}` (`integrable_pow_mul_of_sobolev`, `abs_cepsJetMoment_le`,
  `abs_cepsJetMoment_le_sobolev`), and linear under integrability (`cepsJetMoment_add`, …).
-/

noncomputable section

open MeasureTheory Complex Filter Topology Set

namespace PGM

/-! ## Absolute convergence -/

section Basic

variable {f g : ℝ → ℝ} {s : ℂ}

/-- `‖e^{s(1-x)} f(x)‖ ≤ e^{Re s} |f(x)|` for `Re s ≥ 0` when `f` vanishes on `(-∞, 0)`. -/
theorem norm_cexp_mul_one_sub_mul_le (hneg : ∀ x, x < 0 → f x = 0) (hs : 0 ≤ s.re) (x : ℝ) :
    ‖cexp (s * (1 - x)) * f x‖ ≤ Real.exp s.re * |f x| := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [hneg x hx]
    simp
  · rw [norm_mul, Complex.norm_exp, norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    have : (s * (1 - (x : ℂ))).re = s.re * (1 - x) := by simp
    rw [this]
    nlinarith

theorem integrable_cepsJetTransform_integrand (hf : Integrable f)
    (hneg : ∀ x, x < 0 → f x = 0) (hs : 0 ≤ s.re) :
    Integrable (fun x : ℝ => cexp (s * (1 - x)) * f x) := by
  refine (hf.abs.const_mul (Real.exp s.re)).mono' ?_
    (ae_of_all _ (norm_cexp_mul_one_sub_mul_le hneg hs))
  exact (by fun_prop : Continuous fun x : ℝ => cexp (s * (1 - x))).aestronglyMeasurable.mul
    (continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable)

theorem norm_cepsJetTransform_le (hf : Integrable f) (hneg : ∀ x, x < 0 → f x = 0)
    (hs : 0 ≤ s.re) : ‖cepsJetTransform f s‖ ≤ Real.exp s.re * ∫ x, |f x| := by
  rw [cepsJetTransform, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hf.abs.const_mul _)
    (ae_of_all _ (norm_cexp_mul_one_sub_mul_le hneg hs))

/-! ## Linearity -/

theorem cepsJetTransform_add_of_integrable
    (hf : Integrable fun x : ℝ => cexp (s * (1 - x)) * f x)
    (hg : Integrable fun x : ℝ => cexp (s * (1 - x)) * g x) :
    cepsJetTransform (fun x => f x + g x) s = cepsJetTransform f s + cepsJetTransform g s := by
  simp only [cepsJetTransform, ofReal_add, mul_add]
  exact integral_add hf hg

theorem cepsJetTransform_sub_of_integrable
    (hf : Integrable fun x : ℝ => cexp (s * (1 - x)) * f x)
    (hg : Integrable fun x : ℝ => cexp (s * (1 - x)) * g x) :
    cepsJetTransform (fun x => f x - g x) s = cepsJetTransform f s - cepsJetTransform g s := by
  simp only [cepsJetTransform]
  rw [← integral_sub hf hg]
  congr 1
  funext x
  push_cast
  ring

theorem cepsJetTransform_const_mul (c : ℝ) (f : ℝ → ℝ) (s : ℂ) :
    cepsJetTransform (fun x => c * f x) s = (c : ℂ) * cepsJetTransform f s := by
  simp only [cepsJetTransform, ofReal_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem cepsJetTransform_sum_of_integrable {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    (φ : ι → ℝ → ℝ) (hφ : ∀ i ∈ S, Integrable fun x : ℝ => cexp (s * (1 - x)) * φ i x) :
    cepsJetTransform (fun x => ∑ i ∈ S, c i * φ i x) s =
      ∑ i ∈ S, (c i : ℂ) * cepsJetTransform (φ i) s := by
  simp only [cepsJetTransform, ofReal_sum, ofReal_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  · intro i hi
    refine ((hφ i hi).const_mul (c i : ℂ)).congr (ae_of_all _ fun x => ?_)
    simp only
    ring

theorem cepsJetTransform_add (hf : Integrable f) (hg : Integrable g)
    (hfneg : ∀ x, x < 0 → f x = 0) (hgneg : ∀ x, x < 0 → g x = 0) (hs : 0 ≤ s.re) :
    cepsJetTransform (fun x => f x + g x) s = cepsJetTransform f s + cepsJetTransform g s :=
  cepsJetTransform_add_of_integrable (integrable_cepsJetTransform_integrand hf hfneg hs)
    (integrable_cepsJetTransform_integrand hg hgneg hs)

theorem cepsJetTransform_sub (hf : Integrable f) (hg : Integrable g)
    (hfneg : ∀ x, x < 0 → f x = 0) (hgneg : ∀ x, x < 0 → g x = 0) (hs : 0 ≤ s.re) :
    cepsJetTransform (fun x => f x - g x) s = cepsJetTransform f s - cepsJetTransform g s :=
  cepsJetTransform_sub_of_integrable (integrable_cepsJetTransform_integrand hf hfneg hs)
    (integrable_cepsJetTransform_integrand hg hgneg hs)

theorem cepsJetTransform_sum {ι : Type*} (S : Finset ι) (c : ι → ℝ) (φ : ι → ℝ → ℝ)
    (hφ : ∀ i ∈ S, Integrable (φ i)) (hneg : ∀ i ∈ S, ∀ x, x < 0 → φ i x = 0)
    (hs : 0 ≤ s.re) :
    cepsJetTransform (fun x => ∑ i ∈ S, c i * φ i x) s =
      ∑ i ∈ S, (c i : ℂ) * cepsJetTransform (φ i) s :=
  cepsJetTransform_sum_of_integrable S c φ fun i hi =>
    integrable_cepsJetTransform_integrand (hφ i hi) (hneg i hi) hs

/-! ## Null sets, conjugation, step laws -/

theorem cepsJetTransform_congr_ae (h : f =ᵐ[volume] g) :
    cepsJetTransform f = cepsJetTransform g := by
  funext s
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

theorem cepsJetMoment_congr_ae (h : f =ᵐ[volume] g) : cepsJetMoment f = cepsJetMoment g := by
  funext k
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

theorem cepsJetTransform_conj (f : ℝ → ℝ) (s : ℂ) :
    cepsJetTransform f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (cepsJetTransform f s) := by
  rw [cepsJetTransform, cepsJetTransform, ← integral_conj]
  congr 1
  funext x
  rw [map_mul, ← Complex.exp_conj, map_mul, map_sub, map_one, conj_ofReal, conj_ofReal]

/-- For a step law `W = 1 - X` with density `f_W(y) = f(1 - y)`, `E e^{sW} = M^f(s)`. -/
theorem stepTransform_eq_cepsJetTransform {ρW : Measure ℝ} {fW f : ℝ → ℝ} {D θ v : ℝ}
    (hW : WienerHopf.IsStepLaw ρW fW D θ v) (hfW : ∀ y, fW y = f (1 - y)) (s : ℂ) :
    WienerHopf.stepTransform ρW s = cepsJetTransform f s := by
  rw [stepTransform_eq_integral hW, cepsJetTransform,
    ← integral_sub_left_eq_self (fun x : ℝ => cexp (s * (1 - x)) * f x) volume 1]
  congr 1
  funext y
  rw [hfW y, mul_comm]
  push_cast
  ring_nf

end Basic

/-! ## Integration by parts and Sobolev decay -/

section Decay

/-- Derivatives of a function vanishing on `(-∞, 0)` vanish there too. -/
theorem iteratedDeriv_eq_zero_of_neg {φ : ℝ → ℝ} (hneg : ∀ x, x < 0 → φ x = 0) (k : ℕ)
    {x : ℝ} (hx : x < 0) : iteratedDeriv k φ x = 0 := by
  have h : φ =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hx] with y hy using hneg y hy
  rw [h.iteratedDeriv_eq k]
  simp

/-- **Integration by parts.** `s^k M^φ(s) = M^{φ^{(k)}}(s)`; there are no boundary terms since
`φ` vanishes on `(-∞, 0)` and the integrands are integrable. -/
theorem cepsJetTransform_iteratedDeriv {φ : ℝ → ℝ} {N : ℕ} (hφ : ContDiff ℝ N φ)
    (hneg : ∀ x, x < 0 → φ x = 0) (hint : ∀ k ≤ N, Integrable (iteratedDeriv k φ)) {s : ℂ}
    (hs : 0 ≤ s.re) {k : ℕ} (hk : k ≤ N) :
    s ^ k * cepsJetTransform φ s = cepsJetTransform (iteratedDeriv k φ) s := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ N := by omega
    have hdiff : Differentiable ℝ (iteratedDeriv k φ) :=
      hφ.differentiable_iteratedDeriv k (by exact_mod_cast (show k < N by omega))
    have hI : ∀ j ≤ N,
        Integrable fun x : ℝ => cexp (s * (1 - x)) * ((iteratedDeriv j φ x : ℝ) : ℂ) := fun j hj =>
      integrable_cepsJetTransform_integrand (f := iteratedDeriv j φ) (hint j hj)
        (fun x hx => iteratedDeriv_eq_zero_of_neg hneg j hx) hs
    have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (s * (1 - x)))
        (-s * cexp (s * (1 - x))) x := by
      intro x
      have h := (((hasDerivAt_id' (x : ℂ)).const_sub 1).const_mul s).cexp.comp_ofReal
      convert h using 1
      ring
    have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ((iteratedDeriv k φ x : ℝ) : ℂ))
        ((iteratedDeriv (k + 1) φ x : ℝ) : ℂ) x := by
      intro x
      rw [iteratedDeriv_succ]
      exact (hdiff x).hasDerivAt.ofReal_comp
    have hu'v : Integrable fun x : ℝ =>
        -s * cexp (s * (1 - x)) * ((iteratedDeriv k φ x : ℝ) : ℂ) := by
      refine ((hI k hk').const_mul (-s)).congr (ae_of_all _ fun x => ?_)
      simp only
      ring
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := fun x : ℝ => cexp (s * (1 - x))) (v := fun x : ℝ => ((iteratedDeriv k φ x : ℝ) : ℂ))
      (u' := fun x : ℝ => -s * cexp (s * (1 - x)))
      (v' := fun x : ℝ => ((iteratedDeriv (k + 1) φ x : ℝ) : ℂ))
      (fun x _ => hu x) (fun x _ => hv x) (hI (k + 1) hk) hu'v (hI k hk')
    have e1 : ∫ x : ℝ, -s * cexp (s * (1 - x)) * ((iteratedDeriv k φ x : ℝ) : ℂ) =
        -s * cepsJetTransform (iteratedDeriv k φ) s := by
      rw [cepsJetTransform, ← integral_const_mul]
      congr 1
      funext x
      ring
    rw [e1] at hibp
    have hibp' : cepsJetTransform (iteratedDeriv (k + 1) φ) s =
        -(-s * cepsJetTransform (iteratedDeriv k φ) s) := hibp
    rw [pow_succ, mul_comm (s ^ k) s, mul_assoc, ih hk', hibp']
    ring

variable {φ : ℝ → ℝ} {N : ℕ} {η : ℝ}

theorem one_le_exp_mul_abs (hη : 0 ≤ η) (x : ℝ) : 1 ≤ Real.exp (η * |x|) :=
  Real.one_le_exp (mul_nonneg hη (abs_nonneg x))

/-- For `η ≥ 0` the derivatives of a Sobolev function are integrable. -/
theorem CepsSobolevClass.integrable_iteratedDeriv (hφ : CepsSobolevClass N η φ) (hη : 0 ≤ η)
    {k : ℕ} (hk : k ≤ N) : Integrable (iteratedDeriv k φ) := by
  refine (hφ.integrable k hk).mono (hφ.continuous_iteratedDeriv hk).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_exp_mul_abs hη x)

theorem CepsSobolevClass.integral_abs_iteratedDeriv_le (hφ : CepsSobolevClass N η φ)
    (hη : 0 ≤ η) {k : ℕ} (hk : k ≤ N) :
    ∫ x, |iteratedDeriv k φ x| ≤ cepsSobolev N η φ := by
  have hw : Integrable fun x => Real.exp (η * |x|) * |iteratedDeriv k φ x| := by
    refine (hφ.integrable k hk).norm.congr (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc ∫ x, |iteratedDeriv k φ x| ≤ ∫ x, Real.exp (η * |x|) * |iteratedDeriv k φ x| :=
        integral_mono (hφ.integrable_iteratedDeriv hη hk).abs hw fun x =>
          le_mul_of_one_le_left (abs_nonneg _) (one_le_exp_mul_abs hη x)
    _ ≤ cepsSobolev N η φ := by
        unfold cepsSobolev
        exact Finset.single_le_sum
          (f := fun r => ∫ x, Real.exp (η * |x|) * |iteratedDeriv r φ x|)
          (fun _ _ => integral_nonneg fun _ => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))
          (Finset.mem_range.mpr (by omega))

/-- `‖s‖^k ‖M^φ(s)‖ ≤ e^{Re s} ‖φ‖_{N,η}` for `k ≤ N`. -/
theorem norm_pow_mul_cepsJetTransform_le_sobolev (hφ : CepsSobolevClass N η φ) (hη : 0 ≤ η)
    (hneg : ∀ x, x < 0 → φ x = 0) {s : ℂ} (hs : 0 ≤ s.re) {k : ℕ} (hk : k ≤ N) :
    ‖s‖ ^ k * ‖cepsJetTransform φ s‖ ≤ Real.exp s.re * cepsSobolev N η φ := by
  rw [← norm_pow, ← norm_mul, cepsJetTransform_iteratedDeriv hφ.contDiff hneg
    (fun j hj => hφ.integrable_iteratedDeriv hη hj) hs hk]
  refine (norm_cepsJetTransform_le (hφ.integrable_iteratedDeriv hη hk)
    (fun x hx => iteratedDeriv_eq_zero_of_neg hneg k hx) hs).trans ?_
  exact mul_le_mul_of_nonneg_left (hφ.integral_abs_iteratedDeriv_le hη hk) (Real.exp_pos _).le

/-- **Sobolev decay.** `(1 + ‖s‖)^N ‖M^φ(s)‖ ≤ 2^N e^{Re s} ‖φ‖_{N,η}` on `Re s ≥ 0`. -/
theorem norm_cepsJetTransform_le_sobolev (hφ : CepsSobolevClass N η φ) (hη : 0 ≤ η)
    (hneg : ∀ x, x < 0 → φ x = 0) {s : ℂ} (hs : 0 ≤ s.re) :
    (1 + ‖s‖) ^ N * ‖cepsJetTransform φ s‖ ≤ 2 ^ N * Real.exp s.re * cepsSobolev N η φ := by
  have hT := norm_nonneg (cepsJetTransform φ s)
  rcases le_or_gt ‖s‖ 1 with h1 | h1
  · have h0 := norm_pow_mul_cepsJetTransform_le_sobolev hφ hη hneg hs (Nat.zero_le N)
    rw [pow_zero, one_mul] at h0
    have hp : (1 + ‖s‖) ^ N ≤ 2 ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    calc (1 + ‖s‖) ^ N * ‖cepsJetTransform φ s‖ ≤ 2 ^ N * ‖cepsJetTransform φ s‖ :=
          mul_le_mul_of_nonneg_right hp hT
      _ ≤ 2 ^ N * (Real.exp s.re * cepsSobolev N η φ) :=
          mul_le_mul_of_nonneg_left h0 (by positivity)
      _ = _ := by ring
  · have hN := norm_pow_mul_cepsJetTransform_le_sobolev hφ hη hneg hs le_rfl
    have hp : (1 + ‖s‖) ^ N ≤ 2 ^ N * ‖s‖ ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) N
    calc (1 + ‖s‖) ^ N * ‖cepsJetTransform φ s‖ ≤ 2 ^ N * ‖s‖ ^ N * ‖cepsJetTransform φ s‖ :=
          mul_le_mul_of_nonneg_right hp hT
      _ = 2 ^ N * (‖s‖ ^ N * ‖cepsJetTransform φ s‖) := by ring
      _ ≤ 2 ^ N * (Real.exp s.re * cepsSobolev N η φ) :=
          mul_le_mul_of_nonneg_left hN (by positivity)
      _ = _ := by ring

end Decay

/-! ## Holomorphy and continuity -/

section Analytic

variable {f : ℝ → ℝ}

/-- `M^f` is complex differentiable on `Re s > 0` when `f` and `x f(x)` are integrable. -/
theorem differentiableAt_cepsJetTransform (hf : Integrable f)
    (hx : Integrable fun x => x * f x) (hneg : ∀ x, x < 0 → f x = 0) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (cepsJetTransform f) s := by
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun x : ℝ => cexp (z * (1 - x)) * f x) :=
    fun z => (by fun_prop : Continuous fun x : ℝ => cexp (z * (1 - x))).aestronglyMeasurable.mul
      (continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  have hmeas' : AEStronglyMeasurable
      (fun x : ℝ => (1 - x) * cexp (s * (1 - x)) * f x) :=
    (by fun_prop : Continuous fun x : ℝ =>
      (1 - (x : ℂ)) * cexp (s * (1 - x))).aestronglyMeasurable.mul
      (continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (z : ℂ) (x : ℝ) => cexp (z * (1 - x)) * f x)
    (F' := fun (z : ℂ) (x : ℝ) => (1 - x) * cexp (z * (1 - x)) * f x) (x₀ := s)
    (bound := fun x : ℝ => Real.exp (2 * s.re) * (|f x| + |x * f x|))
    (Metric.ball_mem_nhds s hs) (Eventually.of_forall hmeas)
    (integrable_cepsJetTransform_integrand hf hneg hs.le) hmeas' ?_
    ((hf.abs.add hx.abs).const_mul _) ?_
  · exact key.2.differentiableAt
  · refine ae_of_all _ fun x z hz => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre := abs_re_le_norm (z - s)
    rw [sub_re, abs_le] at hre
    rcases lt_or_ge x 0 with hx0 | hx0
    · rw [hneg x hx0]
      simp only [ofReal_zero, mul_zero, norm_zero]
      positivity
    · rw [norm_mul, norm_mul, Complex.norm_exp, norm_real, Real.norm_eq_abs]
      have h1 : ‖(1 : ℂ) - x‖ ≤ 1 + |x| := by
        rw [show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring, norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith [abs_nonneg x, le_abs_self x, neg_abs_le x]
      have h2 : Real.exp (z * (1 - (x : ℂ))).re ≤ Real.exp (2 * s.re) := by
        apply Real.exp_le_exp.mpr
        have : (z * (1 - (x : ℂ))).re = z.re * (1 - x) := by simp
        rw [this]
        nlinarith
      have h3 : (1 + |x|) * |f x| = |f x| + |x * f x| := by rw [abs_mul]; ring
      calc ‖(1 : ℂ) - x‖ * Real.exp (z * (1 - (x : ℂ))).re * |f x|
          ≤ (1 + |x|) * Real.exp (2 * s.re) * |f x| := by gcongr
        _ = Real.exp (2 * s.re) * (|f x| + |x * f x|) := by rw [← h3]; ring
  · refine ae_of_all _ fun x z _ => ?_
    have h := (((hasDerivAt_id' z).mul_const ((1 : ℂ) - x)).cexp).mul_const (f x : ℂ)
    exact h.congr_deriv (by ring)

/-- `M^f` is continuous on the closed half-plane `Re s ≥ 0`. -/
theorem continuousOn_cepsJetTransform (hf : Integrable f) (hneg : ∀ x, x < 0 → f x = 0) :
    ContinuousOn (cepsJetTransform f) {s : ℂ | 0 ≤ s.re} := by
  intro s₀ _
  have hlt : ∀ᶠ z in 𝓝[{s : ℂ | 0 ≤ s.re}] s₀, z.re < s₀.re + 1 :=
    nhdsWithin_le_nhds (continuous_re.continuousAt.eventually_lt continuousAt_const
      (lt_add_one s₀.re))
  refine continuousWithinAt_of_dominated (F := fun (z : ℂ) (x : ℝ) => cexp (z * (1 - x)) * f x)
    (bound := fun x : ℝ => Real.exp (s₀.re + 1) * |f x|) ?_ ?_ (hf.abs.const_mul _) ?_
  · exact Eventually.of_forall fun z =>
      (by fun_prop : Continuous fun x : ℝ => cexp (z * (1 - x))).aestronglyMeasurable.mul
        (continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin, hlt] with z hz hz'
    refine ae_of_all _ fun x => (norm_cexp_mul_one_sub_mul_le hneg hz x).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hz'.le) (abs_nonneg _)
  · exact ae_of_all _ fun x =>
      (by fun_prop : Continuous fun z : ℂ => cexp (z * (1 - x)) * f x).continuousWithinAt

end Analytic

/-! ## Moments -/

section Moments

variable {f g : ℝ → ℝ} {k : ℕ}

theorem cepsJetMoment_add (hf : Integrable fun x => (1 - x) ^ k * f x)
    (hg : Integrable fun x => (1 - x) ^ k * g x) :
    cepsJetMoment (fun x => f x + g x) k = cepsJetMoment f k + cepsJetMoment g k := by
  simp only [cepsJetMoment, mul_add]
  exact integral_add hf hg

theorem cepsJetMoment_sub (hf : Integrable fun x => (1 - x) ^ k * f x)
    (hg : Integrable fun x => (1 - x) ^ k * g x) :
    cepsJetMoment (fun x => f x - g x) k = cepsJetMoment f k - cepsJetMoment g k := by
  simp only [cepsJetMoment, mul_sub]
  exact integral_sub hf hg

theorem cepsJetMoment_const_mul (c : ℝ) (f : ℝ → ℝ) (k : ℕ) :
    cepsJetMoment (fun x => c * f x) k = c * cepsJetMoment f k := by
  simp only [cepsJetMoment]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem cepsJetMoment_sum {ι : Type*} (S : Finset ι) (c : ι → ℝ) (φ : ι → ℝ → ℝ)
    (hφ : ∀ i ∈ S, Integrable fun x => (1 - x) ^ k * φ i x) :
    cepsJetMoment (fun x => ∑ i ∈ S, c i * φ i x) k = ∑ i ∈ S, c i * cepsJetMoment (φ i) k := by
  simp only [cepsJetMoment, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  · intro i hi
    refine ((hφ i hi).const_mul (c i)).congr (ae_of_all _ fun x => ?_)
    simp only
    ring

variable {m : ℕ} {η : ℝ} {φ : ℝ → ℝ}

/-- `|1 - x|^k ≤ k!/η^k e^η e^{η|x|}` for `η > 0`. -/
theorem abs_one_sub_pow_le (hη : 0 < η) (k : ℕ) (x : ℝ) :
    |(1 - x) ^ k| ≤ k.factorial / η ^ k * Real.exp η * Real.exp (η * |x|) := by
  have hx1 : |1 - x| ≤ 1 + |x| := by
    rw [abs_le]
    constructor <;> linarith [abs_nonneg x, le_abs_self x, neg_abs_le x]
  have ht : 0 ≤ η * (1 + |x|) := by positivity
  have h1 := Real.pow_div_factorial_le_exp _ ht k
  rw [div_le_iff₀ (by positivity)] at h1
  have hηk : 0 < η ^ k := pow_pos hη k
  rw [abs_pow]
  calc |1 - x| ^ k ≤ (1 + |x|) ^ k := pow_le_pow_left₀ (abs_nonneg _) hx1 k
    _ = (η * (1 + |x|)) ^ k / η ^ k := by rw [mul_pow]; field_simp
    _ ≤ Real.exp (η * (1 + |x|)) * k.factorial / η ^ k := by gcongr
    _ = k.factorial / η ^ k * Real.exp η * Real.exp (η * |x|) := by
        rw [mul_add, mul_one, Real.exp_add]
        ring

theorem integrable_pow_mul_of_sobolev (hφ : CepsSobolevClass m η φ) (hη : 0 < η) (k : ℕ) :
    Integrable (fun x => (1 - x) ^ k * φ x) := by
  have hw : Integrable fun x => Real.exp (η * |x|) * |φ x| := by
    refine hφ.integrable_zero.norm.congr (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine (hw.const_mul (k.factorial / η ^ k * Real.exp η)).mono'
    ((by fun_prop : Continuous fun x : ℝ => (1 - x) ^ k).mul hφ.continuous).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (abs_one_sub_pow_le hη k x) (abs_nonneg _)

/-- `|∫ (1-x)^k ψ(x) dx| ≤ k!/η^k e^η ‖ψ‖_{m,η}`. -/
theorem abs_cepsJetMoment_le (hη : 0 < η) (k : ℕ) {ψ : ℝ → ℝ} (hψ : CepsSobolevClass m η ψ) :
    |cepsJetMoment ψ k| ≤ k.factorial / η ^ k * Real.exp η * cepsSobolev m η ψ := by
  have hw : Integrable fun x => Real.exp (η * |x|) * |ψ x| := by
    refine hψ.integrable_zero.norm.congr (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hC : 0 ≤ (k.factorial : ℝ) / η ^ k * Real.exp η := by positivity
  rw [cepsJetMoment, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hw.const_mul (k.factorial / η ^ k * Real.exp η))
    (ae_of_all _ fun x => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (abs_one_sub_pow_le hη k x) (abs_nonneg _)
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_expWeighted_abs_le_cepsSobolev m η ψ) hC

/-- The moment of order `k` is bounded by the Sobolev size, with a constant depending only on
`k` and `η`. -/
theorem abs_cepsJetMoment_le_sobolev (m : ℕ) (hη : 0 < η) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : ℝ → ℝ, CepsSobolevClass m η ψ →
      |cepsJetMoment ψ k| ≤ C * cepsSobolev m η ψ :=
  ⟨_, by positivity, fun _ hψ => abs_cepsJetMoment_le hη k hψ⟩

end Moments

end PGM
