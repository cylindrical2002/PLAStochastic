import PLAStochastic.Index.CEPS.Assembly.Composition
import PLAStochastic.ForMathlib.Analysis.Fourier.DensityRepresentative
import PLAStochastic.ForMathlib.Analysis.Fourier.DerivativeDecay
import PLAStochastic.ForMathlib.Analysis.Fourier.WeightedRemainder
import PLAStochastic.Index.CEPS.Output.Sobolev
import PLAStochastic.Index.GEP.OrbitClosure.Main

/-!
# Track F: inputs in the class, the high band, and the output density

* An expanding family eventually lies in every weighted Sobolev ball around `Λ`
  (`CepsFamilyExpansion.eventually_inputClass`), so T1, T5 and T2 apply to it.
* The proved high band T2 holds along the family for every order `r` with `r + 3 ≤ m`
  (`CepsFamilyExpansion.eventually_high`).
* A regular law whose characteristic function decays quadratically has a continuous,
  nonnegative, integrable density with the same exponential envelope, namely the angular
  inverse of its characteristic function (`RegLaw.continuous_density`); orbit closure supplies
  the regular class of the output (`ceps_output_density`).
* The angular inverse of `φ_Λ` is the density of `Λ` (`angularRealInverse_cepsLambdaChar`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset

/-! ## Weighted Sobolev algebra -/

theorem CepsSobolevClass.mono_order {m₀ m : ℕ} {η : ℝ} {f : ℝ → ℝ} (h : CepsSobolevClass m η f)
    (hm : m₀ ≤ m) : CepsSobolevClass m₀ η f :=
  ⟨h.contDiff.of_le (by exact_mod_cast hm), fun r hr => h.integrable r (hr.trans hm)⟩

theorem cepsSobolev_mono_order {m₀ m : ℕ} (hm : m₀ ≤ m) (η : ℝ) (f : ℝ → ℝ) :
    cepsSobolev m₀ η f ≤ cepsSobolev m η f :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun _ _ _ =>
    integral_nonneg fun _ => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)

theorem CepsSobolevClass.iteratedDeriv_add {m : ℕ} {η : ℝ} {f g : ℝ → ℝ}
    (hf : CepsSobolevClass m η f) (hg : CepsSobolevClass m η g) {r : ℕ} (hr : r ≤ m) :
    iteratedDeriv r (fun x => f x + g x) = fun x => iteratedDeriv r f x + iteratedDeriv r g x :=
  funext fun _ => iteratedDeriv_fun_add
    ((hf.contDiff.of_le (by exact_mod_cast hr)).contDiffAt)
    ((hg.contDiff.of_le (by exact_mod_cast hr)).contDiffAt)

theorem CepsSobolevClass.add {m : ℕ} {η : ℝ} {f g : ℝ → ℝ} (hf : CepsSobolevClass m η f)
    (hg : CepsSobolevClass m η g) : CepsSobolevClass m η (fun x => f x + g x) where
  contDiff := hf.contDiff.add hg.contDiff
  integrable r hr := by
    rw [hf.iteratedDeriv_add hg hr]
    refine ((hf.integrable r hr).add (hg.integrable r hr)).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]
    ring

theorem CepsSobolevClass.const_mul {m : ℕ} {η : ℝ} {f : ℝ → ℝ} (hf : CepsSobolevClass m η f)
    (c : ℝ) : CepsSobolevClass m η (fun x => c * f x) where
  contDiff := contDiff_const.mul hf.contDiff
  integrable r hr := by
    have he : iteratedDeriv r (fun x => c * f x) = fun x => c * iteratedDeriv r f x :=
      funext fun _ => iteratedDeriv_const_mul_field c f
    rw [he]
    simpa only [mul_left_comm] using (hf.integrable r hr).const_mul c

theorem CepsSobolevClass.sub {m : ℕ} {η : ℝ} {f g : ℝ → ℝ} (hf : CepsSobolevClass m η f)
    (hg : CepsSobolevClass m η g) : CepsSobolevClass m η (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg, neg_one_mul] using hf.add (hg.const_mul (-1))

theorem CepsSobolevClass.sum {ι : Type*} (s : Finset ι) {m : ℕ} {η : ℝ} {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ s, CepsSobolevClass m η (F i)) :
    CepsSobolevClass m η (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using cepsSobolevClass_zero m η
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (hF a (mem_insert_self a s)).add (ih fun i hi => hF i (mem_insert_of_mem hi))

theorem CepsSobolevClass.integrable_abs {m : ℕ} {η : ℝ} {f : ℝ → ℝ}
    (hf : CepsSobolevClass m η f) {r : ℕ} (hr : r ≤ m) :
    Integrable (fun x => Real.exp (η * |x|) * |iteratedDeriv r f x|) := by
  simpa only [Real.norm_eq_abs, abs_mul, Real.abs_exp] using (hf.integrable r hr).norm

theorem cepsSobolev_add_le {m : ℕ} {η : ℝ} {f g : ℝ → ℝ} (hf : CepsSobolevClass m η f)
    (hg : CepsSobolevClass m η g) :
    cepsSobolev m η (fun x => f x + g x) ≤ cepsSobolev m η f + cepsSobolev m η g := by
  unfold cepsSobolev
  rw [← sum_add_distrib]
  refine sum_le_sum fun r hr => ?_
  have hr' : r ≤ m := by have := mem_range.mp hr; omega
  rw [hf.iteratedDeriv_add hg hr', ← integral_add (hf.integrable_abs hr') (hg.integrable_abs hr')]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
    ((hf.integrable_abs hr').add (hg.integrable_abs hr')) (ae_of_all _ fun x => ?_)
  have h := abs_add_le (iteratedDeriv r f x) (iteratedDeriv r g x)
  have he := (Real.exp_pos (η * |x|)).le
  simp only
  nlinarith

theorem cepsSobolev_const_mul {m : ℕ} (η c : ℝ) (f : ℝ → ℝ) :
    cepsSobolev m η (fun x => c * f x) = |c| * cepsSobolev m η f := by
  unfold cepsSobolev
  rw [mul_sum]
  refine sum_congr rfl fun r _ => ?_
  have he : iteratedDeriv r (fun x => c * f x) = fun x => c * iteratedDeriv r f x :=
    funext fun _ => iteratedDeriv_const_mul_field c f
  rw [he, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [abs_mul]
  ring

theorem cepsSobolev_sum_le {ι : Type*} (s : Finset ι) {m : ℕ} {η : ℝ} {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ s, CepsSobolevClass m η (F i)) :
    cepsSobolev m η (fun x => ∑ i ∈ s, F i x) ≤ ∑ i ∈ s, cepsSobolev m η (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cepsSobolev]
  | insert a s ha ih =>
    simp only [sum_insert ha]
    have hs := CepsSobolevClass.sum s fun i hi => hF i (mem_insert_of_mem hi)
    exact (cepsSobolev_add_le (hF a (mem_insert_self a s)) hs).trans
      (add_le_add le_rfl (ih fun i hi => hF i (mem_insert_of_mem hi)))

theorem CepsFamilyExpansion.mono_order {ν : ℝ → ProbabilityMeasure ℝ} {m₀ m : ℕ} {η : ℝ}
    {P : ℕ} {g : ℕ → ℝ → ℝ} (h : CepsFamilyExpansion ν m η P g) (hm : m₀ ≤ m) :
    CepsFamilyExpansion ν m₀ η P g where
  reference := h.reference.mono_order hm
  coeff n hn := (h.coeff n hn).mono_order hm
  density := by
    obtain ⟨f, hfev, K, e0, hK⟩ := h.density
    refine ⟨f, hfev.mono fun eps he => ⟨he.1, he.2.1.mono_order hm, he.2.2⟩, K, e0,
      fun eps heps => ?_⟩
    refine le_trans ?_ (hK eps heps)
    rw [abs_of_nonneg (cepsSobolev_nonneg _ _ _), abs_of_nonneg (cepsSobolev_nonneg _ _ _)]
    exact cepsSobolev_mono_order hm _ _

/-! ## Expanding families lie eventually in every Sobolev ball around `Λ` -/

/-- The density of an expanding family approaches the reference density at rate `h`. -/
theorem CepsFamilyExpansion.close {ν : ℝ → ProbabilityMeasure ℝ} {m : ℕ} {η : ℝ}
    {P : ℕ} {g : ℕ → ℝ → ℝ} (h : CepsFamilyExpansion ν m η P g) :
    ∃ f : ℝ → ℝ → ℝ, (∀ᶠ eps in atTop, (∀ x, 0 ≤ f eps x) ∧ CepsSobolevClass m η (f eps) ∧
      (ν eps : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f eps x))) ∧
      IsInverseOrder (fun eps => cepsSobolev m η (fun x => f eps x - cepsLambdaDensity x)) 1 := by
  obtain ⟨f, hfev, K, e0, hK⟩ := h.density
  refine ⟨f, hfev, ?_⟩
  set S : ℝ → ℝ → ℝ := fun eps x => ∑ n ∈ Icc 1 P, (eps⁻¹) ^ n * g n x
  set B : ℝ := ∑ n ∈ Icc 1 P, cepsSobolev m η (g n)
  have hB : 0 ≤ B := sum_nonneg fun _ _ => cepsSobolev_nonneg _ _ _
  obtain ⟨e1, he1⟩ := eventually_atTop.mp hfev
  refine ⟨|K| + B, max 1 (max e0 e1), fun eps heps => ?_⟩
  have h1 : 1 ≤ eps := (le_max_left _ _).trans heps
  have hi0 : 0 ≤ eps⁻¹ := by positivity
  have hi1 : eps⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr h1
  have hcl := (he1 eps ((le_max_right _ _).trans ((le_max_right _ _).trans heps))).2.1
  have hKe := hK eps ((le_max_left _ _).trans ((le_max_right _ _).trans heps))
  rw [abs_of_nonneg (cepsSobolev_nonneg _ _ _)] at hKe
  have hSc : CepsSobolevClass m η (S eps) :=
    CepsSobolevClass.sum _ fun n hn => (h.coeff n hn).const_mul _
  have hRc : CepsSobolevClass m η (fun x => f eps x - cepsLambdaDensity x - S eps x) :=
    (hcl.sub h.reference).sub hSc
  have hsplit : (fun x => f eps x - cepsLambdaDensity x) =
      fun x => (f eps x - cepsLambdaDensity x - S eps x) + S eps x := by
    funext x; ring
  have hSle : cepsSobolev m η (S eps) ≤ eps⁻¹ * B := by
    refine (cepsSobolev_sum_le _ fun n hn => (h.coeff n hn).const_mul _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    rw [cepsSobolev_const_mul, abs_of_nonneg (pow_nonneg hi0 _)]
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    exact mul_le_mul_of_nonneg_right
      ((pow_le_pow_of_le_one hi0 hi1 hn1).trans_eq (pow_one _)) (cepsSobolev_nonneg _ _ _)
  rw [abs_of_nonneg (cepsSobolev_nonneg _ _ _), hsplit]
  have hP : (eps⁻¹) ^ (P + 1) ≤ eps⁻¹ :=
    (pow_le_pow_of_le_one hi0 hi1 (by omega)).trans_eq (pow_one _)
  calc
    _ ≤ cepsSobolev m η (fun x => f eps x - cepsLambdaDensity x - S eps x) +
        cepsSobolev m η (S eps) := cepsSobolev_add_le hRc hSc
    _ ≤ |K| * eps⁻¹ + eps⁻¹ * B := by
      refine add_le_add ?_ hSle
      calc
        _ ≤ K * (eps⁻¹) ^ (P + 1) := hKe
        _ ≤ |K| * (eps⁻¹) ^ (P + 1) := by gcongr; exact le_abs_self K
        _ ≤ |K| * eps⁻¹ := by gcongr
    _ = (|K| + B) * (eps⁻¹) ^ 1 := by ring

/-- **Class membership.** An expanding regular family eventually lies in every input class
of lower derivative order. -/
theorem CepsFamilyExpansion.eventually_inputClass {ν : ℝ → ProbabilityMeasure ℝ} {m : ℕ}
    {η : ℝ} {P : ℕ} {g : ℕ → ℝ → ℝ} (h : CepsFamilyExpansion ν m η P g) {D θ vlo vhi : ℝ}
    (hreg : ∀ᶠ eps in atTop, RegLaw D θ vlo vhi (ν eps)) {m₀ : ℕ} (hm : m₀ ≤ m) {r : ℝ}
    (hr : 0 < r) : ∀ᶠ eps in atTop, CepsInputClass D θ vlo vhi m₀ η r (ν eps) := by
  obtain ⟨f, hfev, hclose⟩ := h.close
  have ht := hclose.tendsto_zero one_pos
  have hsmall : ∀ᶠ eps in atTop,
      cepsSobolev m η (fun x => f eps x - cepsLambdaDensity x) < r := by
    have := (Metric.tendsto_nhds.mp ht) r hr
    filter_upwards [this] with eps he
    rw [Real.dist_eq, sub_zero] at he
    exact (le_abs_self _).trans_lt he
  filter_upwards [hfev, hreg, hsmall] with eps hf hrg hs
  exact ⟨hrg, h.reference.mono_order hm, f eps, hf.1, hf.2.1.mono_order hm, hf.2.2,
    ((cepsSobolev_mono_order hm _ _).trans hs.le)⟩

/-- **The high band T2 along an expanding family.** -/
theorem CepsFamilyExpansion.eventually_high {ν : ℝ → ProbabilityMeasure ℝ} {m : ℕ}
    {η : ℝ} {P : ℕ} {g : ℕ → ℝ → ℝ} (h : CepsFamilyExpansion ν m η P g) (hη : 0 < η)
    {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hreg : ∀ᶠ eps in atTop, RegLaw D θ vlo vhi (ν eps)) {r : ℕ} (hr : r + 3 ≤ m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ eps in atTop, ∀ u : ℝ,
      |u| ^ r * ‖cepsOutChar eps (ν eps) u‖ ≤ K * eps ^ (r + 2) := by
  have hΛ : CepsSobolevClass (r + 3) η cepsLambdaDensity := h.reference.mono_order hr
  obtain ⟨K, e0, -, hK⟩ := norm_charFun_lawPhi_le_of_cepsSobolev r hD hθ hvlo hη
    (vhi := vhi) (R := cepsSobolev (r + 3) η cepsLambdaDensity + 1)
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  filter_upwards [h.eventually_inputClass hreg hr one_pos, eventually_ge_atTop e0,
    eventually_ge_atTop (0 : ℝ)] with eps hcl he he0 u
  obtain ⟨f, hf0, hfc, hν, hclose⟩ := hcl.density
  have hdiff : CepsSobolevClass (r + 3) η (fun x => f x - cepsLambdaDensity x) := hfc.sub hΛ
  have hR : cepsSobolev (r + 3) η f ≤ cepsSobolev (r + 3) η cepsLambdaDensity + 1 := by
    have hsplit : f = fun x => cepsLambdaDensity x + (f x - cepsLambdaDensity x) := by
      funext x; ring
    have h1 := cepsSobolev_add_le hΛ hdiff
    rw [← hsplit] at h1
    linarith
  refine (hK eps he (ν eps) f hcl.reg hf0 hν hfc hR u).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-! ## Characteristic integrals of densities -/

/-- The characteristic function of a law, in the convention of T1 and T2. -/
def cepsChar (μ : ProbabilityMeasure ℝ) (u : ℝ) : ℂ :=
  ∫ x, Complex.exp (Complex.I * u * x) ∂(μ : Measure ℝ)

theorem cepsChar_lawPhi (eps : ℝ) (ν : ProbabilityMeasure ℝ) :
    cepsChar (lawPhi eps ν) = cepsOutChar eps ν := rfl

theorem cepsChar_cepsLambda : cepsChar cepsLambda = cepsLambdaChar := rfl

theorem norm_cepsChar_le_one (μ : ProbabilityMeasure ℝ) (u : ℝ) : ‖cepsChar μ u‖ ≤ 1 := by
  have h : cepsChar μ u = charFun (μ : Measure ℝ) u := by
    rw [charFun_apply_real, cepsChar]
    congr 1
    funext x
    ring_nf
  rw [h]
  exact norm_charFun_le_one u

/-- Integrals against a law with a density, in the form used by the inversion assembly. -/
theorem integral_exp_withDensity {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x) (u : ℝ) :
    ∫ x, Complex.exp (Complex.I * u * x) ∂(volume.withDensity fun x => ENNReal.ofReal (f x)) =
      ∫ x, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (f x : ℂ) := by
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hnn x), Complex.real_smul]
  push_cast
  ring_nf

/-- A regular law whose characteristic function decays quadratically has a continuous density:
the angular inverse of its characteristic function. -/
theorem RegLaw.continuous_density {A θ vlo vhi K : ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : RegLaw A θ vlo vhi μ) (hθ : 0 < θ) (hK : ∀ u : ℝ, |u| ^ 2 * ‖cepsChar μ u‖ ≤ K) :
    (∀ x, 0 ≤ angularRealInverse (cepsChar μ) x) ∧
      Continuous (angularRealInverse (cepsChar μ)) ∧
      Integrable (angularRealInverse (cepsChar μ)) ∧
      (∀ x, |angularRealInverse (cepsChar μ) x| ≤ A * Real.exp (-θ * |x|)) ∧
      ((μ : Measure ℝ) =
        volume.withDensity (fun x => ENNReal.ofReal (angularRealInverse (cepsChar μ) x))) ∧
      cepsChar μ = fun u =>
        ∫ x, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (angularRealInverse (cepsChar μ) x : ℂ) := by
  obtain ⟨f, hfm, hf0, hfneg, hfle, hμf⟩ := hμ.density
  have hA : 0 ≤ A :=
    (mul_nonneg_iff_of_pos_right (Real.exp_pos (-θ * 1))).mp ((hf0 1).trans (hfle 1))
  have henv : ∀ x, f x ≤ A * Real.exp (-θ * |x|) := by
    intro x
    by_cases hx : x ≤ 0
    · rw [hfneg x hx]
      positivity
    · rw [abs_of_pos (lt_of_not_ge hx)]
      exact hfle x
  have hfi : Integrable f := by
    refine ((integrable_exp_neg_abs hθ).const_mul A).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    exact henv x
  have hchar : cepsChar μ = fun u =>
      ∫ x, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (f x : ℂ) := by
    funext u
    rw [cepsChar, hμf, integral_exp_withDensity hfm hf0]
  have hφi : Integrable (cepsChar μ) := by
    refine integrable_of_norm_le_div_one_add_sq (C := 1 + K) ?_ fun u => ?_
    · rw [hchar]
      exact (continuous_charIntegral hfi).aestronglyMeasurable
    · have h1 := norm_cepsChar_le_one μ u
      have h2 := hK u
      rw [sq_abs] at h2
      rw [le_div_iff₀ (by positivity)]
      nlinarith [norm_nonneg (cepsChar μ u)]
  have hae : angularRealInverse (cepsChar μ) =ᵐ[volume] f := by
    have h := angularRealInverse_charIntegral_ae_eq hfi (by rw [← hchar]; exact hφi)
    rwa [← hchar] at h
  have hcont := continuous_angularRealInverse hφi
  have hnn : ∀ x, 0 ≤ angularRealInverse (cepsChar μ) x :=
    le_of_ae_le_of_continuous continuous_const hcont
      (hae.mono fun x hx => by rw [hx]; exact hf0 x)
  have hle : ∀ x, angularRealInverse (cepsChar μ) x ≤ A * Real.exp (-θ * |x|) :=
    le_of_ae_le_of_continuous hcont (by fun_prop) (hae.mono fun x hx => by rw [hx]; exact henv x)
  refine ⟨hnn, hcont, hfi.congr hae.symm, fun x => by rw [abs_of_nonneg (hnn x)]; exact hle x,
    ?_, ?_⟩
  · rw [hμf]
    exact withDensity_congr_ae (hae.mono fun x hx => by rw [hx]) |>.symm
  · funext u
    conv_lhs => rw [hchar]
    exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])

/-- The continuous density representative of the actual output. -/
def cepsOutDensity (eps : ℝ) (ν : ProbabilityMeasure ℝ) : ℝ → ℝ :=
  angularRealInverse (cepsOutChar eps ν)

/-- **The output density.** Orbit closure puts the output in a regular class; with quadratic
decay of its characteristic function the output has a continuous density with a common
exponential envelope. -/
theorem ceps_output_density {ν : ℝ → ProbabilityMeasure ℝ} {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hreg : ∀ᶠ eps in atTop, RegLaw D θ vlo vhi (ν eps))
    (hhigh : ∀ᶠ eps in atTop, ∃ K : ℝ, ∀ u : ℝ, |u| ^ 2 * ‖cepsOutChar eps (ν eps) u‖ ≤ K) :
    ∃ A θ' : ℝ, 0 ≤ A ∧ 0 < θ' ∧ ∀ᶠ eps in atTop,
      (∀ x, 0 ≤ cepsOutDensity eps (ν eps) x) ∧ Continuous (cepsOutDensity eps (ν eps)) ∧
      Integrable (cepsOutDensity eps (ν eps)) ∧
      (∀ x, |cepsOutDensity eps (ν eps) x| ≤ A * Real.exp (-θ' * |x|)) ∧
      ((lawPhi eps (ν eps) : Measure ℝ) =
        volume.withDensity (fun x => ENNReal.ofReal (cepsOutDensity eps (ν eps) x))) ∧
      cepsOutChar eps (ν eps) = fun u =>
        ∫ x, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (cepsOutDensity eps (ν eps) x : ℂ) := by
  obtain ⟨D', θ', vlo', vhi', e0, hD', hθ', -, -, hcl⟩ := orbitClosure D θ vlo vhi hD hθ hvlo hv
  refine ⟨D', θ', hD'.le, hθ', ?_⟩
  filter_upwards [hreg, hhigh, eventually_ge_atTop e0] with eps hr hh he
  obtain ⟨K, hK⟩ := hh
  have hout : RegLaw D' θ' vlo' vhi' (lawPhi eps (ν eps)) := by
    simpa only [Function.iterate_one] using hcl eps he (ν eps) hr 1
  exact hout.continuous_density hθ' hK

/-! ## The reference law -/

theorem cepsLambdaChar_eq (u : ℝ) : cepsLambdaChar u =
    ∫ x, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (cepsLambdaDensity x : ℂ) := by
  rw [cepsLambdaChar, cepsLambda_eq_withDensity, integral_exp_withDensity
    contDiff_cepsLambdaDensity.continuous.measurable cepsLambdaDensity_nonneg]

theorem integrable_iteratedDeriv_cepsLambdaDensity (r : ℕ) :
    Integrable (iteratedDeriv r cepsLambdaDensity) := by
  obtain ⟨η, hη, hi⟩ := cepsLambdaDensity_finite_jet_integrability r
  refine (hi r le_rfl).norm.mono' (contDiff_cepsLambdaDensity.continuous_iteratedDeriv r
    (by exact_mod_cast le_top)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp]
  have h1 : 1 ≤ Real.exp (η * |x|) := Real.one_le_exp (by positivity)
  nlinarith [abs_nonneg (iteratedDeriv r cepsLambdaDensity x)]

theorem integrable_cepsLambdaChar : Integrable cepsLambdaChar := by
  have hfi := integrable_iteratedDeriv_cepsLambdaDensity
  have hd : ∀ j < 2, ∀ x, HasDerivAt (fun y => iteratedDeriv j cepsLambdaDensity y)
      (iteratedDeriv (j + 1) cepsLambdaDensity x) x := by
    intro j _ x
    rw [iteratedDeriv_succ]
    exact ((contDiff_cepsLambdaDensity.differentiable_iteratedDeriv j
      (by exact_mod_cast WithTop.coe_lt_top _)) x).hasDerivAt
  set C₀ := ∫ x, |cepsLambdaDensity x|
  set C₂ := ∫ x, |iteratedDeriv 2 cepsLambdaDensity x|
  refine integrable_of_norm_le_div_one_add_sq (C := C₀ + C₂) ?_ fun u => ?_
  · have hc : Continuous cepsLambdaChar := by
      have he : cepsLambdaChar = fun u =>
          ∫ x, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (cepsLambdaDensity x : ℂ) :=
        funext cepsLambdaChar_eq
      rw [he]
      exact continuous_charIntegral (by simpa only [iteratedDeriv_zero] using hfi 0)
    exact hc.aestronglyMeasurable
  · have h2 := abs_pow_mul_norm_integral_exp_le (k := 2)
      (F := fun j => iteratedDeriv j cepsLambdaDensity) hd (fun j _ => hfi j) u
    simp only [iteratedDeriv_zero] at h2
    rw [← cepsLambdaChar_eq] at h2
    have h0 : ‖cepsLambdaChar u‖ ≤ C₀ := by
      rw [cepsLambdaChar_eq]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    rw [sq_abs] at h2
    rw [le_div_iff₀ (by positivity)]
    nlinarith [norm_nonneg (cepsLambdaChar u)]

/-- The angular inverse of `φ_Λ` is the density of `Λ`. -/
theorem angularRealInverse_cepsLambdaChar : angularRealInverse cepsLambdaChar = cepsLambdaDensity := by
  have he : cepsLambdaChar = fun u =>
      ∫ x, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (cepsLambdaDensity x : ℂ) :=
    funext cepsLambdaChar_eq
  have hfi : Integrable cepsLambdaDensity := by
    simpa only [iteratedDeriv_zero] using integrable_iteratedDeriv_cepsLambdaDensity 0
  have h := angularInverse_charIntegral hfi contDiff_cepsLambdaDensity.continuous
    (by rw [← he]; exact integrable_cepsLambdaChar)
  rw [← he] at h
  funext x
  simp only [angularRealInverse, h, Complex.ofReal_re]

end

end PGM
