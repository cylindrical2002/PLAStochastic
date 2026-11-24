import PLAStochastic.Index.CEPS.Actual.Defs
import PLAStochastic.Index.GEP.Response.Score.Continuity
import PLAStochastic.Index.GEP.RawDisc.Telescoping
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Renewal

/-!
# P-CEPS WP8: the complex-marked telescoping identity (P4)

For `Re t ≥ 0`, a gap law with a density on `(0, ∞)`, `T < ∞` a.s. and `E T < ∞`:

`E e^{-t S_T} = 1 - (1 - φ(t)) ∑_k E[e^{-t S_k}; T > k]`   (`ceps_telescope`),

with `φ(t) = E e^{-tX}` (`cepsLaplace`) and `E[e^{-t S_k}; T > k] = cepsSurvLaplace ν eps t k`.
Pathwise, `e^{-tS_T} - 1` is the finite telescoping sum of `1{k < T}(e^{-tS_{k+1}} - e^{-tS_k})`;
the next gap is independent of `{k < T}` and `S_k` (one-coordinate Fubini), and the partial sums are
bounded by `2`, so bounded convergence applies. Before the constant-line length every survival
probability is one, so `E[e^{-tS_k}; T > k] = φ(t)^k` for `k ≤ ⌊2ε⌋` (`cepsSurvLaplace_of_le`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- `E[e^{-t S_k}; T > k]`. -/
def cepsSurvLaplace (ν : ProbabilityMeasure ℝ) (eps : ℝ) (t : ℂ) (k : ℕ) : ℂ :=
  ∫ g, (survSet eps k).indicator (fun g => Complex.exp (-t * gapKeys g k)) g ∂(iidLaw ν)

theorem norm_cexp_neg_mul_le_one {t : ℂ} (ht : 0 ≤ t.re) {s : ℝ} (hs : 0 ≤ s) :
    ‖Complex.exp (-t * s)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith

variable {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {D : ℝ}

theorem CepsGapDensity.integrable_cexp (hf : CepsGapDensity ν f D) {t : ℂ} (ht : 0 ≤ t.re) :
    Integrable (fun x : ℝ => Complex.exp (-t * x)) (ν : Measure ℝ) := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [hf.ae_pos] with x hx
  exact norm_cexp_neg_mul_le_one ht hx.le

theorem CepsGapDensity.norm_cepsLaplace_le (hf : CepsGapDensity ν f D) {t : ℂ}
    (ht : 0 ≤ t.re) : ‖cepsLaplace ν t‖ ≤ 1 := by
  unfold cepsLaplace
  refine (norm_integral_le_of_norm_le (integrable_const (1 : ℝ)) ?_).trans (by simp)
  filter_upwards [hf.ae_pos] with x hx
  exact norm_cexp_neg_mul_le_one ht hx.le

theorem measurable_cexp_gapKeys (t : ℂ) (k : ℕ) :
    Measurable fun g : ℕ → ℝ => Complex.exp (-t * gapKeys g k) :=
  Complex.measurable_exp.comp
    (measurable_const.mul (Complex.measurable_ofReal.comp (rawAsm_measurable_gapKeys k)))

theorem measurable_survSet_cexp (eps : ℝ) (t : ℂ) (k : ℕ) :
    Measurable ((survSet eps k).indicator fun g : ℕ → ℝ => Complex.exp (-t * gapKeys g k)) :=
  (measurable_cexp_gapKeys t k).indicator (measurableSet_survSet eps k)

theorem CepsGapDensity.ae_gapKeys_nonneg (hf : CepsGapDensity ν f D) :
    ∀ᵐ g ∂(iidLaw ν), ∀ k, 0 ≤ gapKeys g k := by
  filter_upwards [hf.ae_iidLaw_pos] with g hg k
  exact gapKeys_nonneg (fun j => (hg j).le) k

theorem CepsGapDensity.norm_cepsSurvLaplace_le (hf : CepsGapDensity ν f D) (eps : ℝ) {t : ℂ}
    (ht : 0 ≤ t.re) (k : ℕ) :
    ‖cepsSurvLaplace ν eps t k‖ ≤ (iidLaw ν).real (survSet eps k) := by
  unfold cepsSurvLaplace
  have hb : ∀ᵐ g ∂(iidLaw ν), ‖(survSet eps k).indicator
      (fun g : ℕ → ℝ => Complex.exp (-t * gapKeys g k)) g‖ ≤
        (survSet eps k).indicator (fun _ => (1 : ℝ)) g := by
    filter_upwards [hf.ae_gapKeys_nonneg] with g hg
    by_cases hs : g ∈ survSet eps k
    · rw [indicator_of_mem hs, indicator_of_mem hs]
      exact norm_cexp_neg_mul_le_one ht (hg k)
    · rw [indicator_of_notMem hs, indicator_of_notMem hs, norm_zero]
  refine (norm_integral_le_of_norm_le ((integrable_const (1 : ℝ)).indicator
    (measurableSet_survSet eps k)) hb).trans (le_of_eq ?_)
  rw [integral_indicator (measurableSet_survSet eps k), setIntegral_const, smul_eq_mul, mul_one]

/-- Before the constant-line length the survival event is sure: `E[e^{-tS_k}; T > k] = φ(t)^k`. -/
theorem CepsGapDensity.cepsSurvLaplace_of_le (hf : CepsGapDensity ν f D) {eps : ℝ}
    (heps : 0 ≤ eps) {t : ℂ} (ht : 0 ≤ t.re) {k : ℕ} (hk : k ≤ ⌊2 * eps⌋₊) :
    cepsSurvLaplace ν eps t k = cepsLaplace ν t ^ k := by
  have hall : ∀ g : ℕ → ℝ, g ∈ survSet eps k := by
    intro g
    have h := constantLine_le_segLen (ConstantLineLengthCertificate.of_nonneg heps) (gapKeys g)
    show (k : ℕ∞) < gapSegLen eps g
    refine lt_of_lt_of_le ?_ h
    show (k : ℕ∞) < ((⌊2 * eps⌋₊ + 1 : ℕ) : ℕ∞)
    exact_mod_cast Nat.lt_succ_of_le hk
  unfold cepsSurvLaplace
  have e : (survSet eps k).indicator (fun g : ℕ → ℝ => Complex.exp (-t * gapKeys g k)) =
      fun g => Complex.exp ((-t) * WienerHopf.partialSum k g) := by
    funext g
    rw [indicator_of_mem (hall g)]
    rfl
  rw [e]
  exact WienerHopf.integral_cexp_partialSum (hf.integrable_cexp ht) k

/-! ## The expected length as a series of survival probabilities -/

theorem summable_measureReal_survSet {eps : ℝ}
    (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    (hT : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν)) :
    Summable (fun k => (iidLaw ν).real (survSet eps k)) ∧
      ∑' k, (iidLaw ν).real (survSet eps k) = lawC eps ν := by
  have h2 : ∫⁻ g, ENNReal.ofReal ((gapSegLen eps g).toNat : ℝ) ∂(iidLaw ν) =
      ∑' k : ℕ, iidLaw ν (survSet eps k) := by
    calc ∫⁻ g, ENNReal.ofReal ((gapSegLen eps g).toNat : ℝ) ∂(iidLaw ν)
        = ∫⁻ g, ∑' k : ℕ, (1 : ENNReal) *
            {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ENNReal)) g
            ∂(iidLaw ν) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hfin] with g hg
          obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
          rw [tsum_mul_indicator_lt hn.symm, ← hn, ENat.toNat_natCast, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul, mul_one, ENNReal.ofReal_natCast]
      _ = ∑' k : ℕ, iidLaw ν (survSet eps k) := by
          simp_rw [one_mul]
          rw [lintegral_tsum fun k =>
            (measurable_const.indicator (measurableSet_lt_gapSegLen eps k)).aemeasurable]
          congr 1
          funext k
          rw [lintegral_indicator_const (measurableSet_lt_gapSegLen eps k), one_mul]
          rfl
  have hne : ∑' k : ℕ, iidLaw ν (survSet eps k) ≠ ⊤ := by
    rw [← h2]
    have := hT.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun g => Nat.cast_nonneg _)] at this
    exact this.ne
  refine ⟨ENNReal.summable_toReal hne, ?_⟩
  rw [lawC_eq_tsum hfin]
  rfl

/-! ## Pathwise telescoping -/

/-- The increment integrand `1{k < T}(F(S_{k+1}) - F(S_k))`. -/
def cepsIncC (eps : ℝ) (t : ℂ) (k : ℕ) : (ℕ → ℝ) → ℂ :=
  (survSet eps k).indicator
    (fun g => Complex.exp (-t * gapKeys g (k + 1)) - Complex.exp (-t * gapKeys g k))

theorem measurable_cepsIncC (eps : ℝ) (t : ℂ) (k : ℕ) : Measurable (cepsIncC eps t k) :=
  ((measurable_cexp_gapKeys t (k + 1)).sub (measurable_cexp_gapKeys t k)).indicator
    (measurableSet_survSet eps k)

theorem sum_cepsIncC_eq {eps : ℝ} (t : ℂ) {g : ℕ → ℝ} {n : ℕ} (hn : gapSegLen eps g = n)
    (N : ℕ) :
    ∑ k ∈ Finset.range N, cepsIncC eps t k g =
      Complex.exp (-t * gapKeys g (min N n)) - 1 := by
  induction N with
  | zero => simp [gapKeys_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, cepsIncC]
    by_cases hN : N < n
    · rw [indicator_of_mem ((mem_survSet_iff_of_eq hn N).2 hN), min_eq_left hN.le,
        min_eq_left (show N + 1 ≤ n by omega)]
      ring
    · rw [indicator_of_notMem (fun h => hN ((mem_survSet_iff_of_eq hn N).1 h)), add_zero,
        min_eq_right (show n ≤ N by omega), min_eq_right (show n ≤ N + 1 by omega)]

theorem CepsGapDensity.norm_sum_cepsIncC_le (hf : CepsGapDensity ν f D) {eps : ℝ} {t : ℂ}
    (ht : 0 ≤ t.re) (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤) :
    ∀ᵐ g ∂(iidLaw ν), ∀ N, ‖∑ k ∈ Finset.range N, cepsIncC eps t k g‖ ≤ 2 := by
  filter_upwards [hfin, hf.ae_gapKeys_nonneg] with g hT hg N
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hT
  rw [sum_cepsIncC_eq t hn.symm N]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  linarith [norm_cexp_neg_mul_le_one ht (hg (min N n))]

/-- **The next gap is independent**: `E[1{k<T}(e^{-tS_{k+1}} - e^{-tS_k})] = (φ(t) - 1) E[e^{-tS_k}; T>k]`. -/
theorem CepsGapDensity.integral_cepsIncC (hf : CepsGapDensity ν f D) (eps : ℝ) {t : ℂ}
    (ht : 0 ≤ t.re) (k : ℕ) :
    ∫ g, cepsIncC eps t k g ∂(iidLaw ν) = (cepsLaplace ν t - 1) * cepsSurvLaplace ν eps t k := by
  have hint : Integrable (cepsIncC eps t k) (iidLaw ν) := by
    refine (integrable_const (2 : ℝ)).mono' (measurable_cepsIncC eps t k).aestronglyMeasurable ?_
    filter_upwards [hf.ae_gapKeys_nonneg] with g hg
    unfold cepsIncC
    by_cases hs : g ∈ survSet eps k
    · rw [indicator_of_mem hs]
      refine (norm_sub_le _ _).trans ?_
      linarith [norm_cexp_neg_mul_le_one ht (hg (k + 1)), norm_cexp_neg_mul_le_one ht (hg k)]
    · rw [indicator_of_notMem hs, norm_zero]; norm_num
  rw [integral_iidLaw_update ν k hint, cepsSurvLaplace, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [cepsIncC]
  by_cases hs : g ∈ survSet eps k
  · have hs' : ∀ x, Function.update g k x ∈ survSet eps k := fun x =>
      (mem_survSet_update le_rfl g x).2 hs
    simp only [indicator_of_mem (hs' _), indicator_of_mem hs, gapKeys_update_succ,
      gapKeys_update_self]
    have e : ∀ x : ℝ, Complex.exp (-t * ((gapKeys g k + x : ℝ) : ℂ)) -
        Complex.exp (-t * (gapKeys g k : ℂ)) =
        Complex.exp (-t * (gapKeys g k : ℂ)) * Complex.exp (-t * (x : ℂ)) -
          Complex.exp (-t * (gapKeys g k : ℂ)) := by
      intro x
      rw [← Complex.exp_add]
      push_cast
      ring_nf
    simp_rw [e]
    rw [integral_sub ((hf.integrable_cexp ht).const_mul _) (integrable_const _),
      integral_const_mul, integral_const, probReal_univ, one_smul]
    unfold cepsLaplace
    ring
  · have hs' : ∀ x, Function.update g k x ∉ survSet eps k := fun x h =>
      hs ((mem_survSet_update le_rfl g x).1 h)
    simp only [indicator_of_notMem (hs' _), indicator_of_notMem hs, integral_zero, mul_zero]

/-! ## The telescoping identity -/

/-- **The complex-marked telescoping identity (P4).** -/
theorem CepsGapDensity.ceps_telescope (hf : CepsGapDensity ν f D) {eps : ℝ}
    (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    (hT : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν)) {t : ℂ}
    (ht : 0 ≤ t.re) :
    Summable (fun k => ‖cepsSurvLaplace ν eps t k‖) ∧
      ∫ g, Complex.exp (-t * stopSum eps g) ∂(iidLaw ν) =
        1 - (1 - cepsLaplace ν t) * ∑' k, cepsSurvLaplace ν eps t k := by
  have hsumP := (summable_measureReal_survSet hfin hT).1
  have hsum : Summable (fun k => ‖cepsSurvLaplace ν eps t k‖) :=
    hsumP.of_nonneg_of_le (fun k => norm_nonneg _) (hf.norm_cepsSurvLaplace_le eps ht)
  refine ⟨hsum, ?_⟩
  have hmS : Measurable fun g : ℕ → ℝ => Complex.exp (-t * stopSum eps g) :=
    Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_stopSum eps)))
  have hSb : ∀ᵐ g ∂(iidLaw ν), ‖Complex.exp (-t * stopSum eps g)‖ ≤ 1 := by
    filter_upwards [hf.ae_gapKeys_nonneg] with g hg
    exact norm_cexp_neg_mul_le_one ht (hg _)
  have hSint : Integrable (fun g => Complex.exp (-t * stopSum eps g)) (iidLaw ν) :=
    (integrable_const (1 : ℝ)).mono' hmS.aestronglyMeasurable hSb
  -- bounded convergence of the partial sums
  have hlim : Tendsto (fun N => ∫ g, ∑ k ∈ Finset.range N, cepsIncC eps t k g ∂(iidLaw ν))
      atTop (𝓝 (∫ g, (Complex.exp (-t * stopSum eps g) - 1) ∂(iidLaw ν))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
      (fun N => (Finset.measurable_sum _ fun k _ =>
        measurable_cepsIncC eps t k).aestronglyMeasurable) (integrable_const _)
      (fun N => (hf.norm_sum_cepsIncC_le ht hfin).mono fun g hg => hg N) ?_
    filter_upwards [hfin] with g hT'
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hT'
    refine tendsto_atTop_of_eventually_const (i₀ := n) fun N hN => ?_
    rw [sum_cepsIncC_eq t hn.symm N, min_eq_right hN, stopSum_of_eq hn.symm]
  have hpart : ∀ N, ∫ g, ∑ k ∈ Finset.range N, cepsIncC eps t k g ∂(iidLaw ν) =
      (cepsLaplace ν t - 1) * ∑ k ∈ Finset.range N, cepsSurvLaplace ν eps t k := by
    intro N
    rw [integral_finsetSum, Finset.mul_sum]
    · exact Finset.sum_congr rfl fun k _ => hf.integral_cepsIncC eps ht k
    · intro k _
      refine (integrable_const (2 : ℝ)).mono' (measurable_cepsIncC eps t k).aestronglyMeasurable ?_
      filter_upwards [hf.ae_gapKeys_nonneg] with g hg
      unfold cepsIncC
      by_cases hs : g ∈ survSet eps k
      · rw [indicator_of_mem hs]
        refine (norm_sub_le _ _).trans ?_
        linarith [norm_cexp_neg_mul_le_one ht (hg (k + 1)), norm_cexp_neg_mul_le_one ht (hg k)]
      · rw [indicator_of_notMem hs, norm_zero]; norm_num
  simp_rw [hpart] at hlim
  have hlim' : Tendsto (fun N => (cepsLaplace ν t - 1) *
      ∑ k ∈ Finset.range N, cepsSurvLaplace ν eps t k) atTop
      (𝓝 ((cepsLaplace ν t - 1) * ∑' k, cepsSurvLaplace ν eps t k)) :=
    (hsum.of_norm.hasSum.tendsto_sum_nat).const_mul _
  have heq := tendsto_nhds_unique hlim hlim'
  rw [integral_sub hSint (integrable_const _), integral_const, probReal_univ, one_smul] at heq
  linear_combination heq

end

end PGM
