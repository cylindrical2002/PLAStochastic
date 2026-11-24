import PLAStochastic.Index.GEP.Kernel.Tilt.NormalizedLaw
import PLAStochastic.Index.GEP.StrongApprox.Saddle.RateTaylor

/-! # Class-uniform exponential rates for the actual tilted gap laws -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology

/-- The exponent appearing in the actual killed-kernel change of law. -/
def kernelTiltRate (ν : ProbabilityMeasure ℝ) (a lam : ℝ) : ℝ :=
  lam / a - cgf id (ν : Measure ℝ) lam

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

theorem UnivClass.kernel_raw_cgf_eq (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| ≤ θ) :
    cgf id (ν : Measure ℝ) lam =
      lam + cgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam := by
  have hpos := mgf_pos' (NeZero.ne (ν : Measure ℝ)) (h.integrable_exp_centered hlam)
  have hm : mgf id (ν : Measure ℝ) lam =
      mgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam * Real.exp lam := by
    change mgf (fun x : ℝ => x) (ν : Measure ℝ) lam = _
    simpa only [sub_add_cancel, mul_one] using
      (mgf_add_const (X := fun x : ℝ => x - 1) (μ := (ν : Measure ℝ)) (t := lam) 1)
  change Real.log (mgf id (ν : Measure ℝ) lam) = _
  rw [hm, Real.log_mul hpos.ne' (Real.exp_ne_zero _), Real.log_exp]
  unfold cgf
  ring

theorem UnivClass.kernelTiltRate_eq_centered (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| ≤ θ) (a : ℝ) :
    kernelTiltRate ν a lam = lam * (1 / a - 1) -
      cgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam := by
  rw [kernelTiltRate, h.kernel_raw_cgf_eq hlam]
  ring

/-- The common small-tilt interval has a uniform quadratic cumulant upper bound. -/
theorem UnivClass.kernel_centered_cgf_upper (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {t : ℝ} (ht : |t| ≤ saTiltRadius vlo B θ) :
    cgf (fun x : ℝ => x - 1) (ν : Measure ℝ) t ≤ vhi * t ^ 2 := by
  by_cases ht0 : t = 0
  · simp [ht0]
  let f := cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)
  have hwin : uIcc 0 t ⊆ Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ) :=
    (convex_Icc _ _).ordConnected.uIcc_subset
      (by constructor <;> linarith [saTiltRadius_pos (B := B) hvlo hθ]) (abs_le.mp ht)
  have hana (z : ℝ) (hz : z ∈ uIcc 0 t) : AnalyticAt ℝ f z :=
    analyticAt_cgf (h.centered_mem_interior
      (lt_of_le_of_lt ((abs_le.mpr (hwin hz)).trans (saTiltRadius_le_half vlo B hθ))
        (by linarith)))
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (n := 1) (x₀ := 0) (x := t) (Ne.symm ht0)
    (fun z hz => (hana z hz).contDiffAt.contDiffWithinAt)
  have hdif := uniqueDiffOn_uIcc (Ne.symm ht0)
  have hd (k : ℕ) : iteratedDerivWithin k f (uIcc 0 t) 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hdif
      (hana 0 left_mem_uIcc).contDiffAt left_mem_uIcc
  have hf0 : f 0 = 0 := by simp [f]
  have hf'0 : deriv f 0 = 0 := h.deriv_centered_cgf_zero hθ
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, hd, iteratedDeriv_one,
    Nat.factorial, Nat.cast_one, Nat.cast_zero, zero_add, Nat.cast_mul, mul_one,
    smul_eq_mul, hf0, hf'0, sub_zero] at he
  have hhi := (h.centered_cgf_variance_bracket hvlo hθ
    (abs_le.mpr (hwin ⟨hz.1.le, hz.2.le⟩))).2
  have hp := mul_le_mul_of_nonneg_right
    (show iteratedDeriv 2 f z ≤ 5 / 4 * vhi by nlinarith [h.var_le]) (sq_nonneg t)
  have hvhi : 0 ≤ vhi := by linarith [h.var_ge, h.var_le]
  norm_num at he
  change f t ≤ vhi * t ^ 2
  nlinarith [mul_nonneg hvhi (sq_nonneg t)]

/-- The WP5 Taylor theorem specialized to the original, unsmoothed law. -/
theorem UnivClass.kernel_saRate_quadratic_error (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {w : ℝ}
    (hw : |w| ≤ saMeanRadius vlo B θ) :
    |saRate vlo B θ ν 0 w - w ^ 2 / (2 * lawVar ν)| ≤
      saRateThird vlo B θ * |w| ^ 3 / 6 := by
  have hz : |(0 : ℝ)| < 3 / 4 * vlo * saTiltRadius vlo B θ := by
    have := saTiltRadius_pos (B := B) hvlo hθ
    simp only [abs_zero]
    positivity
  have ht := h.saRate_taylor_two hvlo hθ (0 : ℝ) (u := 0) (t := w)
    (by simpa using hw)
  rw [h.saRate_zero hvlo hθ 0, h.deriv_saRate hvlo hθ 0 hz,
    h.saSaddle_zero hvlo hθ 0, h.iteratedDeriv_two_saRate_zero hvlo hθ 0] at ht
  simp only [zero_add, sub_zero, zero_mul] at ht
  convert ht using 1
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The proved WP5 saddle expansion yields a positive quadratic rate. -/
theorem UnivClass.kernel_saRate_lower (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {w : ℝ}
    (hw : |w| ≤ saMeanRadius vlo B θ)
    (hsmall : 4 * saRateThird vlo B θ * vhi * |w| ≤ 1) :
    w ^ 2 / (4 * vhi) ≤ saRate vlo B θ ν 0 w := by
  have hv : 0 < lawVar ν := hvlo.trans_le h.var_ge
  have hvhi : 0 < vhi := hv.trans_le h.var_le
  have he := h.kernel_saRate_quadratic_error hvlo hθ hw
  have hcube : |w| ^ 3 = |w| * w ^ 2 := by rw [pow_succ, sq_abs]; ring
  have hrem : saRateThird vlo B θ * |w| ^ 3 / 6 ≤ w ^ 2 / (4 * vhi) := by
    rw [le_div_iff₀ (show 0 < 4 * vhi by positivity), hcube]
    have hh := mul_le_mul_of_nonneg_right hsmall (sq_nonneg w)
    nlinarith [sq_nonneg w]
  have hq : w ^ 2 / (2 * vhi) ≤ w ^ 2 / (2 * lawVar ν) :=
    div_le_div_of_nonneg_left (sq_nonneg w) (by positivity) (by linarith [h.var_le])
  have hqeq : w ^ 2 / (2 * vhi) = 2 * (w ^ 2 / (4 * vhi)) := by ring
  rw [hqeq] at hq
  linarith [(abs_le.mp he).1]


/-- The canonical WP5 saddle, evaluated at the original gap mean target. -/
def kernelTiltSaddle (D θ vlo : ℝ) (ν : ProbabilityMeasure ℝ) (a : ℝ) : ℝ :=
  saSaddle vlo (2 * D / θ) (θ / 2) ν 0 (1 / a - 1)

/-- Near slope one the actual tilt has mean `1/a` and a quadratic positive rate.
The neighborhood, tilt radius, and rate constant are uniform over the class. -/
theorem kernel_regLaw_saddle_rate (D θ vlo vhi : ℝ)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ δ c : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ a : ℝ, |a - 1| ≤ δ →
        |kernelTiltSaddle D θ vlo ν a| ≤ kernelTiltClassRadius D θ vlo vhi ∧
        kernelTiltMean ν (kernelTiltSaddle D θ vlo ν a) = 1 / a ∧
        c * (a - 1) ^ 2 ≤ kernelTiltRate ν a (kernelTiltSaddle D θ vlo ν a) := by
  have hvhi : 0 < vhi := hvlo.trans_le hv
  have hhalf : 0 < θ / 2 := by positivity
  let r := kernelTiltClassRadius D θ vlo vhi
  let C₃ := saRateThird vlo (2 * D / θ) (θ / 2)
  let W := min (saMeanRadius vlo (2 * D / θ) (θ / 2))
    (min (3 * vlo * r / 4) (1 / (4 * C₃ * vhi)))
  let δ := min (1 / 4 : ℝ) (W / 4)
  have hr : 0 < r := kernelTiltClassRadius_pos hθ hvlo hv
  have hC₃ : 0 < C₃ := saRateThird_pos hvlo hhalf
  have hW : 0 < W := lt_min (saMeanRadius_pos hvlo hhalf)
    (lt_min (by positivity) (by positivity))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδq : δ ≤ 1 / 4 := min_le_left _ _
  have hδW : δ ≤ W / 4 := min_le_right _ _
  refine ⟨δ, 1 / (16 * vhi), hδ, by linarith, by positivity, ?_⟩
  intro ν hν a ha
  have hU := hν.univClass hθ hvlo
  have ha0 : 0 < a := by linarith [(abs_le.mp ha).1]
  have halo : 1 / 2 ≤ a := by linarith [(abs_le.mp ha).1]
  have hahi : a ≤ 2 := by linarith [(abs_le.mp ha).2]
  let w := 1 / a - 1
  let lam := kernelTiltSaddle D θ vlo ν a
  have hwabs : |w| = |a - 1| / a := by
    have he : w = (1 - a) / a := by dsimp [w]; rw [sub_div, div_self ha0.ne']
    rw [he, abs_div, abs_sub_comm 1 a, abs_of_pos ha0]
  have hwa : |w| ≤ 2 * |a - 1| := by
    rw [hwabs, div_le_iff₀ ha0]
    nlinarith [abs_nonneg (a - 1)]
  have haw : |a - 1| ≤ 2 * |w| := by
    have he := (eq_div_iff ha0.ne').mp hwabs
    nlinarith [abs_nonneg w]
  have hwW : |w| ≤ W := by linarith
  have hw : |w| ≤ saMeanRadius vlo (2 * D / θ) (θ / 2) :=
    hwW.trans (min_le_left _ _)
  have hwfull := hw.trans (saMeanRadius_lt_full hvlo hhalf).le
  have hwr : |w| ≤ 3 * vlo * r / 4 :=
    hwW.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : 4 * C₃ * vhi * |w| ≤ 1 := by
    have hh : |w| ≤ 1 / (4 * C₃ * vhi) :=
      hwW.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (show 0 < 4 * C₃ * vhi by positivity)).mp hh
    nlinarith
  have hlam : |lam| ≤ r := by
    apply (hU.abs_saSaddle_le hvlo hhalf 0 hwfull).trans
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 3 * vlo)]
    linarith
  have hrad : |lam| ≤ saTiltRadius vlo (2 * D / θ) (θ / 2) :=
    hlam.trans (min_le_left _ _)
  have hl : |lam| < θ / 2 :=
    (hrad.trans (saTiltRadius_le_half _ _ hhalf)).trans_lt (by linarith)
  have hs := (hU.saSaddle_spec hvlo hhalf 0 hwfull).2
  change deriv (saSmoothCGF ν 0) lam = w at hs
  rw [hU.deriv_saSmoothCGF hl] at hs
  norm_num at hs
  have hm : kernelTiltMean ν lam = 1 / a := by
    rw [hU.kernelTiltMean_eq hl, hs]
    dsimp [w]
    ring
  have hrate : kernelTiltRate ν a lam =
      saRate vlo (2 * D / θ) (θ / 2) ν 0 w := by
    rw [hU.kernelTiltRate_eq_centered hl.le]
    simp [saRate, saSmoothCGF, lam, kernelTiltSaddle, w]
  refine ⟨hlam, hm, ?_⟩
  have hsquare : (a - 1) ^ 2 ≤ 4 * w ^ 2 := by
    nlinarith [sq_abs (a - 1), sq_abs w, sq_nonneg (|a - 1| - 2 * |w|)]
  calc
    1 / (16 * vhi) * (a - 1) ^ 2 = (a - 1) ^ 2 / (16 * vhi) := by ring
    _ ≤ (4 * w ^ 2) / (16 * vhi) :=
      div_le_div_of_nonneg_right hsquare (by positivity)
    _ = w ^ 2 / (4 * vhi) := by ring
    _ ≤ saRate vlo (2 * D / θ) (θ / 2) ν 0 w :=
      hU.kernel_saRate_lower hvlo hhalf hw hsmall
    _ = kernelTiltRate ν a lam := hrate.symm


/-- Fixed opposite tilts control all three regimes away from slope one.
Both tilts lie in the radius where actual-mean normalization preserves RegLaw. -/
theorem kernel_regLaw_fixed_tilt_rates (D θ vlo vhi δ : ℝ)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) :
    ∃ t c : ℝ, 0 < t ∧ t ≤ kernelTiltClassRadius D θ vlo vhi ∧ 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
        (∀ a : ℝ, 2 ≤ a → c ≤ kernelTiltRate ν a (-t)) ∧
        (∀ a : ℝ, 0 < a → a ≤ 1 / 2 → c / a ≤ kernelTiltRate ν a t) ∧
        (∀ a : ℝ, 1 / 2 ≤ a → a ≤ 2 → δ ≤ |a - 1| →
          c ≤ kernelTiltRate ν a (if a ≤ 1 then t else -t)) := by
  have hvhi : 0 < vhi := hvlo.trans_le hv
  let r := kernelTiltClassRadius D θ vlo vhi
  let t := min (r / 2) (δ / (4 * vhi))
  let c := δ * t / 4
  have hr : 0 < r := kernelTiltClassRadius_pos hθ hvlo hv
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htr : t ≤ r := (min_le_left _ _).trans (by linarith)
  have htδ : t ≤ δ / (4 * vhi) := min_le_right _ _
  have hc : 0 < c := by positivity
  have hcsmall : c ≤ t / 4 := by dsimp [c]; nlinarith
  have hquad : vhi * t ^ 2 ≤ c := by
    have hh := (le_div_iff₀ (show 0 < 4 * vhi by positivity)).mp htδ
    have hp := mul_le_mul_of_nonneg_right hh ht.le
    dsimp [c]
    nlinarith
  refine ⟨t, c, ht, htr, hc, ?_⟩
  intro ν hν
  have hU := hν.univClass hθ hvlo
  have htabs : |t| ≤ r := by rwa [abs_of_pos ht]
  have hrad : |t| ≤ saTiltRadius vlo (2 * D / θ) (θ / 2) :=
    htabs.trans (min_le_left _ _)
  have hradneg : |-t| ≤ saTiltRadius vlo (2 * D / θ) (θ / 2) := by
    simpa only [abs_neg] using hrad
  have hl : |t| ≤ θ / 2 :=
    (hrad.trans (saTiltRadius_le_half _ _ (by positivity))).trans (by linarith)
  have hln : |-t| ≤ θ / 2 := by simpa only [abs_neg] using hl
  have hp : cgf (fun x : ℝ => x - 1) (ν : Measure ℝ) t ≤ c :=
    (hU.kernel_centered_cgf_upper hvlo (by positivity) hrad).trans hquad
  have hn : cgf (fun x : ℝ => x - 1) (ν : Measure ℝ) (-t) ≤ c := by
    have hh := hU.kernel_centered_cgf_upper hvlo (by positivity) hradneg
    rw [neg_sq] at hh
    exact hh.trans hquad
  have hIp (a : ℝ) : t * (1 / a - 1) - c ≤ kernelTiltRate ν a t := by
    rw [hU.kernelTiltRate_eq_centered hl]
    linarith
  have hIn (a : ℝ) : t * (1 - 1 / a) - c ≤ kernelTiltRate ν a (-t) := by
    rw [hU.kernelTiltRate_eq_centered hln]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    have ha0 : 0 < a := by linarith
    have hinv : 1 / a ≤ 1 / 2 := by rw [div_le_iff₀ ha0]; linarith
    have hmul := mul_le_mul_of_nonneg_left hinv ht.le
    linarith [hIn a]
  · intro a ha0 ha
    have hnum : c ≤ t - a * t - a * c := by
      have hac := mul_le_mul_of_nonneg_right ha hc.le
      have hat := mul_le_mul_of_nonneg_right ha ht.le
      linarith
    have he : t * (1 / a - 1) - c = (t - a * t - a * c) / a := by
      field_simp
    have hh : c / a ≤ t * (1 / a - 1) - c := by
      rw [he]
      exact div_le_div_of_nonneg_right hnum ha0.le
    exact hh.trans (hIp a)
  · intro a halo hahi haway
    have ha0 : 0 < a := by linarith
    by_cases ha : a ≤ 1
    · rw [if_pos ha]
      have hd : δ ≤ 1 - a := by rwa [abs_of_nonpos (by linarith), neg_sub] at haway
      have hw : δ / 2 ≤ 1 / a - 1 := by
        have he : 1 / a - 1 = (1 - a) / a := by rw [sub_div, div_self ha0.ne']
        rw [he, le_div_iff₀ ha0]
        nlinarith
      have hh := mul_le_mul_of_nonneg_left hw ht.le
      dsimp [c] at hIp ⊢
      nlinarith [hIp a]
    · rw [if_neg ha]
      have hd : δ ≤ a - 1 := by rwa [abs_of_nonneg (by linarith)] at haway
      have hw : δ / 2 ≤ 1 - 1 / a := by
        have he : 1 - 1 / a = (a - 1) / a := by rw [sub_div, div_self ha0.ne']
        rw [he, le_div_iff₀ ha0]
        nlinarith
      have hh := mul_le_mul_of_nonneg_left hw ht.le
      dsimp [c] at hIn ⊢
      nlinarith [hIn a]


/-- At the actual saddle, mean normalization is exactly multiplication by slope. -/
theorem kernelTiltNormalized_eq_map_mul {ν : ProbabilityMeasure ℝ} {lam a : ℝ}
    (hm : kernelTiltMean ν lam = 1 / a) :
    kernelTiltNormalized ν lam =
      ((ν : Measure ℝ).tilted (fun x => lam * x)).map (fun x => a * x) := by
  rw [kernelTiltNormalized, hm, kernel_centeredTilt_eq_raw]
  congr 1
  funext x
  simp [div_eq_mul_inv, mul_comm]

/-- The near-critical rate and the actual transformed regular law in one package.
The new density, exponential, and variance constants precede the original law. -/
theorem kernel_regLaw_saddle_normalized (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ δ c : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ a : ℝ, |a - 1| ≤ δ →
        |kernelTiltSaddle D θ vlo ν a| ≤ kernelTiltClassRadius D θ vlo vhi ∧
        kernelTiltMean ν (kernelTiltSaddle D θ vlo ν a) = 1 / a ∧
        c * (a - 1) ^ 2 ≤ kernelTiltRate ν a (kernelTiltSaddle D θ vlo ν a) ∧
        ∃ ρ : ProbabilityMeasure ℝ,
          (ρ : Measure ℝ) = ((ν : Measure ℝ).tilted
            (fun x => kernelTiltSaddle D θ vlo ν a * x)).map (fun x => a * x) ∧
          RegLaw (2 * D * Real.exp θ) (θ / 4) (3 * vlo / 16) (5 * vhi) ρ := by
  obtain ⟨δ, c, hδ, hδhi, hc, hb⟩ := kernel_regLaw_saddle_rate D θ vlo vhi hθ hvlo hv
  refine ⟨δ, c, hδ, hδhi, hc, ?_⟩
  intro ν hν a ha
  obtain ⟨hlam, hm, hrate⟩ := hb ν hν a ha
  obtain ⟨_, ρ, hρ, hreg⟩ :=
    (kernel_regLaw_normalized_tilt D θ vlo vhi hD hθ hvlo hv).2 ν hν _ hlam
  exact ⟨hlam, hm, hrate, ρ, hρ.trans (kernelTiltNormalized_eq_map_mul hm), hreg⟩

end
end PGM
