import PLAStochastic.Index.GEP.PointwiseSmall.RowV

/-!
# WP4 leaf `PointwiseSmall`, row φ: the output test against two directions of equal variance

For two direction laws `σ₊, σ₋` (same `A, θσ`) with `v(σ₊) = v(σ₋)`, the mixtures
`ν_t^± = (1 - t) ν + t σ±` have the same variance `v_t`.  With the fixed-base test
`F(y) = φ_ψ(y/C₀) / (M/η)` and the `RawDiscId` continuations `f±` of `E_{ν_t^±} F(S_T)`, the
function `H = f⁺ - f⁻` is holomorphic on a fixed disc, polynomially bounded, `H(0) = 0`, and on the
real segment `H(t) = E_{ν_t^+} F(S_T) - E_{ν_t^-} F(S_T)`.  Writing `S_T/C₀ = c_t W`,
`W = v_t S_T/ε²`, `c_t = ε²/(v_t C₀)`, both terms are the *same* test `φ_{χ_t}`, `χ_t(s) =
c_t ψ(c_t s)/(M/η)`, against `rawLaw ε ν_t^±`; (U) compares each with `rawLaw ε ν` (`pw_real_test`),
so `|H(t)| ≤ K ε^{-βU}` and interpolation gives `|H'(0)| = |∫ I_F d(σ₊ - σ₋)| ≤ K ε^{-βU} log² ε`.
Row A for `σ₊` and `σ₋` bounds `|∫ J_C d(σ₊ - σ₋)|/C₀` (the variance terms cancel), and
`KappaBound` bounds `κ_φ`; hence (`pw_rowPhi`)
`|∫ J_φ dσ₊ - ∫ J_φ dσ₋| ≤ M K ε^{-βU} (1 + log ε)²`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

variable {D θ vlo vhi : ℝ}

/-! ## Scaling the tests -/

/-- Scaling the argument of a test: `φ_ψ(c w) = φ_{c ψ(c ·)}(w)`. -/
theorem pw_testFn_mul {ψ : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (w : ℝ) :
    testFn ψ (c * w) = testFn (fun s => c * ψ (c * s)) w := by
  rw [testFn_eq_primitive, testFn_eq_primitive]
  have h : ∀ s, psiPos (fun s => c * ψ (c * s)) s = c * psiPos ψ (c * s) := by
    intro s
    by_cases hs : 0 < s
    · rw [psiPos, indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs), psiPos,
        indicator_of_mem (show c * s ∈ Ioi (0 : ℝ) from mul_pos hc hs)]
    · have hs' : c * s ≤ 0 := by nlinarith [not_lt.1 hs, hc]
      rw [psiPos, indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs), psiPos,
        indicator_of_notMem (show c * s ∉ Ioi (0 : ℝ) from not_lt.2 hs'), mul_zero]
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul]
  show _ = c • ∫ s in (0 : ℝ)..w, psiPos ψ (c * s)
  rw [intervalIntegral.smul_integral_comp_mul_left, mul_zero]

/-- Dividing a test by a constant. -/
theorem pw_testFn_div (f : ℝ → ℝ) (k w : ℝ) : testFn (fun s => f s / k) w = testFn f w / k := by
  unfold testFn
  exact integral_div k f

theorem pw_outTest_of_le {η M η' M' : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : η ≤ η')
    (hM : M ≤ M') : OutTest η' M' ψ :=
  ⟨hψ.1, fun x hx => (hψ.2 x hx).trans
    (mul_le_mul hM (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le (hψ.nonneg'.trans hM))⟩

/-- The rescaled normalised test `χ(s) = c ψ(c s) / (M/η)` is an admissible test of weight
`η c ≤ η L` and size `η c ≤ η L`. -/
theorem pw_pair_outTest {η M : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hM : 0 < M) (hη : 0 < η)
    {c L γ' : ℝ} (hc : 0 < c) (hcL : c ≤ L) (hγ : η * L ≤ γ') :
    OutTest γ' (η * L) (fun s => c * ψ (c * s) / (M / η)) := by
  have h0 : OutTest (η * c) (η * c) (fun s => c * ψ (c * s) / (M / η)) := by
    refine ⟨(measurable_const.mul (hψ.1.comp (measurable_const.mul measurable_id))).div_const _,
      fun s hs => ?_⟩
    have h := hψ.2 (c * s) (by positivity)
    rw [show η * (c * s) = η * c * s by ring] at h
    rw [abs_div, abs_mul, abs_of_pos hc, abs_of_pos (by positivity : (0 : ℝ) < M / η),
      div_le_iff₀ (by positivity)]
    calc c * |ψ (c * s)| ≤ c * (M * Real.exp (η * c * s)) := by gcongr
      _ = η * c * Real.exp (η * c * s) * (M / η) := by
          rw [show η * c * Real.exp (η * c * s) * (M / η) =
            c * Real.exp (η * c * s) * (η * (M / η)) by ring, mul_div_cancel₀ M hη.ne']
          ring
  exact pw_outTest_of_le h0 (by nlinarith) (by nlinarith)

/-- `φ_ψ(S/C₀)/(M/η)` as the scaled test evaluated at `W = v S/ε²`. -/
theorem pw_pair_test_eq {ψ : ℝ → ℝ} {M η vt C₀ eps : ℝ} (hvt : 0 < vt) (hC₀ : 0 < C₀)
    (heps : 0 < eps) (S : ℝ) :
    testFn ψ (S / C₀) / (M / η) =
      testFn (fun s => eps ^ 2 / (vt * C₀) * ψ (eps ^ 2 / (vt * C₀) * s) / (M / η))
        (vt * S / eps ^ 2) := by
  have hc : 0 < eps ^ 2 / (vt * C₀) := by positivity
  rw [pw_testFn_div, ← pw_testFn_mul hc]
  congr 2
  rw [div_mul_div_comm, div_eq_div_iff hC₀.ne' (by positivity)]
  ring

/-! ## Row φ -/

/-- **Row φ for a pair of directions of equal variance** (`M > 0`). -/
theorem pw_rowPhi_pos (hS : SurvivalBound) {βU : ℝ} (hβU : 0 ≤ βU) (hUM : PwUnivMix βU)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ηφ : ℝ, 0 < ηφ ∧ ∀ A θσ : ℝ, 0 < θσ →
      ∃ K e0 : ℝ, 0 ≤ K ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν σp σm : ProbabilityMeasure ℝ,
        RegLaw D θ vlo vhi ν → SigmaLaw A θσ σp → SigmaLaw A θσ σm → lawVar σp = lawVar σm →
        ∀ M ψ, 0 < M → OutTest ηφ M ψ →
          |(∫ x, outJ eps ν ψ x ∂(σp : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(σm : Measure ℝ)| ≤
            M * (K * eps ^ (-βU) * (1 + Real.log eps) ^ 2) := by
  have hvhi : 0 < vhi + 1 := by linarith
  set b₀ : ℝ := 128 * (vhi + 1) with hb₀
  have hb₀0 : 0 < b₀ := by positivity
  obtain ⟨γR, hγR, hRD⟩ := rawDiscId_of_survivalBound hS D θ vlo vhi hD hθ hvlo hv
  obtain ⟨κ₁, K₁, e₁, hκ₁, -, -, hker⟩ := pw_kernel_facts hD hθ hvlo hv
  obtain ⟨γ', hγ', hRT⟩ := pw_real_test hUM hD hθ hvlo hv
  obtain ⟨ηk, hηk, Kk, ek, hkap⟩ := kappaBound D θ vlo vhi hD hθ hvlo hv
  -- the output weight
  set ηφ : ℝ := min (min γR κ₁ / (2 * b₀)) (min ηk (γ' * vlo / (2 * b₀))) with hηφ
  have hηφ0 : 0 < ηφ := by positivity
  have hηφ1 : 2 * ηφ * b₀ ≤ min γR κ₁ := by
    have h : ηφ ≤ min γR κ₁ / (2 * b₀) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hηφk : ηφ ≤ ηk := (min_le_right _ _).trans (min_le_left _ _)
  have hηφγ : ηφ * (2 * b₀ / vlo) ≤ γ' := by
    have h : ηφ ≤ γ' * vlo / (2 * b₀) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    rw [mul_div_assoc', div_le_iff₀ hvlo]
    exact h
  refine ⟨ηφ, hηφ0, fun A θσ hθσ => ?_⟩
  obtain ⟨rR, KR, eR, pR, hrR, hRD'⟩ := hRD A θσ hθσ
  obtain ⟨KT, eT, hKT, -, hRT'⟩ := hRT A θσ hθσ
  obtain ⟨KA, eA, hKA, -, hrowA⟩ := pw_rowA hS hβU hUM hD hθ hvlo hv A θσ hθσ
  obtain ⟨KJ, eJ, -, -, hJC⟩ := pw_lawJC_integrable hD hθ hvlo hv
  obtain ⟨es, hes1, hseg⟩ := pw_seg_facts (vhi := vhi) hD hθ hvlo A θσ hθσ
  set R : ℝ := min rR (tMix A θσ) with hRdef
  have hR0 : 0 < R := lt_min hrR (tMix_pos A θσ hθσ)
  have hRr : R ≤ rR := min_le_left _ _
  have hRt : R ≤ tMix A θσ := min_le_right _ _
  obtain ⟨K₃, hK₃, hint⟩ := pw_interp_small discInterp (R := R) (K₁ := 2 * |KR|)
    (K₂ := 2 * (ηφ * (2 * b₀ / vlo) * KT)) (b := βU) pR hR0 hβU
  set eκ : ℝ := 2 * ηφ * b₀ * (1 / θσ + 2 / θ) + 1 with heκ
  refine ⟨K₃ / ηφ + 2 * |Kk| * KA,
    max (max (max eR eT) (max eA eJ)) (max (max es e₁) (max ek eκ)), by positivity,
    hes1.trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))), ?_⟩
  intro eps heps ν σp σm hν hσp hσm hvar M ψ hM hψ
  have hle1 : ∀ {a : ℝ}, a ≤ max (max (max eR eT) (max eA eJ)) (max (max es e₁) (max ek eκ)) →
      a ≤ eps := fun h => h.trans heps
  have heR' : eR ≤ eps := hle1 ((le_max_left _ _).trans ((le_max_left _ _).trans
    (le_max_left _ _)))
  have heT' : eT ≤ eps := hle1 ((le_max_right _ _).trans ((le_max_left _ _).trans
    (le_max_left _ _)))
  have heA' : eA ≤ eps := hle1 ((le_max_left _ _).trans ((le_max_right _ _).trans
    (le_max_left _ _)))
  have heJ' : eJ ≤ eps := hle1 ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_left _ _)))
  have hes' : es ≤ eps := hle1 ((le_max_left _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _)))
  have he₁' : e₁ ≤ eps := hle1 ((le_max_right _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _)))
  have hek' : ek ≤ eps := hle1 ((le_max_left _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _)))
  have heκ' : eκ ≤ eps := hle1 ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _)))
  have heps1 : 1 ≤ eps := hes1.trans hes'
  have heps0 : 0 < eps := by linarith only [heps1]
  have heps2 : (0 : ℝ) < eps ^ 2 := by positivity
  -- the base law
  have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨le_rfl, (tMix_pos A θσ hθσ).le⟩
  obtain ⟨-, -, -, -, -, -, hCmν, -, -, -⟩ := hseg eps hes' ν σp hν hσp 0 h0t
  simp only [mixPM_zero] at hCmν
  rw [← hb₀] at hCmν
  set C₀ := lawC eps ν with hC₀
  have hC0 : 0 < C₀ := lt_of_lt_of_le (by positivity) hCmν
  have hv0 : vlo ≤ lawVar ν := hν.var_ge
  have hvpos : 0 < lawVar ν := hvlo.trans_le hv0
  -- the normalised test
  obtain ⟨hFm, hFκ⟩ := pw_normTest hψ hηφ0 hM hb₀0 heps0 hCmν
  set Fh : ℝ → ℝ := fun y => testFn ψ (y / C₀) / (M / ηφ) with hFh
  set κ : ℝ := 2 * ηφ * b₀ / eps ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκγ : κ * eps ^ 2 ≤ min γR κ₁ := by
    rw [hκ, div_mul_cancel₀ _ heps2.ne']; exact hηφ1
  have hFγ : ∀ y, 0 ≤ y → |Fh y| ≤ Real.exp (γR * y / eps ^ 2) := by
    intro y hy
    refine (hFκ y hy).trans (Real.exp_le_exp.2 ?_)
    have h1 : κ ≤ γR / eps ^ 2 := by
      rw [le_div_iff₀ heps2]; exact hκγ.trans (min_le_left _ _)
    calc κ * y ≤ γR / eps ^ 2 * y := mul_le_mul_of_nonneg_right h1 hy
      _ = γR * y / eps ^ 2 := by ring
  obtain ⟨-, -, hIint⟩ := hker eps he₁' ν hν κ hκ0 (hκγ.trans (min_le_right _ _)) Fh hFm hFκ
  have heκ1 : 2 * ηφ * b₀ * (1 / θσ) + 1 ≤ eps := by
    refine le_trans ?_ heκ'
    rw [heκ]
    have : 0 ≤ 2 * ηφ * b₀ * (2 / θ) := by positivity
    linarith only [this]
  have heκ2 : 2 * ηφ * b₀ * (2 / θ) + 1 ≤ eps := by
    refine le_trans ?_ heκ'
    rw [heκ]
    have : 0 ≤ 2 * ηφ * b₀ * (1 / θσ) := by positivity
    linarith only [this]
  have hκσ : κ ≤ θσ := by
    rw [hκ]
    refine pw_kappa_le (by positivity) hθσ ?_
    rw [div_eq_mul_one_div]; exact heκ1
  have hκν : κ ≤ θ / 2 := by
    rw [hκ]
    refine pw_kappa_le (by positivity) (half_pos hθ) ?_
    rw [div_div_eq_mul_div, mul_div_assoc]; exact heκ2
  have hIp := hIint σp hσp.pos (hσp.integrable_exp hκσ)
  have hIm := hIint σm hσm.pos (hσm.integrable_exp hκσ)
  have hIν := hIint ν (hν.pos' hθ hvlo) (hν.integrable_exp hθ hvlo hκν)
  have hk0 : (0 : ℝ) < M / ηφ := by positivity
  have houtIns : outIns eps ν ψ =
      fun x => M / ηφ * insKernel eps ν (fun g => Fh (stopSum eps g)) x := by
    funext x
    exact pw_outIns_eq_mul eps ν ψ hk0.ne' x
  -- the continuations
  obtain ⟨fp, hfp, hfpb, -, hfpd, hfpr⟩ := hRD' eps heR' ν σp hν hσp Fh hFm hFγ
  obtain ⟨fm, hfm, hfmb, -, hfmd, hfmr⟩ := hRD' eps heR' ν σm hν hσm Fh hFm hFγ
  obtain ⟨-, -, hJi⟩ := hJC eps heJ' ν hν
  set H : ℂ → ℂ := fun z => fp z - fm z with hH
  have hHd : DifferentiableOn ℂ H (ball 0 R) :=
    (hfp.mono (ball_subset_ball hRr)).sub (hfm.mono (ball_subset_ball hRr))
  have hHb : ∀ z ∈ ball (0 : ℂ) R, ‖H z‖ ≤ 2 * |KR| * eps ^ pR := by
    intro z hz
    have hz' : z ∈ ball (0 : ℂ) rR := ball_subset_ball hRr hz
    have hK : KR * eps ^ pR ≤ |KR| * eps ^ pR := by gcongr; exact le_abs_self _
    calc ‖H z‖ ≤ ‖fp z‖ + ‖fm z‖ := norm_sub_le _ _
      _ ≤ (KR * eps ^ pR) + (KR * eps ^ pR) := add_le_add (hfpb z hz') (hfmb z hz')
      _ ≤ 2 * |KR| * eps ^ pR := by linarith only [hK]
  have hH0 : H 0 = 0 := by
    have h1 := hfpr 0 le_rfl (by positivity)
    have h2 := hfmr 0 le_rfl (by positivity)
    simp only [mixPM_zero, Complex.ofReal_zero] at h1 h2
    simp only [hH]
    rw [h1, h2, sub_self]
  -- the real segment
  have hHs : ∀ t : ℝ, 0 ≤ t → t ≤ R / 8 →
      ‖H t - H 0‖ ≤ 2 * (ηφ * (2 * b₀ / vlo) * KT) * eps ^ (-βU) := by
    intro t ht0 ht1
    have ht : t ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨ht0, by linarith only [ht1, hRt, hR0]⟩
    have ht1' : t ∈ Icc (0 : ℝ) 1 :=
      ⟨ht0, by linarith only [ht1, hRt, hR0, tMix_le A θσ hθσ]⟩
    have hmt := momClass_mix hθ hvlo hθσ hν hσp ht
    have hvtpos : 0 < lawVar (mixPM ν σp t) := by
      have := hmt.var_ge
      linarith only [this, half_pos hvlo]
    have hvtm : lawVar (mixPM ν σm t) = lawVar (mixPM ν σp t) := by
      rw [pw_lawVar_mix hθ hvlo hθσ hν hσp ht1', pw_lawVar_mix hθ hvlo hθσ hν hσm ht1', hvar]
    have hctle : eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) ≤ 2 * b₀ / vlo := by
      rw [div_le_div_iff₀ (by positivity) hvlo]
      have h1 : eps ^ 2 ≤ b₀ * C₀ := by
        have := hCmν
        rw [div_le_iff₀ hb₀0] at this
        linarith only [this]
      have h2 : vlo / 2 ≤ lawVar (mixPM ν σp t) := hmt.var_ge
      have h3 : 0 ≤ b₀ * C₀ := by positivity
      linarith only [mul_nonneg (sub_nonneg.2 h2) h3, mul_nonneg (sub_nonneg.2 h1) hvlo.le]
    have hχ := pw_pair_outTest hψ hM hηφ0 (by positivity) hctle hηφγ
    have hEp : ∫ g, Fh (stopSum eps g) ∂(iidLaw (mixPM ν σp t)) =
        ∫ g, testFn (fun s => eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) *
            ψ (eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) * s) / (M / ηφ))
          (lawVar (mixPM ν σp t) * stopSum eps g / eps ^ 2) ∂(iidLaw (mixPM ν σp t)) := by
      congr 1
      funext g
      simp only [hFh]
      exact pw_pair_test_eq hvtpos hC0 heps0 _
    have hEm : ∫ g, Fh (stopSum eps g) ∂(iidLaw (mixPM ν σm t)) =
        ∫ g, testFn (fun s => eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) *
            ψ (eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) * s) / (M / ηφ))
          (lawVar (mixPM ν σp t) * stopSum eps g / eps ^ 2) ∂(iidLaw (mixPM ν σm t)) := by
      congr 1
      funext g
      simp only [hFh]
      exact pw_pair_test_eq hvtpos hC0 heps0 _
    have h1 := hRT' eps heT' ν σp hν hσp t ht _ _ hχ
    have h2 := hRT' eps heT' ν σm hν hσm t ht _ _ hχ
    rw [hvtm, abs_sub_comm] at h2
    rw [hH0, sub_zero]
    simp only [hH]
    rw [hfpr t ht0 (by linarith only [ht1, hRr]), hfmr t ht0 (by linarith only [ht1, hRr]),
      ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, hEp, hEm]
    refine (abs_sub_le _ (∫ g, testFn (fun s => eps ^ 2 /
      (lawVar (mixPM ν σp t) * C₀) * ψ (eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) * s) /
      (M / ηφ)) (lawVar ν * stopSum eps g / eps ^ 2) ∂(iidLaw ν)) _).trans ?_
    linarith only [h1, h2]
  -- interpolation
  have hmain := hint H eps heps1 hHd hHb hHs
  have hdp : DifferentiableAt ℂ fp 0 :=
    hfp.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrR))
  have hdm : DifferentiableAt ℂ fm 0 :=
    hfm.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrR))
  have hHd0 : deriv H 0 = deriv fp 0 - deriv fm 0 := by
    rw [hH]
    exact (hdp.hasDerivAt.sub hdm.hasDerivAt).deriv
  rw [hHd0, hfpd, hfmd, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hmain
  -- the identification with `J_φ`
  have hIp' : Integrable (outIns eps ν ψ) (σp : Measure ℝ) := by
    rw [houtIns]; exact hIp.const_mul _
  have hIm' : Integrable (outIns eps ν ψ) (σm : Measure ℝ) := by
    rw [houtIns]; exact hIm.const_mul _
  have hIν' : Integrable (outIns eps ν ψ) (ν : Measure ℝ) := by
    rw [houtIns]; exact hIν.const_mul _
  have hJp := pw_integral_outJ_sub hIp' hIν' (hJi σp) (hJi ν)
  have hJm := pw_integral_outJ_sub hIm' hIν' (hJi σm) (hJi ν)
  rw [← hC₀] at hJp hJm
  have hκb : |outKappa eps ν ψ| ≤ M * |Kk| := by
    have h := hkap eps hek' ν hν M ψ (hψ.mono_eta hηφk)
    exact h.trans (by gcongr; exact le_abs_self _)
  have hA1 := hrowA eps heA' ν σp hν hσp
  have hA2 := hrowA eps heA' ν σm hν hσm
  rw [← hC₀, hvar] at hA1
  rw [← hC₀] at hA2
  set Djp : ℝ := (∫ x, lawJC eps ν x ∂(σp : Measure ℝ)) - ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)
    with hDjp
  set Djm : ℝ := (∫ x, lawJC eps ν x ∂(σm : Measure ℝ)) - ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)
    with hDjm
  set Ip : ℝ := ∫ x, insKernel eps ν (fun g => Fh (stopSum eps g)) x ∂(σp : Measure ℝ) with hIpd
  set Im : ℝ := ∫ x, insKernel eps ν (fun g => Fh (stopSum eps g)) x ∂(σm : Measure ℝ) with hImd
  set Iν : ℝ := ∫ x, insKernel eps ν (fun g => Fh (stopSum eps g)) x ∂(ν : Measure ℝ) with hIνd
  set κφ : ℝ := outKappa eps ν ψ with hκφ
  have hid : (∫ x, outJ eps ν ψ x ∂(σp : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(σm : Measure ℝ) =
      M / ηφ * ((Ip - Iν) - (Im - Iν)) - κφ * (Djp / C₀ - Djm / C₀) := by
    have e : (∫ x, outJ eps ν ψ x ∂(σp : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(σm : Measure ℝ) =
        ((∫ x, outJ eps ν ψ x ∂(σp : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(ν : Measure ℝ)) -
        ((∫ x, outJ eps ν ψ x ∂(σm : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(ν : Measure ℝ)) := by
      ring
    rw [e, hJp, hJm, houtIns, integral_const_mul, integral_const_mul, integral_const_mul,
      ← hIpd, ← hImd, ← hIνd]
    ring
  have hA : |Djp / C₀ - Djm / C₀| ≤ 2 * KA * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by
    have h1 := hA1
    have h2 := hA2
    have e : Djp / C₀ - Djm / C₀ = (Djp / C₀ + (lawVar σm - lawVar ν) / lawVar ν) -
        (Djm / C₀ + (lawVar σm - lawVar ν) / lawVar ν) := by ring
    rw [e]
    calc _ ≤ |Djp / C₀ + (lawVar σm - lawVar ν) / lawVar ν| +
          |Djm / C₀ + (lawVar σm - lawVar ν) / lawVar ν| := abs_sub _ _
      _ ≤ KA * eps ^ (-βU) * (1 + Real.log eps) ^ 2 + KA * eps ^ (-βU) * (1 + Real.log eps) ^ 2 :=
          add_le_add h1 h2
      _ = 2 * KA * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by ring
  have hL : 0 ≤ eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by positivity
  rw [hid]
  calc |M / ηφ * ((Ip - Iν) - (Im - Iν)) - κφ * (Djp / C₀ - Djm / C₀)|
      ≤ |M / ηφ * ((Ip - Iν) - (Im - Iν))| + |κφ * (Djp / C₀ - Djm / C₀)| := abs_sub _ _
    _ = M / ηφ * |(Ip - Iν) - (Im - Iν)| + |κφ| * |Djp / C₀ - Djm / C₀| := by
        rw [abs_mul, abs_mul, abs_of_pos hk0]
    _ ≤ M / ηφ * (K₃ * eps ^ (-βU) * (1 + Real.log eps) ^ 2) +
        M * |Kk| * (2 * KA * eps ^ (-βU) * (1 + Real.log eps) ^ 2) := by
        gcongr
    _ = M * ((K₃ / ηφ + 2 * |Kk| * KA) * eps ^ (-βU) * (1 + Real.log eps) ^ 2) := by
        ring

/-- **Row φ for a pair of directions of equal variance**: for all `M ≥ 0`. -/
theorem pw_rowPhi (hS : SurvivalBound) {βU : ℝ} (hβU : 0 ≤ βU) (hUM : PwUnivMix βU)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ηφ : ℝ, 0 < ηφ ∧ ∀ A θσ : ℝ, 0 < θσ →
      ∃ K e0 : ℝ, 0 ≤ K ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν σp σm : ProbabilityMeasure ℝ,
        RegLaw D θ vlo vhi ν → SigmaLaw A θσ σp → SigmaLaw A θσ σm → lawVar σp = lawVar σm →
        ∀ M ψ, OutTest ηφ M ψ →
          |(∫ x, outJ eps ν ψ x ∂(σp : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(σm : Measure ℝ)| ≤
            M * (K * eps ^ (-βU) * (1 + Real.log eps) ^ 2) := by
  obtain ⟨ηφ, hηφ, h⟩ := pw_rowPhi_pos hS hβU hUM hD hθ hvlo hv
  refine ⟨ηφ, hηφ, fun A θσ hθσ => ?_⟩
  obtain ⟨K, e0, hK, he0, h'⟩ := h A θσ hθσ
  refine ⟨K, e0, hK, he0, fun eps heps ν σp σm hν hσp hσm hvar M ψ hψ => ?_⟩
  have hM := hψ.nonneg'
  rcases hM.eq_or_lt with hM0 | hMpos
  · subst hM0
    rw [zero_mul]
    have heps0 : 0 < eps := by linarith only [he0, heps]
    have hc : 0 ≤ K * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by positivity
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε' : 0 < ε / (K * eps ^ (-βU) * (1 + Real.log eps) ^ 2 + 1) := by positivity
    have hb := h' eps heps ν σp σm hν hσp hσm hvar _ ψ hε' (pw_outTest_of_le hψ le_rfl hε'.le)
    refine hb.trans ?_
    rw [zero_add, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith only [hε]
  · exact h' eps heps ν σp σm hν hσp hσm hvar M ψ hMpos hψ

end

end PGM
