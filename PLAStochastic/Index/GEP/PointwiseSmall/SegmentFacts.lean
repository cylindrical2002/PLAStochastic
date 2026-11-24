import PLAStochastic.Index.GEP.PointwiseSmall.RowA
import PLAStochastic.Index.GEP.PointwiseSmall.DirectionKernels
import PLAStochastic.Index.GEP.RawDisc.ContinuationIdentity
import PLAStochastic.Index.GEP.Response.Score.ScoreCalculus

/-!
# WP4 leaves `PointwiseSmall`, `QuadResponse`: facts along the mixture segment

Per-`ε` bookkeeping shared by rows V, φ and `QuadResponse`:

* `pw_seg_facts`: for `t ∈ [0, tMix]` the mixture `ν_t` is in the moment class, `S_T ≥ 0` a.s.,
  `S_T, S_T²` are integrable with `E S_T² ≤ 2 (ε²/γ)² CK` (`γ = gamMix vlo`, from `stopExp_mix`),
  Wald `E S_T = C_ε(ν_t)`, `ε²/(128(vhi+1)) ≤ C_ε(ν_t) ≤ (cPlus/(vlo/2)) ε²`, the variance is affine
  and `pwM1 = v_t C_t/ε²`;
* `pw_normTest`: the normalised output test `φ_ψ(y/C)/(M/η)` is bounded by `e^{κy}`,
  `κ = 2ηb₀/ε²`, and `pw_outIns_eq_mul` rescales its kernel;
* moments of the variance test (`pw_integral_psiVar`, `pw_outKappa_psiVar`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

variable {D θ vlo vhi : ℝ}

/-! ## Moments of the stopped sum -/

theorem pw_stopSum_sq_facts {P : Measure (ℕ → ℝ)} [IsProbabilityMeasure P] {eps c : ℝ}
    (hc : 0 < c) (heps : 0 < eps) (hS0 : ∀ᵐ g ∂P, 0 ≤ stopSum eps g)
    (hint : Integrable (fun g => Real.exp (c * stopSum eps g / eps ^ 2)) P)
    (hle : ∫ g, Real.exp (c * stopSum eps g / eps ^ 2) ∂P ≤ CK) :
    Integrable (stopSum eps) P ∧ Integrable (fun g => stopSum eps g ^ 2) P ∧
      ∫ g, stopSum eps g ^ 2 ∂P ≤ 2 * (eps ^ 2 / c) ^ 2 * CK := by
  have hm := measurable_stopSum eps
  have he2 : 0 < eps ^ 2 := by positivity
  have hk : 0 < eps ^ 2 / c := by positivity
  have hb1 : ∀ s : ℝ, 0 ≤ s → s ≤ eps ^ 2 / c * Real.exp (c * s / eps ^ 2) := by
    intro s hs
    have h := Real.add_one_le_exp (c * s / eps ^ 2)
    have e : s = eps ^ 2 / c * (c * s / eps ^ 2) := by field_simp
    calc s = eps ^ 2 / c * (c * s / eps ^ 2) := e
      _ ≤ eps ^ 2 / c * Real.exp (c * s / eps ^ 2) := by gcongr; linarith
  have hb2 : ∀ s : ℝ, 0 ≤ s → s ^ 2 ≤ 2 * (eps ^ 2 / c) ^ 2 * Real.exp (c * s / eps ^ 2) := by
    intro s hs
    have h := Real.pow_div_factorial_le_exp (x := c * s / eps ^ 2) (by positivity) 2
    have h2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [h2] at h
    have e : s ^ 2 = (eps ^ 2 / c) ^ 2 * (c * s / eps ^ 2) ^ 2 := by field_simp
    rw [e]
    nlinarith [sq_nonneg (eps ^ 2 / c)]
  have i1 : Integrable (stopSum eps) P :=
    (hint.const_mul (eps ^ 2 / c)).mono' hm.aestronglyMeasurable (hS0.mono fun g hg => by
      rw [Real.norm_eq_abs, abs_of_nonneg hg]; exact hb1 _ hg)
  have i2 : Integrable (fun g => stopSum eps g ^ 2) P :=
    (hint.const_mul (2 * (eps ^ 2 / c) ^ 2)).mono' (hm.pow_const 2).aestronglyMeasurable
      (hS0.mono fun g hg => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb2 _ hg)
  refine ⟨i1, i2, ?_⟩
  calc ∫ g, stopSum eps g ^ 2 ∂P
      ≤ ∫ g, 2 * (eps ^ 2 / c) ^ 2 * Real.exp (c * stopSum eps g / eps ^ 2) ∂P :=
        integral_mono_ae i2 (hint.const_mul _) (hS0.mono fun g hg => hb2 _ hg)
    _ = 2 * (eps ^ 2 / c) ^ 2 * ∫ g, Real.exp (c * stopSum eps g / eps ^ 2) ∂P :=
        integral_const_mul _ _
    _ ≤ 2 * (eps ^ 2 / c) ^ 2 * CK := by gcongr

/-- `E φ_V(S/C)` in terms of the first two moments of `S`. -/
theorem pw_integral_psiVar {P : Measure (ℕ → ℝ)} [IsProbabilityMeasure P] {eps C : ℝ}
    (hC : 0 < C) (hS0 : ∀ᵐ g ∂P, 0 ≤ stopSum eps g) (i1 : Integrable (stopSum eps) P)
    (i2 : Integrable (fun g => stopSum eps g ^ 2) P) :
    ∫ g, testFn psiVar (stopSum eps g / C) ∂P =
      (∫ g, stopSum eps g ^ 2 ∂P) / C ^ 2 - 2 * (∫ g, stopSum eps g ∂P) / C := by
  have e : ∀ᵐ g ∂P, testFn psiVar (stopSum eps g / C) =
      1 / C ^ 2 * stopSum eps g ^ 2 - 2 / C * stopSum eps g := by
    filter_upwards [hS0] with g hg
    rcases hg.eq_or_lt with h | h
    · rw [← h, zero_div, testFn_nonneg_arg le_rfl]; ring
    · rw [testFn_psiVar (div_pos h hC)]
      field_simp
  rw [integral_congr_ae e, integral_sub (i2.const_mul _) (i1.const_mul _), integral_const_mul,
    integral_const_mul]
  ring


/-! ## Real identifications -/

theorem pwM2_eq (eps : ℝ) (ρ : ProbabilityMeasure ℝ) :
    pwM2 eps ρ = (lawVar ρ / eps ^ 2) ^ 2 * ∫ g, stopSum eps g ^ 2 ∂(iidLaw ρ) := by
  rw [pwM2, ← integral_const_mul]
  congr 1
  funext g
  ring

/-- `κ_{psiVar} = 2(M₂/C² - 1)`. -/
theorem pw_outKappa_psiVar {eps : ℝ} {ν : ProbabilityMeasure ℝ} (hC : 0 < lawC eps ν)
    (i1 : Integrable (stopSum eps) (iidLaw ν))
    (i2 : Integrable (fun g => stopSum eps g ^ 2) (iidLaw ν))
    (hW : ∫ g, stopSum eps g ∂(iidLaw ν) = lawC eps ν) :
    outKappa eps ν psiVar =
      2 * ((∫ g, stopSum eps g ^ 2 ∂(iidLaw ν)) / lawC eps ν ^ 2 - 1) := by
  have hSm : Measurable fun g => stopSum eps g / lawC eps ν := (measurable_stopSum eps).div_const _
  rw [outKappa, show ((lawPhi eps ν : ProbabilityMeasure ℝ) : Measure ℝ) =
      (iidLaw ν).map fun g => stopSum eps g / lawC eps ν from rfl,
    integral_map hSm.aemeasurable (by unfold psiVar; fun_prop)]
  have e : (fun g => stopSum eps g / lawC eps ν * psiVar (stopSum eps g / lawC eps ν)) =
      fun g => 2 / lawC eps ν ^ 2 * stopSum eps g ^ 2 - 2 / lawC eps ν * stopSum eps g := by
    funext g
    unfold psiVar
    field_simp
  rw [e, integral_sub (i2.const_mul _) (i1.const_mul _), integral_const_mul, integral_const_mul,
    hW]
  field_simp


/-- **Facts along the mixture segment** for `ε` large. -/
theorem pw_seg_facts (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (A θσ : ℝ) (hθσ : 0 < θσ) :
    ∃ e0 : ℝ, 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν σ : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ → ∀ t ∈ Icc (0 : ℝ) (tMix A θσ),
        MomClass (vhi + 1) (βMix D θ vlo) (vlo / 2) (mixPM ν σ t) ∧
        (∀ᵐ g ∂(iidLaw (mixPM ν σ t)), 0 ≤ stopSum eps g) ∧
        Integrable (stopSum eps) (iidLaw (mixPM ν σ t)) ∧
        Integrable (fun g => stopSum eps g ^ 2) (iidLaw (mixPM ν σ t)) ∧
        ∫ g, stopSum eps g ^ 2 ∂(iidLaw (mixPM ν σ t)) ≤ 2 * (eps ^ 2 / gamMix vlo) ^ 2 * CK ∧
        ∫ g, stopSum eps g ∂(iidLaw (mixPM ν σ t)) = lawC eps (mixPM ν σ t) ∧
        eps ^ 2 / (128 * (vhi + 1)) ≤ lawC eps (mixPM ν σ t) ∧
        lawC eps (mixPM ν σ t) ≤ cPlus / (vlo / 2) * eps ^ 2 ∧
        lawVar (mixPM ν σ t) = (1 - t) * lawVar ν + t * lawVar σ ∧
        pwM1 eps (mixPM ν σ t) = lawVar (mixPM ν σ t) * lawC eps (mixPM ν σ t) / eps ^ 2 := by
  obtain ⟨es, hes1, hmix⟩ := stopExp_mix (vhi := vhi) (A := A) hD hθ hvlo hθσ
  refine ⟨max es (epsZero (vhi + 1) (βMix D θ vlo)), hes1.trans (le_max_left _ _), ?_⟩
  intro eps heps ν σ hν hσ t ht
  have hes' : es ≤ eps := (le_max_left _ _).trans heps
  have hez : epsZero (vhi + 1) (βMix D θ vlo) ≤ eps := (le_max_right _ _).trans heps
  have heps0 : 0 < eps := by linarith
  have hm := momClass_mix hθ hvlo hθσ hν hσ ht
  have hS0 : ∀ᵐ g ∂(iidLaw (mixPM ν σ t)), 0 ≤ stopSum eps g := by
    filter_upwards [ae_pos_iidLaw hm.pos] with g hg
    exact rawAsm_stopSum_nonneg fun j => (hg j).le
  obtain ⟨hi, hl⟩ := (hmix eps hes' ν σ hν hσ t ht).2.2 (gamMix vlo) (gamMix_pos hvlo).le le_rfl
  obtain ⟨i1, i2, hb⟩ := pw_stopSum_sq_facts (gamMix_pos hvlo) heps0 hS0 hi hl
  obtain ⟨-, hCm, hCp'⟩ := momClass_oneLayer (by positivity) hez hm
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ((tMix_le A θσ hθσ).trans (by norm_num))⟩
  refine ⟨hm, hS0, i1, i2, hb, pw_integral_stopSum (by positivity) hez hm, hCm, ?_,
    pw_lawVar_mix hθ hvlo hθσ hν hσ ht1, pwM1_eq (by positivity) hez hm⟩
  exact hCp'.trans (le_of_eq (by ring))

/-- **The normalised output test** at the base scale `C ≥ ε²/b₀`. -/
theorem pw_normTest {η M : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hM : 0 < M)
    {C b₀ eps : ℝ} (hb₀ : 0 < b₀) (heps : 0 < eps) (hC : eps ^ 2 / b₀ ≤ C) :
    Measurable (fun y => testFn ψ (y / C) / (M / η)) ∧
      ∀ y, 0 ≤ y → |testFn ψ (y / C) / (M / η)| ≤ Real.exp (2 * η * b₀ / eps ^ 2 * y) := by
  have heps2 : 0 < eps ^ 2 := by positivity
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC
  have hk : 0 < M / η := by positivity
  refine ⟨(hψ.measurable_testFn.comp (measurable_id.div_const _)).div_const _, fun y hy => ?_⟩
  have h := pw_testFn_div_le hψ hη hC0 hy
  rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
  refine h.trans ?_
  rw [mul_comm]
  gcongr
  have h1 : 1 / C ≤ b₀ / eps ^ 2 := by
    rw [div_le_div_iff₀ hC0 heps2]
    rw [div_le_iff₀ hb₀] at hC
    linarith
  calc 2 * η * y / C = 2 * η * y * (1 / C) := by ring
    _ ≤ 2 * η * y * (b₀ / eps ^ 2) := by gcongr
    _ = 2 * η * b₀ / eps ^ 2 * y := by ring

/-- Rescaling the kernel of an output test. -/
theorem pw_outIns_eq_mul (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ) {c : ℝ} (hc : c ≠ 0)
    (x : ℝ) :
    outIns eps ν ψ x =
      c * insKernel eps ν (fun g => testFn ψ (stopSum eps g / lawC eps ν) / c) x := by
  rw [outIns, ← insKernel_const_mul]
  congr 1
  funext g
  field_simp

/-- The exponent `κ = a/ε²` is below `θ'` for `ε ≥ a/θ' + 1`. -/
theorem pw_kappa_le {a θ' eps : ℝ} (ha : 0 ≤ a) (hθ' : 0 < θ') (heps : a / θ' + 1 ≤ eps) :
    a / eps ^ 2 ≤ θ' := by
  have heps1 : 1 ≤ eps := by
    have : 0 ≤ a / θ' := by positivity
    linarith
  have heps0 : 0 < eps := by linarith
  have hee : eps ≤ eps ^ 2 := le_self_pow₀ heps1 (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  have h1 : a / θ' ≤ eps := by linarith
  rw [div_le_iff₀ hθ'] at h1
  nlinarith

end

end PGM
