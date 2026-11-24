import PLAStochastic.Index.GEP.QuadResponse.ScaleLipschitz

/-!
# WP4 leaf `QuadResponse`: the continuation `H = f⁺ - f⁻` for two directions of different variance

For two direction laws `σ₊, σ₋` (same `A, θσ`), the `RawDiscId` continuations `f±` of the fixed-base
test `E_{ν_t^±} φ_ψ(S_T/C₀)/(M/η)` give `H = f⁺ - f⁻`, holomorphic on a fixed disc with
`‖H‖ ≤ K ε^p`, `H(0) = 0`, `H'(0) = ∫ I d(σ₊ - σ₋)` and, on the real segment,
`‖H(t)‖ ≤ K ε^{-βU} + K t`: the (U) comparisons of `pw_real_test` for the two rescaled tests,
plus the change of scale under `ν` (`quad_third_term`, `quad_c_diff`) which is `O(t)` because
`v_t^+ - v_t^- = t (v_σ₊ - v_σ₋)` (`quad_pair_H`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

variable {D θ vlo vhi : ℝ}

/-- `φ_{c ψ(c ·)/k}(W) = φ_ψ(c W)/k`. -/
theorem quad_scaled_test_eq {ψ : ℝ → ℝ} {c k : ℝ} (hc : 0 < c) (W : ℝ) :
    testFn (fun s => c * ψ (c * s) / k) W = testFn ψ (c * W) / k := by
  rw [pw_testFn_div, ← pw_testFn_mul hc]

theorem quad_abs_three {a b x y B₁ B₂ B₃ : ℝ} (h1 : |a - x| ≤ B₁) (h2 : |y - b| ≤ B₂)
    (h3 : |x - y| ≤ B₃) : |a - b| ≤ B₁ + B₃ + B₂ := by
  calc |a - b| = |(a - x) + (x - y) + (y - b)| := by ring_nf
    _ ≤ |a - x| + |x - y| + |y - b| := abs_add_three _ _ _
    _ ≤ B₁ + B₃ + B₂ := by linarith

/-- **The pair continuation with the `O(ε^{-βU}) + O(t)` segment bound.** -/
theorem quad_pair_H (hS : SurvivalBound) {βU : ℝ} (hUM : PwUnivMix βU)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) {A θσ : ℝ} (hθσ : 0 < θσ) :
    ∃ ηQ R Kb Kd Kq e0 : ℝ, ∃ p : ℕ, 0 < ηQ ∧ 0 < R ∧ R ≤ 1 ∧ 0 ≤ Kb ∧ 0 ≤ Kd ∧ 0 ≤ Kq ∧
      1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν σp σm : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
        SigmaLaw A θσ σp → SigmaLaw A θσ σm → ∀ M ψ, 0 < M → OutTest ηQ M ψ →
        Integrable (outIns eps ν ψ) (σp : Measure ℝ) ∧ Integrable (outIns eps ν ψ) (σm : Measure ℝ) ∧
        Integrable (outIns eps ν ψ) (ν : Measure ℝ) ∧
        ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 R) ∧
          (∀ z ∈ ball (0 : ℂ) R, ‖H z‖ ≤ Kb * eps ^ p) ∧
          (∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖H t‖ ≤ Kd * eps ^ (-βU) + Kq * t) ∧
          |(∫ x, outIns eps ν ψ x ∂(σp : Measure ℝ)) - ∫ x, outIns eps ν ψ x ∂(σm : Measure ℝ)| =
            M / ηQ * ‖deriv H 0‖ := by
  have hvhi : 0 < vhi + 1 := by linarith
  set b₀ : ℝ := 128 * (vhi + 1) with hb₀
  have hb₀0 : 0 < b₀ := by positivity
  set cM : ℝ := 2 * b₀ / vlo with hcM
  have hcM0 : 0 < cM := by positivity
  have hgM := gamMix_pos hvlo
  obtain ⟨γR, hγR, hRD⟩ := rawDiscId_of_survivalBound hS D θ vlo vhi hD hθ hvlo hv
  obtain ⟨κ₁, K₁, e₁, hκ₁, -, -, hker⟩ := pw_kernel_facts hD hθ hvlo hv
  obtain ⟨γ', hγ', hRT⟩ := pw_real_test hUM hD hθ hvlo hv
  -- the output weight
  set ηQ : ℝ := min (min γR κ₁ / (2 * b₀))
    (min (γ' * vlo / (2 * b₀)) (gamMix vlo / (2 * cM * (vhi + 1)))) with hηQ
  have hηQ0 : 0 < ηQ := by positivity
  have hηQ1 : 2 * ηQ * b₀ ≤ min γR κ₁ := by
    have h : ηQ ≤ min γR κ₁ / (2 * b₀) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hηQγ : ηQ * cM ≤ γ' := by
    have h : ηQ ≤ γ' * vlo / (2 * b₀) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h
    rw [hcM, mul_div_assoc', div_le_iff₀ hvlo]
    exact h
  have hηQg : 2 * ηQ * cM * (vhi + 1) ≤ gamMix vlo := by
    have h : ηQ ≤ gamMix vlo / (2 * cM * (vhi + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨rR, KR, eR, pR, hrR, hRD'⟩ := hRD A θσ hθσ
  obtain ⟨KT, eT, hKT, -, hRT'⟩ := hRT A θσ hθσ
  obtain ⟨es, hes1, hseg⟩ := pw_seg_facts (vhi := vhi) hD hθ hvlo A θσ hθσ
  obtain ⟨em, -, hmix⟩ := stopExp_mix (vhi := vhi) (A := A) hD hθ hvlo hθσ
  have hks := kapSig_nonneg A θσ hθσ
  have hCK : (0 : ℝ) < CK := by unfold CK; norm_num
  set R : ℝ := min rR (tMix A θσ) with hRdef
  have hR0 : 0 < R := lt_min hrR (tMix_pos A θσ hθσ)
  have hRr : R ≤ rR := min_le_left _ _
  have hRt : R ≤ tMix A θσ := min_le_right _ _
  have hR1 : R ≤ 1 := hRt.trans ((tMix_le A θσ hθσ).trans (by norm_num))
  set eκ : ℝ := 2 * ηQ * b₀ * (1 / θσ + 2 / θ) + 1 with heκ
  refine ⟨ηQ, R, 2 * |KR|, 2 * (ηQ * cM * KT),
    4 * b₀ / vlo ^ 2 * kapSig A θσ * (CK / cM), max (max eR eT) (max (max es e₁) (max em eκ)),
    pR, hηQ0, hR0, hR1, by positivity, by positivity, by positivity,
    hes1.trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))), ?_⟩
  intro eps heps ν σp σm hν hσp hσm M ψ hM hψ
  have hle1 : ∀ {a : ℝ}, a ≤ max (max eR eT) (max (max es e₁) (max em eκ)) → a ≤ eps :=
    fun h => h.trans heps
  have heR' : eR ≤ eps := hle1 ((le_max_left _ _).trans (le_max_left _ _))
  have heT' : eT ≤ eps := hle1 ((le_max_right _ _).trans (le_max_left _ _))
  have hes' : es ≤ eps := hle1 ((le_max_left _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _)))
  have he₁' : e₁ ≤ eps := hle1 ((le_max_right _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _)))
  have hem' : em ≤ eps := hle1 ((le_max_left _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _)))
  have heκ' : eκ ≤ eps := hle1 ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _)))
  have heps1 : 1 ≤ eps := hes1.trans hes'
  have heps0 : 0 < eps := by linarith only [heps1]
  have heps2 : (0 : ℝ) < eps ^ 2 := by positivity
  -- the base law
  have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨le_rfl, (tMix_pos A θσ hθσ).le⟩
  obtain ⟨-, hS0ν, -, -, -, -, hCmν, -, -, -⟩ := hseg eps hes' ν σp hν hσp 0 h0t
  simp only [mixPM_zero] at hS0ν hCmν
  rw [← hb₀] at hCmν
  set C₀ := lawC eps ν with hC₀
  have hC0 : 0 < C₀ := lt_of_lt_of_le (by positivity) hCmν
  have hC₀e : eps ^ 2 ≤ b₀ * C₀ := by
    have := hCmν
    rw [div_le_iff₀ hb₀0] at this
    linarith only [this]
  set v := lawVar ν with hvdef
  have hv0 : vlo ≤ v := hν.var_ge
  have hvle : v ≤ vhi := hν.var_le
  have hvpos : 0 < v := hvlo.trans_le hv0
  have hvσp := hσp.lawVar_le hθσ
  have hvσm := hσm.lawVar_le hθσ
  have hvσp0 := hσp.lawVar_nonneg
  have hvσm0 := hσm.lawVar_nonneg
  -- the exponential moment of `W = v S_T/ε²` under `ν`
  have hWint : Integrable (fun g => Real.exp (2 * ηQ * cM * (v * stopSum eps g / eps ^ 2)))
      (iidLaw ν) ∧
      ∫ g, Real.exp (2 * ηQ * cM * (v * stopSum eps g / eps ^ 2)) ∂(iidLaw ν) ≤ CK := by
    have hc0 : 0 ≤ 2 * ηQ * cM * v := by positivity
    have hcg : 2 * ηQ * cM * v ≤ gamMix vlo := by
      refine le_trans ?_ hηQg
      gcongr
      linarith only [hvle]
    obtain ⟨hi, hl⟩ := (hmix eps hem' ν σp hν hσp 0 h0t).2.2 (2 * ηQ * cM * v) hc0 hcg
    rw [mixPM_zero] at hi hl
    have e : (fun g => Real.exp (2 * ηQ * cM * (v * stopSum eps g / eps ^ 2))) =
        fun g => Real.exp (2 * ηQ * cM * v * stopSum eps g / eps ^ 2) := by
      funext g; ring_nf
    rw [e]
    exact ⟨hi, hl⟩
  have hWm : Measurable fun g => v * stopSum eps g / eps ^ 2 :=
    (measurable_const.mul (measurable_stopSum eps)).div_const _
  have hW0 : ∀ᵐ g ∂(iidLaw ν), 0 ≤ v * stopSum eps g / eps ^ 2 := by
    filter_upwards [hS0ν] with g hg
    positivity
  -- the normalised test
  obtain ⟨hFm, hFκ⟩ := pw_normTest hψ hηQ0 hM hb₀0 heps0 hCmν
  set Fh : ℝ → ℝ := fun y => testFn ψ (y / C₀) / (M / ηQ) with hFh
  set κ : ℝ := 2 * ηQ * b₀ / eps ^ 2 with hκ
  have hκγ : κ * eps ^ 2 ≤ min γR κ₁ := by
    rw [hκ, div_mul_cancel₀ _ heps2.ne']; exact hηQ1
  have hFγ : ∀ y, 0 ≤ y → |Fh y| ≤ Real.exp (γR * y / eps ^ 2) := by
    intro y hy
    refine (hFκ y hy).trans (Real.exp_le_exp.2 ?_)
    have h1 : κ ≤ γR / eps ^ 2 := by
      rw [le_div_iff₀ heps2]; exact hκγ.trans (min_le_left _ _)
    calc κ * y ≤ γR / eps ^ 2 * y := mul_le_mul_of_nonneg_right h1 hy
      _ = γR * y / eps ^ 2 := by ring
  have hk0 : (0 : ℝ) < M / ηQ := by positivity
  have houtIns : outIns eps ν ψ =
      fun x => M / ηQ * insKernel eps ν (fun g => Fh (stopSum eps g)) x := by
    funext x
    exact pw_outIns_eq_mul eps ν ψ hk0.ne' x
  -- integrability of the kernel
  have hκ0 : 0 ≤ κ := by positivity
  obtain ⟨-, -, hIint⟩ := hker eps he₁' ν hν κ hκ0 (hκγ.trans (min_le_right _ _)) Fh hFm hFκ
  have heκ1 : 2 * ηQ * b₀ * (1 / θσ) + 1 ≤ eps := by
    refine le_trans ?_ heκ'
    rw [heκ]
    have : 0 ≤ 2 * ηQ * b₀ * (2 / θ) := by positivity
    linarith only [this]
  have heκ2 : 2 * ηQ * b₀ * (2 / θ) + 1 ≤ eps := by
    refine le_trans ?_ heκ'
    rw [heκ]
    have : 0 ≤ 2 * ηQ * b₀ * (1 / θσ) := by positivity
    linarith only [this]
  have hκσ : κ ≤ θσ := by
    rw [hκ]
    refine pw_kappa_le (by positivity) hθσ ?_
    rw [div_eq_mul_one_div]; exact heκ1
  have hκν : κ ≤ θ / 2 := by
    rw [hκ]
    refine pw_kappa_le (by positivity) (half_pos hθ) ?_
    rw [div_div_eq_mul_div, mul_div_assoc]; exact heκ2
  have hIp : Integrable (outIns eps ν ψ) (σp : Measure ℝ) := by
    rw [houtIns]; exact (hIint σp hσp.pos (hσp.integrable_exp hκσ)).const_mul _
  have hIm : Integrable (outIns eps ν ψ) (σm : Measure ℝ) := by
    rw [houtIns]; exact (hIint σm hσm.pos (hσm.integrable_exp hκσ)).const_mul _
  have hIν : Integrable (outIns eps ν ψ) (ν : Measure ℝ) := by
    rw [houtIns]; exact (hIint ν (hν.pos' hθ hvlo) (hν.integrable_exp hθ hvlo hκν)).const_mul _
  -- the continuations
  obtain ⟨fp, hfp, hfpb, -, hfpd, hfpr⟩ := hRD' eps heR' ν σp hν hσp Fh hFm hFγ
  obtain ⟨fm, hfm, hfmb, -, hfmd, hfmr⟩ := hRD' eps heR' ν σm hν hσm Fh hFm hFγ
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
  -- the real segment
  have hHs : ∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖H t‖ ≤ 2 * (ηQ * cM * KT) * eps ^ (-βU) +
      4 * b₀ / vlo ^ 2 * kapSig A θσ * (CK / cM) * t := by
    intro t ht0 ht1
    have ht : t ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨ht0, by linarith only [ht1, hRt, hR0]⟩
    have ht1' : t ∈ Icc (0 : ℝ) 1 :=
      ⟨ht0, by linarith only [ht1, hRt, hR0, tMix_le A θσ hθσ]⟩
    have hmp := momClass_mix hθ hvlo hθσ hν hσp ht
    have hmm := momClass_mix hθ hvlo hθσ hν hσm ht
    have hvp : vlo / 2 ≤ lawVar (mixPM ν σp t) := hmp.var_ge
    have hvm : vlo / 2 ≤ lawVar (mixPM ν σm t) := hmm.var_ge
    have hvp0 : 0 < lawVar (mixPM ν σp t) := by linarith only [hvp, half_pos hvlo]
    have hvm0 : 0 < lawVar (mixPM ν σm t) := by linarith only [hvm, half_pos hvlo]
    have hct : ∀ vt : ℝ, vlo / 2 ≤ vt → eps ^ 2 / (vt * C₀) ≤ cM := by
      intro vt hvt
      have hvt0 : 0 < vt := by linarith only [hvt, half_pos hvlo]
      rw [hcM, div_le_div_iff₀ (by positivity) hvlo]
      have h3 : 0 ≤ b₀ * C₀ := by positivity
      linarith only [mul_nonneg (sub_nonneg.2 hvt) h3, mul_nonneg (sub_nonneg.2 hC₀e) hvlo.le]
    have hcp := hct _ hvp
    have hcm' := hct _ hvm
    have hcp0 : 0 < eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) := by positivity
    have hcm0 : 0 < eps ^ 2 / (lawVar (mixPM ν σm t) * C₀) := by positivity
    have hχp := pw_pair_outTest hψ hM hηQ0 hcp0 hcp hηQγ
    have hχm := pw_pair_outTest hψ hM hηQ0 hcm0 hcm' hηQγ
    have hEp : ∫ g, Fh (stopSum eps g) ∂(iidLaw (mixPM ν σp t)) =
        ∫ g, testFn (fun s => eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) *
            ψ (eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) * s) / (M / ηQ))
          (lawVar (mixPM ν σp t) * stopSum eps g / eps ^ 2) ∂(iidLaw (mixPM ν σp t)) := by
      congr 1
      funext g
      simp only [hFh]
      exact pw_pair_test_eq hvp0 hC0 heps0 _
    have hEm : ∫ g, Fh (stopSum eps g) ∂(iidLaw (mixPM ν σm t)) =
        ∫ g, testFn (fun s => eps ^ 2 / (lawVar (mixPM ν σm t) * C₀) *
            ψ (eps ^ 2 / (lawVar (mixPM ν σm t) * C₀) * s) / (M / ηQ))
          (lawVar (mixPM ν σm t) * stopSum eps g / eps ^ 2) ∂(iidLaw (mixPM ν σm t)) := by
      congr 1
      funext g
      simp only [hFh]
      exact pw_pair_test_eq hvm0 hC0 heps0 _
    have h1 := hRT' eps heT' ν σp hν hσp t ht _ _ hχp
    have h2 := hRT' eps heT' ν σm hν hσm t ht _ _ hχm
    -- the change of scale under `ν`
    have hXp : ∫ g, testFn (fun s => eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) *
        ψ (eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) * s) / (M / ηQ))
          (lawVar ν * stopSum eps g / eps ^ 2) ∂(iidLaw ν) =
        ∫ g, testFn ψ (eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) * (v * stopSum eps g / eps ^ 2)) /
          (M / ηQ) ∂(iidLaw ν) := by
      congr 1
      funext g
      exact quad_scaled_test_eq hcp0 _
    have hXm : ∫ g, testFn (fun s => eps ^ 2 / (lawVar (mixPM ν σm t) * C₀) *
        ψ (eps ^ 2 / (lawVar (mixPM ν σm t) * C₀) * s) / (M / ηQ))
          (lawVar ν * stopSum eps g / eps ^ 2) ∂(iidLaw ν) =
        ∫ g, testFn ψ (eps ^ 2 / (lawVar (mixPM ν σm t) * C₀) * (v * stopSum eps g / eps ^ 2)) /
          (M / ηQ) ∂(iidLaw ν) := by
      congr 1
      funext g
      exact quad_scaled_test_eq hcm0 _
    obtain ⟨-, -, h3⟩ := quad_third_term hψ hηQ0 hM hcp0 hcp hcm0 hcm' hWm hW0 hWint.1 hWint.2
    have hcd := quad_c_diff (eps := eps) hvlo hvp hvm hC0 hb₀0 hC₀e
    have hvt : lawVar (mixPM ν σp t) - lawVar (mixPM ν σm t) = t * (lawVar σp - lawVar σm) := by
      rw [pw_lawVar_mix hθ hvlo hθσ hν hσp ht1', pw_lawVar_mix hθ hvlo hθσ hν hσm ht1']
      ring
    have hvσ : |lawVar σp - lawVar σm| ≤ kapSig A θσ := by
      rw [abs_le]; constructor <;> linarith only [hvσp, hvσm, hvσp0, hvσm0]
    have h4 : |eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) - eps ^ 2 / (lawVar (mixPM ν σm t) * C₀)| ≤
        4 * b₀ / vlo ^ 2 * kapSig A θσ * t := by
      refine hcd.trans ?_
      rw [hvt, abs_mul, abs_of_nonneg ht0]
      calc 4 * b₀ / vlo ^ 2 * (t * |lawVar σp - lawVar σm|)
          ≤ 4 * b₀ / vlo ^ 2 * (t * kapSig A θσ) := by gcongr
        _ = 4 * b₀ / vlo ^ 2 * kapSig A θσ * t := by ring
    have h5 : |∫ g, testFn ψ (eps ^ 2 / (lawVar (mixPM ν σp t) * C₀) *
        (v * stopSum eps g / eps ^ 2)) / (M / ηQ) ∂(iidLaw ν) -
        ∫ g, testFn ψ (eps ^ 2 / (lawVar (mixPM ν σm t) * C₀) *
        (v * stopSum eps g / eps ^ 2)) / (M / ηQ) ∂(iidLaw ν)| ≤
        4 * b₀ / vlo ^ 2 * kapSig A θσ * (CK / cM) * t := by
      refine h3.trans ?_
      calc _ ≤ 4 * b₀ / vlo ^ 2 * kapSig A θσ * t * (CK / cM) := by gcongr
        _ = 4 * b₀ / vlo ^ 2 * kapSig A θσ * (CK / cM) * t := by ring
    -- assemble
    simp only [hH]
    rw [hfpr t ht0 (by linarith only [ht1, hRr]), hfmr t ht0 (by linarith only [ht1, hRr]),
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hEp, hEm]
    rw [hXp] at h1
    rw [hXm, abs_sub_comm] at h2
    exact (quad_abs_three h1 h2 h5).trans (le_of_eq (by ring))
  -- the derivative
  have hdp : DifferentiableAt ℂ fp 0 :=
    hfp.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrR))
  have hdm : DifferentiableAt ℂ fm 0 :=
    hfm.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrR))
  have hHd0 : deriv H 0 = deriv fp 0 - deriv fm 0 := by
    rw [hH]
    exact (hdp.hasDerivAt.sub hdm.hasDerivAt).deriv
  refine ⟨hIp, hIm, hIν, H, hHd, hHb, hHs, ?_⟩
  rw [hHd0, hfpd, hfmd, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, houtIns,
    integral_const_mul, integral_const_mul, ← mul_sub, abs_mul, abs_of_pos hk0]
  congr 1
  congr 1
  ring

end

end PGM
