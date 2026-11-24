import PLAStochastic.Index.GEP.PointwiseSmall.LengthKernelBound
import PLAStochastic.Index.GEP.RawDisc.OfSurvivalBound

/-!
# WP4 leaves `PointwiseSmall`, `QuadResponse`: the continuation of `C_ε`

Along `ν_z = (1 - z) ν + z σ` the mean segment length has the fixed-disc continuation
`f_C z = ∑_k cSurv_k(z)(1)` (`pw_cDisc`):

* `SurvivalBound` with the test `G = 1` gives a common summable majorant on `ball 0 r_S`, so `f_C`
  is holomorphic with `‖f_C‖ ≤ K ε^p` (Weierstrass M-test);
* on the real segment `[0, r]`, `r ≤ tMix A θσ`, `cSurv_k(t)(1) = P_{ν_t}(k < T)` (`cSurv_ofReal`)
  and `∑_k P_{ν_t}(k < T) = C_ε(ν_t)` (`lawC_eq_tsum`, `T < ∞` a.s. by `momClass_mix`);
* `f_C'(0) = ∑_k survLin_k = ∑_k (∑_{i<k} P_{w{i}}(k < T) - k P_ν(k < T))`
  (`hasSum_deriv_of_summable_norm`, `hasDerivAt_cSurv_zero`), which is
  `∫ J_C dσ - ∫ J_C dν` by the two series of `pw_hasSum_integral_lawJC`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

variable {D θ vlo vhi : ℝ}

theorem survInt_one (eps : ℝ) (μ : Measure (ℕ → ℝ)) (k : ℕ) :
    survInt eps μ k (fun _ => 1) = μ.real (survSet eps k) := by
  rw [survInt, integral_indicator_const _ (measurableSet_survSet eps k), smul_eq_mul, mul_one]

/-- **The continuation of `C_ε` on a fixed disc** (`G = 1` in `SurvivalBound`): holomorphic,
polynomially bounded, equal to `C_ε(ν_t)` on the real segment, with derivative
`∫ J_C dσ - ∫ J_C dν` at `0`. -/
theorem pw_cDisc (hS : SurvivalBound) (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hv : vlo ≤ vhi) {A θσ : ℝ} (hθσ : 0 < θσ) :
    ∃ (r K e0 : ℝ) (p : ℕ), 0 < r ∧ r ≤ tMix A θσ ∧ 1 ≤ e0 ∧
      ∀ eps, e0 ≤ eps → ∀ ν σ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
        SigmaLaw A θσ σ → ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 r) ∧
          (∀ z ∈ ball (0 : ℂ) r, ‖f z‖ ≤ K * eps ^ p) ∧
          (∀ t : ℝ, 0 ≤ t → t ≤ r → f t = ((lawC eps (mixPM ν σ t) : ℝ) : ℂ)) ∧
          deriv f 0 = (((∫ x, lawJC eps ν x ∂(σ : Measure ℝ)) -
            ∫ x, lawJC eps ν x ∂(ν : Measure ℝ) : ℝ) : ℂ) := by
  obtain ⟨γ, hγ, hSB⟩ := hS D θ vlo vhi hD hθ hvlo hv
  obtain ⟨rS, KS, eS, p, hrS, hB⟩ := hSB A θσ hθσ
  obtain ⟨eJ, heJ1, hJ⟩ := pw_hasSum_integral_lawJC hD hθ hvlo hv
  have htm := tMix_pos A θσ hθσ
  set r := min rS (tMix A θσ) with hrdef
  have hr0 : 0 < r := lt_min hrS htm
  have hrS' : r ≤ rS := min_le_left _ _
  have hrt : r ≤ tMix A θσ := min_le_right _ _
  have hr1 : r ≤ 1 := hrt.trans ((tMix_le A θσ hθσ).trans (by norm_num))
  refine ⟨r, KS, max (max eS eJ) (epsZero (vhi + 1) (βMix D θ vlo)), p, hr0, hrt,
    heJ1.trans ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  intro eps heps ν σ hν hσ
  have heS : eS ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have heJ : eJ ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have hez : epsZero (vhi + 1) (βMix D θ vlo) ≤ eps := le_trans (le_max_right _ _) heps
  have heps0 : 0 ≤ eps := by linarith
  obtain ⟨B, hBs, hBsum, hBz⟩ := hB eps heS ν σ hν hσ (fun _ => 1) measurable_const
    (fun y hy => by
      rw [abs_one]
      exact Real.one_le_exp (by positivity))
  set u : ℕ → ℂ → ℂ := fun k z => cSurv eps ν σ z k (fun _ => 1) with hu
  have hub : ∀ k, ∀ z ∈ ball (0 : ℂ) r, ‖u k z‖ ≤ B k := fun k z hz =>
    hBz z (ball_subset_ball hrS' hz) k
  have hdiff : ∀ k, DifferentiableOn ℂ (u k) (ball (0 : ℂ) r) := fun k =>
    (differentiable_cSurv eps ν σ k _).differentiableOn
  refine ⟨fun z => ∑' k, u k z, ?_, ?_, ?_, ?_⟩
  · exact Complex.differentiableOn_tsum_of_summable_norm hBs hdiff isOpen_ball
      fun k w hw => hub k w hw
  · intro z hz
    exact (tsum_of_norm_bounded hBs.hasSum fun k => hub k z hz).trans hBsum
  · intro t ht0 htr
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, htr.trans hr1⟩
    have htm' : t ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨ht0, htr.trans hrt⟩
    have hm := momClass_mix hθ hvlo hθσ hν hσ htm'
    obtain ⟨hfin, -, -⟩ := momClass_oneLayer (by positivity) hez hm
    have hk : ∀ k, u k (t : ℂ) = (((iidLaw (mixPM ν σ t)).real (survSet eps k) : ℝ) : ℂ) := by
      intro k
      simp only [hu]
      rw [cSurv_ofReal eps ν σ ht1 k measurable_const
        (fun S _ => (integrable_const (1 : ℝ)).indicator (measurableSet_survSet eps k)),
        survInt_one]
    simp_rw [hk]
    rw [← Complex.ofReal_tsum, lawC_eq_tsum hfin]
    rfl
  · have hDs := Complex.hasSum_deriv_of_summable_norm hBs hdiff isOpen_ball
      (fun k w hw => hub k w hw) (mem_ball_self hr0)
    have hdk : ∀ k, deriv (u k) 0 = ((survLin eps ν σ k (fun _ => 1) : ℝ) : ℂ) := fun k =>
      (hasDerivAt_cSurv_zero eps ν σ k _).deriv
    simp_rw [hdk] at hDs
    have hσs := hJ eps heJ ν hν σ
    have hνs := hJ eps heJ ν hν ν
    have hR : HasSum (fun k => survLin eps ν σ k (fun _ => 1))
        ((∫ x, lawJC eps ν x ∂(σ : Measure ℝ)) - ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)) := by
      refine (hσs.sub hνs).congr_fun fun k => ?_
      simp only [survLin, survInt_one, pwLaw_self, pwLaw_sigma, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    exact hDs.unique (Complex.hasSum_ofReal.2 hR)

end

end PGM
