import PLAStochastic.Index.GEP.RawDisc.ColumnSums
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# WP4 `RawDisc` from the survival bound (`rawDisc_of_survivalBound`)

Route (`research/2026-09-30-lean-gep-direct-term/rawdisc-design.md` §0–1):

* **Weights.**  The output weight is `γ = min γ_S (gamMix vlo / 2)`: `γ_S` from `SurvivalBound`,
  `gamMix vlo = θK (vlo/2) / cPlus` from the mixture class (`stopExp_mix`); both depend on the
  class only, so `γ` is chosen before `(A, θσ)`.  The radius is `r = min (min r_S 1) (tMix A θσ)`,
  so that on `[0, r/8]` the mixture `ν_t` lies in the moment class.  For `ε` large the rate
  `l = γ/ε²` has `E e^{l X} ≤ 2` under `ν` and `σ` (`lintegral_exp_le_two`).
* **The function.**  With `G_ρ = incFn F ρ` (`|G_ρ| ≤ 3 e^{l s}`),
  `f z = F 0 + ∑_k Ψ_k(z)`, `Ψ_k = occTerm = (1 - z) cSurv_k(G_ν) + z cSurv_k(G_σ)`.  The survival
  bound applied to `G_ν/3` and `G_σ/3` gives `‖Ψ_k‖ ≤ 6 (B^ν_k + B^σ_k)` on `ball 0 r`; hence `f` is
  holomorphic (Weierstrass M-test, `differentiableOn_tsum_of_summable_norm`) and
  `‖f‖ ≤ 1 + 12 K_S ε^p`.
* **Real segment.**  `f t = E_{ν_t}[F(S_T)]` (`occ_series_ofReal`), and
  `|E_{ν_t} F(S_T)| ≤ E_{ν_t} e^{γ S_T/ε²} ≤ CK` (`stopExp_mix`).
* **Derivative.**  `deriv f 0 = ∑_k Ψ_k'(0)` (`hasSum_deriv_of_summable_norm`) and
  `∑_k Ψ_k'(0) = ∫ I_F dσ - ∫ I_F dν` (`hasSum_occDeriv`); the column sums it needs come from
  the stopping moments of `ν` (`wSummable_self`) and from the survival bound applied to the positive
  test `e^{l y}` (`wSummable_sigma`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-- **`RawDisc` from the survival bound.**  The occupation series
`f z = F 0 + ∑_k ((1 - z) cSurv_k(G_ν) + z cSurv_k(G_σ))` is holomorphic on a disc of fixed radius
with `‖f‖ ≤ K ε^p`, equals `E_{ν_t}[F(S_T)]` on the real segment, and has
`f'(0) = ∫ I_F dσ - ∫ I_F dν`. -/
theorem rawDisc_of_survivalBound (hS : SurvivalBound) : RawDisc := by
  intro D θ vlo vhi hD hθ hvlo hv
  obtain ⟨γS, hγS, hSB⟩ := hS D θ vlo vhi hD hθ hvlo hv
  set γ : ℝ := min γS (gamMix vlo / 2) with hγdef
  have hγ0 : 0 < γ := lt_min hγS (half_pos (gamMix_pos hvlo))
  have hγS' : γ ≤ γS := min_le_left _ _
  have hγM : 2 * γ ≤ gamMix vlo := by
    have := min_le_right γS (gamMix vlo / 2); linarith
  refine ⟨γ, hγ0, fun A θσ hθσ => ?_⟩
  obtain ⟨rS, KS, eS, p, hrS, hB⟩ := hSB A θσ hθσ
  obtain ⟨e₁, -, hmix⟩ := stopExp_mix (vhi := vhi) (A := A) hD hθ hvlo hθσ
  have hlam0 : 0 < lamMix D θ A θσ := lamMix_pos hθ hθσ
  set r : ℝ := min (min rS 1) (tMix A θσ) with hrdef
  have hr0 : 0 < r := lt_min (lt_min hrS one_pos) (tMix_pos A θσ hθσ)
  have hr1 : r ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hrS' : r ≤ rS := (min_le_left _ _).trans (min_le_left _ _)
  have hrt : r ≤ tMix A θσ := min_le_right _ _
  refine ⟨r, max (1 + 12 * max KS 0) CK, max (max eS e₁) (max 1 (γ / lamMix D θ A θσ)), p, hr0,
    ?_⟩
  intro eps heps ν σ hν hσ F hFm hFb
  have heS : eS ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have he₁ : e₁ ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have heps1 : 1 ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) heps
  have hepslam : γ / lamMix D θ A θσ ≤ eps :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) heps
  have heps0 : 0 < eps := by linarith
  have heps2 : 0 < eps ^ 2 := by positivity
  set l : ℝ := γ / eps ^ 2 with hldef
  have hl0 : 0 ≤ l := by positivity
  have hllam : l ≤ lamMix D θ A θσ := by
    rw [hldef, div_le_iff₀ heps2]
    rw [div_le_iff₀ hlam0] at hepslam
    nlinarith
  have hlγ : ∀ c y : ℝ, c * γ * y / eps ^ 2 = c * (l * y) := fun c y => by
    rw [hldef]; ring
  -- small exponential moments
  obtain ⟨⟨iν, lν, llν⟩, ⟨iσ, lσ, llσ⟩⟩ := lintegral_exp_le_two hθ hvlo hθσ hν hσ hl0 hllam
  have hνm : SmallMgf l ν := ⟨hν.pos' hθ hvlo, iν, lν, llν⟩
  have hσm : SmallMgf l σ := ⟨hσ.pos, iσ, lσ, llσ⟩
  have hFb' : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y) := fun y hy => by
    have h := hFb y hy
    rwa [show γ * y / eps ^ 2 = l * y by rw [hldef]; ring] at h
  have hExp : ∀ y, 0 ≤ y → Real.exp (l * y) ≤ Real.exp (γS * y / eps ^ 2) := fun y hy => by
    refine Real.exp_le_exp.2 ?_
    rw [hldef, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hγS' hy) heps2.le
  -- the survival majorants
  have hGνm := measurable_incFn hFm ν
  have hGσm := measurable_incFn hFm σ
  have htest : ∀ {α : ProbabilityMeasure ℝ}, SmallMgf l α → ∀ y, 0 ≤ y →
      |incFn F α y / 3| ≤ Real.exp (γS * y / eps ^ 2) := fun hα y hy => by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3), div_le_iff₀ (by norm_num)]
    have h1 := abs_incFn_le hα hFb' hy
    have h2 := hExp y hy
    linarith
  obtain ⟨Bν, hBνs, hBνsum, hBν⟩ := hB eps heS ν σ hν hσ (fun y => incFn F ν y / 3)
    (hGνm.div_const 3) (htest hνm)
  obtain ⟨Bσ, hBσs, hBσsum, hBσ⟩ := hB eps heS ν σ hν hσ (fun y => incFn F σ y / 3)
    (hGσm.div_const 3) (htest hσm)
  obtain ⟨BE, hBEs, -, hBE⟩ := hB eps heS ν σ hν hσ (expTest l) (measurable_expTest l)
    fun y hy => by rw [expTest, abs_of_pos (Real.exp_pos _)]; exact hExp y hy
  have hc3 : ∀ {α : ProbabilityMeasure ℝ} {B : ℕ → ℝ},
      (∀ z ∈ ball (0 : ℂ) rS, ∀ k, ‖cSurv eps ν σ z k (fun y => incFn F α y / 3)‖ ≤ B k) →
      ∀ z ∈ ball (0 : ℂ) rS, ∀ k, ‖cSurv eps ν σ z k (incFn F α)‖ ≤ 3 * B k := by
    intro α B h z hz k
    have e := cSurv_const_mul eps ν σ z k 3 (fun y => incFn F α y / 3)
    rw [show (fun s => 3 * (incFn F α s / 3)) = incFn F α from
      funext fun s => mul_div_cancel₀ _ three_ne_zero] at e
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact mul_le_mul_of_nonneg_left (h z hz k) (by norm_num)
  have hcν := hc3 hBν
  have hcσ := hc3 hBσ
  have h0S : (0 : ℂ) ∈ ball (0 : ℂ) rS := mem_ball_self hrS
  have hBν0 : ∀ k, 0 ≤ Bν k := fun k => (norm_nonneg _).trans (hBν 0 h0S k)
  have hBσ0 : ∀ k, 0 ≤ Bσ k := fun k => (norm_nonneg _).trans (hBσ 0 h0S k)
  set u : ℕ → ℝ := fun k => 6 * (Bν k + Bσ k) with hudef
  have hu : Summable u := (hBνs.add hBσs).mul_left 6
  have hΨ : ∀ k, ∀ z ∈ ball (0 : ℂ) r,
      ‖occTerm eps ν σ (incFn F ν) (incFn F σ) k z‖ ≤ u k := by
    intro k z hz
    have hz' : ‖z‖ ≤ r := (mem_ball_zero_iff.1 hz).le
    have hzS : z ∈ ball (0 : ℂ) rS := ball_subset_ball hrS' hz
    refine (norm_occTerm_le eps ν σ _ _ k hz').trans ?_
    have a := hcν z hzS k
    have b := hcσ z hzS k
    have ha0 := norm_nonneg (cSurv eps ν σ z k (incFn F ν))
    have hb0 := norm_nonneg (cSurv eps ν σ z k (incFn F σ))
    have hr1' : 1 + r ≤ 2 := by linarith
    calc (1 + r) * ‖cSurv eps ν σ z k (incFn F ν)‖ + r * ‖cSurv eps ν σ z k (incFn F σ)‖
        ≤ 2 * (3 * Bν k) + 1 * (3 * Bσ k) := by
          gcongr
    _ ≤ u k := by
          simp only [hudef]
          nlinarith [hBν0 k, hBσ0 k]
  have hdiff : ∀ k, DifferentiableOn ℂ (occTerm eps ν σ (incFn F ν) (incFn F σ) k)
      (ball (0 : ℂ) r) := fun k =>
    (differentiable_occTerm eps ν σ _ _ k).differentiableOn
  refine ⟨fun z => (F 0 : ℂ) + ∑' k, occTerm eps ν σ (incFn F ν) (incFn F σ) k z, ?_, ?_, ?_,
    ?_⟩
  · -- holomorphy
    exact (Complex.differentiableOn_tsum_of_summable_norm hu hdiff isOpen_ball
      fun k w hw => hΨ k w hw).const_add _
  · -- the bound on the disc
    intro z hz
    have h1 : ‖∑' k, occTerm eps ν σ (incFn F ν) (incFn F σ) k z‖ ≤ ∑' k, u k :=
      tsum_of_norm_bounded hu.hasSum fun k => hΨ k z hz
    have hF0 : ‖(F 0 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have := hFb' 0 le_rfl
      simpa using this
    have hsumu : ∑' k, u k ≤ 12 * (KS * eps ^ p) := by
      simp only [hudef]
      rw [tsum_mul_left, hBνs.tsum_add hBσs]
      linarith
    have hp1 : 1 ≤ eps ^ p := one_le_pow₀ heps1
    have hK0 : KS * eps ^ p ≤ max KS 0 * eps ^ p :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    calc ‖(F 0 : ℂ) + ∑' k, occTerm eps ν σ (incFn F ν) (incFn F σ) k z‖
        ≤ ‖(F 0 : ℂ)‖ + ‖∑' k, occTerm eps ν σ (incFn F ν) (incFn F σ) k z‖ := norm_add_le _ _
      _ ≤ 1 + 12 * (max KS 0 * eps ^ p) := by linarith
      _ ≤ (1 + 12 * max KS 0) * eps ^ p := by nlinarith [le_max_right KS 0]
      _ ≤ max (1 + 12 * max KS 0) CK * eps ^ p := by gcongr; exact le_max_left _ _
  · -- the real segment
    intro t ht0 htr
    have ht : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, by linarith⟩
    have htm : t ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨ht0, by linarith⟩
    obtain ⟨hfin, -, hexpc⟩ := hmix eps he₁ ν σ hν hσ t htm
    obtain ⟨hint, hle⟩ := hexpc γ hγ0.le (by linarith)
    have e1 : (fun g => Real.exp (γ * stopSum eps g / eps ^ 2)) =
        fun g => Real.exp (l * stopSum eps g) := funext fun g => by
      congr 1; have := hlγ 1 (stopSum eps g); simpa using this
    rw [e1] at hint hle
    have htB : (t : ℂ) ∈ ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      linarith
    have hsum : Summable fun k => occTerm eps ν σ (incFn F ν) (incFn F σ) k (t : ℂ) :=
      Summable.of_norm_bounded hu fun k => hΨ k _ htB
    have heq := occ_series_ofReal heps0.le hl0 hνm hσm hFm hFb' ht hfin hint hsum
    change ‖(F 0 : ℂ) + ∑' k, occTerm eps ν σ (incFn F ν) (incFn F σ) k (t : ℂ)‖ ≤ _
    rw [heq, Complex.norm_real]
    have hmixm := hνm.mix hσm ht
    have hb : ‖∫ g, F (stopSum eps g) ∂(iidLaw (mixPM ν σ t))‖ ≤
        ∫ g, Real.exp (l * stopSum eps g) ∂(iidLaw (mixPM ν σ t)) := by
      refine norm_integral_le_of_norm_le hint ?_
      filter_upwards [ae_pos_piLaw (ρ := fun _ => mixPM ν σ t) fun _ => hmixm.pos] with g hg
      rw [Real.norm_eq_abs]
      exact hFb' _ (rawAsm_stopSum_nonneg fun j => (hg j).le)
    exact hb.trans (hle.trans (le_max_right _ _))
  · -- the derivative at `0`
    have hD := Complex.hasSum_deriv_of_summable_norm hu hdiff isOpen_ball (fun k w hw => hΨ k w hw)
      (mem_ball_self hr0)
    have hdk : ∀ k, deriv (occTerm eps ν σ (incFn F ν) (incFn F σ) k) 0 =
        ((occDeriv eps ν σ (incFn F ν) (incFn F σ) k : ℝ) : ℂ) := fun k =>
      (hasDerivAt_occTerm_zero eps ν σ _ _ k).deriv
    simp_rw [hdk] at hD
    -- the column sums under `ν`
    have ht0m : (0 : ℝ) ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨le_rfl, (tMix_pos A θσ hθσ).le⟩
    obtain ⟨hfin0, htail0, hexp0⟩ := hmix eps he₁ ν σ hν hσ 0 ht0m
    rw [mixPM_zero] at hfin0 htail0 hexp0
    obtain ⟨hint2, -⟩ := hexp0 (2 * γ) (by positivity) hγM
    have hS2 : ∫⁻ g, ENNReal.ofReal (Real.exp (2 * (l * stopSum eps g))) ∂(iidLaw ν) ≠ ⊤ := by
      have h := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun g =>
        (Real.exp_pos (2 * γ * stopSum eps g / eps ^ 2)).le)).1 hint2.2
      refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) h)
      refine lintegral_congr fun g => ?_
      rw [hlγ 2 (stopSum eps g)]
    set c : ℝ := tailRate * (vlo / 2) with hcdef
    have hc0 : 0 < c := mul_pos tailRate_pos (by positivity)
    set κ : ℝ := c / (4 * eps ^ 2) with hκdef
    have hκ0 : 0 < κ := by positivity
    have htail' : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
        ENNReal.ofReal (72 / 71 * Real.exp (-c / eps ^ 2) ^ m) := by
      intro m
      refine (htail0 m).trans (le_of_eq ?_)
      rw [← Real.exp_nat_mul]
      congr 3
      ring
    have hκa : Real.exp (2 * κ) * Real.exp (-c / eps ^ 2) < 1 := by
      rw [← Real.exp_add, Real.exp_lt_one_iff, hκdef]
      have : 2 * (c / (4 * eps ^ 2)) + -c / eps ^ 2 = -(c / (2 * eps ^ 2)) := by
        field_simp; ring
      rw [this, neg_lt_zero]
      positivity
    have hT := lintegral_exp_toNat_le (P := iidLaw ν) (isStoppingRule_gapSegLen eps).measurable
      hfin0 (by norm_num) (Real.exp_pos _).le htail' (by positivity) hκa
    have hWν : WSummable eps l ν ν :=
      wSummable_self hl0 hνm hfin0 hκ0 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hT) hS2
    have hWσ : WSummable eps l ν σ := wSummable_sigma hWν hrS hBEs hBE
    have hR := hasSum_occDeriv hl0 hνm hσm hFm hFb' hWν hWσ
    have hC := Complex.hasSum_ofReal.2 hR
    rw [deriv_const_add]
    exact hD.unique hC

end

end PGM
