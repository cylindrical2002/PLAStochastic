import PLAStochastic.Index.CEPS.Normal.NegativeDiscountDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # The original canonical definitions inherit the common negative extension -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_actual_regular_forms_eventuallyEq {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q t : ℂ} (hq : ‖q‖ < dom.q₀) (ht : ‖t‖ < dom.c₀ / 2) (l : ℂ) :
    (fun q' => (cepsNormalData D θ ρW μ q').regularEntrance (dom.canonL ρW) μ q' l t)
      =ᶠ[𝓝 q] (fun q' => (cepsWHNormalData D θ ρW μ q').regularEntrance
        (dom.canonL ρW) μ q' l t) ∧
    (fun q' => (cepsNormalData D θ ρW μ q').regularBridge (dom.canonL ρW) μ q' l)
      =ᶠ[𝓝 q] (fun q' => (cepsWHNormalData D θ ρW μ q').regularBridge
        (dom.canonL ρW) μ q' l) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have htA : t ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hqn : ∀ᶠ q' : ℂ in 𝓝 q, ‖q'‖ < dom.q₀ :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hq
  have he : ∀ᶠ q' : ℂ in 𝓝 q,
      (cepsNormalData D θ ρW μ q').regularEntrance (dom.canonL ρW) μ q' l t =
        (cepsWHNormalData D θ ρW μ q').regularEntrance (dom.canonL ρW) μ q' l t ∧
      (cepsNormalData D θ ρW μ q').regularBridge (dom.canonL ρW) μ q' l =
        (cepsWHNormalData D θ ρW μ q').regularBridge (dom.canonL ρW) μ q' l := by
    filter_upwards [hqn] with q' hq'
    have hd := cepsNormal_actual_regular_forms_eq dom hW hθ hD hμ' hq'.le
      (dom.canonL ρW) l htA
    exact ⟨hd.1.symm, hd.2.symm⟩
  exact ⟨he.mono (fun _ hx => hx.1), he.mono (fun _ hx => hx.2)⟩

include hW hθ hD in
theorem cepsNormalData_canonical_analyticOnNhd_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {t : ℂ} (ht : ‖t‖ < dom.c₀ / 2) {l : ℝ} (hl : dom.normalNegativeWidth ≤ l) :
    AnalyticOnNhd ℂ (fun q' => (cepsNormalData D θ ρW μ q').regularEntrance
      (dom.canonL ρW) μ q' l t)
        {q : ℂ | ‖q‖ < dom.q₀ ∧ -(dom.normalNegativeRadius / l ^ 2) < q.re} ∧
    AnalyticOnNhd ℂ (fun q' => (cepsNormalData D θ ρW μ q').regularBridge
      (dom.canonL ρW) μ q' l)
        {q : ℂ | ‖q‖ < dom.q₀ ∧ -(dom.normalNegativeRadius / l ^ 2) < q.re} := by
  have hdiff : ∀ q : ℂ, ‖q‖ < dom.q₀ → -(dom.normalNegativeRadius / l ^ 2) ≤ q.re →
      DifferentiableAt ℂ (fun q' => (cepsNormalData D θ ρW μ q').regularEntrance
        (dom.canonL ρW) μ q' l t) q ∧
      DifferentiableAt ℂ (fun q' => (cepsNormalData D θ ρW μ q').regularBridge
        (dom.canonL ρW) μ q' l) q := by
    intro q hq hre
    obtain ⟨he, hb⟩ := cepsNormal_actual_regular_forms_eventuallyEq dom hW hθ hD hμ hq ht l
    obtain ⟨hdE, hdB⟩ := cepsNormal_actual_holomorphicAt_negative dom hW hθ hD hμ hq ht hl hre
    exact ⟨hdE.congr_of_eventuallyEq he, hdB.congr_of_eventuallyEq hb⟩
  have hU : IsOpen {q : ℂ | ‖q‖ < dom.q₀ ∧
      -(dom.normalNegativeRadius / l ^ 2) < q.re} :=
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const continuous_re)
  have hE : DifferentiableOn ℂ (fun q' =>
      (cepsNormalData D θ ρW μ q').regularEntrance (dom.canonL ρW) μ q' l t)
      {q : ℂ | ‖q‖ < dom.q₀ ∧ -(dom.normalNegativeRadius / l ^ 2) < q.re} :=
    fun q hq => (hdiff q hq.1 hq.2.le).1.differentiableWithinAt
  have hB : DifferentiableOn ℂ (fun q' =>
      (cepsNormalData D θ ρW μ q').regularBridge (dom.canonL ρW) μ q' l)
      {q : ℂ | ‖q‖ < dom.q₀ ∧ -(dom.normalNegativeRadius / l ^ 2) < q.re} :=
    fun q hq => (hdiff q hq.1 hq.2.le).2.differentiableWithinAt
  exact ⟨hE.analyticOnNhd hU, hB.analyticOnNhd hU⟩

include hW hθ hD in
theorem cepsNormalData_canonical_discount_derivative_bounds {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2) {t : ℂ}
    (ht : ‖t‖ ≤ dom.c₀ / 4) (htre : 0 ≤ t.re) {l : ℝ}
    (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / (2 * l ^ 2)) ≤ q.re) (n : ℕ) :
    ‖iteratedDeriv n (fun q' => (cepsNormalData D θ ρW μ q').regularEntrance
      (dom.canonL ρW) μ q' l t) q‖ ≤
        n.factorial * (dom.normalNegativeEntranceBound * (1 + l) ^ 2) *
          (2 / dom.normalDiscountRadius) ^ n * l ^ (2 * n) ∧
    ‖iteratedDeriv n (fun q' => (cepsNormalData D θ ρW μ q').regularBridge
      (dom.canonL ρW) μ q' l) q‖ ≤
        n.factorial * (dom.normalNegativeBridgeBound * (dom.rmax + 1)) *
          (2 / dom.normalDiscountRadius) ^ n * l ^ (2 * n) := by
  obtain ⟨he, hb⟩ := cepsNormal_actual_regular_forms_eventuallyEq dom hW hθ hD hμ
    (show ‖q‖ < dom.q₀ by linarith [dom.q₀_pos]) (show ‖t‖ < dom.c₀ / 2 by
      linarith [dom.c₀_pos]) l
  rw [he.iteratedDeriv_eq n, hb.iteratedDeriv_eq n]
  exact cepsNormal_actual_discount_derivative_bounds dom hW hθ hD hμ hq ht htre hl hre n

end PGM
