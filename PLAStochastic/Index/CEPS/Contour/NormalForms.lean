import PLAStochastic.Index.CEPS.Contour.Shift
import PLAStochastic.Index.CEPS.Normal.DividedDifference
import PLAStochastic.Index.CEPS.Normal.HalfLineRegular
import PLAStochastic.ForMathlib.Analysis.Complex.DividedDifferenceCongr

/-! # Exact contour transfer of the removable physical normal forms -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)
variable {σ : ℝ} (hσ : 0 < σ) (hσc : σ ≤ dom.c₀)

include hW hθ hD in
theorem normalG_shrink_eqOn {μ : ℝ} (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (l : ℂ) :
    EqOn ((cepsWHNormalData D θ ρW μ q).normalG ((dom.shrink σ hσ hσc).canonL ρW) μ q l)
      ((cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l)
      {ζ : ℂ | ζ.re < σ} := by
  intro ζ hζ
  unfold CepsNormalData.normalG
  rw [dom.shrink_canonL_eq hW hθ hD hσ hσc hμ hq hζ]

include hW hθ hD in
theorem normalRoots_mem_shrink {μ : ℝ} (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) :
    (cepsWHNormalData D θ ρW μ q).βp.re < σ ∧
      (cepsWHNormalData D θ ρW μ q).βm.re < σ := by
  have hμc : ‖(μ : ℂ)‖ ≤ (dom.shrink σ hσ hσc).μ₀ := by
    rwa [norm_real, Real.norm_eq_abs]
  obtain ⟨hp, hm⟩ := dom.norm_roots_le_of_shrink hW hθ hD hσ hσc hμc hq
  constructor
  · change (cepsRootPlus D θ ρW μ q).re < σ
    have hr := re_le_norm (cepsRootPlus D θ ρW μ q)
    linarith
  · change (cepsRootMinus D θ ρW μ q).re < σ
    have hr := re_le_norm (cepsRootMinus D θ ρW μ q)
    linarith

include hW hθ hD in
theorem regularBridge_shrink_eq {μ : ℝ} (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (l : ℂ) :
    (cepsWHNormalData D θ ρW μ q).regularBridge ((dom.shrink σ hσ hσc).canonL ρW) μ q l =
      (cepsWHNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l := by
  have hG := dom.normalG_shrink_eqOn hW hθ hD hσ hσc hμ hq l
  obtain ⟨hp, hm⟩ := dom.normalRoots_mem_shrink hW hθ hD hσ hσc hμ hq
  have hU : IsOpen {ζ : ℂ | ζ.re < σ} := isOpen_lt continuous_re continuous_const
  have hS := dslope_eq_of_eqOn hU hG hm hp
  unfold CepsNormalData.regularBridge
  rw [hG hp, hG hm, hS]

include hW hθ hD in
theorem regularEntrance_shrink_eq {μ : ℝ} (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (l : ℂ)
    {t : ℂ} (ht : t.re < σ) :
    (cepsWHNormalData D θ ρW μ q).regularEntrance ((dom.shrink σ hσ hσc).canonL ρW) μ q l t =
      (cepsWHNormalData D θ ρW μ q).regularEntrance (dom.canonL ρW) μ q l t := by
  have hG := dom.normalG_shrink_eqOn hW hθ hD hσ hσc hμ hq l
  obtain ⟨hp, hm⟩ := dom.normalRoots_mem_shrink hW hθ hD hσ hσc hμ hq
  have hU : IsOpen {ζ : ℂ | ζ.re < σ} := isOpen_lt continuous_re continuous_const
  have hS := dslope_eq_of_eqOn hU hG hm hp
  have hS2 := second_dslope_eq_of_eqOn hU hG hm hp ht
  unfold CepsNormalData.regularEntrance
  rw [dom.shrink_canonL_eq hW hθ hD hσ hσc hμ hq ht, hS2, hS]

include hW hθ hD in
theorem regularBridge_shrink_eventuallyEq {μ : ℝ} (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀)
    {q : ℂ} (hq : ‖q‖ < (dom.shrink σ hσ hσc).q₀) (l : ℂ) :
    (fun q' => (cepsWHNormalData D θ ρW μ q').regularBridge
      ((dom.shrink σ hσ hσc).canonL ρW) μ q' l) =ᶠ[𝓝 q]
    (fun q' => (cepsWHNormalData D θ ρW μ q').regularBridge (dom.canonL ρW) μ q' l) :=
  Filter.eventually_of_mem ((isOpen_lt continuous_norm continuous_const).mem_nhds hq)
    fun _ hq' => dom.regularBridge_shrink_eq hW hθ hD hσ hσc hμ hq'.le l

include hW hθ hD in
theorem regularBridge_deriv_shrink_eq {μ : ℝ} (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀)
    {q : ℂ} (hq : ‖q‖ < (dom.shrink σ hσ hσc).q₀) (l : ℂ) :
    deriv (fun q' => (cepsWHNormalData D θ ρW μ q').regularBridge
      ((dom.shrink σ hσ hσc).canonL ρW) μ q' l) q =
    deriv (fun q' => (cepsWHNormalData D θ ρW μ q').regularBridge (dom.canonL ρW) μ q' l) q :=
  (dom.regularBridge_shrink_eventuallyEq hW hθ hD hσ hσc hμ hq l).deriv_eq

include hW hθ hD in
theorem regularHalfEntrance_shrink_eq {μ : ℝ} (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) {t : ℂ} (ht : t.re < σ) :
    (cepsWHNormalData D θ ρW μ q).regularHalfEntrance ((dom.shrink σ hσ hσc).canonL ρW) μ q t =
      (cepsWHNormalData D θ ρW μ q).regularHalfEntrance (dom.canonL ρW) μ q t := by
  unfold CepsNormalData.regularHalfEntrance
  rw [dom.shrink_canonL_eq hW hθ hD hσ hσc hμ hq ht]

include hW hθ hD in
theorem halfBridge_shrink_eq {μ : ℝ} (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (l : ℂ) :
    (cepsWHNormalData D θ ρW μ q).halfBridge ((dom.shrink σ hσ hσc).canonL ρW) μ q l =
      (cepsWHNormalData D θ ρW μ q).halfBridge (dom.canonL ρW) μ q l := by
  have hp := (dom.normalRoots_mem_shrink hW hθ hD hσ hσc hμ hq).1
  unfold CepsNormalData.halfBridge
  rw [dom.shrink_canonL_eq hW hθ hD hσ hσc hμ hq hp]

include hW hθ hD in
theorem halfBridge_shrink_eventuallyEq {μ : ℝ} (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀)
    {q : ℂ} (hq : ‖q‖ < (dom.shrink σ hσ hσc).q₀) (l : ℂ) :
    (fun q' => (cepsWHNormalData D θ ρW μ q').halfBridge
      ((dom.shrink σ hσ hσc).canonL ρW) μ q' l) =ᶠ[𝓝 q]
    (fun q' => (cepsWHNormalData D θ ρW μ q').halfBridge (dom.canonL ρW) μ q' l) :=
  Filter.eventually_of_mem ((isOpen_lt continuous_norm continuous_const).mem_nhds hq)
    fun _ hq' => dom.halfBridge_shrink_eq hW hθ hD hσ hσc hμ hq'.le l

include hW hθ hD in
theorem halfBridge_deriv_shrink_eq {μ : ℝ} (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀)
    {q : ℂ} (hq : ‖q‖ < (dom.shrink σ hσ hσc).q₀) (l : ℂ) :
    deriv (fun q' => (cepsWHNormalData D θ ρW μ q').halfBridge
      ((dom.shrink σ hσ hσc).canonL ρW) μ q' l) q =
    deriv (fun q' => (cepsWHNormalData D θ ρW μ q').halfBridge (dom.canonL ρW) μ q' l) q :=
  (dom.halfBridge_shrink_eventuallyEq hW hθ hD hσ hσc hμ hq l).deriv_eq

end PGM.CepsCanonDomain
