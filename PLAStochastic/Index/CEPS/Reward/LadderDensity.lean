import PLAStochastic.Index.CEPS.Ident.Main
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.ExpRenewal
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex

/-! # The actual ascending ladder density and its Laplace transform

The bounded-test-function density identity first gives the transform in
the left half-plane. Analytic uniqueness extends it to the common
exponential-moment half-plane, so positive contour lines are also covered.
-/

noncomputable section
open MeasureTheory Set Metric Complex Filter Topology
open PGM.WienerHopf
namespace PGM

def cepsAscDensity (ρW : Measure ℝ) (fW : ℝ → ℝ) (μ : ℝ) (s : ℂ) : ℝ → ℂ :=
  ladderDensity (driftStep ρW μ) (fun y => fW (y - μ)) (Ioi 0) s

namespace CepsCanonDomain

def ladderEnvelope {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  D * Real.exp (θ * dom.μ₀) * stepGapConst D θ v

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsAscDensity_isExpDensity {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    IsExpDensity (cepsAscDensity ρW fW μ s) dom.ladderEnvelope θ := by
  have := hW.isProbabilityMeasure
  have hfm : Measurable (fun y => fW (y - μ)) := hW.measurable.comp (by fun_prop)
  refine ⟨?_, ?_, ?_⟩
  · exact (Measurable.tsum (fun n => measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_ladderKernel
        (fun y => hW.nonneg _) hfm n)))).indicator measurableSet_Ioi
  · intro x hx
    simp [cepsAscDensity, ladderDensity, show x ∉ Ioi (0 : ℝ) from not_lt.mpr hx]
  · intro x
    have he := norm_ladderDensity_asc_le_of_stepLaw hW hθ hD
      (CepsCanonDomain.v_pos hW hθ hD) hμ (dom.μ₀_le_drift hW hθ hD) hs x
    have hEnv : 0 ≤ dom.ladderEnvelope := by
      have := stepGapConst_pos hθ hD (CepsCanonDomain.v_pos hW hθ hD)
      unfold CepsCanonDomain.ladderEnvelope
      positivity
    exact he.trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left hEnv hs) (Real.exp_pos _).le)

include hW hθ hD in
/-- The actual density transform on both sides of the imaginary axis. -/
theorem cepsAscDensity_laplace_eq {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {s : ℂ} (hs : ‖s‖ ≤ 1)
    {ζ : ℂ} (hζ : ζ.re < θ / 2) :
    laplaceC (cepsAscDensity ρW fW μ s) ζ = ascTransform (driftStep ρW μ) s ζ := by
  have := hW.isProbabilityMeasure
  have hg := cepsAscDensity_isExpDensity dom hW hθ hD hμ hs
  have hop : IsOpen {z : ℂ | z.re < θ / 2} := isOpen_lt continuous_re continuous_const
  have hf := ((differentiableOn_laplaceC hg).mono
    (show {z : ℂ | z.re < θ / 2} ⊆ {z : ℂ | z.re < θ} by
      intro z hz; dsimp at hz ⊢; linarith)).analyticOnNhd hop
  have ha := (dom.differentiableOn_asc hW hθ hD hμ hs).analyticOnNhd hop
  have he : laplaceC (cepsAscDensity ρW fW μ s) =ᶠ[𝓝 (-1 : ℂ)]
      fun z => ascTransform (driftStep ρW μ) s z := by
    filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds
      (show (-1 : ℂ).re < 0 by norm_num)] with z hz
    have h := entryTransform_eq_integral_ladderDensity (ρ := driftStep ρW μ)
      measurableSet_Ioi (fun y => hW.nonneg _)
      (hW.measurable.comp (show Measurable (fun y : ℝ => y - μ) by fun_prop))
      (driftStep_eq_withDensity hW μ) hs
      (fun x hx => mul_nonpos_of_nonpos_of_nonneg hz.le hx.le)
    rw [ascTransform, h, laplaceC]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  exact hf.eqOn_of_preconnected_of_eventuallyEq ha
    (convex_halfSpace_re_lt _).isPreconnected
    (show (-1 : ℂ).re < θ / 2 by norm_num; linarith) he hζ

include hW in
theorem cepsAscDensity_one_eq_norm (μ x : ℝ) :
    cepsAscDensity ρW fW μ 1 x = (‖cepsAscDensity ρW fW μ 1 x‖ : ℂ) := by
  have := hW.isProbabilityMeasure
  unfold cepsAscDensity
  rw [ladderDensity_one_eq]
  have hn : 0 ≤ (Ioi (0 : ℝ)).indicator
      (fun h => ∑' n, ladderKernel (driftStep ρW μ) (fun y => fW (y - μ)) (Ioi 0) n h) x :=
    indicator_nonneg (fun _ _ => tsum_nonneg fun n => ladderKernel_nonneg
      (fun y => hW.nonneg _) n _) _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]

include hW hθ hD in
theorem cepsAscDensity_weight_integrable {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {s : ℂ} (hs : ‖s‖ ≤ 1) {a : ℝ} (ha : a < θ) :
    Integrable (fun x => Real.exp (a * x) * ‖cepsAscDensity ρW fW μ s x‖) := by
  have hg := cepsAscDensity_isExpDensity dom hW hθ hD hμ hs
  have hIo : IntegrableOn (fun x : ℝ => dom.ladderEnvelope * Real.exp ((a - θ) * x))
      (Ioi 0) := (integrableOn_exp_mul_Ioi (a := a - θ) (by linarith) 0).const_mul
        dom.ladderEnvelope
  have hI := hIo.integrable_indicator measurableSet_Ioi
  refine hI.mono' ((by fun_prop : Measurable (fun x : ℝ => Real.exp (a * x))).mul
    hg.measurable.norm).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    calc
      _ ≤ Real.exp (a * x) * (dom.ladderEnvelope * Real.exp (-θ * x)) :=
        mul_le_mul_of_nonneg_left (hg.norm_le x) (Real.exp_pos _).le
      _ = _ := by rw [mul_comm, mul_assoc, ← Real.exp_add]; congr 2; ring
  · rw [hg.eq_zero_of_nonpos x (not_lt.mp hx), norm_zero, mul_zero,
      indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]

include hW hθ hD in
/-- The strictly contracting left-line mass is paid by the actual ladder gap. -/
theorem cepsAscDensity_weight_mass_lt {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {s : ℂ} (hs : ‖s‖ ≤ 1) {c : ℝ} (hc : 0 < c) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-c * x) * ‖cepsAscDensity ρW fW μ s x‖) < 1 := by
  have := hW.isProbabilityMeasure
  have hdom : ∀ x, ‖cepsAscDensity ρW fW μ s x‖ ≤ ‖cepsAscDensity ρW fW μ 1 x‖ := by
    intro x
    have he := norm_ladderDensity_asc_le_one_of_stepLaw hW hθ hD
      (CepsCanonDomain.v_pos hW hθ hD) hμ (dom.μ₀_le_drift hW hθ hD) hs x
    exact he.trans (mul_le_of_le_one_left (norm_nonneg _) hs)
  have hi := cepsAscDensity_weight_integrable dom hW hθ hD hμ (s := 1) (by simp)
    (a := -c) (by linarith)
  have he : (∫ x, Real.exp (-c * x) * ‖cepsAscDensity ρW fW μ 1 x‖) =
      expEntryMass (driftStep ρW μ) (Ioi 0) (-c) := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    calc
      _ = laplaceC (cepsAscDensity ρW fW μ 1) (-c) := by
        unfold laplaceC
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simpa only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg] using
          congrArg (fun z : ℂ => cexp (-(c : ℂ) * x) * z)
            (cepsAscDensity_one_eq_norm hW μ x).symm
      _ = ascTransform (driftStep ρW μ) 1 (-c) :=
        cepsAscDensity_laplace_eq dom hW hθ hD hμ (by simp) (by simp; linarith)
      _ = _ := by simpa only [ascTransform, ofReal_neg] using
        (ofReal_expEntryMass (ρ := driftStep ρW μ) (Ioi 0) (-c)).symm
  have hgap := expEntryMass_Ioi_lt_one (ρ := driftStep ρW μ) hc
    (dom.driftStep_strip hW hθ hD hμ).2.2.2
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (-c * x) * ‖cepsAscDensity ρW fW μ 1 x‖) :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (hdom x) (Real.exp_pos _).le)
    _ = ENNReal.ofReal (expEntryMass (driftStep ρW μ) (Ioi 0) (-c)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity), he]
    _ < 1 := by simpa using (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hgap

end PGM
