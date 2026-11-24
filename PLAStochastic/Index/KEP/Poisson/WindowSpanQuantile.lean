import PLAStochastic.Index.KEP.Poisson.WindowSpanEvents
import PLAStochastic.Index.KEP.Poisson.PolynomialComparison
import PLAStochastic.Index.KEP.ReferenceScale.UniformSmallMoments
import PLAStochastic.ForMathlib.Probability.Hellinger.ExponentialQuantile
import PLAStochastic.Index.KEP.CountRoute.WindowChoice

/-!
# The original Poisson window has a fixed positive span quantile

The actual reference mean and exponential moment pay a fixed lower tail by
Paley-Zygmund. The proved uniform polynomial comparison transfers that mass
to every actual layer and physical anchor. The exact window-event inclusion
then gives the span-quantile premise of the original finite-sample bridge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Renyi
open scoped ENNReal unitInterval Nat

theorem kepPoisson_window_span_quantile {f : ℝ → ℝ} {A B flo fhi L : ℝ}
    (hf : DensityK f A B flo fhi L) :
    ∃ E c p0 R : ℝ, kepReferenceClassicalThreshold ≤ E ∧ 1 ≤ E ∧
      0 < c ∧ 0 < p0 ∧ 1 ≤ R ∧ 2 * c ≤ R ∧
      ∀ Bc : ℝ, R ≤ Bc →
        KepPoissonSpanQuantile (quantK f A B) E c p0 Bc 153 := by
  obtain ⟨thetaRef, eRef, hthetaRef, href⟩ := kepReference_uniform_small_exponential_moment
  let beta := thetaRef ^ 2 / 16
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  let eta := Real.sqrt beta / 2
  have heta : 0 < eta := div_pos (Real.sqrt_pos.mpr hbeta) (by norm_num)
  obtain ⟨_, _, _, _, hcomp⟩ := kepPoisson_polynomial_comparison (kepExtendedDensity_profile hf)
  obtain ⟨Rc, Ec, hRc, hEc, hEc1, hcomp⟩ := hcomp eta heta
  let c := flo / (4 * fhi)
  have hfhi : 0 < fhi := (kepExtendedDensity_profile hf).fhi_pos
  have hc : 0 < c := div_pos hf.pos (by positivity)
  let R := max Rc (max 1 (2 * c))
  have hR1 : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR2c : 2 * c ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  let E := max Ec eRef
  have hEcE : Ec ≤ E := le_max_left _ _
  refine ⟨E, c, beta / 4, R, hEc.trans hEcE, hEc1.trans hEcE, hc,
    by positivity, hR1, hR2c, ?_⟩
  intro Bc hBc eps heE ell hell M hMcut u hu0 hu1 p hpMass
  have hec : Ec ≤ eps := hEcE.trans heE
  have he1 : 1 ≤ eps := hEc1.trans hec
  have hethr : kepReferenceClassicalThreshold ≤ eps := hEc.trans hec
  have heps : 1 / 2 ≤ eps := (by norm_num : (1 / 2 : ℝ) ≤ 1).trans he1
  have hm4 := kepReferenceSpan_ge_four hethr hell
  have hm : 0 < kepReferenceSpan eps ell := by linarith
  have hBc1 : 1 ≤ Bc := hR1.trans hBc
  have hRcBc : Rc ≤ Bc := (le_max_left _ _).trans hBc
  have hpower : 1 ≤ eps ^ (153 : ℕ) := one_le_pow₀ he1
  have hMbound : Bc * eps ^ (153 : ℕ) * kepReferenceSpan eps ell ≤ M := by
    have hMcast : (⌈Bc * eps ^ (153 : ℝ) * kepReferenceSpan eps ell⌉₊ : ℝ) ≤ (M : ℝ) :=
      by exact_mod_cast hMcut
    have h := (Nat.le_ceil (Bc * eps ^ (153 : ℝ) * kepReferenceSpan eps ell)).trans
      hMcast
    simpa only [show (153 : ℝ) = (153 : ℕ) by norm_num, Real.rpow_natCast] using h
  have hprod : 1 ≤ Bc * eps ^ (153 : ℕ) := by
    simpa only [one_mul] using mul_le_mul hBc1 hpower (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ Bc)
  have hM : 0 < (M : ℝ) := by nlinarith
  have hMrc : Rc * eps ^ (153 : ℕ) * kepReferenceSpan eps ell ≤ M := by
    exact le_trans (by gcongr) hMbound
  have hMn : (M : ℝ) ≤ M / (1 - u) := by
    rw [le_div_iff₀ (sub_pos.mpr hu1)]
    nlinarith
  have h := hcomp eps hec (M / (1 - u)) ell (hMrc.trans hMn)
  let P := kepPoissonLayerMeasure (kepExtendedDensity_profile hf) eps
    (M / (1 - u)) (quantK f A B u) ell
  have hRef := href eps ((le_max_right _ _).trans heE) ell
  have hRefM := hRef.2.2 thetaRef hthetaRef.le le_rfl
  have hQLower : beta ≤ (kepReferenceLaw eps ell : Measure ℝ).real {z | (1 / 2 : ℝ) < z} := by
    simpa only [beta, show (8 : ℝ) * 2 = 16 by norm_num] using
      mean_one_exponential_lower_quantile (kepReferenceLaw eps ell : Measure ℝ)
        hthetaRef (by norm_num : (0 : ℝ) < 2) hRef.1 hRef.2.1 hRefM.1 hRefM.2
  have hPLower : beta / 4 ≤ P.real {z | (1 / 2 : ℝ) < z} :=
    measureHellinger_lower_event P (kepReferenceLaw eps ell : Measure ℝ)
      measurableSet_Ioi hbeta.le hQLower (h.2.2 (quantK f A B u)).2
  have hp : 0 < (p : ℝ) := by rw [hpMass]; positivity
  have hmass : (M : ℝ) * p = c * kepReferenceSpan eps ell := by
    rw [hpMass]
    field_simp
  have hthreshold : (fhi / flo) * ((M * p) / kepReferenceSpan eps ell) = 1 / 4 := by
    rw [hmass]
    dsimp [c]
    field_simp [hf.pos.ne']
  have hbounds := (kepPoissonWindow_span_event_bounds hf heps hell hm M p hM hp hu0 hu1
    (h.1 (quantK f A B u))).2
  rw [hthreshold] at hbounds
  exact hPLower.trans ((measureReal_mono (by
    intro z hz
    change (1 / 2 : ℝ) < z at hz
    change (1 / 4 : ℝ) < z
    linarith) (measure_ne_top _ _)).trans hbounds)

end

end PGM
