import PLAStochastic.Index.KEP.ReferenceScale.ActualBoundedConeTransfer
import PLAStochastic.Index.KEP.ReferenceScale.PrefixConvolution
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Genuine bounded C2 tests for the output convolution increments

Both derivatives of the true probability convolution are obtained under its
original integral with a global bounded derivative. The physical prefix test
is the convolution increment itself, so no derivative-series Fubini exchange
or shifted support restriction is needed later.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

theorem kep_bounded_convolution_hasDerivAt (nu : ProbabilityMeasure ℝ)
    {phi phi' : ℝ → ℝ} (hphi : Measurable phi) (hphi' : Measurable phi')
    (hdphi : ∀ s, HasDerivAt phi (phi' s) s) {M : ℝ}
    (hb : ∀ t, |phi t| ≤ M ∧ |phi' t| ≤ M) (s : ℝ) :
    HasDerivAt (fun t => ∫ x, phi (t + x) ∂(nu : Measure ℝ))
      (∫ x, phi' (s + x) ∂(nu : Measure ℝ)) s := by
  have hi : Integrable (fun x => phi (s + x)) (nu : Measure ℝ) :=
    (integrable_const M).mono' (hphi.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using (hb (s + x)).1)
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x : ℝ => phi (t + x)) (F' := fun t x : ℝ => phi' (t + x))
    (bound := fun _ : ℝ => M) (s := univ) (μ := (nu : Measure ℝ))
    (by exact Filter.univ_mem)
    (Filter.Eventually.of_forall fun _ => (hphi.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
    hi (hphi'.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    (ae_of_all _ fun x t _ => by simpa only [Real.norm_eq_abs] using (hb (t + x)).2)
    (integrable_const M)
    (ae_of_all _ fun x t _ => by
      simpa only [Function.comp_def, id_eq, mul_one] using
        (hdphi (t + x)).comp t ((hasDerivAt_id t).add_const x))
  exact hh.2

def kepConvolutionTest (nu : ProbabilityMeasure ℝ) (phi : ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫ x, phi (s + x) ∂(nu : Measure ℝ)) - phi s

theorem kepConvolutionTest_C2 (nu : ProbabilityMeasure ℝ) {phi phi' phi'' : ℝ → ℝ}
    (hdphi : ∀ s, HasDerivAt phi (phi' s) s) (hddphi : ∀ s, HasDerivAt phi' (phi'' s) s)
    (hcphi'' : Continuous phi'') {M : ℝ}
    (hb : ∀ t, |phi t| ≤ M ∧ |phi' t| ≤ M ∧ |phi'' t| ≤ M) :
    (∀ s, HasDerivAt (kepConvolutionTest nu phi) (kepConvolutionTest nu phi' s) s) ∧
      (∀ s, HasDerivAt (kepConvolutionTest nu phi') (kepConvolutionTest nu phi'' s) s) ∧
      Continuous (kepConvolutionTest nu phi'') ∧
      (∀ s, |kepConvolutionTest nu phi s| ≤ 2 * M ∧
        |kepConvolutionTest nu phi' s| ≤ 2 * M ∧ |kepConvolutionTest nu phi'' s| ≤ 2 * M) := by
  have hcphi := continuous_iff_continuousAt.mpr fun s => (hdphi s).continuousAt
  have hcphi' := continuous_iff_continuousAt.mpr fun s => (hddphi s).continuousAt
  have h1 := fun s => (kep_bounded_convolution_hasDerivAt nu hcphi.measurable hcphi'.measurable
    hdphi (fun t => ⟨(hb t).1, (hb t).2.1⟩) s).sub (hdphi s)
  have h2 := fun s => (kep_bounded_convolution_hasDerivAt nu hcphi'.measurable hcphi''.measurable
    hddphi (fun t => (hb t).2) s).sub (hddphi s)
  have hconv : Continuous (fun s => ∫ x, phi'' (s + x) ∂(nu : Measure ℝ)) := by
    apply continuous_of_dominated (F := fun s x : ℝ => phi'' (s + x)) (μ := (nu : Measure ℝ))
      (bound := fun _ : ℝ => M) (fun s => (hcphi''.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
      (fun s => ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using (hb (s + x)).2.2)
      (integrable_const M)
      (ae_of_all _ fun x => hcphi''.comp (continuous_id.add continuous_const))
  have hbudget (psi : ℝ → ℝ) (hm : Measurable psi) (hbound : ∀ t, |psi t| ≤ M) (s : ℝ) :
      |kepConvolutionTest nu psi s| ≤ 2 * M := by
    have hi : Integrable (fun x => psi (s + x)) (nu : Measure ℝ) :=
      (integrable_const M).mono' (hm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
        (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound (s + x))
    have hbI : |∫ x, psi (s + x) ∂(nu : Measure ℝ)| ≤ M := by
      apply (show |∫ x, psi (s + x) ∂(nu : Measure ℝ)| ≤ ∫ x, |psi (s + x)| ∂(nu : Measure ℝ) from
        by simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := (nu : Measure ℝ)) (fun x : ℝ => psi (s + x))).trans
      have hh := integral_mono hi.abs (integrable_const M) (fun x => hbound (s + x))
      simpa using hh
    exact (abs_sub _ _).trans ((add_le_add hbI (hbound s)).trans_eq (by ring))
  refine ⟨h1, h2, hconv.sub hcphi'', ?_⟩
  intro s
  exact ⟨hbudget phi hcphi.measurable (fun t => (hb t).1) s,
    hbudget phi' hcphi'.measurable (fun t => (hb t).2.1) s,
    hbudget phi'' hcphi''.measurable (fun t => (hb t).2.2) s⟩

end

end PGM
