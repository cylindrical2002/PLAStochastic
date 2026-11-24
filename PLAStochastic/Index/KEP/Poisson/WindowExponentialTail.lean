import PLAStochastic.Index.KEP.Poisson.WindowSpanEvents
import PLAStochastic.Index.KEP.Poisson.PolynomialComparison
import PLAStochastic.Index.KEP.CountRoute.LocalWindowChoice
import Mathlib.Probability.Moments.Basic

/-!
# The original Poisson window block has an exponential tail

The fixed exponential moment of the actual normalized layer gap pays the
physical window-crossing event by Chernoff. The unconditional polynomial
comparison supplies both that moment and true completed-pivot finiteness,
at precisely the local cutoff needed by the original height reduction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Renyi
open scoped ENNReal unitInterval Nat

theorem kepPoissonWindow_exp_tail_of_moment {f : ℝ → ℝ} {A B flo fhi L eps u theta : ℝ}
    (hf : DensityK f A B flo fhi L) (heps : 1 / 2 ≤ eps) {ell : ℕ} (hell : 1 ≤ ell)
    (hm : 0 < kepReferenceSpan eps ell) (M : ℕ) (p : I)
    (hM : 0 < (M : ℝ)) (hp : 0 < (p : ℝ)) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (htheta : 0 < theta)
    (hfin : ∀ᵐ g ∂expSeqMeasure,
      kepPoissonPivot (kepExtendedDensity_profile hf) eps (M / (1 - u))
        (quantK f A B u) ell 1 g ≠ ⊤)
    (hi : Integrable (fun z => Real.exp (theta * z))
      (kepPoissonLayerMeasure (kepExtendedDensity_profile hf) eps (M / (1 - u))
        (quantK f A B u) ell))
    (hb : ∫ z, Real.exp (theta * z) ∂
      kepPoissonLayerMeasure (kepExtendedDensity_profile hf) eps (M / (1 - u))
        (quantK f A B u) ell ≤ 73) :
    (poissonWindow M p).real (tailEvent eps (quantK f A B) u ell) ≤
      73 * Real.exp (-((theta * flo / fhi) * (M * p / kepReferenceSpan eps ell))) := by
  have hbound := (kepPoissonWindow_span_event_bounds hf heps hell hm M p hM hp hu0 hu1 hfin).1
  have hcher := measure_ge_le_exp_mul_mgf (X := fun z : ℝ => z)
    ((flo / fhi) * (M * p / kepReferenceSpan eps ell)) htheta.le hi
  apply (hbound.trans hcher).trans
  change Real.exp (-theta * ((flo / fhi) * (M * p / kepReferenceSpan eps ell))) *
    (∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure (kepExtendedDensity_profile hf)
      eps (M / (1 - u)) (quantK f A B u) ell) ≤ _
  calc
    _ ≤ Real.exp (-theta * ((flo / fhi) * (M * p / kepReferenceSpan eps ell))) * 73 :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by
      have he : -theta * ((flo / fhi) * (M * p / kepReferenceSpan eps ell)) =
          -((theta * flo / fhi) * (M * p / kepReferenceSpan eps ell)) := by ring
      rw [he, mul_comm]

theorem kepPoisson_local_exponential_tail {f : ℝ → ℝ} {A B flo fhi L : ℝ}
    (hf : DensityK f A B flo fhi L) :
    ∃ E R c : ℝ, kepReferenceClassicalThreshold ≤ E ∧ 1 ≤ E ∧
      0 ≤ R ∧ 0 < c ∧
      KepPoissonLocalExpTail (quantK f A B) E R 153 73 c := by
  obtain ⟨theta, _, htheta, _, hcomp⟩ :=
    kepPoisson_polynomial_comparison (kepExtendedDensity_profile hf)
  obtain ⟨R, E, hR, hclass, hE1, hcomp⟩ := hcomp 1 (by norm_num)
  have hc : 0 < theta * flo / fhi :=
    div_pos (mul_pos htheta hf.pos) (kepExtendedDensity_profile hf).fhi_pos
  refine ⟨E, 2 * R + 2, theta * flo / fhi, hclass, hE1, by linarith, hc, ?_⟩
  intro eps heE ell hell M hcut u hu0 hu1 p hp _ _
  have he1 := hE1.trans heE
  have hthr := hclass.trans heE
  have heps : 1 / 2 ≤ eps := (by norm_num : (1 / 2 : ℝ) ≤ 1).trans he1
  have hm4 := kepReferenceSpan_ge_four hthr hell
  have hm : 0 < kepReferenceSpan eps ell := by linarith
  have hpow : 1 ≤ eps ^ (153 : ℕ) := one_le_pow₀ he1
  have hunit : 1 ≤ R * eps ^ (153 : ℕ) * kepReferenceSpan eps ell := by
    nlinarith [mul_le_mul hR hpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ R)]
  rw [show (153 : ℝ) = (153 : ℕ) by norm_num, Real.rpow_natCast] at hcut
  push_cast at hcut
  have hMcut : R * eps ^ (153 : ℕ) * kepReferenceSpan eps ell ≤ M := by
    have hepsm : 0 ≤ eps ^ (153 : ℕ) * kepReferenceSpan eps ell := by positivity
    nlinarith
  have hM : 0 < (M : ℝ) := zero_lt_one.trans_le (hunit.trans hMcut)
  have hrem : 0 < 1 - u := sub_pos.mpr hu1
  have hMn : (M : ℝ) ≤ M / (1 - u) := by
    rw [le_div_iff₀ hrem]
    nlinarith
  have h := hcomp eps heE (M / (1 - u)) ell (hMcut.trans hMn)
  exact kepPoissonWindow_exp_tail_of_moment hf heps hell hm M p hM hp hu0 hu1 htheta
    (h.1 (quantK f A B u)) (h.2.1 (quantK f A B u)).1 (h.2.1 (quantK f A B u)).2

end

end PGM
