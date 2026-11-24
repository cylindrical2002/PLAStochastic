import PLAStochastic.Index.KEP.Poisson.WindowExponentialTail
import PLAStochastic.Index.KEP.Poisson.WindowSpanQuantile
import PLAStochastic.Index.KEP.Poisson.WindowQuantileParameters
import PLAStochastic.Index.KEP.ReferenceScale.LargeLayerSpan
import PLAStochastic.Index.KEP.CountRoute.LargeScaleQuantile

/-!
# Unconditional additive endpoint height for the original general Model K

The actual nonhomogeneous Poisson layer comparison, original arrival-window
law, exponential block tail and positive span quantile pay both finite-sample
window inputs. The conclusion keeps the original density and iid hypotheses,
every sufficiently large epsilon, every sample size at least two and the
exact universal compression denominator gepC.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem H_K_EP_additive_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}
    (hf : DensityK f A B fmin fmax Lf) {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |(∫ omega, (epHeight eps (kKeys X n omega) n : ℝ) ∂P) -
        Real.log n / Real.log (gepC eps)| ≤ K := by
  obtain ⟨Eq, c, p0, Rq, hEq, hEq1, hc, hp0, hRq, _, hS⟩ :=
    kepPoisson_window_span_quantile hf
  obtain ⟨a, p, Bc, N, ha, hac, hp, hBcRq, hBc2, _, hpar⟩ :=
    kepPoisson_quantile_parameters hc hp0 Rq
  obtain ⟨En, _, _, hscale⟩ := kepReferenceSpan_large_layer_lower N
  obtain ⟨Et, Rt, ct, _, _, _, hct, hT⟩ := kepPoisson_local_exponential_tail hf
  let E := max Eq (max Et En)
  have hEqE : Eq ≤ E := le_max_left _ _
  have hEtE : Et ≤ E := (le_max_left _ _).trans (le_max_right _ _)
  have hEnE : En ≤ E := (le_max_right _ _).trans (le_max_right _ _)
  have hEClass : kepReferenceClassicalThreshold ≤ E := hEq.trans hEqE
  have hE1 : 1 ≤ E := hEq1.trans hEqE
  have hS' : KepPoissonSpanQuantile (quantK f A B) E c p0 Bc 153 := by
    intro eps heps ell hell m hm u hu0 hu1 q hq
    exact hS Bc hBcRq eps (hEqE.trans heps) ell hell m hm u hu0 hu1 q hq
  have hQ : KepPoissonQuantile (quantK f A B) E a p Bc 153 :=
    kepPoissonQuantile_of_spanQuantile_large_scale hEClass ha hac (by norm_num) hBc2
      (fun eps heps ell hell => hscale eps (hEnE.trans heps) ell hell) hpar hS'
  have hT' : KepPoissonLocalExpTail (quantK f A B) E Rt 153 73 ct := by
    intro eps heps ell hell m hm u hu0 hu1 q hq0 hqhalf hmass
    exact hT eps (hEtE.trans heps) ell hell m hm u hu0 hu1 q hq0 hqhalf hmass
  have htail := kepPoissonTail_of_localExpTail hEClass (by norm_num : (0 : ℝ) ≤ 153)
    (by norm_num : (0 : ℝ) ≤ 73) hct hT'
  exact H_EP_additive_kKeys_of_poissonWindow hf hXm hX hind
    ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans hE1) ha hp
    (zero_le_one.trans (hRq.trans hBcRq)) (by norm_num) hQ
    ((by norm_num : (1 : ℝ) ≤ 8).trans (le_max_left 8 Rt))
    (by norm_num) (by positivity) htail

theorem H_K_EP_additive {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}
    (hf : DensityK f A B fmin fmax Lf) {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |(∫ omega, (epHeight eps (kKeys X n omega) n : ℝ) ∂P) -
        Real.log n / Real.log (gepC eps)| ≤ K := by
  let : IsProbabilityMeasure (densityLaw f A B) := isProbabilityMeasure_densityLaw hf
  let : IsProbabilityMeasure P := (hX 0).isProbabilityMeasure
  let Y : ℕ → Ω → ℝ := fun i => (hX i).aemeasurable.mk (X i)
  have hYm (i : ℕ) : Measurable (Y i) := (hX i).aemeasurable.measurable_mk
  have heq (i : ℕ) : X i =ᵐ[P] Y i := (hX i).aemeasurable.ae_eq_mk
  have hYlaw (i : ℕ) : HasLaw (Y i) (densityLaw f A B) P :=
    (hX i).congr (Filter.EventuallyEq.symm (heq i))
  have hYind : iIndepFun Y P := hind.congr heq
  obtain ⟨eps0, K, hK⟩ := H_K_EP_additive_measurable hf hYm hYlaw hYind
  refine ⟨eps0, K, ?_⟩
  intro eps heps n hn
  have hi : (∫ omega, (epHeight eps (kKeys X n omega) n : ℝ) ∂P) =
      ∫ omega, (epHeight eps (kKeys Y n omega) n : ℝ) ∂P := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr heq] with omega homega
    have hs : (fun i : Fin n => X i omega) = (fun i : Fin n => Y i omega) := by
      funext i
      exact homega i
    simp only [kKeys, hs]
  rw [hi]
  exact hK eps heps n hn

end

end PGM
