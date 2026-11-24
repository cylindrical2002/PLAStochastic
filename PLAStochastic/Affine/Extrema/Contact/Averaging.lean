import PLAStochastic.Affine.Extrema.Contact.Rescaling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory.Measure
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Uniform probability on the open unit interval. -/
def contactAveragingInterval : Measure ℝ := volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure contactAveragingInterval := by
  constructor
  simp [contactAveragingInterval,Real.volume_Ioo]

def contactAveragingSquare : Measure (ℝ × ℝ) := contactAveragingInterval.prod contactAveragingInterval

instance : IsProbabilityMeasure contactAveragingSquare := by
  unfold contactAveragingSquare
  infer_instance

theorem contactAveragingSquare_mem_ae :
    ∀ᵐ p ∂contactAveragingSquare, p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 := by
  have hi : ∀ᵐ a ∂contactAveragingInterval, a ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  exact (quasiMeasurePreserving_fst.ae hi).and (quasiMeasurePreserving_snd.ae hi)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The observable is jointly AE measurable in the actual Brownian path and both
level-averaging coordinates, under any auxiliary measure. -/
theorem aemeasurable_rescaledOrderedContactTest (hB : IsBrownianReal B μ)
    (ν : Measure (ℝ × ℝ)) (e d : ℝ) {φ : ExtremaVector → ℝ} (hφ : Measurable φ) :
    AEMeasurable (fun p : Ω × (ℝ × ℝ) =>
      rescaledOrderedContactTest φ B e d p.2.1 p.2.2 p.1) (μ.prod ν) := by
  have hm : AEMeasurable (fun p : Ω × (ℝ × ℝ) =>
      slopeLower (unitPath (processPath B p.1) 1) 0) (μ.prod ν) :=
    (aemeasurable_brownianExtremaVector hB).fst.comp_fst
  have hM : AEMeasurable (fun p : Ω × (ℝ × ℝ) =>
      slopeUpper (unitPath (processPath B p.1) 1) 0) (μ.prod ν) :=
    (aemeasurable_brownianExtremaVector hB).snd.fst.comp_fst
  let l : Ω × (ℝ × ℝ) → ℝ := fun p => slopeLower (unitPath (processPath B p.1) 1) 0+e*p.2.1
  let h : Ω × (ℝ × ℝ) → ℝ := fun p => slopeUpper (unitPath (processPath B p.1) 1) 0-d*p.2.2
  have hl : AEMeasurable l (μ.prod ν) :=
    hm.add ((aemeasurable_const (b := e)).mul (measurable_fst.comp measurable_snd).aemeasurable)
  have hh : AEMeasurable h (μ.prod ν) :=
    hM.sub ((aemeasurable_const (b := d)).mul (measurable_snd.comp measurable_snd).aemeasurable)
  have hp : ∀ᵐ p ∂μ.prod ν, ∀ t : ℝ≥0, processPath B p.1 t=B t p.1 :=
    quasiMeasurePreserving_fst.ae (hB.cont.mono (fun ω hc t => processPath_apply_of_continuous hc t))
  have ht := aemeasurable_orderedContactTest_comp (α := Ω × (ℝ × ℝ))
    (B := fun t p => B t p.1) (f := fun p => processPath B p.1)
    (x := fun p => -l p) (r := fun p => h p-l p) (e := fun _ => e) (d := fun _ => d)
    (aemeasurable_processPath hB).comp_fst hp hl.neg (hh.sub hl)
    aemeasurable_const aemeasurable_const hφ
  apply ht.congr
  apply Eventually.of_forall
  intro p
  exact orderedContactTest_congr_paths (B := fun t p => B t p.1) (C := B)
    (ω := p) (ξ := p.1) (fun _ => rfl) (-l p) (h p-l p) e d φ

/-- One Brownian full-measure event supports the test limit for every interior
averaging coordinate and every continuous test at the actual extrema vector. -/
theorem brownian_rescaledOrderedContactTest_tendsto_ae (hB : IsBrownianReal B μ)
    {E F : ℕ → ℝ} (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n)
    (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ φ : ExtremaVector → ℝ, ContinuousAt φ (brownianExtremaVector B ω) →
      Tendsto (fun n => rescaledOrderedContactTest φ B (E n) (F n) a b ω) atTop
        (𝓝 (orderedExtremaTest φ B ω)) := by
  filter_upwards [hB.cont,hB.eval_zero_ae_eq_zero,
    brownian_upper_lower_differentiable_ae hB 0,
    brownianExtremaVector_ordered_support_ae hB] with ω hc h0 hd hs
  intro a ha b hb φ hφ
  have hm : slopeLower (unitPath (processPath B ω) 1) 0 < 0 :=
    hs.elim (fun h => h.1) (fun h => h.1)
  have hM : 0 < slopeUpper (unitPath (processPath B ω) 1) 0 :=
    hs.elim (fun h => h.2.1) (fun h => h.2.1)
  have hne : (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ) ≠
      (upperTime (unitPath (processPath B ω) 1) 0 : ℝ) := by
    rcases hs with hs | hs
    · exact ne_of_lt hs.2.2.2.2.2.1
    · exact (ne_of_lt hs.2.2.2.2.2.1).symm
  exact tendsto_rescaledOrderedContactTest hc h0 hd.2 hd.1 hne hm hM hE hF hElim hFlim ha hb hφ

/-- Actual probability integration of the rescaled contact layers converges to
the actual ordered five-variable extrema test, for every bounded continuous test.
No joint-density formula is used in this probabilistic convergence theorem. -/
theorem tendsto_integral_rescaledOrderedContactTest (hB : IsBrownianReal B μ)
    {E F : ℕ → ℝ} (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n)
    (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0))
    {φ : ExtremaVector → ℝ} (hφ : Continuous φ)
    {M : ℝ} (hM : ∀ p, ‖φ p‖ ≤ M) :
    Tendsto (fun n => ∫ p : Ω × (ℝ × ℝ),
      rescaledOrderedContactTest φ B (E n) (F n) p.2.1 p.2.2 p.1
        ∂μ.prod contactAveragingSquare) atTop
      (𝓝 (∫ ω, orderedExtremaTest φ B ω ∂μ)) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have ht := tendsto_integral_of_dominated_convergence (μ := μ.prod contactAveragingSquare)
    (fun _ => M)
    (fun n => (aemeasurable_rescaledOrderedContactTest hB contactAveragingSquare
      (E n) (F n) hφ.measurable).aestronglyMeasurable)
    (integrable_const M)
    (fun n => Eventually.of_forall (fun p => norm_orderedContactTest_le B _ _ _ _ p.1 hM))
    (f := fun p : Ω × (ℝ × ℝ) => orderedExtremaTest φ B p.1) ?_
  · simpa only [integral_fun_fst,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using ht
  · filter_upwards [quasiMeasurePreserving_fst.ae
      (brownian_rescaledOrderedContactTest_tendsto_ae hB hE hF hElim hFlim),
      quasiMeasurePreserving_snd.ae contactAveragingSquare_mem_ae] with p hp hu
    exact hp p.2.1 hu.1 p.2.2 hu.2 φ hφ.continuousAt

end BrownianAffine
