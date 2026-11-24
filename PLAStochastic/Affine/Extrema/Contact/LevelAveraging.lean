import PLAStochastic.Affine.Extrema.Contact.TestMeasure
import PLAStochastic.Affine.Extrema.Contact.LevelSupport

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory.Measure
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The actual marked layer is jointly AE measurable in both unscaled levels
and the Brownian sample path, including invalid level pairs where it vanishes. -/
theorem aemeasurable_levelOrderedContactTest (hB : IsBrownianReal B μ)
    (ν : Measure (ℝ × ℝ)) (e d : ℝ) {φ : ExtremaVector → ℝ} (hφ : Measurable φ) :
    AEMeasurable (fun p : Ω × (ℝ × ℝ) =>
      orderedContactTest φ B (-p.2.1) (p.2.2-p.2.1) e d p.1) (μ.prod ν) := by
  have hp : ∀ᵐ p ∂μ.prod ν, ∀ t : ℝ≥0, processPath B p.1 t=B t p.1 :=
    quasiMeasurePreserving_fst.ae (hB.cont.mono (fun ω hc t => processPath_apply_of_continuous hc t))
  have ht := aemeasurable_orderedContactTest_comp (α := Ω × (ℝ × ℝ))
    (B := fun t p => B t p.1) (f := fun p => processPath B p.1)
    (x := fun p => -p.2.1) (r := fun p => p.2.2-p.2.1) (e := fun _ => e) (d := fun _ => d)
    (aemeasurable_processPath hB).comp_fst hp (by fun_prop) (by fun_prop)
    aemeasurable_const aemeasurable_const hφ
  apply ht.congr
  exact Eventually.of_forall (fun p => orderedContactTest_congr_paths
    (B := fun t p => B t p.1) (C := B) (ω := p) (ξ := p.1) (fun _ => rfl)
    (-p.2.1) (p.2.2-p.2.1) e d φ)

/-- Fubini and the exact pathwise rectangle change of variables identify the
unscaled level average with the actual rescaled probability average. -/
theorem lintegral_levelOrderedContactTest_eq_rescaled (hB : IsBrownianReal B μ)
    {e d : ℝ} (he : 0 < e) (hd : 0 < d)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ) :
    (∫⁻ q : ℝ × ℝ, ∫⁻ ω, ENNReal.ofReal
      (orderedContactTest φ B (-q.1) (q.2-q.1) e d ω) ∂μ) /
        (ENNReal.ofReal e*ENNReal.ofReal d) =
      ∫⁻ p : Ω × (ℝ × ℝ),
        ENNReal.ofReal (rescaledOrderedContactTest φ B e d p.2.1 p.2.2 p.1)
          ∂μ.prod contactAveragingSquare := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let raw : Ω × (ℝ × ℝ) → ℝ := fun p => orderedContactTest φ B (-p.2.1) (p.2.2-p.2.1) e d p.1
  let res : Ω × (ℝ × ℝ) → ℝ := fun p => rescaledOrderedContactTest φ B e d p.2.1 p.2.2 p.1
  have hmraw : AEMeasurable raw (μ.prod volume) := aemeasurable_levelOrderedContactTest hB volume e d hφ
  have hmres : AEMeasurable res (μ.prod contactAveragingSquare) :=
    aemeasurable_rescaledOrderedContactTest hB contactAveragingSquare e d hφ
  have hinv : (ENNReal.ofReal e*ENNReal.ofReal d)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (mul_ne_zero (ENNReal.ofReal_pos.mpr he).ne' (ENNReal.ofReal_pos.mpr hd).ne')
  rw [←lintegral_prod_symm (fun p => ENNReal.ofReal (raw p)) hmraw.ennreal_ofReal,
    lintegral_prod (fun p => ENNReal.ofReal (raw p)) hmraw.ennreal_ofReal,
    div_eq_mul_inv,←lintegral_mul_const' _ _ hinv,
    lintegral_prod (fun p => ENNReal.ofReal (res p)) hmres.ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [hB.cont,hB.eval_zero_ae_eq_zero,
    hmraw.aestronglyMeasurable.prodMk_left,hmres.aestronglyMeasurable.prodMk_left] with ω hc hz hraw hres
  change (∫⁻ q : ℝ × ℝ, ENNReal.ofReal (raw (ω,q)) ∂volume.prod volume) *
    (ENNReal.ofReal e*ENNReal.ofReal d)⁻¹ =
      ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (res (ω,q)) ∂contactAveragingInterval.prod contactAveragingInterval
  rw [lintegral_prod (fun q : ℝ × ℝ => ENNReal.ofReal (raw (ω,q))) hraw.aemeasurable.ennreal_ofReal,
    lintegral_prod (fun q : ℝ × ℝ => ENNReal.ofReal (res (ω,q))) hres.aemeasurable.ennreal_ofReal]
  exact lintegral_orderedContactTest_normalized_eq_rescaled hc hz he hd φ

/-- The normalized full Lebesgue level average of the true contact observables
converges to the actual ordered extrema measure, for all bounded continuous tests. -/
theorem tendsto_lintegral_levelOrderedContactTest (hB : IsBrownianReal B μ)
    {E F : ℕ → ℝ} (hE : ∀ n, 0 < E n) (hF : ∀ n, 0 < F n)
    (hElim : Tendsto E atTop (𝓝 0)) (hFlim : Tendsto F atTop (𝓝 0))
    {φ : ExtremaVector → ℝ} (hφ : Continuous φ)
    {M : ℝ} (hM : ∀ p, ‖φ p‖ ≤ M) :
    Tendsto (fun n => (∫⁻ q : ℝ × ℝ, ∫⁻ ω, ENNReal.ofReal
      (orderedContactTest φ B (-q.1) (q.2-q.1) (E n) (F n) ω) ∂μ) /
        (ENNReal.ofReal (E n)*ENNReal.ofReal (F n))) atTop
      (𝓝 (∫⁻ p, ENNReal.ofReal (φ p) ∂brownianOrderedExtremaMeasure B μ)) := by
  simpa only [lintegral_levelOrderedContactTest_eq_rescaled hB (hE _) (hF _) hφ.measurable] using
    tendsto_lintegral_rescaledOrderedContactTest hB hE hF hElim hFlim hφ hM

end BrownianAffine
