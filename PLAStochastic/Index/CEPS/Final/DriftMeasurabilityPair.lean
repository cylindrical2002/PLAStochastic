import PLAStochastic.Index.CEPS.Final.DriftMeasurabilityFactors
import PLAStochastic.Index.CEPS.Final.KernelComplexForm

/-! # Drift measurability of the complex subtracted pair and its scale coefficients

The complete and half pairs contain the frequency derivative of the bridge. For each fixed
complex jet vector, frequency and scale, one measurable function of the drift agrees with the
subtracted pair at every drift where the bridge (and, on `1 ≤ lam`, the half bridge) is
differentiable in the frequency. Scale coefficients at `0` are then measurable on the drifts where
the pair is holomorphic in the scale on a disc and those frequency derivatives exist there.
-/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

/-- One measurable function of the drift agrees with the subtracted pair wherever the frequency
derivatives in it are genuine. -/
theorem cepsComplexKernelSubtractedPairJetModel_exists_measurable_drift (p : ℕ → ℂ) (N : ℕ)
    (z b : ℂ) : ∃ g : ℝ → ℂ, Measurable g ∧ ∀ lam : ℝ,
      DifferentiableAt ℂ (fun w => cepsComplexKernelBridgeJetModel p N lam w b) z →
      (1 ≤ lam → DifferentiableAt ℂ (fun w => cepsComplexKernelHalfBridgeJetModel p N lam w b) z) →
        g lam = cepsComplexKernelSubtractedPairJetModel p N lam z b := by
  obtain ⟨D, hD, hDe⟩ := exists_measurable_eq_deriv_param_const
    (f := fun lam w => cepsComplexKernelBridgeJetModel p N lam w b) (z := z)
    fun w => measurable_cepsComplexKernelBridgeJetModel p N measurable_id measurable_const
      measurable_const
  obtain ⟨H, hH, hHe⟩ := exists_measurable_eq_deriv_param_const
    (f := fun lam w => cepsComplexKernelHalfBridgeJetModel p N lam w b) (z := z)
    fun w => measurable_cepsComplexKernelHalfBridgeJetModel p N measurable_id measurable_const
      measurable_const
  have hl : Measurable fun lam : ℝ => (lam : ℂ) := Complex.measurable_ofReal
  have hB := measurable_cepsComplexKernelBridgeJetModel p N measurable_id
    (measurable_const (a := z)) (measurable_const (a := b))
  have hA := measurable_cepsComplexKernelEntranceJetModel p N measurable_id
    (measurable_const (a := z)) (measurable_const (a := b))
  have hHB := measurable_cepsComplexKernelHalfBridgeJetModel p N measurable_id
    (measurable_const (a := z)) (measurable_const (a := b))
  have hHA := measurable_cepsComplexKernelHalfEntranceJetModel p N measurable_id
    (measurable_const (a := z)) (measurable_const (a := b))
  have hP : Measurable fun lam : ℝ =>
      exp ((b * z) * (1 + b * lam)) * (cepsComplexKernelEntranceJetModel p N lam z b) ^ 2 *
        (-(1 / (1 + b * lam)) * D lam - b * cepsComplexKernelBridgeJetModel p N lam z b) := by
    simp only [id_eq] at hB hA
    fun_prop
  have hQ : Measurable fun lam : ℝ =>
      exp ((b * z) * (1 + b * lam)) * (cepsComplexKernelHalfEntranceJetModel p N lam z b) ^ 2 *
        (-(1 / (1 + b * lam)) * H lam - b * cepsComplexKernelHalfBridgeJetModel p N lam z b) := by
    simp only [id_eq] at hHB hHA
    fun_prop
  classical
  refine ⟨fun lam => (exp ((b * z) * (1 + b * lam)) *
      (cepsComplexKernelEntranceJetModel p N lam z b) ^ 2 *
        (-(1 / (1 + b * lam)) * D lam - b * cepsComplexKernelBridgeJetModel p N lam z b)) -
      if 1 ≤ lam then exp ((b * z) * (1 + b * lam)) *
        (cepsComplexKernelHalfEntranceJetModel p N lam z b) ^ 2 *
          (-(1 / (1 + b * lam)) * H lam - b * cepsComplexKernelHalfBridgeJetModel p N lam z b)
      else 0, hP.sub (Measurable.ite measurableSet_Ici hQ measurable_const), ?_⟩
  intro lam hBd hHd
  simp only [cepsComplexKernelSubtractedPairJetModel, cepsComplexKernelPairJetModel,
    cepsComplexKernelHalfPairJetModel, hDe lam hBd]
  by_cases h1 : 1 ≤ lam
  · simp only [if_pos h1, hHe lam (hHd h1)]
  · simp only [if_neg h1]

/-- **(Q2)** On a measurable drift set where the bridge, and on `1 ≤ lam` the half bridge, are
differentiable in the frequency at `z`, the subtracted pair is a.e. strongly measurable in the
drift. -/
theorem cepsComplexKernelSubtractedPairJetModel_aestronglyMeasurable_drift {d N : ℕ}
    (q : Fin d → ℂ) (z h : ℂ) {S : Set ℝ} (hS : MeasurableSet S)
    (hB : ∀ lam ∈ S, DifferentiableAt ℂ
      (fun w => cepsComplexKernelBridgeJetModel (cepsComplexJetPad d q) N lam w h) z)
    (hH : ∀ lam ∈ S, 1 ≤ lam → DifferentiableAt ℂ
      (fun w => cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d q) N lam w h) z) :
    AEStronglyMeasurable
      (fun lam => cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z h)
      (volume.restrict S) := by
  obtain ⟨g, hg, hge⟩ :=
    cepsComplexKernelSubtractedPairJetModel_exists_measurable_drift (cepsComplexJetPad d q) N z h
  refine hg.aestronglyMeasurable.congr ?_
  exact ae_restrict_of_forall_mem hS fun lam hlam => hge lam (hB lam hlam) (hH lam hlam)

/-- Measure-general form of (Q2): almost-everywhere frequency differentiability suffices. -/
theorem cepsComplexKernelSubtractedPairJetModel_aestronglyMeasurable_of_ae {d N : ℕ}
    (q : Fin d → ℂ) (z h : ℂ) {μ : Measure ℝ}
    (hgood : ∀ᵐ lam ∂μ, DifferentiableAt ℂ
      (fun w => cepsComplexKernelBridgeJetModel (cepsComplexJetPad d q) N lam w h) z ∧
      (1 ≤ lam → DifferentiableAt ℂ
        (fun w => cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d q) N lam w h) z)) :
    AEStronglyMeasurable
      (fun lam => cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z h) μ := by
  obtain ⟨g, hg, hge⟩ :=
    cepsComplexKernelSubtractedPairJetModel_exists_measurable_drift (cepsComplexJetPad d q) N z h
  exact hg.aestronglyMeasurable.congr (hgood.mono fun lam hl => hge lam hl.1 hl.2)

/-- The genuine-scale-disc condition at one drift: the subtracted pair is holomorphic in the
scale on `ball 0 r`, and its frequency derivatives exist at every scale in that disc. -/
def CepsPairDriftScaleDisc (d N : ℕ) (q : Fin d → ℂ) (z : ℂ) (lam r : ℝ) : Prop :=
  0 < r ∧
  DifferentiableOn ℂ
    (fun b => cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z b)
    (ball 0 r) ∧
  (∀ b ∈ ball (0 : ℂ) r, DifferentiableAt ℂ
    (fun w => cepsComplexKernelBridgeJetModel (cepsComplexJetPad d q) N lam w b) z) ∧
  (1 ≤ lam → ∀ b ∈ ball (0 : ℂ) r, DifferentiableAt ℂ
    (fun w => cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d q) N lam w b) z)

/-- One measurable function of the drift agrees with every scale coefficient of the subtracted
pair at each drift admitting a genuine scale disc. -/
theorem cepsKernelPairCoeffC_exists_measurable_drift (d N n : ℕ) (q : Fin d → ℂ) (z : ℂ) :
    ∃ c : ℝ → ℂ, Measurable c ∧ ∀ lam r : ℝ, CepsPairDriftScaleDisc d N q z lam r →
      c lam = cepsKernelPairCoeffC d N n q lam z := by
  have hs (i : ℕ) := cepsComplexKernelSubtractedPairJetModel_exists_measurable_drift
    (cepsComplexJetPad d q) N z ((i : ℂ) + 1)⁻¹
  choose g hg hge using hs
  obtain ⟨c, hc, hce⟩ := exists_measurable_eq_taylorCoefficient_of_differentiableOn
    (F := fun lam b => cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z b)
    hg n
  refine ⟨c, hc, fun lam r ⟨hr, hd, hB, hH⟩ => hce lam r hr hd ?_⟩
  filter_upwards [tendsto_complex_inv_succ.eventually (ball_mem_nhds (0 : ℂ) hr)] with i hi
  exact hge i lam (hB _ hi) fun h1 => hH h1 _ hi

/-- Scale coefficients are a.e. strongly measurable in the drift for every measure under which
almost every drift admits a genuine scale disc. -/
theorem cepsKernelPairCoeffC_aestronglyMeasurable_of_ae {d N : ℕ} (n : ℕ) (q : Fin d → ℂ)
    (z : ℂ) {μ : Measure ℝ} (hgood : ∀ᵐ lam ∂μ, ∃ r : ℝ, CepsPairDriftScaleDisc d N q z lam r) :
    AEStronglyMeasurable (fun lam => cepsKernelPairCoeffC d N n q lam z) μ := by
  obtain ⟨c, hc, hce⟩ := cepsKernelPairCoeffC_exists_measurable_drift d N n q z
  exact hc.aestronglyMeasurable.congr (hgood.mono fun lam ⟨r, hr⟩ => hce lam r hr)

/-- **(Q3)** On a measurable drift set with positive scale radii `r lam` on which the subtracted
pair is holomorphic in the scale and the frequency-differentiability hypotheses of (Q2) hold at
every scale of the disc, every scale coefficient is a.e. strongly measurable in the drift. -/
theorem cepsKernelPairCoeffC_aestronglyMeasurable_drift {d N : ℕ} (n : ℕ) (q : Fin d → ℂ)
    (z : ℂ) {S : Set ℝ} (hS : MeasurableSet S) (r : ℝ → ℝ) (hr : ∀ lam ∈ S, 0 < r lam)
    (hP : ∀ lam ∈ S, DifferentiableOn ℂ
      (fun b => cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z b)
      (ball 0 (r lam)))
    (hB : ∀ lam ∈ S, ∀ b ∈ ball (0 : ℂ) (r lam), DifferentiableAt ℂ
      (fun w => cepsComplexKernelBridgeJetModel (cepsComplexJetPad d q) N lam w b) z)
    (hH : ∀ lam ∈ S, 1 ≤ lam → ∀ b ∈ ball (0 : ℂ) (r lam), DifferentiableAt ℂ
      (fun w => cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d q) N lam w b) z) :
    AEStronglyMeasurable (fun lam => cepsKernelPairCoeffC d N n q lam z) (volume.restrict S) :=
  cepsKernelPairCoeffC_aestronglyMeasurable_of_ae n q z
    (ae_restrict_of_forall_mem hS fun lam hlam =>
      ⟨r lam, hr lam hlam, hP lam hlam, hB lam hlam, fun h1 => hH lam hlam h1⟩)

end PGM
