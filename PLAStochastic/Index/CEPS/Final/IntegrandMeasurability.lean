import PLAStochastic.Index.CEPS.Final.PairInputs
import PLAStochastic.Index.CEPS.Final.EndpointCoeff
import PLAStochastic.Index.CEPS.Final.DriftMeasurabilityPair

/-! # Drift measurability of the glued integrand

Outside the central box the Newton scale coefficients are measurable in the drift by the
difference-quotient construction of `DriftMeasurabilityPair`, whose hypotheses are paid by the
outer strip analyticity of the pair and of the bridge factors (package S, stated here in its
proved form). Inside the box the central coefficient is continuous in the drift.
-/

noncomputable section
open Complex Metric Set Filter Topology MeasureTheory
namespace PGM

/-- Outer strip analyticity of the bridge and half bridge, as proved in `Strip/`. -/
def CepsStripBridgeAnalytic (d N : ℕ) : Prop :=
  ∀ M vlo vhi F₀ : ℝ, 0 ≤ M → 0 < vlo → vlo ≤ vhi → 0 < F₀ →
    ∃ δ δb : ℝ, 0 < δ ∧ 0 < δb ∧
      ∀ q : Fin d → ℂ, ‖q‖ ≤ M → vlo ≤ (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re →
        ‖cepsComplexJetPad d q (cepsJetCode (.inl 0))‖ ≤ vhi →
        |(cepsComplexJetPad d q (cepsJetCode (.inl 0))).im| ≤
          (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re / 8 →
        ∀ (lam : ℝ) (z b : ℂ), -δ ≤ z.re → F₀ ≤ |lam| + Real.sqrt ‖z‖ →
          ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δb →
          AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
              cepsComplexKernelBridgeJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2) (q, z, b) ∧
          (1 ≤ lam → AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
              cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2) (q, z, b))

/-- Bridge analyticity on the outer strip around a real reference vector, with the
cone constants of `cepsBall_variance_conditions`. -/
def CepsBridgeStripAt (d N : ℕ) (p₀ : Fin d → ℝ) (hcode : cepsJetCode (.inl 0) < d)
    (F₀ δf δbf : ℝ) : Prop :=
  ∀ q : Fin d → ℂ, ‖q‖ ≤ ‖(fun i => (p₀ i : ℂ))‖ + p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 16 →
    p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 2 ≤ (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re →
    ‖cepsComplexJetPad d q (cepsJetCode (.inl 0))‖ ≤ 2 * p₀ ⟨cepsJetCode (.inl 0), hcode⟩ →
    |(cepsComplexJetPad d q (cepsJetCode (.inl 0))).im| ≤
      (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re / 8 →
    ∀ (lam : ℝ) (z b : ℂ), -δf ≤ z.re → F₀ ≤ |lam| + Real.sqrt ‖z‖ →
      ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δbf →
      AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
          cepsComplexKernelBridgeJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2) (q, z, b) ∧
      (1 ≤ lam → AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
          cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2) (q, z, b))

/-- The strip bridge analyticity specializes to the reference cone constants. -/
theorem CepsStripBridgeAnalytic.at {d N : ℕ} (h : CepsStripBridgeAnalytic d N) (p₀ : Fin d → ℝ)
    (hcode : cepsJetCode (.inl 0) < d) (hV : 0 < p₀ ⟨cepsJetCode (.inl 0), hcode⟩)
    {F₀ : ℝ} (hF₀ : 0 < F₀) :
    ∃ δf δbf : ℝ, 0 < δf ∧ 0 < δbf ∧ CepsBridgeStripAt d N p₀ hcode F₀ δf δbf := by
  obtain ⟨δ, δb, hδ, hδb, H⟩ := h (‖(fun i => (p₀ i : ℂ))‖ + p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 16)
    (p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 2) (2 * p₀ ⟨cepsJetCode (.inl 0), hcode⟩) F₀
    (by positivity) (by positivity) (by linarith) hF₀
  exact ⟨δ, δb, hδ, hδb, H⟩

namespace CepsGlueData

variable {d N : ℕ} (G : CepsGlueData d N)

/-- At outer points the scale disc of `DriftMeasurabilityPair` holds. -/
theorem outer_scaleDisc (p₀ : Fin d → ℝ) (hcode : cepsJetCode (.inl 0) < d)
    (hV : 0 < p₀ ⟨cepsJetCode (.inl 0), hcode⟩) (hc₀ : G.c₀ = fun i => (p₀ i : ℂ))
    (hR : G.R ≤ p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 16) {δf δbf : ℝ} (hδbf : 0 < δbf)
    (hf : CepsBridgeStripAt d N p₀ hcode G.F₀ δf δbf)
    {q : Fin d → ℂ} (hq : q ∈ ball G.c₀ G.R) {lam : ℝ} {z : ℂ} (hz : -G.δ ≤ z.re)
    (hzf : -δf ≤ z.re) (hF : G.F₀ ≤ cepsDriftFreqSize lam z) :
    ∃ r : ℝ, CepsPairDriftScaleDisc d N q z lam r := by
  set X := 1 + cepsDriftFreqSize lam z
  have hX : 0 < X := by simp only [X]; linarith [size_nonneg lam z]
  set r := min G.δb δbf / (2 * X)
  have hr : 0 < r := div_pos (lt_min G.hδb hδbf) (by positivity)
  have hb : ∀ b ∈ ball (0 : ℂ) r, ‖b‖ * X ≤ G.δb ∧ ‖b‖ * X ≤ δbf := by
    intro b hb
    have h1 : ‖b‖ * X < min G.δb δbf / 2 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * X)).mp (mem_ball_zero_iff.mp hb)
      nlinarith
    have hm := min_le_left G.δb δbf
    have hm' := min_le_right G.δb δbf
    have hpos : 0 < min G.δb δbf := lt_min G.hδb hδbf
    constructor <;> linarith
  rw [hc₀] at hq
  obtain ⟨hq1, hq2, hq3, hq4⟩ := cepsBall_variance_conditions p₀ hcode hV hR hq
  have hq1' : ‖q‖ ≤ ‖(fun i => (p₀ i : ℂ))‖ + p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 16 :=
    hq1.trans (by linarith)
  have hq'' : q ∈ ball G.c₀ G.R := by rwa [hc₀]
  have hline (b : ℂ) : AnalyticAt ℂ (fun w : ℂ => (q, w, b)) z :=
    analyticAt_const.prod (analyticAt_id.prod analyticAt_const)
  refine ⟨r, hr, fun b hb' => ?_, fun b hb' => ?_, fun hl b hb' => ?_⟩
  · have h := (G.outer q hq'' lam z b hz hF (by simpa [X] using (hb b hb').1)).1
    have hl : AnalyticAt ℂ (fun t : ℂ => (q, z, t)) b :=
      analyticAt_const.prod (analyticAt_const.prod analyticAt_id)
    exact (h.comp (x := b) hl).differentiableAt.differentiableWithinAt
  · have h := (hf q hq1' hq2 hq3 hq4 lam z b hzf (by simpa [cepsDriftFreqSize] using hF)
      (by simpa [X, cepsDriftFreqSize, add_assoc] using (hb b hb').2)).1
    exact (h.comp (x := z) (hline b)).differentiableAt
  · have h := (hf q hq1' hq2 hq3 hq4 lam z b hzf (by simpa [cepsDriftFreqSize] using hF)
      (by simpa [X, cepsDriftFreqSize, add_assoc] using (hb b hb').2)).2 hl
    exact (h.comp (x := z) (hline b)).differentiableAt

/-- The central coefficient is continuous in the drift on the central box. -/
theorem central_continuousOn {q : Fin d → ℂ} (hq : q ∈ ball G.c₀ G.R) {z : ℂ} (hz : ‖z‖ < G.zc)
    (n : ℕ) : ContinuousOn (fun lam : ℝ => cepsCentralPairCoeff G.H n q lam z) (Ioo (-G.lc) G.lc) := by
  intro lam hlam
  have hl : |lam| < G.lc := abs_lt.mpr hlam
  have hq2 : dist q G.c₀ < G.r := (mem_ball.mp hq).trans_le (G.hRr.trans (half_le_self G.hr.le))
  have hl2 : |lam| < G.r := hl.trans_le (G.hlcr.trans (half_le_self G.hr.le))
  have hz2 : ‖z‖ < G.r := hz.trans_le (by linarith [G.hzcr, G.hzc])
  let P : ℂ × ℂ → ℂ := fun w => G.H (q, w.1, z, w.2)
  have hP : AnalyticAt ℂ P ((lam : ℂ), 0) := by
    have hm : AnalyticAt ℂ (fun w : ℂ × ℂ => (q, w.1, z, w.2)) ((lam : ℂ), 0) :=
      analyticAt_const.prod (analyticAt_fst.prod (analyticAt_const.prod analyticAt_snd))
    exact (G.central_an _ (G.mem_central_ball hq2 hl2 hz2
      (show ‖(0 : ℂ)‖ < G.r by simpa using G.hr))).comp (x := ((lam : ℂ), (0 : ℂ))) hm
  have hD := (hP.iteratedDeriv_snd n).comp (x := (lam : ℂ))
    (f := fun w : ℂ => (w, (0 : ℂ))) (analyticAt_id.prod analyticAt_const)
  have hc : ContinuousAt (fun w : ℂ => cepsScaleCoeff n (fun b => G.H (q, w, z, b))) (lam : ℂ) :=
    (analyticAt_const.mul hD).continuousAt
  exact (hc.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-- Drift measurability of the glued coefficient on the polydisc and strip. -/
theorem glued_aestronglyMeasurable (p₀ : Fin d → ℝ) (hcode : cepsJetCode (.inl 0) < d)
    (hV : 0 < p₀ ⟨cepsJetCode (.inl 0), hcode⟩) (hc₀ : G.c₀ = fun i => (p₀ i : ℂ))
    (hR : G.R ≤ p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 16) {δf δbf : ℝ} (hδbf : 0 < δbf)
    (hf : CepsBridgeStripAt d N p₀ hcode G.F₀ δf δbf)
    {q : Fin d → ℂ} (hq : q ∈ ball G.c₀ G.R) {z : ℂ} (hz : -G.δ ≤ z.re) (hzf : -δf ≤ z.re)
    (n : ℕ) :
    AEStronglyMeasurable (fun lam => cepsGluedPairCoeff d N n G.H G.lc G.zc q lam z) volume := by
  have hgood : ∀ lam : ℝ, ¬ (|lam| < G.lc ∧ ‖z‖ < G.zc) →
      ∃ r : ℝ, CepsPairDriftScaleDisc d N q z lam r := fun lam h =>
    G.outer_scaleDisc p₀ hcode hV hc₀ hR hδbf hf hq hz hzf (G.F₀_le_size_of_not_central h)
  by_cases hzc : ‖z‖ < G.zc
  · set s : Set ℝ := Ioo (-G.lc) G.lc
    have hs : MeasurableSet s := measurableSet_Ioo
    have hmem : ∀ lam, lam ∈ s ↔ |lam| < G.lc := fun lam => by simp [s, abs_lt]
    have heq : (fun lam => cepsGluedPairCoeff d N n G.H G.lc G.zc q lam z) =
        s.indicator (fun lam => cepsCentralPairCoeff G.H n q lam z) +
          sᶜ.indicator (fun lam => cepsKernelPairCoeffC d N n q lam z) := by
      funext lam
      simp only [Pi.add_apply, Set.indicator, Set.mem_compl_iff, hmem, cepsGluedPairCoeff, hzc,
        and_true]
      split_ifs <;> simp
    rw [heq]
    refine AEStronglyMeasurable.add ?_ ?_
    · exact (aestronglyMeasurable_indicator_iff hs).mpr
        ((G.central_continuousOn hq hzc n).aestronglyMeasurable hs)
    · refine (aestronglyMeasurable_indicator_iff hs.compl).mpr
        (cepsKernelPairCoeffC_aestronglyMeasurable_of_ae n q z ?_)
      rw [ae_restrict_iff' hs.compl]
      exact Eventually.of_forall fun lam hl =>
        hgood lam fun h => hl ((hmem lam).mpr h.1)
  · have heq : (fun lam => cepsGluedPairCoeff d N n G.H G.lc G.zc q lam z) =
        fun lam => cepsKernelPairCoeffC d N n q lam z := by
      funext lam
      simp only [cepsGluedPairCoeff, hzc, and_false, if_false]
    rw [heq]
    exact cepsKernelPairCoeffC_aestronglyMeasurable_of_ae n q z
      (Eventually.of_forall fun lam => hgood lam fun h => hzc h.2)

end CepsGlueData

end PGM
