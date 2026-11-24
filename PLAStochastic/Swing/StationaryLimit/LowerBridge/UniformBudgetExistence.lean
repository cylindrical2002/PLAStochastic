import PLAStochastic.Swing.StationaryLimit.LowerBridge.UniformBudget

/-!
# Real-valued early-slope localization helper

`exists_swingEarlySlopeGood` is stated in `ENNReal`.  The lower-bridge mass
certificate is most convenient in `ℝ`; this file records the lossless
conversion under the finite-measure hypothesis supplied by the Gaussian law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem exists_swingEarlySlopeGood_real
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {K : ℝ} (hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ M : ℝ) (J : ℕ), 0 < δ ∧ 1 ≤ J ∧
      μ.real (swingEarlySlopeGood X K δ M (J - 1))ᶜ ≤ ε := by
  obtain ⟨δ, M, J₀, hδ, hbad⟩ :=
    exists_swingEarlySlopeGood (μ := μ) hX hi hG hK
      (e := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  refine ⟨δ, M, J₀ + 1, hδ, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
  simpa [Measure.real, ENNReal.toReal_ofReal (le_of_lt hε)] using hreal

theorem exists_swingEarlySlopeGood_real_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {K : ℝ} (hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ M : ℝ) (J : ℕ), 0 < δ ∧ 0 ≤ M ∧ 1 ≤ J ∧
      μ.real (swingEarlySlopeGood X K δ M (J - 1))ᶜ ≤ ε := by
  obtain ⟨δ, M, J, hδ, hJ, hbad⟩ :=
    exists_swingEarlySlopeGood_real (μ := μ) hX hi hG hK hε
  let M' : ℝ := max M 0
  have hM' : 0 ≤ M' := by
    dsimp [M']
    exact le_max_right _ _
  have hsub :
      swingEarlySlopeGood X K δ M (J - 1) ⊆
        swingEarlySlopeGood X K δ M' (J - 1) := by
    intro ω hω
    rcases hω with ⟨hlo, hupp, htail⟩
    refine ⟨hlo, ?_, htail⟩
    exact hupp.trans (le_max_left _ _)
  have hcomp :
      (swingEarlySlopeGood X K δ M' (J - 1))ᶜ ⊆
        (swingEarlySlopeGood X K δ M (J - 1))ᶜ :=
    Set.compl_subset_compl.mpr hsub
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  refine ⟨δ, M', J, hδ, hM', hJ, ?_⟩
  exact (measureReal_mono hcomp (measure_ne_top μ _)).trans hbad

end SwingRepair
