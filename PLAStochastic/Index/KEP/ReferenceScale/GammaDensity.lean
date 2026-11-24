import PLAStochastic.ForMathlib.Probability.Distributions.GammaMixtureDerivative
import PLAStochastic.Index.Endpoint.GammaClosure
import PLAStochastic.Index.KEP.PivotRestart
import PLAStochastic.Index.Model.ExpSequence
import PLAStochastic.ForMathlib.Probability.Hellinger.RadonNikodym

/-!
# The actual positive reference layers have smooth Gamma-mixture densities

The weights are the actual base-rank probabilities, identified by the existing
conditional Gamma theorem. The deterministic minimum rank removes all shapes
below four. This proves finite-layer regularity, without asserting a uniform
second-derivative budget.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Z : ℕ → Ω → ℝ × ℕ}

def gammaCountWeights (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) (n : ℕ) : ℝ :=
  P.real {ω | (Z 0 ω).2 = n + 4}

omit [IsProbabilityMeasure P] in
theorem gammaCountWeights_nonneg (n : ℕ) : 0 ≤ gammaCountWeights P Z n :=
  measureReal_nonneg

theorem tsum_measure_gammaCount (hZ : Measurable (Z 0))
    (hN : ∀ᵐ ω ∂P, 4 ≤ (Z 0 ω).2) :
    (∑' n : ℕ, P {ω | (Z 0 ω).2 = n + 4}) = 1 := by
  have hs (n : ℕ) : MeasurableSet {ω | (Z 0 ω).2 = n + 4} :=
    hZ.snd (measurableSet_singleton _)
  have hd : Pairwise (Function.onFun Disjoint (fun n : ℕ => {ω | (Z 0 ω).2 = n + 4})) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro ω hn hm
    change (Z 0 ω).2 = n + 4 at hn
    change (Z 0 ω).2 = m + 4 at hm
    exact hnm (by omega)
  have he : (⋃ n : ℕ, {ω | (Z 0 ω).2 = n + 4}) =ᵐ[P] univ := by
    filter_upwards [hN] with ω hω
    apply propext
    change ω ∈ (⋃ n : ℕ, {ω | (Z 0 ω).2 = n + 4}) ↔ ω ∈ univ
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨(Z 0 ω).2 - 4, by omega⟩
  rw [← measure_iUnion hd hs, measure_congr he, measure_univ]

theorem summable_gammaCountWeights (hZ : Measurable (Z 0))
    (hN : ∀ᵐ ω ∂P, 4 ≤ (Z 0 ω).2) : Summable (gammaCountWeights P Z) := by
  apply ENNReal.summable_toReal
  rw [tsum_measure_gammaCount hZ hN]
  exact ENNReal.one_ne_top

theorem tsum_gammaCountWeights (hZ : Measurable (Z 0))
    (hN : ∀ᵐ ω ∂P, 4 ≤ (Z 0 ω).2) : (∑' n, gammaCountWeights P Z n) = 1 := by
  unfold gammaCountWeights Measure.real
  rw [← ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _), tsum_measure_gammaCount hZ hN,
    ENNReal.toReal_one]

omit [IsProbabilityMeasure P] in
theorem gammaKernel_measure_eq_tsum_four (hK : GammaKernel P Z) (hZ : Measurable (Z 0))
    (hN : ∀ᵐ ω ∂P, 4 ≤ (Z 0 ω).2) {A : Set ℝ} (hA : MeasurableSet A) :
    P {ω | (Z 0 ω).1 ∈ A} =
      ∑' n : ℕ, P {ω | (Z 0 ω).2 = n + 4} * gammaMeasure ((n + 4 : ℕ) : ℝ) 1 A := by
  have hs (n : ℕ) : MeasurableSet {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n + 4} :=
    (hZ.fst hA).inter (hZ.snd (measurableSet_singleton _))
  have hd : Pairwise (Function.onFun Disjoint
      (fun n : ℕ => {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n + 4})) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro ω hn hm
    change (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n + 4 at hn
    change (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = m + 4 at hm
    exact hnm (by omega)
  have he : {ω | (Z 0 ω).1 ∈ A} =ᵐ[P]
      ⋃ n : ℕ, {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n + 4} := by
    filter_upwards [hN] with ω hω
    apply propext
    change ω ∈ {ω | (Z 0 ω).1 ∈ A} ↔
      ω ∈ (⋃ n : ℕ, {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n + 4})
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨(Z 0 ω).2 - 4, h, by omega⟩
    · rintro ⟨n, h, -⟩
      exact h
  rw [measure_congr he, measure_iUnion hd hs]
  exact tsum_congr fun n => hK (n + 4) A hA (by omega)

def gammaKernelDensity (hZ : Measurable (Z 0)) (hN : ∀ᵐ ω ∂P, 4 ≤ (Z 0 ω).2) :
    HellingerDensity (volume : Measure ℝ) :=
  gammaMixtureHellinger (gammaCountWeights_nonneg (P := P) (Z := Z))
    (summable_gammaCountWeights hZ hN) (tsum_gammaCountWeights hZ hN)

theorem gammaKernelDensity_toMeasure (hK : GammaKernel P Z) (hZ : Measurable (Z 0))
    (hN : ∀ᵐ ω ∂P, 4 ≤ (Z 0 ω).2) :
    (gammaKernelDensity hZ hN).toMeasure = P.map (fun ω => (Z 0 ω).1) := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hZ.fst hA]
  change volume.withDensity (fun x => ENNReal.ofReal
    (gammaMixtureDensity (gammaCountWeights P Z) 3 x)) A = _
  rw [withDensity_apply _ hA]
  change (∫⁻ x in A, ENNReal.ofReal (gammaMixtureDensity (gammaCountWeights P Z) 3 x)) =
    P {ω | (Z 0 ω).1 ∈ A}
  rw [gammaKernel_measure_eq_tsum_four hK hZ hN hA]
  simp only [gammaMixtureDensity]
  simp_rw [ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (gammaCountWeights_nonneg n) (gammaNatDensity_nonneg _ _))
    (summable_gammaMixtureDensity (gammaCountWeights_nonneg (P := P) (Z := Z))
      (summable_gammaCountWeights hZ hN) 3 _),
    ENNReal.ofReal_mul (gammaCountWeights_nonneg _)]
  have hmeas (n : ℕ) : Measurable (fun x => ENNReal.ofReal (gammaCountWeights P Z n) *
      ENNReal.ofReal (gammaNatDensity (n + 3) x)) :=
    ((measurable_gammaPDFReal ((n + 4 : ℕ) : ℝ) 1).ennreal_ofReal).const_mul _
  rw [lintegral_tsum (fun n => (hmeas n).aemeasurable)]
  apply tsum_congr
  intro n
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hpw : ENNReal.ofReal (gammaCountWeights P Z n) = P {ω | (Z 0 ω).2 = n + 4} :=
    ofReal_measureReal
  have hpdf : (∫⁻ x in A, ENNReal.ofReal (gammaNatDensity (n + 3) x)) =
      gammaMeasure ((n + 4 : ℕ) : ℝ) 1 A := by
    rw [gammaMeasure, withDensity_apply _ hA]
    rfl
  rw [hpw, hpdf]

theorem ae_reference_count_ge_four {eps : ℝ} (heps : 2 ≤ eps) {j : ℕ} (hj : 1 ≤ j) :
    ∀ᵐ ω ∂expSeqMeasure, 4 ≤ (epLayerSeq eps expCoord j 0 ω).2 := by
  have heps0 : 0 ≤ eps := by linarith
  filter_upwards [ae_allLayersFinite_exp iidSeq_expCoord (hasLaw_expCoord 0) heps0] with ω hω
  have hp := pow_le_layerPivot_sub heps0 (z := seq (inputPairs expCoord) ω)
    (fun _ => rfl) hω j 0
  have he : layerPivot eps (seq (inputPairs expCoord) ω) j 1 -
      layerPivot eps (seq (inputPairs expCoord) ω) j 0 = (epLayerSeq eps expCoord j 0 ω).2 := by
    simp only [layerPivot, pairRank_one, pairRank_zero, Nat.sub_zero, ← seq_epLayerSeq]
    rfl
  rw [he] at hp
  have hq : 4 ≤ ⌊2 * eps⌋₊ + 1 := by
    have h : 3 ≤ ⌊2 * eps⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hpow : 1 ≤ (⌊2 * eps⌋₊ + 1) ^ i := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have hqpow : ⌊2 * eps⌋₊ + 1 ≤ (⌊2 * eps⌋₊ + 1) ^ (i + 1) := by
    rw [pow_succ]
    simpa only [one_mul] using Nat.mul_le_mul_right (⌊2 * eps⌋₊ + 1) hpow
  exact (hq.trans hqpow).trans hp

def kepReferenceRawDensity {eps : ℝ} (heps : 2 ≤ eps) {j : ℕ} (hj : 1 ≤ j) :
    HellingerDensity (volume : Measure ℝ) :=
  gammaKernelDensity
    ((gammaClosure_epLayerSeq iidSeq_expCoord (hasLaw_expCoord 0) (by linarith : 0 ≤ eps) j).1.measurable 0)
    (ae_reference_count_ge_four heps hj)

theorem kepReferenceRawDensity_toMeasure {eps : ℝ} (heps : 2 ≤ eps) {j : ℕ} (hj : 1 ≤ j) :
    (kepReferenceRawDensity heps hj).toMeasure =
      expSeqMeasure.map (fun ω => (epLayerSeq eps expCoord j 0 ω).1) :=
  gammaKernelDensity_toMeasure
    (gammaKernel_epLayerSeq iidSeq_expCoord (hasLaw_expCoord 0) (by linarith : 0 ≤ eps) j)
    _ (ae_reference_count_ge_four heps hj)

end

end PGM
