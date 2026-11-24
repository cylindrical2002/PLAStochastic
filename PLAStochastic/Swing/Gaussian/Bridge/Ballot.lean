import PLAStochastic.Swing.Gaussian.Bridge.ActualDensity

/-! The ballot estimate for the actual first half of a Gaussian bridge. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

def gaussianBridgeSurvives (X : ℕ → Ω → ℝ) (N : ℕ) (x a : ℝ) (M : ℕ) : Set Ω :=
  {ω | ∀ j ≤ M, 0 ≤ x+gaussianBridgePosition X N j ω+a*(j : ℝ)}

theorem gaussianBridgeSurvives_measurable (hX : ∀ n, Measurable (X n)) (N : ℕ) (x a : ℝ) (M : ℕ) :
    MeasurableSet (gaussianBridgeSurvives X N x a M) := by
  simp only [gaussianBridgeSurvives, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le measurable_const
    ((measurable_const.add (gaussianBridgePosition_measurable hX N j)).add_const _)

omit mΩ in
theorem gaussianBridgeSurvives_eq_preimage (N M : ℕ) (x a : ℝ) :
    gaussianBridgeSurvives X N x a M = gaussianBridgeIncrementPrefix X N M ⁻¹'
      gaussianHalfLineSurvives (gaussianFiniteSamples M) x a M := by
  ext ω
  have he (j : ℕ) (hj : j ≤ M) :
      gaussianDriftWalk (gaussianFiniteSamples M) x a j (gaussianBridgeIncrementPrefix X N M ω) =
      x+gaussianBridgePosition X N j ω+a*(j : ℝ) := by
    change gaussianDriftWalk (gaussianFiniteSamples M) x a j
      (fun i : Fin M => gaussianBridgeIncrement X N i.val ω) = _
    rw [gaussianFiniteSamples_actual (X := gaussianBridgeIncrement X N) hj x a ω]
    dsimp only [gaussianDriftWalk]
    rw [gaussianBridgePosition_eq_sum]
    rfl
  change (∀ j ≤ M, 0 ≤ _) ↔ ∀ j ≤ M, 0 ≤ _
  constructor <;> intro h j hj
  · rw [he j hj]
    exact h j hj
  · rw [← he j hj]
    exact h j hj

/-- The Radon-Nikodym bound applies to the actual bridge survival event. -/
theorem gaussianBridgeSurvives_le_walk
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M N : ℕ}
    (hMN : M < N) (hhalf : M ≤ N-M) (x a : ℝ) :
    μ.real (gaussianBridgeSurvives X N x a M) ≤
      Real.sqrt 2 * μ.real (gaussianHalfLineSurvives X x a M) := by
  let A := gaussianHalfLineSurvives (gaussianFiniteSamples M) x a M
  have hA : MeasurableSet A := gaussianFiniteSamples_survives_measurable M x a
  have hle := (gaussianBridgeIncrementPrefix_measure_le hX hi hG hMN hhalf) A
  rw [Measure.map_apply (gaussianBridgeIncrementPrefix_measurable hX N M) hA,
    ← gaussianBridgeSurvives_eq_preimage N M x a, Measure.smul_apply] at hle
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (Measure.pi (fun _ : Fin M => gaussianReal 0 1)) A)) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg 2)] at hreal
  have he := gaussianFiniteSurvival_integral hX hi hG M x a (f := fun _ => (1 : ℝ)) measurable_const
  simp only [setIntegral_const, smul_eq_mul, mul_one] at he
  rw [he]
  exact hreal

/-- The ordinary ballot bound transfers through the exact bridge density. -/
theorem gaussianBridge_ballot_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M N : ℕ}
    (hMN : M < N) (hhalf : M ≤ N-M) (hM : 0 < M)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    μ.real (gaussianBridgeSurvives X N x a M) ≤
      Real.sqrt 2*gaussianBallotConstant*(x+1)*(a+(Real.sqrt (M : ℝ))⁻¹) := by
  have hb := gaussianBridgeSurvives_le_walk hX hi hG hMN hhalf x a
  rw [gaussianHalfLineSurvives_eq_survivalEvent hx] at hb
  have hw := gaussian_ballot_bound hX hi hG hx ha ha' hM
  calc
    _ ≤ Real.sqrt 2 * μ.real (gaussianSurvivalEvent X x a M) := hb
    _ ≤ Real.sqrt 2*(gaussianBallotConstant*(x+1)*(a+(Real.sqrt (M : ℝ))⁻¹)) :=
      mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg _)
    _ = _ := by ring

end SwingRepair
