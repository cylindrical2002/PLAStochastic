import PLAStochastic.Swing.Gaussian.Bridge.Ballot

/-! Endpoint-dependent bridge survival, with genuine averaging over the Gaussian endpoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

def gaussianBridgeVariableSurvives (X : ℕ → Ω → ℝ) (N : ℕ) (x : ℝ → ℝ) (a : ℝ) (M : ℕ) : Set Ω :=
  {ω | 0 ≤ x (cumulativeSamples X N ω) ∧
    ω ∈ gaussianBridgeSurvives X N (x (cumulativeSamples X N ω)) a M}

/-- The endpoint factorization justifies averaging the bridge bound at a random starting height. -/
theorem gaussianBridgeVariableSurvives_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M N : ℕ}
    (hMN : M < N) (hhalf : M ≤ N-M) (hM : 0 < M)
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1/2)
    {x b : ℝ → ℝ} (hx : Measurable x) (hb : Integrable b (gaussianReal 0 (N : ℝ≥0)))
    (hb0 : ∀ y, 0 ≤ b y) (hxb : ∀ y, x y ≤ b y) :
    μ.real (gaussianBridgeVariableSurvives X N x a M) ≤
      Real.sqrt 2*gaussianBallotConstant*(a+(Real.sqrt (M : ℝ))⁻¹)*
        (∫ y, b y+1 ∂gaussianReal 0 (N : ℝ≥0)) := by
  have := hi.isProbabilityMeasure
  let ν := μ.map (gaussianBridgePrefix X N M)
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map
    (gaussianBridgePrefix_measurable hX N M).aemeasurable
  let C := Real.sqrt 2*gaussianBallotConstant*(a+(Real.sqrt (M : ℝ))⁻¹)
  have hC : 0 ≤ C := by
    have h := gaussianBallotConstant_pos
    dsimp [C]
    positivity
  let H : Set ((Fin (M+1) → ℝ) × ℝ) :=
    {p | 0 ≤ x p.2 ∧ ∀ j : Fin (M+1), 0 ≤ x p.2+p.1 j+a*(j.val : ℝ)}
  have hH : MeasurableSet H := by
    have hJ : MeasurableSet (⋂ j : Fin (M+1), {p : (Fin (M+1) → ℝ) × ℝ |
        0 ≤ x p.2+p.1 j+a*(j.val : ℝ)}) := by
      apply MeasurableSet.iInter
      intro j
      exact measurableSet_le measurable_const
        (((hx.comp measurable_snd).add ((measurable_pi_apply j).comp measurable_fst)).add_const _)
    have h0 : MeasurableSet {p : (Fin (M+1) → ℝ) × ℝ | 0 ≤ x p.2} :=
      measurableSet_le measurable_const (hx.comp measurable_snd)
    convert h0.inter hJ using 1
    ext p
    simp only [H, Set.mem_inter_iff, Set.mem_iInter, mem_ofPred_eq]
  have hsection (y : ℝ) : MeasurableSet {z : Fin (M+1) → ℝ | (z, y) ∈ H} :=
    hH.preimage (by fun_prop)
  have he : (fun ω => (gaussianBridgePrefix X N M ω, cumulativeSamples X N ω)) ⁻¹' H =
      gaussianBridgeVariableSurvives X N x a M := by
    ext ω
    change (0 ≤ _ ∧ ∀ j : Fin (M+1), 0 ≤ _) ↔ (0 ≤ _ ∧ ∀ j ≤ M, 0 ≤ _)
    constructor
    · rintro ⟨h0, hh⟩
      exact ⟨h0, fun j hj => hh ⟨j, by omega⟩⟩
    · rintro ⟨h0, hh⟩
      exact ⟨h0, fun j => hh j.val (by omega)⟩
  have hμ : μ (gaussianBridgeVariableSurvives X N x a M) =
      ∫⁻ y, ν {z | (z, y) ∈ H} ∂gaussianReal 0 (N : ℝ≥0) := by
    rw [← he, ← Measure.map_apply
      ((gaussianBridgePrefix_measurable hX N M).prodMk
        (show Measurable (cumulativeSamples X N) by unfold cumulativeSamples; fun_prop)) hH,
      gaussianBridgePrefix_endpoint_jointLaw hX hi hG hMN.le, Measure.prod_apply_symm hH]
    rfl
  have hbound (y : ℝ) : ν {z | (z, y) ∈ H} ≤ ENNReal.ofReal (C*(b y+1)) := by
    by_cases hy : 0 ≤ x y
    · have hs : gaussianBridgePrefix X N M ⁻¹' {z | (z, y) ∈ H} =
          gaussianBridgeSurvives X N (x y) a M := by
        ext ω
        change (0 ≤ x y ∧ ∀ j : Fin (M+1), 0 ≤ _) ↔ ∀ j ≤ M, 0 ≤ _
        constructor
        · rintro ⟨_, hh⟩ j hj
          exact hh ⟨j, by omega⟩
        · intro hh
          exact ⟨hy, fun j => hh j.val (by omega)⟩
      dsimp only [ν]
      rw [Measure.map_apply (gaussianBridgePrefix_measurable hX N M) (hsection y), hs]
      have hh := gaussianBridge_ballot_bound hX hi hG hMN hhalf hM hy ha ha'
      have hh' : μ.real (gaussianBridgeSurvives X N (x y) a M) ≤ C*(b y+1) := by
        calc
          _ ≤ Real.sqrt 2*gaussianBallotConstant*(x y+1)*(a+(Real.sqrt (M : ℝ))⁻¹) := hh
          _ = C*(x y+1) := by dsimp [C]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hxb y]) hC
      have he := ENNReal.ofReal_le_ofReal hh'
      simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)] using he
    · have hs : {z : Fin (M+1) → ℝ | (z, y) ∈ H} = ∅ := by
        ext z
        simp only [H, mem_ofPred_eq, hy, false_and, notMem_empty]
      rw [hs, measure_empty]
      exact bot_le
  have hI : Integrable (fun y => C*(b y+1)) (gaussianReal 0 (N : ℝ≥0)) :=
    (hb.add (integrable_const 1)).const_mul C
  have hI0 (y : ℝ) : 0 ≤ C*(b y+1) := mul_nonneg hC (by linarith [hb0 y])
  have hle : μ (gaussianBridgeVariableSurvives X N x a M) ≤
      ENNReal.ofReal (∫ y, C*(b y+1) ∂gaussianReal 0 (N : ℝ≥0)) := by
    rw [hμ, ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hI0)]
    exact lintegral_mono hbound
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (integral_nonneg hI0), integral_const_mul] at hreal
  exact hreal

end SwingRepair
