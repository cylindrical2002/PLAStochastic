import PLAStochastic.Swing.Restart.Chain.State
import PLAStochastic.ForMathlib.Probability.Process.IIDRestart.FutureSequence
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! The actual restart kernel at a stopping time.  Independence of the entire
future sequence is proved from iid increments, rather than assumed at rejection. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The canonical coordinate process used to express path-dependent restart maps. -/
def nativeIncrementCoordinates (k : ℕ) (z : ℕ → ℝ) : ℝ := z k

theorem nativeIncrementCoordinates_measurable (k : ℕ) :
    Measurable (nativeIncrementCoordinates k) := measurable_pi_apply k

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

omit [MeasurableSpace Ω] in
theorem nativeRestartNext_coordinates (x E : ℝ) (ω : Ω) :
    nativeRestartNext nativeIncrementCoordinates E x (fun k => X k ω) =
      nativeRestartNext X E x ω := rfl

omit [MeasurableSpace Ω] in
theorem nativeRestartLengthNat_coordinates (x E : ℝ) (ω : Ω) :
    nativeRestartLengthNat nativeIncrementCoordinates E x (fun k => X k ω) =
      nativeRestartLengthNat X E x ω := rfl

/-- Passing to the law of the complete increment sequence preserves the exact kernel. -/
theorem nativeRestartKernel_coordinates [IsProbabilityMeasure μ]
    (hX : ∀ k, Measurable (X k)) (E : ℝ) :
    nativeRestartKernel nativeIncrementCoordinates (μ.map (fun ω k => X k ω)) E =
      nativeRestartKernel X μ E := by
  have hseq : Measurable (fun ω k => X k ω) := measurable_pi_lambda _ hX
  have : IsProbabilityMeasure (μ.map (fun ω k => X k ω)) := Measure.isProbabilityMeasure_map hseq.aemeasurable
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  have hnext : Measurable (fun z : ℕ → ℝ => nativeRestartNext nativeIncrementCoordinates E x z) :=
    (nativeRestartNext_measurable nativeIncrementCoordinates nativeIncrementCoordinates_measurable E).comp
      ((measurable_const (a := x)).prodMk measurable_id)
  have hset : MeasurableSet {z : ℕ → ℝ | nativeRestartNext nativeIncrementCoordinates E x z ∈ A} := hnext hA
  rw [nativeRestartKernel_apply nativeIncrementCoordinates_measurable E x hA,
    Measure.map_apply hseq hset, nativeRestartKernel_apply hX E x hA]
  rfl

theorem nativeRestartKernel_comp_eq_map_prod [SFinite μ] {ν : Measure ℝ} [SFinite ν]
    (hX : ∀ k, Measurable (X k)) (E : ℝ) :
    nativeRestartKernel X μ E ∘ₘ ν =
      (ν.prod μ).map (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) := by
  rw [nativeRestartKernel, ← Measure.map_comp _ _ (nativeRestartNext_measurable X hX E),
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

/-- The state and the entire unused sequence have the product of their marginal
laws at the original extended stopping time. -/
theorem nativeRestart_stopped_joint_law
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {S : Ω → ℝ} (hS : Measurable[hτ.measurableSpace] S) :
    μ.map (fun ω => (S ω, fun j => X ((τ ω).untopD 0+1+j) ω)) =
      (μ.map S).prod (μ.map (fun ω j => X j ω)) := by
  have := hi.isProbabilityMeasure
  have hSm : Measurable S := hS.mono hτ.measurableSpace_le le_rfl
  have hfuture := stoppedSequence_measurable hX hτ
  have hind : IndepFun S (fun ω j => X ((τ ω).untopD 0+1+j) ω) μ := by
    exact (indep_of_indep_of_le_right (stoppedSequence_indep_stopped hX hi hid hτ hfinite)
      hS.comap_le).symm
  rw [hind.map_prod_eq_prod_map_map hSm.aemeasurable hfuture.aemeasurable,
    (stoppedSequence_identDistrib hX hi hid hτ hfinite).map_eq]

/-- The exact one-step state law for any state measurable at a finite rejection
clock.  No fresh Gaussian replacement of the rejected increment occurs. -/
theorem nativeRestart_stopped_next_law
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {S : Ω → ℝ} (hS : Measurable[hτ.measurableSpace] S) (E : ℝ) :
    μ.map (fun ω => nativeRestartNext nativeIncrementCoordinates E (S ω)
      (fun j => X ((τ ω).untopD 0+1+j) ω)) =
        nativeRestartKernel X μ E ∘ₘ μ.map S := by
  have := hi.isProbabilityMeasure
  have hSm : Measurable S := hS.mono hτ.measurableSpace_le le_rfl
  have hseq : Measurable (fun ω j => X j ω) := measurable_pi_lambda _ hX
  have : IsProbabilityMeasure (μ.map S) := Measure.isProbabilityMeasure_map hSm.aemeasurable
  have : IsProbabilityMeasure (μ.map (fun ω j => X j ω)) := Measure.isProbabilityMeasure_map hseq.aemeasurable
  rw [← nativeRestartKernel_coordinates hX E, nativeRestartKernel_comp_eq_map_prod
    nativeIncrementCoordinates_measurable E,
    ← nativeRestart_stopped_joint_law hX hi hid hτ hfinite hS,
    Measure.map_map (nativeRestartNext_measurable nativeIncrementCoordinates nativeIncrementCoordinates_measurable E)
      (hSm.prodMk (stoppedSequence_measurable hX hτ))]
  rfl

/-- Every measurable state/future functional can be integrated against the
original increment space with an independent copy of the observed state. -/
theorem nativeRestart_stopped_functional_law {β : Type*} [MeasurableSpace β]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {S : Ω → ℝ} (hS : Measurable[hτ.measurableSpace] S)
    {F : ℝ × (ℕ → ℝ) → β} (hF : Measurable F) :
    μ.map (fun ω => F (S ω, fun j => X ((τ ω).untopD 0+1+j) ω)) =
      ((μ.map S).prod μ).map (fun p : ℝ × Ω => F (p.1, fun j => X j p.2)) := by
  have := hi.isProbabilityMeasure
  have hSm : Measurable S := hS.mono hτ.measurableSpace_le le_rfl
  have hseq : Measurable (fun ω j => X j ω) := measurable_pi_lambda _ hX
  have : IsProbabilityMeasure (μ.map S) := Measure.isProbabilityMeasure_map hSm.aemeasurable
  have heq : (μ.map S).prod (μ.map (fun ω j => X j ω)) =
      ((μ.map S).prod μ).map (fun p : ℝ × Ω => (p.1, fun j => X j p.2)) := by
    have hh := Measure.map_prod_map (μ.map S) μ (measurable_id (α := ℝ)) hseq
    rw [Measure.map_id] at hh
    exact hh.trans (congrArg (fun f => ((μ.map S).prod μ).map f) (by funext p; rfl))
  calc
    _ = (μ.map (fun ω => (S ω, fun j => X ((τ ω).untopD 0+1+j) ω))).map F := by
      simpa only [Function.comp_def] using
        (Measure.map_map hF (hSm.prodMk (stoppedSequence_measurable hX hτ)) (μ := μ)).symm
    _ = (((μ.map S).prod μ).map (fun p : ℝ × Ω => (p.1, fun j => X j p.2))).map F := by
      rw [nativeRestart_stopped_joint_law hX hi hid hτ hfinite hS, heq]
    _ = _ := by
      simpa only [Function.comp_def] using
        Measure.map_map hF (measurable_fst.prodMk (hseq.comp measurable_snd)) (μ := (μ.map S).prod μ)

theorem nativeRestartLengthNat_prod_integrable {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    Integrable (fun p : ℝ × Ω => (nativeRestartLengthNat X E p.1 p.2 : ℝ)) (ν.prod μ) := by
  have := hi.isProbabilityMeasure
  have hF : Measurable (fun p : ℝ × Ω => (nativeRestartLengthNat X E p.1 p.2 : ℝ)) :=
    (measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp
      (nativeRestartLengthNat_measurable X hX E)
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (nativeRestartLengthNat_integrable hX hi hG hE)
  · have hnorm : (fun x => ∫ ω, ‖(nativeRestartLengthNat X E x ω : ℝ)‖ ∂μ) =
        nativeRestartMean X μ E := by
      funext x
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => Real.norm_of_nonneg (Nat.cast_nonneg _))
    rw [hnorm]
    apply (integrable_const (2*(⌈8*E^2⌉₊ : ℝ)/(1-gaussianBlockPass.toReal))).mono'
      (nativeRestartMean_measurable hX E).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := (nativeRestartMean_bounds hX hi hG hE x).1; linarith)]
    exact (nativeRestartMean_bounds hX hi hG hE x).2

/-- The real-valued actual stopped duration has its product-space law. -/
theorem nativeRestart_stopped_length_identDistrib
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {S : Ω → ℝ} (hS : Measurable[hτ.measurableSpace] S) (E : ℝ) :
    IdentDistrib (fun ω => (nativeRestartLengthNat nativeIncrementCoordinates E (S ω)
      (fun j => X ((τ ω).untopD 0+1+j) ω) : ℝ))
      (fun p : ℝ × Ω => (nativeRestartLengthNat X E p.1 p.2 : ℝ)) μ ((μ.map S).prod μ) := by
  have := hi.isProbabilityMeasure
  have hSm : Measurable S := hS.mono hτ.measurableSpace_le le_rfl
  have : IsProbabilityMeasure (μ.map S) := Measure.isProbabilityMeasure_map hSm.aemeasurable
  have hF : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      (nativeRestartLengthNat nativeIncrementCoordinates E p.1 p.2 : ℝ)) :=
    (measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp
      (nativeRestartLengthNat_measurable nativeIncrementCoordinates nativeIncrementCoordinates_measurable E)
  exact
    ⟨(hF.comp (hSm.prodMk (stoppedSequence_measurable hX hτ))).aemeasurable,
      ((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp
        (nativeRestartLengthNat_measurable X hX E)).aemeasurable,
      nativeRestart_stopped_functional_law hX hi hid hτ hfinite hS hF⟩

theorem nativeRestart_stopped_length_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {S : Ω → ℝ} (hS : Measurable[hτ.measurableSpace] S) {E : ℝ} (hE : 0 < E) :
    Integrable (fun ω => (nativeRestartLengthNat nativeIncrementCoordinates E (S ω)
      (fun j => X ((τ ω).untopD 0+1+j) ω) : ℝ)) μ := by
  have := hi.isProbabilityMeasure
  have hSm : Measurable S := hS.mono hτ.measurableSpace_le le_rfl
  have : IsProbabilityMeasure (μ.map S) := Measure.isProbabilityMeasure_map hSm.aemeasurable
  exact (nativeRestart_stopped_length_identDistrib hX hi
    (fun n => ⟨(hX n).aemeasurable, (hX 0).aemeasurable, (hG n).trans (hG 0).symm⟩)
    hτ hfinite hS E).symm.integrable_snd (nativeRestartLengthNat_prod_integrable hX hi hG hE)

/-- The actual conditional duration mean is integrated against the law of the
observed state. Product integrability follows from the proved uniform block bound. -/
theorem nativeRestart_stopped_mean
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {S : Ω → ℝ} (hS : Measurable[hτ.measurableSpace] S) {E : ℝ} (hE : 0 < E) :
    (∫ ω, (nativeRestartLengthNat nativeIncrementCoordinates E (S ω)
      (fun j => X ((τ ω).untopD 0+1+j) ω) : ℝ) ∂μ) =
        ∫ x, nativeRestartMean X μ E x ∂μ.map S := by
  have := hi.isProbabilityMeasure
  have hSm : Measurable S := hS.mono hτ.measurableSpace_le le_rfl
  have : IsProbabilityMeasure (μ.map S) := Measure.isProbabilityMeasure_map hSm.aemeasurable
  rw [(nativeRestart_stopped_length_identDistrib hX hi
    (fun n => ⟨(hX n).aemeasurable, (hX 0).aemeasurable, (hG n).trans (hG 0).symm⟩)
    hτ hfinite hS E).integral_eq,
    integral_prod _ (nativeRestartLengthNat_prod_integrable hX hi hG hE)]
  rfl

end SwingRepair
