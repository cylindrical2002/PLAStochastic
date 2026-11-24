import PLAStochastic.Swing.SecondSegment.FrozenMeanBridge
import PLAStochastic.Swing.Restart.Chain.Specification
import PLAStochastic.Swing.StationaryScale.FavorableGeometry

/-! # The finite-budget reflected-margin kernel

The restart chain is naturally a chain on the signed carry `x`.  Its reflected
margin is `r = E - |x|`.  This file constructs a genuine kernel on margins by
choosing the nonnegative representative `E-r`; the reflection identity shows
that this choice is immaterial on the range of the margin map.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

variable {Ω : Type*} [MeasurableSpace Ω]

def finiteMarginMap (E : ℝ) (x : ℝ) : ℝ := E - |x|

def finiteMarginSection (E : ℝ) (r : ℝ) : ℝ := E - r

theorem measurable_finiteMarginMap (E : ℝ) : Measurable (finiteMarginMap E) :=
  measurable_const.sub continuous_abs.measurable

theorem measurable_finiteMarginSection (E : ℝ) : Measurable (finiteMarginSection E) :=
  measurable_const.sub measurable_id

theorem finiteMarginSection_apply_map (E x : ℝ) :
    finiteMarginSection E (finiteMarginMap E x) = |x| := by
  simp only [finiteMarginSection, finiteMarginMap]
  ring

/-! ### Pathwise reflection of the constrained-SSE restart update -/

omit [MeasurableSpace Ω] in
theorem nativeRestartSlope_neg_pathwise
    (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E) (x : ℝ) (ω : Ω)
    (hf : nativeRestartLength X E x ω ≠ ⊤) :
    nativeRestartSlope (negIncrements X) E (-x) ω =
      -nativeRestartSlope X E x ω := by
  have hfneg : nativeRestartLength (negIncrements X) E (-x) ω ≠ ⊤ := by
    rw [nativeRestartLength_neg X E x ω]
    exact hf
  have hN : 0 < nativeRestartLengthNat X E x ω :=
    nativeRestartLengthNat_pos_of_finite X hE x ω hf
  have hN_eq : nativeRestartLengthNat (negIncrements X) E (-x) ω =
      nativeRestartLengthNat X E x ω := nativeRestartLengthNat_neg X E x ω
  rw [nativeRestartSlope, nativeRestartSlope, hN_eq]
  simp only [nativeRestartSlopeAt, dif_pos hN]
  have hspec := nativeRestartLengthNat_spec X E x ω hf
  have hfeas : ∃ m, feasibleSlope (Finset.Icc 1 (nativeRestartLengthNat X E x ω))
      (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E m :=
    ⟨nativeRestartSlope X E x ω,
      nativeRestartSlope_feasible X hE x ω hf⟩
  have ht : ∀ i ∈ Finset.Icc 1 (nativeRestartLengthNat X E x ω),
      (0 : ℝ) < (i : ℝ) := by
    intro i hi
    exact_mod_cast (Finset.mem_Icc.mp hi).1
  have hLU : nativeConeLower (Finset.Icc 1 (nativeRestartLengthNat X E x ω))
      (Finset.nonempty_Icc.mpr hN) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E ≤
      nativeConeUpper (Finset.Icc 1 (nativeRestartLengthNat X E x ω))
      (Finset.nonempty_Icc.mpr hN) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E :=
    (nativeCone_nonempty_iff _ _ _ _ _ _ _ ht).mp hfeas
  have hy : (fun i => nativeCarriedSamples (negIncrements X) (fun _ => -x) i ω) =
      (fun i => -(nativeCarriedSamples X (fun _ => x) i ω)) :=
    nativeCarriedSamples_neg_carry X x ω
  rw [hy]
  exact nativeSelectedSlope_neg _ _ _ _ _ _ hLU

omit [MeasurableSpace Ω] in
theorem nativeRestartNext_neg_pathwise
    (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E) (x : ℝ) (ω : Ω)
    (hf : nativeRestartLength X E x ω ≠ ⊤) :
    nativeRestartNext (negIncrements X) E (-x) ω =
      -nativeRestartNext X E x ω := by
  have hfneg : nativeRestartLength (negIncrements X) E (-x) ω ≠ ⊤ := by
    rw [nativeRestartLength_neg X E x ω]
    exact hf
  have hN := nativeRestartLengthNat_neg X E x ω
  rw [nativeRestartNext, nativeRestartNext, hN,
    nativeRestartSlope_neg_pathwise X hE x ω hf, cumulativeSamples_neg]
  ring

/-! The pathwise identity is enough on the Gaussian full-measure set. -/

theorem nativeRestartNext_neg_ae
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (x : ℝ) :
    nativeRestartNext (negIncrements X) E (-x) =ᵐ[μ]
      fun ω => -nativeRestartNext X E x ω := by
  filter_upwards [nativeRestartLength_ae_finite hX hi hG hE x] with ω hf
  exact nativeRestartNext_neg_pathwise X hE.le x ω hf

/-! ### Symmetry of the reflected output law -/

theorem nativeRestartKernel_map_finiteMargin
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (E x : ℝ) :
    (nativeRestartKernel X μ E x).map (finiteMarginMap E) =
      μ.map (fun ω => finiteMarginMap E (nativeRestartNext X E x ω)) := by
  apply Measure.ext
  intro s hs
  have hnext : Measurable (fun ω => nativeRestartNext X E x ω) :=
    (nativeRestartNext_measurable X hX E).comp
      ((measurable_const (a := x)).prodMk measurable_id)
  rw [Measure.map_apply (measurable_finiteMarginMap E) hs,
    nativeRestartKernel_apply hX E x (hs.preimage (measurable_finiteMarginMap E))]
  have hmap := Measure.map_apply (μ := μ)
    ((measurable_finiteMarginMap E).comp hnext) hs
  have hset : (fun ω => finiteMarginMap E (nativeRestartNext X E x ω)) ⁻¹' s =
      {ω | nativeRestartNext X E x ω ∈ finiteMarginMap E ⁻¹' s} := by
    ext ω
    rfl
  rw [← hset]
  simpa only [Function.comp_def] using hmap.symm

theorem nativeRestartMarginLaw_neg_eq
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (x : ℝ) :
    (nativeRestartKernel X μ E (-x)).map (finiteMarginMap E) =
      (nativeRestartKernel X μ E x).map (finiteMarginMap E) := by
  have hnegX : ∀ n, Measurable (negIncrements X n) := fun n => (hX n).neg
  have hcoord := negSequence_identDistrib hX hi hG
  let F : (ℕ → ℝ) → ℝ := nativeRestartNext nativeIncrementCoordinates E (-x)
  have hF : Measurable F := by
    dsimp [F]
    exact (nativeRestartNext_measurable nativeIncrementCoordinates
      nativeIncrementCoordinates_measurable E).comp
      ((measurable_const (a := -x)).prodMk measurable_id)
  have hFident : IdentDistrib
      (fun ω => F (fun j => X j ω))
      (fun ω => F (fun j => -X j ω)) μ μ :=
    (hcoord.symm.comp hF)
  have houtputs : IdentDistrib
      (fun ω => nativeRestartNext X E (-x) ω)
      (fun ω => nativeRestartNext (negIncrements X) E (-x) ω) μ μ := by
    have hleft : (fun ω => F (fun j => X j ω)) =
        (fun ω => nativeRestartNext X E (-x) ω) := by
      funext ω
      rfl
    have hright : (fun ω => F (fun j => -X j ω)) =
        (fun ω => nativeRestartNext (negIncrements X) E (-x) ω) := by
      funext ω
      rfl
    have hleft' : IdentDistrib
        (fun ω => F (fun j => X j ω))
        (fun ω => nativeRestartNext X E (-x) ω) μ μ :=
      IdentDistrib.of_ae_eq hFident.aemeasurable_fst
        (Eventually.of_forall (fun ω => hleft ▸ rfl))
    have hright' : IdentDistrib
        (fun ω => F (fun j => -X j ω))
        (fun ω => nativeRestartNext (negIncrements X) E (-x) ω) μ μ :=
      IdentDistrib.of_ae_eq hFident.aemeasurable_snd
        (Eventually.of_forall (fun ω => hright ▸ rfl))
    exact hleft'.symm.trans (hFident.trans hright')
  have hmapout : μ.map (fun ω =>
      finiteMarginMap E (nativeRestartNext X E (-x) ω)) =
      μ.map (fun ω => finiteMarginMap E
        (nativeRestartNext (negIncrements X) E (-x) ω)) := by
    have hh := houtputs.comp (measurable_finiteMarginMap E)
    exact hh.map_eq
  have hae : (fun ω => finiteMarginMap E
      (nativeRestartNext (negIncrements X) E (-x) ω)) =ᵐ[μ]
      (fun ω => finiteMarginMap E (nativeRestartNext X E x ω)) := by
    filter_upwards [nativeRestartNext_neg_ae hX hi hG hE x] with ω hω
    simp only [finiteMarginMap, hω, abs_neg]
  rw [nativeRestartKernel_map_finiteMargin hX E (-x),
    nativeRestartKernel_map_finiteMargin hX E x]
  exact hmapout.trans (Measure.map_congr hae)

/-! ### The quotient kernel and its invariant-law pushforward -/

def nativeFiniteMarginKernel (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E : ℝ) : Kernel ℝ ℝ :=
  (nativeRestartKernel X μ E).map (finiteMarginMap E) |>.comap
    (finiteMarginSection E) (measurable_finiteMarginSection E)

theorem nativeFiniteMarginKernel_apply
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (_hX : ∀ n, Measurable (X n)) (E r : ℝ) :
    nativeFiniteMarginKernel X μ E r =
      (nativeRestartKernel X μ E (finiteMarginSection E r)).map (finiteMarginMap E) := by
  rw [nativeFiniteMarginKernel, Kernel.comap_apply]
  exact Kernel.map_apply _ (measurable_finiteMarginMap E) (finiteMarginSection E r)

theorem nativeFiniteMarginKernel_isMarkov
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ] [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (E : ℝ) :
    IsMarkovKernel (nativeFiniteMarginKernel X μ E) := by
  haveI : IsMarkovKernel (nativeRestartKernel X μ E) :=
    nativeRestartKernel_isMarkov hX E
  haveI : IsMarkovKernel ((nativeRestartKernel X μ E).map (finiteMarginMap E)) :=
    Kernel.IsMarkovKernel.map _ (measurable_finiteMarginMap E)
  exact Kernel.IsMarkovKernel.comap _ (measurable_finiteMarginSection E)

theorem nativeFiniteMarginKernel_at_image
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    (x : ℝ) :
    nativeFiniteMarginKernel X μ E (finiteMarginMap E x) =
      (nativeRestartKernel X μ E x).map (finiteMarginMap E) := by
  rw [nativeFiniteMarginKernel_apply hX E (finiteMarginMap E x)]
  have hs : finiteMarginSection E (finiteMarginMap E x) = |x| :=
    finiteMarginSection_apply_map E x
  rw [hs]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [← nativeRestartMarginLaw_neg_eq hX hi hG hE x]
    simp only [abs_of_nonpos hx]

theorem finiteMarginMap_range_subset (E : ℝ) :
    Set.range (finiteMarginMap E) ⊆ Iic E := by
  rintro r ⟨x, rfl⟩
  exact sub_le_self E (abs_nonneg x)

theorem nativeFiniteMarginLaw_invariant
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ] [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    (nativeFiniteMarginKernel X μ E).Invariant
      (π.map (finiteMarginMap E)) := by
  let P := nativeRestartKernel X μ E
  let φ := finiteMarginMap E
  let K := nativeFiniteMarginKernel X μ E
  have hφ : Measurable φ := measurable_finiteMarginMap E
  have hP : IsMarkovKernel P := nativeRestartKernel_isMarkov hX E
  change (π.map φ).bind K = π.map φ
  apply Measure.ext
  intro A hA
  have hpoint : ∀ x : ℝ, K (φ x) A = P x (φ ⁻¹' A) := by
    intro x
    have hsec : finiteMarginSection E (finiteMarginMap E x) = |x| :=
      finiteMarginSection_apply_map E x
    rw [show K = nativeFiniteMarginKernel X μ E from rfl,
      show P = nativeRestartKernel X μ E from rfl,
      nativeFiniteMarginKernel_apply hX E (finiteMarginMap E x),
      hsec, Measure.map_apply (measurable_finiteMarginMap E) hA]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx]
      have hsym := congrArg (fun m : Measure ℝ => m A)
        (nativeRestartMarginLaw_neg_eq hX hi hG hE x)
      rw [Measure.map_apply (measurable_finiteMarginMap E) hA,
        Measure.map_apply (measurable_finiteMarginMap E) hA] at hsym
      exact hsym
  have hKmeas : Measurable (fun r : ℝ => K r A) :=
    Kernel.measurable_coe K hA
  rw [Measure.bind_apply hA K.aemeasurable,
    Measure.map_apply hφ hA,
    lintegral_map hKmeas hφ,
    lintegral_congr_ae (Eventually.of_forall hpoint)]
  have hπA := congrArg (fun m : Measure ℝ => m (φ ⁻¹' A)) hπ
  rw [Measure.bind_apply (hA.preimage hφ) (Kernel.aemeasurable P)] at hπA
  exact hπA

end SwingRepair
