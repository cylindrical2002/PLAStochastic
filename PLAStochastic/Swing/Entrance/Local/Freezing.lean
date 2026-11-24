import PLAStochastic.Swing.Entrance.Local.CutStopping
import PLAStochastic.ForMathlib.Probability.Process.IIDRestart.FutureSequence
import PLAStochastic.Swing.DenseSampling.CarriedPrefix.StoppedHistoryConditional
import PLAStochastic.Swing.Gaussian.ZeroLadder.StrictLadderLaw

/-!
# Freezing the past at the cut

Let `κ = τ - 1` be the cut index (`entranceCutIndex`) and `𝓕_τ` its stopped σ-algebra
(`entranceCutSigma`). The increments after the cut are `X_{τ+j} = X_{κ+1+j}`, and the
side `s = entranceSide` at the cut is `𝓕_τ`-measurable with values `±1`.

* (G4) The reflected future `ξ_j = s X_{τ+j}` is again an iid standard Gaussian sequence and is
  independent of `𝓕_τ` (`entranceReflectedFuture_identDistrib`, `entranceReflectedFuture_map`,
  `entranceReflectedFuture_indep`).
* On `{τ < ∞}` the local residual after the cut is the walk with increments `ξ` and drift
  `-b`, `b = s β` (`entranceLocal_eq_driftPath`); its crossing quantities are the crossing pair
  of `(D, b, ξ)` with `D` the cut width.
* Freezing lemma: for an `𝓕_τ`-measurable `Z` and a bounded measurable `G`,
  `E[G(Z, ξ) | 𝓕_τ] = ∫ G(Z, X(η)) dμ(η)` almost surely (`entrance_condExp_freeze`).
* The conditional law of the local residual given `𝓕_τ` is the law of the Gaussian walk with
  the frozen drift `-b` (`entranceLocal_condExp`).
-/

namespace SwingRepair

noncomputable section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The stopped σ-algebra `𝓕_τ` of the cut. -/
abbrev entranceCutSigma (hX : ∀ k, Measurable (X k)) (E : ℝ) : MeasurableSpace Ω :=
  (entranceCutIndex_isStoppingTime hX E).measurableSpace

/-- The side `s` at the cut. -/
def entranceCutSide (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  entranceSide (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E)

/-- The cut width `D = τ (b_τ - a_τ)`. -/
def entranceCutWidth (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  entranceWidth (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E)

/-- The reflected frozen slope `b = s β` at the cut: the local residual has drift `-b`. -/
def entranceCutDrift (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  entranceCutSide X E ω *
    entranceFrozenSlope (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E)

/-- The increments after the cut, `X_{τ+j} = X_{κ+1+j}`. -/
def entranceFuture (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) (j : ℕ) : ℝ :=
  X ((entranceCutIndex X E ω).untopD 0 + 1 + j) ω

/-- The reflected increments after the cut, `ξ_j = s X_{τ+j}`. -/
def entranceReflectedFuture (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) (j : ℕ) : ℝ :=
  entranceCutSide X E ω * entranceFuture X E ω j

/-! ## Measurability -/

section Measurability

variable (hX : ∀ k, Measurable (X k)) (E : ℝ)
include hX

theorem measurable_entranceCutSide :
    Measurable[entranceCutSigma hX E] (entranceCutSide X E) :=
  measurable_entranceSide_cut hX E

theorem measurable_entranceCutWidth :
    Measurable[entranceCutSigma hX E] (entranceCutWidth X E) :=
  measurable_entranceWidth_cut hX E

theorem measurable_entranceCutDrift :
    Measurable[entranceCutSigma hX E] (entranceCutDrift X E) :=
  (measurable_entranceSide_cut hX E).mul (measurable_entranceFrozenSlope_cut hX E)

theorem measurable_entranceFuture : Measurable (entranceFuture X E) :=
  stoppedSequence_measurable hX (entranceCutIndex_isStoppingTime hX E)

theorem measurable_entranceReflectedFuture : Measurable (entranceReflectedFuture X E) := by
  have hs : Measurable (entranceCutSide X E) :=
    (measurable_entranceCutSide hX E).mono (entranceCutIndex_isStoppingTime hX E).measurableSpace_le
      le_rfl
  exact measurable_pi_lambda _ fun j =>
    hs.mul ((measurable_pi_apply j).comp (measurable_entranceFuture hX E))

end Measurability

/-! ## The reflected future is a fresh iid Gaussian sequence (G4) -/

/-- Reflection preserves the law of the iid standard Gaussian sequence. -/
theorem neg_sequence_map_eq (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1) :
    μ.map (fun ω j => -X j ω) = μ.map (fun ω j => X j ω) := by
  have hneg : iIndepFun (fun j ω => -X j ω) μ := hi.comp (fun _ x => -x) (fun _ => measurable_neg)
  have h1 := hneg.map_fun_eq_infinitePi_map (fun j => (hX j).neg)
  have h2 := hi.map_fun_eq_infinitePi_map hX
  have h3 : (Measure.infinitePi fun j => μ.map (fun ω => -X j ω)) =
      Measure.infinitePi fun j => μ.map (X j) := by
    congr 1
    funext j
    rw [gaussianIncrement_reflected_law hX hG j, hG j]
  exact h1.trans (h3.trans h2.symm)

section Restart

variable (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
  (hG : ∀ k, μ.map (X k) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E)
include hX hi hG hE

theorem entranceReflectedFuture_inter_measure {A : Set Ω}
    (hA : MeasurableSet[entranceCutSigma hX E] A) {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    μ (A ∩ entranceReflectedFuture X E ⁻¹' B) = μ A * μ ((fun ω j => X j ω) ⁻¹' B) := by
  have := hi.isProbabilityMeasure
  have hκ := entranceCutIndex_isStoppingTime hX E
  have hfin := entranceCutIndex_ae_ne_top hX hi hG hE
  have hid := gaussianIncrements_identDistrib hX hG
  let S : Set Ω := {ω | entranceCutSide X E ω = 1}
  have hS : MeasurableSet[entranceCutSigma hX E] S :=
    measurableSet_eq_fun (measurable_entranceCutSide hX E) measurable_const
  let N : (ℕ → ℝ) → (ℕ → ℝ) := fun x j => -x j
  have hN : Measurable N := measurable_pi_lambda _ fun j => (measurable_pi_apply j).neg
  have hfut : Measurable (entranceFuture X E) := measurable_entranceFuture hX E
  have hsplit : A ∩ entranceReflectedFuture X E ⁻¹' B =
      ((A ∩ S) ∩ entranceFuture X E ⁻¹' B) ∪ ((A \ S) ∩ entranceFuture X E ⁻¹' (N ⁻¹' B)) := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_union, mem_sdiff, S, mem_ofPred_eq]
    have hrefl : entranceReflectedFuture X E ω =
        fun j => entranceCutSide X E ω * entranceFuture X E ω j := rfl
    rcases entranceSide_eq_one_or (y := entrancePath X ω) (E := E) (entranceCutNat (entrancePath X ω) E)
      with h1 | h1
    · have h1' : entranceCutSide X E ω = 1 := h1
      rw [hrefl, h1']
      simp only [one_mul]
      tauto
    · have h1' : entranceCutSide X E ω = -1 := h1
      have hNf : N (entranceFuture X E ω) = fun j => -1 * entranceFuture X E ω j := by
        funext j
        simp [N]
      rw [hrefl, h1', ← hNf]
      have : (-1 : ℝ) ≠ 1 := by norm_num
      tauto
  have hdisj : Disjoint ((A ∩ S) ∩ entranceFuture X E ⁻¹' B)
      ((A \ S) ∩ entranceFuture X E ⁻¹' (N ⁻¹' B)) := by
    rw [Set.disjoint_left]
    rintro ω ⟨⟨_, h1⟩, _⟩ ⟨⟨_, h2⟩, _⟩
    exact h2 h1
  have hAS : MeasurableSet[entranceCutSigma hX E] (A ∩ S) := hA.inter hS
  have hAS' : MeasurableSet[entranceCutSigma hX E] (A \ S) := hA.diff hS
  have h1 := stoppedSequence_inter_measure hX hi hid hκ hfin hAS hB
  have h2 := stoppedSequence_inter_measure hX hi hid hκ hfin hAS' (hN hB)
  have hlaw : μ ((fun ω j => X j ω) ⁻¹' (N ⁻¹' B)) = μ ((fun ω j => X j ω) ⁻¹' B) := by
    have hm : Measurable fun ω (j : ℕ) => X j ω := measurable_pi_lambda _ hX
    have hneg : Measurable fun ω (j : ℕ) => -X j ω := measurable_pi_lambda _ fun j => (hX j).neg
    have := congrArg (fun ν : Measure (ℕ → ℝ) => ν B) (neg_sequence_map_eq hX hi hG)
    simp only [Measure.map_apply hneg hB, Measure.map_apply hm hB] at this
    exact this
  rw [hsplit, measure_union hdisj ((hκ.measurableSpace_le _ hAS').inter (hfut (hN hB)))]
  change μ ((A ∩ S) ∩ entranceFuture X E ⁻¹' B) +
    μ ((A \ S) ∩ entranceFuture X E ⁻¹' (N ⁻¹' B)) = _
  have e1 : μ ((A ∩ S) ∩ entranceFuture X E ⁻¹' B) =
      μ (A ∩ S) * μ ((fun ω j => X j ω) ⁻¹' B) := h1
  have e2 : μ ((A \ S) ∩ entranceFuture X E ⁻¹' (N ⁻¹' B)) =
      μ (A \ S) * μ ((fun ω j => X j ω) ⁻¹' B) := h2.trans (by rw [hlaw])
  rw [e1, e2, ← add_mul, measure_inter_add_sdiff _ (hκ.measurableSpace_le _ hS)]

/-- (G4) The reflected increments after the cut are an iid standard Gaussian sequence. -/
theorem entranceReflectedFuture_identDistrib :
    IdentDistrib (entranceReflectedFuture X E) (fun ω j => X j ω) μ μ := by
  have := hi.isProbabilityMeasure
  refine ⟨(measurable_entranceReflectedFuture hX E).aemeasurable,
    (measurable_pi_lambda _ hX).aemeasurable, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_entranceReflectedFuture hX E) hB,
    Measure.map_apply (measurable_pi_lambda _ hX) hB]
  simpa using entranceReflectedFuture_inter_measure hX hi hG hE MeasurableSet.univ hB

/-- (G4) The reflected increments after the cut are independent of the stopped σ-algebra. -/
theorem entranceReflectedFuture_indep :
    Indep (MeasurableSpace.comap (entranceReflectedFuture X E) inferInstance)
      (entranceCutSigma hX E) μ := by
  apply (Indep_iff _ _ μ).mpr
  intro C A hC hA
  rcases hC with ⟨B, hB, rfl⟩
  rw [Set.inter_comm, entranceReflectedFuture_inter_measure hX hi hG hE hA hB,
    (entranceReflectedFuture_identDistrib hX hi hG hE).measure_mem_eq hB, mul_comm]

/-- Freezing lemma: given the stopped σ-algebra, a bounded functional of an
`𝓕_τ`-measurable state and the reflected future integrates the future against the original
iid law. -/
theorem entrance_condExp_freeze {β : Type*} [MeasurableSpace β] {Z : Ω → β}
    (hZ : Measurable[entranceCutSigma hX E] Z) {G : β × (ℕ → ℝ) → ℝ} (hGm : Measurable G)
    {C : ℝ} (hC : ∀ p, |G p| ≤ C) :
    μ[fun ω => G (Z ω, entranceReflectedFuture X E ω) | entranceCutSigma hX E] =ᵐ[μ]
      fun ω => ∫ η, G (Z ω, fun j => X j η) ∂μ := by
  have := hi.isProbabilityMeasure
  have hκ := entranceCutIndex_isStoppingTime hX E
  have hC' : ∀ p, |G p| ≤ max C 0 := fun p => (hC p).trans (le_max_left _ _)
  have hF : @Measurable (Ω × (ℕ → ℝ)) ℝ ((entranceCutSigma hX E).prod inferInstance) _
      (fun p => G (Z p.1, p.2)) :=
    hGm.comp ((hZ.comp measurable_fst).prodMk measurable_snd)
  have h := condExp_history_independent_integral hκ.measurableSpace_le
    (measurable_entranceReflectedFuture hX E).aemeasurable
    (entranceReflectedFuture_indep hX hi hG hE) hF (le_max_right C 0) (fun p => hC' _)
  refine h.trans (Filter.Eventually.of_forall fun ω => ?_)
  change ∫ y, G (Z ω, y) ∂(μ.map (entranceReflectedFuture X E)) = _
  have hm : Measurable fun η (j : ℕ) => X j η := measurable_pi_lambda _ hX
  rw [(entranceReflectedFuture_identDistrib hX hi hG hE).map_eq]
  exact integral_map hm.aemeasurable (f := fun y => G (Z ω, y))
    (hGm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

/-- Set-integral form of the freezing lemma. -/
theorem entrance_setIntegral_freeze {β : Type*} [MeasurableSpace β] {Z : Ω → β}
    (hZ : Measurable[entranceCutSigma hX E] Z) {G : β × (ℕ → ℝ) → ℝ} (hGm : Measurable G)
    {C : ℝ} (hC : ∀ p, |G p| ≤ C) {A : Set Ω} (hA : MeasurableSet[entranceCutSigma hX E] A) :
    ∫ ω in A, G (Z ω, entranceReflectedFuture X E ω) ∂μ =
      ∫ ω in A, (∫ η, G (Z ω, fun j => X j η) ∂μ) ∂μ := by
  have := hi.isProbabilityMeasure
  have hκ := entranceCutIndex_isStoppingTime hX E
  have hZm : Measurable Z := hZ.mono hκ.measurableSpace_le le_rfl
  have hint : Integrable (fun ω => G (Z ω, entranceReflectedFuture X E ω)) μ :=
    Integrable.of_bound
      (hGm.comp (hZm.prodMk (measurable_entranceReflectedFuture hX E))).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hC (Z ω, entranceReflectedFuture X E ω))
  rw [← setIntegral_condExp hκ.measurableSpace_le hint hA]
  exact setIntegral_congr_ae (hκ.measurableSpace_le _ hA)
    ((entrance_condExp_freeze hX hi hG hE hZ hGm hC).mono fun ω h _ => h)

end Restart

/-! ## The local residual is the frozen-drift walk of the reflected future -/

omit mΩ in
theorem cumulativeSamples_add_sub (X : ℕ → Ω → ℝ) (n j : ℕ) (ω : Ω) :
    cumulativeSamples X (n + j) ω - cumulativeSamples X n ω = ∑ i ∈ Finset.range j, X (n + i) ω := by
  simp only [cumulativeSamples, Finset.sum_range_add, add_sub_cancel_left]

omit mΩ in
/-- On `{τ < ∞}` the local residual after the cut is the walk with the reflected increments and
the frozen drift. -/
theorem entranceLocal_eq_driftPath {X : ℕ → Ω → ℝ} {E : ℝ} {ω : Ω}
    (hω : entranceCutIndex X E ω ≠ ⊤) :
    entranceLocal (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E) =
      driftPath (entranceReflectedFuture X E ω) (entranceCutDrift X E ω) := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hω
  have hn := entranceCutNat_of_index hk.symm
  funext j
  have hfut : ∀ i, entranceFuture X E ω i = X (k + 1 + i) ω := by
    intro i
    simp only [entranceFuture, ← hk, WithTop.untopD_coe]
  simp only [entranceLocal, driftPath, entranceReflectedFuture, entranceCutDrift, entranceCutSide,
    hfut, hn, entrancePath, cumulativeSamples_add_sub, ← Finset.mul_sum]

omit mΩ in
/-- On `{τ < ∞}` the entrance pair is the crossing pair of the frozen width and drift and the
reflected future. -/
theorem entrancePair_eq_crossingPair {X : ℕ → Ω → ℝ} {E : ℝ} {ω : Ω}
    (hω : entranceCutIndex X E ω ≠ ⊤) :
    (entranceUndershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E),
        entranceOvershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E)) =
      crossingPair (entranceCutWidth X E ω) (entranceCutDrift X E ω)
        (entranceReflectedFuture X E ω) := by
  rw [entranceUndershoot_eq_levelUndershoot, entranceOvershoot_eq_levelOvershoot, entranceLocal_eq_driftPath hω]
  rfl

omit mΩ in
theorem entranceCrossing_eq_driftCrossing {X : ℕ → Ω → ℝ} {E : ℝ} {ω : Ω}
    (hω : entranceCutIndex X E ω ≠ ⊤) :
    entranceCrossing (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E) =
      levelCrossing (driftPath (entranceReflectedFuture X E ω) (entranceCutDrift X E ω))
        (entranceCutWidth X E ω) := by
  rw [entranceCrossing_eq_levelCrossing, entranceLocal_eq_driftPath hω]
  rfl

end

end SwingRepair
