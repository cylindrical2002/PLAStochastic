import PLAStochastic.Swing.Gaussian.Bridge.ProductDensity

/-! The product density is the law of the bridge built from the actual iid increments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

def gaussianEndpointRemainder (X : ℕ → Ω → ℝ) (M N : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Ico M N, X i ω

theorem gaussianEndpointRemainder_measurable (hX : ∀ n, Measurable (X n)) (M N : ℕ) :
    Measurable (gaussianEndpointRemainder X M N) := by
  unfold gaussianEndpointRemainder
  fun_prop

omit mΩ in
theorem gaussianEndpointRemainder_add {M N : ℕ} (hMN : M ≤ N) (ω : Ω) :
    cumulativeSamples X M ω+gaussianEndpointRemainder X M N ω = cumulativeSamples X N ω :=
  Finset.sum_range_add_sum_Ico (fun i => X i ω) hMN

theorem gaussianEndpointRemainder_hasLaw
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (M N : ℕ) :
    HasLaw (gaussianEndpointRemainder X M N) (gaussianReal 0 ((N-M : ℕ) : ℝ≥0)) μ := by
  have hl := gaussian_weighted_sum_hasLaw hX hi hG (Finset.Ico M N) (fun _ => (1 : ℝ))
  simpa only [one_mul, one_pow, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
    mul_one, Real.toNNReal_natCast] using! hl

theorem gaussianPrefix_indep_remainder
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (M N : ℕ) :
    IndepFun (fun ω => fun i : Fin M => X i.val ω) (gaussianEndpointRemainder X M N) μ := by
  have hd : Disjoint (Finset.range M) (Finset.Ico M N) := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    exact not_lt_of_ge (Finset.mem_Ico.mp hk').1 (Finset.mem_range.mp hk)
  have hind := iIndepFun.indepFun_finset (Finset.range M) (Finset.Ico M N) hd hi hX
  let f : (Finset.range M → ℝ) → (Fin M → ℝ) := fun z i => z ⟨i.val, Finset.mem_range.mpr i.isLt⟩
  let g : (Finset.Ico M N → ℝ) → ℝ := fun z => ∑ i, z i
  have h := hind.comp (show Measurable f by fun_prop) (show Measurable g by fun_prop)
  have he : g ∘ (fun ω => fun i : Finset.Ico M N => X i.val ω) = gaussianEndpointRemainder X M N := by
    funext ω
    exact Finset.sum_coe_sort (Finset.Ico M N) (fun i => X i ω)
  rw [he] at h
  exact h

/-- The independent prefix/remainder decomposition uses the original iid process. -/
theorem gaussianPrefix_remainder_jointLaw
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (M N : ℕ) :
    HasLaw (fun ω => ((fun i : Fin M => X i.val ω), gaussianEndpointRemainder X M N ω))
      ((Measure.pi (fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 ((N-M : ℕ) : ℝ≥0))) μ := by
  have := hi.isProbabilityMeasure
  exact (gaussianPrefix_indep_remainder hX hi M N).hasLaw_prod
    (gaussianFiniteSamples_hasLaw hX hi hG M) (gaussianEndpointRemainder_hasLaw hX hi hG M N)

/-- The centered increment prefix appearing in the bridge density. -/
def gaussianBridgeIncrementPrefix (X : ℕ → Ω → ℝ) (N M : ℕ) (ω : Ω) : Fin M → ℝ :=
  fun i => gaussianBridgeIncrement X N i.val ω

theorem gaussianBridgeIncrementPrefix_measurable (hX : ∀ n, Measurable (X n)) (N M : ℕ) :
    Measurable (gaussianBridgeIncrementPrefix X N M) :=
  measurable_pi_lambda _ (fun i => gaussianBridgeIncrement_measurable hX N i.val)

/-- Exact endpoint factorization, with no conditional distribution assumed. -/
theorem gaussianBridgeIncrementPrefix_endpoint_density
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M N : ℕ} (hMN : M < N) :
    μ.map (fun ω => (gaussianBridgeIncrementPrefix X N M ω, cumulativeSamples X N ω)) =
      ((Measure.pi (fun _ : Fin M => gaussianReal 0 1)).withDensity
        (gaussianBridgeProductDensity M ((N-M : ℕ) : ℝ≥0))).prod (gaussianReal 0 (N : ℝ≥0)) := by
  have hr : (0 : ℝ≥0) < (N-M : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hMN)
  have hv : (M : ℝ≥0)+((N-M : ℕ) : ℝ≥0) = N := by exact_mod_cast (Nat.add_sub_of_le hMN.le)
  have ht : (M : ℝ)+((N-M : ℕ) : ℝ) = N := by exact_mod_cast (Nat.add_sub_of_le hMN.le)
  have hl : HasLaw (gaussianBridgeProductTransform M ((N-M : ℕ) : ℝ≥0))
      (((Measure.pi (fun _ : Fin M => gaussianReal 0 1)).withDensity
        (gaussianBridgeProductDensity M ((N-M : ℕ) : ℝ≥0))).prod (gaussianReal 0 (N : ℝ≥0)))
      ((Measure.pi (fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 ((N-M : ℕ) : ℝ≥0))) :=
    ⟨(gaussianBridgeProductTransform_measurable _ _).aemeasurable, by
      simpa only [hv] using gaussianBridgeProductTransform_map M hr⟩
  have he : gaussianBridgeProductTransform M ((N-M : ℕ) : ℝ≥0) ∘
      (fun ω => ((fun i : Fin M => X i.val ω), gaussianEndpointRemainder X M N ω)) =
      (fun ω => (gaussianBridgeIncrementPrefix X N M ω, cumulativeSamples X N ω)) := by
    funext ω
    have hs : ∑ i : Fin M, X i.val ω = cumulativeSamples X M ω :=
      Fin.sum_univ_eq_sum_range (fun i => X i ω) M
    dsimp only [Function.comp_def, gaussianBridgeProductTransform]
    rw [hs, gaussianEndpointRemainder_add hMN.le]
    simp only [NNReal.coe_natCast]
    rw [ht]
    rfl
  have h := (hl.comp (gaussianPrefix_remainder_jointLaw hX hi hG M N)).map_eq
  rw [he] at h
  exact h

/-- The actual Gaussian bridge prefix has the stated Radon-Nikodym density. -/
theorem gaussianBridgeIncrementPrefix_density
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M N : ℕ} (hMN : M < N) :
    μ.map (gaussianBridgeIncrementPrefix X N M) =
      (Measure.pi (fun _ : Fin M => gaussianReal 0 1)).withDensity
        (gaussianBridgeProductDensity M ((N-M : ℕ) : ℝ≥0)) := by
  have he := congrArg (Measure.map Prod.fst) (gaussianBridgeIncrementPrefix_endpoint_density hX hi hG hMN)
  rw [Measure.map_map measurable_fst
    ((gaussianBridgeIncrementPrefix_measurable hX N M).prodMk
      (show Measurable (cumulativeSamples X N) by unfold cumulativeSamples; fun_prop)),
    Measure.map_fst_prod, measure_univ, one_smul] at he
  exact he


/-- The exact density controls every measurable prefix event, not only one survival test. -/
theorem gaussianBridgeIncrementPrefix_measure_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M N : ℕ}
    (hMN : M < N) (hhalf : M ≤ N-M) :
    μ.map (gaussianBridgeIncrementPrefix X N M) ≤
      ENNReal.ofReal (Real.sqrt 2) • Measure.pi (fun _ : Fin M => gaussianReal 0 1) := by
  have hr : (0 : ℝ≥0) < (N-M : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hMN)
  rw [gaussianBridgeIncrementPrefix_density hX hi hG hMN, ← withDensity_const]
  apply withDensity_mono
  exact ae_of_all _ (fun z => gaussianBridgeProductDensity_le_sqrt_two M hr (by exact_mod_cast hhalf) z)

end SwingRepair
