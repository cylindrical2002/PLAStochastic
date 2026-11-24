import PLAStochastic.Swing.Gaussian.Survival.FiniteLikelihood

/-! The true Gaussian bridge and its endpoint are independent. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Centered increments of the bridge pinned at the actual time-N endpoint. -/
def gaussianBridgeIncrement (X : ℕ → Ω → ℝ) (N i : ℕ) (ω : Ω) : ℝ :=
  X i ω-cumulativeSamples X N ω/(N : ℝ)

/-- The actual pinned bridge position. -/
def gaussianBridgePosition (X : ℕ → Ω → ℝ) (N j : ℕ) (ω : Ω) : ℝ :=
  cumulativeSamples X j ω-(j : ℝ)/(N : ℝ)*cumulativeSamples X N ω

theorem gaussianBridgeIncrement_measurable (hX : ∀ n, Measurable (X n)) (N i : ℕ) :
    Measurable (gaussianBridgeIncrement X N i) := by
  unfold gaussianBridgeIncrement cumulativeSamples
  fun_prop

theorem gaussianBridgePosition_measurable (hX : ∀ n, Measurable (X n)) (N j : ℕ) :
    Measurable (gaussianBridgePosition X N j) := by
  unfold gaussianBridgePosition cumulativeSamples
  fun_prop

omit mΩ in
theorem gaussianBridgePosition_eq_sum (N j : ℕ) (ω : Ω) :
    gaussianBridgePosition X N j ω = ∑ i ∈ Finset.range j, gaussianBridgeIncrement X N i ω := by
  simp only [gaussianBridgePosition, gaussianBridgeIncrement, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold cumulativeSamples
  ring

theorem iid_standardGaussian_covariance
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (i j : ℕ) :
    covariance (X i) (X j) μ = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [covariance_self (hX i).aemeasurable, (iid_standardGaussian_mean_variance hX hG i).2, if_pos rfl]
  · rw [if_neg hij]
    exact (hi.indepFun hij).covariance_eq_zero
      (iid_standardGaussian_hasGaussianLaw hX hG i).memLp_two
      (iid_standardGaussian_hasGaussianLaw hX hG j).memLp_two

theorem gaussianIncrement_covariance_endpoint
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {N i : ℕ} (hiN : i < N) :
    covariance (X i) (cumulativeSamples X N) μ = 1 := by
  have := hi.isProbabilityMeasure
  change covariance (X i) (fun ω => ∑ j ∈ Finset.range N, X j ω) μ = 1
  rw [covariance_fun_sum_right'
    (fun j _ => (iid_standardGaussian_hasGaussianLaw hX hG j).memLp_two)
    (iid_standardGaussian_hasGaussianLaw hX hG i).memLp_two]
  simp only [iid_standardGaussian_covariance hX hi hG]
  simp [hiN]

theorem gaussianEndpoint_covariance
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (N : ℕ) :
    covariance (cumulativeSamples X N) (cumulativeSamples X N) μ = (N : ℝ) := by
  have := hi.isProbabilityMeasure
  have hW : MemLp (cumulativeSamples X N) 2 μ :=
    ((iid_standardGaussian_isGaussianProcess hX hi hG).hasGaussianLaw_fun_sum (I := Finset.range N)).memLp_two
  change covariance (fun ω => ∑ i ∈ Finset.range N, X i ω) (cumulativeSamples X N) μ = _
  rw [covariance_fun_sum_left'
    (fun i _ => (iid_standardGaussian_hasGaussianLaw hX hG i).memLp_two)
    hW]
  calc
    _ = ∑ _i ∈ Finset.range N, (1 : ℝ) := Finset.sum_congr rfl (fun i hiN =>
      gaussianIncrement_covariance_endpoint hX hi hG (Finset.mem_range.mp hiN))
    _ = _ := by simp

theorem gaussianBridgeIncrement_covariance_endpoint
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {N i : ℕ} (hiN : i < N) :
    covariance (gaussianBridgeIncrement X N i) (cumulativeSamples X N) μ = 0 := by
  have := hi.isProbabilityMeasure
  have hW : MemLp (cumulativeSamples X N) 2 μ :=
    ((iid_standardGaussian_isGaussianProcess hX hi hG).hasGaussianLaw_fun_sum
      (I := Finset.range N)).memLp_two
  have hD : MemLp (fun ω => cumulativeSamples X N ω/(N : ℝ)) 2 μ := by
    simpa only [div_eq_mul_inv, mul_comm] using hW.const_mul (N : ℝ)⁻¹
  change covariance (fun ω => X i ω-cumulativeSamples X N ω/(N : ℝ)) (cumulativeSamples X N) μ = 0
  rw [covariance_fun_sub_left (iid_standardGaussian_hasGaussianLaw hX hG i).memLp_two
    hD hW, covariance_fun_div_left,
    gaussianIncrement_covariance_endpoint hX hi hG hiN, gaussianEndpoint_covariance hX hi hG]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [div_self hN, sub_self]

/-- The full finite bridge vector and endpoint are jointly Gaussian by an actual linear map. -/
theorem gaussianBridgeIncrement_joint_gaussian
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (N : ℕ) :
    HasGaussianLaw (fun ω => ((fun i : Fin N => gaussianBridgeIncrement X N i.val ω),
      (fun _ : Unit => cumulativeSamples X N ω))) μ := by
  let S : (Fin N → ℝ) →L[ℝ] ℝ := ∑ i : Fin N, ContinuousLinearMap.proj i
  let L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) × (Unit → ℝ) :=
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i-(N : ℝ)⁻¹ • S)).prod
      (ContinuousLinearMap.pi (fun _ => S))
  have hg : HasGaussianLaw (fun ω => fun i : Fin N => X i.val ω) μ :=
    (iIndepFun.precomp Fin.val_injective hi).hasGaussianLaw
      (fun i => iid_standardGaussian_hasGaussianLaw hX hG i.val)
  apply (hg.map_fun L).congr
  apply ae_of_all
  intro ω
  have hs : S (fun i => X i.val ω) = cumulativeSamples X N ω := by
    simp only [S, sum_apply, ContinuousLinearMap.proj_apply]
    exact Fin.sum_univ_eq_sum_range (fun i => X i ω) N
  apply Prod.ext
  · funext i
    change X i.val ω-(N : ℝ)⁻¹*S (fun i => X i.val ω) = _
    rw [hs]
    unfold gaussianBridgeIncrement
    ring
  · funext i
    exact hs

/-- Orthogonality gives independence of the entire actual bridge, including every prefix. -/
theorem gaussianBridgeIncrement_indep_endpoint
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (N : ℕ) :
    IndepFun (fun ω => fun i : Fin N => gaussianBridgeIncrement X N i.val ω)
      (cumulativeSamples X N) μ := by
  have hind := (gaussianBridgeIncrement_joint_gaussian hX hi hG N).indepFun_of_covariance_eval
    (fun i _ => gaussianBridgeIncrement_covariance_endpoint hX hi hG i.isLt)
  simpa only [Function.comp_def, id_eq] using! hind.comp measurable_id
    (measurable_pi_apply ())


/-- Every actual position in a prefix of the pinned bridge. -/
def gaussianBridgePrefix (X : ℕ → Ω → ℝ) (N M : ℕ) (ω : Ω) : Fin (M+1) → ℝ :=
  fun j => gaussianBridgePosition X N j.val ω

theorem gaussianBridgePrefix_measurable (hX : ∀ n, Measurable (X n)) (N M : ℕ) :
    Measurable (gaussianBridgePrefix X N M) :=
  measurable_pi_lambda _ (fun j => gaussianBridgePosition_measurable hX N j.val)

theorem gaussianBridgePrefix_indep_endpoint
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {N M : ℕ} (hMN : M ≤ N) :
    IndepFun (gaussianBridgePrefix X N M) (cumulativeSamples X N) μ := by
  let f : (Fin N → ℝ) → (Fin (M+1) → ℝ) := fun z j =>
    cumulativeSamples (gaussianFiniteSamples N) j.val z
  have hf : Measurable f := by
    apply measurable_pi_lambda
    intro j
    apply Finset.measurable_sum
    intro k _
    exact gaussianFiniteSamples_measurable N k
  have he : f ∘ (fun ω => fun i : Fin N => gaussianBridgeIncrement X N i.val ω) =
      gaussianBridgePrefix X N M := by
    funext ω j
    dsimp only [Function.comp_def, f, gaussianBridgePrefix]
    rw [gaussianBridgePosition_eq_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k < j.val := Finset.mem_range.mp hk
    have hkN : k < N := lt_of_lt_of_le hkj (le_trans (Nat.le_of_lt_succ j.isLt) hMN)
    simp only [gaussianFiniteSamples, dif_pos hkN]
  have hind := (gaussianBridgeIncrement_indep_endpoint hX hi hG N).comp hf measurable_id
  rw [he] at hind
  simpa only [Function.comp_def, id_eq] using! hind

theorem gaussianEndpoint_hasLaw
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (N : ℕ) :
    HasLaw (cumulativeSamples X N) (gaussianReal 0 (N : ℝ≥0)) μ := by
  have hl := gaussian_weighted_sum_hasLaw hX hi hG (Finset.range N) (fun _ => (1 : ℝ))
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, Real.toNNReal_natCast] using! hl

/-- This product law is the endpoint-conditioning formula for the actual bridge prefix. -/
theorem gaussianBridgePrefix_endpoint_jointLaw
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {N M : ℕ} (hMN : M ≤ N) :
    μ.map (fun ω => (gaussianBridgePrefix X N M ω, cumulativeSamples X N ω)) =
      (μ.map (gaussianBridgePrefix X N M)).prod (gaussianReal 0 (N : ℝ≥0)) := by
  have := hi.isProbabilityMeasure
  have hP : HasLaw (gaussianBridgePrefix X N M) (μ.map (gaussianBridgePrefix X N M)) μ :=
    ⟨(gaussianBridgePrefix_measurable hX N M).aemeasurable, rfl⟩
  exact ((gaussianBridgePrefix_indep_endpoint hX hi hG hMN).hasLaw_prod hP
    (gaussianEndpoint_hasLaw hX hi hG N)).map_eq

end SwingRepair
