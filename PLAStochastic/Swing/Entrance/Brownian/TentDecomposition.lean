import PLAStochastic.Swing.Entrance.Brownian.LawIndependence

/-!
# Gaussian decomposition of Brownian motion along a tent bump

For `r > 0` let `ξ = (2 B_{r/2} - B_r)/r` and `B^⊥_t = B_t - h_r(t) ξ`, with the tent bump
`h_r(t) = min(t, r - t)_+`. The covariance of `ξ` with `B_t` is `h_r(t)/r = Var(ξ) h_r(t)` and
`Var(ξ) = 1/r`. Hence `B^⊥` and `ξ` are jointly Gaussian and uncorrelated, so the whole residual
process is independent of `ξ`. On continuous paths, `B = B^⊥ + ξ h_r` as continuous paths, the
residual path is independent of `ξ` in the Borel path space, and the law of `ξ` is a
nondegenerate Gaussian, absolutely continuous with respect to Lebesgue measure.
-/

open MeasureTheory ProbabilityTheory Set Filter BrownianAffine
open scoped ENNReal NNReal Topology

namespace SwingRepair

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The tent coefficient `ξ = (2 B_{r/2} - B_r)/r`. -/
def tentCoefficient (B : ℝ≥0 → Ω → ℝ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  (2 / (r : ℝ)) * B (r / 2) ω - (1 / (r : ℝ)) * B r ω

/-- The residual process `B^⊥_t = B_t - h_r(t) ξ`. -/
def tentResidual (B : ℝ≥0 → Ω → ℝ) (r : ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω - tentBump r t * tentCoefficient B r ω

/-- The residual process and the coefficient are jointly Gaussian. -/
theorem tent_jointly_gaussian (hB : IsPreBrownianReal B μ) (r : ℝ≥0) :
    IsGaussianProcess (Sum.elim (tentResidual B r) (fun _ : Unit => tentCoefficient B r)) μ := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro i
  cases i with
  | inl t =>
    refine ⟨{t, r / 2, r},
      { toFun := fun x => x ⟨t, by simp⟩ - tentBump r t *
          ((2 / (r : ℝ)) * x ⟨r / 2, by simp⟩ - (1 / (r : ℝ)) * x ⟨r, by simp⟩)
        map_add' := by intro x y; simp only [Pi.add_apply]; ring
        map_smul' := by
          intro c x
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }, ?_⟩
    intro ω
    rfl
  | inr u =>
    refine ⟨{r / 2, r},
      { toFun := fun x => (2 / (r : ℝ)) * x ⟨r / 2, by simp⟩ - (1 / (r : ℝ)) * x ⟨r, by simp⟩
        map_add' := by intro x y; simp only [Pi.add_apply]; ring
        map_smul' := by
          intro c x
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }, ?_⟩
    intro ω
    rfl

theorem memLp_brownian_eval (hB : IsPreBrownianReal B μ) (t : ℝ≥0) : MemLp (B t) 2 μ :=
  (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two

theorem memLp_tentCoefficient (hB : IsPreBrownianReal B μ) (r : ℝ≥0) :
    MemLp (tentCoefficient B r) 2 μ :=
  ((memLp_brownian_eval hB _).const_mul _).sub ((memLp_brownian_eval hB _).const_mul _)

theorem covariance_tentCoefficient_eval (hB : IsPreBrownianReal B μ) {r : ℝ≥0} (hr : 0 < r)
    (t : ℝ≥0) : cov[tentCoefficient B r, B t; μ] = tentBump r t / r := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  unfold tentCoefficient
  rw [covariance_fun_sub_left ((memLp_brownian_eval hB _).const_mul _)
      ((memLp_brownian_eval hB _).const_mul _) (memLp_brownian_eval hB t),
    covariance_const_mul_left, covariance_const_mul_left, hB.covariance_eval,
    hB.covariance_eval, tentBump_apply]
  have hr' : (0 : ℝ) < r := hr
  have ht : (0 : ℝ) ≤ t := t.2
  push_cast
  rcases le_total (t : ℝ) (r / 2) with h1 | h1
  · rw [min_eq_right h1, min_eq_right (by linarith : (t : ℝ) ≤ r),
      min_eq_left (by linarith : (t : ℝ) ≤ r - t), max_eq_right ht]
    ring
  · rcases le_total (t : ℝ) r with h2 | h2
    · rw [min_eq_left h1, min_eq_right h2, min_eq_right (by linarith : (r : ℝ) - t ≤ t),
        max_eq_right (by linarith)]
      field_simp
    · rw [min_eq_left h1, min_eq_left h2, min_eq_right (by linarith : (r : ℝ) - t ≤ t),
        max_eq_left (by linarith)]
      field_simp
      ring

theorem covariance_tentCoefficient_self (hB : IsPreBrownianReal B μ) {r : ℝ≥0} (hr : 0 < r) :
    cov[tentCoefficient B r, tentCoefficient B r; μ] = 1 / r := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hξ := memLp_tentCoefficient hB r
  have hr' : (0 : ℝ) < r := hr
  calc cov[tentCoefficient B r, tentCoefficient B r; μ]
      = cov[tentCoefficient B r,
          fun ω => (2 / (r : ℝ)) * B (r / 2) ω - (1 / (r : ℝ)) * B r ω; μ] := rfl
    _ = (2 / (r : ℝ)) * cov[tentCoefficient B r, B (r / 2); μ] -
          (1 / (r : ℝ)) * cov[tentCoefficient B r, B r; μ] := by
        rw [covariance_fun_sub_right hξ ((memLp_brownian_eval hB _).const_mul _)
          ((memLp_brownian_eval hB _).const_mul _), covariance_const_mul_right,
          covariance_const_mul_right]
    _ = 1 / r := by
        rw [covariance_tentCoefficient_eval hB hr, covariance_tentCoefficient_eval hB hr,
          tentBump_of_le le_rfl]
        push_cast
        rw [tentBump_apply, show (r : ℝ) - r / 2 = r / 2 by ring, min_self,
          max_eq_right (by positivity)]
        field_simp
        ring

theorem variance_tentCoefficient (hB : IsPreBrownianReal B μ) {r : ℝ≥0} (hr : 0 < r) :
    Var[tentCoefficient B r; μ] = 1 / r :=
  (covariance_self (memLp_tentCoefficient hB r).aestronglyMeasurable.aemeasurable).symm.trans
    (covariance_tentCoefficient_self hB hr)

theorem covariance_tentResidual_coefficient (hB : IsPreBrownianReal B μ) {r : ℝ≥0} (hr : 0 < r)
    (t : ℝ≥0) : cov[tentResidual B r t, tentCoefficient B r; μ] = 0 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hξ := memLp_tentCoefficient hB r
  have hr' : (0 : ℝ) < r := hr
  unfold tentResidual
  rw [covariance_fun_sub_left (memLp_brownian_eval hB t) (hξ.const_mul _) hξ,
    covariance_const_mul_left, covariance_comm (X := B t), covariance_tentCoefficient_eval hB hr,
    covariance_tentCoefficient_self hB hr]
  field_simp
  ring

/-- The whole residual process is independent of the tent coefficient. -/
theorem tentResidual_indep_coefficient (hB : IsPreBrownianReal B μ) {r : ℝ≥0} (hr : 0 < r) :
    IndepFun (fun ω t => tentResidual B r t ω) (tentCoefficient B r) μ := by
  have hG := tent_jointly_gaussian hB r
  have hind := hG.indepFun_of_covariance_eq_zero
    (fun t => hG.aemeasurable (Sum.inl t)) (fun _ => hG.aemeasurable (Sum.inr ()))
    (fun t _ => covariance_tentResidual_coefficient hB hr t)
  have heval : Measurable (fun f : Unit → ℝ => f ()) := measurable_pi_apply ()
  simpa only [Function.comp_def, id_eq] using hind.comp measurable_id heval

/-! ## Path-level decomposition -/

omit [MeasurableSpace Ω] in
theorem continuous_tentResidual {ω : Ω} (hω : Continuous (B · ω)) (r : ℝ≥0) :
    Continuous (fun t => tentResidual B r t ω) :=
  hω.sub (((tentBump r).continuous.comp NNReal.continuous_coe).mul continuous_const)

theorem tentBump_coe_toNNReal (r t : ℝ) : tentBump r (t.toNNReal : ℝ) = tentBump r t := by
  rcases le_total 0 t with h | h
  · rw [Real.coe_toNNReal _ h]
  · rw [Real.toNNReal_of_nonpos h, NNReal.coe_zero, tentBump_of_nonpos r le_rfl,
      tentBump_of_nonpos r h]

omit [MeasurableSpace Ω] in
/-- On a continuous path, `B = B^⊥ + ξ h_r` as continuous paths. -/
theorem processPath_eq_tentResidual_add {ω : Ω} (hω : Continuous (B · ω)) (r : ℝ≥0) :
    processPath B ω =
      processPath (tentResidual B r) ω + tentCoefficient B r ω • tentBump r := by
  ext t
  rw [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, processPath_apply_real hω,
    processPath_apply_real (continuous_tentResidual hω r), tentResidual, tentBump_coe_toNNReal]
  ring

/-- The continuous-path representative of an a.e. continuous, coordinatewise a.e. measurable
process is a.e. measurable in the Borel path space. -/
theorem aemeasurable_processPath_of {C : ℝ≥0 → Ω → ℝ} (hm : ∀ t, AEMeasurable (C t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (C · ω)) : AEMeasurable (processPath C) μ := by
  apply measurableEmbedding_fullPathObservations.aemeasurable_comp_iff.mp
  apply (aemeasurable_pi_lambda _ (fun q : ℚ => hm (q : ℝ).toNNReal)).congr
  filter_upwards [hc] with ω hω
  funext q
  exact (processPath_apply_real hω q).symm

theorem aemeasurable_tentCoefficient (hB : IsPreBrownianReal B μ) (r : ℝ≥0) :
    AEMeasurable (tentCoefficient B r) μ :=
  ((hB.aemeasurable _).const_mul _).sub ((hB.aemeasurable _).const_mul _)

theorem aemeasurable_tentResidualPath (hB : IsBrownianReal B μ) (r : ℝ≥0) :
    AEMeasurable (processPath (tentResidual B r)) μ :=
  aemeasurable_processPath_of
    (fun t => (hB.aemeasurable t).sub
      ((aemeasurable_tentCoefficient hB.toIsPreBrownianReal r).const_mul _))
    (by filter_upwards [hB.cont] with ω hω; exact continuous_tentResidual hω r)

/-- The residual path is independent of the tent coefficient in the Borel path space. -/
theorem tentResidualPath_indep (hB : IsBrownianReal B μ) {r : ℝ≥0} (hr : 0 < r) :
    IndepFun (processPath (tentResidual B r)) (tentCoefficient B r) μ := by
  have hproj : Measurable (fun (F : ℝ≥0 → ℝ) (q : ℚ) => F (q : ℝ).toNNReal) :=
    measurable_pi_lambda _ (fun q => measurable_pi_apply _)
  have hs := (tentResidual_indep_coefficient hB.toIsPreBrownianReal hr).comp hproj measurable_id
  have hsp : IndepFun (fun ω => fullPathObservations (processPath (tentResidual B r) ω))
      (tentCoefficient B r) μ := by
    apply hs.congr _ EventuallyEq.rfl
    filter_upwards [hB.cont] with ω hω
    funext q
    exact (processPath_apply_real (continuous_tentResidual hω r) q).symm
  obtain ⟨F, hF, hFeq⟩ := measurableEmbedding_fullPathObservations.exists_measurable_extend
    (g := id) measurable_id (fun _ => ⟨(0 : C(ℝ, ℝ))⟩)
  have h := hsp.comp hF measurable_id
  simpa only [Function.comp_def, id_eq, show ∀ f, F (fullPathObservations f) = f from
    fun f => congrFun hFeq f] using h

/-- The law of the tent coefficient is a nondegenerate Gaussian, hence absolutely continuous. -/
theorem tentCoefficient_map_absolutelyContinuous (hB : IsPreBrownianReal B μ) {r : ℝ≥0}
    (hr : 0 < r) : μ.map (tentCoefficient B r) ≪ volume := by
  have hlaw : HasGaussianLaw (tentCoefficient B r) μ :=
    (tent_jointly_gaussian hB r).hasGaussianLaw_eval (Sum.inr ())
  rw [hlaw.map_eq_gaussianReal, variance_tentCoefficient hB hr]
  apply gaussianReal_absolutelyContinuous
  rw [Ne, Real.toNNReal_eq_zero, not_le]
  have hr' : (0 : ℝ) < r := hr
  positivity

end

end SwingRepair
