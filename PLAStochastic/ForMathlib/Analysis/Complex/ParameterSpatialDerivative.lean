import PLAStochastic.ForMathlib.Analysis.Complex.PartialDeriv

/-! # Continuous spatial derivatives of continuous holomorphic families

The parameter space need not carry a complex structure. Joint continuity
and holomorphy of each spatial slice give joint continuity of every actual
spatial derivative, via locally uniform difference quotients.
-/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

variable {E : Type*} [NormedAddCommGroup E]

private theorem exists_parameter_ball_bound {U : Set (E × ℂ)} (hU : IsOpen U)
    {G : E × ℂ → ℂ} (hG : ContinuousOn G U) {x₀ : E × ℂ} (hx₀ : x₀ ∈ U) :
    ∃ r > 0, ∃ M : ℝ, ball x₀ (2 * r) ⊆ U ∧ ∀ x ∈ ball x₀ (2 * r), ‖G x‖ ≤ M := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hc : ContinuousAt G x₀ := hG.continuousAt (hU.mem_nhds hx₀)
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hc 1 one_pos
  refine ⟨min ε δ / 2, by positivity, ‖G x₀‖ + 1, ?_, ?_⟩
  · intro x hx
    apply hεU
    rw [mem_ball] at hx ⊢
    linarith [min_le_left ε δ]
  · intro x hx
    rw [mem_ball] at hx
    have h1 := hδG (show dist x x₀ < δ by linarith [min_le_right ε δ])
    rw [dist_eq_norm] at h1
    linarith [norm_sub_norm_le (G x) (G x₀)]

private theorem parameter_spatial_mem_ball {x₀ x : E × ℂ} {r : ℝ}
    (hx : x ∈ ball x₀ r) {z : ℂ} (hz : z ∈ ball x.2 r) :
    (x.1, z) ∈ ball x₀ (2 * r) := by
  rw [mem_ball, Prod.dist_eq] at hx
  rw [mem_ball] at hz
  have h1 : dist x.1 x₀.1 < r := lt_of_le_of_lt (le_max_left _ _) hx
  have h2 : dist x.2 x₀.2 < r := lt_of_le_of_lt (le_max_right _ _) hx
  have h3 : dist z x₀.2 < 2 * r := by
    calc dist z x₀.2 ≤ dist z x.2 + dist x.2 x₀.2 := dist_triangle _ _ _
      _ < r + r := add_lt_add hz h2
      _ = 2 * r := by ring
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg h1
  rw [mem_ball, Prod.dist_eq]
  exact max_lt (by linarith) h3

theorem continuousOn_parameter_spatial_deriv {U : Set E} (hU : IsOpen U) {R : ℝ}
    {G : E → ℂ → ℂ} (hG : ContinuousOn (fun x : E × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    (hd : ∀ x ∈ U, DifferentiableOn ℂ (G x) (ball 0 R)) :
    ContinuousOn (fun x : E × ℂ => deriv (G x.1) x.2) (U ×ˢ ball 0 R) := by
  intro x₀ hx₀
  obtain ⟨r, hr, M, hsub, hM⟩ := exists_parameter_ball_bound (hU.prod isOpen_ball) hG hx₀
  let V : Set (E × ℂ) := ball x₀ r
  let q : ℕ → ℂ := fun n => ((r / (4 * ((n : ℝ) + 1)) : ℝ) : ℂ)
  have hqnorm : ∀ n, ‖q n‖ = r / (4 * ((n : ℝ) + 1)) := by
    intro n
    dsimp [q]
    rw [norm_real, Real.norm_of_nonneg (by positivity)]
  have hqsmall : ∀ n, ‖q n‖ < r / 2 := by
    intro n
    rw [hqnorm, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hqzero : ∀ n, q n ≠ 0 := fun n => norm_pos_iff.mp (by rw [hqnorm]; positivity)
  have hVsub : V ⊆ U ×ˢ ball 0 R := (ball_subset_ball (by linarith)).trans hsub
  have hshift : ∀ n, ∀ x ∈ V, (x.1, x.2 + q n) ∈ U ×ˢ ball 0 R := by
    intro n x hx
    apply hsub (parameter_spatial_mem_ball hx ?_)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (hqsmall n).trans (half_lt_self hr)
  have hquot : ∀ n, ContinuousOn (fun x : E × ℂ =>
      (G x.1 (x.2 + q n) - G x.1 x.2) / q n) V := by
    intro n
    exact ((hG.comp (by fun_prop : ContinuousOn
      (fun x : E × ℂ => (x.1, x.2 + q n)) V) (hshift n)).sub (hG.mono hVsub)).div_const _
  have hT : TendstoUniformlyOn (fun n (x : E × ℂ) =>
      (G x.1 (x.2 + q n) - G x.1 x.2) / q n)
        (fun x : E × ℂ => deriv (G x.1) x.2) atTop V := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ (mem_ball_self (by positivity)))
    have ht : Tendsto (fun n : ℕ => 32 * M / r ^ 2 * (r / (4 * ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (32 * M / r ^ 2 * (r / 4))
      rw [mul_zero] at h
      refine h.congr fun n => ?_
      field_simp
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x hx
    have hball : ball x.2 r ⊆ ball (0 : ℂ) R := fun ξ hξ =>
      (hsub (parameter_spatial_mem_ball hx hξ)).2
    have hd' : DifferentiableOn ℂ (G x.1) (ball x.2 r) := (hd x.1 (hVsub hx).1).mono hball
    have hbound : ∀ ξ ∈ ball x.2 r, ‖G x.1 ξ‖ ≤ M :=
      fun ξ hξ => hM _ (parameter_spatial_mem_ball hx hξ)
    have hmem : x.2 + q n ∈ ball x.2 (r / 2) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hqsmall n
    have hTaylor := norm_sub_sub_deriv_le_of_ball hr hd' hbound hmem
    rw [add_sub_cancel_left] at hTaylor
    have heq : (G x.1 (x.2 + q n) - G x.1 x.2) / q n - deriv (G x.1) x.2 =
        (G x.1 (x.2 + q n) - G x.1 x.2 - deriv (G x.1) x.2 * q n) / q n := by
      field_simp [hqzero n]
    rw [dist_comm, dist_eq_norm, heq, norm_div]
    calc
      _ ≤ 32 * M / r ^ 2 * ‖q n‖ := by
        rw [div_le_iff₀ (norm_pos_iff.mpr (hqzero n))]
        exact hTaylor.trans_eq (by ring)
      _ < ε := by rw [hqnorm]; exact hn
  have hc := hT.continuousOn (Eventually.of_forall hquot).frequently
  exact (hc.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousWithinAt

theorem continuousOn_parameter_iterated_spatial_deriv {U : Set E} (hU : IsOpen U) {R : ℝ}
    {G : E → ℂ → ℂ} (hG : ContinuousOn (fun x : E × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    (hd : ∀ x ∈ U, DifferentiableOn ℂ (G x) (ball 0 R)) (n : ℕ) :
    ContinuousOn (fun x : E × ℂ => iteratedDeriv n (G x.1) x.2) (U ×ˢ ball 0 R) := by
  have hdAll : ∀ n : ℕ, ∀ x ∈ U, DifferentiableOn ℂ (iteratedDeriv n (G x)) (ball 0 R) := by
    intro n x hx
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hd x hx
    | succ n ihd => simpa only [iteratedDeriv_succ] using ihd.deriv isOpen_ball
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hG
  | succ n ih =>
    have h := continuousOn_parameter_spatial_deriv (G := fun x => iteratedDeriv n (G x)) hU ih (hdAll n)
    simpa only [iteratedDeriv_succ] using h

end PGM
