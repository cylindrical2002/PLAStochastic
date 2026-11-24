import PLAStochastic.ForMathlib.Analysis.Complex.Osgood
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Partial derivatives of holomorphic functions of two complex variables

* `differentiableOn_deriv_fst`: if `G` is holomorphic on an open set `U ⊆ ℂ²`, so is
  `(z, w) ↦ ∂_z G(z, w)` (Osgood; the difference quotients converge locally uniformly by the
  second-order Cauchy bound);
* `differentiableOn_iteratedDeriv_fst`: the same for `∂_zⁿ G`;
* `norm_iteratedDeriv_iteratedDeriv_le`: the polydisc Cauchy estimate
  `‖∂_w^k ∂_z^l G(z₀, w₀)‖ ≤ k! (l! B/(r₁/2)^l)/(r₂/2)^k` for `‖G‖ ≤ B` on
  `B(z₀, r₁) × B(w₀, r₂)`.
-/

noncomputable section

open Set Metric Filter Topology

namespace PGM

variable {G : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)}

theorem differentiableAt_slice_fst (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) {z w : ℂ}
    (h : ((z, w) : ℂ × ℂ) ∈ U) : DifferentiableAt ℂ (fun z' => G (z', w)) z :=
  DifferentiableAt.fun_comp' (g := G) (f := fun z' : ℂ => ((z', w) : ℂ × ℂ)) z
    ((hG _ h).differentiableAt (hU.mem_nhds h))
    (differentiableAt_id.prodMk (differentiableAt_const _))

theorem differentiableAt_slice_snd (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) {z w : ℂ}
    (h : ((z, w) : ℂ × ℂ) ∈ U) : DifferentiableAt ℂ (fun w' => G (z, w')) w :=
  DifferentiableAt.fun_comp' (g := G) (f := fun w' : ℂ => ((z, w') : ℂ × ℂ)) w
    ((hG _ h).differentiableAt (hU.mem_nhds h))
    ((differentiableAt_const _).prodMk differentiableAt_id)

theorem exists_ball_bound (hU : IsOpen U) (hG : ContinuousOn G U) {x₀ : ℂ × ℂ} (hx₀ : x₀ ∈ U) :
    ∃ r > 0, ∃ M : ℝ, ball x₀ (2 * r) ⊆ U ∧ ∀ x ∈ ball x₀ (2 * r), ‖G x‖ ≤ M := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hc : ContinuousAt G x₀ := hG.continuousAt (hU.mem_nhds hx₀)
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hc 1 one_pos
  refine ⟨min ε δ / 2, by positivity, ‖G x₀‖ + 1, ?_, ?_⟩
  · intro x hx; apply hεU; rw [mem_ball] at hx ⊢; linarith [min_le_left ε δ]
  · intro x hx
    rw [mem_ball] at hx
    have h1 := hδG (show dist x x₀ < δ by linarith [min_le_right ε δ])
    rw [dist_eq_norm] at h1
    have := norm_sub_norm_le (G x) (G x₀); linarith

theorem mem_ball_two_mul_fst {x₀ x : ℂ × ℂ} {r : ℝ} (hx : x ∈ ball x₀ r) {z : ℂ}
    (hz : z ∈ ball x.1 r) : ((z, x.2) : ℂ × ℂ) ∈ ball x₀ (2 * r) := by
  rw [mem_ball, Prod.dist_eq] at hx
  rw [mem_ball] at hz
  have h1 : dist x.1 x₀.1 < r := lt_of_le_of_lt (le_max_left _ _) hx
  have h2 : dist x.2 x₀.2 < r := lt_of_le_of_lt (le_max_right _ _) hx
  have h3 : dist z x₀.1 < 2 * r := by
    calc dist z x₀.1 ≤ dist z x.1 + dist x.1 x₀.1 := dist_triangle _ _ _
      _ < r + r := add_lt_add hz h1
      _ = 2 * r := by ring
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg h2
  rw [mem_ball, Prod.dist_eq]
  exact max_lt h3 (by simp only; linarith)

/-- Second-order control of the `z`-difference quotients. -/
theorem norm_slope_sub_deriv_fst_le (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) {x₀ : ℂ × ℂ}
    {r M : ℝ} (hr : 0 < r) (hsub : ball x₀ (2 * r) ⊆ U) (hM : ∀ x ∈ ball x₀ (2 * r), ‖G x‖ ≤ M)
    {x : ℂ × ℂ} (hx : x ∈ ball x₀ r) {h : ℂ} (h0 : h ≠ 0) (hh : ‖h‖ < r / 2) :
    ‖(G (x.1 + h, x.2) - G x) / h - deriv (fun z => G (z, x.2)) x.1‖ ≤ 32 * M / r ^ 2 * ‖h‖ := by
  set f : ℂ → ℂ := fun z => G (z, x.2) with hfdef
  have hf : DifferentiableOn ℂ f (ball x.1 r) := fun z hz =>
    (differentiableAt_slice_fst hU hG (hsub (mem_ball_two_mul_fst hx hz))).differentiableWithinAt
  have hfM : ∀ z ∈ ball x.1 r, ‖f z‖ ≤ M := fun z hz => hM _ (mem_ball_two_mul_fst hx hz)
  have hz : x.1 + h ∈ ball x.1 (r / 2) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hh
  have key := norm_sub_sub_deriv_le_of_ball hr hf hfM hz
  rw [add_sub_cancel_left] at key
  have hh0 : 0 < ‖h‖ := norm_pos_iff.mpr h0
  have hfx : f x.1 = G x := rfl
  have hfh : f (x.1 + h) = G (x.1 + h, x.2) := rfl
  have e : (G (x.1 + h, x.2) - G x) / h - deriv f x.1 =
      (f (x.1 + h) - f x.1 - deriv f x.1 * h) / h := by
    rw [hfx, hfh]; field_simp
  rw [e, norm_div, div_le_iff₀ hh0]
  calc _ ≤ 32 * M / r ^ 2 * ‖h‖ ^ 2 := key
    _ = 32 * M / r ^ 2 * ‖h‖ * ‖h‖ := by ring

/-- The `z`-difference quotients converge uniformly on `B(x₀, r)`. -/
theorem tendstoUniformlyOn_slope_fst (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) {x₀ : ℂ × ℂ}
    {r M : ℝ} (hr : 0 < r) (hsub : ball x₀ (2 * r) ⊆ U) (hM : ∀ x ∈ ball x₀ (2 * r), ‖G x‖ ≤ M) :
    TendstoUniformlyOn
      (fun (n : ℕ) (x : ℂ × ℂ) => (G (x.1 + ((r / (4 * (n + 1)) : ℝ) : ℂ), x.2) - G x) /
        ((r / (4 * (n + 1)) : ℝ) : ℂ))
      (fun x => deriv (fun z => G (z, x.2)) x.1) atTop (ball x₀ r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ (mem_ball_self (by positivity)))
  have ht : Tendsto (fun n : ℕ => 32 * M / r ^ 2 * (r / (4 * ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (32 * M / r ^ 2 * (r / 4))
    rw [mul_zero] at h1
    refine h1.congr fun n => ?_
    field_simp
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x hx
  have hpos : 0 < r / (4 * ((n : ℝ) + 1)) := by positivity
  have h0 : ((r / (4 * (n + 1)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  have hnorm : ‖((r / (4 * (n + 1)) : ℝ) : ℂ)‖ = r / (4 * (n + 1)) := by
    rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
  have hh : ‖((r / (4 * (n + 1)) : ℝ) : ℂ)‖ < r / 2 := by
    rw [hnorm, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [dist_comm, dist_eq_norm]
  calc _ ≤ 32 * M / r ^ 2 * ‖((r / (4 * (n + 1)) : ℝ) : ℂ)‖ :=
        norm_slope_sub_deriv_fst_le hU hG hr hsub hM hx h0 hh
    _ = 32 * M / r ^ 2 * (r / (4 * ((n : ℝ) + 1))) := by rw [hnorm]
    _ < ε := hn

/-- **Holomorphy of `∂_z G`.** -/
theorem differentiableOn_deriv_fst (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => deriv (fun z => G (z, x.2)) x.1) U := by
  have hlocal : ∀ x₀ ∈ U, ∃ r > 0,
      ContinuousOn (fun x : ℂ × ℂ => deriv (fun z => G (z, x.2)) x.1) (ball x₀ r) ∧
      DifferentiableOn ℂ (fun w => deriv (fun z => G (z, w)) x₀.1) (ball x₀.2 r) := by
    intro x₀ hx₀
    obtain ⟨r, hr, M, hsub, hM⟩ := exists_ball_bound hU hG.continuousOn hx₀
    have hT := tendstoUniformlyOn_slope_fst hU hG hr hsub hM
    have hsub1 : ball x₀ r ⊆ U := (ball_subset_ball (by linarith)).trans hsub
    have hhn : ∀ n : ℕ, ‖((r / (4 * (n + 1)) : ℝ) : ℂ)‖ < r := by
      intro n
      have hpos : 0 < r / (4 * ((n : ℝ) + 1)) := by positivity
      rw [Complex.norm_real, Real.norm_of_nonneg hpos.le, div_lt_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hmem : ∀ (n : ℕ), ∀ x ∈ ball x₀ r,
        ((x.1 + ((r / (4 * (n + 1)) : ℝ) : ℂ), x.2) : ℂ × ℂ) ∈ U := by
      intro n x hx
      refine hsub (mem_ball_two_mul_fst hx ?_)
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hhn n
    refine ⟨r, hr, ?_, ?_⟩
    · refine hT.continuousOn (Eventually.of_forall fun n => ?_).frequently
      have hc := hG.continuousOn
      refine ContinuousOn.div_const ?_ _
      refine ContinuousOn.sub ?_ (hc.mono hsub1)
      exact hc.comp (by fun_prop : Continuous fun x : ℂ × ℂ =>
        ((x.1 + ((r / (4 * (n + 1)) : ℝ) : ℂ), x.2) : ℂ × ℂ)).continuousOn
        (fun x hx => hmem n x hx)
    · have hmap : ball x₀.2 r ⊆ (fun w : ℂ => ((x₀.1, w) : ℂ × ℂ)) ⁻¹' ball x₀ r := by
        intro w hw
        simp only [mem_preimage, mem_ball, Prod.dist_eq, dist_self]
        rw [mem_ball] at hw
        exact max_lt hr hw
      have hT2 := (hT.comp fun w : ℂ => ((x₀.1, w) : ℂ × ℂ)).mono hmap
      refine hT2.tendstoLocallyUniformlyOn.differentiableOn
        (Eventually.of_forall fun n => ?_) isOpen_ball
      intro w hw
      have hw' : ((x₀.1, w) : ℂ × ℂ) ∈ ball x₀ r := hmap hw
      have h1 := differentiableAt_slice_snd hU hG (hmem n _ hw')
      have h2 := differentiableAt_slice_snd hU hG (hsub1 hw')
      exact ((h1.sub h2).div_const _).differentiableWithinAt
  refine osgood hU ?_ ?_ ?_
  · intro x hx
    obtain ⟨r, hr, hc, -⟩ := hlocal x hx
    exact (hc.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousWithinAt
  · intro x hx
    have hopen : IsOpen {z : ℂ | ((z, x.2) : ℂ × ℂ) ∈ U} := hU.preimage (by fun_prop)
    have hsl : DifferentiableOn ℂ (fun z => G (z, x.2)) {z : ℂ | ((z, x.2) : ℂ × ℂ) ∈ U} :=
      fun z hz => (differentiableAt_slice_fst hU hG hz).differentiableWithinAt
    exact ((hsl.deriv hopen) x.1 hx).differentiableAt (hopen.mem_nhds hx)
  · intro x hx
    obtain ⟨r, hr, -, hd⟩ := hlocal x hx
    exact (hd x.2 (mem_ball_self hr)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))

/-- **Holomorphy of `∂_zⁿ G`.** -/
theorem differentiableOn_iteratedDeriv_fst (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    (n : ℕ) : DifferentiableOn ℂ (fun x : ℂ × ℂ => iteratedDeriv n (fun z => G (z, x.2)) x.1) U := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero, Prod.mk.eta] using hG
  | succ n ih =>
    have := differentiableOn_deriv_fst hU ih
    simpa only [iteratedDeriv_succ] using this

/-- **Polydisc Cauchy estimate.** -/
theorem norm_iteratedDeriv_iteratedDeriv_le {z₀ w₀ : ℂ} {r₁ r₂ B : ℝ} (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hG : DifferentiableOn ℂ G (ball z₀ r₁ ×ˢ ball w₀ r₂))
    (hB : ∀ x ∈ ball z₀ r₁ ×ˢ ball w₀ r₂, ‖G x‖ ≤ B) (l k : ℕ) :
    ‖iteratedDeriv k (fun w => iteratedDeriv l (fun z => G (z, w)) z₀) w₀‖ ≤
      k.factorial * (l.factorial * B / (r₁ / 2) ^ l) / (r₂ / 2) ^ k := by
  have hU : IsOpen (ball z₀ r₁ ×ˢ ball w₀ r₂) := isOpen_ball.prod isOpen_ball
  have hJ := differentiableOn_iteratedDeriv_fst hU hG l
  apply norm_iteratedDeriv_le_of_ball k hr₂
  · intro w hw
    have hmem : ((z₀, w) : ℂ × ℂ) ∈ ball z₀ r₁ ×ˢ ball w₀ r₂ := ⟨mem_ball_self hr₁, hw⟩
    exact (differentiableAt_slice_snd hU hJ hmem).differentiableWithinAt
  · intro w hw
    apply norm_iteratedDeriv_le_of_ball l hr₁
    · intro z hz
      exact (differentiableAt_slice_fst hU hG (show ((z, w) : ℂ × ℂ) ∈ _ from ⟨hz, hw⟩)).differentiableWithinAt
    · intro z hz; exact hB _ ⟨hz, hw⟩

end PGM
