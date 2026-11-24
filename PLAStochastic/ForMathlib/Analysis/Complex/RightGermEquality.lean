import PLAStochastic.ForMathlib.Analysis.Complex.MixedPartialDeriv

/-! # Derivative equality from rightward values at a half-plane boundary -/

noncomputable section
open Complex Set Metric Filter Topology PowerSeries
namespace PGM

theorem deriv_eq_of_rightward_germ {F G : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (hG : DifferentiableAt ℂ G z)
    (he0 : F z = G z)
    (he : ∀ᶠ s : ℝ in 𝓝 0, 0 < s → F (z + (s : ℂ)) = G (z + (s : ℂ))) :
    deriv F z = deriv G z := by
  let s : ℕ → ℝ := fun n => 1 / (n + 1)
  have hs : Tendsto s atTop (𝓝 0) := by
    simpa only [s] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hs0 : ∀ n, 0 < s n := by intro n; dsimp [s]; positivity
  have hc : Tendsto (fun n => (s n : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall (fun n => Complex.ofReal_ne_zero.mpr (hs0 n).ne')⟩
    simpa [Function.comp_def] using (continuous_ofReal.tendsto (0 : ℝ)).comp hs
  have h₁ := hF.hasDerivAt.tendsto_slope_zero.comp hc
  have h₂ := hG.hasDerivAt.tendsto_slope_zero.comp hc
  have hEq : (fun n => (s n : ℂ)⁻¹ • (F (z + (s n : ℂ)) - F z)) =ᶠ[atTop]
      (fun n => (s n : ℂ)⁻¹ • (G (z + (s n : ℂ)) - G z)) := by
    filter_upwards [hs.eventually he] with n hn
    rw [hn (hs0 n), he0]
  exact tendsto_nhds_unique (h₁.congr' hEq) h₂

theorem complexTaylorSeries_frequency_jets_eq_of_right_values
    {F G : ℂ × ℂ → ℂ} {B : ℝ} (hB : 0 < B) {z : ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 B ×ˢ ball z B))
    (hG : DifferentiableOn ℂ G (ball 0 B ×ˢ ball z B))
    (N : ℕ) (he : ∀ w ∈ ball z B, 0 ≤ w.re → ∀ n ≤ N,
      coeff n (complexTaylorSeries (fun b => F (b, w)) 0) =
        coeff n (complexTaylorSeries (fun b => G (b, w)) 0))
    (hz : 0 ≤ z.re) : ∀ n ≤ N,
    coeff n (complexTaylorSeries (fun b => deriv (fun w => F (b, w)) z) 0) =
      coeff n (complexTaylorSeries (fun b => deriv (fun w => G (b, w)) z) 0) := by
  intro n hn
  have hU : IsOpen (ball (0 : ℂ) B ×ˢ ball z B) := isOpen_ball.prod isOpen_ball
  have hx : ((0, z) : ℂ × ℂ) ∈ ball (0 : ℂ) B ×ˢ ball z B := ⟨mem_ball_self hB, mem_ball_self hB⟩
  rw [← deriv_complexTaylorSeries_coeff_snd hU hF n hx,
    ← deriv_complexTaylorSeries_coeff_snd hU hG n hx]
  have hdf := differentiableAt_slice_snd hU (differentiableOn_iteratedDeriv_fst hU hF n) hx
  have hdg := differentiableAt_slice_snd hU (differentiableOn_iteratedDeriv_fst hU hG n) hx
  simp only [complexTaylorSeries, coeff_mk] at he ⊢
  apply deriv_eq_of_rightward_germ (hdf.const_mul ((n.factorial : ℂ)⁻¹)) (hdg.const_mul ((n.factorial : ℂ)⁻¹))
    (he z (mem_ball_self hB) hz n hn)
  have hmap : ContinuousAt (fun s : ℝ => z + (s : ℂ)) 0 := by fun_prop
  filter_upwards [hmap.eventually (show ball z B ∈ 𝓝 (z + ((0 : ℝ) : ℂ)) by simpa using ball_mem_nhds z hB)]
    with s hs hpos
  exact he (z + (s : ℂ)) hs (by simp only [add_re, ofReal_re]; linarith) n hn

end PGM
