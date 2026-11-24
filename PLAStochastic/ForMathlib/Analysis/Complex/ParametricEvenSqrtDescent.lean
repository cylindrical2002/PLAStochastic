import PLAStochastic.ForMathlib.Analysis.Complex.CompactAnalyticGermLift
import PLAStochastic.ForMathlib.Analysis.Complex.CircleEvenCauchy

/-! # Genuine joint square-coordinate descent of a local even analytic germ -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
private theorem pair_mem_ball_zero_right {p p₀ : E} {z : ℂ} {r : ℝ}
    (hp : p ∈ ball p₀ r) (hz : ‖z‖ < r) : (p, z) ∈ ball (p₀, (0 : ℂ)) r := by
  rw [mem_ball, dist_eq_norm, Prod.norm_def]
  change max ‖p - p₀‖ ‖z - 0‖ < r
  exact max_lt (by simpa only [mem_ball, dist_eq_norm] using! hp)
    (by simpa only [sub_zero] using! hz)

set_option maxHeartbeats 800000 in
/-- Local evenness in the scalar coordinate gives an actual analytic descent in
all parameters jointly, including the ramification point. -/
theorem analyticAt_parametric_even_sqrt {f : E × ℂ → ℂ} {p₀ : E}
    (hf : AnalyticAt ℂ f (p₀, 0))
    (heven : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), f (u.1, -u.2) = f u) :
    AnalyticAt ℂ (fun u : E × ℂ => f (u.1, Complex.sqrt u.2)) (p₀, 0) := by
  obtain ⟨ρ, hρ, hbρ⟩ := Metric.mem_nhds_iff.mp (hf.eventually_analyticAt.and heven)
  obtain ⟨H, hH, _, he⟩ := exists_analytic_parametric_compact_germ_lift (K := Circle) hf
  obtain ⟨δ, hδ, hbδ⟩ := Metric.mem_nhds_iff.mp (hH.eventually_analyticAt.and he)
  let R : ℝ := min δ ρ / 4
  have hR : 0 < R := div_pos (lt_min hδ hρ) (by norm_num)
  have hRδ : R < δ := by
    have hm := min_le_left δ ρ
    dsimp only [R]
    linarith
  have hRρ : R < ρ := by
    have hm := min_le_right δ ρ
    dsimp only [R]
    linarith
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  have hnR : ‖(R : ℂ)‖ = R := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  let S : C(Circle, ℂ) := (R : ℂ) • circleTraceCoord
  have hSn : ‖S‖ = R := by
    simp only [S, norm_smul, hnR, circleTraceCoord_norm, mul_one]
  have hSp : (p₀, S) ∈ ball (p₀, (0 : C(Circle, ℂ))) δ := by
    rw [mem_ball, dist_eq_norm, Prod.norm_def]
    change max ‖p₀ - p₀‖ ‖S - 0‖ < δ
    simpa only [sub_self, norm_zero, sub_zero, hSn] using max_lt hδ hRδ
  have hHS : AnalyticAt ℂ H (p₀, S) := (hbδ hSp).1
  let X : E → C(Circle, ℂ) := fun p => H (p, S)
  have hX : AnalyticAt ℂ X p₀ := hHS.comp (x := p₀) (f := fun p : E => (p, S))
    (analyticAt_id.prod analyticAt_const)
  have heX : ∀ᶠ p in 𝓝 p₀, ∀ z : Circle, X p z = f (p, (R : ℂ) * z) := by
    filter_upwards [ball_mem_nhds p₀ hR] with p hp
    have hmem : (p, S) ∈ ball (p₀, (0 : C(Circle, ℂ))) δ := by
      rw [mem_ball, dist_eq_norm, Prod.norm_def]
      change max ‖p - p₀‖ ‖S - 0‖ < δ
      have hpn : ‖p - p₀‖ < R := by simpa only [mem_ball, dist_eq_norm] using! hp
      simpa only [sub_zero, hSn] using max_lt (hpn.trans hRδ) hRδ
    intro z
    simpa only [X, S, ContinuousMap.smul_apply, smul_eq_mul, circleTraceCoord] using!
      (hbδ hmem).2 z
  let D : E × ℂ → ℂ := fun u => circleTraceEvenCauchy (X u.1) (u.2 / (R : ℂ) ^ 2)
  have hX' : AnalyticAt ℂ (fun u : E × ℂ => X u.1) (p₀, 0) :=
    hX.comp (x := (p₀, (0 : ℂ))) (f := (Prod.fst : E × ℂ → E)) analyticAt_fst
  have hq' : AnalyticAt ℂ (fun u : E × ℂ => u.2 / (R : ℂ) ^ 2) (p₀, 0) :=
    analyticAt_snd.div analyticAt_const (pow_ne_zero 2 hRc)
  have hD : AnalyticAt ℂ D (p₀, 0) := by
    have hC : AnalyticAt ℂ (fun v : C(Circle, ℂ) × ℂ => circleTraceEvenCauchy v.1 v.2)
        (X p₀, (0 : ℂ) / (R : ℂ) ^ 2) := by
      simpa only [zero_div] using circleTraceEvenCauchy_analyticAt (X p₀)
    have h := hC.comp (x := (p₀, (0 : ℂ)))
      (f := fun u : E × ℂ => (X u.1, u.2 / (R : ℂ) ^ 2)) (hX'.prod hq')
    simpa only [zero_div] using! h
  apply hD.congr
  have htp : Tendsto (Prod.fst : E × ℂ → E) (𝓝 (p₀, (0 : ℂ))) (𝓝 p₀) :=
    continuousAt_fst.tendsto
  have htq : Tendsto (Prod.snd : E × ℂ → ℂ) (𝓝 (p₀, (0 : ℂ))) (𝓝 (0 : ℂ)) :=
    continuousAt_snd.tendsto
  filter_upwards [htp.eventually heX, htp.eventually (ball_mem_nhds p₀ hR),
    htq.eventually (ball_mem_nhds (0 : ℂ) (sq_pos_of_pos hR))] with u hXu hpu hqu
  have hnq : ‖u.2‖ < R ^ 2 := by simpa only [mem_ball, dist_eq_norm, sub_zero] using! hqu
  have hs : ‖Complex.sqrt u.2‖ < R := norm_sqrt_lt hR hnq
  let a : ℂ := Complex.sqrt u.2 / (R : ℂ)
  have ha : ‖a‖ < 1 := by
    rw [show ‖a‖ = ‖Complex.sqrt u.2‖ / R by simp only [a, norm_div, hnR]]
    exact (div_lt_one₀ hR).mpr hs
  have hsq : a ^ 2 = u.2 / (R : ℂ) ^ 2 := by simp only [a, div_pow, sqrt_sq_eq]
  have hq : ‖u.2 / (R : ℂ) ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, hnR]
    exact (div_lt_one₀ (sq_pos_of_pos hR)).mpr hnq
  have hRa : (R : ℂ) * a = Complex.sqrt u.2 := by
    dsimp only [a]
    field_simp
  let g : ℂ → ℂ := fun z => f (u.1, (R : ℂ) * z)
  have hg : DifferentiableOn ℂ g (closedBall 0 1) := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have hzR : ‖(R : ℂ) * z‖ < ρ := by
      rw [norm_mul, hnR]
      exact (mul_le_of_le_one_right (le_of_lt hR) hzn).trans_lt hRρ
    have hpair := pair_mem_ball_zero_right ((ball_subset_ball (le_of_lt hRρ)) hpu) hzR
    have hfa : AnalyticAt ℂ (fun t : ℂ => f (u.1, t)) ((R : ℂ) * z) :=
      (hbρ hpair).1.curry_right
    exact (hfa.comp (x := z) (f := fun t : ℂ => (R : ℂ) * t)
      (analyticAt_const.mul analyticAt_id)).differentiableAt.differentiableWithinAt
  have heva : g (-a) = g a := by
    have hev := (hbρ (pair_mem_ball_zero_right
      ((ball_subset_ball (le_of_lt hRρ)) hpu) (hs.trans hRρ))).2
    simpa only [g, mul_neg, hRa] using hev
  have hid := circleTraceEvenCauchy_eq_of_square hg hq ha hsq hXu heva
  simpa only [D, g, hRa] using hid

end PGM
