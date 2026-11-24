import PLAStochastic.Index.CEPS.Scaled.CanonJetPolynomial
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesCongr

/-! # Finite canonical mixed jets along small complex-scale curves -/

noncomputable section
open Complex Set Metric MeasureTheory Finset Filter Topology Asymptotics PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCanonDriftTaylor_rect_curve_isBigO {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q ζ : ℂ → ℂ} (hμ : ContinuousAt μ 0)
    (hq : Tendsto q (𝓝 0) (𝓝 0)) (hζ : Tendsto ζ (𝓝 0) (𝓝 0))
    (hqo : q =O[𝓝 (0 : ℂ)] fun b => b) (hζo : ζ =O[𝓝 (0 : ℂ)] fun b => b) :
    (fun b => cepsCanonDriftTaylor dom ρW N (μ b) (q b) (ζ b) -
      cepsCanonDriftRectTaylor dom ρW N (μ b) (q b) (ζ b))
      =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
  have hterms : ∀ j ∈ range (N + 1),
      (fun b => (j.factorial : ℂ)⁻¹ * (μ b) ^ j *
        (cepsCanonDriftCoeff dom ρW j (q b) (ζ b) -
          bivariateTaylorSum (cepsCanonDriftCoeff dom ρW j) N (q b) (ζ b)))
        =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
    intro j hj
    have hjm : j + 1 ≤ m := by have := mem_range.mp hj; omega
    have hd : DifferentiableOn ℂ
        (fun x : ℂ × ℂ => cepsCanonDriftCoeff dom ρW j x.2 x.1)
        (ball 0 (dom.c₀ / 2) ×ˢ ball 0 (dom.q₀ / 2)) :=
      (cepsCanonDriftCoeff_differentiableOn dom hW hθ hD hf hη j hjm).mono
        (fun x hx => ⟨(re_le_norm x.1).trans_lt ((mem_ball_zero_iff.mp hx.1).trans
          (half_lt_self dom.c₀_pos)), mem_ball_zero_iff.mp hx.2⟩)
    have hb : ∀ x ∈ ball (0 : ℂ) (dom.c₀ / 2) ×ˢ ball 0 (dom.q₀ / 2),
        ‖cepsCanonDriftCoeff dom ρW j x.2 x.1‖ ≤ dom.canonDriftCoeffBound j M :=
      fun x hx => cepsCanonDriftCoeff_norm_le dom hW hθ hD hf hη hM j hjm
        (mem_ball_zero_iff.mp hx.2).le (mem_ball_zero_iff.mp hx.1).le
    have hB : 0 ≤ dom.canonDriftCoeffBound j M :=
      (norm_nonneg _).trans (hb (0, 0) ⟨mem_ball_self (half_pos dom.c₀_pos),
        mem_ball_self (half_pos dom.q₀_pos)⟩)
    have he := bivariateTaylorSum_curve_isBigO (half_pos dom.c₀_pos)
      (half_pos dom.q₀_pos) hB hd hb hq hζ hqo hζo N
    have hc : (fun b => (j.factorial : ℂ)⁻¹ * (μ b) ^ j)
        =O[𝓝 (0 : ℂ)] (fun _ => (1 : ℂ)) :=
      ((hμ.pow j).const_mul _).tendsto.isBigO_one ℂ
    simpa only [one_mul] using hc.mul he
  have hs := IsBigO.sum hterms
  apply hs.congr_left
  intro b
  simp only [cepsCanonDriftTaylor, cepsCanonDriftRectTaylor, Finset.sum_apply,
    mul_sub, sum_sub_distrib]

include hW hθ hD in
theorem cepsCanonDriftTaylor_curve_analyticAt {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) {μ q ζ : ℂ → ℂ}
    (hμ : AnalyticAt ℂ μ 0) (hq : AnalyticAt ℂ q 0) (hζ : AnalyticAt ℂ ζ 0)
    (hq0 : q 0 = 0) (hζ0 : ζ 0 = 0) :
    AnalyticAt ℂ (fun b => cepsCanonDriftTaylor dom ρW N (μ b) (q b) (ζ b)) 0 := by
  let U : Set (ℂ × (ℂ × ℂ)) := {x | x.2.2.re < dom.c₀ ∧ ‖x.2.1‖ < dom.q₀ / 2}
  have hopen : IsOpen U := (isOpen_lt (continuous_re.comp (continuous_snd.comp continuous_snd))
    continuous_const).inter (isOpen_lt (continuous_fst.comp continuous_snd).norm continuous_const)
  have h0 : (μ 0, (q 0, ζ 0)) ∈ U := by
    simp only [U, Set.mem_ofPred_eq, hq0, hζ0, zero_re, norm_zero]
    exact ⟨dom.c₀_pos, half_pos dom.q₀_pos⟩
  have hmap : ∀ᶠ b : ℂ in 𝓝 0, (μ b, (q b, ζ b)) ∈ U :=
    (hμ.continuousAt.prodMk (hq.continuousAt.prodMk hζ.continuousAt)).eventually
      (hopen.mem_nhds h0)
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [analyticAt_iff_eventually_differentiableAt.mp hμ,
    analyticAt_iff_eventually_differentiableAt.mp hq,
    analyticAt_iff_eventually_differentiableAt.mp hζ, hmap] with b hμb hqb hζb hb
  have hd := cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN
  have hc : DifferentiableAt ℂ (fun b => (μ b, (q b, ζ b))) b :=
    hμb.prodMk (hqb.prodMk hζb)
  have ht := ((hd _ hb).differentiableAt (hopen.mem_nhds hb)).comp b hc
  simpa only [Function.comp_apply] using! ht

end PGM
