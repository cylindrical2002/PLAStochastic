import PLAStochastic.Index.CEPS.Central.MorseData
import PLAStochastic.Index.CEPS.Central.Newton
import PLAStochastic.ForMathlib.Analysis.Complex.AnalyticJetComposition
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesGermCongr

/-! # Newton and exact-root central kernels have the same finite scale jets

At a fixed non-merger point, an analytic branch of the signed Morse coordinate makes the
two scaled Morse roots exact analytic roots through any prescribed zero-scale root `β` and
its partner `-2λ/V - β`. Each fixed-gap Newton step gains one order, so after `N` steps the
node curves agree to `O(b^(N+1))`; analytic composition transfers this to every
node-symmetric kernel, whose Morse evaluation is the descended kernel. -/

noncomputable section
open Complex Set Filter Topology Asymptotics PowerSeries
namespace PGM

variable {d N : ℕ} {η : (Fin d → ℂ) × ℂ → ℂ} {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ}

set_option maxHeartbeats 800000 in
/-- Taylor jets of order at most `N` of a node-symmetric kernel along the two Newton
iterations started at `β` and `-2λ/V - β` coincide with those of its descended kernel. -/
theorem cepsCentralNewton_coeff_eq_descended {F : CepsCentralBase d → ℂ → ℂ → ℂ}
    (hsym : ∀ x a₁ a₂, F x a₁ a₂ = F x a₂ a₁)
    {q : Fin d → ℂ} (hq : CepsCentralMorseData d N η Θ q) {lam w β : ℂ}
    (hβ : β ^ 2 * (cepsComplexJetPad d q (cepsJetCode (.inl 0)) / 2) + lam * β = w)
    (hgap : lam + cepsComplexJetPad d q (cepsJetCode (.inl 0)) * β ≠ 0)
    (hF : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => F X.1 X.2.1 X.2.2)
      ((q, lam, w, 0), β, -2 * lam / cepsComplexJetPad d q (cepsJetCode (.inl 0)) - β)) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => F (q, lam, w, b)
        (cepsCentralNewton d N q lam w β N b)
        (cepsCentralNewton d N q lam w
          (-2 * lam / cepsComplexJetPad d q (cepsJetCode (.inl 0)) - β) N b)) 0) =
      coeff j (complexTaylorSeries
        (fun b => cepsCentralDescended d N η Θ F (q, lam, w, b)) 0) := by
  set V := cepsComplexJetPad d q (cepsJetCode (.inl 0)) with hVdef
  have hV : V ≠ 0 := hq.hV
  set τ := hq.tau with hτdef
  have hτ : τ ^ 2 * (V / 2) = 1 := hq.tau_sq
  have hτ0 : τ ≠ 0 := hq.tau_ne_zero
  set β' := -2 * lam / V - β with hβ'def
  have hβ' : β' ^ 2 * (V / 2) + lam * β' = w := by
    rw [← hβ, hβ'def]
    field_simp
    ring
  have hgap' : lam + V * β' ≠ 0 := by
    have : lam + V * β' = -(lam + V * β) := by
      rw [hβ'def]
      field_simp
      ring
    rw [this]
    exact neg_ne_zero.mpr hgap
  -- the Morse square along the scale
  let Sq : ℂ → ℂ := fun b => cepsComplexJetMorseSquare d N η q lam w b
  have hSqA : AnalyticAt ℂ Sq 0 := by
    have h := (cepsComplexJetMorseSquare_analyticAt (N := N) hq.hη lam w).comp_of_eq
      (x := (0 : ℂ)) (f := fun b : ℂ => (((q, lam), w), b))
      (analyticAt_const.prod analyticAt_id) rfl
    simp only [Function.comp_def] at h
    exact h
  have hSq0 : Sq 0 = w + lam ^ 2 / (2 * V) := hq.square_zero lam w
  -- the signed coordinate branch through the prescribed roots
  let s₀ : ℂ := (β + lam / V) / τ
  have hβlam : β + lam / V ≠ 0 := by
    intro h0
    apply hgap
    have : lam + V * β = V * (β + lam / V) := by field_simp; ring
    rw [this, h0, mul_zero]
  have hs₀ : s₀ ≠ 0 := div_ne_zero hβlam hτ0
  have hτsq : τ ^ 2 = 2 / V := by
    field_simp
    linear_combination 2 * hτ
  have hs₀sq : s₀ ^ 2 = Sq 0 := by
    rw [hSq0]
    simp only [s₀, div_pow, hτsq]
    field_simp
    linear_combination (2 * V) * hβ
  have hs₀sq' : s₀ ^ 2 ≠ 0 := pow_ne_zero 2 hs₀
  let s : ℂ → ℂ := fun b => s₀ * Complex.sqrt (Sq b / s₀ ^ 2)
  have hsA : AnalyticAt ℂ s 0 := by
    have h1 : Sq 0 / s₀ ^ 2 ∈ slitPlane := by
      rw [← hs₀sq, div_self hs₀sq']
      exact one_mem_slitPlane
    have hsqrt : AnalyticAt ℂ Complex.sqrt (Sq 0 / s₀ ^ 2) :=
      Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds h1)
    have hdiv : AnalyticAt ℂ (fun b => Sq b / s₀ ^ 2) 0 := hSqA.div_const
    exact analyticAt_const.mul (hsqrt.comp (f := fun b => Sq b / s₀ ^ 2) (x := 0) hdiv)
  have hs0 : s 0 = s₀ := by
    simp only [s, ← hs₀sq, div_self hs₀sq', Complex.sqrt_one, mul_one]
  have hssq : ∀ b, s b ^ 2 = Sq b := by
    intro b
    simp only [s, mul_pow, sqrt_sq_eq]
    field_simp
  -- the two exact Morse node curves
  let n : ℂ → ℂ → ℂ := fun sgn b => cepsComplexJetMorseNode d Θ sgn (((q, lam), b), s b)
  have hnA : ∀ sgn : ℂ, AnalyticAt ℂ (n sgn) 0 := by
    intro sgn
    have h := (cepsComplexJetMorseScaleRoot_analyticAt hq.hΘ lam (sgn * s₀)).comp_of_eq
      (x := (0 : ℂ)) (f := fun b : ℂ => (((q, lam), sgn * s b), b))
      ((analyticAt_const.prod (analyticAt_const.mul hsA)).prod analyticAt_id)
      (by simp only [hs0])
    simp only [Function.comp_def] at h
    exact h
  have hn0 : ∀ sgn : ℂ, n sgn 0 = -lam / V + sgn * s₀ * τ := by
    intro sgn
    change cepsComplexJetMorseScaleRoot d Θ q lam (sgn * s 0) 0 = _
    rw [hs0, hq.scaleRoot_zero lam (sgn * s₀)]
  have hsτ : s₀ * τ = β + lam / V := by
    simp only [s₀]
    field_simp
  have hn₁0 : n 1 0 = β := by
    rw [hn0, one_mul, hsτ]
    ring
  have hn₂0 : n (-1) 0 = β' := by
    rw [hn0, neg_one_mul, neg_mul, hsτ, hβ'def]
    ring
  have hneq : ∀ sgn : ℂ, sgn ^ 2 = 1 → ∀ᶠ b in 𝓝 (0 : ℂ),
      n sgn b ^ 2 * cepsCgfComplexJetPolynomial (cepsComplexJetPad d q) N (b * n sgn b) +
        lam * n sgn b = w * (1 + b * lam) := by
    intro sgn hsgn
    have hcurve : AnalyticAt ℂ (fun b : ℂ => (((q, lam), sgn * s b), b)) 0 :=
      (analyticAt_const.prod (analyticAt_const.mul hsA)).prod analyticAt_id
    have ht : Tendsto (fun b : ℂ => (((q, lam), sgn * s b), b)) (𝓝 0)
        (𝓝 (((q, lam), sgn * s₀), 0)) := by
      have h := hcurve.continuousAt.tendsto
      simp only [hs0] at h
      exact h
    filter_upwards [ht.eventually (hq.scaleRoot_equation lam (sgn * s₀))] with b hb
    change n sgn b ^ 2 * cepsCgfComplexJetPolynomial (cepsComplexJetPad d q) N (b * n sgn b) +
        lam * n sgn b = lam ^ 2 * cepsComplexCgfJetMinimumUnit d N η (q, b * lam) +
          (sgn * s b) ^ 2 at hb
    rw [hb, mul_pow, hsgn, one_mul, hssq b]
    simp only [Sq, cepsComplexJetMorseSquare]
    ring
  have hO₁ := cepsCentralNewton_isBigO (N := N) (hnA 1) hn₁0 (hneq 1 (by norm_num)) hgap N
  have hO₂ := cepsCentralNewton_isBigO (N := N) (hnA (-1)) hn₂0 (hneq (-1) (by norm_num))
    hgap' N
  rw [min_self] at hO₁ hO₂
  -- analytic composition along the two node curves
  let XN : ℂ → CepsCentralBase d × ℂ × ℂ := fun b =>
    ((q, lam, w, b), cepsCentralNewton d N q lam w β N b, cepsCentralNewton d N q lam w β' N b)
  let XM : ℂ → CepsCentralBase d × ℂ × ℂ := fun b => ((q, lam, w, b), n 1 b, n (-1) b)
  have hbase : AnalyticAt ℂ (fun b : ℂ => ((q, lam, w, b) : CepsCentralBase d)) 0 :=
    analyticAt_const.prod (analyticAt_const.prod (analyticAt_const.prod analyticAt_id))
  have hNA : ∀ γ : ℂ, lam + V * γ ≠ 0 →
      AnalyticAt ℂ (fun b => cepsCentralNewton d N q lam w γ N b) 0 := by
    intro γ hγ
    exact cepsCentralNewton_analyticAt (q := fun _ : ℂ => q) (lam := fun _ => lam)
      (w := fun _ => w) (β := fun _ => γ) (b := id) analyticAt_const analyticAt_const
      analyticAt_const analyticAt_const analyticAt_id hγ N
  have hXN : AnalyticAt ℂ XN 0 := hbase.prod ((hNA β hgap).prod (hNA β' hgap'))
  have hXM : AnalyticAt ℂ XM 0 := hbase.prod ((hnA 1).prod (hnA (-1)))
  have hXN0 : XN 0 = ((q, lam, w, 0), β, β') := by
    simp only [XN, cepsCentralNewton_zero_of_root hβ, cepsCentralNewton_zero_of_root hβ']
  have hXM0 : XM 0 = ((q, lam, w, 0), β, β') := by
    simp only [XM, hn₁0, hn₂0]
  have hdiff : (fun b => XN b - XM b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) := by
    have h0 : (fun b : ℂ => ((q, lam, w, b) : CepsCentralBase d) - (q, lam, w, b)) =O[𝓝 0]
        (fun b : ℂ => b ^ (N + 1)) := by
      simpa only [sub_self] using isBigO_zero (fun b : ℂ => b ^ (N + 1)) (𝓝 0)
    have h₁ : (fun b => cepsCentralNewton d N q lam w β N b - n 1 b) =O[𝓝 0]
        (fun b : ℂ => b ^ (N + 1)) := by
      simpa only [neg_sub] using hO₁.neg_left
    have h₂ : (fun b => cepsCentralNewton d N q lam w β' N b - n (-1) b) =O[𝓝 0]
        (fun b : ℂ => b ^ (N + 1)) := by
      simpa only [neg_sub] using hO₂.neg_left
    exact h0.prod_left (h₁.prod_left h₂)
  have hcomp := complexTaylorSeries_coeff_eq_of_analytic_composition hF hXN hXM hXN0 hXM0 N hdiff
  -- the Morse node curve gives the descended kernel near zero scale
  have hev : (fun b => cepsCentralDescended d N η Θ F (q, lam, w, b)) =ᶠ[𝓝 0]
      (fun b => F (XM b).1 (XM b).2.1 (XM b).2.2) := by
    have hw : ∀ᶠ b : ℂ in 𝓝 0, 1 + b * lam ≠ 0 := by
      have hc : ContinuousAt (fun b : ℂ => 1 + b * lam) 0 := by fun_prop
      exact hc.eventually_ne (by simp)
    filter_upwards [hw] with b hb
    rw [cepsCentralDescended_eq_of_sq (x := (q, lam, w, b)) η Θ hsym (hssq b)]
    have hfreq := cepsComplexJetMorseFrequency_of_sq (N := N) η (q, lam, w, b) (hssq b) hb
    simp only [cepsCentralMorseEval, cepsCentralMorsePoint]
    rw [hfreq]
  intro j hj
  rw [complexTaylorSeries_eq_of_eventuallyEq hev]
  exact hcomp j hj

end PGM
