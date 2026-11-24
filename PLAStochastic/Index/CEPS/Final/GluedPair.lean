import PLAStochastic.Index.CEPS.Final.KernelComplexForm
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricDeriv
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import PLAStochastic.Index.CEPS.BrownianCoeff.IntegralBudget

/-! # Gluing the central exact-root kernel to the outer Newton kernel

Near the root merger `λ = z = 0` the Newton finite-jet pair is replaced by an exact-root kernel
`H` that is jointly analytic there and has the same scale coefficients at non-merger points.
Outside a small drift/frequency box the Newton pair itself is analytic with exponential bounds.
The glued scale coefficient is analytic in `(q, z)` on a polydisc times a strip around the
imaginary axis, for every drift, with a product envelope in drift and frequency.
-/

noncomputable section
open Complex Metric Set Filter Topology
namespace PGM

/-- The drift/frequency size `|λ| + √‖z‖`. -/
def cepsDriftFreqSize (lam : ℝ) (z : ℂ) : ℝ := |lam| + Real.sqrt ‖z‖

/-- Scale coefficient of a central kernel. -/
def cepsCentralPairCoeff {d : ℕ} (H : (Fin d → ℂ) × ℂ × ℂ × ℂ → ℂ) (n : ℕ)
    (q : Fin d → ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  cepsScaleCoeff n (fun b => H (q, (lam : ℂ), z, b))

/-- The glued scale coefficient: central kernel on the small box, Newton pair outside. -/
def cepsGluedPairCoeff (d N n : ℕ) (H : (Fin d → ℂ) × ℂ × ℂ × ℂ → ℂ) (lc zc : ℝ)
    (q : Fin d → ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  if |lam| < lc ∧ ‖z‖ < zc then cepsCentralPairCoeff H n q lam z
  else cepsKernelPairCoeffC d N n q lam z

/-- The data needed for the gluing: an outer budget for the Newton pair, a central analytic
kernel with matching scale coefficients, and compatible radii. -/
structure CepsGlueData (d N : ℕ) where
  c₀ : Fin d → ℂ
  H : (Fin d → ℂ) × ℂ × ℂ × ℂ → ℂ
  r : ℝ
  MH : ℝ
  R : ℝ
  lc : ℝ
  zc : ℝ
  F₀ : ℝ
  δ : ℝ
  δb : ℝ
  K : ℝ
  c : ℝ
  e : ℕ
  hr : 0 < r
  hR : 0 < R
  hRr : R ≤ r / 2
  hlc : 0 < lc
  hlc1 : lc ≤ 1
  hlcr : lc ≤ r / 2
  hzc : 0 < zc
  hzcr : 4 * zc ≤ r
  hF₀ : 0 < F₀
  hF₀lc : F₀ ≤ lc
  hF₀zc : F₀ ^ 2 ≤ zc
  hδ : 0 < δ
  hδb : 0 < δb
  hc : 0 < c
  hK : 0 ≤ K
  /-- Merger points of the small drifts stay well inside the central frequency disc. -/
  merge : ∀ q ∈ ball c₀ R, ∀ lam : ℝ, |lam| < lc →
    ‖(lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0)))‖ < zc / 2
  /-- The outer budget of the Newton subtracted pair. -/
  outer : ∀ q ∈ ball c₀ R, ∀ (lam : ℝ) (z b : ℂ), -δ ≤ z.re → F₀ ≤ cepsDriftFreqSize lam z →
    ‖b‖ * (1 + cepsDriftFreqSize lam z) ≤ δb →
      AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
          cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2) (q, z, b) ∧
      ‖cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z b‖ ≤
        K * (1 + cepsDriftFreqSize lam z) ^ e * Real.exp (-c * cepsDriftFreqSize lam z)
  /-- The central kernel is analytic and bounded on a ball. -/
  central_an : ∀ u ∈ ball (c₀, (0 : ℂ), (0 : ℂ), (0 : ℂ)) r, AnalyticAt ℂ H u
  central_bd : ∀ u ∈ ball (c₀, (0 : ℂ), (0 : ℂ), (0 : ℂ)) r, ‖H u‖ ≤ MH
  /-- Matching scale coefficients at non-merger points. -/
  central_eq : ∀ (q : Fin d → ℂ) (lam : ℝ) (z : ℂ),
    (q, (lam : ℂ), z, (0 : ℂ)) ∈ ball (c₀, (0 : ℂ), (0 : ℂ), (0 : ℂ)) r →
    z + (lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) ≠ 0 →
    ∀ n ≤ N, iteratedDeriv n (fun b => cepsComplexKernelPairJetModel (cepsComplexJetPad d q) N lam z b) 0 =
      iteratedDeriv n (fun b => H (q, (lam : ℂ), z, b)) 0

namespace CepsGlueData

variable {d N : ℕ} (G : CepsGlueData d N)

theorem mem_central_ball {q : Fin d → ℂ} {lam : ℝ} {z b : ℂ} {s : ℝ}
    (hq : dist q G.c₀ < s) (hl : |lam| < s) (hz : ‖z‖ < s) (hb : ‖b‖ < s) :
    (q, (lam : ℂ), z, b) ∈ ball (G.c₀, (0 : ℂ), (0 : ℂ), (0 : ℂ)) s := by
  rw [mem_ball, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
  simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  exact max_lt hq (max_lt hl (max_lt hz hb))

/-- The outer scale coefficient: joint analyticity and the Cauchy bound. -/
theorem outer_coeff {q : Fin d → ℂ} (hq : q ∈ ball G.c₀ G.R) {lam : ℝ} {z : ℂ}
    (hz : -G.δ ≤ z.re) (hF : G.F₀ ≤ cepsDriftFreqSize lam z) (n : ℕ) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => cepsKernelPairCoeffC d N n v.1 lam v.2) (q, z) ∧
    ‖cepsKernelPairCoeffC d N n q lam z‖ ≤
      G.K * (1 + cepsDriftFreqSize lam z) ^ G.e * Real.exp (-G.c * cepsDriftFreqSize lam z) *
        (2 * (1 + cepsDriftFreqSize lam z) / G.δb) ^ n := by
  set X := 1 + cepsDriftFreqSize lam z with hX
  have hX1 : 1 ≤ X := by
    have : 0 ≤ cepsDriftFreqSize lam z := by unfold cepsDriftFreqSize; positivity
    linarith
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  constructor
  · obtain ⟨han, -⟩ := G.outer q hq lam z 0 hz hF (by simp [G.hδb.le])
    let P : ((Fin d → ℂ) × ℂ) × ℂ → ℂ := fun w =>
      cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d w.1.1) N lam w.1.2 w.2
    have hP : AnalyticAt ℂ P ((q, z), 0) := by
      have hm : AnalyticAt ℂ (fun w : ((Fin d → ℂ) × ℂ) × ℂ => (w.1.1, w.1.2, w.2)) ((q, z), 0) :=
        (analyticAt_fst.comp analyticAt_fst).prod ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)
      exact han.comp (x := ((q, z), (0 : ℂ))) hm
    have hD := hP.iteratedDeriv_snd n
    have hc : AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => (v, (0 : ℂ))) (q, z) :=
      analyticAt_id.prod analyticAt_const
    have h := hD.comp (x := (q, z)) hc
    exact analyticAt_const.mul h
  · let f : ℂ → ℂ := fun b => cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z b
    have hρ : 0 < G.δb / X := div_pos G.hδb hX0
    have hball : ∀ b ∈ ball (0 : ℂ) (G.δb / X), ‖b‖ * X ≤ G.δb := by
      intro b hb
      rw [mem_ball_zero_iff, lt_div_iff₀ hX0] at hb
      exact hb.le
    have hdf : DifferentiableOn ℂ f (ball 0 (G.δb / X)) := by
      intro b hb
      obtain ⟨han, -⟩ := G.outer q hq lam z b hz hF (hball b hb)
      have hl : AnalyticAt ℂ (fun t : ℂ => (q, z, t)) b :=
        analyticAt_const.prod (analyticAt_const.prod analyticAt_id)
      exact (han.comp (x := b) hl).differentiableAt.differentiableWithinAt
    have hM : ∀ b ∈ ball (0 : ℂ) (G.δb / X), ‖f b‖ ≤
        G.K * X ^ G.e * Real.exp (-G.c * cepsDriftFreqSize lam z) :=
      fun b hb => (G.outer q hq lam z b hz hF (hball b hb)).2
    have hC := norm_iteratedDeriv_le_of_ball n hρ hdf hM
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    unfold cepsKernelPairCoeffC cepsScaleCoeff
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f 0‖
        ≤ (n.factorial : ℝ)⁻¹ * (n.factorial * (G.K * X ^ G.e *
            Real.exp (-G.c * cepsDriftFreqSize lam z)) / (G.δb / X / 2) ^ n) :=
          mul_le_mul_of_nonneg_left hC (by positivity)
      _ = _ := by
          have h2 : G.δb / X / 2 = (2 * X / G.δb)⁻¹ := by field_simp
          rw [h2, inv_pow, div_inv_eq_mul]
          field_simp

/-- The central scale coefficient: joint analyticity and the Cauchy bound. -/
theorem central_coeff {q : Fin d → ℂ} {lam : ℝ} {z : ℂ}
    (hq : dist q G.c₀ < G.r / 2) (hl : |lam| < G.r / 2) (hz : ‖z‖ < G.r / 2) (n : ℕ) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => cepsCentralPairCoeff G.H n v.1 lam v.2) (q, z) ∧
    ‖cepsCentralPairCoeff G.H n q lam z‖ ≤ G.MH * (4 / G.r) ^ n := by
  constructor
  · let P : ((Fin d → ℂ) × ℂ) × ℂ → ℂ := fun w => G.H (w.1.1, (lam : ℂ), w.1.2, w.2)
    have hP : AnalyticAt ℂ P ((q, z), 0) := by
      have hm : AnalyticAt ℂ (fun w : ((Fin d → ℂ) × ℂ) × ℂ => (w.1.1, (lam : ℂ), w.1.2, w.2))
          ((q, z), 0) :=
        (analyticAt_fst.comp analyticAt_fst).prod (analyticAt_const.prod
          ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd))
      have hH := G.central_an _ (G.mem_central_ball (hq.trans (half_lt_self G.hr))
        (hl.trans (half_lt_self G.hr)) (hz.trans (half_lt_self G.hr)) (show ‖(0 : ℂ)‖ < G.r by simpa using G.hr))
      exact hH.comp (x := ((q, z), (0 : ℂ))) hm
    have h := (hP.iteratedDeriv_snd n).comp (x := (q, z))
      (f := fun v : (Fin d → ℂ) × ℂ => (v, (0 : ℂ))) (analyticAt_id.prod analyticAt_const)
    exact analyticAt_const.mul h
  · let f : ℂ → ℂ := fun b => G.H (q, (lam : ℂ), z, b)
    have hρ : 0 < G.r / 2 := half_pos G.hr
    have hmem : ∀ b ∈ ball (0 : ℂ) (G.r / 2),
        (q, (lam : ℂ), z, b) ∈ ball (G.c₀, (0 : ℂ), (0 : ℂ), (0 : ℂ)) G.r := by
      intro b hb
      exact G.mem_central_ball (hq.trans (half_lt_self G.hr)) (hl.trans (half_lt_self G.hr))
        (hz.trans (half_lt_self G.hr)) ((mem_ball_zero_iff.mp hb).trans (half_lt_self G.hr))
    have hdf : DifferentiableOn ℂ f (ball 0 (G.r / 2)) := by
      intro b hb
      have hl' : AnalyticAt ℂ (fun t : ℂ => (q, (lam : ℂ), z, t)) b :=
        analyticAt_const.prod (analyticAt_const.prod (analyticAt_const.prod analyticAt_id))
      exact ((G.central_an _ (hmem b hb)).comp (x := b) hl').differentiableAt.differentiableWithinAt
    have hM : ∀ b ∈ ball (0 : ℂ) (G.r / 2), ‖f b‖ ≤ G.MH := fun b hb => G.central_bd _ (hmem b hb)
    have hC := norm_iteratedDeriv_le_of_ball n hρ hdf hM
    unfold cepsCentralPairCoeff cepsScaleCoeff
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f 0‖
        ≤ (n.factorial : ℝ)⁻¹ * (n.factorial * G.MH / (G.r / 2 / 2) ^ n) :=
          mul_le_mul_of_nonneg_left hC (by positivity)
      _ = _ := by
          have h2 : G.r / 2 / 2 = (4 / G.r)⁻¹ := by field_simp; norm_num
          rw [h2, inv_pow, div_inv_eq_mul]
          field_simp

theorem size_nonneg (lam : ℝ) (z : ℂ) : 0 ≤ cepsDriftFreqSize lam z := by
  unfold cepsDriftFreqSize; positivity

/-- Outside the central box the size is at least `F₀`. -/
theorem F₀_le_size_of_not_central {lam : ℝ} {z : ℂ} (h : ¬ (|lam| < G.lc ∧ ‖z‖ < G.zc)) :
    G.F₀ ≤ cepsDriftFreqSize lam z := by
  unfold cepsDriftFreqSize
  rcases not_and_or.mp h with h | h
  · have := Real.sqrt_nonneg ‖z‖
    linarith [G.hF₀lc, not_lt.mp h]
  · have h1 : G.F₀ ≤ Real.sqrt ‖z‖ := by
      rw [show G.F₀ = Real.sqrt (G.F₀ ^ 2) by rw [Real.sqrt_sq G.hF₀.le]]
      exact Real.sqrt_le_sqrt (G.hF₀zc.trans (not_lt.mp h))
    linarith [abs_nonneg lam]

/-- The Newton and central scale coefficients agree at non-merger points of the central box. -/
theorem coeff_eq_central_of_ne {q : Fin d → ℂ} (hq : q ∈ ball G.c₀ G.R) {lam : ℝ}
    (hl : |lam| < G.lc) {z : ℂ} (hz : ‖z‖ < 2 * G.zc)
    (hne : z + (lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) ≠ 0)
    {n : ℕ} (hn : n ≤ N) :
    cepsKernelPairCoeffC d N n q lam z = cepsCentralPairCoeff G.H n q lam z := by
  have hl1 : ¬ (1 ≤ lam) := fun h => by linarith [le_abs_self lam, G.hlc1]
  have hqr : dist q G.c₀ < G.r := (mem_ball.mp hq).trans_le (G.hRr.trans (half_le_self G.hr.le))
  have hlr : |lam| < G.r := hl.trans_le (G.hlcr.trans (half_le_self G.hr.le))
  have hzr : ‖z‖ < G.r := hz.trans_le (by linarith [G.hzcr, G.hzc])
  have hmem := G.mem_central_ball hqr hlr hzr (show ‖(0 : ℂ)‖ < G.r by simpa using G.hr)
  have heq := G.central_eq q lam z hmem hne n hn
  have hfun : (fun b => cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z b) =
      fun b => cepsComplexKernelPairJetModel (cepsComplexJetPad d q) N lam z b := by
    funext b
    simp only [cepsComplexKernelSubtractedPairJetModel, if_neg hl1, sub_zero]
  unfold cepsKernelPairCoeffC cepsCentralPairCoeff cepsScaleCoeff
  rw [hfun, heq]

/-- The Newton and central scale coefficients agree away from the merger. -/
theorem coeff_eq_central {q : Fin d → ℂ} (hq : q ∈ ball G.c₀ G.R) {lam : ℝ} (hl : |lam| < G.lc)
    {z : ℂ} (hz : ‖z‖ < 2 * G.zc) (hz' : G.zc / 2 ≤ ‖z‖) {n : ℕ} (hn : n ≤ N) :
    cepsKernelPairCoeffC d N n q lam z = cepsCentralPairCoeff G.H n q lam z := by
  refine G.coeff_eq_central_of_ne hq hl hz ?_ hn
  intro h0
  have hw := G.merge q hq lam hl
  have : ‖z‖ = ‖(lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0)))‖ := by
    rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
  linarith

/-- Away from the merger the glued coefficient is the Newton coefficient. -/
theorem glued_eq_of_ne {q : Fin d → ℂ} (hq : q ∈ ball G.c₀ G.R) (lam : ℝ) {z : ℂ}
    (hne : z + (lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) ≠ 0)
    {n : ℕ} (hn : n ≤ N) :
    cepsGluedPairCoeff d N n G.H G.lc G.zc q lam z = cepsKernelPairCoeffC d N n q lam z := by
  unfold cepsGluedPairCoeff
  split_ifs with hc
  · exact (G.coeff_eq_central_of_ne hq hc.1 (hc.2.trans (by linarith [G.hzc])) hne hn).symm
  · rfl

/-- The glued coefficient is jointly analytic in `(q, z)` for every drift. -/
theorem glued_analyticAt {n : ℕ} (hn : n ≤ N) {q : Fin d → ℂ} (hq : q ∈ ball G.c₀ G.R)
    (lam : ℝ) {z : ℂ} (hz : -G.δ < z.re) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => cepsGluedPairCoeff d N n G.H G.lc G.zc v.1 lam v.2)
      (q, z) := by
  have hopen : IsOpen {v : (Fin d → ℂ) × ℂ | v.1 ∈ ball G.c₀ G.R ∧ -G.δ < v.2.re} :=
    (isOpen_ball.preimage continuous_fst).inter (isOpen_lt continuous_const
      (Complex.continuous_re.comp continuous_snd))
  have hnear : ∀ᶠ v in 𝓝 (q, z), v.1 ∈ ball G.c₀ G.R ∧ -G.δ < v.2.re :=
    hopen.mem_nhds ⟨hq, hz⟩
  by_cases hl : |lam| < G.lc
  · by_cases hzc : ‖z‖ < 2 * G.zc
    · -- central representation on a neighbourhood
      have hq2 : dist q G.c₀ < G.r / 2 := (mem_ball.mp hq).trans_le G.hRr
      have hl2 : |lam| < G.r / 2 := hl.trans_le G.hlcr
      have hz2 : ‖z‖ < G.r / 2 := hzc.trans_le (by linarith [G.hzcr])
      have hc := (G.central_coeff hq2 hl2 hz2 n).1
      apply hc.congr
      have hz' : ∀ᶠ v in 𝓝 (q, z), ‖v.2‖ < 2 * G.zc :=
        (continuous_snd.norm).continuousAt.eventually (gt_mem_nhds hzc)
      filter_upwards [hnear, hz'] with v hv hv2
      unfold cepsGluedPairCoeff
      by_cases hv1 : ‖v.2‖ < G.zc
      · rw [if_pos ⟨hl, hv1⟩]
      · rw [if_neg (fun h => hv1 h.2)]
        exact (G.coeff_eq_central hv.1 hl hv2 (by linarith [not_lt.mp hv1, G.hzc]) hn).symm
    · -- outer representation on a neighbourhood
      have hzz : G.zc < ‖z‖ := by linarith [not_lt.mp hzc, G.hzc]
      have hz' : ∀ᶠ v in 𝓝 (q, z), G.zc < ‖v.2‖ :=
        (continuous_snd.norm).continuousAt.eventually (lt_mem_nhds hzz)
      have hF : G.F₀ ≤ cepsDriftFreqSize lam z :=
        G.F₀_le_size_of_not_central (fun h => by linarith [h.2, not_lt.mp hzc, G.hzc])
      have ho := (G.outer_coeff hq hz.le hF n).1
      apply ho.congr
      filter_upwards [hz'] with v hv
      unfold cepsGluedPairCoeff
      rw [if_neg (fun h => by linarith [h.2])]
  · have hF : G.F₀ ≤ cepsDriftFreqSize lam z := G.F₀_le_size_of_not_central (fun h => hl h.1)
    have ho := (G.outer_coeff hq hz.le hF n).1
    apply ho.congr
    filter_upwards with v
    unfold cepsGluedPairCoeff
    rw [if_neg (fun h => hl h.1)]

/-- The drift envelope of the glued coefficient. -/
def gluedEnvelope (n : ℕ) (lam : ℝ) : ℝ :=
  G.MH * (4 / G.r) ^ n * Real.exp (G.c * Real.sqrt G.zc) * (if |lam| < G.lc then 1 else 0) +
    G.K * (2 / G.δb) ^ n * 2 ^ (G.e + n) * ((1 + |lam|) ^ (G.e + n) * Real.exp (-G.c * |lam|))

theorem gluedEnvelope_integrable (n : ℕ) : MeasureTheory.Integrable (G.gluedEnvelope n) := by
  have h1 : MeasureTheory.Integrable (fun lam : ℝ => if |lam| < G.lc then (1 : ℝ) else 0) := by
    have : (fun lam : ℝ => if |lam| < G.lc then (1 : ℝ) else 0) =
        Set.indicator (Set.Ioo (-G.lc) G.lc) (fun _ => (1 : ℝ)) := by
      funext lam
      simp only [Set.indicator, Set.mem_Ioo, abs_lt]
    rw [this]
    exact (MeasureTheory.integrableOn_const (by simp) ).integrable_indicator measurableSet_Ioo
  have h2 := cepsBrownian_driftEnvelope_integrable (G.e + n) G.hc
  exact (h1.const_mul _).add (h2.const_mul _)

theorem gluedEnvelope_nonneg (n : ℕ) (lam : ℝ) (hMH : 0 ≤ G.MH) : 0 ≤ G.gluedEnvelope n lam := by
  have := G.hδb
  have := G.hr
  unfold gluedEnvelope
  have hK := G.hK
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    split_ifs <;> norm_num
  · positivity

/-- The glued coefficient is bounded by the drift envelope times a stretched frequency weight. -/
theorem glued_norm_le {n : ℕ} {q : Fin d → ℂ} (hq : q ∈ ball G.c₀ G.R) (lam : ℝ) {z : ℂ}
    (hz : -G.δ ≤ z.re) (hMH : 0 ≤ G.MH) :
    ‖cepsGluedPairCoeff d N n G.H G.lc G.zc q lam z‖ ≤
      G.gluedEnvelope n lam * ((1 + ‖z‖) ^ (G.e + n) * Real.exp (-G.c * Real.sqrt ‖z‖)) := by
  have hW1 : 1 ≤ (1 + ‖z‖) ^ (G.e + n) := one_le_pow₀ (by linarith [norm_nonneg z])
  have hE0 : 0 ≤ Real.exp (-G.c * Real.sqrt ‖z‖) := (Real.exp_pos _).le
  unfold cepsGluedPairCoeff
  split_ifs with hc
  · have hq2 : dist q G.c₀ < G.r / 2 := (mem_ball.mp hq).trans_le G.hRr
    have hl2 : |lam| < G.r / 2 := hc.1.trans_le G.hlcr
    have hz2 : ‖z‖ < G.r / 2 := hc.2.trans_le (by linarith [G.hzcr, G.hzc])
    refine (G.central_coeff hq2 hl2 hz2 n).2.trans ?_
    have hexp : 1 ≤ Real.exp (G.c * Real.sqrt G.zc) * Real.exp (-G.c * Real.sqrt ‖z‖) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have : Real.sqrt ‖z‖ ≤ Real.sqrt G.zc := Real.sqrt_le_sqrt hc.2.le
      nlinarith [G.hc]
    have h0 : 0 ≤ G.K * (2 / G.δb) ^ n * 2 ^ (G.e + n) * ((1 + |lam|) ^ (G.e + n) *
        Real.exp (-G.c * |lam|)) * ((1 + ‖z‖) ^ (G.e + n) * Real.exp (-G.c * Real.sqrt ‖z‖)) := by
      have := G.hδb; have := G.hK; positivity
    have hA : 0 ≤ G.MH * (4 / G.r) ^ n := by have := G.hr; positivity
    unfold gluedEnvelope
    rw [if_pos hc.1, mul_one, add_mul]
    refine le_add_of_le_of_nonneg ?_ h0
    calc G.MH * (4 / G.r) ^ n = G.MH * (4 / G.r) ^ n * 1 := (mul_one _).symm
      _ ≤ G.MH * (4 / G.r) ^ n * ((1 + ‖z‖) ^ (G.e + n) *
            (Real.exp (G.c * Real.sqrt G.zc) * Real.exp (-G.c * Real.sqrt ‖z‖))) := by
          apply mul_le_mul_of_nonneg_left _ hA
          calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
            _ ≤ _ := mul_le_mul hW1 hexp zero_le_one (by positivity)
      _ = _ := by ring
  · have hF := G.F₀_le_size_of_not_central hc
    refine (G.outer_coeff hq hz hF n).2.trans ?_
    set X := 1 + cepsDriftFreqSize lam z
    have hsz : Real.sqrt ‖z‖ ≤ 1 + ‖z‖ := by
      nlinarith [Real.sq_sqrt (norm_nonneg z), Real.sqrt_nonneg ‖z‖]
    have hX : X ≤ (1 + |lam|) * (2 * (1 + ‖z‖)) := by
      simp only [X, cepsDriftFreqSize]
      nlinarith [abs_nonneg lam, norm_nonneg z, Real.sqrt_nonneg ‖z‖]
    have hX0 : 0 ≤ X := by simp only [X]; linarith [size_nonneg lam z]
    have hexp : Real.exp (-G.c * cepsDriftFreqSize lam z) =
        Real.exp (-G.c * |lam|) * Real.exp (-G.c * Real.sqrt ‖z‖) := by
      rw [← Real.exp_add]; congr 1; unfold cepsDriftFreqSize; ring
    have hmain : G.K * X ^ G.e * Real.exp (-G.c * cepsDriftFreqSize lam z) * (2 * X / G.δb) ^ n =
        G.K * (2 / G.δb) ^ n * X ^ (G.e + n) *
          (Real.exp (-G.c * |lam|) * Real.exp (-G.c * Real.sqrt ‖z‖)) := by
      rw [hexp, pow_add, div_pow, div_pow, mul_pow]
      ring
    rw [hmain]
    have hXp : X ^ (G.e + n) ≤ (1 + |lam|) ^ (G.e + n) * (2 ^ (G.e + n) * (1 + ‖z‖) ^ (G.e + n)) := by
      rw [← mul_pow, ← mul_pow]
      exact pow_le_pow_left₀ hX0 hX _
    have hB0 : 0 ≤ G.K * (2 / G.δb) ^ n := by have := G.hδb; have := G.hK; positivity
    have hA0 : 0 ≤ G.MH * (4 / G.r) ^ n * Real.exp (G.c * Real.sqrt G.zc) *
        (if |lam| < G.lc then (1 : ℝ) else 0) * ((1 + ‖z‖) ^ (G.e + n) *
          Real.exp (-G.c * Real.sqrt ‖z‖)) := by
      have := G.hr
      apply mul_nonneg (mul_nonneg (by positivity) (by split_ifs <;> norm_num)) (by positivity)
    unfold gluedEnvelope
    rw [add_mul]
    refine le_add_of_nonneg_of_le hA0 ?_
    calc G.K * (2 / G.δb) ^ n * X ^ (G.e + n) *
          (Real.exp (-G.c * |lam|) * Real.exp (-G.c * Real.sqrt ‖z‖))
        ≤ G.K * (2 / G.δb) ^ n * ((1 + |lam|) ^ (G.e + n) * (2 ^ (G.e + n) * (1 + ‖z‖) ^ (G.e + n))) *
          (Real.exp (-G.c * |lam|) * Real.exp (-G.c * Real.sqrt ‖z‖)) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXp hB0) (by positivity)
      _ = _ := by ring

end CepsGlueData

/-- On the imaginary axis a real positive variance gives no merger at nonzero drift. -/
theorem cepsMerger_ne_of_imaginary {v : ℝ} (hv : 0 < v) {lam : ℝ} (hl : lam ≠ 0) (y : ℝ) :
    Complex.I * y + (lam : ℂ) ^ 2 / (2 * (v : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have : ((lam : ℂ) ^ 2 / (2 * (v : ℂ))) = ((lam ^ 2 / (2 * v) : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.add_re, this, Complex.ofReal_re] at hre
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_self, zero_add, Complex.zero_re] at hre
  have : 0 < lam ^ 2 / (2 * v) := by positivity
  linarith


end PGM
