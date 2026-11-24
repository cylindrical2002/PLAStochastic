import PLAStochastic.Index.CEPS.Strip.FactorAnalytic

/-! # The marked endpoint on the strip `-δ ≤ Re z`

The marked endpoint uses the fixed drift `λ = 1`, so `F = 1 + √‖z‖ ≥ 1` and the whole
strip is admissible. The half-line bridge carries the upper-root decay, while the half-line
entrance stays bounded by the marker gap.
-/

noncomputable section
open Complex Set
namespace PGM

/-- **(S2)** Joint analyticity and square-root frequency decay of the marked endpoint. -/
theorem cepsComplexKernelMarkedEndpoint_strip_budget (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi : vlo ≤ vhi) :
    ∃ δ δb K c : ℝ, ∃ e : ℕ, 0 < δ ∧ 0 < δb ∧ 0 < c ∧
      ∀ q : Fin d → ℂ, ‖q‖ ≤ M →
        vlo ≤ (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re →
        ‖cepsComplexJetPad d q (cepsJetCode (.inl 0))‖ ≤ vhi →
        |(cepsComplexJetPad d q (cepsJetCode (.inl 0))).im| ≤
          (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re / 8 →
        ∀ z b : ℂ, -δ ≤ z.re → ‖b‖ * (1 + Real.sqrt ‖z‖) ≤ δb →
          AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
              cepsComplexKernelMarkedEndpointJetModel (cepsComplexJetPad d v.1) N v.2.1 v.2.2)
              (q, z, b) ∧
          ‖cepsComplexKernelMarkedEndpointJetModel (cepsComplexJetPad d q) N z b‖ ≤
            K * (1 + Real.sqrt ‖z‖) ^ e * Real.exp (-c * Real.sqrt ‖z‖) := by
  have hvhi : 0 < vhi := hlo.trans_le hhi
  have hvh : 0 < 2 * vhi := by positivity
  obtain ⟨δ₁, hδ₁, hAdm⟩ := cepsRootAdmissible_of_strip hlo hhi one_pos
  obtain ⟨δE, hδE, hEnv⟩ := cepsStripFactorEnvelope d N (vhi := 2 * vhi) hM hlo hvh
  let D := cepsFiniteRootPhaseLower vlo (2 * vhi)
  have hD : 0 < D := cepsFiniteRootPhaseLower_pos hlo hvh
  let EB := Real.exp (((N : ℝ) + 1) ^ 3 * M)
  let KAh := EB * (4 / vlo) / (7 * D / 16)
  let KH := 4 * cepsFiniteQuadraticRootBound vlo *
    (2 * vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M))
  have hKH : 0 < KH := by
    have := cepsFiniteQuadraticRootBound_pos hlo
    dsimp [KH]
    positivity
  have hKAh : 0 < KAh := by dsimp [KAh, EB]; positivity
  let C := EB * KAh * (KH * Real.exp (1 / vlo))
  have hC : 0 < C := by dsimp [C, EB]; positivity
  refine ⟨δ₁, min (δE / 2) (1 / 4), 2 * C, 7 * D / 8, 1, hδ₁, by positivity, by positivity, ?_⟩
  intro q hq hv hhiq hi z b hz hb
  let P := cepsComplexJetPad d q
  let s := Real.sqrt ‖z‖
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hone : |(1 : ℝ)| = 1 := abs_one
  have hvh' : ‖P (cepsJetCode (.inl 0))‖ ≤ 2 * vhi := hhiq.trans (by linarith)
  have hF : (1 : ℝ) ≤ |(1 : ℝ)| + Real.sqrt ‖z‖ := by
    rw [hone]; linarith [Real.sqrt_nonneg ‖z‖]
  have hadm := hAdm P hv hhiq hi 1 z hz hF
  have hX2 : 1 + |(1 : ℝ)| + Real.sqrt ‖z‖ ≤ 2 * (1 + Real.sqrt ‖z‖) := by
    rw [hone]; linarith [Real.sqrt_nonneg ‖z‖]
  have hbX : ‖b‖ * (1 + |(1 : ℝ)| + Real.sqrt ‖z‖) ≤ 2 * (‖b‖ * (1 + Real.sqrt ‖z‖)) := by
    calc
      _ ≤ ‖b‖ * (2 * (1 + Real.sqrt ‖z‖)) := mul_le_mul_of_nonneg_left hX2 (norm_nonneg _)
      _ = _ := by ring
  have hbE : ‖b‖ * (1 + |(1 : ℝ)| + Real.sqrt ‖z‖) ≤ δE := by
    have := hb.trans (min_le_left _ _)
    linarith
  have hbM : ‖b‖ * (1 + |(1 : ℝ)| + Real.sqrt ‖z‖) ≤ 1 / 2 := by
    have h1 : ‖b‖ * (1 + Real.sqrt ‖z‖) ≤ 1 / 4 := hb.trans (min_le_right _ _)
    calc
      _ ≤ 2 * (‖b‖ * (1 + Real.sqrt ‖z‖)) := hbX
      _ ≤ 2 * (1 / 4) := by gcongr
      _ = 1 / 2 := by norm_num
  obtain ⟨hc, -, hquot, -, -, -, hE, hBleft, -, hpos⟩ := hEnv q hq hv hvh' hi 1 z b hadm hbE
  obtain ⟨-, -, -, hmk, hAh, -⟩ := hpos zero_le_one
  have hFpos : 0 < |(1 : ℝ)| + Real.sqrt ‖z‖ := hadm.pos
  have hmark : b * z - cepsComplexCumulantRootModel P N 1 z (-1) N b ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hmk
    have : 0 < 7 * D / 16 * (|(1 : ℝ)| + Real.sqrt ‖z‖) := by positivity
    linarith
  refine ⟨cepsComplexKernelMarkedEndpointJetModel_analyticAt (U := univ) isOpen_univ
    (mem_univ _) N (p := fun v : (Fin d → ℂ) × ℂ × ℂ => cepsComplexJetPad d v.1)
    (b := fun v => v.2.2) (z := fun v => v.2.1)
    (cepsComplexJetPad_fst_analyticOnNhd d) (cepsStrip_analyticOnNhd_scale d)
    (cepsStrip_analyticOnNhd_freq d) hc hquot hmark, ?_⟩
  -- the four factors
  have hw1 : (1 + b * ((1 : ℝ) : ℂ)) = 1 + b := by rw [ofReal_one, mul_one]
  have hE' : ‖exp ((b * z) * (1 + b))‖ ≤ Real.exp (D / 16 * (1 + s)) := by
    have h := hE
    rw [hw1, hone] at h
    exact h
  have hL := cepsComplexKernelMarker_exp_uniform_budget d N hM q hq 1 z b hbM
  rw [ofReal_one, mul_one] at hL
  have hAh' : ‖cepsComplexKernelHalfEntranceJetModel P N 1 z b‖ ≤ KAh := by
    apply hAh.trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : (1 : ℝ) ≤ |(1 : ℝ)| + Real.sqrt ‖z‖ := hF
    calc
      7 * D / 16 = 7 * D / 16 * 1 := (mul_one _).symm
      _ ≤ 7 * D / 16 * (|(1 : ℝ)| + Real.sqrt ‖z‖) :=
        mul_le_mul_of_nonneg_left this (by positivity)
  have hBh := (hBleft le_rfl).2
  rw [hone] at hBh
  change ‖cepsComplexKernelHalfBridgeJetModel P N 1 z b‖ ≤
    KH * Real.exp (1 / vlo) * (1 + 1 + s) * Real.exp (-(15 * D / 16 * (1 + s))) at hBh
  unfold cepsComplexKernelMarkedEndpointJetModel
  rw [norm_mul, norm_mul, norm_mul]
  have hexp : Real.exp (D / 16 * (1 + s)) * Real.exp (-(15 * D / 16 * (1 + s))) ≤
      Real.exp (-(7 * D / 8) * s) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ Real.exp (D / 16 * (1 + s)) * EB * KAh *
        (KH * Real.exp (1 / vlo) * (1 + 1 + s) * Real.exp (-(15 * D / 16 * (1 + s)))) := by
      gcongr
    _ = C * (1 + 1 + s) * (Real.exp (D / 16 * (1 + s)) * Real.exp (-(15 * D / 16 * (1 + s)))) := by
      dsimp only [C]
      ring
    _ ≤ C * (2 * (1 + s)) * Real.exp (-(7 * D / 8) * s) := by
      gcongr
      linarith
    _ = 2 * C * (1 + Real.sqrt ‖z‖) ^ 1 * Real.exp (-(7 * D / 8) * Real.sqrt ‖z‖) := by
      dsimp only [s]
      ring

end PGM
