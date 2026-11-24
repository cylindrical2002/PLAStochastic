import PLAStochastic.Index.CEPS.Strip.FactorAnalytic

/-! # The complete subtracted time-operator pair on the outer strip

On `-δ ≤ Re z` and `F₀ ≤ F = |λ| + √‖z‖`, every padded finite complex vector in the
narrow variance box gives a jointly analytic complete subtracted pair with the envelope
`K X³ exp(-c F)`. For `λ < 1` the complete pair decays itself; on the positive tail the
half-line pair is subtracted and the difference is split as
`A²(O - Oₕ) + (A - Aₕ)(A + Aₕ)Oₕ`.
-/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsStrip_disc_decay {a κ X X' F F' : ℝ} (ha : 0 ≤ a) (hκ : 0 ≤ κ)
    (hX' : X' ≤ 2 * X) (hX'0 : 0 ≤ X') (hF : F ≤ F' + 1) :
    a * X' * Real.exp (-(κ * F')) ≤ 2 * a * Real.exp κ * X * Real.exp (-(κ * F)) := by
  have he : Real.exp (-(κ * F')) ≤ Real.exp κ * Real.exp (-(κ * F)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    a * X' * Real.exp (-(κ * F')) ≤ a * (2 * X) * (Real.exp κ * Real.exp (-(κ * F))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hX' ha) he (Real.exp_pos _).le
        (mul_nonneg ha (hX'0.trans hX'))
    _ = _ := by ring

theorem cepsStrip_disc_growth {a κ X X' F F' : ℝ} (ha : 0 ≤ a) (hκ : 0 ≤ κ)
    (hX' : X' ≤ 2 * X) (hX'0 : 0 ≤ X') (hF : F' ≤ F + 1) :
    a * X' * Real.exp (κ * F') ≤ 2 * a * Real.exp κ * X * Real.exp (κ * F) := by
  have he : Real.exp (κ * F') ≤ Real.exp κ * Real.exp (κ * F) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    a * X' * Real.exp (κ * F') ≤ a * (2 * X) * (Real.exp κ * Real.exp (κ * F)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hX' ha) he (Real.exp_pos _).le
        (mul_nonneg ha (hX'0.trans hX'))
    _ = _ := by ring

theorem cepsStrip_pair_left_bound {E A O : ℂ} {D F X a k T : ℝ}
    (hE : ‖E‖ ≤ Real.exp (D / 16 * F))
    (hA : ‖A‖ ≤ a * X * Real.exp (3 * D / 8 * F))
    (hO : ‖O‖ ≤ T * (k * X * Real.exp (-(15 * D / 16 * F)))) :
    ‖E * A ^ 2 * O‖ ≤ a ^ 2 * T * k * X ^ 3 * Real.exp (-(D / 8) * F) := by
  have hexp : Real.exp (D / 16 * F) * Real.exp (3 * D / 8 * F) ^ 2 *
      Real.exp (-(15 * D / 16 * F)) = Real.exp (-(D / 8) * F) := by
    rw [pow_two]
    simp only [← Real.exp_add]
    congr 1
    ring
  rw [norm_mul, norm_mul, norm_pow]
  calc
    ‖E‖ * ‖A‖ ^ 2 * ‖O‖ ≤ Real.exp (D / 16 * F) * (a * X * Real.exp (3 * D / 8 * F)) ^ 2 *
        (T * (k * X * Real.exp (-(15 * D / 16 * F)))) := by
      gcongr
    _ = a ^ 2 * T * k * X ^ 3 * (Real.exp (D / 16 * F) * Real.exp (3 * D / 8 * F) ^ 2 *
        Real.exp (-(15 * D / 16 * F))) := by ring
    _ = _ := by rw [hexp]

theorem cepsStrip_pair_right_bound {E A Ah O Oh : ℂ} {D F X a h c k₁ k₂ T : ℝ}
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hX : 1 ≤ X)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hc : 0 ≤ c) (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hT : 0 ≤ T)
    (hE : ‖E‖ ≤ Real.exp (D / 16 * F))
    (hA : ‖A‖ ≤ a * X) (hAh : ‖Ah‖ ≤ h)
    (hAA : ‖A - Ah‖ ≤ h * (c * X) * (2 * Real.exp (-(7 * D / 8 * F))))
    (hOO : ‖O - Oh‖ ≤ T * (k₁ * X * Real.exp (-(25 * D / 16 * F))))
    (hOh : ‖Oh‖ ≤ T * (k₂ * X * Real.exp (5 * D / 16 * F))) :
    ‖E * A ^ 2 * O - E * Ah ^ 2 * Oh‖ ≤
      (a ^ 2 * T * k₁ + 2 * h * c * (a + h) * T * k₂) * X ^ 3 *
        Real.exp (-(D / 8) * F) := by
  have hX0 : 0 ≤ X := by linarith
  have hid : E * A ^ 2 * O - E * Ah ^ 2 * Oh =
      E * (A ^ 2 * (O - Oh) + (A - Ah) * (A + Ah) * Oh) := by ring
  have hsum : ‖A + Ah‖ ≤ (a + h) * X := by
    calc
      ‖A + Ah‖ ≤ ‖A‖ + ‖Ah‖ := norm_add_le _ _
      _ ≤ a * X + h := add_le_add hA hAh
      _ ≤ (a + h) * X := by nlinarith
  have h1 : ‖A ^ 2 * (O - Oh)‖ ≤ (a * X) ^ 2 * (T * (k₁ * X * Real.exp (-(25 * D / 16 * F)))) := by
    rw [norm_mul, norm_pow]
    gcongr
  have h2 : ‖(A - Ah) * (A + Ah) * Oh‖ ≤ (h * (c * X) * (2 * Real.exp (-(7 * D / 8 * F)))) *
      ((a + h) * X) * (T * (k₂ * X * Real.exp (5 * D / 16 * F))) := by
    rw [norm_mul, norm_mul]
    gcongr
  have he1 : Real.exp (D / 16 * F) * Real.exp (-(25 * D / 16 * F)) ≤ Real.exp (-(D / 8) * F) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have he2 : Real.exp (D / 16 * F) * (Real.exp (-(7 * D / 8 * F)) * Real.exp (5 * D / 16 * F)) ≤
      Real.exp (-(D / 8) * F) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [hid, norm_mul]
  calc
    ‖E‖ * ‖A ^ 2 * (O - Oh) + (A - Ah) * (A + Ah) * Oh‖ ≤ Real.exp (D / 16 * F) *
        ((a * X) ^ 2 * (T * (k₁ * X * Real.exp (-(25 * D / 16 * F)))) +
          (h * (c * X) * (2 * Real.exp (-(7 * D / 8 * F)))) * ((a + h) * X) *
            (T * (k₂ * X * Real.exp (5 * D / 16 * F)))) :=
      mul_le_mul hE ((norm_add_le _ _).trans (add_le_add h1 h2)) (norm_nonneg _)
        (Real.exp_pos _).le
    _ = a ^ 2 * T * k₁ * X ^ 3 * (Real.exp (D / 16 * F) * Real.exp (-(25 * D / 16 * F))) +
        2 * h * c * (a + h) * T * k₂ * X ^ 3 *
          (Real.exp (D / 16 * F) * (Real.exp (-(7 * D / 8 * F)) * Real.exp (5 * D / 16 * F))) := by
      ring
    _ ≤ a ^ 2 * T * k₁ * X ^ 3 * Real.exp (-(D / 8) * F) +
        2 * h * c * (a + h) * T * k₂ * X ^ 3 * Real.exp (-(D / 8) * F) := by
      gcongr
    _ = _ := by ring

/-- Master outer-strip theorem: joint analyticity of the four factors and of the subtracted
pair, and the subtracted-pair envelope, with common constants. -/
theorem cepsComplexKernelStrip_master (d N : ℕ) {M vlo vhi F₀ : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi : vlo ≤ vhi) (hF₀ : 0 < F₀) :
    ∃ δ δb K c : ℝ, ∃ e : ℕ, 0 < δ ∧ 0 < δb ∧ 0 < c ∧
      ∀ q : Fin d → ℂ, ‖q‖ ≤ M →
        vlo ≤ (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re →
        ‖cepsComplexJetPad d q (cepsJetCode (.inl 0))‖ ≤ vhi →
        |(cepsComplexJetPad d q (cepsJetCode (.inl 0))).im| ≤
          (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re / 8 →
        ∀ (lam : ℝ) (z b : ℂ), -δ ≤ z.re → F₀ ≤ |lam| + Real.sqrt ‖z‖ →
          ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δb →
          (AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
              cepsComplexKernelBridgeJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
              (q, z, b) ∧
            AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
              cepsComplexKernelEntranceJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
              (q, z, b) ∧
            (1 ≤ lam →
              AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
                cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
                (q, z, b) ∧
              AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
                cepsComplexKernelHalfEntranceJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
                (q, z, b))) ∧
          AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
              cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
              (q, z, b) ∧
          ‖cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z b‖ ≤
            K * (1 + |lam| + Real.sqrt ‖z‖) ^ e * Real.exp (-c * (|lam| + Real.sqrt ‖z‖)) := by
  have hvhi : 0 < vhi := hlo.trans_le hhi
  have hvh : 0 < 2 * vhi := by positivity
  obtain ⟨δ₁, hδ₁, hAdm⟩ := cepsRootAdmissible_of_strip hlo hhi (by positivity : 0 < F₀ / 4)
  obtain ⟨δE, hδE, hEnv⟩ := cepsStripFactorEnvelope d N (vhi := 2 * vhi) hM hlo hvh
  let D := cepsFiniteRootPhaseLower vlo (2 * vhi)
  have hD : 0 < D := cepsFiniteRootPhaseLower_pos hlo hvh
  let ρ := min (δ₁ / 2) (min (F₀ ^ 2 / 8) 1)
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min (by positivity) one_pos)
  have hρδ : ρ ≤ δ₁ / 2 := min_le_left _ _
  have hρF : ρ ≤ F₀ ^ 2 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  let KA := cepsFiniteComplexEntranceConstant N M vlo (2 * vhi)
  let KB := cepsFiniteComplexBridgeConstant M vlo (2 * vhi)
  let KH := 4 * cepsFiniteQuadraticRootBound vlo *
    (2 * vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M))
  let C1 := cepsFiniteComplexSpatialConstant 1 M vlo (2 * vhi)
  let K1 := cepsFiniteComplexSlopeInverseConstant M vlo (2 * vhi)
  let KAh := Real.exp (((N : ℝ) + 1) ^ 3 * M) * (4 / vlo) / (7 * D / 16 * F₀)
  let T := 4 / ρ + 1
  have hKA : 0 < KA := cepsFiniteComplexEntranceConstant_pos N hlo hvh
  have hKB : 0 < KB := cepsFiniteComplexBridgeConstant_pos hlo hvh
  have hKH : 0 < KH := by
    have := cepsFiniteQuadraticRootBound_pos hlo
    dsimp [KH]
    positivity
  have hC1 : 0 < C1 := cepsFiniteComplexSpatialConstant_pos 1 hlo hvh
  have hK1 : 0 < K1 := cepsFiniteComplexSlopeInverseConstant_pos hlo hvh
  have hKAh : 0 < KAh := by dsimp [KAh]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  let kL := 2 * (KB * Real.exp (1 / vlo)) * Real.exp (15 * D / 16)
  let k₁ := 2 * KB * Real.exp (25 * D / 16)
  let k₂ := 2 * KH * Real.exp (5 * D / 16)
  let Kneg := (3 * KA) ^ 2 * T * kL
  let Kpos := (3 * KA) ^ 2 * T * k₁ + 2 * KAh * (C1 * K1) * (3 * KA + KAh) * T * k₂
  have hkL : 0 < kL := by dsimp [kL]; positivity
  have hk₁ : 0 < k₁ := by dsimp [k₁]; positivity
  have hk₂ : 0 < k₂ := by dsimp [k₂]; positivity
  have hKneg : 0 < Kneg := by dsimp [Kneg]; positivity
  have hKpos : 0 < Kpos := by dsimp [Kpos]; positivity
  refine ⟨δ₁ / 2, δE / 2, Kneg + Kpos, D / 8, 3, by positivity, by positivity, by positivity, ?_⟩
  intro q hq hv hhiq hi lam z b hz hF hb
  let P := cepsComplexJetPad d q
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hX1 : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hvh' : ‖P (cepsJetCode (.inl 0))‖ ≤ 2 * vhi := hhiq.trans (by linarith)
  -- admissibility and the envelope on the frequency disc
  have hdisc : ∀ z' ∈ ball z ρ, CepsRootAdmissible P vlo (2 * vhi) lam z' ∧
      ‖b‖ * (1 + |lam| + Real.sqrt ‖z'‖) ≤ δE ∧
      1 + |lam| + Real.sqrt ‖z'‖ ≤ 2 * X ∧
      F ≤ |lam| + Real.sqrt ‖z'‖ + 1 ∧ |lam| + Real.sqrt ‖z'‖ ≤ F + 1 := by
    intro z' hz'
    have hzz : ‖z' - z‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hz'
    obtain ⟨hre, hF', hlo', hhi'⟩ := cepsStrip_disc_geometry hF₀ hρ1 hρF hF hzz
    have hre' : -δ₁ ≤ z'.re := by linarith
    have hX' : 1 + |lam| + Real.sqrt ‖z'‖ ≤ 2 * X := by dsimp [X, F] at *; linarith
    refine ⟨hAdm P hv hhiq hi lam z' hre' hF', ?_, hX', hlo', hhi'⟩
    calc
      ‖b‖ * (1 + |lam| + Real.sqrt ‖z'‖) ≤ ‖b‖ * (2 * X) :=
        mul_le_mul_of_nonneg_left hX' (norm_nonneg _)
      _ = 2 * (‖b‖ * X) := by ring
      _ ≤ 2 * (δE / 2) := by gcongr
      _ = δE := by ring
  have hzball : z ∈ ball z ρ := mem_ball_self hρ
  obtain ⟨hadm, hbE, -, -, -⟩ := hdisc z hzball
  obtain ⟨hc, hden, hquot, hw, hwinv, hbn, hE, hBleft, hAgen, hpos⟩ :=
    hEnv q hq hv hvh' hi lam z b hadm hbE
  -- frequency differentiability on the disc
  have hBd : ∀ z' ∈ ball z ρ,
      DifferentiableAt ℂ (fun w => cepsComplexKernelBridgeJetModel P N lam w b) z' := by
    intro z' hz'
    obtain ⟨hadm', hb', -, -, -⟩ := hdisc z' hz'
    obtain ⟨hc', hden', hquot', -⟩ := hEnv q hq hv hvh' hi lam z' b hadm' hb'
    exact (cepsStrip_frequency_analyticAt
      (cepsComplexKernelFiniteFactors_joint_analyticAt hc' hden' hquot').1).differentiableAt
  have hmarkz : 0 ≤ lam → b * z - cepsComplexCumulantRootModel P N lam z (-1) N b ≠ 0 := by
    intro hl hzero
    have hm := (hpos hl).2.2.2.1
    rw [hzero, norm_zero] at hm
    have : 0 < 7 * D / 16 * F := by
      have hFp : 0 < F := hadm.pos
      positivity
    linarith
  have hBhd : 0 ≤ lam → ∀ z' ∈ ball z ρ,
      DifferentiableAt ℂ (fun w => cepsComplexKernelHalfBridgeJetModel P N lam w b) z' := by
    intro hl z' hz'
    obtain ⟨hadm', hb', -, -, -⟩ := hdisc z' hz'
    obtain ⟨hc', -, hquot', -, -, -, -, -, -, hpos'⟩ := hEnv q hq hv hvh' hi lam z' b hadm' hb'
    have hmark' : b * z' - cepsComplexCumulantRootModel P N lam z' (-1) N b ≠ 0 := by
      intro hzero
      have hm := (hpos' hl).2.2.2.1
      rw [hzero, norm_zero] at hm
      have : 0 < 7 * D / 16 * (|lam| + Real.sqrt ‖z'‖) := by
        have hFp : 0 < |lam| + Real.sqrt ‖z'‖ := hadm'.pos
        positivity
      linarith
    exact (cepsStrip_frequency_analyticAt
      (cepsComplexKernelHalfFactors_joint_analyticAt hc' hquot' hmark').2).differentiableAt
  refine ⟨⟨(cepsComplexKernelFiniteFactors_joint_analyticAt hc hden hquot).1,
      (cepsComplexKernelFiniteFactors_joint_analyticAt hc hden hquot).2, fun hl =>
        ⟨(cepsComplexKernelHalfFactors_joint_analyticAt hc hquot (hmarkz (by linarith))).2,
          (cepsComplexKernelHalfFactors_joint_analyticAt hc hquot (hmarkz (by linarith))).1⟩⟩,
    cepsComplexKernelSubtractedPairJetModel_joint_analyticAt hc hden hquot hw
      (fun hl => hmarkz (by linarith)), ?_⟩
  have hgoal : Real.exp (-(D / 8) * F) = Real.exp (-(D / 8) * (|lam| + Real.sqrt ‖z‖)) := rfl
  unfold cepsComplexKernelSubtractedPairJetModel
  by_cases hl : 1 ≤ lam
  · -- positive tail: subtract the half-line pair
    rw [if_pos hl]
    have hl0 : 0 ≤ lam := by linarith
    obtain ⟨hBB, hBh, hA, hmk, hAh, hAA⟩ := hpos hl0
    have hAh' : ‖cepsComplexKernelHalfEntranceJetModel P N lam z b‖ ≤ KAh := by
      apply hAh.trans
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hF (by positivity)
    have hAA' : ‖cepsComplexKernelEntranceJetModel P N lam z b -
        cepsComplexKernelHalfEntranceJetModel P N lam z b‖ ≤
        KAh * (C1 * K1 * X) * (2 * Real.exp (-(7 * D / 8 * F))) := by
      apply hAA.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hAh' (by positivity)
    -- the bridge difference on the disc
    have hOO : ‖(-(1 / (1 + b * lam)) *
          deriv (fun w => cepsComplexKernelBridgeJetModel P N lam w b) z -
          b * cepsComplexKernelBridgeJetModel P N lam z b) -
        (-(1 / (1 + b * lam)) *
          deriv (fun w => cepsComplexKernelHalfBridgeJetModel P N lam w b) z -
          b * cepsComplexKernelHalfBridgeJetModel P N lam z b)‖ ≤
        T * (k₁ * X * Real.exp (-(25 * D / 16 * F))) := by
      have he : (-(1 / (1 + b * lam)) *
            deriv (fun w => cepsComplexKernelBridgeJetModel P N lam w b) z -
            b * cepsComplexKernelBridgeJetModel P N lam z b) -
          (-(1 / (1 + b * lam)) *
            deriv (fun w => cepsComplexKernelHalfBridgeJetModel P N lam w b) z -
            b * cepsComplexKernelHalfBridgeJetModel P N lam z b) =
          -(1 / (1 + b * lam)) * deriv (fun w => cepsComplexKernelBridgeJetModel P N lam w b -
            cepsComplexKernelHalfBridgeJetModel P N lam w b) z -
            b * ((fun w => cepsComplexKernelBridgeJetModel P N lam w b -
              cepsComplexKernelHalfBridgeJetModel P N lam w b) z) := by
        rw [deriv_fun_sub (hBd z hzball) (hBhd hl0 z hzball)]
        ring
      rw [he]
      apply cepsStrip_timeOperator_norm_le hρ
        (fun z' hz' => (hBd z' hz').sub (hBhd hl0 z' hz')) _ hwinv hbn
      intro z' hz'
      obtain ⟨hadm', hb', hX', hFl, -⟩ := hdisc z' hz'
      obtain ⟨-, -, -, -, -, -, -, -, -, hpos'⟩ := hEnv q hq hv hvh' hi lam z' b hadm' hb'
      exact (hpos' hl0).1.trans (cepsStrip_disc_decay hKB.le (by positivity) hX'
        (by positivity) hFl)
    have hOh : ‖-(1 / (1 + b * lam)) *
          deriv (fun w => cepsComplexKernelHalfBridgeJetModel P N lam w b) z -
          b * cepsComplexKernelHalfBridgeJetModel P N lam z b‖ ≤
        T * (k₂ * X * Real.exp (5 * D / 16 * F)) := by
      apply cepsStrip_timeOperator_norm_le hρ (hBhd hl0) _ hwinv hbn
      intro z' hz'
      obtain ⟨hadm', hb', hX', -, hFu⟩ := hdisc z' hz'
      obtain ⟨-, -, -, -, -, -, -, -, -, hpos'⟩ := hEnv q hq hv hvh' hi lam z' b hadm' hb'
      exact (hpos' hl0).2.1.trans (cepsStrip_disc_growth hKH.le (by positivity) hX'
        (by positivity) hFu)
    have hbound := cepsStrip_pair_right_bound hD.le hF0 hX1 (by positivity) hKAh.le
      (by positivity) hk₁.le hk₂.le hT.le hE hA hAh' hAA' hOO hOh
    unfold cepsComplexKernelPairJetModel cepsComplexKernelHalfPairJetModel
    apply hbound.trans
    have hX3 : 0 ≤ X ^ 3 := by positivity
    have hle : (3 * KA) ^ 2 * T * k₁ + 2 * KAh * (C1 * K1) * (3 * KA + KAh) * T * k₂ ≤
        Kneg + Kpos := by dsimp [Kpos]; linarith
    calc
      _ ≤ (Kneg + Kpos) * X ^ 3 * Real.exp (-(D / 8) * F) := by
        gcongr
      _ = _ := by rw [hgoal]
  · -- drifts below one: the complete pair decays
    rw [if_neg hl, sub_zero]
    have hO : ‖-(1 / (1 + b * lam)) *
          deriv (fun w => cepsComplexKernelBridgeJetModel P N lam w b) z -
          b * cepsComplexKernelBridgeJetModel P N lam z b‖ ≤
        T * (kL * X * Real.exp (-(15 * D / 16 * F))) := by
      apply cepsStrip_timeOperator_norm_le hρ hBd _ hwinv hbn
      intro z' hz'
      obtain ⟨hadm', hb', hX', hFl, -⟩ := hdisc z' hz'
      obtain ⟨-, -, -, -, -, -, -, hBleft', -⟩ := hEnv q hq hv hvh' hi lam z' b hadm' hb'
      exact (hBleft' (not_le.mp hl).le).1.trans (cepsStrip_disc_decay (by positivity)
        (by positivity) hX' (by positivity) hFl)
    have hbound := cepsStrip_pair_left_bound hE hAgen hO
    unfold cepsComplexKernelPairJetModel
    apply hbound.trans
    have hle : (3 * KA) ^ 2 * T * kL ≤ Kneg + Kpos := by dsimp only [Kneg]; linarith
    calc
      _ ≤ (Kneg + Kpos) * X ^ 3 * Real.exp (-(D / 8) * F) := by
        gcongr
      _ = _ := by rw [hgoal]

/-- **(S1)** The complete subtracted time-operator pair on the outer strip. -/
theorem cepsComplexKernelSubtractedPair_strip_budget (d N : ℕ) {M vlo vhi F₀ : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi : vlo ≤ vhi) (hF₀ : 0 < F₀) :
    ∃ δ δb K c : ℝ, ∃ e : ℕ, 0 < δ ∧ 0 < δb ∧ 0 < c ∧
      ∀ q : Fin d → ℂ, ‖q‖ ≤ M →
        vlo ≤ (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re →
        ‖cepsComplexJetPad d q (cepsJetCode (.inl 0))‖ ≤ vhi →
        |(cepsComplexJetPad d q (cepsJetCode (.inl 0))).im| ≤
          (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re / 8 →
        ∀ (lam : ℝ) (z b : ℂ), -δ ≤ z.re → F₀ ≤ |lam| + Real.sqrt ‖z‖ →
          ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δb →
          AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
              cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
              (q, z, b) ∧
          ‖cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z b‖ ≤
            K * (1 + |lam| + Real.sqrt ‖z‖) ^ e * Real.exp (-c * (|lam| + Real.sqrt ‖z‖)) := by
  obtain ⟨δ, δb, K, c, e, hδ, hδb, hc, h⟩ := cepsComplexKernelStrip_master d N hM hlo hhi hF₀
  exact ⟨δ, δb, K, c, e, hδ, hδb, hc, fun q hq hv hhiq hi lam z b hz hF hb =>
    (h q hq hv hhiq hi lam z b hz hF hb).2⟩

/-- The four complete-pair factors are joint germs at `(q, z, b)` on the outer strip; the
half-line factors on the positive tail. The master theorem gives the same `δ`, `δb` as (S1). -/
theorem cepsComplexKernelFactors_strip_analytic (d N : ℕ) {M vlo vhi F₀ : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi : vlo ≤ vhi) (hF₀ : 0 < F₀) :
    ∃ δ δb : ℝ, 0 < δ ∧ 0 < δb ∧
      ∀ q : Fin d → ℂ, ‖q‖ ≤ M →
        vlo ≤ (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re →
        ‖cepsComplexJetPad d q (cepsJetCode (.inl 0))‖ ≤ vhi →
        |(cepsComplexJetPad d q (cepsJetCode (.inl 0))).im| ≤
          (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re / 8 →
        ∀ (lam : ℝ) (z b : ℂ), -δ ≤ z.re → F₀ ≤ |lam| + Real.sqrt ‖z‖ →
          ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δb →
          AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
              cepsComplexKernelBridgeJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
              (q, z, b) ∧
          AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
              cepsComplexKernelEntranceJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
              (q, z, b) ∧
          (1 ≤ lam →
            AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
                cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
                (q, z, b) ∧
            AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
                cepsComplexKernelHalfEntranceJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
                (q, z, b)) := by
  obtain ⟨δ, δb, _K, _c, _e, hδ, hδb, _hc, h⟩ := cepsComplexKernelStrip_master d N hM hlo hhi hF₀
  exact ⟨δ, δb, hδ, hδb, fun q hq hv hhiq hi lam z b hz hF hb =>
    (h q hq hv hhiq hi lam z b hz hF hb).1⟩

end PGM
