import PLAStochastic.Index.GEP.Shadow.PairedEnvelope
import PLAStochastic.Index.GEP.Shadow.FirstLayerEnvelope
import PLAStochastic.Index.GEP.Shadow.ExpMoments

/-!
# WP3: the actual shadow layers satisfy the paired hypotheses

The inputs of `pairedLaw_envelope` for the actual normalised pairs `shPair P eps g ℓ`, `ℓ ≥ 1`
(`memory-route.md` §3–4), all with constants depending only on `μ₀, σ₀`:

* `momClass_of_expMom`: a positive mean-one law with `E e^{θX} ≤ B` and variance in
  `[vmin, b]` is in `MomClass b (expBeta θ B vmin) vmin`; the third-moment constant comes from
  `x³ ≤ 6 e^{θx}/θ³` and does **not** depend on a density bound, so the class constants are
  fixed before the envelope constants are chosen.
* `shLaw_momClass`: for `ℓ ≥ 1` the passive law `η_ℓ` is in
  `MomClass KcIn (expBeta (θK/2) CK (vIn/4)) (vIn/4)`, from `E e^{(θK/2) Y} ≤ CK`
  (`expMom_shLawPM`) and `shLaw_variance_bracket`.
* `LayerOK.measureReal_segLen_gt_le`: the actual stopping tail of any `LayerOK` layer,
  `P(T > m) ≤ (72/71) e^{-tailRate · vmin · m / eps²}` (the argument of
  `measureReal_layerSegLen_gt_le_exp`, with the variance ratio bounded below by `vmin`).
* `pairedHyp_shPair`: `PairedHyp` for the actual pairs, with `At = 72/71`,
  `aT = tailRate · vIn`, `δ = shKd / eps²`, `shKd = (σ₀²/μ₀² + 1) cBr`
  (`shDist_sq_le_first_scale`); the active mean bracket `eps²/(128 bIn) ≤ C_X ≤ cPlus eps²/vIn`
  is `actMean_shPair_bracket`.

Active positivity uses the raw support hypothesis `hpos` (`ae_pos_shPair_fst`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ## The moment class from an exponential moment -/

/-- The third-moment constant of a law with `E e^{θX} ≤ B` and variance at least `vmin`. -/
def expBeta (θ B vmin : ℝ) : ℝ := max 1 ((1 + 6 * B / θ ^ 3) / Real.sqrt vmin ^ 3)

theorem one_le_expBeta (θ B vmin : ℝ) : 1 ≤ expBeta θ B vmin := le_max_left _ _

/-- `x³ ≤ 6 e^{θx}/θ³` for `x ≥ 0`. -/
theorem pow_three_le_exp {θ x : ℝ} (hθ : 0 < θ) (hx : 0 ≤ x) :
    x ^ 3 ≤ 6 / θ ^ 3 * Real.exp (θ * x) := by
  have h : (θ * x) ^ 3 / 6 ≤ Real.exp (θ * x) := by
    have := Real.pow_div_factorial_le_exp (θ * x) (by positivity) 3
    simpa [Nat.factorial] using this
  rw [show 6 / θ ^ 3 * Real.exp (θ * x) = 6 * Real.exp (θ * x) / θ ^ 3 by ring,
    le_div_iff₀ (by positivity)]
  calc x ^ 3 * θ ^ 3 = (θ * x) ^ 3 := by ring
    _ ≤ 6 * Real.exp (θ * x) := by linarith

/-- `|x - 1|³ ≤ 1 + x³` for `x ≥ 0`. -/
theorem abs_sub_one_pow_three_le {x : ℝ} (hx : 0 ≤ x) : |x - 1| ^ 3 ≤ 1 + x ^ 3 := by
  rcases le_total x 1 with h | h
  · rw [abs_of_nonpos (by linarith)]
    have h1 : (-(x - 1)) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h2 : 0 ≤ x ^ 3 := by positivity
    linarith
  · rw [abs_of_nonneg (by linarith)]
    have h1 : (x - 1) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    linarith

/-- **The moment class from an exponential moment**: the constants do not involve any density
bound. -/
theorem momClass_of_expMom {θ B vmin b : ℝ} (hθ : 0 < θ) (hvmin : 0 < vmin)
    {ρ : ProbabilityMeasure ℝ} (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (hexp : ExpMom θ B ρ)
    (hmean : lawMean ρ = 1) (hvlo : vmin ≤ lawVar ρ) (hvhi : lawVar ρ ≤ b) :
    MomClass b (expBeta θ B vmin) vmin ρ := by
  have hae : ∀ᵐ x ∂(ρ : Measure ℝ), 0 < x := by
    filter_upwards [compl_mem_ae_iff.2 hpos] with x hx
    simpa using hx
  have hB : 0 < B := (integral_exp_pos hexp.integrable).trans_le hexp.le
  have hdom : Integrable (fun x => 1 + 6 / θ ^ 3 * Real.exp (θ * x)) (ρ : Measure ℝ) :=
    (integrable_const _).add (hexp.integrable.const_mul _)
  have hdom0 : ∀ x, 0 ≤ 1 + 6 / θ ^ 3 * Real.exp (θ * x) := fun x => by positivity
  -- the third absolute moment
  have hx3 : Integrable (fun x : ℝ => |x| ^ (3 : ℝ)) (ρ : Measure ℝ) := by
    refine hdom.mono' (continuous_abs.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable
      ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos hx,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have := pow_three_le_exp hθ hx.le
    linarith
  have hmem : MemLp id 3 (ρ : Measure ℝ) := by
    rw [← integrable_norm_rpow_iff aestronglyMeasurable_id (by norm_num) (by norm_num)]
    simpa only [id, Real.norm_eq_abs, ENNReal.toReal_ofNat] using hx3
  have hle3 : ∀ᵐ x ∂(ρ : Measure ℝ), ‖|x - 1| ^ 3‖ ≤ 1 + 6 / θ ^ 3 * Real.exp (θ * x) := by
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := abs_sub_one_pow_three_le hx.le
    have h2 := pow_three_le_exp hθ hx.le
    linarith
  have hint3 : Integrable (fun x => |x - 1| ^ 3) (ρ : Measure ℝ) :=
    hdom.mono' (by fun_prop) hle3
  have hthird : ∫ x, |x - 1| ^ 3 ∂(ρ : Measure ℝ) ≤ 1 + 6 * B / θ ^ 3 := by
    calc ∫ x, |x - 1| ^ 3 ∂(ρ : Measure ℝ)
        ≤ ∫ x, (1 + 6 / θ ^ 3 * Real.exp (θ * x)) ∂(ρ : Measure ℝ) :=
          integral_mono_ae hint3 hdom (hle3.mono fun x hx => by
            rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hx)
      _ = 1 + 6 / θ ^ 3 * ∫ x, Real.exp (θ * x) ∂(ρ : Measure ℝ) := by
          rw [integral_add (integrable_const _) (hexp.integrable.const_mul _), integral_const,
            integral_const_mul, probReal_univ, one_smul]
      _ ≤ 1 + 6 / θ ^ 3 * B := by gcongr; exact hexp.le
      _ = 1 + 6 * B / θ ^ 3 := by ring
  have hsq : Real.sqrt vmin ^ 3 ≤ Real.sqrt (lawVar ρ) ^ 3 := by
    gcongr
  have hsv : 0 < Real.sqrt vmin ^ 3 := by positivity
  refine ⟨hpos, hmem, hmean, hvlo, hvhi, ?_⟩
  calc ∫ x, |x - 1| ^ 3 ∂(ρ : Measure ℝ) ≤ 1 + 6 * B / θ ^ 3 := hthird
    _ = (1 + 6 * B / θ ^ 3) / Real.sqrt vmin ^ 3 * Real.sqrt vmin ^ 3 := by field_simp
    _ ≤ expBeta θ B vmin * Real.sqrt (lawVar ρ) ^ 3 :=
        mul_le_mul (le_max_right _ _) hsq hsv.le (le_trans zero_le_one (one_le_expBeta _ _ _))

/-! ## The stopping tail of an actual layer -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The first-segment tail of any `LayerOK` layer:
`P(T > m) ≤ (72/71) e^{-tailRate vmin m/eps²}`. -/
theorem LayerOK.measureReal_segLen_gt_le {Z : ℕ → Ω → ℝ × ℕ} {b β vmin Kc eps : ℝ}
    (hL : LayerOK P Z b β vmin Kc) (heps : epsZero b β ≤ eps) (m : ℕ) :
    P.real {ω | (m : ℕ∞) < pairSegLen eps (seq Z ω)} ≤
      72 / 71 * Real.exp (-(tailRate * vmin) * m / eps ^ 2) := by
  set μ := lmean P Z with hμdef
  set σ := lsig P Z with hσdef
  set κ := lkap P Z with hκdef
  have hX := hL.law
  have hμ := hX.mu_pos
  have hσ := hX.sigma_pos
  have hκ0 : 0 ≤ κ := le_trans (integral_nonneg fun _ => by positivity) hX.third
  have hv : σ ^ 2 ≤ b * μ ^ 2 := hL.var_le
  have hβ : κ ≤ β * σ ^ 3 := hL.third_le
  have hvg : vmin * μ ^ 2 ≤ σ ^ 2 := hL.var_ge
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hepspos : 0 < eps := by linarith
  obtain ⟨c1, c2, c3, c4, -, -, -⟩ := largeConditions hμ hσ hκ0 hv hβ heps
  set G := μ ^ 2 * eps ^ 2 / σ ^ 2 with hG
  obtain ⟨L, hL1, hLG, htail⟩ := layerSegLen_tail_of_large hX hepspos hG c1 c2 c3 c4
  set j := m / L with hj
  have hseg : ∀ ω, pairSegLen eps (seq Z ω) = layerSegLen eps (fun t ω => (Z t ω).1) ω :=
    fun _ => rfl
  have hsub : {ω | (m : ℕ∞) < pairSegLen eps (seq Z ω)} ⊆
      {ω | ((j * L : ℕ) : ℕ∞) < layerSegLen eps (fun t ω => (Z t ω).1) ω} := by
    intro ω hω
    have : j * L ≤ m := Nat.div_mul_le_self m L
    rw [Set.mem_ofPred_eq, ← hseg]
    exact lt_of_le_of_lt (show ((j * L : ℕ) : ℕ∞) ≤ (m : ℕ∞) from Nat.cast_le.2 this) hω
  have hP : P.real {ω | (m : ℕ∞) < pairSegLen eps (seq Z ω)} ≤ (71 / 72 : ℝ) ^ j :=
    (measureReal_mono hsub).trans (htail j)
  have hmL : (m : ℝ) < (j + 1) * L := by
    have : m < j * L + L := Nat.lt_div_mul_add (by omega)
    have : (m : ℝ) < (j * L + L : ℕ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hLv : (L : ℝ) * (σ ^ 2 / μ ^ 2) ≤ 5185 * eps ^ 2 := by
    have h1 : (L : ℝ) * (σ ^ 2 / μ ^ 2) ≤ 5185 * G * (σ ^ 2 / μ ^ 2) :=
      mul_le_mul_of_nonneg_right hLG (by positivity)
    refine h1.trans (le_of_eq ?_)
    have hμ' : μ ≠ 0 := hμ.ne'
    have hσ' : σ ≠ 0 := hσ.ne'
    rw [hG]
    field_simp
  have hvr : vmin ≤ σ ^ 2 / μ ^ 2 := by rw [le_div_iff₀ hμ2]; exact hvg
  have ha : 0 < Real.log (72 / 71) := Real.log_pos (by norm_num)
  have hkey : tailRate * vmin * m / eps ^ 2 ≤ Real.log (72 / 71) * (j + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : vmin * m ≤ (j + 1) * 5185 * eps ^ 2 := by
      have hm0 : (0 : ℝ) ≤ m := by positivity
      have e1 : vmin * m ≤ (σ ^ 2 / μ ^ 2) * m := mul_le_mul_of_nonneg_right hvr hm0
      have e2 : (σ ^ 2 / μ ^ 2) * m ≤ (σ ^ 2 / μ ^ 2) * ((j + 1) * L) :=
        mul_le_mul_of_nonneg_left hmL.le (by positivity)
      have hj0 : (0 : ℝ) ≤ j + 1 := by positivity
      have e3 : (σ ^ 2 / μ ^ 2) * ((j + 1) * L) = (j + 1) * ((L : ℝ) * (σ ^ 2 / μ ^ 2)) := by ring
      have e4 : (j + 1) * ((L : ℝ) * (σ ^ 2 / μ ^ 2)) ≤ (j + 1) * (5185 * eps ^ 2) :=
        mul_le_mul_of_nonneg_left hLv hj0
      linarith
    unfold tailRate
    calc Real.log (72 / 71) / 5185 * vmin * m = Real.log (72 / 71) / 5185 * (vmin * m) := by
          ring
      _ ≤ Real.log (72 / 71) / 5185 * ((j + 1) * 5185 * eps ^ 2) := by gcongr
      _ = Real.log (72 / 71) * (j + 1) * eps ^ 2 := by ring
  have e1 : (71 / 72 : ℝ) ^ j = Real.exp (Real.log (72 / 71)) *
      Real.exp (-(Real.log (72 / 71) * (j + 1))) := by
    rw [← Real.exp_add, show Real.log (72 / 71) + -(Real.log (72 / 71) * (j + 1)) =
      j * (-Real.log (72 / 71)) by ring, Real.exp_nat_mul, Real.exp_neg,
      Real.exp_log (by norm_num)]
    norm_num
  refine hP.trans ?_
  rw [e1, Real.exp_log (by norm_num)]
  gcongr
  rw [neg_mul, neg_div]
  linarith

/-! ## The fixed constants of the actual shadow orbit -/

/-- `vIn ≤ 1/2`. -/
theorem vIn_le_half (μ₀ σ₀ : ℝ) : vIn μ₀ σ₀ ≤ 1 / 2 := by
  have h1 := vIn_le μ₀ σ₀
  have h2 : deltaVar ≤ 1 := by
    unfold deltaVar
    exact pow_le_one₀ (by norm_num) (by norm_num)
  linarith

/-- The lower passive variance of the shadow orbit, `vIn/4`. -/
def shVlo (μ₀ σ₀ : ℝ) : ℝ := vIn μ₀ σ₀ / 4

/-- The third-moment constant of the shadow orbit. -/
def shBeta (μ₀ σ₀ : ℝ) : ℝ := expBeta (θK / 2) CK (shVlo μ₀ σ₀)

/-- The residual constant `(σ₀²/μ₀² + 1) cBr`: `E (X_ℓ - Y_ℓ)² ≤ shKd / eps²` for `ℓ ≥ 1`. -/
def shKd (μ₀ σ₀ : ℝ) : ℝ := (σ₀ ^ 2 / μ₀ ^ 2 + 1) * cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀)

/-- The active stopping-tail rate `tailRate · vIn`. -/
def shAT (μ₀ σ₀ : ℝ) : ℝ := tailRate * vIn μ₀ σ₀

theorem shVlo_pos {μ₀ σ₀ : ℝ} (hμ : 0 < μ₀) (hσ : 0 < σ₀) : 0 < shVlo μ₀ σ₀ := by
  unfold shVlo; have := vIn_pos hμ hσ; positivity

theorem shVlo_le_KcIn (μ₀ σ₀ : ℝ) : shVlo μ₀ σ₀ ≤ KcIn := by
  unfold shVlo; have := vIn_le_half μ₀ σ₀; have := one_le_KcIn; linarith

theorem one_le_shBeta (μ₀ σ₀ : ℝ) : 1 ≤ shBeta μ₀ σ₀ := one_le_expBeta _ _ _

theorem shKd_nonneg (μ₀ σ₀ : ℝ) : 0 ≤ shKd μ₀ σ₀ := by
  unfold shKd
  have hcb : 0 < cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) :=
    lt_of_lt_of_le (by have := bAbs_pos.trans_le (bAbs_le_bIn μ₀ σ₀); positivity)
      (le_max_left _ _)
  positivity

theorem shAT_pos {μ₀ σ₀ : ℝ} (hμ : 0 < μ₀) (hσ : 0 < σ₀) : 0 < shAT μ₀ σ₀ := by
  unfold shAT; have := vIn_pos hμ hσ; have := tailRate_pos; positivity

/-- The scale conditions on `eps` used along the actual orbit: the exponential-moment threshold
`epsK` (which contains `epsZero`) and the two conditions of `shLaw_variance_bracket`. -/
structure ShScale (P : Measure Ω) (g : ℕ → Ω → ℝ) (μ₀ σ₀ eps : ℝ) : Prop where
  epsK_le : epsK (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps
  scale : cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) ≤ eps ^ 2
  small : 4 * cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) * (σ₀ ^ 2 / μ₀ ^ 2 + 1) ≤ vIn μ₀ σ₀ * eps ^ 2

variable {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ eps : ℝ}

omit [IsProbabilityMeasure P] in
theorem ShScale.epsZero_le (hs : ShScale P g μ₀ σ₀ eps) :
    epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps :=
  epsZero_le_of_epsK_le hs.epsK_le

/-! ## The passive class of the shadow laws -/

/-- For `ℓ ≥ 1` the shadow law is in a fixed moment class. -/
theorem shLaw_momClass (hg : GapLaw P g μ₀ σ₀ κ₀) (hs : ShScale P g μ₀ σ₀ eps) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) :
    MomClass KcIn (shBeta μ₀ σ₀) (shVlo μ₀ σ₀) (shLawPM P hg.iid.measurable eps ℓ) := by
  have heps := hs.epsZero_le
  have hbr := shLaw_variance_bracket hg heps hs.scale hs.small hℓ
  exact momClass_of_expMom (by have := θK_pos; positivity) (shVlo_pos hg.mu_pos hg.sigma_pos)
    (shLaw_pos hg heps ℓ) (expMom_shLawPM hg hs.epsK_le ℓ) (lawMean_shLawPM hg heps ℓ)
    hbr.1 hbr.2

/-! ## The active stop of the actual pairs -/

/-- The active mean bracket `eps²/(128 bIn) ≤ C_X ≤ cPlus eps² / vIn`. -/
theorem actMean_shPair_bracket (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    1 / (128 * bIn μ₀ σ₀) * eps ^ 2 ≤ actMean eps (shP P) (shPair P eps g ℓ) ∧
      actMean eps (shP P) (shPair P eps g ℓ) ≤ cPlus / vIn μ₀ σ₀ * eps ^ 2 := by
  have hL := layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ
  rw [actMean_shPair_eq_segMean hg heps]
  constructor
  · calc 1 / (128 * bIn μ₀ σ₀) * eps ^ 2 = eps ^ 2 / (128 * bIn μ₀ σ₀) := by ring
      _ ≤ _ := hL.2.2.2.1
  · calc segMean P eps (epLayerSeq eps g ℓ) ≤ cPlus * eps ^ 2 / vIn μ₀ σ₀ := hL.2.2.2.2
      _ = cPlus / vIn μ₀ σ₀ * eps ^ 2 := by ring

/-- The active stopping tail of the actual pairs, on the product space. -/
theorem measureReal_actLen_shPair_gt_le (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ R : ℕ) :
    (shP P).real {p | (R : ℕ∞) < actLen eps (shPair P eps g ℓ) p} ≤
      72 / 71 * Real.exp (-(shAT μ₀ σ₀ * R / eps ^ 2)) := by
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1
  have h := hL.measureReal_segLen_gt_le heps R
  set S : Set Ω := {ω | (R : ℕ∞) < pairSegLen eps (seq (epLayerSeq eps g ℓ) ω)} with hSdef
  have hset : {p : Ω × (ℕ → ℝ) | (R : ℕ∞) < actLen eps (shPair P eps g ℓ) p} =
      Prod.fst ⁻¹' S := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hSdef,
      actLen_shPair_eq eps g ℓ (shMean_pos hg heps ℓ).ne']
  have hmeas : MeasurableSet S :=
    ((isStoppingRule_pairSegLen eps).measurable.comp
      (measurable_seq fun t => measurable_epLayerSeq_entry hg.iid.measurable eps ℓ t))
      (MeasurableSet.of_discrete : MeasurableSet (Set.Ioi (R : ℕ∞)))
  have hmp : MeasurePreserving Prod.fst (shP P) P := measurePreserving_fst
  rw [hset, measureReal_def, hmp.measure_preimage hmeas.nullMeasurableSet, ← measureReal_def]
  refine h.trans (le_of_eq ?_)
  unfold shAT
  congr 2
  ring

/-- **The paired hypotheses for the actual shadow pairs** at every layer `ℓ ≥ 1`. -/
theorem pairedHyp_shPair (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω)
    (hs : ShScale P g μ₀ σ₀ eps) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    PairedHyp (shP P) (shPair P eps g ℓ) (shLawPM P hg.iid.measurable eps ℓ) eps (72 / 71)
      (shAT μ₀ σ₀) (shKd μ₀ σ₀ / eps ^ 2) := by
  have heps := hs.epsZero_le
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1
  obtain ⟨hX, hY, hm1, hm2⟩ := shPair_moments_of_layerOK hg.iid.measurable hL
  refine ⟨iidSeqE_shPair hg heps ℓ,
    ae_all_iff.mpr fun i => ae_pos_shPair_fst hg hpos heps ℓ i, rfl, hX.sub hY, ?_, ?_,
    ae_actLen_shPair_ne_top hg heps ℓ, fun R => measureReal_actLen_shPair_gt_le hg heps ℓ R⟩
  · rw [integral_sub (hX.integrable one_le_two) (hY.integrable one_le_two), hm1, hm2, sub_self]
  · rw [← shDist_sq]
    refine (shDist_sq_le_first_scale hg heps hs.scale hℓ).trans (le_of_eq ?_)
    rw [div_div_eq_mul_div]
    rfl


end

end PGM
