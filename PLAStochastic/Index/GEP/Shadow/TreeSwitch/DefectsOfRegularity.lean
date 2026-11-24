import PLAStochastic.Index.GEP.Shadow.TreeSwitch.MeanW2Defects
import PLAStochastic.Index.GEP.Shadow.TreeSwitch.DefectSum
import PLAStochastic.Index.GEP.Shadow.ErrorContraction

/-!
# WP3: `ShadowDefects` from the all-layer regularity of the shadow laws

Source: `research/2026-09-28-gep-closure/memory-route.md` §6–7, in the form of
`research/2026-09-29-lean-gep-shadow-defects/README.md` (line B).  The hypothesis `hReg` of
`shadowDefects_of_regLaw` is the conclusion of line A (`regLaw_shLawPM_all`): from some
threshold on, every shadow law `η_ℓ = shLawPM … ℓ`, `ℓ ≥ 1`, is in one regular class.

For every large `eps` and `ℓ ≥ 1`, the actual (active, passive) layer `shPair P eps g ℓ`
satisfies `TreeHyp` with the upper parameter `σ_ℓ = trSig d₀² c_Br eps ℓ`
(`treeHyp_layer`; `d_ℓ² ≤ d₀²/(eps²/c_Br)^ℓ` is `shDist_sq_le_geometric`).  The active stop
moments come from the actual layer bracket (`shPair_actStop`), the fourth moments of the two
stopped sums from the exponential moments of `η_{ℓ+1}` (`RegLaw.expMom`) and of `Φ_ε η_ℓ`
(`lawPhi_expMom`) (`shPair_U4`, `shPair_W4`).  Hence each `W₂` defect `shW` and each log-mean
defect is at most a constant and at most `A eps¹¹ σ_ℓ` (`layer_W2`, `layer_log`), and
`sum_Ico_le_of_eventually_geom` with `trSig_geom` bounds all finite sums uniformly in `eps`.

The witnesses are `η j = shLawPM P _ eps j` and `w j = shW P eps g j`.  The gap positivity
hypothesis of the frozen statement is not used here (it is consumed by line A).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

/-! ## Constants (independent of `eps` and of the layer) -/

/-- `d₀² = σ₀²/μ₀² + 1`. -/
def dfD0 (μ₀ σ₀ : ℝ) : ℝ := σ₀ ^ 2 / μ₀ ^ 2 + 1

/-- The layer bracket constant `c_Br`. -/
def dfCB (μ₀ σ₀ : ℝ) : ℝ := cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀)

/-- `E T_X² ≤ dfMX eps⁴`. -/
def dfMX (μ₀ σ₀ : ℝ) : ℝ := K2 / vIn μ₀ σ₀ ^ 2

/-- Fourth moment of a law with `E e^{θX/2} ≤ 2D/θ`. -/
def dfM4U (D θ : ℝ) : ℝ := (Nat.factorial 4 : ℝ) / (θ / 2) ^ 4 * (2 * D / θ)

/-- Fourth moment of a law with `E e^{θK X} ≤ CK`. -/
def dfM4W : ℝ := (Nat.factorial 4 : ℝ) / θK ^ 4 * CK

/-- The polynomial constant of the `W₂` defect. -/
def dfAW (μ₀ σ₀ D θ vlo : ℝ) : ℝ :=
  Real.sqrt (dfM4U D θ + dfM4W + 2 * treeK D vlo +
    (dfM4W + 1) / 2 * ((2 * (dfMX μ₀ σ₀ + trMY vlo) + treeK D vlo) / (2 * (1 / dfCB μ₀ σ₀))) ^ 2)

/-- The polynomial constant of the log-mean defect. -/
def dfAL (μ₀ σ₀ D vlo vhi : ℝ) : ℝ :=
  (2 * (dfMX μ₀ σ₀ + trMY vlo) + treeK D vlo) /
    (2 * min (1 / dfCB μ₀ σ₀) (1 / (128 * regB vhi)))

/-- The constant bound of the `W₂` defect. -/
def dfKW (D θ : ℝ) : ℝ := Real.sqrt (dfM4U D θ + dfM4W + 2)

/-- The constant bound of the log-mean defect. -/
def dfKL (μ₀ σ₀ vlo vhi : ℝ) : ℝ :=
  (dfCB μ₀ σ₀ + cPlus / regV vlo) / min (1 / dfCB μ₀ σ₀) (1 / (128 * regB vhi))

/-- `d₀^{2/48}`. -/
def dfS0 (μ₀ σ₀ : ℝ) : ℝ := dfD0 μ₀ σ₀ ^ (((48 : ℕ) : ℝ)⁻¹)

theorem dfCB_pos (μ₀ σ₀ : ℝ) : 0 < dfCB μ₀ σ₀ :=
  lt_of_lt_of_le (by have := bAbs_pos.trans_le (bAbs_le_bIn μ₀ σ₀); positivity) (le_max_left _ _)

theorem dfD0_pos (μ₀ σ₀ : ℝ) : 0 < dfD0 μ₀ σ₀ := by unfold dfD0; positivity

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}

/-! ## One layer -/

/-- The actual layer `ℓ ≥ 1` satisfies the tree-switch hypotheses with `σ_ℓ = trSig …`. -/
theorem treeHyp_layer (hg : GapLaw P g μ₀ σ₀ κ₀) {D θ vlo vhi eps : ℝ} (hθ : 0 < θ)
    (hvlo : 0 < vlo) (heIn : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (heR : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps) (hce : dfCB μ₀ σ₀ ≤ eps)
    (hsmall : 2 ^ 48 * (dfCB μ₀ σ₀ * dfD0 μ₀ σ₀) ≤ eps ^ 2) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hreg : RegLaw D θ vlo vhi (shLawPM P hg.iid.measurable eps ℓ)) :
    TreeHyp (shP P) (shPair P eps g ℓ) (shLawPM P hg.iid.measurable eps ℓ) D θ vlo vhi eps
      (trSig (dfD0 μ₀ σ₀) (dfCB μ₀ σ₀) eps ℓ) := by
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heIn
  have hepspos : 0 < eps := by linarith
  have hc := dfCB_pos μ₀ σ₀
  have hd := dfD0_pos μ₀ σ₀
  have hc1 : dfCB μ₀ σ₀ ≤ eps ^ 2 := hce.trans (by nlinarith)
  have hsm : dfD0 μ₀ σ₀ * (dfCB μ₀ σ₀ / eps ^ 2) ≤ (1 / 2) ^ 48 := by
    have h1 : dfD0 μ₀ σ₀ * (dfCB μ₀ σ₀ / eps ^ 2) = dfCB μ₀ σ₀ * dfD0 μ₀ σ₀ / eps ^ 2 := by ring
    rw [h1, div_le_iff₀ (by positivity)]
    have h2 : (1 / 2 : ℝ) ^ 48 * (2 ^ 48 * (dfCB μ₀ σ₀ * dfD0 μ₀ σ₀)) =
        dfCB μ₀ σ₀ * dfD0 μ₀ σ₀ := by
      rw [← mul_assoc, ← mul_pow]; norm_num
    have h3 := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ (1 / 2) ^ 48)
    linarith
  refine ⟨iidSeqE_shPair hg heIn ℓ, by rw [coe_shLawPM]; rfl, hreg, hθ, hvlo, heR,
    trSig_pos hd hc hepspos ℓ, trSig_le_half hd.le hc.le hepspos hc1 hsm hℓ,
    integrable_shPair_sub_sq hg heIn ℓ, ?_⟩
  have h1 := shDist_sq_le_geometric hg heIn ℓ
  rw [shDist_zero_sq hg, shDist_sq] at h1
  rw [trSig_pow hd.le hc.le]
  refine h1.trans (le_of_eq ?_)
  rw [dfD0, dfCB, div_pow, div_pow, div_div_eq_mul_div, mul_div_assoc]

/-- The active stop of layer `ℓ`: second moment and mean bracket. -/
theorem shPair_actStop (hg : GapLaw P g μ₀ σ₀ κ₀) {eps : ℝ}
    (heIn : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    Integrable (fun p => ((actLen eps (shPair P eps g ℓ) p).toNat : ℝ) ^ 2) (shP P) ∧
      ∫ p, ((actLen eps (shPair P eps g ℓ) p).toNat : ℝ) ^ 2 ∂(shP P) ≤
        dfMX μ₀ σ₀ * eps ^ 4 ∧
      1 / dfCB μ₀ σ₀ * eps ^ 2 ≤ actMean eps (shP P) (shPair P eps g ℓ) ∧
      actMean eps (shP P) (shPair P eps g ℓ) ≤ dfCB μ₀ σ₀ * eps ^ 2 := by
  obtain ⟨h1, h2⟩ := actLen_shPair_sq_le hg heIn ℓ
  have hb := segMean_bracket hg heIn ℓ
  rw [actMean_shPair_eq_segMean hg heIn ℓ]
  refine ⟨h1, h2.trans (le_of_eq ?_), ?_, hb.2⟩
  · unfold dfMX
    rw [div_pow]
    ring
  · refine le_trans (le_of_eq ?_) hb.1
    unfold dfCB
    ring

/-- Fourth moment of `U = A^X/C_X`, whose law is `η_{ℓ+1}`. -/
theorem shPair_U4 (hg : GapLaw P g μ₀ σ₀ κ₀) {D θ vlo vhi eps : ℝ} (hθ : 0 < θ) (hvlo : 0 < vlo)
    (heIn : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) {ℓ : ℕ}
    (hreg1 : RegLaw D θ vlo vhi (shLawPM P hg.iid.measurable eps (ℓ + 1))) :
    Integrable (fun p => (actSum eps (shPair P eps g ℓ) p /
        actMean eps (shP P) (shPair P eps g ℓ)) ^ 4) (shP P) ∧
      ∫ p, (actSum eps (shPair P eps g ℓ) p / actMean eps (shP P) (shPair P eps g ℓ)) ^ 4
        ∂(shP P) ≤ dfM4U D θ := by
  have hmV := measurable_shPair hg.iid.measurable P eps ℓ
  have hmap : (shP P).map (fun p => actSum eps (shPair P eps g ℓ) p /
      actMean eps (shP P) (shPair P eps g ℓ)) =
      ((shLawPM P hg.iid.measurable eps (ℓ + 1) : ProbabilityMeasure ℝ) : Measure ℝ) := by
    rw [coe_shLawPM]
    exact shLaw_active_sum hg heIn ℓ
  exact integral_pow_le_of_map ((measurable_actSum_tr hmV eps).div_const _) hmap
    (hreg1.expMom hθ) (half_pos hθ) (hreg1.momClass hθ hvlo).pos 4

/-- Fourth moment of `W = A^Y/C_Y`, whose law is `Φ_ε η_ℓ`. -/
theorem shPair_W4 (hg : GapLaw P g μ₀ σ₀ κ₀) {D θ vlo vhi eps e₂ : ℝ} (hθ : 0 < θ)
    (hvlo : 0 < vlo) (heIn : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (heR : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps) (he₂ : e₂ ≤ eps)
    (hphi : ∀ eps, e₂ ≤ eps → ∀ ρ : ProbabilityMeasure ℝ,
      MomClass (regB vhi) (regBeta D θ vlo) (regV vlo) ρ → ExpMom (θ / 2) (2 * D / θ) ρ →
        ExpMom θK CK (lawPhi eps ρ))
    {ℓ : ℕ} (hreg : RegLaw D θ vlo vhi (shLawPM P hg.iid.measurable eps ℓ)) :
    Integrable (fun p => (pasSum eps (shPair P eps g ℓ) p /
        pasMean eps (shP P) (shPair P eps g ℓ)) ^ 4) (shP P) ∧
      ∫ p, (pasSum eps (shPair P eps g ℓ) p / pasMean eps (shP P) (shPair P eps g ℓ)) ^ 4
        ∂(shP P) ≤ dfM4W := by
  have hmV := measurable_shPair hg.iid.measurable P eps ℓ
  have hM := hreg.momClass hθ hvlo
  have hphiM := lawPhi_momClass (bAbs_le_regB vhi) (βAbs_le_regBeta D θ vlo) (regV_pos hvlo)
    (regV_le_half vlo) heR hM
  exact integral_pow_le_of_map ((measurable_pasSum_tr hmV eps).div_const _)
    (shLaw_passive_sum hg heIn ℓ) (hphi eps he₂ _ hM (hreg.expMom hθ)) θK_pos hphiM.pos 4

/-- **The `W₂` defect of layer `ℓ ≥ 1`**: the coupling, the constant bound and the polynomial
bound. -/
theorem layer_W2 (hg : GapLaw P g μ₀ σ₀ κ₀) {D θ vlo vhi eps e₂ : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (heIn : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (heR : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps) (he₂ : e₂ ≤ eps)
    (hphi : ∀ eps, e₂ ≤ eps → ∀ ρ : ProbabilityMeasure ℝ,
      MomClass (regB vhi) (regBeta D θ vlo) (regV vlo) ρ → ExpMom (θ / 2) (2 * D / θ) ρ →
        ExpMom θK CK (lawPhi eps ρ))
    (hce : dfCB μ₀ σ₀ ≤ eps) (hsmall : 2 ^ 48 * (dfCB μ₀ σ₀ * dfD0 μ₀ σ₀) ≤ eps ^ 2)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hreg : RegLaw D θ vlo vhi (shLawPM P hg.iid.measurable eps ℓ))
    (hreg1 : RegLaw D θ vlo vhi (shLawPM P hg.iid.measurable eps (ℓ + 1))) :
    W2Le (shLawPM P hg.iid.measurable eps (ℓ + 1))
        (lawPhi eps (shLawPM P hg.iid.measurable eps ℓ)) (shW P eps g ℓ) ∧
      shW P eps g ℓ ≤ dfKW D θ ∧
      shW P eps g ℓ ≤
        dfAW μ₀ σ₀ D θ vlo * eps ^ 11 * trSig (dfD0 μ₀ σ₀) (dfCB μ₀ σ₀) eps ℓ := by
  have hmV := measurable_shPair hg.iid.measurable P eps ℓ
  obtain ⟨hU4i, hU4⟩ := shPair_U4 hg hθ hvlo heIn hreg1
  obtain ⟨hW4i, hW4⟩ := shPair_W4 hg hθ hvlo heIn heR he₂ hphi hreg
  obtain ⟨hI, hIle⟩ := integral_sub_sq_le_of_four ((measurable_actSum_tr hmV eps).div_const _)
    ((measurable_pasSum_tr hmV eps).div_const _) hU4i hW4i
  have hT := treeHyp_layer hg hθ hvlo heIn heR hce hsmall hℓ hreg
  obtain ⟨hX2i, hX2, hCX, -⟩ := shPair_actStop hg heIn ℓ
  have hM4U : 0 ≤ dfM4U D θ := by unfold dfM4U; positivity
  have hM4W : 0 ≤ dfM4W := by unfold dfM4W; have := θK_pos; have := CK_pos; positivity
  have hMX : 0 ≤ dfMX μ₀ σ₀ := by unfold dfMX; have := K2_pos; positivity
  have hcX : 0 < 1 / dfCB μ₀ σ₀ := by have := dfCB_pos μ₀ σ₀; positivity
  refine ⟨shW_coupling hg heIn ℓ hI, ?_, ?_⟩
  · unfold shW dfKW
    exact Real.sqrt_le_sqrt (hIle.trans (by linarith))
  · exact hT.sqrt_integral_sq_le_poly hcX hMX hM4U hM4W hX2i hX2 hCX hU4i hU4 hW4i hW4

/-- **The log-mean defect of layer `ℓ ≥ 1`**: the constant bound and the polynomial bound. -/
theorem layer_log (hg : GapLaw P g μ₀ σ₀ κ₀) {D θ vlo vhi eps : ℝ} (hθ : 0 < θ)
    (hvlo : 0 < vlo) (heIn : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (heR : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps) (hce : dfCB μ₀ σ₀ ≤ eps)
    (hsmall : 2 ^ 48 * (dfCB μ₀ σ₀ * dfD0 μ₀ σ₀) ≤ eps ^ 2) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hreg : RegLaw D θ vlo vhi (shLawPM P hg.iid.measurable eps ℓ)) :
    |Real.log (segMean P eps (epLayerSeq eps g ℓ)) -
        Real.log (lawC eps (shLawPM P hg.iid.measurable eps ℓ))| ≤ dfKL μ₀ σ₀ vlo vhi ∧
      |Real.log (segMean P eps (epLayerSeq eps g ℓ)) -
          Real.log (lawC eps (shLawPM P hg.iid.measurable eps ℓ))| ≤
        dfAL μ₀ σ₀ D vlo vhi * eps ^ 11 * trSig (dfD0 μ₀ σ₀) (dfCB μ₀ σ₀) eps ℓ := by
  rw [← actMean_shPair_eq_segMean hg heIn ℓ, ← pasMean_shPair_eq_lawC hg heIn ℓ]
  have hT := treeHyp_layer hg hθ hvlo heIn heR hce hsmall hℓ hreg
  obtain ⟨hX2i, hX2, hCX, hCXu⟩ := shPair_actStop hg heIn ℓ
  have hMX : 0 ≤ dfMX μ₀ σ₀ := by unfold dfMX; have := K2_pos; positivity
  have hcX : 0 < 1 / dfCB μ₀ σ₀ := by have := dfCB_pos μ₀ σ₀; positivity
  exact ⟨hT.abs_log_sub_le_const hcX hCX hCXu, hT.abs_log_sub_le_poly hcX hMX hX2i hX2 hCX⟩

/-! ## Summation -/

/-- A sequence of defects that vanishes at `0`, is bounded by `K₁` and by `A eps¹¹ σ_j` for
`j ≥ 1` has finite sums at most `576 K₁ + 2 A d₀^{2/48}`. -/
theorem sum_defects_le {a : ℕ → ℝ} {K₁ A eps : ℝ} (hA : 0 ≤ A) (heps : 1 ≤ eps)
    (hce : dfCB μ₀ σ₀ ≤ eps) (hsmall : 2 ^ 48 * (dfCB μ₀ σ₀ * dfD0 μ₀ σ₀) ≤ eps ^ 2)
    (ha0 : ∀ j, 0 ≤ a j) (hK : ∀ j, a j ≤ K₁)
    (hpoly : ∀ j, 1 ≤ j → a j ≤ A * eps ^ 11 * trSig (dfD0 μ₀ σ₀) (dfCB μ₀ σ₀) eps j)
    (L : ℕ) : ∑ j ∈ Ico 1 L, a j ≤ 576 * K₁ + 2 * (A * dfS0 μ₀ σ₀) := by
  have hc := dfCB_pos μ₀ σ₀
  have hd := dfD0_pos μ₀ σ₀
  have hepspos : 0 < eps := by linarith
  have hc48 : dfCB μ₀ σ₀ / eps ^ 2 ≤ (1 / 2) ^ 48 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (1 / 2 : ℝ) ^ 48 * (2 ^ 48 * (dfCB μ₀ σ₀ * dfD0 μ₀ σ₀)) =
        dfCB μ₀ σ₀ * dfD0 μ₀ σ₀ := by
      rw [← mul_assoc, ← mul_pow]; norm_num
    have h3 := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ (1 / 2) ^ 48)
    have h4 : dfCB μ₀ σ₀ ≤ dfCB μ₀ σ₀ * dfD0 μ₀ σ₀ := by
      have : 1 ≤ dfD0 μ₀ σ₀ := by
        unfold dfD0
        have := div_nonneg (sq_nonneg σ₀) (sq_nonneg μ₀)
        linarith
      nlinarith
    linarith
  have key := sum_Ico_le_of_eventually_geom (n₀ := 576) (C := A * dfS0 μ₀ σ₀) ha0 hK
    (mul_nonneg hA (Real.rpow_nonneg hd.le _)) (fun j hj => by
      have h1 := hpoly j (by omega)
      have h2 := trSig_geom hd.le hc.le heps hce hc48 hj
      calc a j ≤ A * (eps ^ 11 * trSig (dfD0 μ₀ σ₀) (dfCB μ₀ σ₀) eps j) := by
            rw [← mul_assoc]; exact h1
        _ ≤ A * (dfD0 μ₀ σ₀ ^ (((48 : ℕ) : ℝ)⁻¹) * (1 / 2) ^ (j - 576)) :=
            mul_le_mul_of_nonneg_left h2 hA
        _ = A * dfS0 μ₀ σ₀ * (1 / 2) ^ (j - 576) := by rw [dfS0]; ring) L
  simpa only [Nat.cast_ofNat] using key

/-! ## The assembly interface -/

/-- **`ShadowDefects` from the all-layer regularity of the shadow laws.**  The hypothesis
`hReg` is the conclusion of `regLaw_shLawPM_all` (line A); the gap positivity is not used
here. -/
theorem shadowDefects_of_regLaw (hg : GapLaw P g μ₀ σ₀ κ₀) (_hpos : ∀ᵐ ω ∂P, 0 < g 0 ω)
    (hReg : ∃ D θ vlo vhi e0 : ℝ, 0 < D ∧ 0 < θ ∧ 0 < vlo ∧ vlo ≤ vhi ∧
      ∀ eps, e0 ≤ eps → ∀ ℓ, 1 ≤ ℓ → RegLaw D θ vlo vhi (shLawPM P hg.iid.measurable eps ℓ)) :
    ShadowDefects P g := by
  obtain ⟨D, θ, vlo, vhi, eR, hD, hθ, hvlo, hvv, hR⟩ := hReg
  obtain ⟨e₂, hphi⟩ := lawPhi_expMom (b := regB vhi) (β := regBeta D θ vlo) (vmin := regV vlo)
    (θ₁ := θ / 2) (B₁ := 2 * D / θ) (regV_pos hvlo) (half_pos hθ) (by positivity)
  refine ⟨D, θ, vlo, vhi,
    max (576 * dfKW D θ + 2 * (dfAW μ₀ σ₀ D θ vlo * dfS0 μ₀ σ₀))
      (576 * dfKL μ₀ σ₀ vlo vhi + 2 * (dfAL μ₀ σ₀ D vlo vhi * dfS0 μ₀ σ₀)),
    max (max (max eR (epsZero (regB vhi) (regBeta D θ vlo)))
      (max e₂ (epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))))))
      (max (dfCB μ₀ σ₀) (Real.sqrt (2 ^ 48 * (dfCB μ₀ σ₀ * dfD0 μ₀ σ₀)))),
    hD, hθ, hvlo, hvv, fun eps heps => ?_⟩
  simp only [max_le_iff] at heps
  obtain ⟨⟨⟨heR', heR⟩, he₂, heIn⟩, hce, hsq⟩ := heps
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heIn
  have hsmall : 2 ^ 48 * (dfCB μ₀ σ₀ * dfD0 μ₀ σ₀) ≤ eps ^ 2 := by
    have h0 : 0 ≤ 2 ^ 48 * (dfCB μ₀ σ₀ * dfD0 μ₀ σ₀) := by
      have := dfCB_pos μ₀ σ₀; have := dfD0_pos μ₀ σ₀; positivity
    calc 2 ^ 48 * (dfCB μ₀ σ₀ * dfD0 μ₀ σ₀)
        = Real.sqrt (2 ^ 48 * (dfCB μ₀ σ₀ * dfD0 μ₀ σ₀)) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ eps ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
  have hRe := hR eps heR'
  refine ⟨fun j => shLawPM P hg.iid.measurable eps j, fun j => shW P eps g j,
    fun j hj => hRe j hj, fun j hj => ⟨Real.sqrt_nonneg _, (layer_W2 hg hD hθ hvlo heIn heR he₂
      hphi hce hsmall hj (hRe j hj) (hRe (j + 1) (by omega))).1⟩, fun L => ?_, fun L => ?_⟩
  · -- the `W₂` defects
    set a : ℕ → ℝ := fun j => if j = 0 then 0 else shW P eps g j with ha
    have hsum : ∑ j ∈ Ico 1 L, shW P eps g j = ∑ j ∈ Ico 1 L, a j :=
      sum_congr rfl fun j hj => by
        have : j ≠ 0 := by simp only [Finset.mem_Ico] at hj; omega
        rw [ha]
        dsimp only
        rw [if_neg this]
    have hKW0 : 0 ≤ dfKW D θ := Real.sqrt_nonneg _
    have key := sum_defects_le (a := a) (K₁ := dfKW D θ) (Real.sqrt_nonneg _) heps1 hce hsmall
      (fun j => by
        simp only [ha]
        split_ifs
        · exact le_rfl
        · exact Real.sqrt_nonneg _)
      (fun j => by
        simp only [ha]
        split_ifs with h0
        · exact hKW0
        · exact (layer_W2 hg hD hθ hvlo heIn heR he₂ hphi hce hsmall (by omega)
            (hRe j (by omega)) (hRe (j + 1) (by omega))).2.1)
      (fun j hj => by
        have h0 : j ≠ 0 := by omega
        rw [ha]
        dsimp only
        rw [if_neg h0]
        exact (layer_W2 hg hD hθ hvlo heIn heR he₂ hphi hce hsmall hj
          (hRe j hj) (hRe (j + 1) (by omega))).2.2) L
    rw [hsum]
    exact key.trans (le_max_left _ _)
  · -- the log-mean defects
    set a : ℕ → ℝ := fun j => if j = 0 then 0 else
      |Real.log (segMean P eps (epLayerSeq eps g j)) -
        Real.log (lawC eps (shLawPM P hg.iid.measurable eps j))| with ha
    have hsum : ∑ j ∈ Ico 1 L, |Real.log (segMean P eps (epLayerSeq eps g j)) -
        Real.log (lawC eps (shLawPM P hg.iid.measurable eps j))| = ∑ j ∈ Ico 1 L, a j :=
      sum_congr rfl fun j hj => by
        have : j ≠ 0 := by simp only [Finset.mem_Ico] at hj; omega
        rw [ha]
        dsimp only
        rw [if_neg this]
    have hKL0 : 0 ≤ dfKL μ₀ σ₀ vlo vhi := by
      have := (layer_log hg hθ hvlo heIn heR hce hsmall (le_refl 1) (hRe 1 le_rfl)).1
      exact (abs_nonneg _).trans this
    have hAL0 : 0 ≤ dfAL μ₀ σ₀ D vlo vhi := by
      unfold dfAL
      have := dfCB_pos μ₀ σ₀
      have := regB_pos vhi
      have := treeK_nonneg hD.le hvlo
      have := trMY_nonneg vlo
      have : 0 ≤ dfMX μ₀ σ₀ := by unfold dfMX; have := K2_pos; positivity
      have : 0 < min (1 / dfCB μ₀ σ₀) (1 / (128 * regB vhi)) := lt_min (by positivity)
        (by positivity)
      positivity
    have key := sum_defects_le (a := a) (K₁ := dfKL μ₀ σ₀ vlo vhi) hAL0 heps1 hce hsmall
      (fun j => by
        simp only [ha]
        split_ifs
        · exact le_rfl
        · exact abs_nonneg _)
      (fun j => by
        simp only [ha]
        split_ifs with h0
        · exact hKL0
        · exact (layer_log hg hθ hvlo heIn heR hce hsmall (by omega) (hRe j (by omega))).1)
      (fun j hj => by
        have h0 : j ≠ 0 := by omega
        rw [ha]
        dsimp only
        rw [if_neg h0]
        exact (layer_log hg hθ hvlo heIn heR hce hsmall hj (hRe j hj)).2) L
    rw [hsum]
    exact key.trans (le_max_right _ _)

end

end PGM
