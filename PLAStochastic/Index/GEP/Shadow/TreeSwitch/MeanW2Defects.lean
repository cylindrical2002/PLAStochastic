import PLAStochastic.Index.GEP.Shadow.TreeSwitch.Moments

/-!
# WP3 tree switch: the mean and `W₂` defects (tree-mean, tree-W2)

Source: `research/2026-09-28-gep-closure/memory-route.md` §6, (tree-mean) and (tree-W2), in
the polynomial form of `research/2026-09-29-lean-gep-shadow-defects/README.md` (line B).

`TreeHyp P V ν D θ vlo vhi eps σ` collects the hypotheses for one layer: iid pairs, a regular
passive law `ν`, `eps ≥ epsZero (regB vhi) (regBeta D θ vlo)`, `0 < σ ≤ 1/2` and
`E (X - Y)² ≤ σ⁴⁸`.  Then `P(B) ≤ treeK · eps¹¹ σ⁴` for `B = {T_X ≠ T_Y}` (`TreeHyp.prob_le`,
from `treeProb_le` with `τ = σ⁴`).  With `E T_X² ≤ MX eps⁴`:

* `TreeHyp.abs_actMean_sub_pasMean`: `|C_X - C_Y| ≤ Q eps² σ²/2`, `Q = 2 (MX + MY) + treeK eps¹¹`
  (`C_X - C_Y = ∫_B (T_X - T_Y)` and AM–GM with `s = σ²/eps²`);
* `TreeHyp.abs_log_sub_le`: `|log C_X - log C_Y| ≤ Q σ² / (2 cmin)`;
* `TreeHyp.integral_sq_le`: for `U = A^X/C_X`, `W = A^Y/C_Y` with fourth moments `M4U`, `M4W`,
  `E (U - W)² ≤ (M4U + M4W + 2 treeK eps¹¹ + (M4W + 1)/2 · (Q/(2 cX))²) σ²`, using `U = W C_Y/C_X`
  off `B` and AM–GM with `s = σ²` on `B`;
* the polynomial forms `TreeHyp.abs_log_sub_le_poly`, `TreeHyp.sqrt_integral_sq_le_poly`
  (`≤ A eps¹¹ σ` with `A` independent of `eps`) and the constant bounds
  `TreeHyp.abs_log_sub_le_const`, `integral_sub_sq_le_of_four`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {V : ℕ → Ω → ℝ × ℝ}

/-- The hypotheses of the tree switch for one layer. -/
structure TreeHyp (P : Measure Ω) (V : ℕ → Ω → ℝ × ℝ) (ν : ProbabilityMeasure ℝ)
    (D θ vlo vhi eps σ : ℝ) : Prop where
  iid : IIDSeqE P V
  law : P.map (fun ω => (V 0 ω).2) = (ν : Measure ℝ)
  reg : RegLaw D θ vlo vhi ν
  θ_pos : 0 < θ
  vlo_pos : 0 < vlo
  eps_ge : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps
  σ_pos : 0 < σ
  σ_le : σ ≤ 1 / 2
  dist_int : Integrable (fun ω => ((V 0 ω).1 - (V 0 ω).2) ^ 2) P
  dist_le : ∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P ≤ σ ^ 48

/-- The passive second-moment constant `K2 / regV(vlo)²`. -/
def trMY (vlo : ℝ) : ℝ := K2 / regV vlo ^ 2

theorem trMY_nonneg (vlo : ℝ) : 0 ≤ trMY vlo := by
  unfold trMY; have := K2_pos; positivity

theorem regB_pos (vhi : ℝ) : 0 < regB vhi := bAbs_pos.trans_le (bAbs_le_regB vhi)

omit [IsProbabilityMeasure P] in
theorem pasMean_eq_lawC_tr (hV : IIDSeqE P V) {ν : ProbabilityMeasure ℝ}
    (hν : P.map (fun ω => (V 0 ω).2) = (ν : Measure ℝ)) (eps : ℝ) :
    pasMean eps P V = lawC eps ν := by
  have hY := hV.iidSeq_pas
  have hmap := map_seq_eq_iidLaw hY ν hν.symm
  have hs := measurable_seq hY.measurable
  unfold pasMean lawC
  rw [← hmap, integral_map hs.aemeasurable (measurable_toNat_gapSegLen eps).aestronglyMeasurable]
  rfl

/-- Second moments from fourth moments on a probability space. -/
theorem sq_integral_le_of_four {F : Ω → ℝ} (hF : Measurable F)
    (hF4 : Integrable (fun ω => F ω ^ 4) P) :
    Integrable (fun ω => F ω ^ 2) P ∧ ∫ ω, F ω ^ 2 ∂P ≤ (∫ ω, F ω ^ 4 ∂P + 1) / 2 := by
  have hpt : ∀ ω, F ω ^ 2 ≤ (F ω ^ 4 + 1) / 2 := fun ω => by
    nlinarith [sq_nonneg (F ω ^ 2 - 1)]
  have hbd : Integrable (fun ω => (F ω ^ 4 + 1) / 2) P :=
    (hF4.add (integrable_const 1)).div_const 2
  have hi : Integrable (fun ω => F ω ^ 2) P :=
    hbd.mono' (hF.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt ω)
  refine ⟨hi, (integral_mono hi hbd hpt).trans (le_of_eq ?_)⟩
  rw [integral_div, integral_add hF4 (integrable_const 1)]
  simp

/-- The crude constant bound `E (U - W)² ≤ E U⁴ + E W⁴ + 2`. -/
theorem integral_sub_sq_le_of_four {U W : Ω → ℝ} (hU : Measurable U) (hW : Measurable W)
    (hU4 : Integrable (fun ω => U ω ^ 4) P) (hW4 : Integrable (fun ω => W ω ^ 4) P) :
    Integrable (fun ω => (U ω - W ω) ^ 2) P ∧
      ∫ ω, (U ω - W ω) ^ 2 ∂P ≤ ∫ ω, U ω ^ 4 ∂P + ∫ ω, W ω ^ 4 ∂P + 2 := by
  obtain ⟨hU2i, hU2⟩ := sq_integral_le_of_four hU hU4
  obtain ⟨hW2i, hW2⟩ := sq_integral_le_of_four hW hW4
  have hpt : ∀ ω, (U ω - W ω) ^ 2 ≤ 2 * U ω ^ 2 + 2 * W ω ^ 2 := fun ω => by
    nlinarith [sq_nonneg (U ω + W ω)]
  have hbd : Integrable (fun ω => 2 * U ω ^ 2 + 2 * W ω ^ 2) P :=
    (hU2i.const_mul 2).add (hW2i.const_mul 2)
  have hi : Integrable (fun ω => (U ω - W ω) ^ 2) P :=
    hbd.mono' ((hU.sub hW).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt ω)
  refine ⟨hi, (integral_mono hi hbd hpt).trans ?_⟩
  rw [integral_add (hU2i.const_mul 2) (hW2i.const_mul 2), integral_const_mul, integral_const_mul]
  linarith

namespace TreeHyp

variable {ν : ProbabilityMeasure ℝ} {D θ vlo vhi eps σ : ℝ}

omit [IsProbabilityMeasure P] in
theorem momClass (h : TreeHyp P V ν D θ vlo vhi eps σ) :
    MomClass (regB vhi) (regBeta D θ vlo) (regV vlo) ν :=
  h.reg.momClass h.θ_pos h.vlo_pos

omit [IsProbabilityMeasure P] in
theorem one_le_eps (h : TreeHyp P V ν D θ vlo vhi eps σ) : 1 ≤ eps :=
  (one_le_epsZero _ _).trans h.eps_ge

omit [IsProbabilityMeasure P] in
theorem σ_le_one (h : TreeHyp P V ν D θ vlo vhi eps σ) : σ ≤ 1 := by
  have := h.σ_le; linarith

/-- (tree-prob) with `τ = σ⁴`. -/
theorem prob_le (h : TreeHyp P V ν D θ vlo vhi eps σ) :
    P.real {ω | actLen eps V ω ≠ pasLen eps V ω} ≤ treeK D vlo * eps ^ 11 * σ ^ 4 :=
  treeProb_le h.iid h.law h.reg h.θ_pos h.vlo_pos h.eps_ge (pow_pos h.σ_pos 4)
    ((pow_le_pow_left₀ h.σ_pos.le h.σ_le 4).trans (by norm_num)) h.dist_int
    (by rw [← pow_mul]; exact h.dist_le)

omit [IsProbabilityMeasure P] in
/-- The passive mean is at least `eps²/(128 regB)`. -/
theorem pasMean_ge (h : TreeHyp P V ν D θ vlo vhi eps σ) :
    eps ^ 2 / (128 * regB vhi) ≤ pasMean eps P V := by
  rw [pasMean_eq_lawC_tr h.iid h.law]
  exact (momClass_oneLayer (regV_pos h.vlo_pos) h.eps_ge h.momClass).2.1

omit [IsProbabilityMeasure P] in
/-- The passive mean is at most `cPlus eps²/regV`. -/
theorem pasMean_le (h : TreeHyp P V ν D θ vlo vhi eps σ) :
    pasMean eps P V ≤ cPlus * eps ^ 2 / regV vlo := by
  rw [pasMean_eq_lawC_tr h.iid h.law]
  exact (momClass_oneLayer (regV_pos h.vlo_pos) h.eps_ge h.momClass).2.2

/-- **(tree-mean), difference form**: `|C_X - C_Y| ≤ Q eps² σ²/2`. -/
theorem abs_actMean_sub_pasMean (h : TreeHyp P V ν D θ vlo vhi eps σ) {MX : ℝ}
    (hX2i : Integrable (fun ω => ((actLen eps V ω).toNat : ℝ) ^ 2) P)
    (hX2 : ∫ ω, ((actLen eps V ω).toNat : ℝ) ^ 2 ∂P ≤ MX * eps ^ 4) :
    |actMean eps P V - pasMean eps P V| ≤
      (2 * (MX + trMY vlo) + treeK D vlo * eps ^ 11) * eps ^ 2 * σ ^ 2 / 2 := by
  have hm := h.iid.measurable
  have heps1 := h.one_le_eps
  have hepspos : 0 < eps := by linarith
  have hσ := h.σ_pos
  obtain ⟨hY2i, hY2⟩ := pasLen_sq_le h.iid h.law (regV_pos h.vlo_pos) h.eps_ge h.momClass
  have hY2' : ∫ ω, ((pasLen eps V ω).toNat : ℝ) ^ 2 ∂P ≤ trMY vlo * eps ^ 4 := by
    refine hY2.trans (le_of_eq ?_)
    unfold trMY
    have := regV_pos h.vlo_pos
    field_simp
  set TX : Ω → ℝ := fun ω => ((actLen eps V ω).toNat : ℝ) with hTX
  set TY : Ω → ℝ := fun ω => ((pasLen eps V ω).toNat : ℝ) with hTY
  have hTXm : Measurable TX :=
    (Measurable.of_discrete (f := fun n : ℕ∞ => (n.toNat : ℝ))).comp (measurable_actLen_tr hm eps)
  have hTYm : Measurable TY :=
    (Measurable.of_discrete (f := fun n : ℕ∞ => (n.toNat : ℝ))).comp (measurable_pasLen_tr hm eps)
  have hTXi : Integrable TX P := integrable_toNat_of_sq (measurable_actLen_tr hm eps) hX2i
  have hTYi : Integrable TY P := integrable_toNat_of_sq (measurable_pasLen_tr hm eps) hY2i
  set B := {ω | actLen eps V ω ≠ pasLen eps V ω} with hBdef
  have hB : MeasurableSet B := measurableSet_actLen_ne_pasLen hm eps
  have hind : (fun ω => TX ω - TY ω) = B.indicator (fun ω => TX ω - TY ω) := by
    funext ω
    by_cases hω : ω ∈ B
    · rw [indicator_of_mem hω]
    · rw [indicator_of_notMem hω]
      have heq : actLen eps V ω = pasLen eps V ω := not_not.mp hω
      simp only [hTX, hTY, heq, sub_self]
  have e1 : actMean eps P V - pasMean eps P V = ∫ ω in B, (TX ω - TY ω) ∂P := by
    rw [← integral_indicator hB, ← hind, integral_sub hTXi hTYi]
    rfl
  set s : ℝ := σ ^ 2 / eps ^ 2 with hs
  have hs0 : 0 < s := by positivity
  have hf2 : Integrable (fun ω => (TX ω + TY ω) ^ 2) P := by
    refine ((hX2i.const_mul 2).add (hY2i.const_mul 2)).mono'
      ((hTXm.add hTYm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (TX ω + TY ω) ^ 2 ≤ 2 * TX ω ^ 2 + 2 * TY ω ^ 2
    nlinarith [sq_nonneg (TX ω - TY ω)]
  obtain ⟨hfi', hamgm'⟩ := setIntegral_le_amgm (hTXm.add hTYm).aestronglyMeasurable hf2
    (fun ω => add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hB hs0
  have hfi : Integrable (fun ω => TX ω + TY ω) P := hfi'
  have hamgm : ∫ ω in B, (TX ω + TY ω) ∂P ≤
      (s * ∫ ω, (TX ω + TY ω) ^ 2 ∂P + P.real B / s) / 2 := hamgm'
  have hf2le : ∫ ω, (TX ω + TY ω) ^ 2 ∂P ≤ 2 * (MX + trMY vlo) * eps ^ 4 := by
    calc ∫ ω, (TX ω + TY ω) ^ 2 ∂P ≤ ∫ ω, (2 * TX ω ^ 2 + 2 * TY ω ^ 2) ∂P :=
          integral_mono hf2 ((hX2i.const_mul 2).add (hY2i.const_mul 2)) fun ω => by
            nlinarith [sq_nonneg (TX ω - TY ω)]
      _ = 2 * ∫ ω, TX ω ^ 2 ∂P + 2 * ∫ ω, TY ω ^ 2 ∂P := by
          rw [integral_add (hX2i.const_mul 2) (hY2i.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * (MX + trMY vlo) * eps ^ 4 := by
          have h1 : ∫ ω, TX ω ^ 2 ∂P ≤ MX * eps ^ 4 := hX2
          have h2 : ∫ ω, TY ω ^ 2 ∂P ≤ trMY vlo * eps ^ 4 := hY2'
          linarith
  have hPB := h.prob_le
  have habs : |∫ ω in B, (TX ω - TY ω) ∂P| ≤ ∫ ω in B, (TX ω + TY ω) ∂P := by
    refine abs_integral_le_integral_abs.trans (setIntegral_mono_on
      (hTXi.sub hTYi).abs.integrableOn hfi.integrableOn hB fun ω _ => ?_)
    have h0 : 0 ≤ TX ω := Nat.cast_nonneg _
    have h1 : 0 ≤ TY ω := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith
  rw [e1]
  refine habs.trans (hamgm.trans ?_)
  have t1 : s * ∫ ω, (TX ω + TY ω) ^ 2 ∂P ≤ s * (2 * (MX + trMY vlo) * eps ^ 4) :=
    mul_le_mul_of_nonneg_left hf2le hs0.le
  have t2 : P.real B / s ≤ treeK D vlo * eps ^ 11 * σ ^ 4 / s :=
    div_le_div_of_nonneg_right hPB hs0.le
  have e2 : s * (2 * (MX + trMY vlo) * eps ^ 4) = 2 * (MX + trMY vlo) * eps ^ 2 * σ ^ 2 := by
    rw [hs]; field_simp
  have e3 : treeK D vlo * eps ^ 11 * σ ^ 4 / s = treeK D vlo * eps ^ 11 * eps ^ 2 * σ ^ 2 := by
    rw [hs]; field_simp
  rw [e2] at t1
  rw [e3] at t2
  have e4 : (2 * (MX + trMY vlo) + treeK D vlo * eps ^ 11) * eps ^ 2 * σ ^ 2 / 2 =
      (2 * (MX + trMY vlo) * eps ^ 2 * σ ^ 2 + treeK D vlo * eps ^ 11 * eps ^ 2 * σ ^ 2) / 2 := by
    ring
  rw [e4]
  linarith

/-- **(tree-mean)**: `|log C_X - log C_Y| ≤ Q σ² / (2 cmin)`, `cmin = min cX (1/(128 regB))`. -/
theorem abs_log_sub_le (h : TreeHyp P V ν D θ vlo vhi eps σ) {MX cX : ℝ} (hcX : 0 < cX)
    (hX2i : Integrable (fun ω => ((actLen eps V ω).toNat : ℝ) ^ 2) P)
    (hX2 : ∫ ω, ((actLen eps V ω).toNat : ℝ) ^ 2 ∂P ≤ MX * eps ^ 4)
    (hCX : cX * eps ^ 2 ≤ actMean eps P V) :
    |Real.log (actMean eps P V) - Real.log (pasMean eps P V)| ≤
      (2 * (MX + trMY vlo) + treeK D vlo * eps ^ 11) * σ ^ 2 /
        (2 * min cX (1 / (128 * regB vhi))) := by
  have heps1 := h.one_le_eps
  have hepspos : 0 < eps := by linarith
  have hb := regB_pos vhi
  set cm := min cX (1 / (128 * regB vhi)) with hcm
  have hcm0 : 0 < cm := lt_min hcX (by positivity)
  have hm0 : 0 < cm * eps ^ 2 := by positivity
  have hmX : cm * eps ^ 2 ≤ actMean eps P V :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg eps)).trans hCX
  have hmY : cm * eps ^ 2 ≤ pasMean eps P V := by
    refine (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg eps)).trans ?_
    refine le_trans (le_of_eq ?_) h.pasMean_ge
    field_simp
  refine (abs_log_sub_log_le hm0 hmX hmY).trans ?_
  refine (div_le_div_of_nonneg_right (h.abs_actMean_sub_pasMean hX2i hX2) hm0.le).trans
    (le_of_eq ?_)
  field_simp

/-- **(tree-W2)**: the square coupling error of the two stopped passive sums. -/
theorem integral_sq_le (h : TreeHyp P V ν D θ vlo vhi eps σ) {MX cX M4U M4W : ℝ}
    (hcX : 0 < cX)
    (hX2i : Integrable (fun ω => ((actLen eps V ω).toNat : ℝ) ^ 2) P)
    (hX2 : ∫ ω, ((actLen eps V ω).toNat : ℝ) ^ 2 ∂P ≤ MX * eps ^ 4)
    (hCX : cX * eps ^ 2 ≤ actMean eps P V)
    (hU4i : Integrable (fun ω => (actSum eps V ω / actMean eps P V) ^ 4) P)
    (hU4 : ∫ ω, (actSum eps V ω / actMean eps P V) ^ 4 ∂P ≤ M4U)
    (hW4i : Integrable (fun ω => (pasSum eps V ω / pasMean eps P V) ^ 4) P)
    (hW4 : ∫ ω, (pasSum eps V ω / pasMean eps P V) ^ 4 ∂P ≤ M4W) :
    Integrable (fun ω => (actSum eps V ω / actMean eps P V -
        pasSum eps V ω / pasMean eps P V) ^ 2) P ∧
      ∫ ω, (actSum eps V ω / actMean eps P V - pasSum eps V ω / pasMean eps P V) ^ 2 ∂P ≤
        (M4U + M4W + 2 * (treeK D vlo * eps ^ 11) +
          (M4W + 1) / 2 * ((2 * (MX + trMY vlo) + treeK D vlo * eps ^ 11) / (2 * cX)) ^ 2) *
          σ ^ 2 := by
  have hm := h.iid.measurable
  have heps1 := h.one_le_eps
  have hepspos : 0 < eps := by linarith
  have hσ := h.σ_pos
  have hσ1 := h.σ_le_one
  set CX := actMean eps P V with hCXdef
  set CY := pasMean eps P V with hCYdef
  have hCX0 : 0 < CX := lt_of_lt_of_le (by positivity) hCX
  have hCY0 : 0 < CY := lt_of_lt_of_le (by have := regB_pos vhi; positivity) h.pasMean_ge
  set U : Ω → ℝ := fun ω => actSum eps V ω / CX with hU
  set W : Ω → ℝ := fun ω => pasSum eps V ω / CY with hW
  have hUm : Measurable U := (measurable_actSum_tr hm eps).div_const _
  have hWm : Measurable W := (measurable_pasSum_tr hm eps).div_const _
  obtain ⟨hU2i, -⟩ := sq_integral_le_of_four hUm hU4i
  obtain ⟨hW2i, hW2⟩ := sq_integral_le_of_four hWm hW4i
  have hDi : Integrable (fun ω => (U ω - W ω) ^ 2) P := (integral_sub_sq_le_of_four hUm hWm hU4i hW4i).1
  refine ⟨hDi, ?_⟩
  set B := {ω | actLen eps V ω ≠ pasLen eps V ω} with hBdef
  have hB : MeasurableSet B := measurableSet_actLen_ne_pasLen hm eps
  set r : ℝ := CY / CX - 1 with hr
  -- off `B` the two sums agree
  have hoff : ∀ ω, ω ∉ B → U ω - W ω = r * W ω := by
    intro ω hω
    have heq : actLen eps V ω = pasLen eps V ω := not_not.mp hω
    have hS : actSum eps V ω = pasSum eps V ω := by
      simp only [actSum, pasSum, heq]
    simp only [hU, hW, hr, hS]
    field_simp
  have hpt : ∀ ω, (U ω - W ω) ^ 2 ≤
      B.indicator (fun ω => 2 * U ω ^ 2 + 2 * W ω ^ 2) ω + r ^ 2 * W ω ^ 2 := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [indicator_of_mem hω]
      nlinarith [sq_nonneg (U ω + W ω), sq_nonneg (r * W ω)]
    · rw [indicator_of_notMem hω, hoff ω hω]
      nlinarith
  have hIi : Integrable (fun ω => 2 * U ω ^ 2 + 2 * W ω ^ 2) P :=
    (hU2i.const_mul 2).add (hW2i.const_mul 2)
  have hint1 : ∫ ω, (U ω - W ω) ^ 2 ∂P ≤
      2 * ∫ ω in B, U ω ^ 2 ∂P + 2 * ∫ ω in B, W ω ^ 2 ∂P + r ^ 2 * ∫ ω, W ω ^ 2 ∂P := by
    calc ∫ ω, (U ω - W ω) ^ 2 ∂P
        ≤ ∫ ω, (B.indicator (fun ω => 2 * U ω ^ 2 + 2 * W ω ^ 2) ω + r ^ 2 * W ω ^ 2) ∂P :=
          integral_mono hDi ((hIi.indicator hB).add (hW2i.const_mul _)) hpt
      _ = ∫ ω in B, (2 * U ω ^ 2 + 2 * W ω ^ 2) ∂P + r ^ 2 * ∫ ω, W ω ^ 2 ∂P := by
          rw [integral_add (hIi.indicator hB) (hW2i.const_mul _), integral_indicator hB,
            integral_const_mul]
      _ = 2 * ∫ ω in B, U ω ^ 2 ∂P + 2 * ∫ ω in B, W ω ^ 2 ∂P + r ^ 2 * ∫ ω, W ω ^ 2 ∂P := by
          rw [integral_add (hU2i.const_mul 2).integrableOn (hW2i.const_mul 2).integrableOn,
            integral_const_mul, integral_const_mul]
  -- AM–GM on `B` with `s = σ²`
  have hPB := h.prob_le
  have hamgm : ∀ {F : Ω → ℝ}, Measurable F → Integrable (fun ω => F ω ^ 4) P →
      2 * ∫ ω in B, F ω ^ 2 ∂P ≤ (∫ ω, F ω ^ 4 ∂P + treeK D vlo * eps ^ 11) * σ ^ 2 := by
    intro F hF hF4
    have hF4' : Integrable (fun ω => (F ω ^ 2) ^ 2) P :=
      hF4.congr (Filter.Eventually.of_forall fun ω => by ring)
    obtain ⟨-, hle'⟩ := setIntegral_le_amgm (hF.pow_const 2).aestronglyMeasurable hF4'
      (fun ω => sq_nonneg (F ω)) hB (pow_pos hσ 2)
    have hle : ∫ ω in B, F ω ^ 2 ∂P ≤
        (σ ^ 2 * ∫ ω, (F ω ^ 2) ^ 2 ∂P + P.real B / σ ^ 2) / 2 := hle'
    have e1 : ∫ ω, (F ω ^ 2) ^ 2 ∂P = ∫ ω, F ω ^ 4 ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [e1] at hle
    have t2 : P.real B / σ ^ 2 ≤ treeK D vlo * eps ^ 11 * σ ^ 4 / σ ^ 2 :=
      div_le_div_of_nonneg_right hPB (by positivity)
    have e2 : treeK D vlo * eps ^ 11 * σ ^ 4 / σ ^ 2 = treeK D vlo * eps ^ 11 * σ ^ 2 := by
      field_simp
    rw [e2] at t2
    have e3 : (∫ ω, F ω ^ 4 ∂P + treeK D vlo * eps ^ 11) * σ ^ 2 =
        σ ^ 2 * ∫ ω, F ω ^ 4 ∂P + treeK D vlo * eps ^ 11 * σ ^ 2 := by ring
    rw [e3]
    linarith
  have hBU := hamgm hUm hU4i
  have hBW := hamgm hWm hW4i
  -- the normalisation defect
  have hmean := h.abs_actMean_sub_pasMean hX2i hX2
  set Q : ℝ := 2 * (MX + trMY vlo) + treeK D vlo * eps ^ 11 with hQ
  have hQnn : 0 ≤ Q := by
    by_contra hneg
    push Not at hneg
    have h1 : 0 < eps ^ 2 * σ ^ 2 := by positivity
    have h2 : Q * eps ^ 2 * σ ^ 2 / 2 < 0 := by nlinarith
    linarith [abs_nonneg (actMean eps P V - pasMean eps P V)]
  have hr2 : r ^ 2 ≤ (Q / (2 * cX)) ^ 2 * σ ^ 2 := by
    have hr' : |r| ≤ Q / (2 * cX) * σ ^ 2 := by
      have e1 : r = (CY - CX) / CX := by rw [hr]; field_simp
      rw [e1, abs_div, abs_of_pos hCX0, abs_sub_comm, div_le_iff₀ hCX0]
      refine hmean.trans ?_
      have hQ0 : 0 ≤ Q / (2 * cX) * σ ^ 2 := by positivity
      have h3 := mul_le_mul_of_nonneg_left hCX hQ0
      refine le_trans (le_of_eq ?_) h3
      field_simp
    have hσ4 : σ ^ 4 ≤ σ ^ 2 := pow_le_pow_of_le_one hσ.le hσ1 (by norm_num)
    calc r ^ 2 = |r| ^ 2 := (sq_abs r).symm
      _ ≤ (Q / (2 * cX) * σ ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg r) hr' 2
      _ = (Q / (2 * cX)) ^ 2 * σ ^ 4 := by ring
      _ ≤ (Q / (2 * cX)) ^ 2 * σ ^ 2 := by gcongr
  have hW2' : ∫ ω, W ω ^ 2 ∂P ≤ (M4W + 1) / 2 := by
    have : ∫ ω, W ω ^ 4 ∂P ≤ M4W := hW4
    linarith
  have hW20 : 0 ≤ ∫ ω, W ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hlast : r ^ 2 * ∫ ω, W ω ^ 2 ∂P ≤ (M4W + 1) / 2 * (Q / (2 * cX)) ^ 2 * σ ^ 2 := by
    calc r ^ 2 * ∫ ω, W ω ^ 2 ∂P ≤ (Q / (2 * cX)) ^ 2 * σ ^ 2 * ((M4W + 1) / 2) :=
          mul_le_mul hr2 hW2' hW20 (by positivity)
      _ = (M4W + 1) / 2 * (Q / (2 * cX)) ^ 2 * σ ^ 2 := by ring
  have hU4' : ∫ ω, U ω ^ 4 ∂P ≤ M4U := hU4
  have hσ2 : 0 ≤ σ ^ 2 := by positivity
  have t1 : (∫ ω, U ω ^ 4 ∂P + treeK D vlo * eps ^ 11) * σ ^ 2 ≤
      (M4U + treeK D vlo * eps ^ 11) * σ ^ 2 := by gcongr
  have t2 : (∫ ω, W ω ^ 4 ∂P + treeK D vlo * eps ^ 11) * σ ^ 2 ≤
      (M4W + treeK D vlo * eps ^ 11) * σ ^ 2 := by gcongr
  have e5 : (M4U + M4W + 2 * (treeK D vlo * eps ^ 11) + (M4W + 1) / 2 * (Q / (2 * cX)) ^ 2) *
      σ ^ 2 = (M4U + treeK D vlo * eps ^ 11) * σ ^ 2 + (M4W + treeK D vlo * eps ^ 11) * σ ^ 2 +
        (M4W + 1) / 2 * (Q / (2 * cX)) ^ 2 * σ ^ 2 := by ring
  rw [e5]
  linarith

/-- (tree-mean) in the form `≤ A eps¹¹ σ`. -/
theorem abs_log_sub_le_poly (h : TreeHyp P V ν D θ vlo vhi eps σ) {MX cX : ℝ} (hcX : 0 < cX)
    (hMX : 0 ≤ MX)
    (hX2i : Integrable (fun ω => ((actLen eps V ω).toNat : ℝ) ^ 2) P)
    (hX2 : ∫ ω, ((actLen eps V ω).toNat : ℝ) ^ 2 ∂P ≤ MX * eps ^ 4)
    (hCX : cX * eps ^ 2 ≤ actMean eps P V) :
    |Real.log (actMean eps P V) - Real.log (pasMean eps P V)| ≤
      (2 * (MX + trMY vlo) + treeK D vlo) / (2 * min cX (1 / (128 * regB vhi))) *
        eps ^ 11 * σ := by
  refine (h.abs_log_sub_le hcX hX2i hX2 hCX).trans ?_
  have heps1 := h.one_le_eps
  have hσ := h.σ_pos
  have hσ1 := h.σ_le_one
  have hcm0 : 0 < min cX (1 / (128 * regB vhi)) :=
    lt_min hcX (by have := regB_pos vhi; positivity)
  have hK := treeK_nonneg h.reg.D_nonneg h.vlo_pos
  have hMY := trMY_nonneg vlo
  have h11 : 1 ≤ eps ^ 11 := one_le_pow₀ heps1
  have hQ : 2 * (MX + trMY vlo) + treeK D vlo * eps ^ 11 ≤
      (2 * (MX + trMY vlo) + treeK D vlo) * eps ^ 11 := by nlinarith
  have hσ2 : σ ^ 2 ≤ σ := by nlinarith
  have hQ0 : 0 ≤ (2 * (MX + trMY vlo) + treeK D vlo) * eps ^ 11 := by positivity
  calc (2 * (MX + trMY vlo) + treeK D vlo * eps ^ 11) * σ ^ 2 /
        (2 * min cX (1 / (128 * regB vhi)))
      ≤ (2 * (MX + trMY vlo) + treeK D vlo) * eps ^ 11 * σ /
          (2 * min cX (1 / (128 * regB vhi))) :=
        div_le_div_of_nonneg_right (mul_le_mul hQ hσ2 (by positivity) hQ0) (by positivity)
    _ = (2 * (MX + trMY vlo) + treeK D vlo) / (2 * min cX (1 / (128 * regB vhi))) *
          eps ^ 11 * σ := by ring

/-- (tree-W2) in the form `≤ A eps¹¹ σ`. -/
theorem sqrt_integral_sq_le_poly (h : TreeHyp P V ν D θ vlo vhi eps σ) {MX cX M4U M4W : ℝ}
    (hcX : 0 < cX) (hMX : 0 ≤ MX) (hM4U : 0 ≤ M4U) (hM4W : 0 ≤ M4W)
    (hX2i : Integrable (fun ω => ((actLen eps V ω).toNat : ℝ) ^ 2) P)
    (hX2 : ∫ ω, ((actLen eps V ω).toNat : ℝ) ^ 2 ∂P ≤ MX * eps ^ 4)
    (hCX : cX * eps ^ 2 ≤ actMean eps P V)
    (hU4i : Integrable (fun ω => (actSum eps V ω / actMean eps P V) ^ 4) P)
    (hU4 : ∫ ω, (actSum eps V ω / actMean eps P V) ^ 4 ∂P ≤ M4U)
    (hW4i : Integrable (fun ω => (pasSum eps V ω / pasMean eps P V) ^ 4) P)
    (hW4 : ∫ ω, (pasSum eps V ω / pasMean eps P V) ^ 4 ∂P ≤ M4W) :
    Real.sqrt (∫ ω, (actSum eps V ω / actMean eps P V -
        pasSum eps V ω / pasMean eps P V) ^ 2 ∂P) ≤
      Real.sqrt (M4U + M4W + 2 * treeK D vlo +
        (M4W + 1) / 2 * ((2 * (MX + trMY vlo) + treeK D vlo) / (2 * cX)) ^ 2) *
        eps ^ 11 * σ := by
  obtain ⟨-, hle⟩ := h.integral_sq_le hcX hX2i hX2 hCX hU4i hU4 hW4i hW4
  have heps1 := h.one_le_eps
  have hσ := h.σ_pos
  have hK := treeK_nonneg h.reg.D_nonneg h.vlo_pos
  have hMY := trMY_nonneg vlo
  have h11 : 1 ≤ eps ^ 11 := one_le_pow₀ heps1
  have h22 : 1 ≤ eps ^ 22 := one_le_pow₀ heps1
  have e22 : eps ^ 22 = (eps ^ 11) ^ 2 := by ring
  set Q := 2 * (MX + trMY vlo) + treeK D vlo * eps ^ 11 with hQdef
  set Q' := 2 * (MX + trMY vlo) + treeK D vlo with hQ'def
  set Khat := M4U + M4W + 2 * treeK D vlo + (M4W + 1) / 2 * (Q' / (2 * cX)) ^ 2 with hKhat
  have hQ0 : 0 ≤ Q := by positivity
  have hQ : Q ≤ Q' * eps ^ 11 := by rw [hQdef, hQ'def]; nlinarith
  have hQq : (Q / (2 * cX)) ^ 2 ≤ (Q' / (2 * cX)) ^ 2 * eps ^ 22 := by
    rw [e22, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hQ (by positivity)
  have hKW : M4U + M4W + 2 * (treeK D vlo * eps ^ 11) + (M4W + 1) / 2 * (Q / (2 * cX)) ^ 2 ≤
      Khat * eps ^ 22 := by
    have t1 : M4U ≤ M4U * eps ^ 22 := le_mul_of_one_le_right hM4U h22
    have t2 : M4W ≤ M4W * eps ^ 22 := le_mul_of_one_le_right hM4W h22
    have t3 : treeK D vlo * eps ^ 11 ≤ treeK D vlo * eps ^ 22 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ heps1 (by norm_num)) hK
    have t4 : (M4W + 1) / 2 * (Q / (2 * cX)) ^ 2 ≤
        (M4W + 1) / 2 * ((Q' / (2 * cX)) ^ 2 * eps ^ 22) :=
      mul_le_mul_of_nonneg_left hQq (by positivity)
    have e1 : Khat * eps ^ 22 = M4U * eps ^ 22 + M4W * eps ^ 22 + 2 * (treeK D vlo * eps ^ 22) +
        (M4W + 1) / 2 * ((Q' / (2 * cX)) ^ 2 * eps ^ 22) := by rw [hKhat]; ring
    rw [e1]
    linarith
  have hKhat0 : 0 ≤ Khat := by positivity
  have hfin : ∫ ω, (actSum eps V ω / actMean eps P V -
      pasSum eps V ω / pasMean eps P V) ^ 2 ∂P ≤ (Real.sqrt Khat * eps ^ 11 * σ) ^ 2 := by
    refine hle.trans ?_
    have e2 : (Real.sqrt Khat * eps ^ 11 * σ) ^ 2 = Khat * eps ^ 22 * σ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hKhat0, e22]
    rw [e2]
    exact mul_le_mul_of_nonneg_right hKW (by positivity)
  calc Real.sqrt _ ≤ Real.sqrt ((Real.sqrt Khat * eps ^ 11 * σ) ^ 2) := Real.sqrt_le_sqrt hfin
    _ = Real.sqrt Khat * eps ^ 11 * σ := Real.sqrt_sq (by positivity)

omit [IsProbabilityMeasure P] in
/-- The constant bound for the log defect. -/
theorem abs_log_sub_le_const (h : TreeHyp P V ν D θ vlo vhi eps σ) {cX cXp : ℝ} (hcX : 0 < cX)
    (hCX : cX * eps ^ 2 ≤ actMean eps P V) (hCXu : actMean eps P V ≤ cXp * eps ^ 2) :
    |Real.log (actMean eps P V) - Real.log (pasMean eps P V)| ≤
      (cXp + cPlus / regV vlo) / min cX (1 / (128 * regB vhi)) := by
  have heps1 := h.one_le_eps
  have hepspos : 0 < eps := by linarith
  have hb := regB_pos vhi
  have hv := regV_pos h.vlo_pos
  set cm := min cX (1 / (128 * regB vhi)) with hcm
  have hcm0 : 0 < cm := lt_min hcX (by positivity)
  have hm0 : 0 < cm * eps ^ 2 := by positivity
  have hmX : cm * eps ^ 2 ≤ actMean eps P V :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg eps)).trans hCX
  have hmY : cm * eps ^ 2 ≤ pasMean eps P V := by
    refine (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg eps)).trans ?_
    refine le_trans (le_of_eq ?_) h.pasMean_ge
    field_simp
  have hY := h.pasMean_le
  refine (abs_log_sub_log_le hm0 hmX hmY).trans ?_
  have hsum : |actMean eps P V - pasMean eps P V| ≤ (cXp + cPlus / regV vlo) * eps ^ 2 := by
    have e1 : (cXp + cPlus / regV vlo) * eps ^ 2 = cXp * eps ^ 2 + cPlus * eps ^ 2 / regV vlo := by
      ring
    rw [e1, abs_le]
    constructor <;> linarith
  calc |actMean eps P V - pasMean eps P V| / (cm * eps ^ 2)
      ≤ (cXp + cPlus / regV vlo) * eps ^ 2 / (cm * eps ^ 2) :=
        div_le_div_of_nonneg_right hsum hm0.le
    _ = (cXp + cPlus / regV vlo) / cm := by field_simp

end TreeHyp

end

end PGM
