import PLAStochastic.Index.GEP.OrbitClosure.Defs
import PLAStochastic.Index.GEP.LayerLaw.ActualLayers
import PLAStochastic.Index.Endpoint.HyperSegmentMoments
import PLAStochastic.Index.LocalCount.MaximalBernstein

/-!
# WP2: moments along the orbit (law-level one-step lemmas)

All statements are about one application of `lawPhi eps` to a law `ρ` of the moment class,
on the canonical space `iidLaw ρ` with the input pairs `inputPairs gapCoord`
(`LayerOK` with counts `≡ 1`, so `lmean = 1`, `segMean = lawC`, `lawC_eq_segMean`).
No Brownian input: the brackets come from `oneLayer_bracket` and `layerOK_step`.

* `momClass_oneLayer`: `T < ∞` a.s. and `eps²/(128 b) ≤ C_ε(ρ) ≤ cPlus eps²/vmin`
  (`oneLayer_bracket` with `G = eps²/lawVar ρ`, via `largeConditions`).
* `lawPhi_momClass`: the class `MomClass b β vmin` is invariant under `lawPhi eps` for
  `eps ≥ epsZero b β` (`layerOK_step` on the canonical input layer; `lawVar (lawPhi ρ) =
  lvar/lmean²` of the next layer; positivity from `T ≥ 1`).  Replaces TeX `prop:layer`.
* `gapSegLen_tail`: `P(T > m) ≤ (72/71) exp(-tailRate · vmin · m / eps²)`, from
  `layerSegLen_tail_of_large` (`P(T > jL) ≤ (71/72)^j`, `L ≤ 5185 G`).
* `iid_maximal_bernstein`, `iid_endpoint_bernstein`: the maximal Bernstein inequality
  `P(max_{j ≤ s} |S_j - j| > x) ≤ 2 exp(-c min(x²/s, x))`, `c = bernsteinRate θ₁ B₁`, for iid
  mean-one positive gaps with `E e^{θ₁ X} ≤ B₁` (`lem:maxineq` of
  `research/2026-09-25-ep-rate/tex/main.tex` L255–268, in the form of
  `maximal_bernstein` of `PLAStochastic/Index/LocalCount/MaximalBernstein.lean`, with `lcbb_centred_moments`
  replaced by `E e^{η|X-1|} ≤ e^η E e^{ηX}`; the proof reuses `lcbb_one_sided`).
* `lawPhi_expMom`: `E e^{θ₁ X} ≤ B₁` gives `E_{lawPhi ρ} e^{θK X} ≤ CK` for large `eps`
  (`lem:expmom` of `research/2026-09-26-pla-local/tex/main.tex` L372–413, formalised as the
  gap version of `hyperexp_step` in `PLAStochastic/Index/Endpoint/HyperSegmentMoments.lean`: cumulant bound for general
  `(θ₁, B₁)` in place of `integral_exp_mul_le`, `lintegral_exp_stopped_le_one` with
  `f p = θ p.1`, `lintegral_exp_toNat_le_145`, the AM–GM step, rescaling by `C ≥ G/128`).
  The output constants `θK, CK` are absolute, so the orbit induction closes.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- The exponential rate of the stopping tail, `log(72/71)/5185`. -/
def tailRate : ℝ := Real.log (72 / 71) / 5185

theorem tailRate_pos : 0 < tailRate := by
  unfold tailRate
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- The one-layer facts on the canonical space of a law of the moment class, with
`G = eps² / Var`. -/
theorem momClass_setup {b β vmin eps : ℝ} (hvmin0 : 0 < vmin) (heps : epsZero b β ≤ eps)
    {ρ : ProbabilityMeasure ℝ} (hρ : MomClass b β vmin ρ) :
    0 < b ∧ 1 ≤ eps ∧ eps ^ 2 / b ≤ eps ^ 2 / lawVar ρ ∧ eps ^ 2 / lawVar ρ ≤ eps ^ 2 / vmin ∧
      (∀ᵐ g ∂(iidLaw ρ), gapSegLen eps g ≠ ⊤) ∧
      Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ρ) ∧
      eps ^ 2 / lawVar ρ / 128 ≤ lawC eps ρ ∧ lawC eps ρ ≤ cPlus * (eps ^ 2 / lawVar ρ) ∧
      ∃ L : ℕ, 1 ≤ L ∧ (L : ℝ) ≤ 5185 * (eps ^ 2 / lawVar ρ) ∧
        ∀ j : ℕ, (iidLaw ρ).real {g | ((j * L : ℕ) : ℕ∞) < gapSegLen eps g} ≤
          (71 / 72 : ℝ) ^ j := by
  have hv0 : 0 < lawVar ρ := hvmin0.trans_le hρ.var_ge
  have hb0 : 0 < b := hv0.trans_le hρ.var_le
  set σ := Real.sqrt (lawVar ρ) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hv0
  have hσ2 : σ ^ 2 = lawVar ρ := Real.sq_sqrt hv0.le
  set κ := ∫ x, |x - 1| ^ 3 ∂(ρ : Measure ℝ) with hκdef
  have hX : GapLaw (iidLaw ρ) gapCoord 1 σ κ :=
    gapLaw_iidLaw hρ.memLp3 hρ.mean one_pos hσ2.symm hσ le_rfl
  have hκ : 0 ≤ κ := integral_nonneg fun _ => by positivity
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero b β) heps
  have hepspos : 0 < eps := by linarith
  obtain ⟨c1, c2, c3, c4, -, -, -⟩ := largeConditions one_pos hσ hκ
    (by rw [hσ2, one_pow, mul_one]; exact hρ.var_le) hρ.third_le heps
  set G := eps ^ 2 / lawVar ρ with hG
  have hGdef : G = 1 ^ 2 * eps ^ 2 / σ ^ 2 := by rw [hσ2, one_pow, one_mul]
  rw [← hGdef] at c1 c2
  obtain ⟨-, hfin, hT1, -, -, hCm, hCp, -, -, -, -⟩ :=
    oneLayer_bracket hX hepspos hGdef c1 c2 c3 c4
  obtain ⟨L, hL1, hLG, htail⟩ := layerSegLen_tail_of_large hX hepspos hGdef c1 c2 c3 c4
  refine ⟨hb0, heps1, ?_, ?_, hfin.mono fun g h => h.ne, hT1, ?_, hCp, L, hL1, hLG, htail⟩
  · exact div_le_div_of_nonneg_left (sq_nonneg eps) hv0 hρ.var_le
  · exact div_le_div_of_nonneg_left (sq_nonneg eps) hvmin0 hρ.var_ge
  · have : cMinus * G = G / 128 := by unfold cMinus; ring
    rw [← this]
    exact hCm

/-- Under a law with `ρ(-∞, 0] = 0`, the canonical gaps are almost surely all positive. -/
theorem ae_pos_iidLaw {ρ : ProbabilityMeasure ℝ} (hpos : (ρ : Measure ℝ) (Iic 0) = 0) :
    ∀ᵐ g ∂(iidLaw ρ), ∀ i, 0 < g i :=
  ae_all_iff.2 fun i => by
    have h := (measurePreserving_eval_infinitePi (fun _ : ℕ => (ρ : Measure ℝ))
      i).measure_preimage (s := Iic 0) measurableSet_Iic.nullMeasurableSet
    rw [hpos] at h
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with g hg
    simpa using hg

/-- **One layer on the moment class**: the first segment is almost surely finite, and
`eps²/(128 b) ≤ C_ε(ρ) ≤ cPlus eps²/vmin`. -/
theorem momClass_oneLayer {b β vmin eps : ℝ} (hvmin0 : 0 < vmin) (heps : epsZero b β ≤ eps)
    {ρ : ProbabilityMeasure ℝ} (hρ : MomClass b β vmin ρ) :
    (∀ᵐ g ∂(iidLaw ρ), gapSegLen eps g ≠ ⊤) ∧
      eps ^ 2 / (128 * b) ≤ lawC eps ρ ∧ lawC eps ρ ≤ cPlus * eps ^ 2 / vmin := by
  obtain ⟨-, -, hGb, hGv, hfin, -, hCm, hCp, -⟩ := momClass_setup hvmin0 heps hρ
  refine ⟨hfin, ?_, ?_⟩
  · calc eps ^ 2 / (128 * b) = eps ^ 2 / b / 128 := by ring
      _ ≤ eps ^ 2 / lawVar ρ / 128 := by gcongr
      _ ≤ lawC eps ρ := hCm
  · calc lawC eps ρ ≤ cPlus * (eps ^ 2 / lawVar ρ) := hCp
      _ ≤ cPlus * (eps ^ 2 / vmin) := by gcongr; exact cPlus_pos.le
      _ = cPlus * eps ^ 2 / vmin := by ring

/-- **Invariance of the moment class** under the layer map (replaces TeX `prop:layer`). -/
theorem lawPhi_momClass {b β vmin eps : ℝ} (hb : bAbs ≤ b) (hβ : βAbs ≤ β)
    (hvmin0 : 0 < vmin) (hvmin : vmin ≤ deltaVar / 2) (heps : epsZero b β ≤ eps)
    {ρ : ProbabilityMeasure ℝ} (hρ : MomClass b β vmin ρ) :
    MomClass b β vmin (lawPhi eps ρ) := by
  obtain ⟨-, heps1, -, -, hfin, hT1, hCm, -, -⟩ := momClass_setup hvmin0 heps hρ
  have hv0 : 0 < lawVar ρ := hvmin0.trans_le hρ.var_ge
  set σ := Real.sqrt (lawVar ρ) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hv0
  have hσ2 : σ ^ 2 = lawVar ρ := Real.sq_sqrt hv0.le
  have hX : GapLaw (iidLaw ρ) gapCoord 1 σ (∫ x, |x - 1| ^ 3 ∂(ρ : Measure ℝ)) :=
    gapLaw_iidLaw hρ.memLp3 hρ.mean one_pos hσ2.symm hσ le_rfl
  set C := lawC eps ρ with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hCm
  set P := iidLaw ρ with hPdef
  -- the canonical input layer
  set Z := inputPairs (gapCoord : ℕ → (ℕ → ℝ) → ℝ) with hZdef
  have hL0 := layerOK_input hX
  have hmean0 : lmean P Z = 1 := hX.mean
  have hv0' : lvar P Z = σ ^ 2 := by unfold lvar; rw [hmean0]; exact hX.var
  have hs0 : lsig P Z = σ := by unfold lsig; rw [hv0']; exact Real.sqrt_sq hσ.le
  have hL : LayerOK P Z b β vmin KcIn :=
    { hL0 with
      var_le := by rw [hs0, hmean0, hσ2, one_pow, mul_one]; exact hρ.var_le
      var_ge := by rw [hs0, hmean0, hσ2, one_pow, mul_one]; exact hρ.var_ge
      third_le := by
        unfold lkap; rw [hmean0, hs0]
        exact hX.third.trans hρ.third_le }
  obtain ⟨hfin', hL', -, -, -⟩ := layerOK_step hL hb hβ hvmin0 hvmin KcAbs_le_KcIn heps
  set Z' := nextLayer eps Z with hZ'
  have hS : ∀ ω, (Z' 0 ω).1 = stopSum eps ω := fun ω => (stopSum_fst eps (seq Z ω)).symm
  have hS1 : ∫ ω, stopSum eps ω ∂P = C := by
    have h := integral_nextGap hL.iid hL.law hfin' hT1 rfl
    rw [hmean0, one_mul] at h
    have e : ∫ ω, stopSum eps ω ∂P = ∫ ω, (firstBlock eps (seq Z ω)).1 ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => (hS ω).symm)
    rw [e, h]
    rfl
  have hlmean' : lmean P Z' = C := by
    unfold lmean; simp only [hS]; exact hS1
  have hmean1 : lawMean (lawPhi eps ρ) = 1 := lawMean_lawPhi hX hfin hT1 hCpos
  have hmap : ((lawPhi eps ρ : ProbabilityMeasure ℝ) : Measure ℝ) =
      P.map (fun g => stopSum eps g / C) := rfl
  have hSm : Measurable fun g => stopSum eps g / C := (measurable_stopSum eps).div_const _
  have hvar : lawVar (lawPhi eps ρ) = lvar P Z' / C ^ 2 := by
    unfold lawVar
    rw [hmean1, hmap, integral_map hSm.aemeasurable (by fun_prop)]
    unfold lvar
    simp only [hS, hlmean']
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    field_simp
  have hkap : ∫ x, |x - 1| ^ 3 ∂((lawPhi eps ρ : ProbabilityMeasure ℝ) : Measure ℝ) =
      lkap P Z' / C ^ 3 := by
    rw [hmap, integral_map hSm.aemeasurable (by fun_prop)]
    unfold lkap
    simp only [hS, hlmean']
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    rw [← div_pow, ← abs_of_pos hCpos, ← abs_div, abs_of_pos hCpos, sub_div, div_self hCpos.ne']
  have hvge := hL'.var_ge
  have hvle := hL'.var_le
  have hthird := hL'.third_le
  rw [lsig_sq, hlmean'] at hvge hvle
  refine
    { pos := ?_
      memLp3 := ?_
      mean := hmean1
      var_ge := ?_
      var_le := ?_
      third_le := ?_ }
  · -- positivity of the support
    have hae : ∀ᵐ g ∂P, ∀ i, 0 < g i := ae_pos_iidLaw hρ.pos
    have hpos : ∀ᵐ g ∂P, 0 < stopSum eps g := by
      filter_upwards [hae, hfin] with g hg hT
      have h1 : ((⌊2 * eps⌋₊ : ℕ) : ℕ∞) < gapSegLen eps g :=
        floor_two_eps_lt_pairSegLen (by linarith) (seq Z g)
      have h2 : 1 ≤ (gapSegLen eps g).toNat := by
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hT
        rw [← hn] at h1 ⊢
        simp only [ENat.toNat_natCast]
        have : ⌊2 * eps⌋₊ < n := by exact_mod_cast h1
        omega
      unfold stopSum gapKeys
      exact Finset.sum_pos (fun i _ => hg i) (Finset.nonempty_range_iff.2 (by omega))
    rw [hmap, Measure.map_apply hSm measurableSet_Iic]
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hpos] with g hg
    simp only [mem_preimage, mem_Iic, not_le]
    positivity
  · rw [hmap, memLp_map_measure_iff aestronglyMeasurable_id hSm.aemeasurable]
    have h3 := hL'.law.memLp3
    have hfun : (fun ω => (Z' 0 ω).1) = stopSum eps := funext hS
    change MemLp (fun ω => (Z' 0 ω).1) 3 P at h3
    rw [hfun] at h3
    have h4 := MemLp.mul_const h3 C⁻¹
    simpa [Function.comp_def, div_eq_mul_inv] using h4
  · rw [hvar, le_div_iff₀ (by positivity)]; exact hvge
  · rw [hvar, div_le_iff₀ (by positivity)]; exact hvle
  · rw [hkap, hvar, Real.sqrt_div (lvar_nonneg P Z'), Real.sqrt_sq hCpos.le, div_pow,
      ← lsig, mul_div_assoc']
    exact div_le_div_of_nonneg_right hthird (by positivity)

/-- **Exponential stopping tail**: `P(T > m) ≤ (72/71) exp(-tailRate · vmin · m / eps²)`. -/
theorem gapSegLen_tail {b β vmin eps : ℝ} (hvmin0 : 0 < vmin) (heps : epsZero b β ≤ eps)
    {ρ : ProbabilityMeasure ℝ} (hρ : MomClass b β vmin ρ) (m : ℕ) :
    iidLaw ρ {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * Real.exp (-(tailRate * vmin) * m / eps ^ 2)) := by
  obtain ⟨-, heps1, -, hGv, -, -, -, -, L, hL1, hLG, htail⟩ := momClass_setup hvmin0 heps hρ
  set j := m / L with hj
  have hsub : {g | (m : ℕ∞) < gapSegLen eps g} ⊆
      {g | ((j * L : ℕ) : ℕ∞) < gapSegLen eps g} := by
    intro g hg
    have : j * L ≤ m := Nat.div_mul_le_self m L
    exact lt_of_le_of_lt (show ((j * L : ℕ) : ℕ∞) ≤ (m : ℕ∞) from Nat.cast_le.2 this) hg
  have hP : (iidLaw ρ).real {g | (m : ℕ∞) < gapSegLen eps g} ≤ (71 / 72 : ℝ) ^ j :=
    (measureReal_mono hsub).trans (htail j)
  have hmL : (m : ℝ) < (j + 1) * L := by
    have : m < j * L + L := Nat.lt_div_mul_add (by omega)
    have : (m : ℝ) < (j * L + L : ℕ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hLv : (L : ℝ) * vmin ≤ 5185 * eps ^ 2 := by
    have h1 : (L : ℝ) ≤ 5185 * (eps ^ 2 / vmin) := hLG.trans (by gcongr)
    rw [mul_div_assoc', le_div_iff₀ hvmin0] at h1
    exact h1
  have hepspos : 0 < eps := by linarith
  have ha : 0 < Real.log (72 / 71) := Real.log_pos (by norm_num)
  have hkey : tailRate * vmin * m / eps ^ 2 ≤ Real.log (72 / 71) * (j + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : vmin * m ≤ (j + 1) * 5185 * eps ^ 2 := by
      have := mul_le_mul_of_nonneg_left hmL.le hvmin0.le
      have hj0 : (0 : ℝ) ≤ j + 1 := by positivity
      nlinarith
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
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (hP.trans ?_)
  rw [e1, Real.exp_log (by norm_num)]
  gcongr
  rw [neg_mul, neg_div]
  linarith

/-- The maximal Bernstein inequality from centred exponential moments: the exponent step of
`maximal_bernstein`, with `lcbb_centred_moments` replaced by the hypotheses `E φ(Z 0) = 0` and
`E e^{η₀ |φ(Z 0)|} ≤ e^{η₀} B`, `η₀ = bernsteinEta θ`. -/
theorem maximal_bernstein_of_centred {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ × ℕ} (h : IIDPairs P Z) {φ : ℝ × ℕ → ℝ}
    (hφ : Measurable φ) (hXi : Integrable (fun ω => φ (Z 0 ω)) P)
    (hX0 : ∫ ω, φ (Z 0 ω) ∂P = 0) {θ B : ℝ} (hθ : 0 < θ) (hB : 0 < B)
    (hKi : Integrable (fun ω => Real.exp (bernsteinEta θ * |φ (Z 0 ω)|)) P)
    (hKle : ∫ ω, Real.exp (bernsteinEta θ * |φ (Z 0 ω)|) ∂P ≤ Real.exp (bernsteinEta θ) * B)
    (s : ℕ) (hs : 1 ≤ s) {x : ℝ} (hx : 0 < x) :
    P.real {ω | ∃ j ≤ s, x < |∑ i ∈ Finset.range j, φ (Z i ω)|} ≤
      2 * Real.exp (-(bernsteinRate θ B * min (x ^ 2 / s) x)) := by
  have hη := lcbb_eta_pos hθ
  have hC₀ : 0 < bernsteinC0 θ B := lcbb_C0_pos hθ hB
  have hc0 : 0 < bernsteinRate θ B := bernsteinRate_pos hθ hB
  have hC₀eq : 8 / bernsteinEta θ ^ 2 * (Real.exp (bernsteinEta θ) * B) = bernsteinC0 θ B := by
    unfold bernsteinC0; ring
  set η := bernsteinEta θ with hηdef
  set C₀ := bernsteinC0 θ B with hC₀def
  set c := bernsteinRate θ B with hcdef
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  set l := min (η / 2) (x / (2 * C₀ * s)) with hldef
  have hl0 : 0 ≤ l := le_min (by positivity) (by positivity)
  have hlη : l ≤ η / 2 := min_le_left _ _
  have hlx : l ≤ x / (2 * C₀ * s) := min_le_right _ _
  -- the exponent
  have hexpo : C₀ * l ^ 2 * s - l * x ≤ -(c * min (x ^ 2 / s) x) := by
    have h1 : C₀ * l * s ≤ x / 2 := by
      have := mul_le_mul_of_nonneg_left hlx (by positivity : 0 ≤ C₀ * s)
      calc C₀ * l * s = C₀ * s * l := by ring
        _ ≤ C₀ * s * (x / (2 * C₀ * s)) := this
        _ = x / 2 := by field_simp
    have h2 : C₀ * l ^ 2 * s - l * x ≤ -(l * x / 2) := by nlinarith
    have h3 : c * min (x ^ 2 / s) x ≤ l * x / 2 := by
      rcases min_cases (η / 2) (x / (2 * C₀ * s)) with ⟨hl, _⟩ | ⟨hl, _⟩
      · rw [hldef, hl]
        calc c * min (x ^ 2 / s) x ≤ c * x := mul_le_mul_of_nonneg_left (min_le_right _ _) hc0.le
          _ ≤ η / 4 * x := mul_le_mul_of_nonneg_right (min_le_right _ _) hx.le
          _ = η / 2 * x / 2 := by ring
      · rw [hldef, hl]
        calc c * min (x ^ 2 / s) x ≤ c * (x ^ 2 / s) :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) hc0.le
          _ ≤ 1 / (4 * C₀) * (x ^ 2 / s) :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
          _ = x / (2 * C₀ * s) * x / 2 := by field_simp; ring
    linarith
  -- the two one-sided bounds
  have hup := lcbb_one_sided h hφ hXi hX0 hη hKi hKle hl0 hlη s x
  have hdn := lcbb_one_sided (φ := fun z : ℝ × ℕ => -φ z) h hφ.neg hXi.neg
    (by rw [integral_neg, hX0, neg_zero]) hη
    (by simpa only [abs_neg] using hKi) (by simpa only [abs_neg] using hKle) hl0 hlη s x
  rw [hC₀eq] at hup hdn
  have hsub : {ω | ∃ j ≤ s, x < |∑ i ∈ Finset.range j, φ (Z i ω)|} ⊆
      {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, φ (Z i ω)} ∪
        {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, -φ (Z i ω)} := by
    rintro ω ⟨j, hj, hjx⟩
    rcases lt_abs.1 hjx with h1 | h1
    · exact Or.inl ⟨j, hj, h1.le⟩
    · refine Or.inr ⟨j, hj, ?_⟩
      rw [Finset.sum_neg_distrib]
      exact h1.le
  have hE := Real.exp_le_exp.2 hexpo
  calc P.real {ω | ∃ j ≤ s, x < |∑ i ∈ Finset.range j, φ (Z i ω)|}
      ≤ P.real ({ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, φ (Z i ω)} ∪
          {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, -φ (Z i ω)}) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, φ (Z i ω)} +
          P.real {ω | ∃ j ≤ s, x ≤ ∑ i ∈ Finset.range j, -φ (Z i ω)} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (C₀ * l ^ 2 * s - l * x) + Real.exp (C₀ * l ^ 2 * s - l * x) :=
        add_le_add hup hdn
    _ ≤ 2 * Real.exp (-(c * min (x ^ 2 / s) x)) := by linarith

/-- Centred exponential moments of a positive law with mean one and `E e^{θ₁ X} ≤ B₁`, on the
canonical space: `E (X - 1) = 0` and `E e^{η₀ |X - 1|} ≤ e^{η₀} B₁`, `η₀ = bernsteinEta θ₁`. -/
theorem iid_centred_moments {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) {ρ : ProbabilityMeasure ℝ}
    (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ρ = 1) (hexp : ExpMom θ₁ B₁ ρ) :
    Integrable (fun g : ℕ → ℝ => g 0 - 1) (iidLaw ρ) ∧ ∫ g, (g 0 - 1) ∂(iidLaw ρ) = 0 ∧
      Integrable (fun g : ℕ → ℝ => Real.exp (bernsteinEta θ₁ * |g 0 - 1|)) (iidLaw ρ) ∧
      ∫ g, Real.exp (bernsteinEta θ₁ * |g 0 - 1|) ∂(iidLaw ρ) ≤
        Real.exp (bernsteinEta θ₁) * B₁ := by
  have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => (ρ : Measure ℝ)) 0
  set η := bernsteinEta θ₁ with hηdef
  have hη0 : 0 < η := lcbb_eta_pos hθ₁
  have h2η : 2 * η ≤ θ₁ := lcbb_two_eta_le θ₁
  have hpos' : ∀ᵐ x ∂(ρ : Measure ℝ), 0 ≤ x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hpos] with x hx
    simp only [mem_Iic, not_le] at hx
    exact hx.le
  have hint1 : Integrable (fun x : ℝ => x) (ρ : Measure ℝ) :=
    Integrable.of_integral_ne_zero (by
      change lawMean ρ ≠ 0
      rw [hmean]; exact one_ne_zero)
  have hKm : Measurable fun x : ℝ => Real.exp (η * |x - 1|) := by fun_prop
  have hdom : ∀ᵐ x ∂(ρ : Measure ℝ), ‖Real.exp (η * |x - 1|)‖ ≤
      Real.exp η * Real.exp (θ₁ * x) := by
    filter_upwards [hpos'] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : |x - 1| ≤ x + 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  have hKint : Integrable (fun x : ℝ => Real.exp (η * |x - 1|)) (ρ : Measure ℝ) :=
    (hexp.integrable.const_mul (Real.exp η)).mono' hKm.aestronglyMeasurable hdom
  have hKle : ∫ x, Real.exp (η * |x - 1|) ∂(ρ : Measure ℝ) ≤ Real.exp η * B₁ := by
    calc ∫ x, Real.exp (η * |x - 1|) ∂(ρ : Measure ℝ)
        ≤ ∫ x, Real.exp η * Real.exp (θ₁ * x) ∂(ρ : Measure ℝ) :=
          integral_mono_ae hKint (hexp.integrable.const_mul _)
            (hdom.mono fun x hx => (le_abs_self _).trans hx)
      _ = Real.exp η * ∫ x, Real.exp (θ₁ * x) ∂(ρ : Measure ℝ) := integral_const_mul _ _
      _ ≤ Real.exp η * B₁ := by gcongr; exact hexp.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hmp.integrable_comp (g := fun x : ℝ => x - 1)
      (by fun_prop)).2 (hint1.sub (integrable_const 1))
  · refine (integral_gapCoord_zero ρ (F := fun x => x - 1) (by fun_prop)).trans ?_
    rw [integral_sub hint1 (integrable_const 1)]
    change lawMean ρ - _ = 0
    simp [hmean]
  · exact (hmp.integrable_comp (g := fun x : ℝ => Real.exp (η * |x - 1|))
      hKm.aestronglyMeasurable).2 hKint
  · exact (integral_gapCoord_zero ρ (F := fun x => Real.exp (η * |x - 1|)) hKm).trans_le hKle

/-- **Maximal Bernstein inequality** for iid mean-one positive gaps with an exponential
moment. -/
theorem iid_maximal_bernstein {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) {ρ : ProbabilityMeasure ℝ}
    (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ρ = 1) (hexp : ExpMom θ₁ B₁ ρ)
    (s : ℕ) (hs : 1 ≤ s) {x : ℝ} (hx : 0 < x) :
    (iidLaw ρ).real {g | ∃ j ≤ s, x < |gapKeys g j - j|} ≤
      2 * Real.exp (-(bernsteinRate θ₁ B₁ * min (x ^ 2 / s) x)) := by
  have hZ : IIDPairs (iidLaw ρ) (inputPairs gapCoord) := IIDPairs.inputPairs (iidSeq_gapCoord ρ)
  have hB₁ : 0 < B₁ := (integral_exp_pos hexp.integrable).trans_le hexp.le
  obtain ⟨hXi, hX0, hKi, hKle⟩ := iid_centred_moments hθ₁ hpos hmean hexp
  have h := maximal_bernstein_of_centred (φ := fun z : ℝ × ℕ => z.1 - 1) hZ
    (measurable_fst.sub_const 1) hXi hX0 hθ₁ hB₁ hKi hKle s hs hx
  have hset : {g : ℕ → ℝ | ∃ j ≤ s, x < |gapKeys g j - j|} =
      {g | ∃ j ≤ s, x < |∑ i ∈ Finset.range j, ((inputPairs gapCoord i g).1 - 1)|} := by
    ext g
    simp only [Set.mem_ofPred_eq, inputPairs, gapCoord, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, gapKeys]
  rw [hset]
  exact h

/-- **Endpoint Bernstein inequality**: `P(|S_n - n| ≥ d) ≤ 2 exp(-(c/4) min(d²/n, d))`. -/
theorem iid_endpoint_bernstein {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) {ρ : ProbabilityMeasure ℝ}
    (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ρ = 1) (hexp : ExpMom θ₁ B₁ ρ)
    (n : ℕ) (hn : 1 ≤ n) {d : ℝ} (hd : 0 ≤ d) :
    (iidLaw ρ).real {g | d ≤ |gapKeys g n - n|} ≤
      2 * Real.exp (-(bernsteinRate θ₁ B₁ / 4 * min (d ^ 2 / n) d)) := by
  have hB₁ : 0 < B₁ := (integral_exp_pos hexp.integrable).trans_le hexp.le
  have hc := bernsteinRate_pos hθ₁ hB₁
  rcases hd.eq_or_lt with rfl | hd0
  · have h1 : (iidLaw ρ).real {g | (0 : ℝ) ≤ |gapKeys g n - n|} ≤ 1 := measureReal_le_one
    have h2 : (0 : ℝ) ^ 2 / n = 0 := by simp
    rw [h2, min_self, mul_zero, neg_zero, Real.exp_zero]
    linarith
  have hsub : {g : ℕ → ℝ | d ≤ |gapKeys g n - n|} ⊆
      {g | ∃ j ≤ n, d / 2 < |gapKeys g j - j|} := fun g hg =>
    ⟨n, le_rfl, lt_of_lt_of_le (by linarith) hg⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (measureReal_mono hsub).trans ((iid_maximal_bernstein hθ₁ hpos hmean hexp n hn
    (by linarith : 0 < d / 2)).trans ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) (by norm_num)
  have hmin : min (d ^ 2 / n) d / 4 ≤ min ((d / 2) ^ 2 / n) (d / 2) := by
    refine le_min ?_ ?_
    · calc min (d ^ 2 / n) d / 4 ≤ d ^ 2 / n / 4 := by gcongr; exact min_le_left _ _
        _ = (d / 2) ^ 2 / n := by ring
    · calc min (d ^ 2 / n) d / 4 ≤ d / 4 := by gcongr; exact min_le_right _ _
        _ ≤ d / 2 := by linarith
  calc bernsteinRate θ₁ B₁ / 4 * min (d ^ 2 / n) d
      = bernsteinRate θ₁ B₁ * (min (d ^ 2 / n) d / 4) := by ring
    _ ≤ bernsteinRate θ₁ B₁ * min ((d / 2) ^ 2 / n) (d / 2) := by gcongr

/-- **Cumulant bound** for a general exponential moment (the `(θ₁, B₁)` version of
`integral_exp_mul_le`): if `X ≥ 0` a.e., `E X ≤ 1` and `E e^{θ₁ X} ≤ B₁`, then
`E e^{θ X} ≤ exp(θ + (8 B₁/θ₁²) θ²)` for `0 ≤ θ ≤ θ₁/2`. -/
theorem integral_exp_mul_le_of_expMom {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁)
    (hX0 : ∀ᵐ ω ∂P, 0 ≤ X ω) (hX1 : Integrable X P) (hXmean : ∫ ω, X ω ∂P ≤ 1)
    (hXe : Integrable (fun ω => Real.exp (θ₁ * X ω)) P)
    (hXeC : ∫ ω, Real.exp (θ₁ * X ω) ∂P ≤ B₁) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ θ₁ / 2) :
    Integrable (fun ω => Real.exp (θ * X ω)) P ∧
      ∫ ω, Real.exp (θ * X ω) ∂P ≤ Real.exp (θ + 8 * B₁ / θ₁ ^ 2 * θ ^ 2) := by
  have hint : Integrable (fun ω => Real.exp (θ * X ω)) P := by
    refine hXe.mono' ?_ (hX0.mono fun ω hω => ?_)
    · exact (Real.measurable_exp.comp_aemeasurable
        (hX1.aemeasurable.const_mul θ)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hω)
  refine ⟨hint, ?_⟩
  have hbd : Integrable (fun ω => 1 + θ * X ω + θ ^ 2 * (8 / θ₁ ^ 2 *
      Real.exp (θ₁ * X ω))) P :=
    ((integrable_const 1).add (hX1.const_mul θ)).add ((hXe.const_mul _).const_mul _)
  calc ∫ ω, Real.exp (θ * X ω) ∂P
      ≤ ∫ ω, (1 + θ * X ω + θ ^ 2 * (8 / θ₁ ^ 2 * Real.exp (θ₁ * X ω))) ∂P :=
        integral_mono_ae hint hbd (hX0.mono fun ω hω => exp_mul_le_quadratic hθ₁ hθ0 hθ hω)
    _ = 1 + θ * ∫ ω, X ω ∂P + θ ^ 2 * (8 / θ₁ ^ 2 * ∫ ω, Real.exp (θ₁ * X ω) ∂P) := by
        rw [integral_add (f := fun ω => 1 + θ * X ω)
          (g := fun ω => θ ^ 2 * (8 / θ₁ ^ 2 * Real.exp (θ₁ * X ω)))
          ((integrable_const 1).add (hX1.const_mul θ)) ((hXe.const_mul _).const_mul _),
          integral_add (f := fun _ => (1 : ℝ)) (g := fun ω => θ * X ω) (integrable_const 1)
          (hX1.const_mul θ), integral_const_mul, integral_const_mul, integral_const_mul]
        simp
    _ ≤ 1 + θ * 1 + θ ^ 2 * (8 / θ₁ ^ 2 * B₁) := by
        gcongr
    _ = 1 + (θ + 8 * B₁ / θ₁ ^ 2 * θ ^ 2) := by ring
    _ ≤ Real.exp (θ + 8 * B₁ / θ₁ ^ 2 * θ ^ 2) := by
        linarith [Real.add_one_le_exp (θ + 8 * B₁ / θ₁ ^ 2 * θ ^ 2)]

/-- **Exponential moments along the orbit** (`lem:expmom`, gap version of `hyperexp_step`):
for `eps` large in terms of `(b, β, vmin, θ₁, B₁)`, the next layer has the absolute
exponential moment `E e^{θK X} ≤ CK`. -/
theorem lawPhi_expMom {b β vmin θ₁ B₁ : ℝ} (hvmin0 : 0 < vmin) (hθ₁ : 0 < θ₁)
    (hB₁ : 0 < B₁) :
    ∃ e₂ : ℝ, ∀ eps, e₂ ≤ eps → ∀ ρ : ProbabilityMeasure ℝ, MomClass b β vmin ρ →
      ExpMom θ₁ B₁ ρ → ExpMom θK CK (lawPhi eps ρ) := by
  set K₁ : ℝ := 8 * B₁ / θ₁ ^ 2 with hK₁
  set G₁ : ℝ := aK / θ₁ + K₁ * aK with hG₁
  refine ⟨max (epsZero b β) (G₁ * b), fun eps heps ρ hρ hexp => ?_⟩
  have heps0 : epsZero b β ≤ eps := le_trans (le_max_left _ _) heps
  obtain ⟨hb0, heps1, hGb, -, hfin, -, hC, -, L, hL1, hLG, htail⟩ :=
    momClass_setup hvmin0 heps0 hρ
  set G := eps ^ 2 / lawVar ρ with hGdef
  set C := lawC eps ρ with hCdef
  set P := iidLaw ρ with hPdef
  have haK := aK_pos
  have hK₁0 : 0 < K₁ := by positivity
  -- `G ≥ G₁`
  have hGG₁ : G₁ ≤ G := by
    have h1 : G₁ * b ≤ eps := le_trans (le_max_right _ _) heps
    have h2 : eps ≤ eps ^ 2 := by nlinarith
    have h3 : G₁ ≤ eps ^ 2 / b := by rw [le_div_iff₀ hb0]; linarith
    linarith
  have hGpos : 0 < G := lt_of_lt_of_le (by positivity) hGG₁
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hC
  -- the parameters
  set θ : ℝ := aK / (2 * G) with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hθ₁2 : θ ≤ θ₁ / 2 := by
    have h1 : aK / θ₁ ≤ G := le_trans (le_add_of_nonneg_right (by positivity)) hGG₁
    rw [div_le_iff₀ hθ₁] at h1
    rw [hθdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set Λ : ℝ := θ + K₁ * θ ^ 2 with hΛdef
  have hK₁θ : K₁ * θ ≤ 1 := by
    have h1 : K₁ * aK ≤ G := le_trans (le_add_of_nonneg_left (by positivity)) hGG₁
    rw [hθdef, mul_div_assoc', div_le_one (by positivity)]
    linarith
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛ2 : Λ ≤ 2 * θ := by
    have : K₁ * θ ^ 2 ≤ θ := by nlinarith
    linarith
  have hΛL : Λ * L ≤ 1 / 144 := by
    have h1 : Λ * L ≤ 2 * θ * (5185 * G) := by
      have := mul_le_mul hΛ2 hLG (Nat.cast_nonneg L) (by positivity)
      linarith
    have h2 : 2 * θ * (5185 * G) = 5185 * aK := by
      rw [hθdef]; field_simp
    rw [h2] at h1
    unfold aK at h1
    linarith
  -- (a) the cumulant bound on `ρ`
  have hpos' : ∀ᵐ x ∂(ρ : Measure ℝ), 0 ≤ x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hρ.pos] with x hx
    simp only [mem_Iic, not_le] at hx
    exact hx.le
  have hint1 : Integrable (fun x : ℝ => x) (ρ : Measure ℝ) :=
    hρ.memLp3.integrable (by norm_num)
  obtain ⟨hθint, hθle⟩ := integral_exp_mul_le_of_expMom (X := fun x : ℝ => x) hθ₁ hpos' hint1
    (by change lawMean ρ ≤ 1; rw [hρ.mean]) hexp.integrable hexp.le hθ0 hθ₁2
  -- (b) the stopped supermartingale on the canonical input pairs
  set Z := inputPairs (gapCoord : ℕ → (ℕ → ℝ) → ℝ) with hZdef
  have hZ : IIDPairs P Z := IIDPairs.inputPairs (iidSeq_gapCoord ρ)
  set f : ℝ × ℕ → ℝ := fun p => θ * p.1 with hfdef
  have hf : Measurable f := measurable_fst.const_mul θ
  have hexpΛ : ∫⁻ g, ENNReal.ofReal (Real.exp (f (Z 0 g) - Λ)) ∂P ≤ 1 := by
    have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => (ρ : Measure ℝ)) 0
    have e : ∫⁻ g, ENNReal.ofReal (Real.exp (f (Z 0 g) - Λ)) ∂P =
        ∫⁻ x, ENNReal.ofReal (Real.exp (θ * x - Λ)) ∂(ρ : Measure ℝ) :=
      hmp.lintegral_comp (f := fun x => ENNReal.ofReal (Real.exp (θ * x - Λ))) (by fun_prop)
    rw [e]
    have hint : Integrable (fun x : ℝ => Real.exp (θ * x - Λ)) (ρ : Measure ℝ) := by
      refine (hθint.mul_const (Real.exp (-Λ))).congr (Eventually.of_forall fun x => ?_)
      simp only [sub_eq_add_neg, Real.exp_add]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ => (Real.exp_pos _).le), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have e2 : ∫ x, Real.exp (θ * x - Λ) ∂(ρ : Measure ℝ) =
        (∫ x, Real.exp (θ * x) ∂(ρ : Measure ℝ)) * Real.exp (-Λ) := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [sub_eq_add_neg, Real.exp_add]
    rw [e2]
    calc (∫ x, Real.exp (θ * x) ∂(ρ : Measure ℝ)) * Real.exp (-Λ) ≤
          Real.exp Λ * Real.exp (-Λ) :=
          mul_le_mul_of_nonneg_right hθle (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hM := lintegral_exp_stopped_le_one hZ eps hf Λ hexpΛ hfin
  -- (c) the exponential moment of `T`
  have hTm : Measurable fun g : ℕ → ℝ => gapSegLen eps g := (isStoppingRule_gapSegLen eps).measurable
  have hTexp := lintegral_exp_toNat_le_145 (P := P) hTm hL1 hΛ0 hΛL htail
  -- (d) the arithmetic-geometric mean inequality, pathwise
  have hid : ∀ g, stoppedSumE (fun t ω => f (Z t ω) - Λ) (fun ω => pairSegLen eps (seq Z ω)) g =
      θ * stopSum eps g - Λ * ((gapSegLen eps g).toNat : ℝ) := by
    intro g
    show ∑ i ∈ Finset.range (gapSegLen eps g).toNat, (θ * g i - Λ) =
      θ * ∑ i ∈ Finset.range (gapSegLen eps g).toNat, g i - Λ * ((gapSegLen eps g).toNat : ℝ)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    ring
  have hθC : 2 * θK ≤ θ * C := by
    have h1 : θ * (G / 128) ≤ θ * C := mul_le_mul_of_nonneg_left hC hθ0
    have h2 : θ * (G / 128) = 2 * θK := by
      rw [hθdef, θK]; field_simp; ring
    linarith
  have hSnn : ∀ᵐ g ∂P, 0 ≤ stopSum eps g := by
    filter_upwards [ae_pos_iidLaw hρ.pos] with g hg
    unfold stopSum gapKeys
    exact Finset.sum_nonneg fun i _ => (hg i).le
  have hpt : ∀ᵐ g ∂P, Real.exp (θK * (stopSum eps g / C)) ≤
      (Real.exp (stoppedSumE (fun t ω => f (Z t ω) - Λ) (fun ω => pairSegLen eps (seq Z ω)) g) +
        Real.exp (Λ * ((gapSegLen eps g).toNat : ℝ))) / 2 := by
    filter_upwards [hSnn] with g hg
    refine le_trans ?_ (exp_half_add_le _ _)
    rw [hid]
    refine Real.exp_le_exp.2 ?_
    have hsum : (θ * stopSum eps g - Λ * ((gapSegLen eps g).toNat : ℝ) +
        Λ * ((gapSegLen eps g).toNat : ℝ)) / 2 = θ * stopSum eps g / 2 := by ring
    rw [hsum, mul_div_assoc', div_le_div_iff₀ hCpos (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hθC hg]
  -- (e) integrate
  have hTn : Measurable fun g : ℕ → ℝ => ((gapSegLen eps g).toNat : ℝ) :=
    (Measurable.of_discrete (f := fun n : ℕ∞ => (n.toNat : ℝ))).comp hTm
  have hlint : ∫⁻ g, ENNReal.ofReal (Real.exp (θK * (stopSum eps g / C))) ∂P ≤
      ENNReal.ofReal 73 := by
    calc ∫⁻ g, ENNReal.ofReal (Real.exp (θK * (stopSum eps g / C))) ∂P
        ≤ ∫⁻ g, (ENNReal.ofReal (1 / 2) * ENNReal.ofReal
            (Real.exp (stoppedSumE (fun t ω => f (Z t ω) - Λ)
              (fun ω => pairSegLen eps (seq Z ω)) g)) +
            ENNReal.ofReal (1 / 2) * ENNReal.ofReal
              (Real.exp (Λ * ((gapSegLen eps g).toNat : ℝ)))) ∂P := by
          refine lintegral_mono_ae (hpt.mono fun g hg => ?_)
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          linarith
      _ = ENNReal.ofReal (1 / 2) * ∫⁻ g, ENNReal.ofReal
            (Real.exp (stoppedSumE (fun t ω => f (Z t ω) - Λ)
              (fun ω => pairSegLen eps (seq Z ω)) g)) ∂P +
          ENNReal.ofReal (1 / 2) * ∫⁻ g, ENNReal.ofReal
            (Real.exp (Λ * ((gapSegLen eps g).toNat : ℝ))) ∂P := by
          rw [lintegral_add_right _ (((hTn.const_mul Λ).exp.ennreal_ofReal).const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (1 / 2) * 1 + ENNReal.ofReal (1 / 2) * ENNReal.ofReal 145 := by
          gcongr
      _ = ENNReal.ofReal 73 := by
          rw [mul_one, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  -- transfer to the law `lawPhi eps ρ`
  have hmap : ((lawPhi eps ρ : ProbabilityMeasure ℝ) : Measure ℝ) =
      P.map (fun g => stopSum eps g / C) := rfl
  have hSm : Measurable fun g => stopSum eps g / C := (measurable_stopSum eps).div_const _
  have he : Measurable fun x : ℝ => Real.exp (θK * x) := by fun_prop
  have hlint' : ∫⁻ x, ENNReal.ofReal (Real.exp (θK * x))
      ∂((lawPhi eps ρ : ProbabilityMeasure ℝ) : Measure ℝ) ≤ ENNReal.ofReal 73 := by
    rw [hmap, lintegral_map he.ennreal_ofReal hSm]
    exact hlint
  have hu0 : 0 ≤ᵐ[((lawPhi eps ρ : ProbabilityMeasure ℝ) : Measure ℝ)]
      fun x => Real.exp (θK * x) := Eventually.of_forall fun _ => (Real.exp_pos _).le
  have hint : Integrable (fun x => Real.exp (θK * x))
      ((lawPhi eps ρ : ProbabilityMeasure ℝ) : Measure ℝ) :=
    ⟨he.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hu0).2
      (lt_of_le_of_lt hlint' ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hu0 he.aestronglyMeasurable]
  unfold CK
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hlint'

end

end PGM
