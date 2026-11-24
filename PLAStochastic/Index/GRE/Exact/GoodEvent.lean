import PLAStochastic.Index.GRE.Exact.Deterministic
import PLAStochastic.Index.GRE.LogLogTheta

/-!
# The good event of `thm:GRE`

For the Model G keys `x0 + g 0 + ⋯ + g (s-1)` with `GapLaw P g μ₀ σ₀ κ₀`, write
`A = μ₀² ε² / σ₀²` (the TeX `G₀`), `t = tRE (n²) + 1`, `τ = 4 t / aRE` and
`θ = √(A n) / log n`.  The good event `greGood` is `𝒞_n ∩ 𝒲_n`:

* `𝒞_n = (reBad ε g A (tRE (n²)) n)ᶜ`, on which every ALG-RE layer is in the count bracket
  (`bracket_of_not_reBad`); its failure probability is at most `1 / n²`;
* `𝒲_n = {max_{k ≤ n} |∑_{i<k} (g_i - μ₀)| < σ₀ √n log n}` (`kolEvent`), with
  `P(𝒲_nᶜ) ≤ 1 / log² n` by Kolmogorov's maximal inequality.

On `𝒲_n` every layer with `N_ℓ ≤ θ` is one segment (Step 1,
`reSize_succ_eq_one_of_kolEvent`), so `reHeight_window_of_bracket` applies on `greGood`
(`reHeight_window_of_greGood`).  `integral_le_of_event` and `le_integral_of_event` turn pathwise
bounds on an event into expectation bounds.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ## The Kolmogorov event -/

/-- `𝒲_n = {max_{k ≤ n} |∑_{i<k} (g_i - μ)| < σ √n log n}`. -/
def kolEvent (g : ℕ → Ω → ℝ) (μ σ : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ k ≤ n, |partialSum (centred g μ) k ω| < σ * Real.sqrt n * Real.log n}

theorem measurableSet_kolEvent {g : ℕ → Ω → ℝ} (hg : ∀ s, Measurable (g s)) (μ σ : ℝ)
    (n : ℕ) : MeasurableSet (kolEvent g μ σ n) := by
  have : kolEvent g μ σ n = ⋂ k ∈ range (n + 1),
      {ω | |partialSum (centred g μ) k ω| < σ * Real.sqrt n * Real.log n} := by
    ext ω
    simp only [kolEvent, Set.mem_ofPred_eq, Set.mem_iInter, mem_range, Nat.lt_succ_iff]
  rw [this]
  refine MeasurableSet.biInter (range (n + 1)).countable_toSet fun k _ => ?_
  have hm : Measurable (partialSum (centred g μ) k) :=
    Finset.measurable_sum _ fun i _ => (hg i).sub measurable_const
  exact measurableSet_lt (continuous_abs.measurable.comp hm) measurable_const

private theorem integral_centredSum_sq [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ σ κ : ℝ}
    (hg : GapLaw P g μ σ κ) (n : ℕ) :
    ∫ ω, partialSum (centred g μ) n ω ^ 2 ∂P = n * σ ^ 2 := by
  rw [partialSum_eq_weightedSum_one, integral_weightedSum_sq hg.indepIncrements
    (PredictableWeight.one _) (fun t => (hg.memLp_centred t).mono_exponent (by norm_num))
    hg.integral_centred]
  simp [hg.integral_centred_sq]

/-- Kolmogorov's maximal inequality at level `σ₀ √n log n`: `P(𝒲_nᶜ) ≤ 1 / log² n`. -/
theorem measureReal_kolEvent_compl_le [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}
    {μ₀ σ₀ κ₀ : ℝ} (hg : GapLaw P g μ₀ σ₀ κ₀) {n : ℕ} (hn : 2 ≤ n) :
    P.real (kolEvent g μ₀ σ₀ n)ᶜ ≤ 1 / Real.log n ^ 2 := by
  have hσ := hg.sigma_pos
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log n := Real.log_pos hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hlam0 : 0 < σ₀ * Real.sqrt n * Real.log n := by positivity
  have hk := kolmogorov_maximal hg.indepIncrements
    (fun t => (hg.memLp_centred t).mono_exponent (by norm_num)) hg.integral_centred hlam0 n
  rw [integral_centredSum_sq hg] at hk
  have hc : (kolEvent g μ₀ σ₀ n)ᶜ =
      {ω | ∃ k ≤ n, σ₀ * Real.sqrt n * Real.log n ≤ |partialSum (centred g μ₀) k ω|} := by
    ext ω
    simp [kolEvent]
  rw [hc]
  have hlam2 : (σ₀ * Real.sqrt n * Real.log n) ^ 2 = σ₀ ^ 2 * n * Real.log n ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
  rw [hlam2] at hk
  rw [le_div_iff₀ (by positivity)]
  have hnσ : 0 < σ₀ ^ 2 * n := by positivity
  refine le_of_mul_le_mul_left ?_ hnσ
  nlinarith

/-! ## Step 1 on the Kolmogorov event -/

omit mΩ in
/-- **Step 1** (`thm:GRE`): on `𝒲_n`, a layer with `N_ℓ ≤ √(A n) / log n` is one segment,
witnessed by the line `x ↦ (x - x0) / (μ₀ Δ_ℓ)`. -/
theorem reSize_succ_eq_one_of_kolEvent {g : ℕ → Ω → ℝ} {μ₀ σ₀ : ℝ} (hμ : 0 < μ₀)
    (hσ : 0 < σ₀) {eps : ℝ} (heps : 1 ≤ eps) {n : ℕ} (hn : 2 ≤ n) (x0 : ℝ) {ω : Ω}
    (hω : ω ∈ kolEvent g μ₀ σ₀ n) (ℓ : ℕ)
    (hN : (reSize eps (fun s => x0 + ∑ i ∈ range s, g i ω) n ℓ : ℝ) ≤
      Real.sqrt (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 * n) / Real.log n) :
    reSize eps (fun s => x0 + ∑ i ∈ range s, g i ω) n (ℓ + 1) = 1 := by
  set p : ℕ → ℝ := fun s => x0 + ∑ i ∈ range s, g i ω with hp
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log n := Real.log_pos hnR
  have hsqn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have heps0 : 0 < eps := by linarith
  have hsqA : Real.sqrt (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 * n) = μ₀ * eps / σ₀ * Real.sqrt n := by
    rw [show μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 * n = (μ₀ * eps / σ₀) ^ 2 * n by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hsqA, le_div_iff₀ hL] at hN
  have hNpos : (0 : ℝ) < reSize eps p n ℓ := by exact_mod_cast one_le_reSize heps hn1 ℓ
  have hcov : (n : ℝ) ≤ (reSize eps p n ℓ : ℝ) * reDelta eps p n ℓ := by
    exact_mod_cast (re_cover (p := p) heps hn1 ℓ).2
  -- `σ₀ √n log n ≤ μ₀ Δ_ℓ eps`
  have hkey : σ₀ * Real.sqrt n * Real.log n ≤ μ₀ * reDelta eps p n ℓ * eps := by
    have h1 : σ₀ * (reSize eps p n ℓ : ℝ) * Real.log n ≤ μ₀ * eps * Real.sqrt n := by
      have := mul_le_mul_of_nonneg_left hN hσ.le
      field_simp at this
      linarith
    have h2 : σ₀ * Real.sqrt n * Real.log n * reSize eps p n ℓ ≤
        μ₀ * reDelta eps p n ℓ * eps * reSize eps p n ℓ := by
      have h3 := mul_le_mul_of_nonneg_left h1 hsqn.le
      have h4 : Real.sqrt n * (μ₀ * eps * Real.sqrt n) = μ₀ * eps * n := by
        rw [show Real.sqrt n * (μ₀ * eps * Real.sqrt n) = μ₀ * eps * (Real.sqrt n * Real.sqrt n)
          by ring, Real.mul_self_sqrt (by linarith)]
      have h5 : μ₀ * eps * n ≤ μ₀ * eps * ((reSize eps p n ℓ : ℝ) * reDelta eps p n ℓ) :=
        mul_le_mul_of_nonneg_left hcov (by positivity)
      nlinarith
    exact le_of_mul_le_mul_right h2 hNpos
  apply reSize_succ_eq_one_of_tube heps hn1 hμ (x0 := x0)
  intro j hj
  have hjn : j * reDelta eps p n ℓ < n := mul_reDelta_lt heps hn1 hj
  have hW := hω (j * reDelta eps p n ℓ) hjn.le
  have heq : p (j * reDelta eps p n ℓ) - x0 - μ₀ * ((j * reDelta eps p n ℓ : ℕ) : ℝ) =
      partialSum (centred g μ₀) (j * reDelta eps p n ℓ) ω := by
    simp only [hp, partialSum, centred, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    ring
  rw [heq]
  linarith

/-! ## The good event -/

/-- The good event `𝒞_n ∩ 𝒲_n` of `thm:GRE`: every lattice pair is in the count bracket at
level `tRE (n²)`, and the Kolmogorov event holds. -/
def greGood (eps : ℝ) (g : ℕ → Ω → ℝ) (μ σ : ℝ) (n : ℕ) : Set Ω :=
  (reBad eps g (μ ^ 2 * eps ^ 2 / σ ^ 2) (tRE (n ^ 2)) n)ᶜ ∩ kolEvent g μ σ n

theorem measurableSet_greGood {g : ℕ → Ω → ℝ} (hg : ∀ s, Measurable (g s)) (eps μ σ : ℝ)
    (n : ℕ) : MeasurableSet (greGood eps g μ σ n) :=
  (measurableSet_reBad hg _ _ _ _).compl.inter (measurableSet_kolEvent hg _ _ _)

/-- `P(greGoodᶜ) ≤ 1 / n² + 1 / log² n`. -/
theorem measureReal_greGood_compl_le [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}
    {μ₀ σ₀ κ₀ : ℝ} (hg : GapLaw P g μ₀ σ₀ κ₀) {eps : ℝ}
    (heps : epsZero (σ₀ ^ 2 / μ₀ ^ 2) (2 + κ₀ / σ₀ ^ 3) ≤ eps) {n : ℕ} (hn : 3 ≤ n) :
    P.real (greGood eps g μ₀ σ₀ n)ᶜ ≤ 1 / (n : ℝ) ^ 2 + 1 / Real.log n ^ 2 := by
  rw [greGood, Set.compl_inter, compl_compl]
  refine (measureReal_union_le _ _).trans
    (add_le_add ?_ (measureReal_kolEvent_compl_le hg (by omega)))
  refine (measureReal_reBad_le hg heps _ n).trans ?_
  have hn2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hpf := pairFail_tRE_le hn2
  push_cast at hpf
  have hN : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hsq : ((2 * n + 1 : ℕ) : ℝ) ^ 2 ≤ 9 * (n : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have h81 : (81 : ℝ) ≤ (n : ℝ) ^ 4 := by
    have : (3 : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hN 4
    norm_num at this
    linarith
  calc ((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail (tRE (n ^ 2))
      ≤ 9 * (n : ℝ) ^ 2 * (2 / ((n : ℝ) ^ 2) ^ 4) :=
        mul_le_mul hsq hpf (pairFail_nonneg _) (by positivity)
    _ = 18 / (n : ℝ) ^ 4 * (1 / (n : ℝ) ^ 2) := by field_simp; ring
    _ ≤ 1 * (1 / (n : ℝ) ^ 2) := by
        gcongr
        rw [div_le_one (by positivity)]
        linarith
    _ = 1 / (n : ℝ) ^ 2 := one_mul _

omit mΩ in
/-- **Pathwise window on the good event.**  With `A = μ₀² ε² / σ₀²`, `t = tRE (n²) + 1`,
`τ = 4 t / aRE` and `θ = √(A n) / log n`, the conclusions of `reHeight_window_of_bracket`
hold on `greGood` whenever `y ≥ 0` and `w > 0` dominate the three `log₂` thresholds. -/
theorem reHeight_window_of_greGood {g : ℕ → Ω → ℝ} {μ₀ σ₀ : ℝ} (hμ : 0 < μ₀) (hσ : 0 < σ₀)
    {eps : ℝ} (heps : 1 ≤ eps) {n : ℕ} (hn : 2 ≤ n) (x0 : ℝ) {ω : Ω}
    (hω : ω ∈ greGood eps g μ₀ σ₀ n) {y w : ℝ}
    (hA : 4 * 128 < μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)
    (hθ : 2 * (128 * (4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE) + ((tRE (n ^ 2) : ℝ) + 1)) ≤
      Real.sqrt (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 * n) / Real.log n)
    (hθn : Real.sqrt (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 * n) / Real.log n ≤ 2 * n)
    (hτn : 4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE ≤ n)
    (hy : 0 ≤ y) (hw : 0 < w)
    (hlo : y - w ≤ Real.logb 2 ((Real.log n - Real.log (4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE)) /
      Real.log (2 / aRE * (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)) + 1))
    (hup : Real.logb 2 (Real.log n / Real.log (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 / (4 * 128)) + 1) ≤
      y + w)
    (htop : Real.logb 2 ((Real.log n + 2 * Real.log (2 * Real.log n)) /
      Real.log (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 / (4 * 128)) + 1) ≤ y + w) :
    (y - w < reHeight eps (fun s => x0 + ∑ i ∈ range s, g i ω) n ∧
        (reHeight eps (fun s => x0 + ∑ i ∈ range s, g i ω) n : ℝ) ≤ y + 1 + w) ∧
      ((∀ m : ℤ, w ≤ |y - m|) →
        ((reHeight eps (fun s => x0 + ∑ i ∈ range s, g i ω) n : ℕ) : ℤ) = ⌈y⌉) := by
  obtain ⟨hbad, hkol⟩ := hω
  have hA0 : 0 < μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 := by linarith
  have hbr := bracket_of_not_reBad heps hA0 (by omega) x0 (tRE (n ^ 2)) hbad
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log n := Real.log_pos hnR
  have ht : (1 : ℝ) ≤ (tRE (n ^ 2) : ℝ) + 1 := by
    have := (Nat.cast_nonneg (tRE (n ^ 2)) : (0 : ℝ) ≤ _); linarith
  -- `2 log (2 n / θ) + log (A / 512) ≤ log n + 2 log (2 log n)`
  have hXtop : 2 * Real.log (2 * n / (Real.sqrt (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 * n) /
      Real.log n)) + Real.log (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 / (4 * 128)) ≤
      Real.log n + 2 * Real.log (2 * Real.log n) := by
    set A := μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2
    clear_value A
    have hsq : 0 < Real.sqrt (A * n) := Real.sqrt_pos.2 (by positivity)
    have e1 : Real.log (2 * n / (Real.sqrt (A * n) / Real.log n)) =
        Real.log 2 + Real.log n + Real.log (Real.log n) - (Real.log A + Real.log n) / 2 := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_div hsq.ne' hL.ne',
        Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity),
        Real.log_mul hA0.ne' (by positivity)]
      ring
    have e2 : Real.log (A / (4 * 128)) = Real.log A - Real.log 512 := by
      rw [Real.log_div hA0.ne' (by norm_num)]; norm_num
    have e3 : Real.log (2 * Real.log n) = Real.log 2 + Real.log (Real.log n) :=
      Real.log_mul (by norm_num) hL.ne'
    have h512 : 0 ≤ Real.log 512 := Real.log_nonneg (by norm_num)
    rw [e1, e2, e3]
    linarith
  exact reHeight_window_of_bracket heps (by omega) aRE_pos aRE_le_one (by norm_num) ht hA hbr
    (fun ℓ hN => reSize_succ_eq_one_of_kolEvent hμ hσ heps hn x0 hkol ℓ hN)
    hθ hθn hτn hXtop hy hw hlo hup htop

/-! ## Expectations from pathwise bounds on an event -/

private theorem integrable_of_bounded [IsProbabilityMeasure P] {H : Ω → ℝ} (hH : Measurable H)
    {Hmax : ℝ} (h0 : ∀ ω, 0 ≤ H ω) (hmax : ∀ ω, H ω ≤ Hmax) : Integrable H P :=
  Integrable.mono' (integrable_const Hmax) hH.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_of_nonneg (h0 ω)]; exact hmax ω)

/-- If `0 ≤ H ≤ Hmax` and `H ≤ U` on `E`, then `E H ≤ U + Hmax · δ` for `P(Eᶜ) ≤ δ`. -/
theorem integral_le_of_event [IsProbabilityMeasure P] {H : Ω → ℝ} (hH : Measurable H)
    {E : Set Ω} (hE : MeasurableSet E) {U Hmax δ : ℝ} (hU : 0 ≤ U) (hHmax : 0 ≤ Hmax)
    (h0 : ∀ ω, 0 ≤ H ω) (hmax : ∀ ω, H ω ≤ Hmax) (hδ : P.real Eᶜ ≤ δ)
    (hgood : ∀ ω ∈ E, H ω ≤ U) : ∫ ω, H ω ∂P ≤ U + Hmax * δ := by
  have h := integral_le_of_good (P := P) hE.compl hH.aestronglyMeasurable hU h0 hmax
    (fun ω hω => hgood ω (by simpa using hω))
  have : Hmax * P.real Eᶜ ≤ Hmax * δ := mul_le_mul_of_nonneg_left hδ hHmax
  linarith

/-- If `0 ≤ H ≤ Hmax` and `V ≤ H` on `E`, then `V - |V| δ ≤ E H` for `P(Eᶜ) ≤ δ`. -/
theorem le_integral_of_event [IsProbabilityMeasure P] {H : Ω → ℝ} (hH : Measurable H)
    {E : Set Ω} (hE : MeasurableSet E) {V Hmax δ : ℝ} (h0 : ∀ ω, 0 ≤ H ω)
    (hmax : ∀ ω, H ω ≤ Hmax) (hδ : P.real Eᶜ ≤ δ) (hgood : ∀ ω ∈ E, V ≤ H ω) :
    V - |V| * δ ≤ ∫ ω, H ω ∂P := by
  have hHint := integrable_of_bounded (P := P) hH h0 hmax
  have hint0 : 0 ≤ ∫ ω, H ω ∂P := integral_nonneg h0
  have hδ0 : 0 ≤ δ := le_trans (measureReal_nonneg (μ := P)) hδ
  rcases le_or_gt V 0 with hV | hV
  · have : 0 ≤ |V| * δ := by positivity
    linarith
  · have hpt : ∀ ω, E.indicator (fun _ => V) ω ≤ H ω := by
      intro ω
      by_cases hω : ω ∈ E
      · rw [Set.indicator_of_mem hω]; exact hgood ω hω
      · rw [Set.indicator_of_notMem hω]; exact h0 ω
    have hmono := integral_mono ((integrable_const V).indicator hE) hHint hpt
    rw [integral_indicator hE, setIntegral_const, smul_eq_mul] at hmono
    have hc := probReal_compl_eq_one_sub (μ := P) hE
    rw [abs_of_pos hV]
    have : V * P.real Eᶜ ≤ V * δ := mul_le_mul_of_nonneg_left hδ hV.le
    nlinarith

end

end PGM
