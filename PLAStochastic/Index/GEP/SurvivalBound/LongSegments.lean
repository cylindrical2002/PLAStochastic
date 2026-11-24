import PLAStochastic.Index.GEP.SurvivalBound.GoodSlope
import PLAStochastic.Index.GEP.SurvivalBound.AbsoluteBounds

/-!
# WP4 `SurvivalBound`: the long segments `k ≥ 8ε`

Source: `task-survival.md` (P2–P3), `progress-surv.md` (坏斜率).

For `k ≥ 8ε` the survival event `{k < T}` is the a.e. disjoint union of the certificate events
(`cert_integral_indicator_eq_sum`), so `cSurv_k` is the sum over the admissible pairs `(i, j)` of
the certificate word functionals.  Each is split by the slope indicator into the good-slope part
(`surv_certInt`, bounded by `surv_good_bound`) and the bad-slope part `surv_badInt`.  The bad
parts are summed first: a.e. at most one certificate holds, and a bad slope forces
`p_k ≥ 3k/2` or `p_k ≤ 5k/8` (`surv_bad_slope_ld`), so `‖∑ bad‖ ≤ b^k E_{ρ̃}[e^{γ' p_k} 1_{LD}]`
through the positive mixture (`surv_norm_wint_le_mix`) and `surv_bad_integral_le` gives
`3 b^k e^{-κ k}`.

`surv_long_bound`: for `1 ≤ ε`, `8ε ≤ k`, `|G y| ≤ e^{γ' y}` (`y ≥ 0`),
`‖cSurv ε ν σ z k G‖ ≤ ∑_{(i,j)} goodB(i,j) + (‖1-z‖ + ‖z‖)^k · 3 e^{-κ k}`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

/-! ## The survival integrand as a word functional -/

/-- The test restricted to the nonnegative axis. -/
def surv_Gpos (G : ℝ → ℝ) : ℝ → ℝ := (Ici (0 : ℝ)).indicator G

theorem surv_measurable_Gpos {G : ℝ → ℝ} (hG : Measurable G) : Measurable (surv_Gpos G) :=
  hG.indicator measurableSet_Ici

theorem surv_abs_Gpos_le {G : ℝ → ℝ} {γ' : ℝ} (hG : ∀ y, 0 ≤ y → |G y| ≤ Real.exp (γ' * y)) (y : ℝ) :
    |surv_Gpos G y| ≤ Real.exp (γ' * y) := by
  unfold surv_Gpos
  by_cases hy : y ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hy]
    exact hG y hy
  · rw [indicator_of_notMem hy, abs_zero]
    exact (Real.exp_pos _).le

theorem surv_abs_Gpos_le_of_le {G : ℝ → ℝ} {γ' : ℝ} (hγ0 : 0 ≤ γ')
    (hG : ∀ y, 0 ≤ y → |G y| ≤ Real.exp (γ' * y)) {Y : ℝ} (y : ℝ) (hy : y ≤ Y) :
    |surv_Gpos G y| ≤ Real.exp (γ' * Y) :=
  (surv_abs_Gpos_le hG y).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hy hγ0))

theorem surv_Gpos_of_nonneg (G : ℝ → ℝ) {y : ℝ} (hy : 0 ≤ y) : surv_Gpos G y = G y :=
  indicator_of_mem (show y ∈ Ici (0 : ℝ) from hy) G

/-- `cSurv` is the word functional of the (complexified) survival integrand. -/
theorem surv_cSurv_eq_wint (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (k : ℕ) (G : ℝ → ℝ) :
    cSurv eps ν σ z k G = surv_wint ν σ z k
      (fun g => (((survSet eps k).indicator (fun g => G (gapKeys g k)) g : ℝ) : ℂ)) := by
  rw [cSurv_eq]
  unfold surv_wint surv_wcoef survInt
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← integral_complex_ofReal]

/-- The survival integrand only sees `G` on the nonnegative axis (positive gaps). -/
theorem surv_survInd_eq_Gpos (eps : ℝ) (k : ℕ) (G : ℝ → ℝ) {g : ℕ → ℝ} (hg : ∀ l, 0 < g l) :
    (survSet eps k).indicator (fun g => G (gapKeys g k)) g =
      (survSet eps k).indicator (fun g => surv_Gpos G (gapKeys g k)) g := by
  have hp : 0 ≤ gapKeys g k := Finset.sum_nonneg fun l _ => (hg l).le
  by_cases h : g ∈ survSet eps k
  · rw [indicator_of_mem h, indicator_of_mem h, surv_Gpos_of_nonneg G hp]
  · rw [indicator_of_notMem h, indicator_of_notMem h]

/-! ## The certificate decomposition -/

theorem surv_ofReal_indicator (s : Set (ℕ → ℝ)) (f : (ℕ → ℝ) → ℝ) (g : ℕ → ℝ) :
    ((s.indicator f g : ℝ) : ℂ) = s.indicator (fun g => (f g : ℂ)) g := by
  by_cases h : g ∈ s
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

/-- **Certificate decomposition of the survival word functional** (`2ε < k`). -/
theorem surv_wint_survInd_eq_certSum (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {eps : ℝ} {k : ℕ}
    (hk : 2 * eps < k) (hνac : (ν : Measure ℝ) ≪ volume) (hσac : (σ : Measure ℝ) ≪ volume)
    (hνpos : (ν : Measure ℝ) (Iic 0) = 0) (hσpos : (σ : Measure ℝ) (Iic 0) = 0) (G' : ℝ → ℝ)
    (hint : ∀ S, Integrable (fun g => (G' (gapKeys g k) : ℂ)) (wordLaw ν σ S)) :
    surv_wint ν σ z k (fun g => (((survSet eps k).indicator (fun g => G' (gapKeys g k)) g : ℝ) : ℂ)) =
      ∑ ij ∈ certPairs eps k, surv_wint ν σ z k (fun g =>
        {g' : ℕ → ℝ | certOK eps (gapKeys g') k ij.1 ij.2}.indicator
          (fun g => (G' (gapKeys g k) : ℂ)) g) := by
  unfold surv_wint
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp only [surv_ofReal_indicator]
  exact cert_integral_indicator_eq_sum hνac hσac hνpos hσpos S hk (hint S)

/-- The bad-slope certificate integrand `1{certOK} · 1{a ∉ [1/2, 2]} · G'(p_k)`. -/
def surv_badInt (eps : ℝ) (k i j : ℕ) (G' : ℝ → ℝ) (g : ℕ → ℝ) : ℂ :=
  {g' : ℕ → ℝ | certOK eps (gapKeys g') k i j}.indicator (fun _ => (1 : ℂ)) g *
    (Icc (1 / 2 : ℝ) 2)ᶜ.indicator (fun _ => (1 : ℂ)) (certSlope eps (gapKeys g) i j) *
    (G' (gapKeys g k) : ℂ)

theorem surv_certInd_eq_good_add_bad (eps : ℝ) (k i j : ℕ) (G' : ℝ → ℝ) (g : ℕ → ℝ) :
    {g' : ℕ → ℝ | certOK eps (gapKeys g') k i j}.indicator (fun g => (G' (gapKeys g k) : ℂ)) g =
      surv_certInt eps k i j G' g + surv_badInt eps k i j G' g := by
  unfold surv_certInt surv_badInt
  by_cases hok : g ∈ {g' : ℕ → ℝ | certOK eps (gapKeys g') k i j}
  · rw [indicator_of_mem hok, indicator_of_mem hok]
    by_cases ha : certSlope eps (gapKeys g) i j ∈ Icc (1 / 2 : ℝ) 2
    · rw [indicator_of_mem ha, indicator_of_notMem (show certSlope eps (gapKeys g) i j ∉
        (Icc (1 / 2 : ℝ) 2)ᶜ from fun h => h ha)]
      ring
    · rw [indicator_of_notMem ha, indicator_of_mem (show certSlope eps (gapKeys g) i j ∈
        (Icc (1 / 2 : ℝ) 2)ᶜ from ha)]
      ring
  · rw [indicator_of_notMem hok, indicator_of_notMem hok]
    ring

theorem surv_measurable_certSlope (eps : ℝ) (i j : ℕ) :
    Measurable fun g : ℕ → ℝ => certSlope eps (gapKeys g) i j :=
  measurable_const.div ((rawAsm_measurable_gapKeys j).sub (rawAsm_measurable_gapKeys i))

theorem surv_measurable_certInt (eps : ℝ) (k i j : ℕ) {G' : ℝ → ℝ} (hG' : Measurable G') :
    Measurable (surv_certInt eps k i j G') := by
  unfold surv_certInt
  exact ((measurable_const.indicator (measurableSet_certOK eps k i j)).mul
    ((measurable_const.indicator measurableSet_Icc).comp (surv_measurable_certSlope eps i j))).mul
    (Complex.measurable_ofReal.comp (hG'.comp (rawAsm_measurable_gapKeys k)))

theorem surv_measurable_badInt (eps : ℝ) (k i j : ℕ) {G' : ℝ → ℝ} (hG' : Measurable G') :
    Measurable (surv_badInt eps k i j G') := by
  unfold surv_badInt
  exact ((measurable_const.indicator (measurableSet_certOK eps k i j)).mul
    ((measurable_const.indicator measurableSet_Icc.compl).comp
      (surv_measurable_certSlope eps i j))).mul
    (Complex.measurable_ofReal.comp (hG'.comp (rawAsm_measurable_gapKeys k)))

theorem surv_norm_indicator_one_le' {α : Type*} (s : Set α) (x : α) :
    ‖s.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
  by_cases h : x ∈ s
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

theorem surv_norm_certInt_le (eps : ℝ) (k i j : ℕ) (G' : ℝ → ℝ) (g : ℕ → ℝ) :
    ‖surv_certInt eps k i j G' g‖ ≤ |G' (gapKeys g k)| := by
  unfold surv_certInt
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖{g' : ℕ → ℝ | certOK eps (gapKeys g') k i j}.indicator (fun _ => (1 : ℂ)) g‖ ≤ 1 :=
    surv_norm_indicator_one_le' _ _
  have h2 : ‖(Icc (1 / 2 : ℝ) 2).indicator (fun _ => (1 : ℂ)) (certSlope eps (gapKeys g) i j)‖ ≤
      1 := surv_norm_indicator_one_le' _ _
  calc _ ≤ 1 * 1 * |G' (gapKeys g k)| :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) (abs_nonneg _)
    _ = |G' (gapKeys g k)| := by ring

theorem surv_norm_badInt_le (eps : ℝ) (k i j : ℕ) (G' : ℝ → ℝ) (g : ℕ → ℝ) :
    ‖surv_badInt eps k i j G' g‖ ≤ |G' (gapKeys g k)| := by
  unfold surv_badInt
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖{g' : ℕ → ℝ | certOK eps (gapKeys g') k i j}.indicator (fun _ => (1 : ℂ)) g‖ ≤ 1 :=
    surv_norm_indicator_one_le' _ _
  have h2 : ‖(Icc (1 / 2 : ℝ) 2)ᶜ.indicator (fun _ => (1 : ℂ)) (certSlope eps (gapKeys g) i j)‖ ≤
      1 := surv_norm_indicator_one_le' _ _
  calc _ ≤ 1 * 1 * |G' (gapKeys g k)| :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) (abs_nonneg _)
    _ = |G' (gapKeys g k)| := by ring

/-- Integrability of a functional dominated by `|G'(p_k)| ≤ e^{γ' p_k}` under a word law. -/
theorem surv_integrable_of_le_Gpos (ν σ : ProbabilityMeasure ℝ) (S : Finset ℕ) {k : ℕ}
    {G' : ℝ → ℝ} {γ' : ℝ} (hGb : ∀ y, |G' y| ≤ Real.exp (γ' * y))
    (hint : Integrable (fun g => Real.exp (γ' * gapKeys g k)) (wordLaw ν σ S)) {H : (ℕ → ℝ) → ℂ}
    (hH : Measurable H) (hle : ∀ g, ‖H g‖ ≤ |G' (gapKeys g k)|) : Integrable H (wordLaw ν σ S) :=
  hint.mono' hH.aestronglyMeasurable (Filter.Eventually.of_forall fun g =>
    (hle g).trans (hGb _))

/-! ## Bad slopes force a large deviation of the last key -/

/-- The event `{p_k ≥ 3k/2 ∨ p_k ≤ 5k/8}`. -/
def surv_ld (k : ℕ) : Set (ℕ → ℝ) :=
  {g | 3 * k / 2 ≤ gapKeys g k ∨ gapKeys g k ≤ 5 * k / 8}

theorem surv_measurableSet_ld (k : ℕ) : MeasurableSet (surv_ld k) :=
  (measurableSet_le measurable_const (rawAsm_measurable_gapKeys k)).union
    (measurableSet_le (rawAsm_measurable_gapKeys k) measurable_const)

/-- **A bad-slope certificate forces `p_k ≥ 3k/2` or `p_k ≤ 5k/8`** when `8ε ≤ k`. -/
theorem surv_bad_slope_ld {eps : ℝ} {k i j : ℕ} (hk : 8 * eps ≤ k) (_heps : 0 ≤ eps)
    {g : ℕ → ℝ} (hg : ∀ l, 0 < g l) (hij : i < j) (hL : 2 * eps < (j : ℝ) - i)
    (hok : certOK eps (gapKeys g) k i j) (ha : certSlope eps (gapKeys g) i j ∉ Icc (1 / 2 : ℝ) 2) :
    g ∈ surv_ld k := by
  have habs := cert_abs_sub_le_of_band (gapKeys_zero g) hok
  rw [abs_le] at habs
  have hp : 0 ≤ gapKeys g k := Finset.sum_nonneg fun l _ => (hg l).le
  have hpij : gapKeys g i < gapKeys g j := cert_gapKeys_lt (k := j) (fun l _ => hg l) i j hij le_rfl
  have ha0 : 0 < certSlope eps (gapKeys g) i j := by
    unfold certSlope
    exact div_pos (by linarith) (by linarith)
  simp only [Set.mem_Icc, not_and_or, not_le] at ha
  show 3 * k / 2 ≤ gapKeys g k ∨ gapKeys g k ≤ 5 * k / 8
  rcases ha with ha | ha
  · left
    have h1 := mul_le_mul_of_nonneg_right ha.le hp
    linarith [habs.2]
  · right
    have h1 := mul_le_mul_of_nonneg_right ha.le hp
    linarith [habs.1]

/-- **The bad parts of all certificates**: a.e. at most one certificate holds, and its slope is
bad only on the large-deviation event. -/
theorem surv_norm_badSum_le {eps : ℝ} {k : ℕ} (hk : 8 * eps ≤ k) (heps : 0 ≤ eps) {G' : ℝ → ℝ}
    {γ' : ℝ} (hGb : ∀ y, |G' y| ≤ Real.exp (γ' * y)) {g : ℕ → ℝ} (hg : ∀ l, 0 < g l)
    (huniq : ∀ ij ∈ certPairs eps k, ∀ ij' ∈ certPairs eps k,
      certOK eps (gapKeys g) k ij.1 ij.2 → certOK eps (gapKeys g) k ij'.1 ij'.2 → ij = ij') :
    ‖∑ ij ∈ certPairs eps k, surv_badInt eps k ij.1 ij.2 G' g‖ ≤
      (surv_ld k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g := by
  have hnn : 0 ≤ (surv_ld k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g :=
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) g
  have hzero : ∀ ij : ℕ × ℕ, ¬ certOK eps (gapKeys g) k ij.1 ij.2 →
      surv_badInt eps k ij.1 ij.2 G' g = 0 := by
    intro ij hok
    unfold surv_badInt
    rw [indicator_of_notMem (show g ∉ {g' : ℕ → ℝ | certOK eps (gapKeys g') k ij.1 ij.2} from hok)]
    simp
  by_cases hex : ∃ ij ∈ certPairs eps k, certOK eps (gapKeys g) k ij.1 ij.2
  · obtain ⟨ij, hmem, hok⟩ := hex
    rw [Finset.sum_eq_single_of_mem ij hmem fun ij' hmem' hne =>
      hzero ij' fun hok' => hne (huniq ij' hmem' ij hmem hok' hok)]
    by_cases ha : certSlope eps (gapKeys g) ij.1 ij.2 ∈ Icc (1 / 2 : ℝ) 2
    · unfold surv_badInt
      rw [indicator_of_notMem (show certSlope eps (gapKeys g) ij.1 ij.2 ∉ (Icc (1 / 2 : ℝ) 2)ᶜ
        from fun h => h ha)]
      simpa using hnn
    · obtain ⟨hij, -, hL⟩ := mem_certPairs.1 hmem
      have hld := surv_bad_slope_ld hk heps hg hij hL hok ha
      rw [Set.indicator_of_mem hld]
      exact (surv_norm_badInt_le eps k ij.1 ij.2 G' g).trans (hGb _)
  · push Not at hex
    rw [Finset.sum_eq_zero fun ij hmem => hzero ij (hex ij hmem), norm_zero]
    exact hnn

theorem surv_depPrefix_ld (k : ℕ) (γ' : ℝ) :
    DepPrefix k (fun g => (surv_ld k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g) := by
  intro g g' hgg
  have hkeys : gapKeys g k = gapKeys g' k :=
    Finset.sum_congr rfl fun s hs => hgg s (Finset.mem_range.1 hs)
  simp only [surv_ld, Set.indicator_apply, Set.mem_ofPred_eq, hkeys]

/-! ## The long-segment bound -/

/-- The good-slope bound of one certificate `(i, j)` (`surv_good_bound`). -/
def surv_goodB (eps : ℝ) (z : ℂ) (D E : ℝ) (RB : ℕ → ℝ) (k i j : ℕ) : ℝ :=
  E * RB (k - j) * RB i * (∑ m ∈ Finset.range (j - i),
    ‖1 - z‖ * ‖z‖ ^ (j - i - 1 - m) * (3 * (((j - i : ℕ) : ℝ) - 2 * eps) / 2 * (D * RB m)) +
      ‖z‖ ^ (j - i))

/-- **The long-segment bound** (`1 ≤ ε`, `8ε ≤ k`).  With `G' = 1_{[0,∞)} G`,
`E = e^{2γ'(k+2ε)}`, `ρ̃ = mixPM ν σ (surv_tz z)` and `κ = surv_rate θ₁ B₁`,
`‖cSurv ε ν σ z k G‖ ≤ ∑_{(i,j) ∈ certPairs} goodB(i,j) + (‖1-z‖ + ‖z‖)^k · 3 e^{-κ k}`. -/
theorem surv_long_bound (ν σ : ProbabilityMeasure ℝ) (z : ℂ) {eps : ℝ} (heps : 1 ≤ eps) {k : ℕ}
    (hk : 8 * eps ≤ k) (hνac : (ν : Measure ℝ) ≪ volume) (hσac : (σ : Measure ℝ) ≪ volume)
    (hνpos : (ν : Measure ℝ) (Iic 0) = 0) (hσpos : (σ : Measure ℝ) (Iic 0) = 0) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hD : 0 < D) (hfD : ∀ x, f x ≤ D)
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) {G : ℝ → ℝ}
    (hG : Measurable G) {γ' : ℝ} (hγ0 : 0 ≤ γ') (hGb : ∀ y, 0 ≤ y → |G y| ≤ Real.exp (γ' * y))
    (hint : ∀ S, Integrable (fun g => Real.exp (γ' * gapKeys g k)) (wordLaw ν σ S))
    {RB : ℕ → ℝ} (hRBpos : ∀ n, 0 < RB n)
    (hRB : ∀ β a' : ℝ, 1 / 2 ≤ |a'| → ∀ n : ℕ, ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      ∀ y, ‖kRow (surv_J eps) ν σ z β a' n φ y‖ ≤ RB n) {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁)
    (hmix : (mixPM ν σ (surv_tz z) : Measure ℝ) (Iic 0) = 0 ∧ lawMean (mixPM ν σ (surv_tz z)) = 1 ∧
      ExpMom θ₁ B₁ (mixPM ν σ (surv_tz z)))
    (hγκ : γ' ≤ surv_rate θ₁ B₁ / 8) :
    ‖cSurv eps ν σ z k G‖ ≤
      (∑ ij ∈ certPairs eps k, surv_goodB eps z D (Real.exp (γ' * (2 * (k + 2 * eps)))) RB k
        ij.1 ij.2) + (‖1 - z‖ + ‖z‖) ^ k * (3 * Real.exp (-(surv_rate θ₁ B₁ * k))) := by
  have heps0 : 0 ≤ eps := by linarith
  have hk2 : 2 * eps < k := by linarith
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  set G' := surv_Gpos G with hG'def
  have hG'm : Measurable G' := surv_measurable_Gpos hG
  have hG'b : ∀ y, |G' y| ≤ Real.exp (γ' * y) := surv_abs_Gpos_le hGb
  set E := Real.exp (γ' * (2 * (k + 2 * eps))) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hGE : ∀ y, y ≤ 2 * (k + 2 * eps) → |G' y| ≤ E := fun y hy =>
    surv_abs_Gpos_le_of_le hγ0 hGb y hy
  have hintG : ∀ S, Integrable (fun g => (G' (gapKeys g k) : ℂ)) (wordLaw ν σ S) := fun S =>
    surv_integrable_of_le_Gpos ν σ S hG'b (hint S)
      (Complex.measurable_ofReal.comp (hG'm.comp (rawAsm_measurable_gapKeys k)))
      (fun g => by rw [Complex.norm_real, Real.norm_eq_abs])
  -- step 1: `cSurv` as a word functional of the restricted test
  rw [surv_cSurv_eq_wint]
  have e1 : surv_wint ν σ z k
      (fun g => (((survSet eps k).indicator (fun g => G (gapKeys g k)) g : ℝ) : ℂ)) =
      surv_wint ν σ z k
        (fun g => (((survSet eps k).indicator (fun g => G' (gapKeys g k)) g : ℝ) : ℂ)) :=
    surv_wint_congr ν σ z k fun S _ => (cert_ae_pos_wordLaw hνpos hσpos S).mono fun g hg => by
      rw [surv_survInd_eq_Gpos eps k G hg]
  rw [e1, surv_wint_survInd_eq_certSum ν σ z hk2 hνac hσac hνpos hσpos G' hintG]
  -- step 2: split each certificate into good and bad slopes
  have e2 : ∀ ij ∈ certPairs eps k, surv_wint ν σ z k (fun g =>
      {g' : ℕ → ℝ | certOK eps (gapKeys g') k ij.1 ij.2}.indicator
        (fun g => (G' (gapKeys g k) : ℂ)) g) =
      surv_wint ν σ z k (surv_certInt eps k ij.1 ij.2 G') +
        surv_wint ν σ z k (surv_badInt eps k ij.1 ij.2 G') := by
    intro ij _
    rw [← surv_wint_add ν σ z k (fun S => surv_integrable_of_le_Gpos ν σ S hG'b (hint S)
        (surv_measurable_certInt eps k ij.1 ij.2 hG'm) (surv_norm_certInt_le eps k ij.1 ij.2 G'))
      (fun S => surv_integrable_of_le_Gpos ν σ S hG'b (hint S)
        (surv_measurable_badInt eps k ij.1 ij.2 hG'm) (surv_norm_badInt_le eps k ij.1 ij.2 G'))]
    refine surv_wint_congr ν σ z k fun S _ => Filter.Eventually.of_forall fun g => ?_
    exact surv_certInd_eq_good_add_bad eps k ij.1 ij.2 G' g
  rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  -- step 3: the good slopes
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ij hmem => ?_)
    obtain ⟨hij, hjk, hL⟩ := mem_certPairs.1 hmem
    have hL' : ij.1 + (ij.2 - ij.1) = ij.2 := by omega
    have hLε : 2 * eps < ((ij.2 - ij.1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hij.le]
      exact hL
    exact surv_good_bound ν σ z heps0 hij hL' hjk hLε hνpos hσpos hf hf0 hD hfD hνf hG'm hE hGE
      hRBpos hRB
  -- step 4: the bad slopes through the positive mixture
  · rw [← surv_wint_finsetSum ν σ z k _ fun ij _ S => surv_integrable_of_le_Gpos ν σ S hG'b
      (hint S) (surv_measurable_badInt eps k ij.1 ij.2 hG'm) (surv_norm_badInt_le eps k ij.1 ij.2 G')]
    have hH'm : Measurable fun g => (surv_ld k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g :=
      (((rawAsm_measurable_gapKeys k).const_mul γ').exp).indicator (surv_measurableSet_ld k)
    have hH'int : ∀ S, Integrable
        (fun g => (surv_ld k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g) (wordLaw ν σ S) :=
      fun S => (hint S).indicator (surv_measurableSet_ld k)
    have hle : ∀ S, ∀ᵐ g ∂(wordLaw ν σ S), ‖∑ ij ∈ certPairs eps k,
        surv_badInt eps k ij.1 ij.2 G' g‖ ≤
          (surv_ld k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g := fun S => by
      filter_upwards [cert_ae_pos_wordLaw hνpos hσpos S,
        cert_ae_certOK_unique hνac hσac hνpos hσpos S eps k] with g hg huniq
      exact surv_norm_badSum_le hk heps0 hG'b hg huniq
    refine (surv_norm_wint_le_mix ν σ z k hH'm (surv_depPrefix_ld k γ') hH'int hle).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    obtain ⟨hpos, hmean, hexp⟩ := hmix
    exact surv_bad_integral_le hθ₁ hpos hmean hexp hk1 hγ0 hγκ

end

end PGM
