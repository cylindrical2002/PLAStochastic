import PLAStochastic.Index.GEP.Kernel.Row.KilledTransition
import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.RegularClass

/-!
# WP4 kernel rows: Chapman–Kolmogorov, forward/reverse symmetry, and the bridge to the
complex row and its killed `L²` gap

Source: `influence-lipschitz.md` §3 (three-block form of pins and long rows).

* `krDens_add`: **pointwise** Chapman–Kolmogorov
  `krDens (m+1+(n+1)) y₀ z = ∫ krDens (m+1) y₀ y · krDens (n+1) y z dy` for every `y₀, z`;
* `krDens_symm`: `krDens β a (n+1) y₀ z = krDens (-β) (-a) (n+1) z y₀`, hence
  `integral_krDens_left`: `∫ krDens (n+1) y z dy = krSurv (-β) (-a) (n+1) z` (the reverse
  survival from the target point);
* `krDens_three_block`: `krDens (m+1+(j+1)+(k+1)) y₀ z = ∫∫ q_{m+1}(y₀,y) q_{j+1}(y,y') q_{k+1}(y',z)`;
* `kRow_zero_eq_krRow`: the complex row at `z = 0`, `σ = ν` is the coercion of the real row;
* `integral_krStep_sq_le_gap`, `integral_krRow_sq_le_gap_pow`: the killed `L²` contraction of
  the real step/row on `Icc α (α + w)` with the class-uniform gap
  `1 - killGapConst (killCnu D vlo vhi) (1/2) / w²` (from `integral_norm_kStepZ_sq_le_gap` and
  `kill_regLaw_charFun_gap`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {J : Set ℝ} {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-! ## Chapman–Kolmogorov -/

/-- **Pointwise Chapman–Kolmogorov.** -/
theorem krDens_add (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (m n : ℕ) (y₀ z : ℝ) :
    krDens J ν f β a (m + 1 + (n + 1)) y₀ z =
      ∫ y, krDens J ν f β a (m + 1) y₀ y * krDens J ν f β a (n + 1) y z := by
  have hD0 : 0 ≤ D / |a| := div_nonneg ((hf0 0).trans (hfD 0)) (abs_nonneg _)
  -- the tail integrand
  have hFm : Measurable (Function.uncurry fun (y : ℝ) (h : ℕ → ℝ) =>
      krAlive J β a n y h * krKer J f β a (kWalk y β a h n) z) :=
    (measurable_krAlive_prod hJ β a n).mul
      ((measurable_krKer_prod hJ hf β a).comp ((measurable_kWalk_prod β a n).prodMk
        measurable_const))
  have hFb : ∀ (y : ℝ) (h : ℕ → ℝ),
      |krAlive J β a n y h * krKer J f β a (kWalk y β a h n) z| ≤ D / |a| := by
    intro y h
    rw [abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
    calc _ ≤ 1 * (D / |a|) :=
          mul_le_mul (krAlive_le_one _ _ _) (abs_krKer_le hf0 hfD _ _) (abs_nonneg _) zero_le_one
      _ = D / |a| := one_mul _
  have e1 : m + 1 + (n + 1) = (m + 1 + n) + 1 := by omega
  rw [e1, krDens_succ]
  have e2 : ∀ g : ℕ → ℝ,
      krAlive J β a (m + 1 + n) y₀ g * krKer J f β a (kWalk y₀ β a g (m + 1 + n)) z =
      krAlive J β a (m + 1) y₀ g *
        (krAlive J β a n (kWalk y₀ β a g (m + 1)) (fun i => g (i + (m + 1))) *
          krKer J f β a (kWalk (kWalk y₀ β a g (m + 1)) β a (fun i => g (i + (m + 1))) n) z) := by
    intro g
    rw [krAlive_add (m + 1) n y₀ g, kWalk_add y₀ β a g (m + 1) n, mul_assoc]
  simp_rw [e2]
  rw [kr_integral_markov hJ ν β a (m + 1) hFm hFb y₀]
  simp_rw [← krDens_succ ν n]
  rw [← krRow_eq_integral hJ ν β a (m + 1) (measurable_krDens_left ν hJ hf β a (n + 1) z)
    (fun y => abs_krDens_le ν hf0 hfD (n + 1) y z) y₀]
  exact krRow_succ_eq_integral_krDens ν hJ hJfin hf hf0 hfD hν ha m
    (measurable_krDens_left ν hJ hf β a (n + 1) z) (fun y => abs_krDens_le ν hf0 hfD (n + 1) y z) y₀

/-- **Forward/reverse symmetry** of the density representative. -/
theorem krDens_symm (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (n : ℕ) (y₀ z : ℝ) :
    krDens J ν f β a (n + 1) y₀ z = krDens J ν f (-β) (-a) (n + 1) z y₀ := by
  induction n generalizing y₀ z with
  | zero => rw [krDens_one, krDens_one, krKer_symm]
  | succ n ih =>
    have ha' : -a ≠ 0 := neg_ne_zero.2 ha
    have e1 : n + 1 + 1 = 0 + 1 + (n + 1) := by omega
    have e2 : n + 1 + 1 = n + 1 + (0 + 1) := by omega
    conv_lhs => rw [e1, krDens_add ν hJ hJfin hf hf0 hfD hν ha 0 n y₀ z]
    conv_rhs => rw [e2, krDens_add ν hJ hJfin hf hf0 hfD hν ha' n 0 z y₀]
    congr 1
    funext y
    rw [krDens_one, krDens_one, ih, krKer_symm, mul_comm]

/-- The reverse mass identity: `∫ krDens (n+1) y z dy` is the reverse survival from `z`. -/
theorem integral_krDens_left (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (n : ℕ) (z : ℝ) :
    ∫ y, krDens J ν f β a (n + 1) y z = krSurv J (ν : Measure ℝ) (-β) (-a) (n + 1) z := by
  simp_rw [krDens_symm ν hJ hJfin hf hf0 hfD hν ha n _ z]
  exact integral_krDens ν hJ hJfin hf hf0 hfD hν (neg_ne_zero.2 ha) n z

/-- Three-block form of the density. -/
theorem krDens_three_block (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (m j k : ℕ) (y₀ z : ℝ) :
    krDens J ν f β a (m + 1 + (j + 1) + (k + 1)) y₀ z =
      ∫ y, krDens J ν f β a (m + 1) y₀ y *
        ∫ y', krDens J ν f β a (j + 1) y y' * krDens J ν f β a (k + 1) y' z := by
  have e : m + 1 + (j + 1) + (k + 1) = m + 1 + (j + 1 + k + 1) := by omega
  rw [e, krDens_add ν hJ hJfin hf hf0 hfD hν ha m (j + 1 + k) y₀ z]
  congr 1
  funext y
  rw [show j + 1 + k + 1 = j + 1 + (k + 1) by omega,
    krDens_add ν hJ hJfin hf hf0 hfD hν ha j k y z]

/-! ## The bridge to the complex row -/

theorem kStep_ofReal (ρ : Measure ℝ) (u : ℝ → ℝ) (y : ℝ) :
    kStep J ρ β a (fun x => (u x : ℂ)) y = (krStep J ρ β a u y : ℂ) := by
  unfold kStep krStep
  by_cases hy : y ∈ J
  · simp only [indicator_of_mem hy, integral_complex_ofReal]
  · simp only [indicator_of_notMem hy, Complex.ofReal_zero]

/-- The complex row at `z = 0` is the coercion of the real row (any `σ`). -/
theorem kRow_zero_eq_krRow (ρ σ : Measure ℝ) (n : ℕ) (φ : ℝ → ℝ) :
    kRow J ρ σ 0 β a n (fun x => (φ x : ℂ)) = fun y => (krRow J ρ β a n φ y : ℂ) := by
  induction n with
  | zero =>
    funext y
    simp only [kRow, krRow, Function.iterate_zero, id_eq]
    by_cases hy : y ∈ J
    · simp [indicator_of_mem hy]
    · simp [indicator_of_notMem hy]
  | succ n ih =>
    funext y
    have h1 : kRow J ρ σ 0 β a (n + 1) (fun x => (φ x : ℂ)) y =
        kStepZ J ρ σ 0 β a (kRow J ρ σ 0 β a n (fun x => (φ x : ℂ))) y := by
      simp only [kRow, Function.iterate_succ_apply']
    rw [h1, ih, krRow_succ]
    unfold kStepZ
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    exact kStep_ofReal ρ (krRow J ρ β a n φ) y

theorem kStepZ_zero_ofReal (ρ σ : Measure ℝ) (u : ℝ → ℝ) (y : ℝ) :
    kStepZ J ρ σ 0 β a (fun x => (u x : ℂ)) y = (krStep J ρ β a u y : ℂ) := by
  unfold kStepZ
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  exact kStep_ofReal ρ u y

/-! ## The killed `L²` gap of the real step -/

/-- The class-uniform charFun gap in the form used by `integral_norm_kStepZ_sq_le_gap`
(`z = 0`, `σ = ν`). -/
theorem kr_charFun_gap {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (t : ℝ) :
    ‖(1 - (0 : ℂ)) * charFun (ν : Measure ℝ) t + 0 * charFun (ν : Measure ℝ) t‖ ^ 2 ≤
      1 - killCnu D vlo vhi * min (t ^ 2) 1 := by
  have h := kill_regLaw_charFun_gap hD hθ hvlo hν (a := 1) (by norm_num) t
  simp only [one_mul] at h
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  linarith

/-- **Killed `L²` contraction of the real step** on `Icc α (α + w)`, class-uniform gap. -/
theorem integral_krStep_sq_le_gap {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) {α w : ℝ}
    (hw : 1 ≤ w) (ha : 1 / 2 ≤ |a|) {u : ℝ → ℝ} (hu : Measurable u)
    (hsupp : ∀ y, y ∉ Icc α (α + w) → u y = 0) (h2 : Integrable (fun y => u y ^ 2)) :
    ∫ y, krStep (Icc α (α + w)) (ν : Measure ℝ) β a u y ^ 2 ≤
      (1 - killGapConst (killCnu D vlo vhi) (1 / 2) / w ^ 2) * ∫ y, u y ^ 2 := by
  have hc : 0 < killCnu D vlo vhi := killCnu_pos hD hvlo hvhi
  have hu' : Measurable (fun x => (u x : ℂ)) := Complex.measurable_ofReal.comp hu
  have hsupp' : ∀ y, y ∉ Icc α (α + w) → (u y : ℂ) = 0 := fun y hy => by
    rw [hsupp y hy, Complex.ofReal_zero]
  have h2' : Integrable (fun y => ‖(u y : ℂ)‖ ^ 2) := by
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h := integral_norm_kStepZ_sq_le_gap (ν := (ν : Measure ℝ)) (σ := (ν : Measure ℝ))
    (z := 0) (β := β) (a := a) hw hc (by norm_num : (0 : ℝ) < 1 / 2) ha
    (kr_charFun_gap hD hθ hvlo hν) hu' hsupp' h2'
  have e1 : ∀ y, ‖kStepZ (Icc α (α + w)) (ν : Measure ℝ) (ν : Measure ℝ) 0 β a
      (fun x => (u x : ℂ)) y‖ ^ 2 = krStep (Icc α (α + w)) (ν : Measure ℝ) β a u y ^ 2 := by
    intro y
    rw [kStepZ_zero_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have e2 : ∀ y, ‖(u y : ℂ)‖ ^ 2 = u y ^ 2 := by
    intro y
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [e1, e2] at h
  exact h

/-- Rows are supported in `J` and bounded, hence square-integrable when `J` has finite measure. -/
theorem kr_integrable_sq_of_bdd {u : ℝ → ℝ} (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hu : Measurable u) (hsupp : ∀ y, y ∉ J → u y = 0) {M : ℝ} (hM : ∀ y, |u y| ≤ M) :
    Integrable (fun y => u y ^ 2) := by
  have hdom : Integrable (fun y => J.indicator (fun _ => M ^ 2) y) := by
    rw [integrable_indicator_iff hJ]
    exact integrableOn_const hJfin
  refine hdom.mono' (hu.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hy : y ∈ J
  · rw [indicator_of_mem hy, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM y) 2
  · rw [indicator_of_notMem hy, hsupp y hy]
    simp

/-- **Killed `L²` contraction of the real row**: `∫ (krRow n φ)² ≤ λⁿ ∫ (1_J φ)²`. -/
theorem integral_krRow_sq_le_gap_pow {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) {α w : ℝ}
    (hw : 1 ≤ w) (ha : 1 / 2 ≤ |a|) {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ y, |φ y| ≤ M) (n : ℕ) :
    ∫ y, krRow (Icc α (α + w)) (ν : Measure ℝ) β a n φ y ^ 2 ≤
      (1 - killGapConst (killCnu D vlo vhi) (1 / 2) / w ^ 2) ^ n *
        ∫ y, (Icc α (α + w)).indicator φ y ^ 2 := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  have hfin : volume (Icc α (α + w)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hlam0 : 0 ≤ 1 - killGapConst (killCnu D vlo vhi) (1 / 2) / w ^ 2 := by
    have hc : 0 < killCnu D vlo vhi := killCnu_pos hD hvlo hvhi
    have hcle : killCnu D vlo vhi ≤ 1 := by
      have h := kill_regLaw_charFun_gap hD hθ hvlo hν (a := 1) (by norm_num) 1
      have h0 : 0 ≤ ‖charFun (ν : Measure ℝ) (1 * 1)‖ ^ 2 := sq_nonneg _
      simp only [one_pow, min_self, mul_one] at h h0
      linarith
    have h1 : killGapConst (killCnu D vlo vhi) (1 / 2) ≤ 1 := by
      unfold killGapConst
      have hmin : min (Real.pi ^ 2 * (1 / 2) ^ 2 / 4) 1 ≤ 1 := min_le_right _ _
      have hmin0 : 0 ≤ min (Real.pi ^ 2 * (1 / 2) ^ 2 / 4) 1 := le_min (by positivity) zero_le_one
      calc killCnu D vlo vhi * min (Real.pi ^ 2 * (1 / 2) ^ 2 / 4) 1 / 2 ≤ 1 * 1 / 2 := by
            gcongr
        _ ≤ 1 := by norm_num
    have h2 : killGapConst (killCnu D vlo vhi) (1 / 2) / w ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact h1.trans (by nlinarith)
    linarith
  induction n with
  | zero => simp [krRow_zero]
  | succ n ih =>
    rw [krRow_succ, pow_succ]
    have hrow := integral_krStep_sq_le_gap hD hθ hvlo hvhi hν hw ha (β := β)
      (measurable_krRow measurableSet_Icc ν β a n hφ hM)
      (fun y hy => krRow_eq_zero_of_notMem hy)
      (kr_integrable_sq_of_bdd measurableSet_Icc hfin (measurable_krRow measurableSet_Icc ν β a n hφ hM)
        (fun y hy => krRow_eq_zero_of_notMem hy) (abs_krRow_le measurableSet_Icc ν β a n hφ hM))
    calc _ ≤ (1 - killGapConst (killCnu D vlo vhi) (1 / 2) / w ^ 2) *
          ∫ y, krRow (Icc α (α + w)) (ν : Measure ℝ) β a n φ y ^ 2 := hrow
      _ ≤ (1 - killGapConst (killCnu D vlo vhi) (1 / 2) / w ^ 2) *
          ((1 - killGapConst (killCnu D vlo vhi) (1 / 2) / w ^ 2) ^ n *
            ∫ y, (Icc α (α + w)).indicator φ y ^ 2) := mul_le_mul_of_nonneg_left ih hlam0
      _ = _ := by ring

end

end PGM
