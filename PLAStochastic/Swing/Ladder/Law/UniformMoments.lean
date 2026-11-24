import PLAStochastic.Swing.Ladder.Law.UniformBounds

/-! # Uniformly bounded ladder-height moments on a compact drift interval

The compact exponential tail of `GaussianAscendingLadderTail` is turned into an
integer-grid exponential tail for the excess `(H_a - M)_+`.  Every fixed
polynomial moment of `H_a` is then finite with a bound depending only on
`δ`, `M` and the order, not on the drift `a ∈ [δ,M]`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The part of the ladder height above the drift bound. -/
def gaussianAscendingLadderExcess (X : ℕ → Ω → ℝ) (a M : ℝ) (ω : Ω) : ℝ :=
  max (gaussianAscendingLadderHeight X a ω - M) 0

omit [MeasurableSpace Ω] in
theorem gaussianAscendingLadderExcess_nonneg (X : ℕ → Ω → ℝ) (a M : ℝ) (ω : Ω) :
    0 ≤ gaussianAscendingLadderExcess X a M ω := le_max_right _ _

theorem gaussianAscendingLadderExcess_measurable
    (hX : ∀ n, Measurable (X n)) (a M : ℝ) :
    Measurable (gaussianAscendingLadderExcess X a M) :=
  (((gaussianAscendingLadderHeight_measurable hX a).sub measurable_const).max measurable_const)

/-- The uniform excess tail constant. -/
def gaussianAscendingLadderExcessConstant (δ : ℝ) : ℝ :=
  3 * Real.exp (gaussianAscendingLadderTailRate δ)

theorem gaussianAscendingLadderExcessConstant_nonneg (δ : ℝ) :
    0 ≤ gaussianAscendingLadderExcessConstant δ := by
  unfold gaussianAscendingLadderExcessConstant
  positivity

/-- An integer-grid exponential tail for the ladder excess, with constants
depending only on the compact drift interval. -/
theorem gaussianAscendingLadderExcess_integer_expTail
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) (n : ℕ) :
    μ {ω | (n : ℝ) ≤ gaussianAscendingLadderExcess X a M ω} ≤
      ENNReal.ofReal (gaussianAscendingLadderExcessConstant δ *
        Real.exp (-gaussianAscendingLadderTailRate δ * (n : ℝ))) := by
  have := hi.isProbabilityMeasure
  set r : ℝ := gaussianAscendingLadderTailRate δ with hrdef
  have hr : 0 < r := gaussianAscendingLadderTailRate_pos hδ
  set C : ℝ := gaussianAscendingLadderExcessConstant δ with hCdef
  have hC : C = 3 * Real.exp r := by rw [hCdef, gaussianAscendingLadderExcessConstant, hrdef]
  by_cases hn0 : n ≤ 1
  · have hprob : μ {ω | (n : ℝ) ≤ gaussianAscendingLadderExcess X a M ω} ≤ 1 := by
      calc μ {ω | (n : ℝ) ≤ gaussianAscendingLadderExcess X a M ω} ≤ μ univ :=
            measure_mono (subset_univ _)
        _ = 1 := by simp
    have hnR : (n : ℝ) ≤ 1 := by exact_mod_cast hn0
    have hge : (1 : ℝ) ≤ C * Real.exp (-r * (n : ℝ)) := by
      rw [hC, mul_assoc, ← Real.exp_add]
      have harg : 0 ≤ r + -r * (n : ℝ) := by nlinarith
      nlinarith [Real.one_le_exp harg]
    exact hprob.trans (by simpa using ENNReal.ofReal_le_ofReal hge)
  · have hn2 : 2 ≤ n := by omega
    have hsubset : {ω | (n : ℝ) ≤ gaussianAscendingLadderExcess X a M ω} ⊆
        {ω | M + ((n-1 : ℕ) : ℝ) < gaussianAscendingLadderHeight X a ω} := by
      intro ω hω
      have hω' : (n : ℝ) ≤ max (gaussianAscendingLadderHeight X a ω - M) 0 := hω
      have hpos : 0 < (n : ℝ) := by
        have : 0 < n := by omega
        exact_mod_cast this
      have hsub : (n : ℝ) ≤ gaussianAscendingLadderHeight X a ω - M := by
        by_contra hnot
        have hlt : gaussianAscendingLadderHeight X a ω - M < (n : ℝ) := lt_of_not_ge hnot
        have hmax : max (gaussianAscendingLadderHeight X a ω - M) 0 < (n : ℝ) :=
          max_lt_iff.mpr ⟨hlt, hpos⟩
        linarith
      have hcast : ((n-1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) (m := 1) (n := n) (by omega)]
        norm_num
      show M + ((n-1 : ℕ) : ℝ) < gaussianAscendingLadderHeight X a ω
      rw [hcast]
      linarith
    have hreal := (measureReal_mono hsubset).trans
      (gaussianAscendingLadderHeight_compact_tail hX hi hG hδ hδa haM
        (N := n-1) (by omega))
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    refine ENNReal.ofReal_le_ofReal (hreal.trans (le_of_eq ?_))
    rw [hC, show ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 by
      rw [Nat.cast_sub (R := ℝ) (m := 1) (n := n) (by omega)]; norm_num,
      mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    simp only [hrdef]
    ring

theorem gaussianAscendingLadderExcess_pow_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) (k : ℕ) :
    Integrable (fun ω => gaussianAscendingLadderExcess X a M ω ^ k) μ :=
  integrable_pow_of_expTail (gaussianAscendingLadderExcess_measurable hX a M)
    (ae_of_all _ (gaussianAscendingLadderExcess_nonneg X a M))
    (gaussianAscendingLadderExcessConstant_nonneg δ)
    (gaussianAscendingLadderTailRate_pos hδ)
    (gaussianAscendingLadderExcess_integer_expTail hX hi hG hδ hδa haM) k

theorem gaussianAscendingLadderExcess_pow_integral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) (k : ℕ) :
    (∫ ω, gaussianAscendingLadderExcess X a M ω ^ k ∂μ) ≤
      gaussianAscendingLadderExcessConstant δ *
        expTailMomentSum (gaussianAscendingLadderTailRate δ) k :=
  integral_pow_le_of_expTail (gaussianAscendingLadderExcess_measurable hX a M)
    (ae_of_all _ (gaussianAscendingLadderExcess_nonneg X a M))
    (gaussianAscendingLadderExcessConstant_nonneg δ)
    (gaussianAscendingLadderTailRate_pos hδ)
    (gaussianAscendingLadderExcess_integer_expTail hX hi hG hδ hδa haM) k

/-- The explicit uniform bound on every fixed ladder-height moment. -/
def gaussianAscendingLadderMomentBound (δ M : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ)^k * (M^k + gaussianAscendingLadderExcessConstant δ *
    expTailMomentSum (gaussianAscendingLadderTailRate δ) k)

theorem gaussianAscendingLadderHeight_pow_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) (k : ℕ) :
    Integrable (fun ω => gaussianAscendingLadderHeight X a ω ^ k) μ := by
  have := hi.isProbabilityMeasure
  have hM : 0 ≤ M := (hδ.le.trans hδa).trans haM
  have hYint := gaussianAscendingLadderExcess_pow_integrable hX hi hG hδ hδa haM k
  have hmajor : Integrable
      (fun ω => (2 : ℝ)^k * (M^k + gaussianAscendingLadderExcess X a M ω ^ k)) μ :=
    (((integrable_const (M^k)).add hYint)).const_mul _
  refine hmajor.mono'
    (((gaussianAscendingLadderHeight_measurable hX a).pow_const k).aestronglyMeasurable) ?_
  filter_upwards with ω
  have hH : 0 ≤ gaussianAscendingLadderHeight X a ω :=
    gaussianAscendingLadderHeight_nonneg (X := X) a ω
  have hY : 0 ≤ gaussianAscendingLadderExcess X a M ω :=
    gaussianAscendingLadderExcess_nonneg X a M ω
  have hle : gaussianAscendingLadderHeight X a ω ≤ M + gaussianAscendingLadderExcess X a M ω := by
    unfold gaussianAscendingLadderExcess
    rcases le_total (gaussianAscendingLadderHeight X a ω) M with h | h
    · rw [max_eq_right (by linarith)]
      linarith
    · rw [max_eq_left (by linarith)]
      linarith
  have hmax : M + gaussianAscendingLadderExcess X a M ω ≤
      2 * max M (gaussianAscendingLadderExcess X a M ω) := by
    have h1 : M ≤ max M (gaussianAscendingLadderExcess X a M ω) := le_max_left _ _
    have h2 : gaussianAscendingLadderExcess X a M ω ≤
        max M (gaussianAscendingLadderExcess X a M ω) := le_max_right _ _
    linarith
  have hpow : gaussianAscendingLadderHeight X a ω ^ k ≤
      (2 * max M (gaussianAscendingLadderExcess X a M ω))^k :=
    pow_le_pow_left₀ hH (hle.trans hmax) k
  have hmaxpow : (max M (gaussianAscendingLadderExcess X a M ω))^k ≤
      M^k + gaussianAscendingLadderExcess X a M ω ^ k := by
    rcases max_cases M (gaussianAscendingLadderExcess X a M ω) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · have : 0 ≤ gaussianAscendingLadderExcess X a M ω ^ k := pow_nonneg hY k
      linarith
    · have : 0 ≤ M^k := pow_nonneg hM k
      linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hH k)]
  calc gaussianAscendingLadderHeight X a ω ^ k
      ≤ (2 * max M (gaussianAscendingLadderExcess X a M ω))^k := hpow
    _ = (2 : ℝ)^k * (max M (gaussianAscendingLadderExcess X a M ω))^k := by rw [mul_pow]
    _ ≤ (2 : ℝ)^k * (M^k + gaussianAscendingLadderExcess X a M ω ^ k) :=
        mul_le_mul_of_nonneg_left hmaxpow (by positivity)

/-- Uniformly bounded ladder-height moments over `δ ≤ a ≤ M`. -/
theorem gaussianAscendingLadderHeight_pow_integral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) (k : ℕ) :
    (∫ ω, gaussianAscendingLadderHeight X a ω ^ k ∂μ) ≤
      gaussianAscendingLadderMomentBound δ M k := by
  have := hi.isProbabilityMeasure
  have hM : 0 ≤ M := (hδ.le.trans hδa).trans haM
  have hYint := gaussianAscendingLadderExcess_pow_integrable hX hi hG hδ hδa haM k
  have hHint := gaussianAscendingLadderHeight_pow_integrable hX hi hG hδ hδa haM k
  have hmajor : Integrable
      (fun ω => (2 : ℝ)^k * (M^k + gaussianAscendingLadderExcess X a M ω ^ k)) μ :=
    (((integrable_const (M^k)).add hYint)).const_mul _
  have hpoint : ∀ ω, gaussianAscendingLadderHeight X a ω ^ k ≤
      (2 : ℝ)^k * (M^k + gaussianAscendingLadderExcess X a M ω ^ k) := by
    intro ω
    have hH : 0 ≤ gaussianAscendingLadderHeight X a ω :=
      gaussianAscendingLadderHeight_nonneg (X := X) a ω
    have hY : 0 ≤ gaussianAscendingLadderExcess X a M ω :=
      gaussianAscendingLadderExcess_nonneg X a M ω
    have hle : gaussianAscendingLadderHeight X a ω ≤
        M + gaussianAscendingLadderExcess X a M ω := by
      unfold gaussianAscendingLadderExcess
      rcases le_total (gaussianAscendingLadderHeight X a ω) M with h | h
      · rw [max_eq_right (by linarith)]; linarith
      · rw [max_eq_left (by linarith)]; linarith
    have hmax : M + gaussianAscendingLadderExcess X a M ω ≤
        2 * max M (gaussianAscendingLadderExcess X a M ω) := by
      have h1 : M ≤ max M (gaussianAscendingLadderExcess X a M ω) := le_max_left _ _
      have h2 : gaussianAscendingLadderExcess X a M ω ≤
          max M (gaussianAscendingLadderExcess X a M ω) := le_max_right _ _
      linarith
    have hmaxpow : (max M (gaussianAscendingLadderExcess X a M ω))^k ≤
        M^k + gaussianAscendingLadderExcess X a M ω ^ k := by
      rcases max_cases M (gaussianAscendingLadderExcess X a M ω) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
      · have : 0 ≤ gaussianAscendingLadderExcess X a M ω ^ k := pow_nonneg hY k
        linarith
      · have : 0 ≤ M^k := pow_nonneg hM k
        linarith
    calc gaussianAscendingLadderHeight X a ω ^ k
        ≤ (2 * max M (gaussianAscendingLadderExcess X a M ω))^k :=
          pow_le_pow_left₀ hH (hle.trans hmax) k
      _ = (2 : ℝ)^k * (max M (gaussianAscendingLadderExcess X a M ω))^k := by rw [mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmaxpow (by positivity)
  have hmono := integral_mono hHint hmajor hpoint
  refine hmono.trans ?_
  rw [integral_const_mul, integral_add (integrable_const (M^k)) hYint, integral_const,
    gaussianAscendingLadderMomentBound]
  rw [show μ.real univ = 1 by simp, one_smul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hY := gaussianAscendingLadderExcess_pow_integral_le hX hi hG hδ hδa haM k
  linarith

/-! ### Uniform exponential moments

The renewal expansion quoted in `app:limit` needs a finite exponential moment
uniform over the family.  The same integer-grid tail supplies it for every
order strictly below the tail rate.
-/

/-- The explicit uniform bound on the ladder exponential moment. -/
def gaussianAscendingLadderExpMomentBound (δ M θ : ℝ) : ℝ :=
  Real.exp (θ*M) * (gaussianAscendingLadderExcessConstant δ *
    expTailExpMomentSum (gaussianAscendingLadderTailRate δ) θ)

theorem gaussianAscendingLadderExcess_exp_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a θ : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    (hθ : 0 ≤ θ) (hθr : θ < gaussianAscendingLadderTailRate δ) :
    Integrable (fun ω => Real.exp (θ*gaussianAscendingLadderExcess X a M ω)) μ :=
  integrable_exp_of_expTail (gaussianAscendingLadderExcess_measurable hX a M)
    (ae_of_all _ (gaussianAscendingLadderExcess_nonneg X a M))
    (gaussianAscendingLadderExcessConstant_nonneg δ) hθ hθr
    (gaussianAscendingLadderExcess_integer_expTail hX hi hG hδ hδa haM)

theorem gaussianAscendingLadderExcess_exp_integral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a θ : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    (hθ : 0 ≤ θ) (hθr : θ < gaussianAscendingLadderTailRate δ) :
    (∫ ω, Real.exp (θ*gaussianAscendingLadderExcess X a M ω) ∂μ) ≤
      gaussianAscendingLadderExcessConstant δ *
        expTailExpMomentSum (gaussianAscendingLadderTailRate δ) θ :=
  integral_exp_le_of_expTail (gaussianAscendingLadderExcess_measurable hX a M)
    (ae_of_all _ (gaussianAscendingLadderExcess_nonneg X a M))
    (gaussianAscendingLadderExcessConstant_nonneg δ) hθ hθr
    (gaussianAscendingLadderExcess_integer_expTail hX hi hG hδ hδa haM)

omit [MeasurableSpace Ω] in
theorem gaussianAscendingLadderHeight_le_excess (X : ℕ → Ω → ℝ) {a M : ℝ} (ω : Ω) :
    gaussianAscendingLadderHeight X a ω ≤ M + gaussianAscendingLadderExcess X a M ω := by
  unfold gaussianAscendingLadderExcess
  rcases le_total (gaussianAscendingLadderHeight X a ω) M with h | h
  · rw [max_eq_right (by linarith)]
    linarith
  · rw [max_eq_left (by linarith)]
    linarith

theorem gaussianAscendingLadderHeight_exp_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a θ : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    (hθ : 0 ≤ θ) (hθr : θ < gaussianAscendingLadderTailRate δ) :
    Integrable (fun ω => Real.exp (θ*gaussianAscendingLadderHeight X a ω)) μ := by
  have := hi.isProbabilityMeasure
  have hYint := gaussianAscendingLadderExcess_exp_integrable hX hi hG hδ hδa haM hθ hθr
  have hmajor : Integrable
      (fun ω => Real.exp (θ*M)*Real.exp (θ*gaussianAscendingLadderExcess X a M ω)) μ :=
    hYint.const_mul _
  have hmeas : Measurable (fun ω => Real.exp (θ*gaussianAscendingLadderHeight X a ω)) :=
    Real.measurable_exp.comp (measurable_const.mul (gaussianAscendingLadderHeight_measurable hX a))
  refine hmajor.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hle := gaussianAscendingLadderHeight_le_excess (M := M) X (a := a) ω
  nlinarith

/-- A uniform exponential moment for the actual ladder heights: the bound holds
for every `δ ≤ a ≤ M` and every order below the tail rate. -/
theorem gaussianAscendingLadderHeight_exp_integral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a θ : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    (hθ : 0 ≤ θ) (hθr : θ < gaussianAscendingLadderTailRate δ) :
    (∫ ω, Real.exp (θ*gaussianAscendingLadderHeight X a ω) ∂μ) ≤
      gaussianAscendingLadderExpMomentBound δ M θ := by
  have := hi.isProbabilityMeasure
  have hYint := gaussianAscendingLadderExcess_exp_integrable hX hi hG hδ hδa haM hθ hθr
  have hHint := gaussianAscendingLadderHeight_exp_integrable hX hi hG hδ hδa haM hθ hθr
  have hmajor : Integrable
      (fun ω => Real.exp (θ*M)*Real.exp (θ*gaussianAscendingLadderExcess X a M ω)) μ :=
    hYint.const_mul _
  have hpoint : ∀ ω, Real.exp (θ*gaussianAscendingLadderHeight X a ω) ≤
      Real.exp (θ*M)*Real.exp (θ*gaussianAscendingLadderExcess X a M ω) := by
    intro ω
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hle := gaussianAscendingLadderHeight_le_excess (M := M) X (a := a) ω
    nlinarith
  have hmono := integral_mono hHint hmajor hpoint
  refine hmono.trans ?_
  rw [integral_const_mul, gaussianAscendingLadderExpMomentBound]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact gaussianAscendingLadderExcess_exp_integral_le hX hi hG hδ hδa haM hθ hθr

end SwingRepair
