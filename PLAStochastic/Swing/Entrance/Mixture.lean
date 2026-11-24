import PLAStochastic.Swing.Ladder.ZeroDrift.PairLaw

/-! # Integrals against the entrance mixture

Two ingredients of the entrance limit that do not involve the walk:

* `abs_integral_sub_mixture_le`: if on disjoint events `A` and `B` a random variable `R` is within
  `η` of `V` and of `W` respectively, outside a bad set, then for a bounded Lipschitz test `g`
  the mean `E g(R)` is within explicit errors of `P(A) a + P(B) b`, given how close
  `∫_A g(V)` is to `P(A) a` and `∫_B g(W)` to `P(B) b`;
* `integral_entranceLaw`: `∫ g dρ = θ ∫ g(-o) dπ + (1 - θ) ∫ g(-(u + o)) dπ` for the equilibrium
  pair law `π` of the zero-drift ladder height.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SwingRepair

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A pointwise bound `|F - G| ≤ η` on `A` outside a bad set, and `≤ 2C` on all of `A`, integrates
to `η P(A) + 2C P(A ∩ Bad)`. -/
theorem abs_setIntegral_sub_le [IsFiniteMeasure μ] {F G : Ω → ℝ} {A Bad : Set Ω}
    (hA : MeasurableSet A) (hF : IntegrableOn F A μ) (hG : IntegrableOn G A μ) {η C : ℝ}
    (hη : 0 ≤ η) (hFC : ∀ ω ∈ A, |F ω - G ω| ≤ 2 * C)
    (hgood : ∀ ω ∈ A, ω ∉ Bad → |F ω - G ω| ≤ η) :
    |∫ ω in A, F ω ∂μ - ∫ ω in A, G ω ∂μ| ≤ η * μ.real A + 2 * C * μ.real (A ∩ Bad) := by
  set B' := toMeasurable μ Bad
  have hB'm : MeasurableSet B' := measurableSet_toMeasurable μ Bad
  have hbound : ∀ ω ∈ A, |F ω - G ω| ≤ η + 2 * C * B'.indicator 1 ω := by
    intro ω hω
    by_cases hb : ω ∈ B'
    · rw [Set.indicator_of_mem hb, Pi.one_apply, mul_one]
      linarith [hFC ω hω]
    · rw [Set.indicator_of_notMem hb, mul_zero, add_zero]
      exact hgood ω hω fun h => hb (subset_toMeasurable μ Bad h)
  have hind : Integrable (fun ω => 2 * C * B'.indicator (1 : Ω → ℝ) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hB'm).const_mul (2 * C)
  have hint : IntegrableOn (fun ω => η + 2 * C * B'.indicator 1 ω) A μ :=
    ((integrable_const η).add hind).integrableOn
  have hmeas : μ.real (A ∩ B') = μ.real (A ∩ Bad) := by
    simp only [measureReal_def]
    rw [inter_comm, Measure.measure_toMeasurable_inter hA (measure_ne_top μ Bad), inter_comm]
  calc |∫ ω in A, F ω ∂μ - ∫ ω in A, G ω ∂μ| = |∫ ω in A, (F ω - G ω) ∂μ| := by
        rw [integral_sub hF hG]
    _ ≤ ∫ ω in A, |F ω - G ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω in A, (η + 2 * C * B'.indicator 1 ω) ∂μ :=
        setIntegral_mono_on (hF.sub hG).abs hint hA hbound
    _ = η * μ.real A + 2 * C * μ.real (A ∩ Bad) := by
        rw [integral_add (integrable_const η).integrableOn hind.integrableOn, setIntegral_const,
          integral_const_mul, setIntegral_indicator hB'm]
        simp only [Pi.one_apply]
        rw [setIntegral_const, hmeas]
        simp only [smul_eq_mul, mul_one]
        ring

/-- **Mixture bound.**  Let `A`, `B` be disjoint events on which `R` is within `η` of `V`,
respectively `W`, outside a bad set. For `|g| ≤ C` with `|g x - g y| ≤ L |x - y|`,
`|E g(R) - (P(A) a + P(B) b)|` is at most the errors of `∫_A g(V) ≈ P(A) a` and
`∫_B g(W) ≈ P(B) b`, plus `L η + 2C (P(A ∩ Bad) + P(B ∩ Bad)) + C (1 - P(A) - P(B))`. -/
theorem abs_integral_sub_mixture_le [IsProbabilityMeasure μ] {g : ℝ → ℝ} {C L : ℝ}
    (hg : Continuous g) (hgC : ∀ x, |g x| ≤ C) (hgL : ∀ x y, |g x - g y| ≤ L * |x - y|)
    (hL : 0 ≤ L) {R V W : Ω → ℝ} (hR : Measurable R) {A B Bad : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B)
    (hV : IntegrableOn (fun ω => g (V ω)) A μ) (hW : IntegrableOn (fun ω => g (W ω)) B μ)
    {η : ℝ} (hη : 0 ≤ η) (hAη : ∀ ω ∈ A, ω ∉ Bad → |R ω - V ω| ≤ η)
    (hBη : ∀ ω ∈ B, ω ∉ Bad → |R ω - W ω| ≤ η) (a b : ℝ) :
    |∫ ω, g (R ω) ∂μ - (μ.real A * a + μ.real B * b)| ≤
      |∫ ω in A, g (V ω) ∂μ - μ.real A * a| + |∫ ω in B, g (W ω) ∂μ - μ.real B * b| +
        L * η + 2 * C * (μ.real (A ∩ Bad) + μ.real (B ∩ Bad)) +
          C * (1 - μ.real A - μ.real B) := by
  have hF : Integrable (fun ω => g (R ω)) μ :=
    Integrable.of_bound (hg.measurable.comp hR).aestronglyMeasurable C
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgC _)
  have h2C : ∀ x y, |g x - g y| ≤ 2 * C := fun x y => by
    have := hgC x; have := hgC y
    calc |g x - g y| ≤ |g x| + |g y| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  have eA := abs_setIntegral_sub_le (Bad := Bad) hA hF.integrableOn hV (mul_nonneg hL hη)
    (fun ω _ => h2C _ _) fun ω hω hb =>
      (hgL _ _).trans (mul_le_mul_of_nonneg_left (hAη ω hω hb) hL)
  have eB := abs_setIntegral_sub_le (Bad := Bad) hB hF.integrableOn hW (mul_nonneg hL hη)
    (fun ω _ => h2C _ _) fun ω hω hb =>
      (hgL _ _).trans (mul_le_mul_of_nonneg_left (hBη ω hω hb) hL)
  have hrest : |∫ ω in (A ∪ B)ᶜ, g (R ω) ∂μ| ≤ C * μ.real (A ∪ B)ᶜ := by
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := (A ∪ B)ᶜ)
      (f := fun ω => g (R ω)) (measure_lt_top μ _) fun ω _ => by
        rw [Real.norm_eq_abs]; exact hgC _
    rwa [Real.norm_eq_abs] at this
  have hsplit : ∫ ω, g (R ω) ∂μ = ∫ ω in A, g (R ω) ∂μ + ∫ ω in B, g (R ω) ∂μ +
      ∫ ω in (A ∪ B)ᶜ, g (R ω) ∂μ := by
    rw [← setIntegral_union hAB hB hF.integrableOn hF.integrableOn,
      integral_add_compl (hA.union hB) hF]
  have hcompl : μ.real (A ∪ B)ᶜ = 1 - μ.real A - μ.real B := by
    rw [measureReal_compl (hA.union hB), measureReal_union hAB hB, probReal_univ]
    ring
  have hAB1 : μ.real A + μ.real B ≤ 1 := by
    rw [← measureReal_union hAB hB]; exact measureReal_le_one
  have hA0 : 0 ≤ μ.real A := measureReal_nonneg
  have hB0 : 0 ≤ μ.real B := measureReal_nonneg
  have hLη : L * η * μ.real A + L * η * μ.real B ≤ L * η := by
    have := mul_nonneg hL hη
    nlinarith
  rw [hsplit]
  rw [hcompl] at hrest
  have k1 := abs_le.mp eA
  have k2 := abs_le.mp eB
  have k3 := abs_le.mp hrest
  set x1 := ∫ ω in A, g (R ω) ∂μ
  set y1 := ∫ ω in A, g (V ω) ∂μ
  set x2 := ∫ ω in B, g (R ω) ∂μ
  set y2 := ∫ ω in B, g (W ω) ∂μ
  have j1 := abs_le.mp (le_refl |y1 - μ.real A * a|)
  have j2 := abs_le.mp (le_refl |y2 - μ.real B * b|)
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg (y1 - μ.real A * a), abs_nonneg (y2 - μ.real B * b),
    le_abs_self (y1 - μ.real A * a), neg_abs_le (y1 - μ.real A * a),
    le_abs_self (y2 - μ.real B * b), neg_abs_le (y2 - μ.real B * b)]

variable {X : ℕ → Ω → ℝ}

/-- **Integrals against the entrance law.**  For a bounded continuous `g`,
`∫ g dρ = θ ∫ g(-o) dπ + (1 - θ) ∫ g(-(u + o)) dπ`. -/
theorem integral_entranceLaw (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) :
    ∫ x, g x ∂(entranceLaw X μ) =
      entranceSelectionProb *
          ∫ p, g (-p.2) ∂(equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0)) +
        (1 - entranceSelectionProb) *
          ∫ p, g (-(p.1 + p.2)) ∂(equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0)) := by
  set ν₀ := gaussianAscendingLadderLaw X μ 0
  have hQ := gaussianZeroLadder_equilibrium_isProbabilityMeasure hX hi hG
  have hS := gaussianZeroLadder_sizeBiased_isProbabilityMeasure hX hi hG
  have hbdd : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν], Integrable g ν := fun ν _ =>
    Integrable.of_bound hg.aestronglyMeasurable C
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hgC x)
  have hθ0 := entranceSelectionProb_nonneg
  have hθ1 := entranceSelectionProb_le_one
  rw [entranceLaw, integral_add_measure ((hbdd _).smul_measure ENNReal.ofReal_ne_top)
      ((hbdd _).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hθ0, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul,
    integral_map measurable_neg.aemeasurable hg.aestronglyMeasurable,
    integral_map measurable_neg.aemeasurable hg.aestronglyMeasurable,
    ← gaussianZeroLadder_pair_map_snd hX hi hG, ← gaussianZeroLadder_pair_map_add X μ,
    integral_map measurable_snd.aemeasurable
      (show Continuous fun x : ℝ => g (-x) from hg.comp continuous_neg).aestronglyMeasurable,
    integral_map (show Measurable fun p : ℝ × ℝ => p.1 + p.2 from
        measurable_fst.add measurable_snd).aemeasurable
      (show Continuous fun x : ℝ => g (-x) from hg.comp continuous_neg).aestronglyMeasurable]

end

end SwingRepair
