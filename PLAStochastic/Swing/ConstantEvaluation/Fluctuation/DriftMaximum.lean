import PLAStochastic.Swing.Gaussian.HalfLine.ExponentialStopping
import PLAStochastic.Swing.Gaussian.StripExit.Overshoot
import PLAStochastic.Swing.StationaryLimit.Slope.EarlyLocalization
import PLAStochastic.Swing.Restart.MaximalPrefix.ThreePointBlocks
import PLAStochastic.Swing.ConstantEvaluation.ContractionReduction
import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.GaussianTailSeries
import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.OvershootMeanAssembly

/-! # The maximum of the negative-drift Gaussian walk (roadmap 1.1(b))

`M_a = sup_n (W_n - a n)` and its first argmax `τ*_a`.  For `a > 0` the strong law
makes the maximum attained almost surely.  The pathwise **argmax envelope**

  `(c - a) τ*_c ≤ M_a - M_c ≤ (c - a) τ*_a`  for `a ≤ c`

integrates to `(c - a) 𝔼τ*_c ≤ 𝔼M_a - 𝔼M_c ≤ (c - a) 𝔼τ*_a`.  Together with the
Gaussian law of `W_n` (`P(W_n > a n) = P(Z > a√n)`) this feeds
`Fluctuation.overshootMean_bounds_of_inputs`: the final theorem
`overshootMeanLipschitz_of_inputs` derives `OvershootMeanLipschitz X μ (3/4)` (and
the lower bound `1/2`) from the two remaining named inputs of Appendix I,

* the mean identity `β(a) = a/2 - 1/(2a) + 𝔼M_a` (duality lemma + Lindley balance), and
* Sparre Andersen `𝔼τ*_a = ∑_{n≥1} P(W_n > a n)`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- `S^a_n = W_n - a n`. -/
def negDriftWalk (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  gaussianDriftWalk X 0 (-a) n ω

omit [MeasurableSpace Ω] in
theorem negDriftWalk_eq (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) :
    negDriftWalk X a n ω = cumulativeSamples X n ω - a * n := by
  simp only [negDriftWalk, gaussianDriftWalk]
  ring

omit [MeasurableSpace Ω] in
theorem negDriftWalk_zero (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : negDriftWalk X a 0 ω = 0 := by
  simp [negDriftWalk_eq, cumulativeSamples]

theorem negDriftWalk_measurable (hX : ∀ n, Measurable (X n)) (a : ℝ) (n : ℕ) :
    Measurable (negDriftWalk X a n) :=
  gaussianDriftWalk_measurable hX 0 (-a) n

/-- The maximum is attained. -/
def DriftMaxAttained (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : Prop :=
  ∃ n, ∀ m, negDriftWalk X a m ω ≤ negDriftWalk X a n ω

/-- `M_a = sup_n S^a_n`. -/
def driftMaximum (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : ℝ := ⨆ n, negDriftWalk X a n ω

/-- `τ*_a`, the first index attaining the maximum (`0` if the maximum is not attained). -/
def driftArgmax (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : ℕ :=
  if h : DriftMaxAttained X a ω then Nat.find h else 0

omit [MeasurableSpace Ω] in
theorem driftArgmax_spec {a : ℝ} {ω : Ω} (h : DriftMaxAttained X a ω) (m : ℕ) :
    negDriftWalk X a m ω ≤ negDriftWalk X a (driftArgmax X a ω) ω := by
  unfold driftArgmax
  rw [dif_pos h]
  exact Nat.find_spec h m

omit [MeasurableSpace Ω] in
theorem driftMaximum_eq_argmax {a : ℝ} {ω : Ω} (h : DriftMaxAttained X a ω) :
    driftMaximum X a ω = negDriftWalk X a (driftArgmax X a ω) ω := by
  apply le_antisymm
  · exact ciSup_le (driftArgmax_spec h)
  · exact le_ciSup ⟨_, forall_mem_range.mpr (driftArgmax_spec h)⟩ _

omit [MeasurableSpace Ω] in
theorem le_driftMaximum {a : ℝ} {ω : Ω} (h : DriftMaxAttained X a ω) (n : ℕ) :
    negDriftWalk X a n ω ≤ driftMaximum X a ω := by
  rw [driftMaximum_eq_argmax h]
  exact driftArgmax_spec h n

omit [MeasurableSpace Ω] in
theorem driftMaximum_nonneg {a : ℝ} {ω : Ω} (h : DriftMaxAttained X a ω) :
    0 ≤ driftMaximum X a ω := by
  have := le_driftMaximum h 0
  rwa [negDriftWalk_zero] at this

/-! ### Measurability -/

theorem driftMaximum_measurable (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    Measurable (driftMaximum X a) :=
  Measurable.iSup fun n => negDriftWalk_measurable hX a n

theorem measurableSet_le_walk (hX : ∀ n, Measurable (X n)) (a : ℝ) (n : ℕ) :
    MeasurableSet {ω | ∀ m, negDriftWalk X a m ω ≤ negDriftWalk X a n ω} := by
  have : {ω | ∀ m, negDriftWalk X a m ω ≤ negDriftWalk X a n ω} =
      ⋂ m, {ω | negDriftWalk X a m ω ≤ negDriftWalk X a n ω} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.iInter fun m =>
    measurableSet_le (negDriftWalk_measurable hX a m) (negDriftWalk_measurable hX a n)

theorem measurableSet_driftMaxAttained (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    MeasurableSet {ω | DriftMaxAttained X a ω} := by
  have : {ω | DriftMaxAttained X a ω} =
      ⋃ n, {ω | ∀ m, negDriftWalk X a m ω ≤ negDriftWalk X a n ω} := by
    ext ω; simp [DriftMaxAttained]
  rw [this]
  exact MeasurableSet.iUnion fun n => measurableSet_le_walk hX a n

theorem driftArgmax_measurable (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    Measurable (driftArgmax X a) := by
  classical
  apply measurable_to_countable'
  intro k
  have hset : driftArgmax X a ⁻¹' {k} =
      ({ω | DriftMaxAttained X a ω} ∩ ({ω | ∀ m, negDriftWalk X a m ω ≤ negDriftWalk X a k ω} ∩
        ⋂ j, ⋂ (_ : j < k), {ω | ∀ m, negDriftWalk X a m ω ≤ negDriftWalk X a j ω}ᶜ)) ∪
      ({ω | DriftMaxAttained X a ω}ᶜ ∩ {ω | k = 0}) := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_iInter, mem_compl_iff,
      mem_ofPred_eq, driftArgmax]
    by_cases h : DriftMaxAttained X a ω
    · rw [dif_pos h]
      simp only [h, true_and, not_true_eq_false, false_and, or_false]
      rw [Nat.find_eq_iff h]
    · rw [dif_neg h]
      simp [h, eq_comm]
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.inter (measurableSet_driftMaxAttained hX a)
    (MeasurableSet.inter (measurableSet_le_walk hX a k)
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        (measurableSet_le_walk hX a j).compl))) ?_
  exact MeasurableSet.inter (measurableSet_driftMaxAttained hX a).compl
    (by by_cases hk : k = 0 <;> simp [hk])

/-! ### The maximum is attained almost surely for positive drift -/

theorem driftMaxAttained_ae (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂μ, DriftMaxAttained X a ω := by
  filter_upwards [gaussianDriftWalk_strongLaw hX hi hG 0 (-a)] with ω hω
  -- eventually `S_n / n < -a/2 < 0`, hence `S_n < 0 = S_0`
  have hev : ∀ᶠ n : ℕ in atTop, negDriftWalk X a n ω / n < -a / 2 :=
    hω (Iio_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 1)).exists_forall_of_atTop
  have hneg : ∀ n, N ≤ n → negDriftWalk X a n ω < 0 := by
    intro n hn
    obtain ⟨h1, h2⟩ := hN n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast h2
    have := (div_lt_iff₀ hnpos).mp h1
    nlinarith
  have hN1 : 1 ≤ N := (hN N le_rfl).2
  obtain ⟨n₀, _, hn₀⟩ := Finset.exists_max_image (Finset.range N) (fun n => negDriftWalk X a n ω)
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  refine ⟨n₀, fun m => ?_⟩
  by_cases hm : m < N
  · exact hn₀ m (Finset.mem_range.mpr hm)
  · push Not at hm
    have h0 : negDriftWalk X a 0 ω ≤ negDriftWalk X a n₀ ω :=
      hn₀ 0 (Finset.mem_range.mpr (by omega))
    rw [negDriftWalk_zero] at h0
    exact (hneg m hm).le.trans h0

/-! ### The argmax envelope -/

omit [MeasurableSpace Ω] in
theorem negDriftWalk_sub (X : ℕ → Ω → ℝ) (a c : ℝ) (n : ℕ) (ω : Ω) :
    negDriftWalk X c n ω = negDriftWalk X a n ω - (c - a) * n := by
  rw [negDriftWalk_eq, negDriftWalk_eq]
  ring

omit [MeasurableSpace Ω] in
/-- **Pathwise argmax envelope**: `(c-a) τ*_c ≤ M_a - M_c ≤ (c-a) τ*_a` for `a ≤ c`. -/
theorem driftMaximum_envelope {a c : ℝ} {ω : Ω}
    (ha : DriftMaxAttained X a ω) (hc : DriftMaxAttained X c ω) :
    (c - a) * (driftArgmax X c ω : ℝ) ≤ driftMaximum X a ω - driftMaximum X c ω ∧
      driftMaximum X a ω - driftMaximum X c ω ≤ (c - a) * (driftArgmax X a ω : ℝ) := by
  rw [driftMaximum_eq_argmax ha, driftMaximum_eq_argmax hc]
  set τa := driftArgmax X a ω
  set τc := driftArgmax X c ω
  have h1 : negDriftWalk X a τc ω ≤ negDriftWalk X a τa ω := driftArgmax_spec ha τc
  have h2 : negDriftWalk X c τa ω ≤ negDriftWalk X c τc ω := driftArgmax_spec hc τa
  rw [negDriftWalk_sub X a c τc] at h2 ⊢
  rw [negDriftWalk_sub X a c τa] at h2
  constructor <;> linarith

/-- The integrated envelope: `(c-a) 𝔼τ*_c ≤ 𝔼M_a - 𝔼M_c ≤ (c-a) 𝔼τ*_a`. -/
theorem integral_driftMaximum_envelope (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hMa : Integrable (driftMaximum X a) μ) (hMc : Integrable (driftMaximum X c) μ)
    (hτa : Integrable (fun ω => (driftArgmax X a ω : ℝ)) μ)
    (hτc : Integrable (fun ω => (driftArgmax X c ω : ℝ)) μ) :
    (c - a) * ∫ ω, (driftArgmax X c ω : ℝ) ∂μ ≤
        (∫ ω, driftMaximum X a ω ∂μ) - ∫ ω, driftMaximum X c ω ∂μ ∧
      (∫ ω, driftMaximum X a ω ∂μ) - ∫ ω, driftMaximum X c ω ∂μ ≤
        (c - a) * ∫ ω, (driftArgmax X a ω : ℝ) ∂μ := by
  have hc : 0 < c := lt_of_lt_of_le ha hac
  rw [← integral_sub hMa hMc, ← integral_const_mul, ← integral_const_mul]
  constructor
  · refine integral_mono_ae (hτc.const_mul _) (hMa.sub hMc) ?_
    filter_upwards [driftMaxAttained_ae hX hi hG ha, driftMaxAttained_ae hX hi hG hc] with ω h1 h2
    exact (driftMaximum_envelope h1 h2).1
  · refine integral_mono_ae (hMa.sub hMc) (hτa.const_mul _) ?_
    filter_upwards [driftMaxAttained_ae hX hi hG ha, driftMaxAttained_ae hX hi hG hc] with ω h1 h2
    exact (driftMaximum_envelope h1 h2).2

/-! ### The Gaussian law of the positive-sum events -/

/-- `P(W_n > a n) = P(Z > a√n)` for `n ≥ 1`. -/
theorem measureReal_cumulativeSamples_gt (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    μ.real {ω | a * n < cumulativeSamples X n ω} = Fluctuation.gaussianTailSqrt a n := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hl : HasLaw (cumulativeSamples X n) (gaussianReal 0 (n : ℝ≥0)) μ := by
    simpa [cumulativeSamples] using! gaussian_weighted_sum_hasLaw hX hi hG (Finset.range n) (fun _ => 1)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  -- `gaussianReal 0 n = map (√n * ·) (gaussianReal 0 1)`
  have hscale : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt n * x) = gaussianReal 0 (n : ℝ≥0) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp only [NNReal.coe_mk, mul_one, NNReal.coe_natCast]
      rw [Real.sq_sqrt hnpos.le]
  have hset : {ω | a * n < cumulativeSamples X n ω} = cumulativeSamples X n ⁻¹' Ioi (a * n) := rfl
  rw [Measure.real, hset, ← Measure.map_apply (cumulativeSamples_measurable hX n) measurableSet_Ioi,
    hl.map_eq, ← hscale, Measure.map_apply (measurable_const_mul _) measurableSet_Ioi]
  have hpre : (fun x : ℝ => Real.sqrt n * x) ⁻¹' Ioi (a * n) = Ioi (a * Real.sqrt n) := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    have h2 : Real.sqrt n * (a * Real.sqrt n) = a * n := by
      have : Real.sqrt n * (a * Real.sqrt n) = a * (Real.sqrt n * Real.sqrt n) := by ring
      rw [this, hss]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_left hc hsq.le
      linarith
    · intro h
      have := mul_lt_mul_of_pos_left h hsq
      linarith
  rw [hpre]
  rfl

/-! ### The reduction of the overshoot-mean Lipschitz bound -/

/-- **Mean identity input** (`β(a) = a/2 - 1/(2a) + 𝔼M_a` with `M_a` integrable). -/
def OvershootMeanIdentity (X : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ⦃a : ℝ⦄, 0 < a → Integrable (driftMaximum X a) μ ∧
    overshootMean X μ a = a / 2 - 1 / (2 * a) + ∫ ω, driftMaximum X a ω ∂μ

/-- **Sparre Andersen input** (`𝔼τ*_a = ∑_{n≥1} P(W_n > a n)` with `τ*_a` integrable). -/
def SparreAndersenArgmax (X : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ⦃a : ℝ⦄, 0 < a → Integrable (fun ω => (driftArgmax X a ω : ℝ)) μ ∧
    (∫ ω, (driftArgmax X a ω : ℝ) ∂μ) =
      ∑' n : ℕ, μ.real {ω | a * ((n + 1 : ℕ) : ℝ) < cumulativeSamples X (n + 1) ω}

/-- Under Sparre Andersen, `1/(2a²) - 1/4 ≤ 𝔼τ*_a ≤ 1/(2a²)`. -/
theorem integral_driftArgmax_bounds (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (hSA : SparreAndersenArgmax X μ)
    {a : ℝ} (ha : 0 < a) :
    1 / (2 * a ^ 2) - 1 / 4 ≤ ∫ ω, (driftArgmax X a ω : ℝ) ∂μ ∧
      (∫ ω, (driftArgmax X a ω : ℝ) ∂μ) ≤ 1 / (2 * a ^ 2) := by
  rw [(hSA ha).2]
  have heq : (fun n : ℕ => μ.real {ω | a * ((n + 1 : ℕ) : ℝ) < cumulativeSamples X (n + 1) ω}) =
      fun n : ℕ => Fluctuation.gaussianTailSqrt a (n + 1 : ℕ) := by
    funext n
    exact measureReal_cumulativeSamples_gt hX hi hG a (by omega)
  rw [heq]
  exact Fluctuation.tsum_gaussianTailSqrt_bounds ha

/-- **`OvershootMeanLipschitz X μ (3/4)` (and the lower bound `1/2`) from the mean
identity and Sparre Andersen.** -/
theorem overshootMean_bounds_of_identity_sparreAndersen
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hid : OvershootMeanIdentity X μ) (hSA : SparreAndersenArgmax X μ)
    {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    1 / 2 * (c - a) ≤ overshootMean X μ c - overshootMean X μ a ∧
      overshootMean X μ c - overshootMean X μ a ≤ 3 / 4 * (c - a) := by
  refine Fluctuation.overshootMean_bounds_of_inputs (β := overshootMean X μ)
    (m := fun x => ∫ ω, driftMaximum X x ω ∂μ) (τ := fun x => ∫ ω, (driftArgmax X x ω : ℝ) ∂μ)
    (fun x hx => (hid hx).2) ?_ ?_ (fun x hx => (integral_driftArgmax_bounds hX hi hG hSA hx).1)
    (fun x hx => (integral_driftArgmax_bounds hX hi hG hSA hx).2) ha hac
  · intro x y hx hxy
    have hy : 0 < y := lt_of_lt_of_le hx hxy
    exact (integral_driftMaximum_envelope hX hi hG hx hxy (hid hx).1 (hid hy).1 (hSA hx).1
      (hSA hy).1).1
  · intro x y hx hxy
    have hy : 0 < y := lt_of_lt_of_le hx hxy
    exact (integral_driftMaximum_envelope hX hi hG hx hxy (hid hx).1 (hid hy).1 (hSA hx).1
      (hSA hy).1).2

theorem overshootMeanLipschitz_of_inputs
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hid : OvershootMeanIdentity X μ) (hSA : SparreAndersenArgmax X μ) :
    OvershootMeanLipschitz X μ (3 / 4) := fun _ _ ha hac =>
  (overshootMean_bounds_of_identity_sparreAndersen hX hi hG hid hSA ha hac).2

end SwingRepair
