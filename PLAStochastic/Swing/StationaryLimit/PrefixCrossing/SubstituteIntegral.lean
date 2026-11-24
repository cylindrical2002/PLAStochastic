import PLAStochastic.Swing.Ladder.Renewal.WalkOvershootLimit
import PLAStochastic.Swing.StationaryLimit.MarginKernel.WeakFeller
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.Substitute
import PLAStochastic.Swing.Restart.MaximalPrefix.HistoryIndependence
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.DistantBridge
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.LocalErrorBridge

/-!
# Reflected overshoot integrals for the prefix substitute

The finite-prefix substitute is a reflected first-passage overshoot.  This
file isolates the analytic part of the substitute-law comparison: the
uniform bounded-Lipschitz estimate already proved for the (unreflected)
overshoot transfers, without loss, through `o ↦ a-o`.  It also records the
exact prefix/future factorisation supplied by the iid coordinate split; the
remaining localization and kernel-comparison estimates are kept explicit in
the endpoint theorems below.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Exact factorisation of an independent prefix and future -/

theorem integral_pair_of_indepFun
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {P : Ω → α} {Q : Ω → β}
    (hP : Measurable P) (hQ : Measurable Q) (hPQ : P ⟂ᵢ[μ] Q)
    {F : α × β → ℝ} (hF : Measurable F) {B : ℝ} (_hB : 0 ≤ B)
    (hFB : ∀ z, |F z| ≤ B) :
    (∫ ω, F (P ω, Q ω) ∂μ) =
      ∫ p, ∫ q, F (p, q) ∂(μ.map Q) ∂(μ.map P) := by
  let _ : IsProbabilityMeasure (μ.map P) :=
    Measure.isProbabilityMeasure_map hP.aemeasurable
  let _ : IsProbabilityMeasure (μ.map Q) :=
    Measure.isProbabilityMeasure_map hQ.aemeasurable
  have hpair : Measurable (fun ω => (P ω, Q ω)) := hP.prodMk hQ
  have hmap : μ.map (fun ω => (P ω, Q ω)) = (μ.map P).prod (μ.map Q) :=
    hPQ.map_prod_eq_prod_map_map hP.aemeasurable hQ.aemeasurable
  have hFI : Integrable F ((μ.map P).prod (μ.map Q)) := by
    refine (integrable_const B).mono' hF.aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact hFB z
  calc
    (∫ ω, F (P ω, Q ω) ∂μ) =
        ∫ z, F z ∂(μ.map (fun ω => (P ω, Q ω))) := by
      exact (integral_map hpair.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ z, F z ∂((μ.map P).prod (μ.map Q)) := by rw [hmap]
    _ = ∫ p, ∫ q, F (p, q) ∂(μ.map Q) ∂(μ.map P) :=
      integral_prod F hFI

/-! ### The concrete prefix/future product representation -/

/-- The finite prefix state `(slope, level)`. -/
def prefixCrossingParameter (X : ℕ → Ω → ℝ) (E r : ℝ) (J : ℕ) :
    Ω → (ℝ × ℝ) :=
  fun ω => (prefixCrossingSlope X r J ω, prefixCrossingLevel X E r J ω)

/-- The reflected fresh sequence used after the prefix. -/
def prefixCrossingFuture (X : ℕ → Ω → ℝ) (J : ℕ) : Ω → (ℕ → ℝ) :=
  fun ω j => -X (J - 1 + j) ω

/-- The output functional on a prefix state and a fresh sequence. -/
def prefixCrossingProductOutput (f : ℝ → ℝ) :
    (ℝ × ℝ) × (ℕ → ℝ) → ℝ :=
  fun p => f (if 0 < p.1.1 ∧ 0 < p.1.2 then
      p.1.1 - gaussianWalkOvershoot (fun n q => q.2 n)
      p.1.1 p.1.2 p else 0)

omit [MeasurableSpace Ω] in
theorem gaussianWalkOvershoot_product_eq_native
    (a b : ℝ) (s : ℝ × ℝ) (z : ℕ → ℝ) :
    gaussianWalkOvershoot (fun (n : ℕ) (q : (ℝ × ℝ) × (ℕ → ℝ)) => q.2 n)
        a b (s, z) =
      gaussianWalkOvershoot nativeIncrementCoordinates a b z := by
  simp [gaussianWalkOvershoot, gaussianWalkPassage, gaussianDriftWalk,
    cumulativeSamples, nativeIncrementCoordinates]

theorem prefixCrossingParameter_measurable
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (E r : ℝ) (J : ℕ) : Measurable (prefixCrossingParameter X E r J) := by
  exact (prefixCrossingSlope_measurable hX r J).prodMk
    (prefixCrossingLevel_measurable hX E r J)

theorem prefixCrossingFuture_measurable
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n)) (J : ℕ) :
    Measurable (prefixCrossingFuture X J) := by
  exact measurable_pi_lambda _ (fun j => (hX (J - 1 + j)).neg)

/-! The prefix parameter really is measurable before the first increment of the
shifted future.  We keep these relative-measurability lemmas explicit: global
measurability alone is not enough to invoke the iid sigma-algebra split. -/

theorem cumulativeSamples_measurable_indexSpace
    {X : ℕ → Ω → ℝ} (_hX : ∀ n, Measurable (X n))
    {k n : ℕ} (hkn : k ≤ n) :
    Measurable[incrementIndexSpace X (Iio n)] (cumulativeSamples X k) := by
  unfold cumulativeSamples
  apply Finset.measurable_sum
  intro i hi
  exact incrementIndexSpace_eval (Set.mem_Iio.mpr (by
    have hik : i < k := Finset.mem_range.mp hi
    omega))

theorem swingSlopeTerm_measurable_indexSpace
    {X : ℕ → Ω → ℝ} (_hX : ∀ n, Measurable (X n))
    (r : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    Measurable[incrementIndexSpace X (Iio n)] (swingSlopeTerm X r k) := by
  unfold swingSlopeTerm
  exact (cumulativeSamples_measurable_indexSpace _hX hkn).sub measurable_const |>.div_const _

theorem swingEarlySlope_measurable_indexSpace
    {X : ℕ → Ω → ℝ} (_hX : ∀ n, Measurable (X n))
    (r : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    Measurable[incrementIndexSpace X (Iio n)] (swingEarlySlope X r k) := by
  induction k with
  | zero =>
      simpa [swingEarlySlope] using
        (swingSlopeTerm_measurable_indexSpace _hX r (k := 0) (n := n)
          (Nat.zero_le n))
  | succ k ih =>
      have hik : k ≤ n := by omega
      have hi := ih hik
      have ht := swingSlopeTerm_measurable_indexSpace _hX r
        (k := k + 1) (n := n) (by omega)
      simpa [swingEarlySlope] using hi.max ht

theorem prefixCrossingParameter_measurable_indexSpace
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (E r : ℝ) (J : ℕ) :
    Measurable[incrementIndexSpace X (Iio (J - 1))]
      (prefixCrossingParameter X E r J) := by
  have hs : Measurable[incrementIndexSpace X (Iio (J - 1))]
      (prefixCrossingSlope X r J) := by
    unfold prefixCrossingSlope
    split
    · exact swingEarlySlope_measurable_indexSpace hX r le_rfl
    · exact measurable_const
  have hl : Measurable[incrementIndexSpace X (Iio (J - 1))]
      (prefixCrossingLevel X E r J) := by
    unfold prefixCrossingLevel
    exact (((measurable_const.sub measurable_const).sub
      (hs.mul_const (J : ℝ))).add
      (cumulativeSamples_measurable_indexSpace hX le_rfl))
  exact hs.prodMk hl

/-! The iid hypothesis really supplies the independence used by the product
representation.  The index split is `Iio (J-1)` versus `Ici (J-1)`: the
prefix uses only the coordinates `X 0, ..., X (J-2)` (equivalently
`W_(J-1)`), while the shifted future starts with `X (J-1)`. -/
theorem prefixCrossingParameter_indep_future
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (E r : ℝ) (J : ℕ) :
    prefixCrossingParameter X E r J ⟂ᵢ[μ] prefixCrossingFuture X J := by
  let n : ℕ := J - 1
  have hdis : Disjoint (Iio n) (Ici n) := by
    exact Set.disjoint_left.mpr (by
      intro k hklt hkle
      change k < n at hklt
      change n ≤ k at hkle
      exact (not_lt_of_ge hkle) hklt)
  have hspaces :
      Indep (incrementIndexSpace X (Iio n))
        (incrementIndexSpace X (Ici n)) μ := by
    exact indep_iSup_of_disjoint (fun k => (hX k).comap_le) hi.iIndep hdis
  have hP : Measurable[incrementIndexSpace X (Iio n)]
      (prefixCrossingParameter X E r J) := by
    simpa [n] using prefixCrossingParameter_measurable_indexSpace hX E r J
  have hQ' : Measurable[incrementIndexSpace X (Ici (J - 1))]
      (prefixCrossingFuture X J) := by
    let _ : MeasurableSpace Ω := incrementIndexSpace X (Ici (J - 1))
    unfold prefixCrossingFuture
    change Measurable (fun ω j => -X (J - 1 + j) ω)
    apply measurable_pi_lambda _
    intro j
    exact (incrementIndexSpace_eval (X := X)
      (show J - 1 + j ∈ Set.Ici (J - 1) by
        exact Set.mem_Ici.mpr (by omega))).neg
  have hQ : Measurable[incrementIndexSpace X (Ici n)]
      (prefixCrossingFuture X J) := by
    simpa [n] using hQ'
  apply (IndepFun_iff_Indep _ _ μ).2
  exact indep_of_indep_of_le hspaces hP.comap_le hQ.comap_le

/-! Shifted iid sequence laws, including the reflected sign used by the
substitute.  This is the law-level bridge needed to turn the inner product
integral into the already established reflected overshoot reward. -/
theorem shiftedSequence_identDistrib
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (s : ℕ) :
    IdentDistrib (fun ω (j : ℕ) => X (s + j) ω)
      (fun ω (j : ℕ) => X j ω) μ μ := by
  have hshift : iIndepFun (fun j : ℕ => X (s + j)) μ :=
    hi.precomp (g := fun j : ℕ => s + j)
      (by intro i j hij; dsimp at hij; omega)
  refine ⟨(measurable_pi_lambda _ fun j : ℕ => hX (s + j)).aemeasurable,
    (measurable_pi_lambda _ hX).aemeasurable, ?_⟩
  rw [hshift.map_fun_eq_infinitePi_map (fun j => hX (s + j)),
    hi.map_fun_eq_infinitePi_map hX]
  congr 1
  funext j
  exact (hG (s + j)).trans (hG j).symm

theorem prefixCrossingFuture_identDistrib
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (J : ℕ) :
    IdentDistrib (prefixCrossingFuture X J)
      (fun ω (j : ℕ) => X j ω) μ μ := by
  have hshift := shiftedSequence_identDistrib hX hi hG (J - 1)
  have hneg := negSequence_identDistrib hX hi hG
  have hN : Measurable (fun z : ℕ → ℝ => fun j => -z j) :=
    measurable_pi_lambda _ (fun j => (measurable_pi_apply j).neg)
  have hcomp := hshift.comp hN
  have htrans := hcomp.trans hneg
  change IdentDistrib (fun ω (j : ℕ) => -X (J - 1 + j) ω)
    (fun ω (j : ℕ) => X j ω) μ μ
  simpa only [Function.comp_def] using htrans

theorem prefixCrossingProductOutput_measurable
    {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (prefixCrossingProductOutput f) := by
  let Y : ℕ → ((ℝ × ℝ) × (ℕ → ℝ)) → ℝ :=
    fun j p => p.2 j
  have hY : ∀ j, Measurable (Y j) := by
    intro j
    exact (measurable_pi_apply j).comp measurable_snd
  have ha : Measurable (fun p : (ℝ × ℝ) × (ℕ → ℝ) => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hb : Measurable (fun p : (ℝ × ℝ) × (ℕ → ℝ) => p.1.2) :=
    measurable_snd.comp measurable_fst
  have ho : Measurable (fun p : (ℝ × ℝ) × (ℕ → ℝ) =>
      gaussianWalkOvershoot Y (p.1.1) (p.1.2) p) := by
    exact gaussianWalkOvershoot_random_measurable hY ha hb
  have hcond : MeasurableSet {p : (ℝ × ℝ) × (ℕ → ℝ) |
      0 < p.1.1 ∧ 0 < p.1.2} := by
    exact (measurableSet_lt measurable_const ha).inter
      (measurableSet_lt measurable_const hb)
  have hout : Measurable (fun p : (ℝ × ℝ) × (ℕ → ℝ) =>
      if 0 < p.1.1 ∧ 0 < p.1.2 then
        p.1.1 - gaussianWalkOvershoot Y (p.1.1) (p.1.2) p else 0) := by
    exact Measurable.ite hcond (ha.sub ho) measurable_const
  exact hf.comp hout

omit [MeasurableSpace Ω] in
theorem prefixCrossingProductOutput_eq_substitute
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (f : ℝ → ℝ) (ω : Ω) :
    prefixCrossingProductOutput f
        (prefixCrossingParameter X E r J ω, prefixCrossingFuture X J ω) =
      f (prefixCrossingSubstitute X E r J ω) := by
  unfold prefixCrossingProductOutput prefixCrossingParameter prefixCrossingFuture
    prefixCrossingSubstitute prefixCrossingOvershoot
  simp [gaussianWalkOvershoot, gaussianWalkPassage, gaussianDriftWalk,
    cumulativeSamples, negIncrements]

theorem prefixCrossingSubstitute_integral_eq_independent_product
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (E r : ℝ) (J : ℕ)
    {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ y, |f y| ≤ B) :
    (∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) =
      ∫ p : ℝ × ℝ, ∫ z : ℕ → ℝ,
        prefixCrossingProductOutput f (p, z) ∂(μ.map (prefixCrossingFuture X J)) ∂
          (μ.map (prefixCrossingParameter X E r J)) := by
  have hP := prefixCrossingParameter_measurable hX E r J
  have hQ := prefixCrossingFuture_measurable hX J
  let F := prefixCrossingProductOutput f
  have hF : Measurable F := prefixCrossingProductOutput_measurable hf
  have hFB : ∀ p, |F p| ≤ B := by
    intro p
    exact hfB _
  have hPQ := prefixCrossingParameter_indep_future (μ := μ) hX hi E r J
  have hprod := integral_pair_of_indepFun hP hQ hPQ hF hB hFB
  have hleft : (∫ ω, F (prefixCrossingParameter X E r J ω,
      prefixCrossingFuture X J ω) ∂μ) =
      ∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact prefixCrossingProductOutput_eq_substitute E r J f ω
  rw [← hleft]
  simpa [F] using hprod

/-- The reflected finite-level overshoot reward.  This is the fibre reward
appearing after conditioning on a prefix slope and crossing level. -/
def gaussianWalkReflectedReward
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ ω, f (a - gaussianWalkOvershoot X a b ω) ∂μ

theorem prefixCrossingProductFibre_eq_reflectedReward
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (_E : ℝ) (_r : ℝ) (J : ℕ) {f : ℝ → ℝ} (hf : Measurable f)
    {a b : ℝ} (hpos : 0 < a ∧ 0 < b) :
    (∫ z, prefixCrossingProductOutput f ((a, b), z)
      ∂(μ.map (prefixCrossingFuture X J))) =
      gaussianWalkReflectedReward X μ f a b := by
  let φ : (ℕ → ℝ) → ℝ := fun z =>
    f (a - gaussianWalkOvershoot nativeIncrementCoordinates a b z)
  have hO : Measurable (gaussianWalkOvershoot nativeIncrementCoordinates a b) :=
    gaussianWalkOvershoot_measurable (fun n => nativeIncrementCoordinates_measurable n) a b
  have hφ : Measurable φ := by
    exact hf.comp (measurable_const.sub hO)
  have hmap := (integral_map
    (μ := μ)
    (prefixCrossingFuture_measurable hX J).aemeasurable
    hφ.aestronglyMeasurable)
  have hident := (prefixCrossingFuture_identDistrib hX hi hG J).comp hφ
  have hovershoot : ∀ z : ℕ → ℝ,
      gaussianWalkOvershoot
          (fun (n : ℕ) (q : (ℝ × ℝ) × (ℕ → ℝ)) => q.2 n) a b ((a, b), z) =
        gaussianWalkOvershoot nativeIncrementCoordinates a b z := by
    intro z
    rfl
  calc
    (∫ z, prefixCrossingProductOutput f ((a, b), z)
        ∂(μ.map (prefixCrossingFuture X J))) =
        ∫ z, φ z ∂(μ.map (prefixCrossingFuture X J)) := by
      simp [prefixCrossingProductOutput, φ, hovershoot, hpos.1, hpos.2]
    _ = ∫ ω, φ (prefixCrossingFuture X J ω) ∂μ := hmap
    _ = ∫ ω, φ (fun j => X j ω) ∂μ := hident.integral_eq
    _ = gaussianWalkReflectedReward X μ f a b := by
      rfl

/-- The inner product integral, viewed as a function of the prefix state. -/
def prefixCrossingProductFibre
    {X : ℕ → Ω → ℝ} (μ : Measure Ω) (f : ℝ → ℝ) (J : ℕ)
    (p : ℝ × ℝ) : ℝ :=
  ∫ z, prefixCrossingProductOutput f (p, z)
    ∂(μ.map (prefixCrossingFuture X J))

theorem prefixCrossingProductFibre_measurable
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Measurable f) (J : ℕ) :
    Measurable (prefixCrossingProductFibre (X := X) μ f J) := by
  change Measurable (fun p : ℝ × ℝ =>
    ∫ z, prefixCrossingProductOutput f (p, z)
      ∂(μ.map (prefixCrossingFuture X J)))
  have hsm : StronglyMeasurable (prefixCrossingProductOutput f) :=
    (prefixCrossingProductOutput_measurable hf).stronglyMeasurable
  exact hsm.integral_prod_right'.measurable

theorem prefixCrossingProductFibre_bound
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) {f : ℝ → ℝ} {B : ℝ}
    (hfB : ∀ y, |f y| ≤ B) (J : ℕ) (p : ℝ × ℝ) :
    |prefixCrossingProductFibre (X := X) μ f J p| ≤ B := by
  change |∫ z, prefixCrossingProductOutput f (p, z)
      ∂(μ.map (prefixCrossingFuture X J))| ≤ B
  have hFbound : ∀ z : ℕ → ℝ,
      ‖prefixCrossingProductOutput f (p, z)‖ ≤ B := by
    intro z
    rw [Real.norm_eq_abs]
    exact hfB _
  let _ : IsProbabilityMeasure (μ.map (prefixCrossingFuture X J)) :=
    Measure.isProbabilityMeasure_map
      (prefixCrossingFuture_measurable hX (J := J)).aemeasurable
  have h := norm_integral_le_of_norm_le_const
    (μ := μ.map (prefixCrossingFuture X J))
    (ae_of_all _ hFbound)
  simpa [Real.norm_eq_abs] using h

theorem gaussianWalkReflectedReward_measurable_integrand
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    {f : ℝ → ℝ} (hf : Measurable f) (a b : ℝ) :
    Measurable (fun ω => f (a - gaussianWalkOvershoot X a b ω)) := by
  exact hf.comp (measurable_const.sub
    (gaussianWalkOvershoot_measurable hX a b))

theorem abs_swingOvershootReward_le_of_finite
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : 0 ≤ B) (hfB : ∀ y, |f y| ≤ B) (a : ℝ) :
    |swingOvershootReward X μ f a| ≤ B := by
  let ν : Measure ℝ := swingOvershootMeasure X μ a
  have hνle : ν Set.univ ≤ 1 := by
    dsimp [ν]
    exact swingOvershootMeasure_univ_le_one hX hi a
  have hνtop : ν Set.univ ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hνle
  let _ : IsFiniteMeasure ν := ⟨hνtop.lt_top⟩
  have hint : Integrable f ν := by
    refine (integrable_const B).mono' hf.aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact hfB y
  have hνreal : ν.real Set.univ ≤ 1 := by
    unfold Measure.real
    exact ENNReal.toReal_mono ENNReal.one_ne_top hνle
  change |∫ y, f y ∂ν| ≤ B
  calc
    |∫ y, f y ∂ν| ≤ ∫ y, |f y| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ _y, B ∂ν := integral_mono_ae hint.norm (integrable_const B)
      (ae_of_all _ hfB)
    _ = B * ν.real Set.univ := by
      rw [integral_const]
      simp [smul_eq_mul, mul_comm]
    _ ≤ B := by
      nlinarith [mul_le_mul_of_nonneg_left hνreal hB]

theorem gaussianWalkReflectedReward_eq_overshootLaw_integral
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) {f : ℝ → ℝ} (hf : Measurable f)
    (a b : ℝ) :
    gaussianWalkReflectedReward X μ f a b =
      ∫ y, f y ∂((gaussianWalkOvershootLaw X μ a b).map (fun o => a - o)) := by
  unfold gaussianWalkReflectedReward gaussianWalkOvershootLaw
  have hO : Measurable (gaussianWalkOvershoot X a b) :=
    gaussianWalkOvershoot_measurable hX a b
  have hR : Measurable (fun o : ℝ => a - o) := measurable_const.sub measurable_id
  have hRf : Measurable (fun o : ℝ => f (a - o)) := hf.comp hR
  calc
    gaussianWalkReflectedReward X μ f a b =
        ∫ ω, f (a - gaussianWalkOvershoot X a b ω) ∂μ := rfl
    _ = ∫ x, f (a - x) ∂(μ.map (gaussianWalkOvershoot X a b)) := by
      exact (integral_map hO.aemeasurable hRf.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂((μ.map (gaussianWalkOvershoot X a b)).map
        (fun o : ℝ => a - o)) := by
      exact (integral_map hR.aemeasurable hf.aestronglyMeasurable).symm

/-! The corresponding reflected equilibrium reward is represented by the same
map.  Keeping this rewrite named makes the later comparison insensitive to
the implementation of `swingOvershootMeasure`. -/
theorem swingOvershootReward_eq_equilibriumLaw_integral
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} {f : ℝ → ℝ}
    (a : ℝ) :
    swingOvershootReward X μ f a =
      ∫ y, f y ∂((equilibriumOvershootLaw
        (gaussianAscendingLadderLaw X μ a)).map (fun o => a - o)) := by
  rfl

theorem gaussianWalkReflectedReward_lipschitz_le
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M C c : ℝ} (hδ : 0 < δ)
    (hexp : UniformLadderRenewalExpansion
      (gaussianAscendingLadderLaw X μ) (Icc δ M) C c)
    {a : ℝ} (hδa : δ ≤ a) (haM : a ≤ M)
    {b T : ℝ} (hb : 0 < b) (hT : 0 < T)
    {f : ℝ → ℝ} (hf : Measurable f) {K B : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ K * |x - y|)
    (hfB : ∀ x, |f x| ≤ B) :
    |gaussianWalkReflectedReward X μ f a b -
        swingOvershootReward X μ f a| ≤
      gaussianOvershootLipschitzBound δ M K B C c b T := by
  let g : ℝ → ℝ := fun o => f (a - o)
  have hg : Measurable g := Measurable.comp hf (measurable_const.sub measurable_id)
  have hglip : ∀ x y : ℝ, |g x - g y| ≤ K * |x - y| := by
    intro x y
    dsimp [g]
    calc
      |f (a - x) - f (a - y)| ≤ K * |(a - x) - (a - y)| := hlip _ _
      _ = K * |x - y| := by
        congr 1
        rw [show (a - x) - (a - y) = -(x - y) by ring, abs_neg]
  have hgbdd : ∀ x, |g x| ≤ B := by
    intro x
    exact hfB _
  have hmain := gaussianWalkOvershoot_lipschitz_le
    (X := X) (μ := μ) hX hi hG hδ hexp hδa haM hb hT hK hglip hgbdd
  have hfinite : gaussianWalkReflectedReward X μ f a b =
      ∫ o, g o ∂(gaussianWalkOvershootLaw X μ a b) := by
    unfold gaussianWalkReflectedReward gaussianWalkOvershootLaw
    exact (integral_map
      (gaussianWalkOvershoot_measurable hX a b).aemeasurable
      (show Measurable (fun o : ℝ => f (a - o)) from hg).aestronglyMeasurable).symm
  have hequil : swingOvershootReward X μ f a =
      ∫ o, g o ∂(equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a)) := by
    unfold swingOvershootReward swingOvershootMeasure
    simpa [g] using (integral_map
      (φ := fun o : ℝ => a - o)
      (measurable_const.sub measurable_id).aemeasurable
      hf.aestronglyMeasurable)
  rw [hfinite, hequil]
  exact hmain

/-! The preceding fibre estimate can be made simultaneous in the crossing
level and in the bounded-Lipschitz test function.  This is the exact
``uniform overshoot`` input needed after a prefix/future factorisation. -/
theorem gaussianWalkReflectedReward_lipschitz_uniform
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M C c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hexp : UniformLadderRenewalExpansion
      (gaussianAscendingLadderLaw X μ) (Icc δ M) C c)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {η : ℝ} (hη : 0 < η) :
    ∃ b₀ : ℝ, ∀ a ∈ Icc δ M, ∀ b : ℝ, b₀ ≤ b → ∀ f : ℝ → ℝ,
      (∀ x y : ℝ, |f x - f y| ≤ K * |x - y|) →
      (∀ x, |f x| ≤ B) →
        |gaussianWalkReflectedReward X μ f a b -
            swingOvershootReward X μ f a| ≤ η := by
  obtain ⟨b₀, hb₀⟩ := gaussianWalkOvershoot_lipschitz_uniform
    (X := X) (μ := μ) hX hi hG hδ hc hexp hK hB hη
  refine ⟨b₀, ?_⟩
  intro a ha b hb f hfl hfB
  let g : ℝ → ℝ := fun o => f (a - o)
  have hfLip : LipschitzWith ⟨K, hK⟩ f := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    change |f x - f y| ≤ K * |x - y|
    exact hfl x y
  have hfmeas : Measurable f := hfLip.continuous.measurable
  have hg : Measurable g := by
    exact Measurable.comp hfmeas (measurable_const.sub measurable_id)
  have hglip : ∀ x y : ℝ, |g x - g y| ≤ K * |x - y| := by
    intro x y
    dsimp [g]
    calc
      |f (a - x) - f (a - y)| ≤ K * |(a - x) - (a - y)| := hfl _ _
      _ = K * |x - y| := by
        congr 1
        rw [show (a - x) - (a - y) = -(x - y) by ring, abs_neg]
  have hgbdd : ∀ x, |g x| ≤ B := by
    intro x
    exact hfB _
  have hmain := hb₀ a ha b hb g hglip hgbdd
  have hfinite : gaussianWalkReflectedReward X μ f a b =
      ∫ o, g o ∂(gaussianWalkOvershootLaw X μ a b) := by
    unfold gaussianWalkReflectedReward gaussianWalkOvershootLaw
    exact (integral_map
      (gaussianWalkOvershoot_measurable hX a b).aemeasurable
      (show Measurable (fun o : ℝ => f (a - o)) from hg).aestronglyMeasurable).symm
  have hequil : swingOvershootReward X μ f a =
      ∫ o, g o ∂(equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a)) := by
    unfold swingOvershootReward swingOvershootMeasure
    simpa [g] using (integral_map
      (φ := fun o : ℝ => a - o)
      (measurable_const.sub measurable_id).aemeasurable
      hfmeas.aestronglyMeasurable)
  rw [hfinite, hequil]
  exact hmain

/-- The uniform passage-level witness can be chosen strictly positive.  The
upstream theorem already enlarges its witness by `max _ 1`; this wrapper makes
that positivity part of the public interface so downstream support arguments
do not have to recover it from the implementation. -/
theorem gaussianWalkReflectedReward_lipschitz_uniform_pos
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M C c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hexp : UniformLadderRenewalExpansion
      (gaussianAscendingLadderLaw X μ) (Icc δ M) C c)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {η : ℝ} (hη : 0 < η) :
    ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ a ∈ Icc δ M, ∀ b : ℝ, b₀ ≤ b → ∀ f : ℝ → ℝ,
        (∀ x y : ℝ, |f x - f y| ≤ K * |x - y|) →
        (∀ x, |f x| ≤ B) →
          |gaussianWalkReflectedReward X μ f a b -
              swingOvershootReward X μ f a| ≤ η := by
  obtain ⟨b₀, hb₀⟩ := gaussianWalkReflectedReward_lipschitz_uniform
    (X := X) (μ := μ) hX hi hG hδ hc hexp hK hB hη
  refine ⟨max b₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro a ha b hb f hfl hfB
  exact hb₀ a ha b (le_trans (le_max_left _ _) hb) f hfl hfB

/-! ### Lifting a fibre estimate to a random prefix law

The next lemma is purely measure-theoretic.  It is intentionally stated for
an arbitrary law on `(slope, level)`: the remaining prefix/future
factorisation can therefore be supplied independently, while this file still
closes the exact integration step once that factorisation is available. -/
theorem integral_sub_le_of_uniform_prefix_fibres
    {ρ : Measure (ℝ × ℝ)} [IsProbabilityMeasure ρ]
    {u v : ℝ × ℝ → ℝ} {B η δ M b₀ : ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (huB : ∀ p, |u p| ≤ B) (hvB : ∀ p, |v p| ≤ B)
    (hsupport : ∀ᵐ p ∂ρ, p.1 ∈ Icc δ M ∧ b₀ ≤ p.2)
    (hfibre : ∀ a ∈ Icc δ M, ∀ b, b₀ ≤ b →
      |u (a, b) - v (a, b)| ≤ η) :
    |(∫ p, u p ∂ρ) - ∫ p, v p ∂ρ| ≤ η := by
  have huI : Integrable u ρ := by
    refine (integrable_const B).mono' hu.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact huB p
  have hvI : Integrable v ρ := by
    refine (integrable_const B).mono' hv.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact hvB p
  have hdiffI : Integrable (fun p => u p - v p) ρ := huI.sub hvI
  have hpoint : ∀ᵐ p ∂ρ, |u p - v p| ≤ η := by
    filter_upwards [hsupport] with p hp
    exact hfibre p.1 hp.1 p.2 hp.2
  have hηI : Integrable (fun _ : ℝ × ℝ => η) ρ := integrable_const η
  calc
    |(∫ p, u p ∂ρ) - ∫ p, v p ∂ρ| =
        |∫ p, (u p - v p) ∂ρ| := by rw [integral_sub huI hvI]
    _ ≤ ∫ p, |u p - v p| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ _p, η ∂ρ := integral_mono_ae hdiffI.norm hηI hpoint
    _ = η := by simp

theorem integral_sub_le_of_ae_uniform_bound
    {ρ : Measure (ℝ × ℝ)} [IsProbabilityMeasure ρ]
    {u v : ℝ × ℝ → ℝ} {B η : ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (huB : ∀ p, |u p| ≤ B) (hvB : ∀ p, |v p| ≤ B)
    (hpoint : ∀ᵐ p ∂ρ, |u p - v p| ≤ η) :
    |(∫ p, u p ∂ρ) - ∫ p, v p ∂ρ| ≤ η := by
  have huI : Integrable u ρ := by
    refine (integrable_const B).mono' hu.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact huB p
  have hvI : Integrable v ρ := by
    refine (integrable_const B).mono' hv.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact hvB p
  have hdiffI : Integrable (fun p => u p - v p) ρ := huI.sub hvI
  have hηI : Integrable (fun _ : ℝ × ℝ => η) ρ := integrable_const η
  calc
    |(∫ p, u p ∂ρ) - ∫ p, v p ∂ρ| =
        |∫ p, (u p - v p) ∂ρ| := by rw [integral_sub huI hvI]
    _ ≤ ∫ p, |u p - v p| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ _p, η ∂ρ := integral_mono_ae hdiffI.norm hηI hpoint
    _ = η := by simp

/-- Bounded integral comparison when the fibre estimate is only available on a
measurable state set.  The complement is paid for explicitly; no support
property is inferred from the measure bound. -/
theorem integral_sub_le_of_ae_uniform_bound_on_event
    {ρ : Measure (ℝ × ℝ)} [IsProbabilityMeasure ρ]
    {u v : ℝ × ℝ → ℝ} {B η q : ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (hB : 0 ≤ B) (hη : 0 ≤ η)
    (huB : ∀ p, |u p| ≤ B) (hvB : ∀ p, |v p| ≤ B)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpoint : ∀ᵐ p ∂ρ, p ∈ S → |u p - v p| ≤ η)
    (hbad : ρ.real Sᶜ ≤ q) :
    |(∫ p, u p ∂ρ) - ∫ p, v p ∂ρ| ≤ η + 2 * B * q := by
  have huI : Integrable u ρ := by
    refine (integrable_const B).mono' hu.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact huB p
  have hvI : Integrable v ρ := by
    refine (integrable_const B).mono' hv.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact hvB p
  have hdiffI : Integrable (fun p => u p - v p) ρ := huI.sub hvI
  have hpointN : ∀ᵐ p ∂ρ, p ∈ S → ‖u p - v p‖ ≤ η := by
    filter_upwards [hpoint] with p hp hps
    rw [Real.norm_eq_abs]
    exact hp hps
  have hdiffN : ∀ᵐ p ∂ρ, ‖u p - v p‖ ≤ 2 * B := by
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_sub_comm]
    calc
      |v p - u p| ≤ ‖v p - u p‖ := by rfl
      _ ≤ ‖v p‖ + ‖u p‖ := norm_sub_le _ _
      _ = |v p| + |u p| := by simp only [Real.norm_eq_abs]
      _ ≤ B + B := add_le_add (hvB p) (huB p)
      _ = 2 * B := by ring
  have hSbound :
      ‖∫ p in S, (u p - v p) ∂ρ‖ ≤ η * ρ.real S :=
    norm_setIntegral_le_of_norm_le_const_ae'
      (lt_top_iff_ne_top.mpr (measure_ne_top ρ S)) hpointN
  have hScbound :
      ‖∫ p in Sᶜ, (u p - v p) ∂ρ‖ ≤ (2 * B) * ρ.real Sᶜ :=
    norm_setIntegral_le_of_norm_le_const_ae'
      (lt_top_iff_ne_top.mpr (measure_ne_top ρ Sᶜ))
      (hdiffN.mono (fun p hp _ => hp))
  have hSbound' :
      |∫ p in S, (u p - v p) ∂ρ| ≤ η * ρ.real S := by
    simpa only [Real.norm_eq_abs] using hSbound
  have hScbound' :
      |∫ p in Sᶜ, (u p - v p) ∂ρ| ≤ (2 * B) * ρ.real Sᶜ := by
    simpa only [Real.norm_eq_abs] using hScbound
  have hSle : ρ.real S ≤ 1 := by
    have hle := measureReal_mono (μ := ρ) (Set.subset_univ S)
      (measure_ne_top ρ Set.univ)
    rw [show ρ.real (Set.univ : Set (ℝ × ℝ)) = 1 by simp] at hle
    exact hle
  have hηS : η * ρ.real S ≤ η := by
    calc
      η * ρ.real S ≤ η * 1 := mul_le_mul_of_nonneg_left hSle hη
      _ = η := by ring
  have hBSc : (2 * B) * ρ.real Sᶜ ≤ (2 * B) * q :=
    mul_le_mul_of_nonneg_left hbad (by positivity)
  calc
    |(∫ p, u p ∂ρ) - ∫ p, v p ∂ρ| =
        |∫ p, (u p - v p) ∂ρ| := by rw [integral_sub huI hvI]
    _ = |(∫ p in S, (u p - v p) ∂ρ) +
        ∫ p in Sᶜ, (u p - v p) ∂ρ| := by
      rw [integral_add_compl hS hdiffI]
    _ ≤ |∫ p in S, (u p - v p) ∂ρ| +
        |∫ p in Sᶜ, (u p - v p) ∂ρ| := abs_add_le _ _
    _ ≤ η + 2 * B * q := by
      have hsum := add_le_add hSbound' hScbound'
      nlinarith [hηS, hBSc]

/-! State-space version of the substitute estimate.  The good event is only
required to force the prefix parameter into a measurable state set `S`; its
complement is converted to a bad mass for the prefix-state law.  Thus future
path conditions may remain in the event without being (incorrectly) treated
as prefix-measurable. -/
theorem prefixCrossingSubstitute_integral_sub_swingReward_of_state_event
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hGau : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (E r : ℝ) (J : ℕ)
    {f : ℝ → ℝ} (hf : Measurable f) {B δ M η q b₀ : ℝ}
    (hB : 0 ≤ B) (hη : 0 ≤ η) (hδ : 0 < δ) (_hδM : δ ≤ M)
    (hb₀ : 0 < b₀) (hfB : ∀ y, |f y| ≤ B)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hSsupport : ∀ p, p ∈ S → p.1 ∈ Icc δ M ∧ b₀ ≤ p.2)
    (hfibre : ∀ p, p ∈ S →
      |gaussianWalkReflectedReward X μ f p.1 p.2 -
        swingOvershootReward X μ f p.1| ≤ η)
    {G : Set Ω} (hstate : ∀ ω, ω ∈ G →
      prefixCrossingParameter X E r J ω ∈ S)
    (hbad : μ.real Gᶜ ≤ q) :
    |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
        ∫ p, swingOvershootReward X μ f p.1
          ∂(μ.map (prefixCrossingParameter X E r J))| ≤
      η + 2 * B * q := by
  let ρ : Measure (ℝ × ℝ) := μ.map (prefixCrossingParameter X E r J)
  let _ : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map
      (prefixCrossingParameter_measurable hX E r J).aemeasurable
  let u : ℝ × ℝ → ℝ := prefixCrossingProductFibre (X := X) μ f J
  let v : ℝ × ℝ → ℝ := fun p => swingOvershootReward X μ f p.1
  have hu : Measurable u := by
    exact prefixCrossingProductFibre_measurable hf J
  have hreward : Measurable (swingOvershootReward X μ f) :=
    swingOvershootReward_measurable hX hi hf
  have hv : Measurable v := hreward.comp measurable_fst
  have huB : ∀ p, |u p| ≤ B := by
    intro p
    exact prefixCrossingProductFibre_bound hX hfB J p
  have hvB : ∀ p, |v p| ≤ B := by
    intro p
    exact abs_swingOvershootReward_le_of_finite hX hi hf hB hfB p.1
  have hstate_compl :
      (prefixCrossingParameter X E r J ⁻¹' Sᶜ) ⊆ Gᶜ := by
    intro ω hω
    by_contra hωG
    have hmemG : ω ∈ G := by
      simpa only [mem_compl_iff, not_not] using hωG
    exact hω (hstate ω hmemG)
  have hρbad : ρ.real Sᶜ ≤ q := by
    have hmap : ρ Sᶜ =
        μ (prefixCrossingParameter X E r J ⁻¹' Sᶜ) := by
      dsimp [ρ]
      exact Measure.map_apply
        (prefixCrossingParameter_measurable hX E r J) hS.compl
    have hmono := measureReal_mono hstate_compl (measure_ne_top μ _)
    have hreal : ρ.real Sᶜ =
        μ.real (prefixCrossingParameter X E r J ⁻¹' Sᶜ) := by
      unfold Measure.real
      rw [hmap]
    rw [hreal]
    exact hmono.trans hbad
  have hpoint : ∀ᵐ p ∂ρ, p ∈ S → |u p - v p| ≤ η := by
    filter_upwards [] with p hpS
    have hpstrip := hSsupport p hpS
    have ha : 0 < p.1 := lt_of_lt_of_le hδ hpstrip.1.1
    have hb : 0 < p.2 := lt_of_lt_of_le hb₀ hpstrip.2
    have hprod := prefixCrossingProductFibre_eq_reflectedReward
      (X := X) (μ := μ) hX hi hGau E r J hf ⟨ha, hb⟩
    have hfib := hfibre p hpS
    have hu_reflect : u p = gaussianWalkReflectedReward X μ f p.1 p.2 := by
      simpa [u, prefixCrossingProductFibre] using hprod
    dsimp [v]
    rw [hu_reflect]
    exact hfib
  have hdiff := integral_sub_le_of_ae_uniform_bound_on_event
    (ρ := ρ) hu hv hB hη huB hvB hS hpoint hρbad
  have huEq : (∫ p, u p ∂ρ) =
      ∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ := by
    dsimp [u, ρ]
    simpa [prefixCrossingProductFibre] using
      (prefixCrossingSubstitute_integral_eq_independent_product
        (X := X) (μ := μ) hX hi E r J hf hB hfB).symm
  rw [huEq] at hdiff
  simpa [ρ, v] using hdiff

/-! Combining the state-local fibre estimate with the slope localization gives
the corresponding limiting-kernel estimate.  The two exceptional uses of the
good event are kept visible: one costs `2Bq` for the prefix-state fibre and a
second costs `2Bq` when replacing the prefix slope by `A_r`. -/
theorem prefixCrossingSubstitute_integral_sub_swingMarginKernel_of_state_event
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hGau : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (E r : ℝ) (J : ℕ)
    {f : ℝ → ℝ} (hf : Measurable f)
    {B η q δ M b₀ : ℝ} (hB : 0 ≤ B) (hη : 0 ≤ η) (hq : 0 ≤ q)
    (hδ : 0 < δ) (hδM : δ ≤ M) (hb₀ : 0 < b₀)
    (hfB : ∀ y, |f y| ≤ B)
    (hfibre : ∀ a ∈ Icc δ M, ∀ b, b₀ ≤ b →
      |gaussianWalkReflectedReward X μ f a b -
        swingOvershootReward X μ f a| ≤ η)
    {G : Set Ω} (hGmeas : MeasurableSet G)
    (hbad : μ.real Gᶜ ≤ q)
    (hstate : ∀ ω, ω ∈ G →
      prefixCrossingSlope X r J ω ∈ Icc δ M ∧
        b₀ ≤ prefixCrossingLevel X E r J ω)
    (hSlope : ∀ᵐ ω ∂μ, ω ∈ G →
      prefixCrossingSlope X r J ω = swingLimitingSlope X r ω) :
    |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
        ∫ y, f y ∂(swingMarginKernel X μ r)| ≤ η + 4 * B * q := by
  let ρ : Measure (ℝ × ℝ) := μ.map (prefixCrossingParameter X E r J)
  let S : Set (ℝ × ℝ) := Icc δ M ×ˢ Ici b₀
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Ici
  have hstateS : ∀ ω, ω ∈ G →
      prefixCrossingParameter X E r J ω ∈ S := by
    intro ω hω
    exact hstate ω hω
  have hSsupport : ∀ p, p ∈ S → p.1 ∈ Icc δ M ∧ b₀ ≤ p.2 := by
    intro p hp
    exact ⟨hp.1, hp.2⟩
  have hfibreS : ∀ p, p ∈ S →
      |gaussianWalkReflectedReward X μ f p.1 p.2 -
        swingOvershootReward X μ f p.1| ≤ η := by
    intro p hp
    exact hfibre p.1 hp.1 p.2 hp.2
  have hsub := prefixCrossingSubstitute_integral_sub_swingReward_of_state_event
    (X := X) (μ := μ) hX hi hGau E r J hf hB hη hδ hδM hb₀ hfB hS
      hSsupport hfibreS hstateS hbad
  have hreward : Measurable (swingOvershootReward X μ f) :=
    swingOvershootReward_measurable hX hi hf
  have hP : Measurable (prefixCrossingParameter X E r J) :=
    prefixCrossingParameter_measurable hX E r J
  have hprefixV :
      (∫ p, swingOvershootReward X μ f p.1 ∂ρ) =
        ∫ ω, swingOvershootReward X μ f
          (prefixCrossingSlope X r J ω) ∂μ := by
    dsimp [ρ]
    exact integral_map hP.aemeasurable
      ((hreward.comp measurable_fst).aestronglyMeasurable)
  have hRbound : ∀ ω : Ω,
      |swingOvershootReward X μ f (prefixCrossingSlope X r J ω)| ≤ B := by
    intro ω
    exact abs_swingOvershootReward_le_of_finite hX hi hf hB hfB _
  have hLbound : ∀ ω : Ω,
      |swingOvershootReward X μ f (swingLimitingSlope X r ω)| ≤ B := by
    intro ω
    exact abs_swingOvershootReward_le_of_finite hX hi hf hB hfB _
  have hslopediff :
      |(∫ ω, swingOvershootReward X μ f
          (prefixCrossingSlope X r J ω) ∂μ) -
        ∫ ω, swingOvershootReward X μ f
          (swingLimitingSlope X r ω) ∂μ| ≤ 2 * B * q := by
    have htmp := abs_integral_sub_le_of_eq_on_event
      (μ := μ)
      (u := fun ω => swingOvershootReward X μ f
        (prefixCrossingSlope X r J ω))
      (v := fun ω => swingOvershootReward X μ f
        (swingLimitingSlope X r ω))
      (hreward.comp (prefixCrossingSlope_measurable hX r J))
      (hreward.comp (swingLimitingSlope_measurable hX r)) hB
      hRbound hLbound hGmeas
    have heq : ∀ᵐ ω ∂μ, ω ∈ G →
        swingOvershootReward X μ f (prefixCrossingSlope X r J ω) =
          swingOvershootReward X μ f (swingLimitingSlope X r ω) := by
      filter_upwards [hSlope] with ω hω hωG
      rw [hω hωG]
    have htmp' := htmp heq
    exact htmp'.trans (mul_le_mul_of_nonneg_left hbad (by positivity))
  have hkernel :
      (∫ y, f y ∂(swingMarginKernel X μ r)) =
        ∫ ω, swingOvershootReward X μ f
          (swingLimitingSlope X r ω) ∂μ :=
    swingMarginKernel_integral_eq hX hi hGau r hf hfB
  have hcombine :
      |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
          ∫ ω, swingOvershootReward X μ f
            (swingLimitingSlope X r ω) ∂μ| ≤ η + 4 * B * q := by
    have hqnonneg : 0 ≤ 4 * B * q := by
      exact mul_nonneg (mul_nonneg (by norm_num) hB) hq
    have hfirst :
        |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
            ∫ p, swingOvershootReward X μ f p.1 ∂ρ| ≤ η + 2 * B * q := by
      simpa [ρ] using hsub
    have hsecond :
        |(∫ p, swingOvershootReward X μ f p.1 ∂ρ) -
            ∫ ω, swingOvershootReward X μ f
              (swingLimitingSlope X r ω) ∂μ| ≤ 2 * B * q := by
      rw [hprefixV]
      exact hslopediff
    calc
      _ ≤
          |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
              ∫ p, swingOvershootReward X μ f p.1 ∂ρ| +
            |(∫ p, swingOvershootReward X μ f p.1 ∂ρ) -
              ∫ ω, swingOvershootReward X μ f
                (swingLimitingSlope X r ω) ∂μ| := by
        have hid :
            (∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
                ∫ ω, swingOvershootReward X μ f
                  (swingLimitingSlope X r ω) ∂μ =
              ((∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
                ∫ p, swingOvershootReward X μ f p.1 ∂ρ) +
              ((∫ p, swingOvershootReward X μ f p.1 ∂ρ) -
                ∫ ω, swingOvershootReward X μ f
                  (swingLimitingSlope X r ω) ∂μ) := by
          ring
        rw [hid]
        exact abs_add_le _ _
      _ ≤ η + 4 * B * q := by linarith [hqnonneg]
  rw [hkernel]
  exact hcombine

/-! A concrete local-kernel estimate.  The support condition is the exact
finite-prefix localization input: on that support the product fibre is the
reflected finite-level reward, and the supplied fibre estimate compares it to
the equilibrium reward. -/
theorem prefixCrossingSubstitute_integral_sub_swingReward_of_fibre
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (E r : ℝ) (J : ℕ)
    {f : ℝ → ℝ} (hf : Measurable f) {B δ M η b₀ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 < δ) (_hδM : δ ≤ M) (hb₀ : 0 < b₀)
    (hfB : ∀ y, |f y| ≤ B)
    (hsupport : ∀ᵐ p ∂(μ.map (prefixCrossingParameter X E r J)),
      p.1 ∈ Icc δ M ∧ b₀ ≤ p.2)
    (hfibre : ∀ a ∈ Icc δ M, ∀ b, b₀ ≤ b →
      |gaussianWalkReflectedReward X μ f a b -
        swingOvershootReward X μ f a| ≤ η) :
    |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
        ∫ p, swingOvershootReward X μ f p.1
          ∂(μ.map (prefixCrossingParameter X E r J))| ≤ η := by
  let ρ : Measure (ℝ × ℝ) := μ.map (prefixCrossingParameter X E r J)
  let _ : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map
      (prefixCrossingParameter_measurable hX E r J).aemeasurable
  let u : ℝ × ℝ → ℝ := prefixCrossingProductFibre (X := X) μ f J
  let v : ℝ × ℝ → ℝ := fun p =>
    if 0 < p.1 then swingOvershootReward X μ f p.1 else 0
  have hu : Measurable u := by
    exact prefixCrossingProductFibre_measurable hf J
  have hvr : Measurable (swingOvershootReward X μ f) :=
    swingOvershootReward_measurable hX hi hf
  have hv : Measurable v := by
    exact Measurable.ite
      (measurableSet_lt measurable_const measurable_fst)
      (hvr.comp measurable_fst) measurable_const
  have huB : ∀ p, |u p| ≤ B := by
    intro p
    exact prefixCrossingProductFibre_bound hX hfB J p
  have hvB : ∀ p, |v p| ≤ B := by
    intro p
    by_cases hp : 0 < p.1
    · dsimp [v]
      rw [if_pos hp]
      exact abs_swingOvershootReward_le hX hi hG hp hf hfB
    · simp [v, hp, hB]
  have hsupport' : ∀ᵐ p ∂ρ,
      p.1 ∈ Icc δ M ∧ b₀ ≤ p.2 := by
    simpa [ρ] using hsupport
  have hpoint : ∀ᵐ p ∂ρ, |u p - v p| ≤ η := by
    filter_upwards [hsupport'] with p hp
    have ha : 0 < p.1 := lt_of_lt_of_le hδ hp.1.1
    have hb : 0 < p.2 := lt_of_lt_of_le hb₀ hp.2
    have hprod := prefixCrossingProductFibre_eq_reflectedReward
      (X := X) (μ := μ) hX hi hG E r J hf ⟨ha, hb⟩
    have hfib := hfibre p.1 hp.1 p.2 hp.2
    have hu_reflect : u p = gaussianWalkReflectedReward X μ f p.1 p.2 := by
      simpa [u, prefixCrossingProductFibre] using hprod
    dsimp [v]
    rw [if_pos ha, hu_reflect]
    exact hfib
  have hdiff := integral_sub_le_of_ae_uniform_bound
    (ρ := ρ) hu hv huB hvB hpoint
  have huEq : (∫ p, u p ∂ρ) =
      ∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ := by
    dsimp [u, ρ]
    simpa [prefixCrossingProductFibre] using
      (prefixCrossingSubstitute_integral_eq_independent_product
        (X := X) (μ := μ) hX hi E r J hf hB hfB).symm
  have hvEq : (∫ p, v p ∂ρ) =
      ∫ p, swingOvershootReward X μ f p.1 ∂ρ := by
    apply integral_congr_ae
    filter_upwards [hsupport'] with p hp
    have ha : 0 < p.1 := lt_of_lt_of_le hδ hp.1.1
    simp [v, ha]
  rw [huEq, hvEq] at hdiff
  simpa [ρ] using hdiff

/-! A bounded-Lipschitz wrapper for the preceding conditional estimate.  The
renewal expansion chooses a single passage threshold uniformly over all
`a ∈ [δ,M]` and all tests with Lipschitz constant `K` and bound `B`.  The
prefix-law support is deliberately left as an implication in the conclusion:
this theorem does not claim that the bridge/localization event supplies that
support automatically. -/
theorem exists_prefixCrossingSubstitute_integral_sub_swingReward_uniform_of_support
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M C c K B η : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M) (hc : 0 < c)
    (hexp : UniformLadderRenewalExpansion
      (gaussianAscendingLadderLaw X μ) (Icc δ M) C c)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hη : 0 < η)
    (E r : ℝ) (J : ℕ) {f : ℝ → ℝ}
    (hfl : ∀ x y : ℝ, |f x - f y| ≤ K * |x - y|)
    (hfB : ∀ x, |f x| ≤ B) :
    ∃ b₀ : ℝ, 0 < b₀ ∧
      ((∀ᵐ p ∂(μ.map (prefixCrossingParameter X E r J)),
          p.1 ∈ Icc δ M ∧ b₀ ≤ p.2) →
        |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
            ∫ p, swingOvershootReward X μ f p.1
              ∂(μ.map (prefixCrossingParameter X E r J))| ≤ η) := by
  obtain ⟨bstar, hbstar⟩ := gaussianWalkReflectedReward_lipschitz_uniform
    (X := X) (μ := μ) hX hi hG hδ hc hexp hK hB hη
  let b₀ : ℝ := max bstar 1
  have hb₀ : 0 < b₀ := by
    dsimp [b₀]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have huniform : ∀ a ∈ Icc δ M, ∀ b : ℝ, b₀ ≤ b →
      |gaussianWalkReflectedReward X μ f a b -
          swingOvershootReward X μ f a| ≤ η := by
    intro a ha b hb
    have hbb : bstar ≤ b :=
      le_trans (le_max_left _ _) hb
    have hfLip : LipschitzWith ⟨K, hK⟩ f := by
      refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
      change |f x - f y| ≤ K * |x - y|
      exact hfl x y
    exact hbstar a ha b hbb f hfl hfB
  have hf : Measurable f := by
    have hfLip : LipschitzWith ⟨K, hK⟩ f := by
      refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
      change |f x - f y| ≤ K * |x - y|
      exact hfl x y
    exact hfLip.continuous.measurable
  refine ⟨b₀, hb₀, ?_⟩
  intro hsupport
  exact prefixCrossingSubstitute_integral_sub_swingReward_of_fibre
    (X := X) (μ := μ) hX hi hG E r J hf hB hδ hδM hb₀ hfB hsupport
      (fun a ha b hb => huniform a ha b hb)

/-! The preceding estimate still integrates the equilibrium reward against the
finite-prefix slope law.  The following wrapper supplies the missing local
kernel step explicitly: on a measurable good event the finite prefix slope is
the limiting slope, while the complement has controlled mass.  Every
exceptional nonpositive slope is clipped to zero in the comparison; the
prefix support and the a.e. positivity of the limiting slope then remove the
clipping from the two displayed integrals. -/
theorem prefixCrossingSubstitute_integral_sub_swingMarginKernel_of_event
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hGau : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (E r : ℝ) (J : ℕ)
    {f : ℝ → ℝ} (hf : Measurable f) {B δ M η q b₀ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 < δ) (hδM : δ ≤ M) (hb₀ : 0 < b₀)
    (hfB : ∀ y, |f y| ≤ B)
    (hsupport : ∀ᵐ p ∂(μ.map (prefixCrossingParameter X E r J)),
      p.1 ∈ Icc δ M ∧ b₀ ≤ p.2)
    (hfibre : ∀ a ∈ Icc δ M, ∀ b, b₀ ≤ b →
      |gaussianWalkReflectedReward X μ f a b -
        swingOvershootReward X μ f a| ≤ η)
    {G : Set Ω} (hGmeas : MeasurableSet G)
    (hSlope : ∀ᵐ ω ∂μ, ω ∈ G →
      prefixCrossingSlope X r J ω = swingLimitingSlope X r ω)
    (hbad : μ.real Gᶜ ≤ q) :
    |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
        ∫ y, f y ∂(swingMarginKernel X μ r)| ≤ η + 2 * B * q := by
  let ρ : Measure (ℝ × ℝ) := μ.map (prefixCrossingParameter X E r J)
  let R : ℝ → ℝ := fun a =>
    if 0 < a then swingOvershootReward X μ f a else 0
  have hRmeas : Measurable R := by
    have hreward : Measurable (swingOvershootReward X μ f) :=
      swingOvershootReward_measurable hX hi hf
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      hreward measurable_const
  have hRB : ∀ a : ℝ, |R a| ≤ B := by
    intro a
    by_cases ha : 0 < a
    · simp only [R, if_pos ha]
      exact abs_swingOvershootReward_le hX hi hGau ha hf hfB
    · simp [R, ha, hB]
  have hprefix_reward :
      (∫ p, swingOvershootReward X μ f p.1 ∂ρ) =
        ∫ p, R p.1 ∂ρ := by
    have hs : ∀ᵐ p ∂ρ, p.1 ∈ Icc δ M ∧ b₀ ≤ p.2 := by
      simpa [ρ] using hsupport
    apply integral_congr_ae
    filter_upwards [hs] with p hp
    have ha : 0 < p.1 := lt_of_lt_of_le hδ hp.1.1
    simp [R, ha]
  have hmap_prefix :
      (∫ p, R p.1 ∂ρ) =
        ∫ ω, R (prefixCrossingSlope X r J ω) ∂μ := by
    dsimp [ρ]
    exact integral_map
      (prefixCrossingParameter_measurable hX E r J).aemeasurable
      ((hRmeas.comp measurable_fst).aestronglyMeasurable)
  have hmap_limit :
      (∫ ω, R (swingLimitingSlope X r ω) ∂μ) =
        ∫ ω, swingOvershootReward X μ f (swingLimitingSlope X r ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [swingLimitingSlope_pos_ae hX hi hGau r] with ω hω
    simp [R, hω]
  have hprefix_limit :
      |(∫ ω, R (prefixCrossingSlope X r J ω) ∂μ) -
          ∫ ω, R (swingLimitingSlope X r ω) ∂μ| ≤
        2 * B * (μ.real Gᶜ) := by
    apply abs_integral_sub_le_of_eq_on_event
      (u := fun ω => R (prefixCrossingSlope X r J ω))
      (v := fun ω => R (swingLimitingSlope X r ω))
      (hRmeas.comp (prefixCrossingSlope_measurable hX r J))
      (hRmeas.comp (swingLimitingSlope_measurable hX r)) hB
      (fun ω => hRB _) (fun ω => hRB _) hGmeas
    filter_upwards [hSlope] with ω hω hωG
    rw [hω hωG]
  have hkernel :
      (∫ y, f y ∂(swingMarginKernel X μ r)) =
        ∫ ω, swingOvershootReward X μ f (swingLimitingSlope X r ω) ∂μ := by
    exact swingMarginKernel_integral_eq hX hi hGau r hf hfB
  have hsub := prefixCrossingSubstitute_integral_sub_swingReward_of_fibre
    (X := X) (μ := μ) hX hi hGau E r J hf hB hδ hδM hb₀ hfB
      hsupport hfibre
  have hmid :
      |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
          ∫ ω, swingOvershootReward X μ f (swingLimitingSlope X r ω) ∂μ| ≤
        η + 2 * B * q := by
    have hfirst :
        |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
            ∫ ω, R (prefixCrossingSlope X r J ω) ∂μ| ≤ η := by
      rw [← hmap_prefix, ← hprefix_reward]
      exact hsub
    have hsecond :
        |(∫ ω, R (prefixCrossingSlope X r J ω) ∂μ) -
            ∫ ω, swingOvershootReward X μ f (swingLimitingSlope X r ω) ∂μ| ≤
          2 * B * q := by
      rw [← hmap_limit]
      exact (hprefix_limit.trans (mul_le_mul_of_nonneg_left hbad (by positivity)))
    calc
      _ ≤
          |(∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
              ∫ ω, R (prefixCrossingSlope X r J ω) ∂μ| +
            |(∫ ω, R (prefixCrossingSlope X r J ω) ∂μ) -
              ∫ ω, swingOvershootReward X μ f (swingLimitingSlope X r ω) ∂μ| := by
        have hid :
            (∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
                ∫ ω, swingOvershootReward X μ f (swingLimitingSlope X r ω) ∂μ =
              ((∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ) -
                ∫ ω, R (prefixCrossingSlope X r J ω) ∂μ) +
              ((∫ ω, R (prefixCrossingSlope X r J ω) ∂μ) -
                ∫ ω, swingOvershootReward X μ f (swingLimitingSlope X r ω) ∂μ) := by
          ring
        rw [hid]
        exact abs_add_le _ _
      _ ≤ η + 2 * B * q := add_le_add hfirst hsecond
  rw [hkernel]
  exact hmid

end SwingRepair
