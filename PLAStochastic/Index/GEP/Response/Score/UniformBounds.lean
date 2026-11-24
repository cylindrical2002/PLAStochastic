import PLAStochastic.Index.GEP.Response.Score.MixturePath
import PLAStochastic.Index.GEP.OrbitClosure.OneLayerEnvelope
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass

/-!
# WP4 leaf 4A-S, part 4: uniform bounds on the regular class

Inputs of the score calculus that hold uniformly on `RegLaw D θ vlo vhi` for large `eps`
(`joint-response.md` §5: "有限停止截断与统一指数尾"):

* `lintegral_exp_toNat_le`: a geometric tail `P(N > m) ≤ K a^m` gives
  `E e^{κN} ≤ 1 + (e^κ - 1) K / (1 - e^κ a)` when `e^κ a < 1`;
* `regLaw_facts`: for `eps ≥ e0` and every law of the class, `T < ∞` a.s., the stopping tail
  `P(T > m) ≤ (72/71) a_ε^m` (`gapSegLen_tail`), the lower bound `ε²/(128 b) ≤ C_ε`
  (`momClass_oneLayer`), the output moment `E e^{θK Y} ≤ CK` (`lawPhi_expMom`), absolute
  continuity of the output law (`lawPhi_envelope`) and `S_T > 0` a.s. (`lawPhi_momClass`);
* output tests: `testFn ψ` is the primitive of `ψ 1_{(0,∞)}` (`testFn_eq_primitive`), hence
  continuous, locally Lipschitz with `|φ(a) - φ(b)| ≤ M e^{η max(a,b)} |a - b|`, and
  differentiable with derivative `ψ` at Lebesgue-a.e. point of `(0,∞)`
  (`LocallyIntegrable.ae_hasDerivAt_integral`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

/-! ## Exponential moments from a geometric tail -/

theorem ofReal_exp_nat_eq {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) :
    ENNReal.ofReal (Real.exp (κ * n)) =
      1 + ∑' m : ℕ, (if m < n then ENNReal.ofReal ((Real.exp κ - 1) * Real.exp κ ^ m) else 0) := by
  have h1 : 1 ≤ Real.exp κ := Real.one_le_exp hκ
  rw [tsum_eq_sum (s := Finset.range n) (fun m hm => by
    rw [Finset.mem_range] at hm; simp [hm])]
  rw [Finset.sum_congr rfl (fun m hm => by rw [if_pos (Finset.mem_range.1 hm)]),
    ← ENNReal.ofReal_sum_of_nonneg (fun m _ => mul_nonneg (by linarith) (by positivity)),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
      (Finset.sum_nonneg fun m _ => mul_nonneg (by linarith) (by positivity))]
  congr 1
  rw [← Finset.mul_sum, mul_comm (Real.exp κ - 1), geom_sum_mul, ← Real.exp_nat_mul,
    mul_comm (n : ℝ) κ]
  ring

/-- **Exponential moment from a geometric tail.** -/
theorem lintegral_exp_toNat_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {N : Ω → ℕ∞} (hN : Measurable N) (hfin : ∀ᵐ ω ∂P, N ω ≠ ⊤)
    {K a κ : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a)
    (htail : ∀ m : ℕ, P {ω | (m : ℕ∞) < N ω} ≤ ENNReal.ofReal (K * a ^ m))
    (hκ : 0 ≤ κ) (hκa : Real.exp κ * a < 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (κ * (N ω).toNat)) ∂P ≤
      ENNReal.ofReal (1 + (Real.exp κ - 1) * K / (1 - Real.exp κ * a)) := by
  have h1 : 1 ≤ Real.exp κ := Real.one_le_exp hκ
  set c : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal ((Real.exp κ - 1) * Real.exp κ ^ m) with hc
  have hmeas : ∀ m : ℕ, MeasurableSet {ω | (m : ℕ∞) < N ω} := fun m =>
    hN (Set.to_countable (Set.Ioi (m : ℕ∞))).measurableSet
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (κ * (N ω).toNat)) =
      1 + ∑' m : ℕ, {ω | (m : ℕ∞) < N ω}.indicator (fun _ => c m) ω := by
    filter_upwards [hfin] with ω hω
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hω
    rw [← hn, ENat.toNat_natCast, ofReal_exp_nat_eq hκ n]
    congr 1
    refine tsum_congr fun m => ?_
    by_cases hm : m < n
    · rw [if_pos hm, Set.indicator_of_mem (show ω ∈ {ω | (m : ℕ∞) < N ω} by
        simp only [Set.mem_ofPred_eq, ← hn, Nat.cast_lt]; exact hm)]
    · rw [if_neg hm, Set.indicator_of_notMem (show ω ∉ {ω | (m : ℕ∞) < N ω} by
        simp only [Set.mem_ofPred_eq, ← hn, Nat.cast_lt]; exact hm)]
  have hr0 : 0 ≤ Real.exp κ * a := by positivity
  have hsum : Summable fun m : ℕ => (Real.exp κ - 1) * K * (Real.exp κ * a) ^ m :=
    (summable_geometric_of_lt_one hr0 hκa).mul_left _
  rw [lintegral_congr_ae hpt, lintegral_add_left measurable_const, lintegral_const,
    measure_univ, one_mul, lintegral_tsum fun m => (measurable_const.indicator (hmeas m)).aemeasurable]
  simp_rw [lintegral_indicator_const (hmeas _)]
  calc 1 + ∑' m : ℕ, c m * P {ω | (m : ℕ∞) < N ω}
      ≤ 1 + ∑' m : ℕ, ENNReal.ofReal ((Real.exp κ - 1) * K * (Real.exp κ * a) ^ m) := by
        gcongr with m
        refine (mul_le_mul_right (htail m) _).trans (le_of_eq ?_)
        rw [hc, ← ENNReal.ofReal_mul (mul_nonneg (by linarith) (by positivity))]
        congr 1
        ring
    _ = 1 + ENNReal.ofReal (∑' m : ℕ, (Real.exp κ - 1) * K * (Real.exp κ * a) ^ m) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun m => by
          have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ Real.exp κ - 1) hK)
            (pow_nonneg hr0 m)
          exact this) hsum]
    _ = ENNReal.ofReal (1 + (Real.exp κ - 1) * K / (1 - Real.exp κ * a)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hκa, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (by
            have : 0 < 1 - Real.exp κ * a := by linarith
            have : 0 ≤ (Real.exp κ - 1) * K := mul_nonneg (by linarith) hK
            positivity)]
        congr 1

/-! ## Uniform facts on the regular class -/

variable {D θ vlo vhi : ℝ}

/-- The geometric ratio of the stopping tail on the class, `exp(-tailRate · v / ε²)`. -/
def tailA (vlo eps : ℝ) : ℝ := Real.exp (-(tailRate * regV vlo) / eps ^ 2)

theorem tailA_pos (vlo eps : ℝ) : 0 < tailA vlo eps := Real.exp_pos _

theorem tailA_lt_one (hvlo : 0 < vlo) {eps : ℝ} (heps : eps ≠ 0) : tailA vlo eps < 1 := by
  rw [tailA, Real.exp_lt_one_iff, neg_div, neg_lt_zero]
  have := regV_pos hvlo
  have := tailRate_pos
  positivity

/-- **Uniform facts on the class** for `eps ≥ e0`. -/
theorem regLaw_facts (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ e0 : ℝ, 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν →
        (∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤) ∧
        eps ^ 2 / (128 * regB vhi) ≤ lawC eps ν ∧
        (∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
          ENNReal.ofReal (72 / 71 * tailA vlo eps ^ m)) ∧
        ExpMom θK CK (lawPhi eps ν) ∧
        (lawPhi eps ν : Measure ℝ) ≪ volume ∧
        (∀ᵐ g ∂(iidLaw ν), 0 < stopSum eps g) := by
  have hv0 := regV_pos hvlo
  have hB : 0 < 2 * D / θ := by positivity
  obtain ⟨e₂, he₂⟩ := lawPhi_expMom (b := regB vhi) (β := regBeta D θ vlo) hv0 (half_pos hθ) hB
  obtain ⟨K, c, -, -, henv⟩ := lawPhi_envelope (b := regB vhi) (β := regBeta D θ vlo)
    hv0 (regV_le_regB hv) (one_le_regBeta D θ vlo) (half_pos hθ) hB
  obtain ⟨e₁, he₁⟩ := henv D hD
  refine ⟨max (max 1 (epsZero (regB vhi) (regBeta D θ vlo))) (max e₁ e₂), le_trans
    (le_max_left _ _) (le_max_left _ _), fun eps heps ν hν => ?_⟩
  have hez : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have he1 : e₁ ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) heps
  have he2 : e₂ ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) heps
  have heps1 : 1 ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have hm := hν.momClass hθ hvlo
  have hexp := hν.expMom hθ
  obtain ⟨hfin, hCm, -⟩ := momClass_oneLayer hv0 hez hm
  have hb0 : 0 < regB vhi := hv0.trans_le (regV_le_regB hv)
  have hCpos : 0 < lawC eps ν := lt_of_lt_of_le (by positivity) hCm
  refine ⟨hfin, hCm, fun m => ?_, he₂ eps he2 ν hm hexp, ?_, ?_⟩
  · refine (gapSegLen_tail hv0 hez hm m).trans (le_of_eq ?_)
    congr 1
    rw [tailA, ← Real.exp_nat_mul]
    congr 2
    ring
  · have hE := he₁ eps he1 ν hm hexp (hν.envBd.locBd hD.le hθ.le)
    exact (Measure.absolutelyContinuous_of_le hE).trans (withDensity_absolutelyContinuous _ _)
  · have hm' := lawPhi_momClass (bAbs_le_regB vhi) (βAbs_le_regBeta D θ vlo) hv0
      (regV_le_half vlo) hez hm
    have hpos := hm'.pos
    have hSm : Measurable fun g => stopSum eps g / lawC eps ν :=
      (measurable_stopSum eps).div_const _
    change ((iidLaw ν).map fun g => stopSum eps g / lawC eps ν) (Iic 0) = 0 at hpos
    rw [Measure.map_apply hSm measurableSet_Iic] at hpos
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hpos] with g hg
    simp only [Set.mem_preimage, Set.mem_Iic, not_le] at hg
    exact (div_pos_iff_of_pos_right hCpos).1 hg

/-! ## Output tests -/

/-- The test derivative restricted to `(0,∞)`. -/
def psiPos (ψ : ℝ → ℝ) : ℝ → ℝ := (Ioi (0 : ℝ)).indicator ψ

variable {η M : ℝ} {ψ : ℝ → ℝ}

theorem OutTest.measurable_psiPos (hψ : OutTest η M ψ) : Measurable (psiPos ψ) :=
  hψ.1.indicator measurableSet_Ioi

theorem OutTest.abs_psiPos_le (hψ : OutTest η M ψ) (x : ℝ) :
    |psiPos ψ x| ≤ M * Real.exp (η * |x|) := by
  by_cases hx : 0 < x
  · rw [psiPos, Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), abs_of_pos hx]
    exact hψ.2 x hx.le
  · rw [psiPos, Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), abs_zero]
    exact mul_nonneg hψ.nonneg (Real.exp_pos _).le

theorem OutTest.locallyIntegrable_psiPos (hψ : OutTest η M ψ) :
    LocallyIntegrable (psiPos ψ) volume := by
  have hc : Continuous fun x : ℝ => M * Real.exp (η * |x|) := by fun_prop
  refine hc.locallyIntegrable.mono hψ.measurable_psiPos.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hψ.nonneg (Real.exp_pos _).le)]
  exact hψ.abs_psiPos_le x

/-- `testFn ψ` is the primitive of `ψ 1_{(0,∞)}` from `0`. -/
theorem testFn_eq_primitive (ψ : ℝ → ℝ) (y : ℝ) :
    testFn ψ y = ∫ t in (0 : ℝ)..y, psiPos ψ t := by
  rcases le_or_gt 0 y with hy | hy
  · rw [intervalIntegral.integral_of_le hy, testFn, ← integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [psiPos, Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht.1)]
  · rw [intervalIntegral.integral_of_ge hy.le, testFn, Set.Ioo_eq_empty (by linarith),
      Measure.restrict_empty, integral_zero_measure]
    have : ∫ t in Ioc y 0, psiPos ψ t = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      rw [psiPos, Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.2 ht.2)]
    rw [this, neg_zero]

theorem OutTest.intervalIntegrable (hψ : OutTest η M ψ) (a b : ℝ) :
    IntervalIntegrable (psiPos ψ) volume a b :=
  intervalIntegrable_iff.mpr <| (hψ.locallyIntegrable_psiPos.integrableOn_isCompact
    isCompact_uIcc).mono_set uIoc_subset_uIcc

theorem OutTest.continuous_testFn (hψ : OutTest η M ψ) : Continuous (testFn ψ) := by
  have h : testFn ψ = fun y => ∫ t in (0 : ℝ)..y, psiPos ψ t := funext (testFn_eq_primitive ψ)
  rw [h]
  exact intervalIntegral.continuous_primitive (fun a b => hψ.intervalIntegrable a b) 0

theorem OutTest.measurable_testFn (hψ : OutTest η M ψ) : Measurable (testFn ψ) :=
  hψ.continuous_testFn.measurable

/-- **Lebesgue differentiation for the test**: at a.e. `y > 0`, `φ_ψ' (y) = ψ(y)`. -/
theorem OutTest.ae_hasDerivAt_testFn (hψ : OutTest η M ψ) :
    ∀ᵐ y ∂(volume : Measure ℝ), 0 < y → HasDerivAt (testFn ψ) (ψ y) y := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hψ.locallyIntegrable_psiPos]
    with y hy hy0
  have h : testFn ψ = fun y => ∫ t in (0 : ℝ)..y, psiPos ψ t := funext (testFn_eq_primitive ψ)
  have := hy 0
  rw [psiPos, Set.indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy0)] at this
  rw [h]
  exact this

/-- The local Lipschitz bound of the test: `|φ(a) - φ(b)| ≤ M e^{η max(a,b)} |a - b|`. -/
theorem OutTest.abs_testFn_sub_le (hψ : OutTest η M ψ) (hη : 0 ≤ η) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    |testFn ψ a - testFn ψ b| ≤ M * Real.exp (η * max a b) * |a - b| := by
  rw [testFn_eq_primitive, testFn_eq_primitive,
    intervalIntegral.integral_interval_sub_left (hψ.intervalIntegrable 0 a)
      (hψ.intervalIntegrable 0 b), ← Real.norm_eq_abs (∫ x in b..a, psiPos ψ x)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Real.norm_eq_abs]
  refine (hψ.abs_psiPos_le x).trans ?_
  have hx' : x ∈ Set.uIcc b a := Set.uIoc_subset_uIcc hx
  have hx0 : |x| ≤ max a b := by
    rw [Set.mem_uIcc] at hx'
    rw [abs_le]
    constructor
    · rcases hx' with h | h <;> linarith [le_max_left a b, le_max_right a b]
    · rcases hx' with h | h
      · exact h.2.trans (le_max_left _ _)
      · exact h.2.trans (le_max_right _ _)
  gcongr
  exact hψ.nonneg

theorem OutTest.abs_testFn_le (hψ : OutTest η M ψ) (hη : 0 ≤ η) {y : ℝ} (hy : 0 ≤ y) :
    |testFn ψ y| ≤ M * Real.exp (η * y) * y := by
  have h := hψ.abs_testFn_sub_le hη hy le_rfl
  have h0 : testFn ψ 0 = 0 := by rw [testFn, Set.Ioo_self, Measure.restrict_empty,
    integral_zero_measure]
  rwa [h0, sub_zero, max_eq_left hy, sub_zero, abs_of_nonneg hy] at h

/-! ## Real forms of the stopping moment -/

/-- The exponential moment of the stopping time on the class, in real form. -/
theorem integrable_exp_gapSegLen {ν : ProbabilityMeasure ℝ} {eps K a κ : ℝ}
    (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤ ENNReal.ofReal (K * a ^ m))
    (hκ : 0 ≤ κ) (hκa : Real.exp κ * a < 1) :
    Integrable (fun g => Real.exp (κ * (gapSegLen eps g).toNat)) (iidLaw ν) ∧
      ∫ g, Real.exp (κ * (gapSegLen eps g).toNat) ∂(iidLaw ν) ≤
        1 + (Real.exp κ - 1) * K / (1 - Real.exp κ * a) := by
  have hl := lintegral_exp_toNat_le (isStoppingRule_gapSegLen eps).measurable hfin hK ha htail
    hκ hκa
  have hm : Measurable fun g : ℕ → ℝ => Real.exp (κ * (gapSegLen eps g).toNat) :=
    Real.measurable_exp.comp (measurable_const.mul (measurable_toNat_gapSegLen eps))
  have hint : Integrable (fun g => Real.exp (κ * (gapSegLen eps g).toNat)) (iidLaw ν) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun g => (Real.exp_pos _).le)]
    exact lt_of_le_of_lt hl ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun g => (Real.exp_pos _).le)
    hm.aestronglyMeasurable]
  have h0 : 0 ≤ 1 + (Real.exp κ - 1) * K / (1 - Real.exp κ * a) := by
    have : 0 < 1 - Real.exp κ * a := by linarith
    have : 0 ≤ Real.exp κ - 1 := by linarith [Real.one_le_exp hκ]
    positivity
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hl).trans (ENNReal.toReal_ofReal h0).le

end

end PGM
