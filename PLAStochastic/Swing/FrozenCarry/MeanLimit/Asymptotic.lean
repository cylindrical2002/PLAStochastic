import PLAStochastic.Swing.FrozenCarry.MeanLimit.OmittedRangeBound

/-! # The exact conditional logarithmic mean asymptotic

The mean of the actual maximal frozen Gaussian prefix, divided by E log E,
converges to 4 V(w), uniformly on compact subsets of the nonnegative carried states.
The proof sums the actual survival probabilities and controls every omitted range.
-/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set Finset
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem frozenMeanLimit_error_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ici 0)
    {M B : ℝ} (hM : 0 ≤ M) (_hB : 0 ≤ B)
    (hVM : ∀ w ∈ K, |gaussianRenewalPotential X μ w| ≤ M)
    (hWB : ∀ w ∈ K, frozenHarmonicTailConstant*(1+max w 0) ≤ B)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) (hε : 0 < ε) :
    ∀ᶠ E : ℝ in atTop, ∀ w ∈ K,
      |(∫ ω, frozenPrefixLengthReal X w E ω ∂μ)-
          4*gaussianRenewalPotential X μ w*(E*Real.log E)| ≤
        E*((ε+δ*(8*M+2*B))*Real.log E+
          (2*ε+8*M+2+B*(5+18/(1-gaussianBlockPass.toReal)))) := by
  filter_upwards [frozen_interior_range_sum hX hi hG hδ hK hK0 hε,
    eventually_ge_atTop (1 : ℝ)] with E hsum hE
  intro w hw
  have hEp : 0 < E := by linarith
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE
  have hq : 0 < 1-gaussianBlockPass.toReal := sub_pos.mpr frozen_block_ratio_lt_one
  let a : ℕ := frozenInteriorLow δ E
  let b : ℕ := frozenInteriorHigh δ E
  let V : ℝ := gaussianRenewalPotential X μ w
  let I : ℝ := ∑ n ∈ Finset.Ico a b,
    μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω}
  let g : ℝ := ∫ ω, frozenPrefixLengthReal X w E ω ∂μ
  let L : ℝ := Real.log (b : ℝ)-Real.log (a : ℝ)
  obtain ⟨hc, hca, hab, _⟩ := frozenMeanLimit_endpoint_order hδ.le hδ4 hE
  have ha : 1 ≤ a := hc.trans hca
  have hI : |I-4*V*E*L| ≤ E*(ε*(|L|+1)+|4*V|) :=
    hsum w hw a b ha hab (fun n hn => frozenInteriorRange_mem hEp.le hn)
  have hwidth : |L-(1-2*δ)*Real.log E| ≤ Real.log 2 :=
    frozenInteriorRange_log_width hδ.le (by linarith) hE
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hL : |L| ≤ Real.log E+1 := by
    have hh := abs_le.mp hwidth
    have hδlog := mul_nonneg hδ.le hlog
    rw [abs_le]
    constructor <;> nlinarith
  have hdiff : |L-Real.log E| ≤ 1+2*δ*Real.log E := by
    calc
      _ ≤ |L-(1-2*δ)*Real.log E|+|(1-2*δ)*Real.log E-Real.log E| := abs_sub_le _ _ _
      _ = |L-(1-2*δ)*Real.log E|+2*δ*Real.log E := by
        congr 1
        rw [show (1-2*δ)*Real.log E-Real.log E = -(2*δ*Real.log E) by ring,
          abs_neg, abs_of_nonneg (by positivity)]
      _ ≤ _ := by linarith
  have hV4 : |4*V| ≤ 4*M := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    exact mul_le_mul_of_nonneg_left (hVM w hw) (by norm_num)
  have hIfirst : |I-4*V*E*L| ≤ E*(ε*(Real.log E+2)+4*M) := by
    refine hI.trans (mul_le_mul_of_nonneg_left ?_ hEp.le)
    have := mul_le_mul_of_nonneg_left (show |L|+1 ≤ Real.log E+2 by linarith) hε.le
    linarith
  have hIsecond : |4*V*E*L-4*V*(E*Real.log E)| ≤ E*(4*M+8*M*δ*Real.log E) := by
    rw [show 4*V*E*L-4*V*(E*Real.log E) = E*((4*V)*(L-Real.log E)) by ring,
      abs_mul, abs_of_nonneg hEp.le, abs_mul]
    calc
      _ ≤ E*(4*M*(1+2*δ*Real.log E)) := by gcongr
      _ = _ := by ring
  have hIerr : |I-4*V*(E*Real.log E)| ≤ E*((ε+8*M*δ)*Real.log E+2*ε+8*M) := by
    have hh := (abs_sub_le I (4*V*E*L) (4*V*(E*Real.log E))).trans (add_le_add hIfirst hIsecond)
    nlinarith only [hh]
  have hIg : I ≤ g := frozen_range_sum_le_mean hX hi hG w hEp ha
  have hrem := frozenMeanLimit_remainder_bound hX hi hG w hδ.le hδ4 hE
  have hrem' : g-I ≤ E*(2+B*(2*δ*Real.log E+5+18/(1-gaussianBlockPass.toReal))) := by
    refine hrem.trans (mul_le_mul_of_nonneg_left ?_ hEp.le)
    have hb := mul_le_mul_of_nonneg_right (hWB w hw)
      (show 0 ≤ 2*δ*Real.log E+5+18/(1-gaussianBlockPass.toReal) by positivity)
    linarith
  have herr := (abs_sub_le g I (4*V*(E*Real.log E))).trans
    (add_le_add (show |g-I| ≤ E*(2+B*(2*δ*Real.log E+5+18/(1-gaussianBlockPass.toReal))) by
      rwa [abs_of_nonneg (sub_nonneg.mpr hIg)]) hIerr)
  change |g-4*V*(E*Real.log E)| ≤ _
  nlinarith only [herr]

/-- C.4: the exact mean coefficient is uniform on every compact set of
nonnegative carried values. -/
theorem frozenPrefixLength_mean_uniform_eventually
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ici 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ E : ℝ in atTop, ∀ w ∈ K,
      |(∫ ω, frozenPrefixLengthReal X w E ω ∂μ)/(E*Real.log E)-
          4*gaussianRenewalPotential X μ w| < η := by
  obtain ⟨M0, hM0⟩ := hK.bddAbove_image
    ((gaussianRenewalPotential_continuousOn hX hi hG).mono hK0).abs
  let M : ℝ := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hVM : ∀ w ∈ K, |gaussianRenewalPotential X μ w| ≤ M :=
    fun w hw => (hM0 ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  obtain ⟨W0, hW0⟩ := hK.bddAbove_image (f := fun w : ℝ => |w|) continuous_abs.continuousOn
  let W : ℝ := max W0 0
  have hW : 0 ≤ W := le_max_right _ _
  have hWW : ∀ w ∈ K, |w| ≤ W := fun w hw => (hW0 ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  let B : ℝ := frozenHarmonicTailConstant*(1+W)
  have hB : 0 ≤ B := mul_nonneg frozenHarmonicTailConstant_pos.le (by linarith)
  have hWB : ∀ w ∈ K, frozenHarmonicTailConstant*(1+max w 0) ≤ B := by
    intro w hw
    exact mul_le_mul_of_nonneg_left
      (by have hh := (le_abs_self w).trans (hWW w hw); exact add_le_add_right (max_le hh hW) 1)
      frozenHarmonicTailConstant_pos.le
  let A : ℝ := 8*M+2*B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let δ : ℝ := min (1/4) (η/(4*(A+1)))
  let ε : ℝ := η/4
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ4 : δ ≤ 1/4 := min_le_left _ _
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hδA : δ*A ≤ η/4 := by
    have hh := (le_div_iff₀ (show 0 < 4*(A+1) by positivity)).mp
      (show δ ≤ η/(4*(A+1)) from min_le_right _ _)
    nlinarith
  let C : ℝ := 2*ε+8*M+2+B*(5+18/(1-gaussianBlockPass.toReal))
  have hC : 0 ≤ C := by
    have hq : 0 < 1-gaussianBlockPass.toReal := sub_pos.mpr frozen_block_ratio_lt_one
    dsimp [C]
    positivity
  have hsmall : ∀ᶠ E : ℝ in atTop, C ≤ (η/4)*Real.log E := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (4*C/η)] with E hE
    have hh := (div_le_iff₀ hη).mp hE
    nlinarith
  filter_upwards [frozenMeanLimit_error_bound hX hi hG hK hK0 hM hB hVM hWB hδ hδ4 hε,
    hsmall, eventually_gt_atTop (1 : ℝ)] with E hE hEC hE1
  intro w hw
  have hEp : 0 < E := by linarith
  have hlog : 0 < Real.log E := Real.log_pos hE1
  have hscale : 0 < E*Real.log E := mul_pos hEp hlog
  have hcoef : ε+δ*(8*M+2*B) ≤ η/2 := by
    change ε+δ*A ≤ η/2
    dsimp [ε]
    linarith
  have herr : |(∫ ω, frozenPrefixLengthReal X w E ω ∂μ)-
      4*gaussianRenewalPotential X μ w*(E*Real.log E)| < η*(E*Real.log E) := by
    calc
      _ ≤ E*((ε+δ*(8*M+2*B))*Real.log E+C) := hE w hw
      _ ≤ E*((η/2)*Real.log E+(η/4)*Real.log E) := by gcongr
      _ < _ := by nlinarith
  have heq : (∫ ω, frozenPrefixLengthReal X w E ω ∂μ)/(E*Real.log E)-
      4*gaussianRenewalPotential X μ w =
      ((∫ ω, frozenPrefixLengthReal X w E ω ∂μ)-
        4*gaussianRenewalPotential X μ w*(E*Real.log E))/(E*Real.log E) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hscale]
  exact (div_lt_iff₀ hscale).mpr herr

/-- The compact-uniform mean limit for the actual frozen prefix. -/
theorem frozenPrefixLength_mean_tendstoUniformlyOn
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ici 0) :
    TendstoUniformlyOn
      (fun E w => (∫ ω, frozenPrefixLengthReal X w E ω ∂μ)/(E*Real.log E))
      (fun w => 4*gaussianRenewalPotential X μ w) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [frozenPrefixLength_mean_uniform_eventually hX hi hG hK hK0 hη] with E hE
  intro w hw
  simpa only [Real.dist_eq, abs_sub_comm] using hE w hw

/-- The pointwise C.4 mean asymptotic, for every nonnegative carried value. -/
theorem frozenPrefixLength_mean_tendsto
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {w : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun E => (∫ ω, frozenPrefixLengthReal X w E ω ∂μ)/(E*Real.log E))
      atTop (𝓝 (4*gaussianRenewalPotential X μ w)) := by
  exact (frozenPrefixLength_mean_tendstoUniformlyOn hX hi hG
    (isCompact_singleton (x := w)) (by simpa using hw)).tendsto_at (mem_singleton w)

end SwingRepair
