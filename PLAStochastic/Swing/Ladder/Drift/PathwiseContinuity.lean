import PLAStochastic.Swing.Ladder.Drift.LawFamily
import PLAStochastic.Swing.Ladder.Law.UniformMoments
import PLAStochastic.Swing.Gaussian.Bridge.EndpointIndependence

/-! # The ladder height is continuous in the drift

The continuity paragraph of `app:limit` couples all drifts with the same
Gaussian walk.  Along one path the drifted walk never vanishes after time zero,
so the first crossing index is locally constant in the drift and the ladder
height depends affinely on the drift near each point.  With the uniform second
moment this upgrades to `L¹` continuity, which is what the equilibrium
overshoot density needs.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The drifted walk avoids zero after time zero -/

theorem gaussianDriftWalk_ne_zero_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) :
    ∀ᵐ ω ∂μ, ∀ j : ℕ, 1 ≤ j → gaussianDriftWalk X 0 a j ω ≠ 0 := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [ae_all_iff]
  intro j
  rw [ae_all_iff]
  intro hj
  have hlaw := (gaussianEndpoint_hasLaw hX hi hG j).map_eq
  have hvar : ((j : ℝ≥0)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hns : NullSingletonClass (gaussianReal 0 (j : ℝ≥0)) :=
    nullSingletonClass_gaussianReal hvar
  have hset : {ω : Ω | ¬ gaussianDriftWalk X 0 a j ω ≠ 0} =
      (cumulativeSamples X j) ⁻¹' {-(a*(j : ℝ))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, not_not, mem_preimage, mem_singleton_iff, gaussianDriftWalk,
      zero_add]
    constructor
    · intro h; linarith
    · intro h; linarith
  have hmeas : Measurable (cumulativeSamples X j) :=
    Finset.measurable_sum _ (fun k _ => hX k)
  have hkey : μ ((cumulativeSamples X j) ⁻¹' {-(a*(j : ℝ))}) =
      gaussianReal 0 (j : ℝ≥0) {-(a*(j : ℝ))} := by
    rw [← hlaw, Measure.map_apply hmeas (measurableSet_singleton _)]
  rw [ae_iff, hset, hkey]
  exact measure_singleton _

/-! ### Local constancy of the ladder time -/

omit [MeasurableSpace Ω] in
/-- On a path with a finite ladder time and no zero after time zero, the ladder
time is constant in a neighbourhood of the drift and the height is affine. -/
theorem gaussianAscendingLadder_locally_affine {a : ℝ} {ω : Ω}
    (hT : gaussianAscendingLadderTime X a ω ≠ ⊤)
    (hne : ∀ j : ℕ, 1 ≤ j → gaussianDriftWalk X 0 a j ω ≠ 0) :
    ∃ ε > 0, ∀ a' : ℝ, |a' - a| < ε →
      gaussianAscendingLadderTime X a' ω = gaussianAscendingLadderTime X a ω ∧
      gaussianAscendingLadderHeight X a' ω =
        gaussianAscendingLadderHeight X a ω +
          (a' - a)*(((gaussianAscendingLadderTime X a ω).untopD 0 : ℕ) : ℝ) := by
  set n : ℕ := (gaussianAscendingLadderTime X a ω).untopD 0 with hn
  have hTn : gaussianAscendingLadderTime X a ω = (n : WithTop ℕ) := by
    rw [hn]
    lift gaussianAscendingLadderTime X a ω to ℕ using hT with m hm
    simp
  have hnpos : 1 ≤ n := by
    have h0 := gaussianAscendingLadderTime_pos (X := X) a ω
    rw [hTn] at h0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro hc
      rw [hc] at h0
      exact absurd h0 (lt_irrefl _))
  -- the strict gaps below and at the crossing index
  have hbelow : ∀ j : ℕ, j < n → gaussianDriftWalk X 0 a j ω < 0 ∨ j = 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact Or.inr rfl
    · have hlt : (j : WithTop ℕ) < gaussianAscendingLadderTime X a ω := by
        rw [hTn]
        exact_mod_cast hj
      have hle := (lt_gaussianAscendingLadderTime_iff X a j ω).mp hlt j le_rfl
      exact Or.inl (lt_of_le_of_ne hle (hne j hj0))
  have hat : 0 < gaussianDriftWalk X 0 a n ω := by
    have hnotlt : ¬ ((n : ℕ) : WithTop ℕ) < gaussianAscendingLadderTime X a ω := by
      rw [hTn]
      exact lt_irrefl _
    rw [lt_gaussianAscendingLadderTime_iff] at hnotlt
    push Not at hnotlt
    obtain ⟨j, hj, hpos⟩ := hnotlt
    rcases lt_or_eq_of_le hj with hjlt | rfl
    · rcases hbelow j hjlt with hneg | rfl
      · linarith
      · simp only [gaussianDriftWalk, cumulativeSamples] at hpos
        norm_num at hpos
    · exact hpos
  -- choose the radius
  set ε : ℝ := (Finset.Icc 1 n).inf' (Finset.nonempty_Icc.mpr hnpos)
      (fun j => |gaussianDriftWalk X 0 a j ω| / (j : ℝ)) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    refine (Finset.lt_inf'_iff _).2 ?_
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hjr : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hnz : gaussianDriftWalk X 0 a j ω ≠ 0 := hne j hj1
    positivity
  refine ⟨ε, hεpos, fun a' ha' => ?_⟩
  have hgap : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      |a' - a| * (j : ℝ) < |gaussianDriftWalk X 0 a j ω| := by
    intro j hj1 hjn
    have hjr : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hle : ε ≤ |gaussianDriftWalk X 0 a j ω| / (j : ℝ) :=
      Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hj1, hjn⟩)
    have := lt_of_lt_of_le ha' hle
    rw [lt_div_iff₀ hjr] at this
    exact this
  have hshift : ∀ j : ℕ, gaussianDriftWalk X 0 a' j ω =
      gaussianDriftWalk X 0 a j ω + (a' - a)*(j : ℝ) := by
    intro j
    simp only [gaussianDriftWalk]
    ring
  have hbelow' : ∀ j : ℕ, j < n → gaussianDriftWalk X 0 a' j ω ≤ 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [gaussianDriftWalk, cumulativeSamples]
    · rcases hbelow j hj with hneg | rfl
      · have hg := hgap j hj0 hj.le
        rw [abs_of_neg hneg] at hg
        have habs := neg_abs_le (a' - a)
        have hjr : (0 : ℝ) ≤ (j : ℝ) := by positivity
        have : (a' - a)*(j : ℝ) ≤ |a' - a| * (j : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hjr
        rw [hshift j]
        linarith
      · omega
  have hat' : 0 < gaussianDriftWalk X 0 a' n ω := by
    have hg := hgap n hnpos le_rfl
    rw [abs_of_pos hat] at hg
    have hjr : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hlow : -(|a' - a| * (n : ℝ)) ≤ (a' - a)*(n : ℝ) := by
      have := mul_le_mul_of_nonneg_right (neg_abs_le (a' - a)) hjr
      linarith
    rw [hshift n]
    linarith
  have hTeq : gaussianAscendingLadderTime X a' ω = (n : WithTop ℕ) := by
    refine withTop_nat_eq_of_le_of_forall_lt ?_ ?_
    · by_contra hc
      push Not at hc
      rw [lt_gaussianAscendingLadderTime_iff] at hc
      have := hc n le_rfl
      linarith
    · intro j hj
      rw [lt_gaussianAscendingLadderTime_iff]
      intro i hi
      exact hbelow' i (lt_of_le_of_lt hi hj)
  refine ⟨by rw [hTeq, hTn], ?_⟩
  have hTne' : gaussianAscendingLadderTime X a' ω ≠ ⊤ := by
    rw [hTeq]
    exact WithTop.coe_ne_top
  have huntop : WithTop.untopD 0 ((n : ℕ) : WithTop ℕ) = n := rfl
  rw [gaussianAscendingLadderHeight_eq_position hTne',
    gaussianAscendingLadderHeight_eq_position hT, hTeq, hTn, huntop, hshift n]

/-- The ladder height converges pointwise as the drift varies, on a full-measure
set determined by the base drift. -/
theorem gaussianAscendingLadderHeight_tendsto_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂μ, Tendsto (fun a' : ℝ => gaussianAscendingLadderHeight X a' ω) (𝓝 a)
      (𝓝 (gaussianAscendingLadderHeight X a ω)) := by
  filter_upwards [gaussianAscendingLadderTime_finite_ae hX hi hG ha,
    gaussianDriftWalk_ne_zero_ae hX hi hG a] with ω hT hne
  obtain ⟨ε, hε, hloc⟩ := gaussianAscendingLadder_locally_affine hT hne
  set n : ℝ := (((gaussianAscendingLadderTime X a ω).untopD 0 : ℕ) : ℝ) with hn
  have heq : (fun a' : ℝ => gaussianAscendingLadderHeight X a' ω) =ᶠ[𝓝 a]
      (fun a' : ℝ => gaussianAscendingLadderHeight X a ω + (a' - a)*n) := by
    have hball : ∀ᶠ a' : ℝ in 𝓝 a, |a' - a| < ε := by
      filter_upwards [Metric.ball_mem_nhds a hε] with a' ha'
      simpa only [Metric.mem_ball, Real.dist_eq] using ha'
    filter_upwards [hball] with a' ha'
    exact (hloc a' ha').2
  refine Tendsto.congr' heq.symm ?_
  have : Tendsto (fun a' : ℝ => gaussianAscendingLadderHeight X a ω + (a' - a)*n) (𝓝 a)
      (𝓝 (gaussianAscendingLadderHeight X a ω + (a - a)*n)) := by
    exact tendsto_const_nhds.add (((continuous_id.sub continuous_const).mul
      continuous_const).continuousAt)
  simpa using this

end SwingRepair
