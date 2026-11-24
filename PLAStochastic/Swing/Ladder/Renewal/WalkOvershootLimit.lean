import PLAStochastic.ForMathlib.Probability.TailComparison.BoundedLipschitz
import PLAStochastic.Affine.Error.Measurable
import PLAStochastic.Affine.Lifetime.GaussianBlocks
import PLAStochastic.Swing.Gaussian.Tail.QuadraticDrift
import PLAStochastic.Swing.Ladder.Renewal.ResidualLifeUniform

/-! # The overshoot law of the actual walk and its bounded Lipschitz limit

`app:limit` concludes the renewal step by saying that truncating the overshoot
variable turns the uniform tail convergence into uniform convergence against
bounded Lipschitz test functions.  This file builds the overshoot law of the
actual positive-drift Gaussian walk as a genuine probability measure on the
line, identifies its tail with the residual-life expression already proved, and
combines the uniform residual-life bound with the truncation estimate to get
that uniform bounded Lipschitz convergence over a compact drift interval.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-! ### Measurability of the first passage and its overshoot -/

omit mΩ in
theorem measurable_apply_nat [MeasurableSpace Ω] {τ : Ω → ℕ} (hτ : Measurable τ)
    {u : ℕ → Ω → ℝ} (hu : ∀ n, Measurable (u n)) :
    Measurable fun ω => u (τ ω) ω := by
  intro S hS
  have hset : (fun ω => u (τ ω) ω) ⁻¹' S = ⋃ n : ℕ, ({ω | τ ω = n} ∩ (u n ⁻¹' S)) := by
    ext ω
    constructor
    · intro hω
      exact Set.mem_iUnion.2 ⟨τ ω, ⟨rfl, hω⟩⟩
    · intro hω
      obtain ⟨n, hn, hmem⟩ := Set.mem_iUnion.1 hω
      have hn' : τ ω = n := hn
      show u (τ ω) ω ∈ S
      rw [hn']
      exact hmem
  rw [hset]
  exact MeasurableSet.iUnion fun n => (hτ (measurableSet_singleton n)).inter (hu n hS)

theorem gaussianWalkPassage_measurable (hX : ∀ n, Measurable (X n)) (a b : ℝ) :
    Measurable (gaussianWalkPassage X a b) := by
  have hW : ∀ m, Measurable (gaussianDriftWalk X 0 a m) := fun m =>
    gaussianDriftWalk_measurable hX 0 a m
  have hE : ∀ m, MeasurableSet {ω | b < gaussianDriftWalk X 0 a m ω} := fun m =>
    measurableSet_lt measurable_const (hW m)
  have hEc : ∀ m, MeasurableSet {ω | ¬ b < gaussianDriftWalk X 0 a m ω} := fun m =>
    (hE m).compl
  refine measurable_to_countable' fun n => ?_
  match n with
  | 0 =>
    have hset : gaussianWalkPassage X a b ⁻¹' {0} =
        {ω | b < gaussianDriftWalk X 0 a 0 ω} ∪
          ⋂ m : ℕ, {ω | ¬ b < gaussianDriftWalk X 0 a m ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iInter,
        Set.mem_ofPred_eq]
      constructor
      · intro hω
        by_cases hex : ∃ m : ℕ, b < gaussianDriftWalk X 0 a m ω
        · left
          have : Nat.find hex = 0 := by
            rw [gaussianWalkPassage, dif_pos hex] at hω
            exact hω
          have hspec := Nat.find_spec hex
          rwa [this] at hspec
        · right
          intro m hm
          exact hex ⟨m, hm⟩
      · intro hω
        rcases hω with hω | hω
        · have hex : ∃ m : ℕ, b < gaussianDriftWalk X 0 a m ω := ⟨0, hω⟩
          rw [gaussianWalkPassage, dif_pos hex]
          exact Nat.find_eq_zero hex |>.mpr hω
        · have hex : ¬ ∃ m : ℕ, b < gaussianDriftWalk X 0 a m ω := by
            rintro ⟨m, hm⟩
            exact hω m hm
          rw [gaussianWalkPassage, dif_neg hex]
    rw [hset]
    exact (hE 0).union (MeasurableSet.iInter fun m => hEc m)
  | (n+1) =>
    have hset : gaussianWalkPassage X a b ⁻¹' {n+1} =
        {ω | b < gaussianDriftWalk X 0 a (n+1) ω} ∩
          ⋂ j : ℕ, ⋂ _ : j < n+1, {ω | ¬ b < gaussianDriftWalk X 0 a j ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_ofPred_eq]
      constructor
      · intro hω
        by_cases hex : ∃ m : ℕ, b < gaussianDriftWalk X 0 a m ω
        · rw [gaussianWalkPassage, dif_pos hex] at hω
          have := (Nat.find_eq_iff hex).mp hω
          exact ⟨this.1, fun j hj => this.2 j hj⟩
        · rw [gaussianWalkPassage, dif_neg hex] at hω
          exact absurd hω (by omega)
      · rintro ⟨h1, h2⟩
        have hex : ∃ m : ℕ, b < gaussianDriftWalk X 0 a m ω := ⟨n+1, h1⟩
        rw [gaussianWalkPassage, dif_pos hex]
        exact (Nat.find_eq_iff hex).mpr ⟨h1, fun j hj => h2 j hj⟩
    rw [hset]
    exact (hE (n+1)).inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => hEc j)

theorem gaussianWalkOvershoot_measurable (hX : ∀ n, Measurable (X n)) (a b : ℝ) :
    Measurable (gaussianWalkOvershoot X a b) :=
  (measurable_apply_nat (gaussianWalkPassage_measurable hX a b)
    (fun m => gaussianDriftWalk_measurable hX 0 a m)).sub_const b

/-! ### The overshoot law -/

/-- The law of the overshoot of the actual positive-drift walk above a level. -/
def gaussianWalkOvershootLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a b : ℝ) : Measure ℝ :=
  μ.map (gaussianWalkOvershoot X a b)

theorem gaussianWalkOvershootLaw_isProbabilityMeasure [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (a b : ℝ) :
    IsProbabilityMeasure (gaussianWalkOvershootLaw X μ a b) :=
  Measure.isProbabilityMeasure_map (gaussianWalkOvershoot_measurable hX a b).aemeasurable

theorem gaussianWalkOvershootLaw_Ioi [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M a : ℝ} (ha : 0 < a) (haM : a ≤ M)
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    gaussianWalkOvershootLaw X μ a b (Ioi t) =
      renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b t := by
  rw [gaussianWalkOvershootLaw,
    Measure.map_apply (gaussianWalkOvershoot_measurable hX a b) measurableSet_Ioi]
  exact gaussianWalkOvershoot_tail_eq hX hi hG ha haM hb ht

theorem gaussianWalkOvershootLaw_Iio_zero [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M a : ℝ} (ha : 0 < a) (haM : a ≤ M)
    {b : ℝ} (hb : 0 ≤ b) :
    gaussianWalkOvershootLaw X μ a b (Iio 0) = 0 := by
  rw [gaussianWalkOvershootLaw,
    Measure.map_apply (gaussianWalkOvershoot_measurable hX a b) measurableSet_Iio,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [gaussianWalkOvershoot_ae_eq_ladder hX hi hG ha haM hb,
    gaussianLadderSum_exists_gt_ae hX hi hG ha haM] with ω hω hex
  have hpos : 0 < gaussianLadderOvershoot X a b ω := by
    have hb' := hex b
    rw [gaussianLadderOvershoot, gaussianLadderPassage, dif_pos hb']
    have := Nat.find_spec hb'
    linarith
  simp only [Set.mem_preimage, mem_Iio, not_lt]
  rw [hω]
  exact hpos.le

/-! ### The equilibrium overshoot law as a law on `[0,∞)` -/

theorem equilibriumOvershootLaw_Iio_zero (ν : Measure ℝ) :
    equilibriumOvershootLaw ν (Iio 0) = 0 := by
  rw [equilibriumOvershootLaw_apply ν measurableSet_Iio]
  have hempty : Iio (0 : ℝ) ∩ Ici (0 : ℝ) = (∅ : Set ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, mem_Iio, mem_Ici, Set.mem_empty_iff_false, iff_false, not_and,
      not_le]
    intro hx
    exact hx
  rw [hempty, Measure.restrict_empty, lintegral_zero_measure]

theorem equilibriumOvershootLaw_Ioi (ν : Measure ℝ) (h0 : ladderMeanENN ν ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    equilibriumOvershootLaw ν (Ioi t) = equilibriumOvershootTail ν t := by
  rw [equilibriumOvershootLaw_apply ν measurableSet_Ioi]
  have hinter : Ioi t ∩ Ici (0 : ℝ) = Ioi t := by
    refine Set.inter_eq_self_of_subset_left (fun x hx => ?_)
    have hx' : t < x := hx
    exact le_of_lt (lt_of_le_of_lt ht hx')
  rw [hinter, equilibriumOvershootTail]
  simp_rw [ENNReal.div_eq_inv_mul]
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr h0)]

/-! ### The uniform bounded Lipschitz limit -/

/-- The explicit bound for bounded Lipschitz test functions: the uniform
residual-life bound at passage level `b`, plus the truncation error at level
`T`. -/
noncomputable def gaussianOvershootLipschitzBound (δ M K B C c b T : ℝ) : ℝ :=
  (4*B + 2*K*T) * gaussianResidualLifeBound δ M C c b +
    4*B*gaussianAscendingLadderMomentBound δ M 2 /
      (gaussianAscendingLadderCommonDensity M * T)

/-- The equilibrium overshoot tail obeys the same uniform Chebyshev bound as
the ladder height. -/
theorem equilibriumOvershoot_tail_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) {T : ℝ} (hT : 0 < T) :
    (equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a)).real (Ioi T) ≤
      gaussianAscendingLadderMomentBound δ M 2 /
        (gaussianAscendingLadderCommonDensity M * T) := by
  have := hi.isProbabilityMeasure
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hc := gaussianAscendingLadderCommonDensity_pos M
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  have hmean := ladderMean_gaussianAscendingLadderLaw_ge hX hi hG hδ hδa haM
  have hmean0 : 0 < ladderMean ν := lt_of_lt_of_le hc hmean
  have hid := gaussianAscendingLadderLaw_id_integrable hX hi hG hδ hδa haM
  have hsq := gaussianAscendingLadderLaw_sq_integrable hX hi hG hδ hδa haM
  have hsqle : (∫ x, x^2 ∂ν) ≤ gaussianAscendingLadderMomentBound δ M 2 :=
    gaussianAscendingLadderLaw_sq_integral_le hX hi hG hδ hδa haM
  have hlaw : (equilibriumOvershootLaw ν).real (Ioi T) =
      (∫ h, max (h-T) 0 ∂ν) / ladderMean ν := by
    rw [Measure.real, equilibriumOvershootLaw_Ioi ν
      (gaussianAscendingLadderLaw_mean_ne_zero hX hG ha haM) hT.le,
      equilibriumOvershootTail_toReal]
  have hsplit : (∫ h, max (h-T) 0 ∂ν) = ∫ h in Ioi T, (h-T) ∂ν := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi T)]
    · exact setIntegral_congr_fun measurableSet_Ioi (fun h hh => by
        have hh' : T < h := hh
        exact max_eq_left (by linarith))
    · intro h hh
      have hh' : ¬ T < h := hh
      exact max_eq_right (by linarith)
  have hnum : (∫ h, max (h-T) 0 ∂ν) ≤ gaussianAscendingLadderMomentBound δ M 2 / T := by
    rw [hsplit]
    refine (setIntegral_sub_le_sq_moment hid hsq (t := T) hT.le hT).trans ?_
    exact div_le_div_of_nonneg_right hsqle hT.le
  rw [hlaw]
  have hB0 : 0 ≤ gaussianAscendingLadderMomentBound δ M 2 :=
    gaussianAscendingLadderMomentBound_two_nonneg hX hi hG hδ hδa haM
  calc (∫ h, max (h-T) 0 ∂ν) / ladderMean ν
      ≤ (gaussianAscendingLadderMomentBound δ M 2 / T) / gaussianAscendingLadderCommonDensity M := by
        refine div_le_div₀ (by positivity) hnum hc hmean
    _ = gaussianAscendingLadderMomentBound δ M 2 /
          (gaussianAscendingLadderCommonDensity M * T) := by
        field_simp

/-- The uniform bounded Lipschitz comparison for the actual walk: the overshoot
law above level `b` and the equilibrium overshoot law integrate every bounded
Lipschitz test function to within an explicit bound that depends only on the
drift interval, the test-function constants, the passage level and the
truncation level. -/
theorem gaussianWalkOvershoot_lipschitz_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M C c : ℝ} (hδ : 0 < δ)
    (hexp : UniformLadderRenewalExpansion (gaussianAscendingLadderLaw X μ) (Icc δ M) C c)
    {a : ℝ} (hδa : δ ≤ a) (haM : a ≤ M) {b T : ℝ} (hb : 0 < b) (hT : 0 < T)
    {f : ℝ → ℝ} {K B : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ K*|x-y|) (hfB : ∀ x, |f x| ≤ B) :
    |(∫ x, f x ∂(gaussianWalkOvershootLaw X μ a b)) -
        ∫ x, f x ∂(equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a))| ≤
      gaussianOvershootLipschitzBound δ M K B C c b T := by
  have := hi.isProbabilityMeasure
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hlprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
  have hPprob := gaussianWalkOvershootLaw_isProbabilityMeasure (μ := μ) hX a b
  have hQprob := gaussianAscendingLadderEquilibrium_isProbabilityMeasure hX hi hG hδ hδa haM
  set P := gaussianWalkOvershootLaw X μ a b with hPdef
  set Q := equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a) with hQdef
  set ε := gaussianResidualLifeBound δ M C c b with hεdef
  have hPIio : P (Iio 0) = 0 := gaussianWalkOvershootLaw_Iio_zero hX hi hG ha haM hb.le
  have hQIio : Q (Iio 0) = 0 := equilibriumOvershootLaw_Iio_zero _
  have htail : ∀ t : ℝ, 0 ≤ t → |P.real (Ioi t) - Q.real (Ioi t)| ≤ ε := by
    intro t ht
    have hP : P.real (Ioi t) =
        (renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b t).toReal := by
      rw [Measure.real, gaussianWalkOvershootLaw_Ioi hX hi hG ha haM hb.le ht]
    have hQ : Q.real (Ioi t) =
        (equilibriumOvershootTail (gaussianAscendingLadderLaw X μ a) t).toReal := by
      rw [Measure.real, equilibriumOvershootLaw_Ioi _
        (gaussianAscendingLadderLaw_mean_ne_zero hX hG ha haM) ht]
    rw [hP, hQ]
    exact gaussianAscendingLadder_residual_life_uniform_le hX hi hG hδ hexp hδa haM ht hb
  have hmain := integral_lipschitz_sub_le_of_tail_close hPIio hQIio htail hK hlip hfB hT.le
  have hQtail : Q.real (Ioi T) ≤
      gaussianAscendingLadderMomentBound δ M 2 /
        (gaussianAscendingLadderCommonDensity M * T) :=
    equilibriumOvershoot_tail_le hX hi hG hδ hδa haM hT
  have hPtail : P.real (Ioi T) ≤ Q.real (Ioi T) + ε := by
    have := htail T hT.le
    have h1 : P.real (Ioi T) - Q.real (Ioi T) ≤ ε := (le_abs_self _).trans this
    linarith
  refine hmain.trans ?_
  rw [gaussianOvershootLipschitzBound, ← hεdef]
  have hQ0 : 0 ≤ Q.real (Ioi T) := measureReal_nonneg
  have h1 : 2*B*P.real (Ioi T) ≤ 2*B*(Q.real (Ioi T) + ε) :=
    mul_le_mul_of_nonneg_left hPtail (by linarith)
  have h2 : 4*B*Q.real (Ioi T) ≤
      4*B*gaussianAscendingLadderMomentBound δ M 2 /
        (gaussianAscendingLadderCommonDensity M * T) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hQtail (by linarith)
  linarith

/-- The paper's uniform statement: for every accuracy there is a passage level
beyond which the overshoot law of the actual walk and the equilibrium overshoot
law agree to that accuracy against **every** test function with the given
Lipschitz constant and sup norm, **simultaneously for every drift** in the
compact interval.  The renewal expansion is the only input. -/
theorem gaussianWalkOvershoot_lipschitz_uniform
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M C c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hexp : UniformLadderRenewalExpansion (gaussianAscendingLadderLaw X μ) (Icc δ M) C c)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {η : ℝ} (hη : 0 < η) :
    ∃ b₀ : ℝ, ∀ a ∈ Icc δ M, ∀ b : ℝ, b₀ ≤ b → ∀ f : ℝ → ℝ,
      (∀ x y : ℝ, |f x - f y| ≤ K*|x-y|) → (∀ x, |f x| ≤ B) →
        |(∫ x, f x ∂(gaussianWalkOvershootLaw X μ a b)) -
            ∫ x, f x ∂(equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a))| ≤ η := by
  have hcM := gaussianAscendingLadderCommonDensity_pos M
  set B2 := gaussianAscendingLadderMomentBound δ M 2 with hB2def
  set cM := gaussianAscendingLadderCommonDensity M with hcMdef
  -- choose the truncation level so that the tail term costs at most `η/2`
  set T : ℝ := max 1 (8*B*|B2|/(cM*η)) with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_left _ _
  have hT : 0 < T := lt_of_lt_of_le one_pos hT1
  have hTtail : 4*B*B2/(cM*T) ≤ η/2 := by
    have hTge : 8*B*|B2|/(cM*η) ≤ T := le_max_right _ _
    have hkey : 8*B*|B2| ≤ cM*η*T := by
      rw [div_le_iff₀ (by positivity)] at hTge
      linarith
    have habs : B2 ≤ |B2| := le_abs_self _
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg B2, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hB) (abs_nonneg B2)]
  -- choose the passage level so that the renewal term costs at most `η/2`
  have hlim := gaussianResidualLifeBound_tendsto (δ := δ) (M := M) (C := C) (c := c) hc
  have hA : (0 : ℝ) ≤ 4*B + 2*K*T := by positivity
  have hsmall : ∀ᶠ b : ℝ in atTop,
      gaussianResidualLifeBound δ M C c b < η/(2*(4*B + 2*K*T) + 2) :=
    hlim.eventually_lt_const (by positivity)
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.mp hsmall
  refine ⟨max b₀ 1, fun a ha b hb f hlip hfB => ?_⟩
  have hb1 : (1 : ℝ) ≤ b := le_trans (le_max_right _ _) hb
  have hbpos : 0 < b := lt_of_lt_of_le one_pos hb1
  have hbb : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hres := hb₀ b hbb
  have hmain := gaussianWalkOvershoot_lipschitz_le hX hi hG hδ hexp ha.1 ha.2 hbpos hT
    hK hlip hfB
  refine hmain.trans ?_
  rw [gaussianOvershootLipschitzBound, ← hB2def, ← hcMdef]
  have hstep : (4*B + 2*K*T) * gaussianResidualLifeBound δ M C c b ≤ η/2 := by
    have hlt : (4*B + 2*K*T) * gaussianResidualLifeBound δ M C c b ≤
        (4*B + 2*K*T) * (η/(2*(4*B + 2*K*T) + 2)) :=
      mul_le_mul_of_nonneg_left hres.le hA
    refine hlt.trans ?_
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

end SwingRepair
