import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.UniformIntegrability
import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.ConcreteBounds
import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.LimitRewardBounds
import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.CutoffAssembly
import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.CentralCutoff

/-!
# Concrete UI and cutoff transfer for Theorem 4.3

The preceding files separate the finite estimates from the weak-limit
functional analysis.  Here we begin the final assembly: the stationary margin
laws inherit a uniform square moment from Theorem 4.2, and hence every weak
limit has a finite first moment.  The remaining cutoff estimates can then be
used without postulating integrability of the limit law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace LeadingCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ## A four-region integral decomposition

The discontinuity at zero and the linear tail are handled by splitting the
line into a central interval, a negative half-line, a positive compact
interval, and a positive far tail.  The lemma below is purely measure
theoretic; all model-specific estimates are supplied as the four displayed
regional errors. -/

theorem abs_integral_sub_le_of_four_regions
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    {f g : ℝ → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    {δ C a n p q : ℝ} (hδ : 0 < δ) (hC : δ ≤ C)
    (hA : |(∫ x in Icc (-δ) δ, f x ∂ν) -
      ∫ x in Icc (-δ) δ, g x ∂ν| ≤ a)
    (hN : |(∫ x in Iio (-δ), f x ∂ν) -
      ∫ x in Iio (-δ), g x ∂ν| ≤ n)
    (hP : |(∫ x in Ioc δ C, f x ∂ν) -
      ∫ x in Ioc δ C, g x ∂ν| ≤ p)
    (hF : |(∫ x in Ioi C, f x ∂ν) -
      ∫ x in Ioi C, g x ∂ν| ≤ q) :
    |(∫ x, f x ∂ν) - ∫ x, g x ∂ν| ≤ a + n + p + q := by
  let A : Set ℝ := Icc (-δ) δ
  let N : Set ℝ := Iio (-δ)
  let P : Set ℝ := Ioc δ C
  let F : Set ℝ := Ioi C
  have hmeasA : MeasurableSet A := measurableSet_Icc
  have hmeasN : MeasurableSet N := measurableSet_Iio
  have hmeasP : MeasurableSet P := measurableSet_Ioc
  have hmeasF : MeasurableSet F := measurableSet_Ioi
  have hdisjNA : Disjoint N A := by
    refine Set.disjoint_left.2 ?_
    intro x hxN hxA
    exact (not_lt_of_ge (mem_Icc.mp hxA).1) (mem_Iio.mp hxN)
  have hdisjNP : Disjoint N P := by
    refine Set.disjoint_left.2 ?_
    intro x hxN hxP
    have hxδ : δ < x := (mem_Ioc.mp hxP).1
    have hneg : x < -δ := mem_Iio.mp hxN
    linarith
  have hdisjNF : Disjoint N F := by
    refine Set.disjoint_left.2 ?_
    intro x hxN hxF
    have hneg : x < -δ := mem_Iio.mp hxN
    have hpos : C < x := mem_Ioi.mp hxF
    linarith
  have hdisjAP : Disjoint A P := by
    refine Set.disjoint_left.2 ?_
    intro x hxA hxP
    exact (not_lt_of_ge (mem_Icc.mp hxA).2) (mem_Ioc.mp hxP).1
  have hdisjAF : Disjoint A F := by
    refine Set.disjoint_left.2 ?_
    intro x hxA hxF
    have hxa : x ≤ δ := (mem_Icc.mp hxA).2
    have hxf : C < x := mem_Ioi.mp hxF
    linarith
  have hdisjPF : Disjoint P F := by
    refine Set.disjoint_left.2 ?_
    intro x hxP hxF
    exact (not_lt_of_ge (mem_Ioc.mp hxP).2) (mem_Ioi.mp hxF)
  have hunion : N ∪ A ∪ P ∪ F = (Set.univ : Set ℝ) := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      by_cases hN' : x < -δ
      · exact Or.inl (Or.inl (Or.inl hN'))
      · by_cases hA' : x ≤ δ
        · exact Or.inl (Or.inl (Or.inr ⟨le_of_not_gt hN', hA'⟩))
        · by_cases hP' : x ≤ C
          · exact Or.inl (Or.inr ⟨lt_of_not_ge hA', hP'⟩)
          · exact Or.inr (lt_of_not_ge hP')
  have hhi : Integrable (fun x : ℝ => f x - g x) ν := hf.sub hg
  have hhiA : IntegrableOn (fun x : ℝ => f x - g x) A ν := hhi.integrableOn
  have hhiN : IntegrableOn (fun x : ℝ => f x - g x) N ν := hhi.integrableOn
  have hhiP : IntegrableOn (fun x : ℝ => f x - g x) P ν := hhi.integrableOn
  have hhiF : IntegrableOn (fun x : ℝ => f x - g x) F ν := hhi.integrableOn
  have hNA : ∫ x in N ∪ A, (f x - g x) ∂ν =
      ∫ x in N, (f x - g x) ∂ν + ∫ x in A, (f x - g x) ∂ν :=
    setIntegral_union hdisjNA hmeasA hhiN hhiA
  have hPF : ∫ x in P ∪ F, (f x - g x) ∂ν =
      ∫ x in P, (f x - g x) ∂ν + ∫ x in F, (f x - g x) ∂ν :=
    setIntegral_union hdisjPF hmeasF hhiP hhiF
  have hNPF : ∫ x in (N ∪ A) ∪ (P ∪ F), (f x - g x) ∂ν =
      ∫ x in N ∪ A, (f x - g x) ∂ν +
        ∫ x in P ∪ F, (f x - g x) ∂ν := by
    apply setIntegral_union
    · refine Set.disjoint_left.2 ?_
      intro x hxNA hxPF
      rcases hxNA with hxN | hxA <;> rcases hxPF with hxP | hxF
      · exact hdisjNP.le_bot ⟨hxN, hxP⟩
      · exact hdisjNF.le_bot ⟨hxN, hxF⟩
      · exact hdisjAP.le_bot ⟨hxA, hxP⟩
      · exact hdisjAF.le_bot ⟨hxA, hxF⟩
    · exact hmeasP.union hmeasF
    · exact hhi.integrableOn.mono_set (Set.subset_univ _)
    · exact hhi.integrableOn.mono_set (Set.subset_univ _)
  have hglobal : ∫ x, (f x - g x) ∂ν =
      ∫ x in N ∪ A, (f x - g x) ∂ν +
        ∫ x in P ∪ F, (f x - g x) ∂ν := by
    have hunion' : (N ∪ A) ∪ (P ∪ F) = (Set.univ : Set ℝ) := by
      simpa [union_assoc] using hunion
    rw [← setIntegral_univ, ← hunion']
    exact hNPF
  have hNA' : ∫ x in N ∪ A, (f x - g x) ∂ν =
      (∫ x in N, f x ∂ν - ∫ x in N, g x ∂ν) +
      (∫ x in A, f x ∂ν - ∫ x in A, g x ∂ν) := by
    rw [hNA]
    have hN' := integral_sub hf.integrableOn hg.integrableOn (μ := ν.restrict N)
    have hA' := integral_sub hf.integrableOn hg.integrableOn (μ := ν.restrict A)
    rw [hN', hA']
  have hPF' : ∫ x in P ∪ F, (f x - g x) ∂ν =
      (∫ x in P, f x ∂ν - ∫ x in P, g x ∂ν) +
      (∫ x in F, f x ∂ν - ∫ x in F, g x ∂ν) := by
    rw [hPF]
    have hP' := integral_sub hf.integrableOn hg.integrableOn (μ := ν.restrict P)
    have hF' := integral_sub hf.integrableOn hg.integrableOn (μ := ν.restrict F)
    rw [hP', hF']
  calc
    |(∫ x, f x ∂ν) - ∫ x, g x ∂ν| =
        |∫ x, (f x - g x) ∂ν| := by rw [integral_sub hf hg]
    _ = |((∫ x in N, f x ∂ν - ∫ x in N, g x ∂ν) +
        (∫ x in A, f x ∂ν - ∫ x in A, g x ∂ν)) +
        ((∫ x in P, f x ∂ν - ∫ x in P, g x ∂ν) +
        (∫ x in F, f x ∂ν - ∫ x in F, g x ∂ν))| := by
      rw [hglobal, hNA', hPF']
    _ ≤
        |∫ x in N, f x ∂ν - ∫ x in N, g x ∂ν| +
          |∫ x in A, f x ∂ν - ∫ x in A, g x ∂ν| +
          |∫ x in P, f x ∂ν - ∫ x in P, g x ∂ν| +
          |∫ x in F, f x ∂ν - ∫ x in F, g x ∂ν| := by
      calc
        _ ≤ |(∫ x in N, f x ∂ν - ∫ x in N, g x ∂ν) +
              (∫ x in A, f x ∂ν - ∫ x in A, g x ∂ν)| +
            |(∫ x in P, f x ∂ν - ∫ x in P, g x ∂ν) +
              (∫ x in F, f x ∂ν - ∫ x in F, g x ∂ν)| := abs_add_le _ _
        _ ≤ (|∫ x in N, f x ∂ν - ∫ x in N, g x ∂ν| +
              |∫ x in A, f x ∂ν - ∫ x in A, g x ∂ν|) +
            (|∫ x in P, f x ∂ν - ∫ x in P, g x ∂ν| +
              |∫ x in F, f x ∂ν - ∫ x in F, g x ∂ν|) := by
          gcongr <;> exact abs_add_le _ _
        _ = _ := by ring
    _ ≤ n + a + p + q := by linarith [hN, hA, hP, hF]
    _ = a + n + p + q := by ring

theorem abs_setIntegral_sub_le_of_uniform
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    {S : Set ℝ} {u v : ℝ → ℝ} (hS : MeasurableSet S)
    (hu : IntegrableOn u S ν) (hv : IntegrableOn v S ν)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ x ∈ S, |u x - v x| ≤ ε)
    (hmass : ν.real S ≤ 1) :
    |(∫ x in S, u x ∂ν) - ∫ x in S, v x ∂ν| ≤ ε := by
  have hsub : IntegrableOn (fun x => u x - v x) S ν := hu.sub hv
  have hnorm : IntegrableOn (fun x => |u x - v x|) S ν := hsub.norm
  have hpoint : ∀ x ∈ S, |u x - v x| ≤ ε := hclose
  have hconst : IntegrableOn (fun _ : ℝ => ε) S ν := (integrable_const _).integrableOn
  have hmono : (∫ x in S, |u x - v x| ∂ν) ≤ ε * ν.real S := by
    calc
      (∫ x in S, |u x - v x| ∂ν) ≤ ∫ _x in S, ε ∂ν :=
        setIntegral_mono_on hnorm hconst hS hpoint
      _ = ε * ν.real S := by rw [setIntegral_const, smul_eq_mul]; ring
  have habs : |(∫ x in S, u x ∂ν) - ∫ x in S, v x ∂ν| ≤
      ∫ x in S, |u x - v x| ∂ν := by
    rw [← integral_sub hu hv]
    exact abs_integral_le_integral_abs
  exact habs.trans (hmono.trans (by nlinarith))

theorem setIntegral_nonneg_subset_le
    {ν : Measure ℝ} [IsFiniteMeasure ν] {u : ℝ → ℝ}
    {S T : Set ℝ} (_hT : MeasurableSet T) (hsub : S ⊆ T)
    (hu : IntegrableOn u T ν) (hu0 : ∀ x, 0 ≤ u x) :
    ∫ x in S, u x ∂ν ≤ ∫ x in T, u x ∂ν := by
  apply setIntegral_mono_set hu
  · exact ae_of_all _ (fun x => hu0 x)
  · exact Eventually.of_forall (fun x hx => hsub hx)

/-! The four cut-off scales can be chosen before taking the budget limit. -/

theorem exists_leading_cutoff_parameters
    [SFinite μ] (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνac : ν ≪ (volume : Measure ℝ))
    (hνabs : Integrable (fun r : ℝ => |r|) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ C ∧
      (2 * frozenUniformMeanConstant * (1 + δ) +
        4 * (gaussianExcessExpMomentBound 2 + δ)) *
          (2 * nativeFirstMarginConcentrationConstant 1 * δ) < ε / 8 ∧
      4 * (gaussianExcessExpMomentBound 2 + δ) *
          ν.real (Icc (-δ) δ) < ε / 8 ∧
      (4 * frozenUniformMeanConstant / C) * stationaryMarginMomentBound 2 < ε / 8 ∧
      ∫ r in {r : ℝ | C < |r|}, marginLeadingReward X μ r ∂ν < ε / 8 := by
  let F : ℝ := frozenUniformMeanConstant
  let M : ℝ := gaussianExcessExpMomentBound 2
  let k : ℝ := nativeFirstMarginConcentrationConstant 1
  let Q : ℝ := stationaryMarginMomentBound 2
  have hF : 0 ≤ F := by
    dsimp [F]
    exact frozenUniformMeanConstant_pos.le
  have hM : 0 ≤ M := by
    dsimp [M]
    exact (gaussianExcessExpMomentBound_pos 2).le
  have hk : 0 ≤ k := by
    dsimp [k]
    exact nativeFirstMarginConcentrationConstant_nonneg (by norm_num)
  have hQ : 0 ≤ Q := by
    dsimp [Q, stationaryMarginMomentBound, stationaryMarginPosMomentBound]
    have hEx : 0 ≤ stationaryExcessMomentBound 2 :=
      stationaryExcessMomentBound_nonneg 2
    have hTail : 0 ≤ expTailMomentSum 1 2 := expTailMomentSum_nonneg 1 2
    have hEnv : 0 ≤ nativeGaussianEnvelopeExpTailConstant :=
      nativeGaussianEnvelopeExpTailConstant_nonneg
    positivity
  let D : ℝ := 4 * F + 4 * (M + 1)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  let H : ℝ := D * (2 * (k + 1)) + 1
  have hH : 0 < H := by
    dsimp [H]
    have : 0 ≤ D * (2 * (k + 1)) := by positivity
    linarith
  let L : ℝ := 4 * (M + 1) + 1
  have hL : 0 < L := by
    dsimp [L]
    linarith
  obtain ⟨δ₀, hδ₀, hmass₀⟩ :=
    exists_measureReal_zeroNeighbourhood_lt hνac
      (ε := ε / (8 * L)) (by positivity)
  obtain ⟨C₀, hC₀, htail₀⟩ :=
    exists_marginLeadingReward_far_cutoff hX hi hG hνabs (ε := ε / 8)
      (by linarith)
  let δ₁ : ℝ := min (1 / 2) (ε / (16 * H))
  have hδ₁ : 0 < δ₁ := by
    dsimp [δ₁]
    apply lt_min
    · norm_num
    · positivity
  have hδ₁le : δ₁ ≤ 1 := by
    dsimp [δ₁]
    linarith [min_le_left (1 / 2 : ℝ) (ε / (16 * H))]
  let δ : ℝ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  have hδle : δ ≤ 1 := (min_le_right _ _).trans hδ₁le
  have hδle₀ : δ ≤ δ₀ := min_le_left _ _
  have hδle₁ : δ ≤ δ₁ := min_le_right _ _
  have hmass : ν.real (Icc (-δ) δ) ≤ ν.real (Icc (-δ₀) δ₀) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro x hx
    exact mem_Icc.mpr ⟨by
      have := (mem_Icc.mp hx).1
      exact (neg_le_neg hδle₀).trans this,
      (mem_Icc.mp hx).2.trans hδle₀⟩
  have hmass' : ν.real (Icc (-δ) δ) < ε / (8 * L) :=
    lt_of_le_of_lt hmass hmass₀
  let C₁ : ℝ := 16 * (4 * F * Q + 1) / ε + 1
  have hC₁ : 1 ≤ C₁ := by
    dsimp [C₁]
    have : 0 ≤ 16 * (4 * F * Q + 1) / ε := by positivity
    linarith
  let C : ℝ := max (max C₀ C₁) (max 1 δ)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_max_of_le_right (le_max_left _ _)
  have hδC : δ ≤ C := le_trans hδle (hC)
  have hC₀C : C₀ ≤ C := by
    dsimp [C]
    exact le_max_of_le_left (le_max_left _ _)
  have hC₁C : C₁ ≤ C := by
    dsimp [C]
    exact le_max_of_le_left (le_max_right _ _)
  have htail : ∫ r in {r : ℝ | C < |r|}, marginLeadingReward X μ r ∂ν < ε / 8 := by
    have hsub : {r : ℝ | C < |r|} ⊆ {r : ℝ | C₀ < |r|} := by
      intro r hr
      exact lt_of_le_of_lt hC₀C hr
    have hnon : ∀ r, 0 ≤ marginLeadingReward X μ r :=
      fun r => marginLeadingReward_nonneg hX hi hG
    have hfin := marginLeadingReward_integrable_of_abs_integrable hX hi hG hνabs
    exact (setIntegral_nonneg_subset_le
      (KernelLimit.measurableSet_abs_gt C₀) hsub hfin.integrableOn hnon).trans_lt htail₀
  have hcentral_fin :
      (2 * F * (1 + δ) + 4 * (M + δ)) * (2 * k * δ) < ε / 8 := by
    have hcoef : 2 * F * (1 + δ) + 4 * (M + δ) ≤ D := by
      dsimp [D]
      have h1 : 1 + δ ≤ 2 := by linarith
      have h2 : M + δ ≤ M + 1 := by linarith
      have hleft : 2 * F * (1 + δ) ≤ 4 * F := by
        nlinarith
      have hright : 4 * (M + δ) ≤ 4 * (M + 1) := by
        nlinarith
      linarith
    have hδbound : δ ≤ ε / (16 * H) := by
      dsimp [δ₁] at hδle₁
      exact le_trans hδle₁ (min_le_right _ _)
    have hkbound : 2 * k ≤ 2 * (k + 1) := by linarith
    have hnonD : 0 ≤ D := hD
    have hnonδ : 0 ≤ δ := hδ.le
    have hprod : D * (2 * k * δ) ≤ D * (2 * (k + 1) * δ) := by
      gcongr
    have hHdef : D * (2 * (k + 1)) < H := by
      dsimp [H]
      linarith
    have hprod' : D * (2 * (k + 1) * δ) < ε / 8 := by
      have hδ' : D * (2 * (k + 1)) * δ ≤
          H * (ε / (16 * H)) := by
        gcongr
      have hHe : H * (ε / (16 * H)) = ε / 16 := by
        field_simp
      have hprod'' : D * (2 * (k + 1)) * δ ≤ ε / 16 := by
        calc
          D * (2 * (k + 1)) * δ ≤ H * (ε / (16 * H)) := hδ'
          _ = ε / 16 := hHe
      linarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcoef (by positivity))
      (lt_of_le_of_lt hprod hprod')
  have hcentral_lim :
      4 * (M + δ) * ν.real (Icc (-δ) δ) < ε / 8 := by
    have hcoef : 4 * (M + δ) ≤ L := by
      dsimp [L]
      have : M + δ ≤ M + 1 := by linarith
      nlinarith
    have hmass_nonneg : 0 ≤ ν.real (Icc (-δ) δ) := ENNReal.toReal_nonneg
    have hmul : 4 * (M + δ) * ν.real (Icc (-δ) δ) ≤
        L * ν.real (Icc (-δ) δ) := by
      exact mul_le_mul_of_nonneg_right hcoef hmass_nonneg
    have hsmall : L * ν.real (Icc (-δ) δ) < ε / 8 := by
      have := mul_lt_mul_of_pos_left hmass' hL
      have hcancel : L * (ε / (8 * L)) = ε / 8 := by
        field_simp
      rw [hcancel] at this
      exact this
    exact hmul.trans_lt hsmall
  have htail_fin :
      (4 * F / C) * Q < ε / 8 := by
    have hA : 0 ≤ 4 * F * Q := by positivity
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
    have hC₁bound : 16 * (4 * F * Q + 1) / ε < C := by
      have hbase : 16 * (4 * F * Q + 1) / ε < C₁ := by
        dsimp [C₁]
        linarith
      exact lt_of_lt_of_le hbase hC₁C
    have hrewrite : (4 * F / C) * Q = (4 * F * Q) / C := by ring
    rw [hrewrite]
    apply (div_lt_iff₀ hCpos).2
    have hnum : 4 * F * Q < ε * C / 8 := by
      have hmul := mul_lt_mul_of_pos_right hC₁bound (by positivity : 0 < ε)
      have heq :
          16 * (4 * F * Q + 1) / ε * ε = 16 * (4 * F * Q + 1) := by
        field_simp
      rw [heq] at hmul
      nlinarith [hmul]
    nlinarith
  refine ⟨δ, C, hδ, hδle, hC, ?_, ?_, ?_, htail⟩
  · simpa [F, M, k] using hcentral_fin
  · simpa [M] using hcentral_lim
  · simpa [F, Q] using htail_fin

/-! ## Uniform square moments for the actual reflected margin laws -/

theorem stationaryMarginLaw_sq_moment_data [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {E : ℝ} (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    Integrable (fun r : ℝ => |r| ^ 2) (stationaryMarginLaw E π) ∧
      (∫ r : ℝ, |r| ^ 2 ∂(stationaryMarginLaw E π)) ≤
        stationaryMarginMomentBound 2 := by
  let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let ν : Measure ℝ := stationaryMarginLaw E π
  let _ : IsProbabilityMeasure ν := isProbabilityMeasure_stationaryMarginLaw E π
  have hπpow : Integrable (fun y : ℝ => |E - abs y| ^ 2) π :=
    stationary_margin_abs_pow_integrable hX hi hG hE hπ (k := 2) (by norm_num)
  have hνpow : Integrable (fun r : ℝ => |r| ^ 2) ν := by
    rw [show ν = stationaryMarginLaw E π by rfl, stationaryMarginLaw]
    apply (integrable_map_measure (continuous_abs.pow 2).aestronglyMeasurable
      (measurable_reflectedMargin E).aemeasurable).mpr
    simpa [Function.comp_def] using hπpow
  have hmap := MeasureTheory.integral_map (μ := π)
      (φ := fun y : ℝ => E - |y|)
      (measurable_reflectedMargin E).aemeasurable
      ((continuous_abs.pow 2).aestronglyMeasurable)
  have heq : (∫ r, |r| ^ 2 ∂ν) =
      ∫ y, |E - abs y| ^ 2 ∂π := by
    simpa [ν, stationaryMarginLaw, Function.comp_def] using hmap
  refine ⟨hνpow, ?_⟩
  rw [heq]
  exact nativeRestart_stationary_margin_pow_le hX hi hG hE hπ
    (k := 2) (by norm_num)

theorem stationaryMarginProb_sq_moment_data [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {budget : ι → ℝ} {πs : ι → Measure ℝ}
    (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hπinv : ∀ i, (nativeRestartKernel X μ (budget i)).Invariant (πs i)) :
    ∀ i, Integrable (fun r : ℝ => |r| ^ 2)
        (stationaryMarginProb (budget i) (πs i) (hπP i) : Measure ℝ) ∧
      (∫ r : ℝ, |r| ^ 2 ∂
        (stationaryMarginProb (budget i) (πs i) (hπP i) : Measure ℝ)) ≤
        stationaryMarginMomentBound 2 := by
  intro i
  exact stationaryMarginLaw_sq_moment_data hX hi hG (hbudget i) (hπinv i)

/-! A weak-limit wrapper which no longer leaves first-moment integrability as
an unspoken UI assumption. -/

theorem limit_margin_first_moment_of_actual_sq_moments [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} {πs : ι → Measure ℝ}
    (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hπinv : ∀ i, (nativeRestartKernel X μ (budget i)).Invariant (πs i))
    {ν : ProbabilityMeasure ℝ}
    (hν : Tendsto
      (fun i => stationaryMarginProb (budget i) (πs i) (hπP i)) l (𝓝 ν)) :
    Integrable (fun r : ℝ => |r|) (ν : Measure ℝ) := by
  have hdata := stationaryMarginProb_sq_moment_data hX hi hG hbudget hπP hπinv
  exact limit_integrable_abs_of_uniform_sq_moment hν
    (M := stationaryMarginMomentBound 2)
    (fun i => hdata i |>.1) (fun i => hdata i |>.2)

/-! ## The concrete bounded-continuous transfer for the actual laws

The next theorem discharges the remainder interface in the final limit theorem.
All four pieces of the real line are visible in the proof: the central ramp,
the negative carry, the positive compact annulus, and the compact-cutoff tail.
-/

theorem leadingCoefficient_integralTransfer_actual [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop)
    {πs : ι → Measure ℝ}
    (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hπinv : ∀ i,
      (nativeRestartKernel X μ (budget i)).Invariant (πs i))
    {ν : ProbabilityMeasure ℝ}
    (hν : Tendsto
      (fun i => stationaryMarginProb (budget i) (πs i) (hπP i)) l (𝓝 ν))
    (hνac : (ν : Measure ℝ) ≪ (volume : Measure ℝ)) :
    IntegralTransferHypothesis (l := l)
      (νs := fun i => stationaryMarginProb (budget i) (πs i) (hπP i))
      (ν := ν)
      (fun i r => normalizedFrozenMean X μ (budget i) r)
      (marginLeadingReward X μ) := by
  let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let νlim : Measure ℝ := (ν : Measure ℝ)
  have hνabs : Integrable (fun r : ℝ => |r|) νlim := by
    exact limit_margin_first_moment_of_actual_sq_moments
      (X := X) (μ := μ) hX hi hG hbudget hπP hπinv hν
  intro ε hε
  obtain ⟨δ, C, hδ, hδ1, hC, hcentral_fin, hcentral_lim,
      htail_fin, htail_lim⟩ :=
    exists_leading_cutoff_parameters (X := X) (μ := μ) hX hi hG
      (ν := νlim) hνac hνabs hε
  obtain ⟨B, hB⟩ := marginLeadingReward_continuousCutoff_bounded
    (X := X) (μ := μ) hX hi hG (δ := δ) (C := C)
      (zero_le_one.trans hC)
  let g : ℝ → ℝ := marginLeadingReward_continuousCutoff X μ δ C
  have hgcont : Continuous g := by
    exact marginLeadingReward_continuousCutoff_continuous
      (X := X) (μ := μ) hX hi hG δ C
  have hgbound : ∀ x, |g x| ≤ B := by
    intro x
    exact hB x
  have hglim : Integrable g νlim := by
    dsimp [g, νlim]
    exact marginLeadingReward_continuousCutoff_integrable
      (X := X) (μ := μ) (ν := (ν : Measure ℝ)) hX hi hG
        (zero_le_one.trans hC)
  have hlimit_cutoff_error :
      |(∫ r, marginLeadingReward X μ r * compactCutoff C r ∂νlim) -
          ∫ r, g r ∂νlim| < ε / 4 := by
    let fcut : ℝ → ℝ := fun r =>
      marginLeadingReward X μ r * compactCutoff C r
    have hfcut : Integrable fcut νlim := by
      dsimp [fcut, νlim]
      exact (marginLeadingReward_integrable_of_abs_integrable
        (X := X) (μ := μ) hX hi hG hνabs).mul_bdd (μ := (ν : Measure ℝ))
        (compactCutoff_continuous C).measurable.aestronglyMeasurable
        (ae_of_all _ (fun r => by
          rw [Real.norm_eq_abs, abs_of_nonneg (compactCutoff_nonneg C r)]
          exact compactCutoff_le_one C r))
    have hfour := abs_integral_sub_le_of_four_regions
      (ν := νlim) hfcut hglim hδ (by linarith : δ ≤ C + 1)
      (a := 4 * (gaussianExcessExpMomentBound 2 + δ) *
        νlim.real (Icc (-δ) δ)) (n := 0) (p := 0) (q := 0)
      (by
        simpa [fcut, g] using
          (marginLeadingReward_compactCutoff_continuousCutoff_central_error_le
            (X := X) (μ := μ) hX hi hG hνabs hδ
              (zero_le_one.trans hC)))
      (by
        have hfzero : ∀ x ∈ Iio (-δ), fcut x = 0 := by
          intro x hx
          have hxneg : x < -δ := mem_Iio.mp hx
          have hx0 : x ≤ 0 := by linarith
          simp [fcut, marginLeadingReward, not_lt.mpr hx0]
        have hgzero : ∀ x ∈ Iio (-δ), g x = 0 := by
          intro x hx
          dsimp [g]
          have hx0 : x ≤ 0 := by
            have hxneg : x < -δ := mem_Iio.mp hx
            linarith
          exact marginLeadingReward_continuousCutoff_eq_zero_of_nonpos
            hX hi hG hδ hx0
        rw [setIntegral_eq_zero_of_forall_eq_zero hfzero,
          setIntegral_eq_zero_of_forall_eq_zero hgzero]
        simp)
      (by
        have heq : ∀ x ∈ Ioc δ (C + 1), fcut x = g x := by
          intro x hx
          have hxδ : δ ≤ x := (mem_Ioc.mp hx).1.le
          have hxpos : 0 < x := lt_of_lt_of_le hδ hxδ
          have hramp : positiveMarginRamp δ x = 1 :=
            positiveMarginRamp_eq_one_of_ge hδ hxδ
          have hmargin : marginLeadingReward X μ x =
              4 * gaussianRenewalPotential X μ (max x 0) := by
            unfold marginLeadingReward
            rw [if_pos hxpos, max_eq_left hxpos.le]
          dsimp [fcut, g, marginLeadingReward_continuousCutoff]
          rw [hmargin, hramp]
          ring
        rw [setIntegral_congr_fun measurableSet_Ioc heq]
        simp)
      (by
        have heq : ∀ x ∈ Ioi (C + 1), fcut x = g x := by
          intro x hx
          have hxgt : C + 1 < x := mem_Ioi.mp hx
          have hxpos : 0 < x := by linarith [hC, hxgt]
          have habs : C + 1 ≤ |x| := by
            rw [abs_of_pos hxpos]
            exact le_of_lt hxgt
          have hcut : compactCutoff C x = 0 := compactCutoff_eq_zero habs
          simp [fcut, g, marginLeadingReward_continuousCutoff, hcut]
        rw [setIntegral_congr_fun measurableSet_Ioi heq]
        simp)
    have hfour' :
        |(∫ r, fcut r ∂νlim) - ∫ r, g r ∂νlim| ≤
          4 * (gaussianExcessExpMomentBound 2 + δ) *
            νlim.real (Icc (-δ) δ) := by
      simpa using hfour
    have hlt := hcentral_lim
    exact lt_of_le_of_lt hfour' (by linarith)

  have hnegative_event : ∀ᶠ i in l,
      ∫ r in Iio (-δ), normalizedFrozenMean X μ (budget i) r ∂
        (stationaryMarginLaw (budget i) (πs i)) < ε / 8 := by
    have hneg_tendsto := tendsto_normalizedFrozenMean_setIntegral_Iio_neg
      (X := X) (μ := μ) hX hi hG hbudget hbudget_top hπP hπinv hδ
    have hev := hneg_tendsto.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by linarith : 0 < ε / 8))
    filter_upwards [hev] with i hi'
    let _ : IsProbabilityMeasure (πs i) := hπP i
    let νi : Measure ℝ := stationaryMarginLaw (budget i) (πs i)
    let _ : IsProbabilityMeasure νi :=
      isProbabilityMeasure_stationaryMarginLaw (budget i) (πs i)
    have hnon : 0 ≤ ∫ r in Iio (-δ),
        normalizedFrozenMean X μ (budget i) r ∂νi := by
      apply setIntegral_nonneg measurableSet_Iio
      intro r hr
      exact normalizedFrozenMean_nonneg hX hi hG (by
        have hexp : (1 : ℝ) ≤ Real.exp 1 := by norm_num
        exact hexp.trans ((le_max_right _ _).trans
          ((le_max_left _ _).trans (hbudget i))))
    have hi'' : |∫ r in Iio (-δ),
        normalizedFrozenMean X μ (budget i) r ∂νi| < ε / 8 := by
      simpa [νi, Real.dist_eq] using hi'
    simpa [νi, abs_of_nonneg hnon] using hi''

  have hpositive_event : ∀ᶠ i in l, ∀ r ∈ Ioc δ (C + 1),
      |normalizedFrozenMean X μ (budget i) r * compactCutoff C r - g r| <
        ε / 8 := by
    have hunif := normalizedFrozenMean_tendstoUniformlyOn_of_tendsto_budget
      (X := X) (μ := μ) hbudget_top (K := Icc 0 (C + 1))
        isCompact_Icc (by
          intro r hr
          exact (mem_Icc.mp hr).1) hX hi hG
    have hev := (Metric.tendstoUniformlyOn_iff.mp hunif) (ε / 8)
      (by linarith : 0 < ε / 8)
    filter_upwards [hev] with i hi'
    intro r hr
    have hrδ : δ ≤ r := (mem_Ioc.mp hr).1.le
    have hr0 : 0 ≤ r := le_trans hδ.le hrδ
    have hrC : r ≤ C + 1 := (mem_Ioc.mp hr).2
    have hdiff : |normalizedFrozenMean X μ (budget i) r -
        4 * gaussianRenewalPotential X μ r| < ε / 8 := by
      simpa only [Real.dist_eq, abs_sub_comm] using
        hi' r (mem_Icc.mpr ⟨hr0, hrC⟩)
    have hRone : positiveMarginRamp δ r = 1 :=
      positiveMarginRamp_eq_one_of_ge hδ hrδ
    have hcut0 : 0 ≤ compactCutoff C r := compactCutoff_nonneg C r
    have hcut1 : compactCutoff C r ≤ 1 := compactCutoff_le_one C r
    have hq : g r =
        (4 * gaussianRenewalPotential X μ r) * compactCutoff C r := by
      dsimp [g, marginLeadingReward_continuousCutoff]
      rw [hRone, max_eq_left hr0]
      ring
    rw [hq]
    calc
      |normalizedFrozenMean X μ (budget i) r * compactCutoff C r -
          (4 * gaussianRenewalPotential X μ r) * compactCutoff C r| =
          |(normalizedFrozenMean X μ (budget i) r -
            4 * gaussianRenewalPotential X μ r) * compactCutoff C r| := by
        ring_nf
      _ = |normalizedFrozenMean X μ (budget i) r -
          4 * gaussianRenewalPotential X μ r| * |compactCutoff C r| :=
        abs_mul _ _
      _ ≤ |normalizedFrozenMean X μ (budget i) r -
          4 * gaussianRenewalPotential X μ r| := by
        have hmul := mul_le_mul_of_nonneg_left hcut1
          (abs_nonneg (normalizedFrozenMean X μ (budget i) r -
            4 * gaussianRenewalPotential X μ r))
        simpa [abs_of_nonneg hcut0] using hmul
      _ < ε / 8 := hdiff

  have hfinite_event : ∀ᶠ i in l,
      |(∫ r, normalizedFrozenMean X μ (budget i) r ∂
          (stationaryMarginLaw (budget i) (πs i))) -
        ∫ r, g r ∂(stationaryMarginLaw (budget i) (πs i))| < ε := by
    filter_upwards [hnegative_event, hpositive_event] with i hneg hpos
    let _ : IsProbabilityMeasure (πs i) := hπP i
    let νi : Measure ℝ := stationaryMarginLaw (budget i) (πs i)
    let _ : IsProbabilityMeasure νi :=
      isProbabilityMeasure_stationaryMarginLaw (budget i) (πs i)
    let fi : ℝ → ℝ := normalizedFrozenMean X μ (budget i)
    let fci : ℝ → ℝ := fun r => fi r * compactCutoff C r
    have hfi : Integrable fi νi := by
      dsimp [fi, νi]
      exact normalizedFrozenMean_integrable_stationaryMarginLaw
        (X := X) (μ := μ) hX hi hG (hbudget i) (hπinv i)
    have hfci : Integrable fci νi := by
      exact hfi.mul_bdd (μ := νi) (compactCutoff_continuous C).measurable.aestronglyMeasurable
        (ae_of_all _ (fun r => by
          rw [Real.norm_eq_abs, abs_of_nonneg (compactCutoff_nonneg C r)]
          exact compactCutoff_le_one C r))
    have hgi : Integrable g νi := by
      dsimp [g]
      exact marginLeadingReward_continuousCutoff_integrable
        (X := X) (μ := μ) (ν := νi) hX hi hG (zero_le_one.trans hC)
    have hcoef : 0 ≤
        2 * frozenUniformMeanConstant * (1 + δ) +
          4 * (gaussianExcessExpMomentBound 2 + δ) := by
      have hF : 0 ≤ frozenUniformMeanConstant := frozenUniformMeanConstant_pos.le
      have hM : 0 ≤ gaussianExcessExpMomentBound 2 :=
        (gaussianExcessExpMomentBound_pos 2).le
      positivity
    have hmass := stationaryMarginLaw_zero_interval_le_linear
      (X := X) (μ := μ) hX hi hG (hbudget i) hδ.le hδ1 (hπinv i)
    have hcentral :
        |(∫ r in Icc (-δ) δ, fci r ∂νi) -
          ∫ r in Icc (-δ) δ, g r ∂νi| ≤
        (2 * frozenUniformMeanConstant * (1 + δ) +
          4 * (gaussianExcessExpMomentBound 2 + δ)) *
          (2 * nativeFirstMarginConcentrationConstant 1 * δ) := by
      have hc := normalizedFrozenMean_compactCutoff_continuousCutoff_central_error_le
        (X := X) (μ := μ) hX hi hG (E := budget i) (δ := δ) (C := C)
        (hbudget i) hδ hδ1 (zero_le_one.trans hC) (hπinv i)
      have hc' := hc.trans (mul_le_mul_of_nonneg_left hmass hcoef)
      simpa [fi, fci, νi, g] using hc'
    have hfi_nonneg : ∀ r, 0 ≤ fi r := by
      intro r
      exact normalizedFrozenMean_nonneg hX hi hG (by
        have hexp : (1 : ℝ) ≤ Real.exp 1 := by norm_num
        exact hexp.trans ((le_max_right _ _).trans
          ((le_max_left _ _).trans (hbudget i))))
    have hneg_i : ∫ r in Iio (-δ), fci r ∂νi ≤ ε / 8 := by
      have hpoint : ∀ r ∈ Iio (-δ), fci r ≤ fi r := by
        intro r hr
        exact mul_le_of_le_one_right (hfi_nonneg r)
          (compactCutoff_le_one C r)
      have hmono := setIntegral_mono_on hfci.integrableOn hfi.integrableOn
        measurableSet_Iio hpoint
      have hneg' : ∫ r in Iio (-δ), fi r ∂νi < ε / 8 := by
        simpa [fi, νi] using hneg
      exact hmono.trans (le_of_lt hneg')
    have hneg_abs :
        |(∫ r in Iio (-δ), fci r ∂νi) -
          ∫ r in Iio (-δ), g r ∂νi| ≤ ε / 8 := by
      have hgzero : ∀ r ∈ Iio (-δ), g r = 0 := by
        intro r hr
        dsimp [g]
        have hr0 : r ≤ 0 := by linarith [mem_Iio.mp hr, hδ]
        exact marginLeadingReward_continuousCutoff_eq_zero_of_nonpos
          hX hi hG hδ hr0
      rw [setIntegral_eq_zero_of_forall_eq_zero hgzero]
      have hnon : 0 ≤ ∫ r in Iio (-δ), fci r ∂νi :=
        setIntegral_nonneg measurableSet_Iio (fun r hr =>
          mul_nonneg (by exact hfi_nonneg r) (compactCutoff_nonneg C r))
      simpa [sub_zero, abs_of_nonneg hnon] using hneg_i
    have hpos_abs :
        |(∫ r in Ioc δ (C + 1), fci r ∂νi) -
          ∫ r in Ioc δ (C + 1), g r ∂νi| ≤ ε / 8 := by
      apply abs_setIntegral_sub_le_of_uniform measurableSet_Ioc
        hfci.integrableOn hgi.integrableOn (by linarith : 0 ≤ ε / 8)
      · intro r hr
        exact le_of_lt (by simpa [fi, fci] using hpos r hr)
      · exact MeasureTheory.measureReal_le_one
    have hfar_abs :
        |(∫ r in Ioi (C + 1), fci r ∂νi) -
          ∫ r in Ioi (C + 1), g r ∂νi| ≤ 0 := by
      have heq : ∀ r ∈ Ioi (C + 1), fci r = g r := by
        intro r hr
        have hrgt : C + 1 < r := mem_Ioi.mp hr
        have hrpos : 0 < r := by linarith [hC, hrgt]
        have hcut : compactCutoff C r = 0 := compactCutoff_eq_zero (by
          rw [abs_of_pos hrpos]
          exact le_of_lt hrgt)
        simp [fci, g, fi, marginLeadingReward_continuousCutoff, hcut]
      rw [setIntegral_congr_fun measurableSet_Ioi heq]
      simp
    have hfour := abs_integral_sub_le_of_four_regions
      (ν := νi) hfci hgi hδ (by linarith : δ ≤ C + 1)
      hcentral hneg_abs hpos_abs hfar_abs
    have hfour' : |(∫ r, fci r ∂νi) - ∫ r, g r ∂νi| ≤
        (2 * frozenUniformMeanConstant * (1 + δ) +
          4 * (gaussianExcessExpMomentBound 2 + δ)) *
            (2 * nativeFirstMarginConcentrationConstant 1 * δ) +
          ε / 4 := by
      calc
        _ ≤
            (2 * frozenUniformMeanConstant * (1 + δ) +
              4 * (gaussianExcessExpMomentBound 2 + δ)) *
                (2 * nativeFirstMarginConcentrationConstant 1 * δ) +
              ε / 8 + ε / 8 + 0 := by simpa using hfour
        _ ≤ _ := by ring_nf; linarith
    have htail_i := normalizedFrozenMean_compactCutoff_remainder_le
      (X := X) (μ := μ) hX hi hG (E := budget i) (C := C)
      (hbudget i) hC (hπinv i)
    have htail_i' :
        |(∫ r, fci r ∂νi) - ∫ r, fi r ∂νi| ≤
          (4 * frozenUniformMeanConstant / C) * stationaryMarginMomentBound 2 := by
      simpa [fi, fci, νi] using htail_i
    have huncut :
        |(∫ r, fi r ∂νi) - ∫ r, g r ∂νi| < ε := by
      have htail_i'' :
          |(∫ r, fi r ∂νi) - ∫ r, fci r ∂νi| ≤
            (4 * frozenUniformMeanConstant / C) * stationaryMarginMomentBound 2 := by
        simpa [abs_sub_comm] using htail_i'
      calc
        |(∫ r, fi r ∂νi) - ∫ r, g r ∂νi| ≤
            |(∫ r, fi r ∂νi) - ∫ r, fci r ∂νi| +
              |(∫ r, fci r ∂νi) - ∫ r, g r ∂νi| := by
          exact abs_sub_le _ _ _
        _ ≤ (4 * frozenUniformMeanConstant / C) * stationaryMarginMomentBound 2 +
              ((2 * frozenUniformMeanConstant * (1 + δ) +
                4 * (gaussianExcessExpMomentBound 2 + δ)) *
                (2 * nativeFirstMarginConcentrationConstant 1 * δ) + ε / 4) := by
          exact add_le_add htail_i'' hfour'
        _ < ε := by linarith [htail_fin, hcentral_fin]
    simpa [fi, νi] using huncut
  have hlimit_uncut :
      |(∫ r, marginLeadingReward X μ r ∂νlim) - ∫ r, g r ∂νlim| < ε := by
    have hrem := marginLeadingReward_compactCutoff_remainder_le
      (X := X) (μ := μ) hX hi hG hνabs (zero_le_one.trans hC)
    have hrem' :
        |(∫ r, marginLeadingReward X μ r ∂νlim) -
          ∫ r, marginLeadingReward X μ r * compactCutoff C r ∂νlim| < ε / 8 := by
      have hle := hrem
      rw [abs_sub_comm]
      exact lt_of_le_of_lt hle htail_lim
    calc
      |(∫ r, marginLeadingReward X μ r ∂νlim) - ∫ r, g r ∂νlim| ≤
          |(∫ r, marginLeadingReward X μ r ∂νlim) -
            ∫ r, marginLeadingReward X μ r * compactCutoff C r ∂νlim| +
            |(∫ r, marginLeadingReward X μ r * compactCutoff C r ∂νlim) -
              ∫ r, g r ∂νlim| := by
        exact abs_sub_le _ _ _
      _ < ε := by linarith [hrem', hlimit_cutoff_error]
  refine ⟨g, B, hgcont, hgbound, hfinite_event, ?_⟩
  simpa [νlim] using hlimit_uncut

end LeadingCoefficient
end SwingRepair
