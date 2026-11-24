import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic

/-! # From tail closeness to bounded Lipschitz test functions

`app:limit` passes from the uniform convergence of the overshoot tails to the
uniform convergence against bounded Lipschitz test functions by truncating the
overshoot variable.  This file proves that passage as a statement about two
probability laws on `[0,∞)`: if their tails agree to within `ε` at every
nonnegative level, then their integrals of a bounded Lipschitz function agree
to within an explicit multiple of `ε` plus a truncation error.

The argument uses no renewal input.  A continuous monotone bounded test
function is handled by the layer cake, because its superlevel sets are open
upper sets, hence open half-lines; a Lipschitz function is written as a
difference of two such functions after truncation.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-! ### Open upper sets of the line -/

/-- An open upper set of `ℝ` which is nonempty and misses a point is the open
half-line above its infimum. -/
theorem isOpen_upper_eq_Ioi {A : Set ℝ} (hopen : IsOpen A)
    (hup : ∀ x ∈ A, ∀ y, x ≤ y → y ∈ A) (hne : A.Nonempty) {z : ℝ} (hz : z ∉ A) :
    A = Ioi (sInf A) := by
  have hsub : A ⊆ Ioi z := by
    intro y hy
    by_contra hcon
    exact hz (hup y hy z (le_of_not_gt hcon))
  have hbdd : BddBelow A := ⟨z, fun y hy => (hsub hy).le⟩
  have hle : ∀ y ∈ A, sInf A ≤ y := fun y hy => csInf_le hbdd hy
  have hcA : sInf A ∉ A := by
    intro hcmem
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen _ hcmem
    have hmem : sInf A - δ/2 ∈ A := by
      refine hball ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    have := hle _ hmem
    linarith
  ext y
  constructor
  · intro hy
    rcases eq_or_lt_of_le (hle y hy) with h | h
    · exact absurd (show sInf A ∈ A by rw [h]; exact hy) hcA
    · exact h
  · intro hy
    obtain ⟨a, haA, hay⟩ := exists_lt_of_csInf_lt hne hy
    exact hup a haA y hay.le

/-! ### Continuous monotone test functions -/

/-- If two laws on `[0,∞)` have tails within `ε` at every nonnegative level,
their integrals of a continuous monotone function with values in `[0,S]` are
within `S*ε`. -/
theorem integral_sub_le_of_tail_close
    {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P (Iio 0) = 0) (hQ : Q (Iio 0) = 0)
    {ε : ℝ} (htail : ∀ t : ℝ, 0 ≤ t → |P.real (Ioi t) - Q.real (Ioi t)| ≤ ε)
    {u : ℝ → ℝ} (hcont : Continuous u) (hmono : Monotone u)
    {S : ℝ} (hu0 : ∀ x, 0 ≤ u x) (huS : ∀ x, u x ≤ S) :
    |(∫ x, u x ∂P) - ∫ x, u x ∂Q| ≤ S * ε := by
  have hS0 : 0 ≤ S := (hu0 0).trans (huS 0)
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (htail 0 le_rfl)
  -- the superlevel sets
  set A : ℝ → Set ℝ := fun t => {x : ℝ | t < u x} with hAdef
  have hAeq : ∀ t : ℝ, A t = u ⁻¹' Ioi t := fun t => rfl
  have hAopen : ∀ t, IsOpen (A t) := fun t => (hAeq t) ▸ isOpen_Ioi.preimage hcont
  have hAmeas : ∀ t, MeasurableSet (A t) := fun t => (hAopen t).measurableSet
  have hAup : ∀ t, ∀ x ∈ A t, ∀ y, x ≤ y → y ∈ A t := by
    intro t x hx y hxy
    exact lt_of_lt_of_le hx (hmono hxy)
  -- the pointwise comparison of the two superlevel measures
  have hkey : ∀ t : ℝ, 0 < t → |P.real (A t) - Q.real (A t)| ≤ ε := by
    intro t ht
    rcases eq_empty_or_nonempty (A t) with hempty | hne
    · rw [hempty]
      simpa using hε
    by_cases hall : ∀ z : ℝ, z ∈ A t
    · have hu : A t = univ := eq_univ_of_forall hall
      rw [hu]
      simpa using hε
    · obtain ⟨z, hz⟩ := not_forall.mp hall
      have hform := isOpen_upper_eq_Ioi (hAopen t) (hAup t) hne hz
      rw [hform]
      rcases le_or_gt 0 (sInf (A t)) with hc | hc
      · exact htail _ hc
      · have hsubP : Ici (0 : ℝ) ⊆ Ioi (sInf (A t)) := fun y hy => lt_of_lt_of_le hc hy
        have hone : ∀ R : Measure ℝ, IsProbabilityMeasure R → R (Iio 0) = 0 →
            R.real (Ioi (sInf (A t))) = 1 := by
          intro R hR hR0
          have hIci : R (Ici (0 : ℝ)) = 1 := by
            have : R (Iio (0 : ℝ)) + R (Ici (0 : ℝ)) = 1 := by
              rw [← measure_union (by
                  simp only [Set.disjoint_left, mem_Iio, mem_Ici]
                  intro x hx hx'
                  linarith) measurableSet_Ici,
                Iio_union_Ici, measure_univ]
            rw [hR0, zero_add] at this
            exact this
          have hle1 : (1 : ℝ≥0∞) ≤ R (Ioi (sInf (A t))) := hIci ▸ measure_mono hsubP
          have : R (Ioi (sInf (A t))) = 1 := le_antisymm prob_le_one hle1
          rw [Measure.real, this]
          simp
        rw [hone P inferInstance hP, hone Q inferInstance hQ]
        simpa using hε
  -- layer cake for both laws
  have hint : ∀ R : Measure ℝ, IsProbabilityMeasure R → Integrable u R := by
    intro R hR
    refine Integrable.mono' (integrable_const S) hcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hu0 x)]
    exact huS x
  have hlayer : ∀ R : Measure ℝ, IsProbabilityMeasure R →
      (∫ x, u x ∂R) = ∫ t in Ioc (0 : ℝ) S, R.real (A t) := by
    intro R hR
    rw [(hint R hR).integral_eq_integral_meas_lt (ae_of_all _ hu0)]
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Ioi
      Ioc_subset_Ioi_self ?_
    refine Eventually.of_forall (fun t ht => ?_)
    have htS : S < t := by
      rcases ht with ⟨ht1, ht2⟩
      have ht1' : (0 : ℝ) < t := ht1
      by_contra hcon
      exact ht2 ⟨ht1', le_of_not_gt hcon⟩
    have : A t = (∅ : Set ℝ) := by
      refine eq_empty_of_forall_notMem (fun x hx => ?_)
      have : t < u x := hx
      linarith [huS x]
    show R.real (A t) = 0
    rw [this]
    simp
  -- integrate the comparison
  have hmeasP : ∀ R : Measure ℝ, IsProbabilityMeasure R →
      Measurable (fun t => R.real (A t)) := by
    intro R hR
    refine Antitone.measurable (fun s t hst => ?_)
    refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    exact lt_of_le_of_lt hst hx
  have hIntOn : ∀ R : Measure ℝ, IsProbabilityMeasure R →
      IntegrableOn (fun t => R.real (A t)) (Ioc (0 : ℝ) S) volume := by
    intro R hR
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) S) volume :=
      integrableOn_const measure_Ioc_lt_top.ne
    refine Integrable.mono' hconst (hmeasP R hR).aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hconstε : IntegrableOn (fun _ : ℝ => ε) (Ioc (0 : ℝ) S) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  rw [hlayer P inferInstance, hlayer Q inferInstance,
    ← integral_sub (hIntOn P inferInstance) (hIntOn Q inferInstance)]
  calc |∫ t in Ioc (0 : ℝ) S, (P.real (A t) - Q.real (A t))|
      ≤ ∫ t in Ioc (0 : ℝ) S, |P.real (A t) - Q.real (A t)| := abs_integral_le_integral_abs
    _ ≤ ∫ _t in Ioc (0 : ℝ) S, ε :=
        setIntegral_mono_on ((hIntOn P inferInstance).sub (hIntOn Q inferInstance)).abs
          hconstε measurableSet_Ioc
          (fun t ht => hkey t ht.1)
    _ = S * ε := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
          ENNReal.toReal_ofReal hS0, smul_eq_mul]

/-! ### Bounded Lipschitz test functions -/

/-- The truncation of the overshoot variable to `[0,T]`. -/
def truncate (T x : ℝ) : ℝ := min (max x 0) T

theorem truncate_continuous (T : ℝ) : Continuous (truncate T) :=
  (continuous_id.max continuous_const).min continuous_const

theorem truncate_monotone (T : ℝ) : Monotone (truncate T) :=
  fun _ _ hxy => min_le_min (max_le_max hxy le_rfl) le_rfl

theorem truncate_nonneg {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : 0 ≤ truncate T x :=
  le_min (le_max_right _ _) hT

theorem truncate_le (T x : ℝ) : truncate T x ≤ T := min_le_right _ _

theorem truncate_eq_self {T x : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ T) : truncate T x = x := by
  rw [truncate, max_eq_left hx0, min_eq_left hxT]

/-- Truncating the test function: the paper's passage from uniform tail
convergence to uniform convergence against bounded Lipschitz test functions.
The bound is explicit in the Lipschitz constant, the sup norm, the truncation
level and the tail accuracy. -/
theorem integral_lipschitz_sub_le_of_tail_close
    {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P (Iio 0) = 0) (hQ : Q (Iio 0) = 0)
    {ε : ℝ} (htail : ∀ t : ℝ, 0 ≤ t → |P.real (Ioi t) - Q.real (Ioi t)| ≤ ε)
    {f : ℝ → ℝ} {K B T : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ K * |x - y|)
    (hB : ∀ x, |f x| ≤ B) (hT : 0 ≤ T) :
    |(∫ x, f x ∂P) - ∫ x, f x ∂Q| ≤
      (2*B + 2*K*T)*ε + 2*B*(P.real (Ioi T) + Q.real (Ioi T)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hcont : Continuous f := by
    refine Metric.continuous_iff.2 (fun x δ hδ => ?_)
    refine ⟨δ/(K+1), by positivity, fun y hy => ?_⟩
    rw [Real.dist_eq] at hy ⊢
    have h1 : |f y - f x| ≤ K*|y-x| := hlip y x
    have h2 : K*|y-x| ≤ K*(δ/(K+1)) := by
      refine mul_le_mul_of_nonneg_left hy.le hK
    have h3 : K*(δ/(K+1)) < δ := by
      rw [mul_div_assoc'] at *
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  set r : ℝ → ℝ := truncate T with hrdef
  set g : ℝ → ℝ := fun x => f (r x) - f 0 + K * r x with hgdef
  have hrc : Continuous r := truncate_continuous T
  have hrm : Monotone r := truncate_monotone T
  have hr0 : ∀ x, 0 ≤ r x := truncate_nonneg hT
  have hrT : ∀ x, r x ≤ T := truncate_le T
  have hgc : Continuous g := ((hcont.comp hrc).sub continuous_const).add (hrc.const_mul K)
  have hgm : Monotone g := by
    intro x y hxy
    have hrxy : r x ≤ r y := hrm hxy
    have h1 : f (r x) - f (r y) ≤ K * (r y - r x) := by
      have := hlip (r x) (r y)
      have habs : |r x - r y| = r y - r x := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [habs] at this
      exact (le_abs_self _).trans this
    simp only [hgdef]
    nlinarith
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    have h1 : f 0 - f (r x) ≤ K * r x := by
      have := hlip 0 (r x)
      have habs : |(0 : ℝ) - r x| = r x := by
        rw [zero_sub, abs_neg, abs_of_nonneg (hr0 x)]
      rw [habs] at this
      exact (le_abs_self _).trans this
    simp only [hgdef]
    linarith
  have hgS : ∀ x, g x ≤ 2*B + K*T := by
    intro x
    have h1 : f (r x) ≤ B := (le_abs_self _).trans (hB _)
    have h2 : -B ≤ f 0 := neg_le_of_neg_le ((neg_le_abs _).trans (hB 0))
    have h3 : K * r x ≤ K * T := mul_le_mul_of_nonneg_left (hrT x) hK
    simp only [hgdef]
    linarith
  -- the two monotone comparisons
  have hcmpg := integral_sub_le_of_tail_close hP hQ htail hgc hgm hg0 hgS
  have hcmpr := integral_sub_le_of_tail_close hP hQ htail hrc hrm hr0 hrT
  -- integrability of the bounded pieces
  have hintf : ∀ R : Measure ℝ, IsProbabilityMeasure R → Integrable f R := by
    intro R hR
    refine Integrable.mono' (integrable_const B) hcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hB x
  have hintfr' : ∀ R : Measure ℝ, IsProbabilityMeasure R →
      Integrable (fun x => f (r x)) R := by
    intro R hR
    refine Integrable.mono' (integrable_const B) (hcont.comp hrc).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hB _
  have hintr : ∀ R : Measure ℝ, IsProbabilityMeasure R → Integrable r R := by
    intro R hR
    refine Integrable.mono' (integrable_const T) hrc.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hr0 x)]
    exact hrT x
  have hintg : ∀ R : Measure ℝ, IsProbabilityMeasure R → Integrable g R := by
    intro R hR
    exact ((hintfr' R hR).sub (integrable_const _)).add ((hintr R hR).const_mul K)
  -- the truncated comparison
  have hsplit : ∀ R : Measure ℝ, IsProbabilityMeasure R →
      (∫ x, g x ∂R) = (∫ x, f (r x) ∂R) - f 0 + K * ∫ x, r x ∂R := by
    intro R hR
    have h1 : Integrable (fun x => f (r x) - f 0) R :=
      (hintfr' R hR).sub (integrable_const _)
    have h2 : Integrable (fun x => K * r x) R := (hintr R hR).const_mul K
    have hadd : (∫ x, g x ∂R) = (∫ x, (f (r x) - f 0) ∂R) + ∫ x, K * r x ∂R := by
      simp only [hgdef]
      exact integral_add h1 h2
    rw [hadd, integral_sub (hintfr' R hR) (integrable_const _), integral_const,
      integral_const_mul]
    simp
  have htrunc : |(∫ x, f (r x) ∂P) - ∫ x, f (r x) ∂Q| ≤ (2*B + 2*K*T)*ε := by
    have hP' := hsplit P inferInstance
    have hQ' := hsplit Q inferInstance
    have hK' : |K * ((∫ x, r x ∂P) - ∫ x, r x ∂Q)| ≤ K * (T*ε) := by
      rw [abs_mul, abs_of_nonneg hK]
      exact mul_le_mul_of_nonneg_left hcmpr hK
    have heq : (∫ x, f (r x) ∂P) - ∫ x, f (r x) ∂Q =
        ((∫ x, g x ∂P) - ∫ x, g x ∂Q) - K * ((∫ x, r x ∂P) - ∫ x, r x ∂Q) := by
      rw [hP', hQ']
      ring
    rw [heq]
    calc |((∫ x, g x ∂P) - ∫ x, g x ∂Q) - K * ((∫ x, r x ∂P) - ∫ x, r x ∂Q)|
        ≤ |(∫ x, g x ∂P) - ∫ x, g x ∂Q| + |K * ((∫ x, r x ∂P) - ∫ x, r x ∂Q)| :=
          abs_sub _ _
      _ ≤ (2*B + K*T)*ε + K*(T*ε) := add_le_add hcmpg hK'
      _ = (2*B + 2*K*T)*ε := by ring
  -- the truncation error
  have htail_err : ∀ R : Measure ℝ, IsProbabilityMeasure R → R (Iio 0) = 0 →
      |(∫ x, f x ∂R) - ∫ x, f (r x) ∂R| ≤ 2*B*R.real (Ioi T) := by
    intro R hR hR0
    have hae : ∀ᵐ x ∂R, (0 : ℝ) ≤ x := by
      rw [ae_iff]
      have hset : {x : ℝ | ¬ (0 : ℝ) ≤ x} = Iio (0 : ℝ) := by
        ext x
        simp
      rw [hset, hR0]
    have hdiff : Integrable (fun x => f x - f (r x)) R :=
      (hintf R hR).sub (hintfr' R hR)
    have hdom : Integrable (fun x => 2*B*(Ioi T).indicator (fun _ => (1:ℝ)) x) R := by
      refine ((integrable_const (1:ℝ)).indicator measurableSet_Ioi).const_mul (2*B)
    have hbound : ∀ᵐ x ∂R, |f x - f (r x)| ≤
        2*B*(Ioi T).indicator (fun _ => (1:ℝ)) x := by
      filter_upwards [hae] with x hx
      by_cases hxT : T < x
      · rw [Set.indicator_of_mem (show x ∈ Ioi T from hxT), mul_one]
        have h1 : |f x| ≤ B := hB x
        have h2 : |f (r x)| ≤ B := hB _
        calc |f x - f (r x)| ≤ |f x| + |f (r x)| := abs_sub _ _
          _ ≤ 2*B := by linarith
      · have hrx : r x = x := truncate_eq_self hx (le_of_not_gt hxT)
        rw [hrx, sub_self, abs_zero]
        have hind : (0:ℝ) ≤ (Ioi T).indicator (fun _ => (1:ℝ)) x :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) x
        exact mul_nonneg (by linarith) hind
    rw [← integral_sub (hintf R hR) (hintfr' R hR)]
    calc |∫ x, (f x - f (r x)) ∂R| ≤ ∫ x, |f x - f (r x)| ∂R :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x, 2*B*(Ioi T).indicator (fun _ => (1:ℝ)) x ∂R :=
          integral_mono_ae hdiff.abs hdom hbound
      _ = 2*B*R.real (Ioi T) := by
          rw [integral_const_mul, integral_indicator measurableSet_Ioi, integral_const]
          rw [smul_eq_mul, mul_one, Measure.real, Measure.real, Measure.restrict_apply_univ]
  have hPerr := htail_err P inferInstance hP
  have hQerr := htail_err Q inferInstance hQ
  calc |(∫ x, f x ∂P) - ∫ x, f x ∂Q|
      ≤ |(∫ x, f x ∂P) - ∫ x, f (r x) ∂P| +
        |((∫ x, f (r x) ∂P) - ∫ x, f (r x) ∂Q) + ((∫ x, f (r x) ∂Q) - ∫ x, f x ∂Q)| := by
        have : (∫ x, f x ∂P) - ∫ x, f x ∂Q =
            ((∫ x, f x ∂P) - ∫ x, f (r x) ∂P) +
              (((∫ x, f (r x) ∂P) - ∫ x, f (r x) ∂Q) +
                ((∫ x, f (r x) ∂Q) - ∫ x, f x ∂Q)) := by ring
        rw [this]
        exact abs_add_le _ _
    _ ≤ 2*B*P.real (Ioi T) +
        ((2*B + 2*K*T)*ε + 2*B*Q.real (Ioi T)) := by
        refine add_le_add hPerr ?_
        refine (abs_add_le _ _).trans (add_le_add htrunc ?_)
        rw [abs_sub_comm]
        exact hQerr
    _ = (2*B + 2*K*T)*ε + 2*B*(P.real (Ioi T) + Q.real (Ioi T)) := by ring

end SwingRepair
