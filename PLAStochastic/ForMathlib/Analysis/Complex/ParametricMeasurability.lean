import PLAStochastic.ForMathlib.Analysis.Complex.TaylorCoefficientLimit
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Measurability of complex derivatives, slopes and Taylor coefficients in a parameter

For a family `f : α → ℂ → ℂ` measurable in the parameter, the complex derivative, the slope
`dslope (f a) (x a) (y a)` and the Taylor coefficients at `0` are pointwise limits of
measurable difference quotients wherever they are genuine. The lemmas below produce one measurable
function that agrees with them at every parameter where the relevant differentiability holds;
no measurability of the set of such parameters is needed.
-/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory Finset
namespace PGM

variable {α : Type*} [MeasurableSpace α]

/-- A measurable sequence has one measurable function agreeing with its limit wherever the
limit exists. -/
theorem exists_measurable_eq_limit {g : ℕ → α → ℂ} (hg : ∀ i, Measurable (g i)) :
    ∃ L : α → ℂ, Measurable L ∧
      ∀ a c, Tendsto (fun i => g i a) atTop (𝓝 c) → L a = c := by
  refine ⟨fun a => limUnder atTop (fun i => g i a),
    (StronglyMeasurable.limUnder (l := atTop) fun i => (hg i).stronglyMeasurable).measurable,
    fun a c hc => hc.limUnder_eq⟩

/-- The points `(i + 1)⁻¹` tend to zero through nonzero complex values. -/
theorem complex_inv_succ_ne_zero (i : ℕ) : ((i : ℂ) + 1)⁻¹ ≠ 0 :=
  inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero i)

theorem tendsto_complex_inv_succ : Tendsto (fun i : ℕ => ((i : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
  simpa only [one_div] using h

/-- A parametric derivative at a moving point, with joint sample measurability. -/
theorem exists_measurable_eq_deriv_param {f : α → ℂ → ℂ} {x : α → ℂ}
    (hf : ∀ t : ℂ, Measurable fun a => f a (x a + t)) :
    ∃ D : α → ℂ, Measurable D ∧
      ∀ a, DifferentiableAt ℂ (f a) (x a) → D a = deriv (f a) (x a) := by
  have hm (i : ℕ) : Measurable fun a =>
      ((i : ℂ) + 1)⁻¹⁻¹ • (f a (x a + ((i : ℂ) + 1)⁻¹) - f a (x a)) := by
    have h0 : Measurable fun a => f a (x a) := by simpa only [add_zero] using hf 0
    exact ((hf _).sub h0).const_smul ((i : ℂ) + 1)⁻¹⁻¹
  obtain ⟨D, hD, hlim⟩ := exists_measurable_eq_limit hm
  refine ⟨D, hD, fun a ha => hlim a _ ?_⟩
  have h1 := ha.hasDerivAt.tendsto_slope_zero
  have h2 : Tendsto (fun i : ℕ => ((i : ℂ) + 1)⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_complex_inv_succ,
      Eventually.of_forall complex_inv_succ_ne_zero⟩
  exact h1.comp h2

/-- A parametric derivative at a fixed point, from measurability of the values alone. -/
theorem exists_measurable_eq_deriv_param_const {f : α → ℂ → ℂ} {z : ℂ}
    (hf : ∀ w, Measurable fun a => f a w) :
    ∃ D : α → ℂ, Measurable D ∧ ∀ a, DifferentiableAt ℂ (f a) z → D a = deriv (f a) z :=
  exists_measurable_eq_deriv_param (x := fun _ => z) fun t => hf (z + t)

/-- Everywhere-differentiable version: the parametric derivative is itself measurable. -/
theorem measurable_deriv_param_of_differentiableAt {f : α → ℂ → ℂ} {x : α → ℂ}
    (hf : Measurable (Function.uncurry f)) (hx : Measurable x)
    (hd : ∀ a, DifferentiableAt ℂ (f a) (x a)) :
    Measurable fun a => deriv (f a) (x a) := by
  obtain ⟨D, hD, he⟩ := exists_measurable_eq_deriv_param (f := f) (x := x)
    fun t => hf.comp (measurable_id.prodMk (hx.add_const t))
  have heq : D = fun a => deriv (f a) (x a) := funext fun a => he a (hd a)
  exact heq ▸ hD

/-- Slopes of an entire function are entire. -/
theorem differentiable_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (dslope f c) := by
  have hd := (differentiableOn_dslope (s := univ) (c := c) univ_mem).mpr hf.differentiableOn
  exact fun ξ => (hd ξ (mem_univ ξ)).differentiableAt univ_mem

/-- The slope `dslope (f a) (x a)` is jointly measurable in the parameter and the spatial
variable whenever every `f a` is differentiable at its moving node. -/
theorem measurable_uncurry_dslope_param {f : α → ℂ → ℂ} {x : α → ℂ}
    (hf : Measurable (Function.uncurry f)) (hx : Measurable x)
    (hd : ∀ a, DifferentiableAt ℂ (f a) (x a)) :
    Measurable (Function.uncurry fun a => dslope (f a) (x a)) := by
  have hD := measurable_deriv_param_of_differentiableAt hf hx hd
  have hset : MeasurableSet {p : α × ℂ | p.2 = x p.1} :=
    measurableSet_eq_fun measurable_snd (hx.comp measurable_fst)
  have hxv : Measurable fun p : α × ℂ => f p.1 (x p.1) :=
    hf.comp (measurable_fst.prodMk (hx.comp measurable_fst))
  have hS : Measurable fun p : α × ℂ => (p.2 - x p.1)⁻¹ • (f p.1 p.2 - f p.1 (x p.1)) :=
    ((measurable_snd.sub (hx.comp measurable_fst)).inv).smul (hf.sub hxv)
  classical
  have heq : (Function.uncurry fun a => dslope (f a) (x a)) = fun p : α × ℂ =>
      if p.2 = x p.1 then deriv (f p.1) (x p.1)
      else (p.2 - x p.1)⁻¹ • (f p.1 p.2 - f p.1 (x p.1)) := by
    funext p
    by_cases hp : p.2 = x p.1
    · simp only [Function.uncurry, hp, dslope_same, if_true]
    · simp only [Function.uncurry, hp, if_false, dslope_of_ne _ hp, slope_def_module]
  rw [heq]
  exact Measurable.ite hset (hD.comp measurable_fst) hS

theorem measurable_dslope_param {f : α → ℂ → ℂ} {x y : α → ℂ}
    (hf : Measurable (Function.uncurry f)) (hx : Measurable x) (hy : Measurable y)
    (hd : ∀ a, DifferentiableAt ℂ (f a) (x a)) :
    Measurable fun a => dslope (f a) (x a) (y a) :=
  (measurable_uncurry_dslope_param hf hx hd).comp (measurable_id.prodMk hy)

/-- Finite Taylor remainders of a function holomorphic near `0` are `O(‖h‖ⁿ)` along every
sequence tending to `0`. -/
theorem exists_eventually_norm_sub_complexTaylorSum_le {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball 0 r)) {h : ℕ → ℂ} (hlim : Tendsto h atTop (𝓝 0))
    (n : ℕ) : ∃ K : ℝ, ∀ᶠ i in atTop,
      ‖f (h i) - complexTaylorSum f n 0 (h i)‖ ≤ K * ‖h i‖ ^ n := by
  have hR : 0 < r / 2 := half_pos hr
  have hsub : closedBall (0 : ℂ) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (half_lt_self hr)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (r / 2)).exists_bound_of_continuousOn
    (hf.continuousOn.mono hsub)
  refine ⟨(n.factorial : ℝ) * M / (r / 2 / 4) ^ n, ?_⟩
  filter_upwards [hlim.eventually (ball_mem_nhds (0 : ℂ) (half_pos hR))] with i hi
  have hb := norm_sub_complexTaylorSum_le_of_ball (f := f) (c := 0) (M := M) n hR
    (hf.mono (ball_subset_closedBall.trans hsub)) (fun w hw => hM w (ball_subset_closedBall hw)) hi
  simpa only [sub_zero] using hb

/-- Taylor coefficients at `0` recovered from measurable samples: one measurable function agrees
with the `n`-th coefficient at every parameter where the samples are eventually genuine and the
finite Taylor remainders are controlled. -/
theorem exists_measurable_eq_taylorCoefficient {F : α → ℂ → ℂ} {P : α → Prop}
    {samples : ℕ → α → ℂ} {h : ℕ → ℂ}
    (hne : ∀ i, h i ≠ 0) (hlim : Tendsto h atTop (𝓝 0))
    (hm : ∀ i, Measurable (samples i))
    (he : ∀ a, P a → ∀ᶠ i in atTop, samples i a = F a (h i))
    (hb : ∀ a, P a → ∀ n, ∃ K : ℝ, ∀ᶠ i in atTop,
      ‖F a (h i) - complexTaylorSum (F a) (n + 1) 0 (h i)‖ ≤ K * ‖h i‖ ^ (n + 1)) (n : ℕ) :
    ∃ c : α → ℂ, Measurable c ∧
      ∀ a, P a → c a = (n.factorial : ℂ)⁻¹ * iteratedDeriv n (F a) 0 := by
  classical
  have key : ∀ n : ℕ, ∃ c : ℕ → α → ℂ, ∀ j < n, Measurable (c j) ∧
      ∀ a, P a → c j a = (j.factorial : ℂ)⁻¹ * iteratedDeriv j (F a) 0 := by
    intro n
    induction n with
    | zero => exact ⟨fun _ _ => 0, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      have hsum (i : ℕ) : Measurable fun a => ∑ j ∈ range n, (h i) ^ j * c j a :=
        Finset.measurable_fun_sum _ fun j hj =>
          (hc j (mem_range.mp hj)).1.const_mul _
      obtain ⟨L, hL, hLe⟩ := exists_measurable_eq_limit
        (g := fun i a => ((h i) ^ n)⁻¹ * (samples i a - ∑ j ∈ range n, (h i) ^ j * c j a))
        fun i => ((hm i).sub (hsum i)).const_mul _
      refine ⟨Function.update c n L, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjn | rfl
      · rw [Function.update_of_ne hjn.ne]
        exact hc j hjn
      · rw [Function.update_self]
        refine ⟨hL, fun a ha => hLe a _ ?_⟩
        obtain ⟨K, hK⟩ := hb a ha j
        have ht := tendsto_taylorCoefficient_of_remainder hne hlim j hK
        refine ht.congr' ((he a ha).mono fun i hi => ?_)
        have hT : complexTaylorSum (F a) j 0 (h i) = ∑ m ∈ range j, (h i) ^ m * c m a := by
          unfold complexTaylorSum
          refine sum_congr rfl fun m hm' => ?_
          rw [(hc m (mem_range.mp hm')).2 a ha, sub_zero]
          ring
        simp only [hi, hT]
  obtain ⟨c, hc⟩ := key (n + 1)
  exact ⟨c n, (hc n n.lt_succ_self).1, (hc n n.lt_succ_self).2⟩

/-- The `n`-th Taylor coefficient at `0` of holomorphic germs is measurable in the parameter on
the parameters where the germ is holomorphic on a disc around `0` and the samples along
`(i + 1)⁻¹` are eventually genuine. -/
theorem exists_measurable_eq_taylorCoefficient_of_differentiableOn {F : α → ℂ → ℂ}
    {samples : ℕ → α → ℂ} (hm : ∀ i, Measurable (samples i)) (n : ℕ) :
    ∃ c : α → ℂ, Measurable c ∧ ∀ a (r : ℝ), 0 < r → DifferentiableOn ℂ (F a) (ball 0 r) →
      (∀ᶠ i in atTop, samples i a = F a ((i : ℂ) + 1)⁻¹) →
        c a = (n.factorial : ℂ)⁻¹ * iteratedDeriv n (F a) 0 := by
  obtain ⟨c, hc, he⟩ := exists_measurable_eq_taylorCoefficient
    (P := fun a => ∃ r : ℝ, 0 < r ∧ DifferentiableOn ℂ (F a) (ball 0 r) ∧
      ∀ᶠ i in atTop, samples i a = F a ((i : ℂ) + 1)⁻¹)
    complex_inv_succ_ne_zero tendsto_complex_inv_succ hm
    (fun a ⟨_, _, _, hs⟩ => hs)
    (fun a ⟨_, hr, hd, _⟩ k => exists_eventually_norm_sub_complexTaylorSum_le hr hd
      tendsto_complex_inv_succ (k + 1)) n
  exact ⟨c, hc, fun a r hr hd hs => he a ⟨r, hr, hd, hs⟩⟩

end PGM
