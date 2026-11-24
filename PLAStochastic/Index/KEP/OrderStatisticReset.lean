import PLAStochastic.ForMathlib.Probability.OrderStatistics.Renyi
import PLAStochastic.Index.Algorithm.MeasurableEndpointHeight
import Mathlib.Probability.Process.Stopping

/-!
# The reset property of uniform order statistics

`orderLaw n = n! • volume.restrict (simplex n)` is the law of `n` sorted iid uniform `[0, 1]`
variables (`map_sortVec_uniform`).  Write `N = r + 1 + m`.

* **Deterministic time** (`map_pre_resc_orderLaw`, `indepFun_pre_resc`, `map_resc_orderLaw`).
  Under `orderLaw N`, the first `r + 1` coordinates `pre r v` and the rescaled future
  `resc r v i = (v (r + 1 + i) - v r) / (1 - v r)` are independent, and `resc r v` has law
  `orderLaw m`.  The law of `pre r v` has density `N! / m! · (1 - v r) ^ m` on
  `simplex (r + 1)` (`preLaw_eq`).
* **Stopping time** (`orderLaw_inter_futureKeys_stopping`,
  `orderLaw_inter_futureKeys_isStoppingTime`).  For a time `ρ < N` a.s. and an event `A` with
  `A ∩ {ρ = r} ∈ σ(v 0, …, v r)` for all `r`, the rescaled future keys after `ρ`, extended to a
  sequence by `0`, satisfy
  `P (A ∩ {futureKeys ρ v ∈ B}) = ∑ r < N, P (A ∩ {ρ = r}) · (orderLaw (N-1-r)).map extendKeys B`.

The proof of the deterministic case splits `Fin N → ℝ` as `(Fin (r+1) → ℝ) × (Fin m → ℝ)`
(`measurePreserving_appendMap`).  For `x ∈ simplex (r + 1)` the section of
`{pre ∈ C, resc ∈ D} ∩ simplex N` at `x` is the preimage of `D ∩ simplex m` under the affine map
`y ↦ (y - x r) / (1 - x r)`, of Lebesgue measure `(1 - x r) ^ m · vol (D ∩ simplex m)`.
-/

noncomputable section

namespace PGM.Renyi

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal Nat

/-! ### The law of the sorted uniform sample -/

/-- The law of the sorted vector of `n` iid uniform `[0, 1]` variables
(`map_sortVec_uniform`): density `n!` on the open simplex. -/
def orderLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (n ! : ℝ≥0∞) • volume.restrict (simplex n)

theorem orderLaw_apply (n : ℕ) (s : Set (Fin n → ℝ)) :
    orderLaw n s = n ! * volume (s ∩ simplex n) := by
  rw [orderLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' measurableSet_simplex]

theorem volume_cube (n : ℕ) : volume (cube n) = 1 := by
  rw [cube, volume_pi_pi]
  simp [Real.volume_Icc]

instance isProbabilityMeasure_orderLaw (n : ℕ) : IsProbabilityMeasure (orderLaw n) := by
  constructor
  have h := congrArg (fun μ : Measure (Fin n → ℝ) => μ univ) (map_sortVec_cube (n := n))
  rw [Measure.map_apply measurable_sortVec MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, volume_cube] at h
  rw [orderLaw, ← h]

/-- `orderLaw n` is the law of the sorted vector of `n` iid uniform `[0, 1]` variables. -/
theorem map_sortVec_uniform_eq_orderLaw {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : Fin n → Ω → ℝ}
    (hU : ∀ i, HasLaw (U i) (volume.restrict (Icc (0 : ℝ) 1)) P) (hind : iIndepFun U P) :
    P.map (fun ω => sortVec fun i => U i ω) = orderLaw n :=
  map_sortVec_uniform hU hind

/-- `n! · vol (simplex n) = 1`. -/
theorem factorial_mul_volume_simplex (n : ℕ) : (n ! : ℝ≥0∞) * volume (simplex n) = 1 := by
  have h := measure_univ (μ := orderLaw n)
  rwa [orderLaw_apply, univ_inter] at h

/-! ### Splitting off the first `r + 1` coordinates -/

variable {r m : ℕ}

/-- The first `r + 1` coordinates `(v 0, …, v r)`. -/
def pre (r : ℕ) {m : ℕ} (v : Fin (r + 1 + m) → ℝ) : Fin (r + 1) → ℝ :=
  fun i => v (Fin.castAdd m i)

/-- The pivot coordinate `v r`. -/
abbrev pivot (r : ℕ) {m : ℕ} (v : Fin (r + 1 + m) → ℝ) : ℝ :=
  v (Fin.castAdd m (Fin.last r))

/-- Affine rescaling of `(c, 1)` onto `(0, 1)`: `y ↦ (y - c) / (1 - c)`. -/
def rescVec {m : ℕ} (c : ℝ) (y : Fin m → ℝ) : Fin m → ℝ :=
  fun i => (y i - c) / (1 - c)

/-- The rescaled future `resc r v i = (v (r + 1 + i) - v r) / (1 - v r)`. -/
def resc (r : ℕ) {m : ℕ} (v : Fin (r + 1 + m) → ℝ) : Fin m → ℝ :=
  fun i => (v (Fin.natAdd (r + 1) i) - pivot r v) / (1 - pivot r v)

theorem pre_apply (v : Fin (r + 1 + m) → ℝ) (i : Fin (r + 1)) :
    pre r v i = v (Fin.castAdd m i) := rfl

theorem resc_apply (v : Fin (r + 1 + m) → ℝ) (i : Fin m) :
    resc r v i = (v (Fin.natAdd (r + 1) i) - pivot r v) / (1 - pivot r v) := rfl

theorem measurable_pre : Measurable (pre r (m := m)) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem measurable_resc : Measurable (resc r (m := m)) :=
  measurable_pi_lambda _ fun i => by
    simp only [resc_apply]
    fun_prop

theorem measurable_pre_resc : Measurable fun v : Fin (r + 1 + m) → ℝ => (pre r v, resc r v) :=
  measurable_pre.prodMk measurable_resc

/-- Concatenation `(x, y) ↦ Fin.append x y`. -/
def appendMap (a b : ℕ) (p : (Fin a → ℝ) × (Fin b → ℝ)) : Fin (a + b) → ℝ :=
  Fin.append p.1 p.2

theorem measurable_appendMap (a b : ℕ) : Measurable (appendMap a b) := by
  refine measurable_pi_lambda _ fun j => ?_
  induction j using Fin.addCases with
  | left i =>
    simp only [appendMap, Fin.append_left]
    exact (measurable_pi_apply i).comp measurable_fst
  | right i =>
    simp only [appendMap, Fin.append_right]
    exact (measurable_pi_apply i).comp measurable_snd

theorem measurePreserving_appendMap (a b : ℕ) :
    MeasurePreserving (appendMap a b) (volume.prod volume) volume := by
  refine ⟨measurable_appendMap a b, ?_⟩
  refine Eq.symm ((volume_pi (α := fun _ : Fin (a + b) => ℝ)).trans (Measure.pi_eq fun s hs => ?_))
  have hpre : appendMap a b ⁻¹' univ.pi s =
      (univ.pi fun i => s (Fin.castAdd b i)) ×ˢ (univ.pi fun i => s (Fin.natAdd a i)) := by
    ext p
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, mem_prod, appendMap]
    constructor
    · intro h
      exact ⟨fun i => by simpa using h (Fin.castAdd b i),
        fun i => by simpa using h (Fin.natAdd a i)⟩
    · rintro ⟨h1, h2⟩ j
      induction j using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
  rw [Measure.map_apply (measurable_appendMap a b) (MeasurableSet.univ_pi hs), hpre,
    Measure.prod_prod, volume_pi_pi, volume_pi_pi, Fin.prod_univ_add]

theorem pre_append (x : Fin (r + 1) → ℝ) (y : Fin m → ℝ) : pre r (Fin.append x y) = x := by
  funext i
  simp [pre]

theorem pivot_append (x : Fin (r + 1) → ℝ) (y : Fin m → ℝ) :
    pivot r (Fin.append x y) = x (Fin.last r) := by
  simp [pivot]

theorem resc_append (x : Fin (r + 1) → ℝ) (y : Fin m → ℝ) :
    resc r (Fin.append x y) = rescVec (x (Fin.last r)) y := by
  funext i
  simp [resc, rescVec, pivot]

/-! ### The simplex in split coordinates -/

theorem rescVec_mem_simplex_iff {c : ℝ} (hc : c < 1) {y : Fin m → ℝ} :
    rescVec c y ∈ simplex m ↔ StrictMono y ∧ (∀ i, c < y i) ∧ ∀ i, y i < 1 := by
  have h1c : 0 < 1 - c := sub_pos.2 hc
  simp only [simplex, mem_ofPred_eq, rescVec, StrictMono]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact forall_congr' fun a => forall_congr' fun b => imp_congr_right fun _ => by
      rw [div_lt_div_iff_of_pos_right h1c, sub_lt_sub_iff_right]
  · exact forall_congr' fun i => by rw [div_pos_iff_of_pos_right h1c, sub_pos]
  · exact forall_congr' fun i => by rw [div_lt_one h1c, sub_lt_sub_iff_right]

theorem append_mem_simplex_iff {x : Fin (r + 1) → ℝ} {y : Fin m → ℝ} :
    Fin.append x y ∈ simplex (r + 1 + m) ↔
      x ∈ simplex (r + 1) ∧ rescVec (x (Fin.last r)) y ∈ simplex m := by
  constructor
  · rintro ⟨hmono, hpos, hlt⟩
    have hx : x ∈ simplex (r + 1) := by
      refine ⟨fun a b hab => ?_, fun i => ?_, fun i => ?_⟩
      · simpa using hmono ((Fin.strictMono_castAdd m) hab)
      · simpa using hpos (Fin.castAdd m i)
      · simpa using hlt (Fin.castAdd m i)
    refine ⟨hx, (rescVec_mem_simplex_iff (hx.2.2 _)).2
      ⟨fun a b hab => ?_, fun i => ?_, fun i => ?_⟩⟩
    · simpa using hmono ((Fin.strictMono_natAdd (r + 1)) hab)
    · have := hmono (show Fin.castAdd m (Fin.last r) < Fin.natAdd (r + 1) i by
        rw [Fin.lt_def]
        simp only [Fin.val_castAdd, Fin.val_last, Fin.val_natAdd]
        omega)
      simpa using this
    · simpa using hlt (Fin.natAdd (r + 1) i)
  · rintro ⟨hx, hy⟩
    obtain ⟨hymono, hcy, hy1⟩ := (rescVec_mem_simplex_iff (hx.2.2 _)).1 hy
    have hxle : ∀ i, x i ≤ x (Fin.last r) := fun i => hx.1.monotone (Fin.le_last i)
    refine ⟨fun a b hab => ?_, fun a => ?_, fun a => ?_⟩
    · induction a using Fin.addCases with
      | left i =>
        induction b using Fin.addCases with
        | left j =>
          simp only [Fin.append_left]
          exact hx.1 ((Fin.strictMono_castAdd m).lt_iff_lt.1 hab)
        | right j =>
          simp only [Fin.append_left, Fin.append_right]
          exact lt_of_le_of_lt (hxle i) (hcy j)
      | right i =>
        induction b using Fin.addCases with
        | left j =>
          exfalso
          rw [Fin.lt_def] at hab
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hab
          omega
        | right j =>
          simp only [Fin.append_right]
          exact hymono ((Fin.strictMono_natAdd (r + 1)).lt_iff_lt.1 hab)
    · induction a using Fin.addCases with
      | left i => simpa using hx.2.1 i
      | right i => simpa using lt_trans (hx.2.1 _) (hcy i)
    · induction a using Fin.addCases with
      | left i => simpa using hx.2.2 i
      | right i => simpa using hy1 i

theorem append_mem_rect_iff {C : Set (Fin (r + 1) → ℝ)} {D : Set (Fin m → ℝ)}
    {x : Fin (r + 1) → ℝ} {y : Fin m → ℝ} :
    Fin.append x y ∈ pre r ⁻¹' C ∩ resc r ⁻¹' D ∩ simplex (r + 1 + m) ↔
      x ∈ C ∩ simplex (r + 1) ∧ rescVec (x (Fin.last r)) y ∈ D ∩ simplex m := by
  simp only [mem_inter_iff, mem_preimage, pre_append, resc_append, append_mem_simplex_iff]
  tauto

/-- Lebesgue measure of the preimage of `E` under `y ↦ (y - c) / (1 - c)`. -/
theorem volume_preimage_rescVec {c : ℝ} (hc : c < 1) (E : Set (Fin m → ℝ)) :
    volume (rescVec c ⁻¹' E) = ENNReal.ofReal ((1 - c) ^ m) * volume E := by
  have h1c : 0 < 1 - c := sub_pos.2 hc
  have hfun : ∀ y : Fin m → ℝ, rescVec c y = (1 - c)⁻¹ • (y + fun _ => -c) := by
    intro y
    funext i
    simp [rescVec, div_eq_inv_mul, sub_eq_add_neg]
  have hpre : rescVec c ⁻¹' E =
      (fun y : Fin m → ℝ => y + fun _ => -c) ⁻¹' ((fun z => (1 - c)⁻¹ • z) ⁻¹' E) := by
    ext y
    simp only [mem_preimage, hfun]
  rw [hpre, measure_preimage_add_right, Measure.addHaar_preimage_smul _ (inv_ne_zero h1c.ne'),
    Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (pow_pos h1c m)]

theorem measurable_pivotDensity :
    Measurable fun x : Fin (r + 1) → ℝ => ENNReal.ofReal ((1 - x (Fin.last r)) ^ m) := by
  fun_prop

/-- **Change of variables.**  The Lebesgue measure of `{pre ∈ C, resc ∈ D}` inside the
simplex factorizes. -/
theorem volume_pre_resc {C : Set (Fin (r + 1) → ℝ)} {D : Set (Fin m → ℝ)}
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    volume (pre r ⁻¹' C ∩ resc r ⁻¹' D ∩ simplex (r + 1 + m)) =
      (∫⁻ x in C ∩ simplex (r + 1), ENNReal.ofReal ((1 - x (Fin.last r)) ^ m)) *
        volume (D ∩ simplex m) := by
  set S := pre r ⁻¹' C ∩ resc r ⁻¹' D ∩ simplex (r + 1 + m) with hSdef
  have hS : MeasurableSet S :=
    ((measurable_pre hC).inter (measurable_resc hD)).inter measurableSet_simplex
  rw [← (measurePreserving_appendMap (r + 1) m).measure_preimage hS.nullMeasurableSet,
    Measure.prod_apply (measurable_appendMap _ _ hS)]
  have hsec : ∀ x : Fin (r + 1) → ℝ, volume (Prod.mk x ⁻¹' (appendMap (r + 1) m ⁻¹' S)) =
      (C ∩ simplex (r + 1)).indicator
        (fun x => ENNReal.ofReal ((1 - x (Fin.last r)) ^ m)) x * volume (D ∩ simplex m) := by
    intro x
    by_cases hx : x ∈ C ∩ simplex (r + 1)
    · have hset : Prod.mk x ⁻¹' (appendMap (r + 1) m ⁻¹' S) =
          rescVec (x (Fin.last r)) ⁻¹' (D ∩ simplex m) := by
        ext y
        simp only [mem_preimage, appendMap, hSdef, append_mem_rect_iff, hx, true_and]
      rw [hset, volume_preimage_rescVec (hx.2.2.2 _), indicator_of_mem hx]
    · have hset : Prod.mk x ⁻¹' (appendMap (r + 1) m ⁻¹' S) = ∅ := by
        ext y
        simp only [mem_preimage, appendMap, hSdef, append_mem_rect_iff, hx, false_and,
          mem_empty_iff_false]
      rw [hset, measure_empty, indicator_of_notMem hx, zero_mul]
  simp_rw [hsec]
  rw [lintegral_mul_const _ (measurable_pivotDensity.indicator
      (hC.inter measurableSet_simplex)),
    lintegral_indicator (hC.inter measurableSet_simplex)]

/-! ### Deterministic time: independence and the law of the rescaled future -/

theorem orderLaw_pre_resc_eq {C : Set (Fin (r + 1) → ℝ)} {D : Set (Fin m → ℝ)}
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    orderLaw (r + 1 + m) (pre r ⁻¹' C ∩ resc r ⁻¹' D) =
      (r + 1 + m)! * (∫⁻ x in C ∩ simplex (r + 1), ENNReal.ofReal ((1 - x (Fin.last r)) ^ m)) *
        volume (D ∩ simplex m) := by
  rw [orderLaw_apply, volume_pre_resc hC hD, mul_assoc]

/-- The law of the first `r + 1` of `r + 1 + m` uniform order statistics. -/
def preLaw (r m : ℕ) : Measure (Fin (r + 1) → ℝ) :=
  (orderLaw (r + 1 + m)).map (pre r)

instance isProbabilityMeasure_preLaw : IsProbabilityMeasure (preLaw r m) :=
  Measure.isProbabilityMeasure_map measurable_pre.aemeasurable

theorem preLaw_apply {C : Set (Fin (r + 1) → ℝ)} (hC : MeasurableSet C) :
    preLaw r m C = orderLaw (r + 1 + m) (pre r ⁻¹' C) :=
  Measure.map_apply measurable_pre hC

theorem preLaw_apply_eq {C : Set (Fin (r + 1) → ℝ)} (hC : MeasurableSet C) :
    preLaw r m C =
      (r + 1 + m)! * (∫⁻ x in C ∩ simplex (r + 1), ENNReal.ofReal ((1 - x (Fin.last r)) ^ m)) *
        volume (simplex m) := by
  have h : pre r ⁻¹' C = pre r ⁻¹' C ∩ resc r (m := m) ⁻¹' univ := by
    rw [preimage_univ, inter_univ]
  rw [preLaw_apply hC, h, orderLaw_pre_resc_eq hC MeasurableSet.univ, univ_inter]

/-- **Reset property at a deterministic time.**  Under the law of `r + 1 + m` sorted uniforms,
the first `r + 1` order statistics and the rescaled future `(v (r+1+i) - v r) / (1 - v r)` are
independent, and the rescaled future has the law of `m` sorted uniforms. -/
theorem map_pre_resc_orderLaw :
    (orderLaw (r + 1 + m)).map (fun v => (pre r v, resc r v)) =
      (preLaw r m).prod (orderLaw m) := by
  symm
  refine Measure.prod_eq fun C D hC hD => ?_
  rw [Measure.map_apply measurable_pre_resc (hC.prod hD), mk_preimage_prod,
    orderLaw_pre_resc_eq hC hD, preLaw_apply_eq hC, orderLaw_apply,
    mul_assoc (_ * _) (volume (simplex m)), ← mul_assoc (volume (simplex m)),
    mul_comm (volume (simplex m)) (m ! : ℝ≥0∞), factorial_mul_volume_simplex, one_mul]

theorem map_resc_orderLaw : (orderLaw (r + 1 + m)).map (resc r) = orderLaw m := by
  have h := congrArg (fun μ : Measure ((Fin (r + 1) → ℝ) × (Fin m → ℝ)) => μ.map Prod.snd)
    (map_pre_resc_orderLaw (r := r) (m := m))
  simp only [Measure.map_map measurable_snd measurable_pre_resc, Measure.map_snd_prod,
    measure_univ, one_smul] at h
  exact h

theorem indepFun_pre_resc : IndepFun (pre r) (resc r) (orderLaw (r + 1 + m)) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_pre.aemeasurable
    measurable_resc.aemeasurable, map_pre_resc_orderLaw, map_resc_orderLaw]
  rfl

theorem orderLaw_pre_inter_resc {C : Set (Fin (r + 1) → ℝ)} {D : Set (Fin m → ℝ)}
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    orderLaw (r + 1 + m) (pre r ⁻¹' C ∩ resc r ⁻¹' D) =
      orderLaw (r + 1 + m) (pre r ⁻¹' C) * orderLaw m D := by
  rw [← mk_preimage_prod, ← Measure.map_apply measurable_pre_resc (hC.prod hD),
    map_pre_resc_orderLaw, Measure.prod_prod, preLaw_apply hC]

theorem volume_simplex (n : ℕ) : volume (simplex n) = (n ! : ℝ≥0∞)⁻¹ :=
  ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm, factorial_mul_volume_simplex])

/-- The law of the first `r + 1` of `r + 1 + m` sorted uniforms has density
`(r + 1 + m)! / m! · (1 - v r) ^ m` on the simplex. -/
theorem preLaw_eq : preLaw r m =
    (((r + 1 + m)! : ℝ≥0∞) / m !) • (volume.restrict (simplex (r + 1))).withDensity
      fun x => ENNReal.ofReal ((1 - x (Fin.last r)) ^ m) := by
  ext C hC
  rw [preLaw_apply_eq hC, Measure.smul_apply, withDensity_apply _ hC,
    Measure.restrict_restrict hC, volume_simplex, smul_eq_mul, div_eq_mul_inv, mul_right_comm]

/-! ### Scalar facts on the simplex -/

section Scalar

variable {v : Fin (r + 1 + m) → ℝ}

theorem pivot_pos (hv : v ∈ simplex (r + 1 + m)) : 0 < pivot r v := hv.2.1 _

theorem pivot_lt_one (hv : v ∈ simplex (r + 1 + m)) : pivot r v < 1 := hv.2.2 _

theorem pivot_lt_future (hv : v ∈ simplex (r + 1 + m)) (i : Fin m) :
    pivot r v < v (Fin.natAdd (r + 1) i) :=
  hv.1 (by
    rw [Fin.lt_def]
    simp only [Fin.val_castAdd, Fin.val_last, Fin.val_natAdd]
    omega)

theorem append_pre_future (v : Fin (r + 1 + m) → ℝ) :
    Fin.append (pre r v) (fun i => v (Fin.natAdd (r + 1) i)) = v :=
  Fin.append_castAdd_natAdd

theorem pre_mem_simplex (hv : v ∈ simplex (r + 1 + m)) : pre r v ∈ simplex (r + 1) := by
  rw [← append_pre_future v] at hv
  exact (append_mem_simplex_iff.1 hv).1

theorem resc_mem_simplex (hv : v ∈ simplex (r + 1 + m)) : resc r v ∈ simplex m := by
  rw [← append_pre_future v] at hv
  exact (append_mem_simplex_iff.1 hv).2

/-- The inverse relation `v (r + 1 + i) = v r + (1 - v r) · resc r v i`. -/
theorem future_eq_pivot_add (hv : pivot r v ≠ 1) (i : Fin m) :
    v (Fin.natAdd (r + 1) i) = pivot r v + (1 - pivot r v) * resc r v i := by
  have h : 1 - pivot r v ≠ 0 := sub_ne_zero.2 (Ne.symm hv)
  rw [resc_apply, mul_div_cancel₀ _ h]
  ring

theorem future_eq_pivot_add_of_mem (hv : v ∈ simplex (r + 1 + m)) (i : Fin m) :
    v (Fin.natAdd (r + 1) i) = pivot r v + (1 - pivot r v) * resc r v i :=
  future_eq_pivot_add (pivot_lt_one hv).ne i

end Scalar

/-! ### The coordinate filtration and the future keys -/

/-- The σ-algebra `σ(v 0, …, v r)` on `Fin N → ℝ` (all of `v` once `N ≤ r + 1`). -/
@[instance_reducible]
def coordSigma (N r : ℕ) : MeasurableSpace (Fin N → ℝ) :=
  ⨆ (i : Fin N) (_ : (i : ℕ) ≤ r), MeasurableSpace.comap (fun v => v i) inferInstance

theorem coordSigma_le (N r : ℕ) : coordSigma N r ≤ MeasurableSpace.pi :=
  iSup₂_le fun i _ => (measurable_pi_apply i).comap_le

theorem coordSigma_mono (N : ℕ) : Monotone (coordSigma N) := fun _ _ hrs =>
  iSup₂_mono' fun i hi => ⟨i, hi.trans hrs, le_rfl⟩

theorem coordSigma_le_comap_pre (r m : ℕ) :
    coordSigma (r + 1 + m) r ≤ MeasurableSpace.comap (pre r) MeasurableSpace.pi := by
  refine iSup₂_le fun i hi => ?_
  have hfun : (fun v : Fin (r + 1 + m) → ℝ => v i) =
      (fun x : Fin (r + 1) → ℝ => x ⟨i, by omega⟩) ∘ pre r := by
    funext v
    simp only [comp_apply, pre_apply]
    congr 1
  rw [hfun, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

theorem exists_preimage_pre_of_measurableSet_coordSigma {E : Set (Fin (r + 1 + m) → ℝ)}
    (hE : MeasurableSet[coordSigma (r + 1 + m) r] E) :
    ∃ C, MeasurableSet C ∧ pre r ⁻¹' C = E :=
  MeasurableSpace.measurableSet_comap.1 (coordSigma_le_comap_pre r m E hE)

/-- The rescaled keys after position `r`, as a sequence:
`futureKeys r v i = (v (r + 1 + i) - v r) / (1 - v r)` for `r + 1 + i < N`, and `0` beyond. -/
def futureKeys {N : ℕ} (r : ℕ) (v : Fin N → ℝ) : ℕ → ℝ := fun i =>
  if h : r + 1 + i < N then
    (v ⟨r + 1 + i, h⟩ - v ⟨r, by omega⟩) / (1 - v ⟨r, by omega⟩)
  else 0

theorem futureKeys_eq_extendKeys (v : Fin (r + 1 + m) → ℝ) :
    futureKeys r v = extendKeys (resc r v) := by
  funext i
  by_cases h : i < m
  · have h' : r + 1 + i < r + 1 + m := by omega
    rw [futureKeys, dif_pos h', extendKeys_of_lt _ h, resc_apply]
    rfl
  · have h' : ¬ r + 1 + i < r + 1 + m := by omega
    rw [futureKeys, dif_neg h', extendKeys, dif_neg h]

theorem measurable_futureKeys (N r : ℕ) : Measurable (futureKeys (N := N) r) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : r + 1 + i < N
  · simp only [futureKeys, h, dif_pos]
    fun_prop
  · simp only [futureKeys, h, dif_neg, not_false_eq_true]
    exact measurable_const

theorem lt_of_mem_simplex_of_lt {N : ℕ} {v : Fin N → ℝ} (hv : v ∈ simplex N) {i j : ℕ}
    (hi : i < N) (hj : j < N) (hij : i < j) : v ⟨i, hi⟩ < v ⟨j, hj⟩ :=
  hv.1 (Fin.mk_lt_mk.2 hij)

/-- On the simplex, `v (r + 1 + i) = v r + (1 - v r) · futureKeys r v i`. -/
theorem futureKeys_spec {N r i : ℕ} {v : Fin N → ℝ} (hv : v ∈ simplex N)
    (h : r + 1 + i < N) :
    v ⟨r + 1 + i, h⟩ = v ⟨r, by omega⟩ + (1 - v ⟨r, by omega⟩) * futureKeys r v i := by
  have h1 : 1 - v ⟨r, by omega⟩ ≠ 0 := sub_ne_zero.2 (hv.2.2 _).ne'
  rw [futureKeys, dif_pos h, mul_div_cancel₀ _ h1]
  ring

/-- **Reset at a deterministic time, sequence form.**  For `E ∈ σ(v 0, …, v r)`, the rescaled
future keys are independent of `E` and distributed as `N - 1 - r` sorted uniforms. -/
theorem orderLaw_inter_futureKeys {N r : ℕ} (hr : r < N) {E : Set (Fin N → ℝ)}
    (hE : MeasurableSet[coordSigma N r] E) {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    orderLaw N (E ∩ {v | futureKeys r v ∈ B}) =
      orderLaw N E * (orderLaw (N - 1 - r)).map extendKeys B := by
  obtain ⟨m, rfl⟩ : ∃ m, N = r + 1 + m := ⟨N - 1 - r, by omega⟩
  have hm : r + 1 + m - 1 - r = m := by omega
  rw [hm]
  obtain ⟨C, hC, rfl⟩ := exists_preimage_pre_of_measurableSet_coordSigma hE
  have hset : {v : Fin (r + 1 + m) → ℝ | futureKeys r v ∈ B} = resc r ⁻¹' (extendKeys ⁻¹' B) := by
    ext v
    simp only [mem_ofPred_eq, mem_preimage, futureKeys_eq_extendKeys]
  rw [hset, orderLaw_pre_inter_resc hC (measurable_extendKeys hB),
    Measure.map_apply measurable_extendKeys hB]

/-- **Reset at a stopping time.**  Let `ρ` be a time with `ρ < N` almost surely and `A` an
event of the stopped σ-algebra: `A ∩ {ρ = r} ∈ σ(v 0, …, v r)` for every `r`.  Then the
rescaled future keys after `ρ` are, given `A ∩ {ρ = r}`, distributed as `N - 1 - r` sorted
uniforms. -/
theorem orderLaw_inter_futureKeys_stopping {N : ℕ} {ρ : (Fin N → ℝ) → ℕ}
    (hρN : ∀ᵐ v ∂orderLaw N, ρ v < N) {A : Set (Fin N → ℝ)}
    (hA : ∀ r, MeasurableSet[coordSigma N r] (A ∩ {v | ρ v = r}))
    {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    orderLaw N (A ∩ {v | futureKeys (ρ v) v ∈ B}) =
      ∑ r ∈ Finset.range N,
        orderLaw N (A ∩ {v | ρ v = r}) * (orderLaw (N - 1 - r)).map extendKeys B := by
  have hae : (A ∩ {v | futureKeys (ρ v) v ∈ B} : Set (Fin N → ℝ)) =ᵐ[orderLaw N]
      ⋃ r ∈ Finset.range N, (A ∩ {v | ρ v = r}) ∩ {v | futureKeys r v ∈ B} := by
    refine Filter.eventuallyEq_set.2 (hρN.mono fun v hv => ?_)
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨hvA, hvB⟩
      exact ⟨ρ v, hv, ⟨hvA, rfl⟩, hvB⟩
    · rintro ⟨r, -, ⟨hvA, rfl⟩, hvB⟩
      exact ⟨hvA, hvB⟩
  rw [measure_congr hae, measure_biUnion_finset]
  · exact Finset.sum_congr rfl fun r hr =>
      orderLaw_inter_futureKeys (Finset.mem_range.1 hr) (hA r) hB
  · intro r _ s _ hrs
    exact disjoint_left.2 fun v h1 h2 => hrs (h1.1.2.symm.trans h2.1.2)
  · intro r _
    exact (coordSigma_le N r _ (hA r)).inter (measurable_futureKeys N r hB)

/-- The coordinate filtration `r ↦ σ(v 0, …, v r)` on `Fin N → ℝ`. -/
def coordFiltration (N : ℕ) : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (Fin N → ℝ)) where
  seq := coordSigma N
  mono' := coordSigma_mono N
  le' := coordSigma_le N

/-- **Reset at a stopping time**, with Mathlib's stopping-time σ-algebra. -/
theorem orderLaw_inter_futureKeys_isStoppingTime {N : ℕ} {ρ : (Fin N → ℝ) → ℕ}
    (hρ : IsStoppingTime (coordFiltration N) fun v => (ρ v : WithTop ℕ))
    (hρN : ∀ᵐ v ∂orderLaw N, ρ v < N) {A : Set (Fin N → ℝ)}
    (hA : MeasurableSet[hρ.measurableSpace] A) {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    orderLaw N (A ∩ {v | futureKeys (ρ v) v ∈ B}) =
      ∑ r ∈ Finset.range N,
        orderLaw N (A ∩ {v | ρ v = r}) * (orderLaw (N - 1 - r)).map extendKeys B := by
  refine orderLaw_inter_futureKeys_stopping hρN (fun r => ?_) hB
  have h1 := hA.2 r
  have h2 := hρ.measurableSet_eq r
  have heq : A ∩ {v | ρ v = r} = (A ∩ {v | (ρ v : WithTop ℕ) ≤ (r : ℕ)}) ∩
      {v | (ρ v : WithTop ℕ) = (r : ℕ)} := by
    ext v
    simp only [mem_inter_iff, mem_ofPred_eq, Nat.cast_le, Nat.cast_inj]
    constructor
    · rintro ⟨hv, h⟩
      exact ⟨⟨hv, h.le⟩, h⟩
    · rintro ⟨⟨hv, -⟩, h⟩
      exact ⟨hv, h⟩
  rw [heq]
  exact h1.inter h2

end PGM.Renyi
