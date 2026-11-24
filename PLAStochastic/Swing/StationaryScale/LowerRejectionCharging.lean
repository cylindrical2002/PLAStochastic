import PLAStochastic.Swing.FirstSegment.MarginCharging

/-! # Gaussian charging on the favorable stationary lower-rejection branch

For an accepted history with nonnegative old slope `m` and residual gap `g`,
rejection occurs when the next fresh increment is below `m-g`.  Its negative
margin exceeds `t` only below `-g-t`.  The two lemmas below prove the scalar
Gaussian comparison and transfer it to any past-measurable random state.
The rejected increment is never assigned a Gaussian law after selection.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Set
open scoped ENNReal
namespace SwingRepair
/-- Reflection of the standard Gaussian exchanges opposite open half-lines. -/
theorem gaussianReal_Iio_neg_eq_Ioi (a : ℝ) :
    gaussianReal 0 1 (Iio (-a)) = gaussianReal 0 1 (Ioi a) := by
  have hmap : Measure.map (fun x : ℝ => -x) (gaussianReal 0 1) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  have h := congrArg (fun ν : Measure ℝ => ν (Iio (-a))) hmap
  rw [Measure.map_apply measurable_neg measurableSet_Iio] at h
  have hp : (fun x : ℝ => -x) ⁻¹' Iio (-a) = Ioi a := by
    ext x
    simp
  rw [hp] at h
  exact h.symm
/-- The favorable lower branch has an `exp(-t²/2)` tail relative to its
rejection probability, uniformly over all nonnegative slopes and gaps. -/
theorem gaussian_favorable_lower_charge {g m t : ℝ}
    (hg : 0 ≤ g) (hm : 0 ≤ m) (ht : 0 ≤ t) :
    gaussianReal 0 1 (Iio (-g-t)) ≤
      ENNReal.ofReal (Real.exp (-t^2/2)) * gaussianReal 0 1 (Iio (m-g)) := by
  have hshift := gaussianReal_Ioi_shift_le hg ht
  have hsub : Iio (-g) ⊆ Iio (m-g) := by intro z hz; change z < m-g; exact lt_of_lt_of_le hz (by linarith)
  have hb := mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp (-t^2/2)))) (measure_mono (μ := gaussianReal 0 1) hsub)
  have heq : -g-t = -(g+t) := by ring
  rw [heq, gaussianReal_Iio_neg_eq_Ioi (g+t)]
  calc
    gaussianReal 0 1 (Ioi (g+t)) ≤ ENNReal.ofReal (Real.exp (-t^2/2)) * gaussianReal 0 1 (Ioi g) := hshift
    _ = ENNReal.ofReal (Real.exp (-t^2/2)) * gaussianReal 0 1 (Iio (-g)) := by rw [gaussianReal_Iio_neg_eq_Ioi]
    _ ≤ _ := hb

/-- Predictable-history version of the favorable lower-branch charge.  The
state is arbitrary and independent only of the new Gaussian increment; `g`
and `m` are measurable functions of that state. -/
theorem independent_gaussian_favorable_lower_charge {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hi : IndepFun X Z μ) (hlaw : μ.map Z = gaussianReal 0 1)
    {U : Set α} (hU : MeasurableSet U) {g m : α → ℝ}
    (hg : Measurable g) (hm : Measurable m)
    (hg0 : ∀ x ∈ U, 0 ≤ g x) (hm0 : ∀ x ∈ U, 0 ≤ m x)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | X ω ∈ U ∧ Z ω < -g (X ω)-t} ≤
      Real.exp (-t^2/2)*μ.real {ω | X ω ∈ U ∧ Z ω < m (X ω)-g (X ω)} := by
  let F (w : α × ℝ) : ℝ := if w.2 < -g w.1-t then 1 else 0
  let G (w : α × ℝ) : ℝ := if w.2 < m w.1-g w.1 then 1 else 0
  have hFm : Measurable F := measurable_const.ite
    (measurableSet_lt measurable_snd ((hg.comp measurable_fst).neg.sub_const t)) measurable_const
  have hGm : Measurable G := measurable_const.ite
    (measurableSet_lt measurable_snd ((hm.comp measurable_fst).sub (hg.comp measurable_fst))) measurable_const
  have hFb : ∀ w, |F w| ≤ 1 := by intro w; dsimp only [F]; split_ifs <;> norm_num
  have hGb : ∀ w, |G w| ≤ 1 := by intro w; dsimp only [G]; split_ifs <;> norm_num
  have hsection : ∀ x ∈ U, (∫ z, F (x,z) ∂μ.map Z) ≤
      Real.exp (-t^2/2)*(∫ z, G (x,z) ∂μ.map Z)+0 := by
    intro x hx
    rw [hlaw]
    have hFv : (∫ z, F (x,z) ∂gaussianReal 0 1) =
        (gaussianReal 0 1).real (Iio (-g x-t)) := by
      change (∫ z, if z ∈ Iio (-g x-t) then (1 : ℝ) else 0 ∂gaussianReal 0 1) = _
      exact integral_if_one_eq_measureReal measurableSet_Iio
    have hGv : (∫ z, G (x,z) ∂gaussianReal 0 1) =
        (gaussianReal 0 1).real (Iio (m x-g x)) := by
      change (∫ z, if z ∈ Iio (m x-g x) then (1 : ℝ) else 0 ∂gaussianReal 0 1) = _
      exact integral_if_one_eq_measureReal measurableSet_Iio
    rw [hFv, hGv, add_zero]
    have hbound := gaussian_favorable_lower_charge (hg0 x hx) (hm0 x hx) ht
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _)) hbound
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] at h
  have hc := IndepFun.integral_state_guard_le hX.aemeasurable hZ.aemeasurable hi hU hFm hGm
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hFb hGb hsection
  have hA : MeasurableSet {ω | X ω ∈ U ∧ Z ω < -g (X ω)-t} :=
    (hU.preimage hX).inter (measurableSet_lt hZ ((hg.comp hX).neg.sub_const t))
  have hB : MeasurableSet {ω | X ω ∈ U ∧ Z ω < m (X ω)-g (X ω)} :=
    (hU.preimage hX).inter (measurableSet_lt hZ ((hm.comp hX).sub (hg.comp hX)))
  have heF : (fun ω => if X ω ∈ U then F (X ω,Z ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ Z ω < -g (X ω)-t} then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [F, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have heG : (fun ω => if X ω ∈ U then G (X ω,Z ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ Z ω < m (X ω)-g (X ω)} then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [G, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have hFL := (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heF).trans
    (integral_if_one_eq_measureReal hA)
  have hGL := (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heG).trans
    (integral_if_one_eq_measureReal hB)
  rw [hFL, hGL, zero_mul, add_zero] at hc
  exact hc
/-- The reflected favorable upper branch, with a nonpositive old slope. -/
theorem independent_gaussian_favorable_upper_charge {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hi : IndepFun X Z μ) (hlaw : μ.map Z = gaussianReal 0 1)
    {U : Set α} (hU : MeasurableSet U) {g m : α → ℝ}
    (hg : Measurable g) (hm : Measurable m)
    (hg0 : ∀ x ∈ U, 0 ≤ g x) (hm0 : ∀ x ∈ U, m x ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | X ω ∈ U ∧ g (X ω)+t < Z ω} ≤
      Real.exp (-t^2/2)*μ.real {ω | X ω ∈ U ∧ m (X ω)+g (X ω) < Z ω} := by
  have hnegG : μ.map (fun ω => -Z ω) = gaussianReal 0 1 := by
    calc
      _ = (μ.map Z).map (fun z : ℝ => -z) :=
        (Measure.map_map measurable_neg hZ).symm
      _ = _ := by rw [hlaw, gaussianReal_map_neg, neg_zero]
  have hnegI : IndepFun X (fun ω => -Z ω) μ := by
    simpa only [Function.comp_def, id_eq] using hi.comp measurable_id measurable_neg
  have h := independent_gaussian_favorable_lower_charge hX hZ.neg hnegI hnegG hU hg hm.neg
    hg0 (fun x hx => neg_nonneg.mpr (hm0 x hx)) ht
  have hA : {ω | X ω ∈ U ∧ -Z ω < -g (X ω)-t} =
      {ω | X ω ∈ U ∧ g (X ω)+t < Z ω} := by
    ext ω
    constructor <;> rintro ⟨hU,hZ⟩ <;> exact ⟨hU, by linarith⟩
  have hB : {ω | X ω ∈ U ∧ -Z ω < (-m (X ω))-g (X ω)} =
      {ω | X ω ∈ U ∧ m (X ω)+g (X ω) < Z ω} := by
    ext ω
    constructor <;> rintro ⟨hU,hZ⟩ <;> exact ⟨hU, by linarith⟩
  change μ.real {ω | X ω ∈ U ∧ -Z ω < -g (X ω)-t} ≤
    Real.exp (-t^2/2)*μ.real {ω | X ω ∈ U ∧ -Z ω < (-m (X ω))-g (X ω)} at h
  rw [hA, hB] at h
  exact h
end SwingRepair
