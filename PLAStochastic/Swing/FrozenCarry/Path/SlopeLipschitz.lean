import PLAStochastic.Swing.FrozenCarry.Path.SlopeLaw

/-! # The pathwise Lipschitz slope map

The frozen slope is antitone and 1-Lipschitz in the incoming margin on every
sublinear path.  The Gaussian statement uses one common full-measure set for
all margins, rather than an uncountable intersection of fixed-margin events.
This is the slope-map component of the limiting-kernel coupling argument.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SwingRepair

variable {Ω : Type*} {X : ℕ → Ω → ℝ} {ω : Ω}

lemma frozenSlopeMagnitude_le_add_abs {w v : ℝ}
    (hv : BddAbove (Set.range (fun n => -frozenUpperSlope X v n ω))) :
    frozenSlopeMagnitude X w ω ≤ frozenSlopeMagnitude X v ω + |w-v| := by
  apply csSup_le (Set.range_nonempty _)
  rintro z ⟨n, rfl⟩
  have hden : 0 < (n : ℝ)+1 := by positivity
  have hdiv : (v-w)/((n : ℝ)+1) ≤ |w-v| := by
    apply (div_le_iff₀ hden).2
    have hvw : v-w ≤ |w-v| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    have hmul : |w-v| ≤ |w-v| * ((n : ℝ)+1) := by
      nlinarith [abs_nonneg (w-v), (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
    exact hvw.trans hmul
  calc
    -frozenUpperSlope X w n ω =
        -frozenUpperSlope X v n ω + (v-w)/((n : ℝ)+1) := by
      unfold frozenUpperSlope
      ring
    _ ≤ frozenSlopeMagnitude X v ω + |w-v| :=
      add_le_add (neg_frozenUpperSlope_le_magnitude hv n) hdiv

lemma frozenSlopeMagnitude_abs_sub_le {w v : ℝ}
    (hw : BddAbove (Set.range (fun n => -frozenUpperSlope X w n ω)))
    (hv : BddAbove (Set.range (fun n => -frozenUpperSlope X v n ω))) :
    |frozenSlopeMagnitude X w ω - frozenSlopeMagnitude X v ω| ≤ |w-v| := by
  have h₁ := frozenSlopeMagnitude_le_add_abs (w := w) hv
  have h₂ := frozenSlopeMagnitude_le_add_abs (w := v) hw
  rw [abs_sub_comm v w] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma frozenUpperSlope_tendsto_zero_of_zero
    (h0 : Tendsto (fun n => frozenUpperSlope X 0 n ω) atTop (𝓝 0)) (w : ℝ) :
    Tendsto (fun n => frozenUpperSlope X w n ω) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using!
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hw : Tendsto (fun n : ℕ => w/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have h := h0.add hw
  convert h using 1
  · funext n
    simp only [frozenUpperSlope, zero_add]
    ring
  · simp

theorem frozenSlopeMagnitude_lipschitz_of_sublinear
    (h0 : Tendsto (fun n => frozenUpperSlope X 0 n ω) atTop (𝓝 0)) :
    LipschitzWith 1 (fun w => frozenSlopeMagnitude X w ω) := by
  apply LipschitzWith.of_dist_le_mul
  intro w v
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    frozenSlopeMagnitude_abs_sub_le
      (frozenSlopeMagnitude_bddAbove (frozenUpperSlope_tendsto_zero_of_zero h0 w))
      (frozenSlopeMagnitude_bddAbove (frozenUpperSlope_tendsto_zero_of_zero h0 v))

theorem frozenSlopeMagnitude_antitone_of_sublinear
    (h0 : Tendsto (fun n => frozenUpperSlope X 0 n ω) atTop (𝓝 0)) :
    Antitone (fun w => frozenSlopeMagnitude X w ω) := by
  intro w v hwv
  apply csSup_le (Set.range_nonempty _)
  rintro z ⟨n, rfl⟩
  have hupper : frozenUpperSlope X w n ω ≤ frozenUpperSlope X v n ω := by
    unfold frozenUpperSlope
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  exact (neg_le_neg hupper).trans
    (neg_frozenUpperSlope_le_magnitude
      (frozenSlopeMagnitude_bddAbove (frozenUpperSlope_tendsto_zero_of_zero h0 w)) n)

theorem frozenSlopeMagnitude_lipschitz_ae [MeasurableSpace Ω] {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, LipschitzWith 1 (fun w => frozenSlopeMagnitude X w ω) := by
  filter_upwards [frozenUpperSlope_tendsto_zero_ae hX hi hG 0] with ω hω
  exact frozenSlopeMagnitude_lipschitz_of_sublinear hω

theorem frozenSlopeMagnitude_antitone_ae [MeasurableSpace Ω] {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, Antitone (fun w => frozenSlopeMagnitude X w ω) := by
  filter_upwards [frozenUpperSlope_tendsto_zero_ae hX hi hG 0] with ω hω
  exact frozenSlopeMagnitude_antitone_of_sublinear hω

end SwingRepair
