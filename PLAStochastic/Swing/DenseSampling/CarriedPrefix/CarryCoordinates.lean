import PLAStochastic.Swing.DenseSampling.CarriedPrefix.TruncatedLogMean

/-! # Exact carry coordinates at the rejection observation -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem nativePolarity_mul_self (x : ℝ) : nativePolarity x * nativePolarity x = 1 := by
  rcases nativePolarity_values x with h | h <;> rw [h] <;> norm_num

theorem nativePolarity_mul_eq_abs (x : ℝ) : nativePolarity x*x = |x| := by
  unfold nativePolarity
  split_ifs with hx
  · simp only [one_mul, abs_of_nonneg hx]
  · simp only [neg_one_mul, abs_of_nonpos (le_of_not_ge hx)]

/-- The inherited anchor error and the observed carry determine the state.
The carry remains part of the observed past. -/
def nativeCarriedState (y : ℕ → ℝ) (ε q : ℝ) (b : ℕ) : ℝ :=
  ε - |q-y b| + nativePolarity (q-y b)*(y (b+1)-y b)

def nativeCarriedFuture (y : ℕ → ℝ) (q : ℝ) (b : ℕ) (j : ℕ) : ℝ :=
  nativePolarity (q-y b)*(y ((b+1)+j)-y (b+1))

theorem nativeCarriedState_coordinate (y : ℕ → ℝ) (ε q m h : ℝ) (b j : ℕ) :
    nativeCarriedState y ε q b + nativeCarriedFuture y q b j -
      (nativePolarity (q-y b)*m)*(((j : ℝ)+1)*h) =
        ε + nativePolarity (q-y b)*(y ((b+1)+j)-(q+m*((((b+1)+j : ℕ) : ℝ)*h-(b : ℝ)*h))) := by
  unfold nativeCarriedState nativeCarriedFuture
  rw [← nativePolarity_mul_eq_abs (q-y b)]
  push_cast
  ring

/-- Reflection by the inherited sign preserves the original absolute-error
constraint exactly, including the carried first observation. -/
theorem nativeCarriedState_constraint_iff (y : ℕ → ℝ) (ε q m h : ℝ) (b j : ℕ) :
    nativeCarriedState y ε q b + nativeCarriedFuture y q b j -
      (nativePolarity (q-y b)*m)*(((j : ℝ)+1)*h) ∈ Icc 0 (2*ε) ↔
        |y ((b+1)+j)-(q+m*((((b+1)+j : ℕ) : ℝ)*h-(b : ℝ)*h))| ≤ ε := by
  rw [nativeCarriedState_coordinate]
  rcases nativePolarity_values (q-y b) with hs | hs <;> rw [hs]
  · simp only [one_mul, mem_Icc, abs_le]
    constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith
  · simp only [neg_one_mul, mem_Icc, abs_le]
    constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith

/-- The reflected state and fresh-grid problem is the actual continuation cone
of the original algorithm at its inherited fitted anchor. -/
theorem nativeCarriedFit_state_iff_nativePrefix (y : ℕ → ℝ) (ε q h : ℝ) (b N : ℕ) :
    nativeCarriedFit (nativeCarriedFuture y q b) (nativeCarriedState y ε q b) ε h N ↔
      nativePrefixFeasible (fun j => (j : ℝ)*h) y ε b ((b+1)+N) q := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨nativePolarity (q-y b)*m, ?_⟩
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Finset.mem_Icc.mp hk).1
    have hj : j ≤ N := by have := (Finset.mem_Icc.mp hk).2; omega
    have hf := hm j hj
    have heq : nativePolarity (q-y b)*(nativePolarity (q-y b)*m) = m := by
      rw [← mul_assoc, nativePolarity_mul_self, one_mul]
    have hh := (nativeCarriedState_constraint_iff y ε q (nativePolarity (q-y b)*m) h b j).mp
      (by simpa only [heq] using hf)
    exact hh
  · rintro ⟨m, hm⟩
    refine ⟨nativePolarity (q-y b)*m, fun j hj => ?_⟩
    exact (nativeCarriedState_constraint_iff y ε q m h b j).mpr
      (hm ((b+1)+j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))

theorem measurable_nativePolarity : Measurable nativePolarity :=
  measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const

theorem measurable_nativeCarriedState {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℕ → Ω → ℝ) {Q : Ω → ℝ} (hQ : Measurable Q) (hY : ∀ j, Measurable (Y j))
    (ε : ℝ) (b : ℕ) : Measurable (fun ω => nativeCarriedState (fun j => Y j ω) ε (Q ω) b) := by
  exact (measurable_const.sub (hQ.sub (hY b)).abs).add
    ((measurable_nativePolarity.comp (hQ.sub (hY b))).mul ((hY (b+1)).sub (hY b)))

theorem measurable_nativeCarriedFuture {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℕ → Ω → ℝ) {Q : Ω → ℝ} (hQ : Measurable Q) (hY : ∀ j, Measurable (Y j))
    (b j : ℕ) : Measurable (fun ω => nativeCarriedFuture (fun j => Y j ω) (Q ω) b j) := by
  exact (measurable_nativePolarity.comp (hQ.sub (hY b))).mul ((hY ((b+1)+j)).sub (hY (b+1)))

/-- A fixed inherited polarity preserves the Brownian law. Random polarities
are subsequently integrated as part of the observed state. -/
theorem isBrownianReal_nativePolarity_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) (x : ℝ) :
    IsBrownianReal (fun t ω => nativePolarity x*B t ω) μ := by
  rcases nativePolarity_values x with hx | hx
  · simpa only [hx, one_mul] using hB
  · have heq : (fun t ω => nativePolarity x*B t ω) = -B := by
      funext t ω
      simp only [hx, neg_one_mul, Pi.neg_apply]
    rw [heq]
    exact hB.neg

/-- Full sampled Brownian laws agree, so constants proved for one Brownian
process transfer uniformly to every time shift and inherited fixed sign. -/
theorem identDistrib_brownianSamples {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B C : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) (hC : IsBrownianReal C μ)
    (t : ℕ → ℝ≥0) : IdentDistrib (fun ω j => B (t j) ω) (fun ω j => C (t j) ω) μ μ := by
  have hd := (identDistrib_processPath_of_Brownian hB hC).comp
    (measurable_pi_lambda _ (fun j : ℕ => (continuous_eval_const (t j : ℝ)).measurable))
  have hb : (fun ω j => processPath B ω (t j : ℝ)) =ᵐ[μ] (fun ω j => B (t j) ω) := by
    filter_upwards [hB.cont] with ω hω
    funext j
    exact processPath_apply_of_continuous hω (t j)
  have hc : (fun ω j => processPath C ω (t j : ℝ)) =ᵐ[μ] (fun ω j => C (t j) ω) := by
    filter_upwards [hC.cont] with ω hω
    funext j
    exact processPath_apply_of_continuous hω (t j)
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst hb).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd hc)

end SwingRepair
