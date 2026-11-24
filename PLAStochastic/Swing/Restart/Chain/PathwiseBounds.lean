import PLAStochastic.Swing.Restart.Chain.ShortSegments
import PLAStochastic.Swing.Restart.Chain.Specification

/-! # Pathwise duration, slope, and margin bounds at an actual restart

The only path input is a bound on all fresh partial sums.  The duration lower
bound is proved with a candidate line; the selected slope is then bounded using
its actual last accepted sample.  These bounds do not assume an overshoot law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*}

def nativeRestartExcess (E x : ℝ) : ℝ := max (|x|-E) 0

theorem nativeRestart_candidate_feasible (X : ℕ → Ω → ℝ) {E G x : ℝ}
    (_hE : 0 ≤ E) (hG : 0 ≤ G) (ω : Ω)
    (hW : ∀ n, |cumulativeSamples X n ω| ≤ G*((n : ℝ)+1))
    {N : ℕ} (hN : (nativeRestartExcess E x+2*G)*(N : ℝ) ≤ E) :
    nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) E 0 N 0 := by
  let c := nativeRestartExcess E x
  have hc : 0 ≤ c := le_max_right _ _
  have hx : |x| ≤ E+c := by have := le_max_left (|x|-E) 0; dsimp [c, nativeRestartExcess]; linarith
  have hB : 0 ≤ c+2*G := by positivity
  by_cases hx0 : 0 ≤ x
  · refine ⟨c+G, fun i hi => ?_⟩
    have hi' := Finset.mem_Icc.mp hi
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi'.1
    have hiN : (i : ℝ) ≤ N := by exact_mod_cast hi'.2
    have hwi := hW (i-1)
    rw [Nat.cast_sub hi'.1, Nat.cast_one, sub_add_cancel] at hwi
    have hBn : (c+2*G)*(i : ℝ) ≤ E :=
      (mul_le_mul_of_nonneg_left hiN hB).trans hN
    have hci : c ≤ c*(i : ℝ) := by nlinarith
    simp only [nativeCarriedSamples, if_neg (by omega : i ≠ 0), Nat.cast_zero, sub_zero,
      zero_add]
    rw [abs_le]
    rw [abs_of_nonneg hx0] at hx
    constructor <;> nlinarith [(abs_le.mp hwi).1, (abs_le.mp hwi).2]
  · have hxneg : x ≤ 0 := (lt_of_not_ge hx0).le
    refine ⟨-(c+G), fun i hi => ?_⟩
    have hi' := Finset.mem_Icc.mp hi
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi'.1
    have hiN : (i : ℝ) ≤ N := by exact_mod_cast hi'.2
    have hwi := hW (i-1)
    rw [Nat.cast_sub hi'.1, Nat.cast_one, sub_add_cancel] at hwi
    have hBn : (c+2*G)*(i : ℝ) ≤ E :=
      (mul_le_mul_of_nonneg_left hiN hB).trans hN
    have hci : c ≤ c*(i : ℝ) := by nlinarith
    simp only [nativeCarriedSamples, if_neg (by omega : i ≠ 0), Nat.cast_zero, sub_zero,
      zero_add]
    rw [abs_le]
    rw [abs_of_nonpos hxneg] at hx
    constructor <;> nlinarith [(abs_le.mp hwi).1, (abs_le.mp hwi).2]

theorem nativeRestartLength_floor_lower (X : ℕ → Ω → ℝ) {E G x : ℝ}
    (hE : 0 ≤ E) (hG : 0 ≤ G) (ω : Ω)
    (hW : ∀ n, |cumulativeSamples X n ω| ≤ G*((n : ℝ)+1))
    (hB : 0 < nativeRestartExcess E x+2*G) :
    (⌊E/(nativeRestartExcess E x+2*G)⌋₊ : WithTop ℕ) ≤ nativeRestartLength X E x ω := by
  apply (le_nativePrefixLength_iff _ _ _ _ _).mpr
  apply nativeRestart_candidate_feasible X hE hG ω hW
  have hf := Nat.floor_le (div_nonneg hE hB.le)
  have hh := (mul_le_mul_of_nonneg_left hf hB.le)
  rwa [mul_div_cancel₀ _ hB.ne'] at hh

/-- A finite actual prefix is long enough to absorb its initial boundary excess. -/
theorem nativeRestartLengthNat_scale_lower (X : ℕ → Ω → ℝ) {E G x : ℝ}
    (hE : 0 ≤ E) (hG : 0 ≤ G) (ω : Ω)
    (hW : ∀ n, |cumulativeSamples X n ω| ≤ G*((n : ℝ)+1))
    (hB : 0 < nativeRestartExcess E x+2*G)
    (hfinite : nativeRestartLength X E x ω ≠ ⊤) :
    1 ≤ nativeRestartLengthNat X E x ω ∧
      E ≤ 2*(nativeRestartExcess E x+2*G)*(nativeRestartLengthNat X E x ω : ℝ) := by
  have hone := one_le_nativePrefixLength (nativeCarriedSamples X (fun _ => x))
    (fun _ => 0) hE ω
  have hf := nativeRestartLength_floor_lower X hE hG ω hW hB
  change (1 : WithTop ℕ) ≤ nativeRestartLength X E x ω at hone
  change 1 ≤ (nativeRestartLength X E x ω).untopD 0 ∧
    E ≤ 2*(nativeRestartExcess E x+2*G)*
      (((nativeRestartLength X E x ω).untopD 0 : ℕ) : ℝ)
  cases heq : nativeRestartLength X E x ω using WithTop.recTopCoe with
  | top => exact (hfinite heq).elim
  | coe N =>
    rw [heq] at hone hf
    have hN : 1 ≤ N := WithTop.coe_le_coe.mp hone
    have hfloor : ⌊E/(nativeRestartExcess E x+2*G)⌋₊ ≤ N := WithTop.coe_le_coe.mp hf
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hfloorR : (⌊E/(nativeRestartExcess E x+2*G)⌋₊ : ℝ) ≤ N := by exact_mod_cast hfloor
    have hlt := Nat.lt_floor_add_one (E/(nativeRestartExcess E x+2*G))
    have hdiv : E/(nativeRestartExcess E x+2*G) < (N : ℝ)+1 := by linarith
    have hprod := (div_lt_iff₀ hB).mp hdiv
    refine ⟨hN, ?_⟩
    change E ≤ 2*(nativeRestartExcess E x+2*G)*(N : ℝ)
    nlinarith

/-- Every feasible final slope satisfies the required uniform pathwise bound. -/
theorem nativeRestart_feasible_slope_bound (X : ℕ → Ω → ℝ) {E G x m : ℝ}
    (hE : 0 ≤ E) (hG : 0 ≤ G) (ω : Ω)
    (hW : ∀ n, |cumulativeSamples X n ω| ≤ G*((n : ℝ)+1))
    (hB : 0 < nativeRestartExcess E x+2*G)
    (hfinite : nativeRestartLength X E x ω ≠ ⊤)
    (hfit : feasibleSlope (Finset.Icc 1 (nativeRestartLengthNat X E x ω))
      (fun i => (i : ℝ)) (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E m) :
    |m| ≤ 5*nativeRestartExcess E x+10*G := by
  obtain ⟨hN, hscale⟩ := nativeRestartLengthNat_scale_lower X hE hG ω hW hB hfinite
  let N := nativeRestartLengthNat X E x ω
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlast := hfit N (Finset.mem_Icc.mpr ⟨hN, le_rfl⟩)
  have hwi := hW (N-1)
  rw [Nat.cast_sub hN, Nat.cast_one, sub_add_cancel] at hwi
  simp only [nativeCarriedSamples, if_neg (by omega : N ≠ 0), sub_zero,
    zero_add] at hlast
  have hx : |x| ≤ E+nativeRestartExcess E x := by
    have := le_max_left (|x|-E) 0
    dsimp [nativeRestartExcess]
    linarith
  have hc : 0 ≤ nativeRestartExcess E x := le_max_right _ _
  have hres := abs_le.mp hlast
  have hw := abs_le.mp hwi
  have hxx := abs_le.mp hx
  have hm : |m| *(N : ℝ) ≤ 2*E+nativeRestartExcess E x+G*(N : ℝ) := by
    have heq : |m| * (N : ℝ) = |m*(N : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ N by positivity)]
    rw [heq, abs_le]
    constructor <;> linarith [hres.1, hres.2, hw.1, hw.2, hxx.1, hxx.2]
  have hcN : nativeRestartExcess E x ≤ nativeRestartExcess E x*(N : ℝ) := by nlinarith
  have hGprod : 0 ≤ G*(N : ℝ) := by positivity
  nlinarith

theorem nativeRestart_slope_bound (X : ℕ → Ω → ℝ) {E G x : ℝ}
    (hE : 0 ≤ E) (hG : 0 ≤ G) (ω : Ω)
    (hW : ∀ n, |cumulativeSamples X n ω| ≤ G*((n : ℝ)+1))
    (hB : 0 < nativeRestartExcess E x+2*G)
    (hf : nativeRestartLength X E x ω ≠ ⊤) :
    |nativeRestartSlope X E x ω| ≤ 5*nativeRestartExcess E x+10*G :=
  nativeRestart_feasible_slope_bound X hE hG ω hW hB hf
    (nativeRestartSlope_feasible X hE x ω hf)

/-- Both endpoints of the actual final cone have the same uniform bound. -/
theorem nativeRestart_final_cone_bound (X : ℕ → Ω → ℝ) {E G x : ℝ}
    (hE : 0 ≤ E) (hG : 0 ≤ G) (ω : Ω)
    (hW : ∀ n, |cumulativeSamples X n ω| ≤ G*((n : ℝ)+1))
    (hB : 0 < nativeRestartExcess E x+2*G)
    (hf : nativeRestartLength X E x ω ≠ ⊤)
    (hn : 0 < nativeRestartLengthNat X E x ω) :
    |nativeConeLower (Finset.Icc 1 (nativeRestartLengthNat X E x ω))
        (Finset.nonempty_Icc.mpr hn) (fun i => (i : ℝ))
        (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E| ≤
          5*nativeRestartExcess E x+10*G ∧
      |nativeConeUpper (Finset.Icc 1 (nativeRestartLengthNat X E x ω))
        (Finset.nonempty_Icc.mpr hn) (fun i => (i : ℝ))
        (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E| ≤
          5*nativeRestartExcess E x+10*G := by
  have ht : ∀ i ∈ Finset.Icc 1 (nativeRestartLengthNat X E x ω), (0 : ℝ) < i := by
    intro i hi
    have := (Finset.mem_Icc.mp hi).1
    exact_mod_cast (show 0 < i by omega)
  have hc : ∃ m, feasibleSlope (Finset.Icc 1 (nativeRestartLengthNat X E x ω))
      (fun i => (i : ℝ)) (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E m := by
    simpa only [nativePrefixFeasible, Nat.cast_zero, Nat.zero_add] using
      (nativeRestartLengthNat_spec X E x ω hf).1
  have hlu := (nativeCone_nonempty_iff _ (Finset.nonempty_Icc.mpr hn) _ _ 0 0 E ht).mp hc
  constructor
  · apply nativeRestart_feasible_slope_bound X hE hG ω hW hB hf
    exact (nativeCone_mem_iff _ (Finset.nonempty_Icc.mpr hn) _ _ 0 0 E _ ht).mp ⟨le_rfl, hlu⟩
  · apply nativeRestart_feasible_slope_bound X hE hG ω hW hB hf
    exact (nativeCone_mem_iff _ (Finset.nonempty_Icc.mpr hn) _ _ 0 0 E _ ht).mp ⟨hlu, le_rfl⟩

end SwingRepair
