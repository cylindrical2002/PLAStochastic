import PLAStochastic.Swing.Gaussian.StripExit.Ballot

/-! # The actual frozen carry prefix and its slope envelope -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*}

/-- Maximal feasible prefix for the paper's frozen effective carry w.
The anchor E shifts the tolerance band to [w+W-2E,w+W]. -/
def frozenPrefixLength (X : ℕ → Ω → ℝ) (w E : ℝ) : Ω → WithTop ℕ :=
  nativePrefixLength (nativeCarriedSamples X (fun _ => w)) (fun _ => E) E

/-- The actual upper slope at the carried observation n+1. -/
def frozenUpperSlope (X : ℕ → Ω → ℝ) (w : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (w+cumulativeSamples X n ω)/((n : ℝ)+1)

/-- The paper's actual positive magnitude, not an independent replacement variable. -/
def frozenSlopeMagnitude (X : ℕ → Ω → ℝ) (w : ℝ) (ω : Ω) : ℝ :=
  sSup (Set.range (fun n : ℕ => -frozenUpperSlope X w n ω))

/-- Exact equivalence with the frozen constraints, with j=1 retaining the read carry. -/
theorem le_frozenPrefixLength_iff (X : ℕ → Ω → ℝ) (w E : ℝ) (n : ℕ) (ω : Ω) :
    (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω ↔
      ∃ m : ℝ, ∀ j ∈ Finset.Icc 1 n,
        w+cumulativeSamples X (j-1) ω-2*E ≤ m*(j : ℝ) ∧
        m*(j : ℝ) ≤ w+cumulativeSamples X (j-1) ω := by
  rw [frozenPrefixLength, le_nativePrefixLength_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j hj => ?_⟩
    have hj0 : j ≠ 0 := by have := Finset.mem_Icc.mp hj; omega
    have hh := hm j hj
    simp only [nativeCarriedSamples, if_neg hj0, Nat.cast_zero, sub_zero] at hh
    have h := abs_le.mp hh
    constructor <;> linarith [h.1, h.2]
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j hj => ?_⟩
    have hj0 : j ≠ 0 := by have := Finset.mem_Icc.mp hj; omega
    simp only [nativeCarriedSamples, if_neg hj0, Nat.cast_zero, sub_zero]
    apply abs_le.mpr
    have h := hm j hj
    constructor <;> linarith [h.1, h.2]

/-- Negative carry forces every feasible slope to stay below the carry value. -/
theorem frozenPrefix_negative_carry_endpoint {X : ℕ → Ω → ℝ} {c E : ℝ} {n : ℕ} {ω : Ω}
    (hn : 1 ≤ n) (h : (n : WithTop ℕ) ≤ frozenPrefixLength X (-c) E ω) :
    cumulativeSamples X (n-1) ω ≤ 2*E-c*((n : ℝ)-1) := by
  obtain ⟨m, hm⟩ := (le_frozenPrefixLength_iff X (-c) E n ω).mp h
  have h₁ := (hm 1 (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)).2
  simp only [Nat.sub_self, cumulativeSamples_zero, add_zero, Nat.cast_one, mul_one] at h₁
  have hlast := (hm n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)).1
  nlinarith [mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

end SwingRepair
