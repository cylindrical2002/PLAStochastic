import PLAStochastic.Swing.Gaussian.Bridge.Ballot
import PLAStochastic.Swing.FrozenCarry.Path.Prefix

/-! The true frozen-prefix constraints imply a Gaussian bridge survival event. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The starting height after conditioning on the final observed centered sum. -/
def frozenBridgeStart (w E : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  w-(w+y-2*E)/((N : ℝ)+1)

theorem frozenBridgeStart_measurable (w E : ℝ) (N : ℕ) : Measurable (frozenBridgeStart w E N) := by
  unfold frozenBridgeStart
  fun_prop

variable {Ω : Type*} {X : ℕ → Ω → ℝ} {w E : ℝ} {N M : ℕ} {ω : Ω}

/-- The endpoint lower slope is bounded above by every feasible upper slope. -/
theorem frozenPrefix_endpoint_slope_upper
    (h : ((N+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X w E ω) :
    ∀ j ≤ N, ((w+cumulativeSamples X N ω-2*E)/((N : ℝ)+1))*((j : ℝ)+1) ≤
      w+cumulativeSamples X j ω := by
  obtain ⟨q, hq⟩ := (le_frozenPrefixLength_iff X w E (N+1) ω).mp h
  have he := (hq (N+1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)).1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at he
  have hq0 : (w+cumulativeSamples X N ω-2*E)/((N : ℝ)+1) ≤ q :=
    (div_le_iff₀ (by positivity)).mpr he
  intro j hj
  have hu := (hq (j+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).2
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hu
  exact (mul_le_mul_of_nonneg_right hq0 (by positivity)).trans hu

/-- Feasibility retains the read carry and gives a nonnegative bridge starting point. -/
theorem frozenBridgeStart_nonneg_of_feasible
    (h : ((N+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X w E ω) :
    0 ≤ frozenBridgeStart w E N (cumulativeSamples X N ω) := by
  have hh := frozenPrefix_endpoint_slope_upper h 0 (Nat.zero_le N)
  simp only [Nat.cast_zero, zero_add, mul_one, cumulativeSamples_zero, add_zero] at hh
  exact sub_nonneg.mpr hh

/-- A fixed larger drift 2E/N removes the random drift from the necessary bridge event. -/
theorem frozenPrefix_implies_bridge_survives (hN : 0 < N) (hMN : M ≤ N)
    (h : ((N+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X w E ω) :
    ω ∈ gaussianBridgeSurvives X N (frozenBridgeStart w E N (cumulativeSamples X N ω))
      (2*E/(N : ℝ)) M := by
  have hx := frozenBridgeStart_nonneg_of_feasible h
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  intro j hj
  have hu := frozenPrefix_endpoint_slope_upper h j (hj.trans hMN)
  have he : frozenBridgeStart w E N (cumulativeSamples X N ω)+gaussianBridgePosition X N j ω+
      (2*E/(N : ℝ))*(j : ℝ) =
      w+cumulativeSamples X j ω-((w+cumulativeSamples X N ω-2*E)/((N : ℝ)+1))*((j : ℝ)+1)+
        frozenBridgeStart w E N (cumulativeSamples X N ω)*(j : ℝ)/(N : ℝ) := by
    unfold frozenBridgeStart gaussianBridgePosition
    field_simp
    ring
  rw [he]
  exact add_nonneg (sub_nonneg.mpr hu) (by positivity)

/-- The endpoint-dependent starting height has a simple integrable upper bound. -/
theorem frozenBridgeStart_le (w E : ℝ) (N : ℕ) (y : ℝ) :
    frozenBridgeStart w E N y ≤ max w 0+2*E/((N : ℝ)+1)+|y|/((N : ℝ)+1) := by
  have hn : (0 : ℝ) < (N : ℝ)+1 := by positivity
  have hw := le_max_left w 0
  have hw0 := le_max_right w 0
  have hnw := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hy := neg_le_abs y
  unfold frozenBridgeStart
  apply (mul_le_mul_iff_left₀ hn).mp
  field_simp
  nlinarith

end SwingRepair
