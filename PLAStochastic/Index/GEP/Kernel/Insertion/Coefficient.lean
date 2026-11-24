import PLAStochastic.Index.GEP.Kernel.Insertion.WidthCutoff
import PLAStochastic.Index.GEP.Kernel.Influence.Pins.OuterRows
import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.BlockIndex

/-!
# The actual exterior reward and the other pin as a signed Green coefficient

Both outside paths are kept in one joint reward. After integration and
summation of the two outside lengths and the other pin length, the remaining
coefficient may still couple the two marked-side lengths arbitrarily.
-/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option maxHeartbeats 800000

/-- Actual outside survival of the original facet indexed by the block lengths. -/
def krInsertionOuter (w : ℝ) (outerUp : Bool) (l r : ℕ) (t : ℕ × ℕ × ℕ)
    (a : ℝ) (g : ℕ → ℝ) : ℝ :=
  kernelIFOuterSurvival (w/2) a
    (kernelIFLeftOfBlocks (t.1,l,r,t.2.1,t.2.2,outerUp)).1.2.2 g

/-- The exterior rows depend only on the first and last contacts. -/
theorem krInsertionOuter_eq (w : ℝ) (outerUp : Bool) (l r : ℕ) (t : ℕ × ℕ × ℕ)
    (a : ℝ) (g : ℕ → ℝ) :
    krInsertionOuter w outerUp l r t a g =
      krAlive (Icc 0 w) (-1) (-a) t.1 (if outerUp then 0 else w)
        (kernelReversePrefix g t.1) *
      krAlive (Icc 0 w) 1 a t.2.2 (if outerUp then 0 else w)
        (fun j => g (j+(t.1+(l+r+1)+(t.2.1+1)))) := by
  have hw : 2*(w/2)=w := by ring
  cases outerUp <;>
    simp [hw,krInsertionOuter,kernelIFLeftOfBlocks,kernelIFOuterSurvival,fluxFacetSign]

/-- Both slope and the unmodified exterior coordinates remain measurable. -/
theorem measurable_krInsertionOuter (w : ℝ) (outerUp : Bool) (l r : ℕ) (t : ℕ × ℕ × ℕ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => krInsertionOuter w outerUp l r t p.1 p.2) := by
  simp_rw [krInsertionOuter_eq]
  apply Measurable.mul
  · apply measurable_krAlive_param measurableSet_Icc measurable_const measurable_fst.neg measurable_const
    unfold kernelReversePrefix
    fun_prop
  · apply measurable_krAlive_param measurableSet_Icc measurable_const measurable_fst measurable_const
    fun_prop

theorem krInsertionOuter_nonneg (w : ℝ) (outerUp : Bool) (l r : ℕ) (t : ℕ × ℕ × ℕ)
    (a : ℝ) (g : ℕ → ℝ) : 0 ≤ krInsertionOuter w outerUp l r t a g :=
  kernel_IF_outer_survival_nonneg _ _ _ _

theorem krInsertionOuter_le_one (w : ℝ) (outerUp : Bool) (l r : ℕ) (t : ℕ × ℕ × ℕ)
    (a : ℝ) (g : ℕ → ℝ) : krInsertionOuter w outerUp l r t a g ≤ 1 := by
  rw [krInsertionOuter_eq]
  exact (mul_le_mul (krAlive_le_one _ _ _) (krAlive_le_one _ _ _)
    (krAlive_nonneg _ _ _) zero_le_one).trans_eq (one_mul 1)

/-- The original outside integral is the product of the two actual killed rows. -/
theorem integral_krInsertionOuter (ν : ProbabilityMeasure ℝ) (w : ℝ) (outerUp : Bool)
    (l r : ℕ) (t : ℕ × ℕ × ℕ) (a : ℝ) :
    (∫ g, krInsertionOuter w outerUp l r t a g ∂iidLaw ν) =
      krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) t.1 (if outerUp then 0 else w) *
      krSurv (Icc 0 w) (ν : Measure ℝ) 1 a t.2.2 (if outerUp then 0 else w) := by
  have hmap : Measurable (fun g : ℕ → ℝ => (a,g)) := measurable_const.prodMk measurable_id
  have hm : Measurable (krInsertionOuter w outerUp l r t a) :=
    (measurable_krInsertionOuter w outerUp l r t).comp hmap
  have hi : Integrable (krInsertionOuter w outerUp l r t a) (iidLaw ν) :=
    kr_integrable_of_bdd (μ := iidLaw ν) (F := krInsertionOuter w outerUp l r t a) hm (M := 1) (fun g => by
      rw [abs_of_nonneg (krInsertionOuter_nonneg w outerUp l r t a g)]
      exact krInsertionOuter_le_one w outerUp l r t a g)
  have he := kernel_IF_outer_lintegral ν (w/2) a
    (kernelIFLeftOfBlocks (t.1,l,r,t.2.1,t.2.2,outerUp)).1.2.2 (by
      change t.1 ≤ t.1+(l+r+1)+(t.2.1+1)
      omega)
  change (∫⁻ g, ENNReal.ofReal (krInsertionOuter w outerUp l r t a g) ∂iidLaw ν) = _ at he
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun g => krInsertionOuter_nonneg w outerUp l r t a g))] at he
  have he' := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun g => krInsertionOuter_nonneg w outerUp l r t a g)),
    ENNReal.toReal_ofReal (mul_nonneg
      (krSurv_nonneg measurableSet_Icc ν _ _ _ _) (krSurv_nonneg measurableSet_Icc ν _ _ _ _))] at he'
  have hw : 2*(w/2)=w := by ring
  cases outerUp <;> simpa [hw,kernelIFLeftOfBlocks,fluxFacetSign] using he'

/-- The exact ordinary-pin Jacobian, including its possible sign before support is applied. -/
def krInsertionOtherFactor (w : ℝ) (up : Bool) (m : ℕ) : ℝ :=
  (m : ℝ)+1+(if up then w else -w)

/-- One actual signed outside-and-pin term, before the three outside lengths are summed. -/
def krInsertionCoefficientTerm (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w : ℝ)
    (up outerUp : Bool) (W : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℝ → (ℕ → ℝ) → ℝ)
    (l r : ℕ) (t : ℕ × ℕ × ℕ) (a : ℝ) : ℝ :=
  krInsertionOtherFactor w up t.2.1 *
    krDens (Icc 0 w) ν f 1 a (t.2.1+1) (if up then w else 0) (if up then 0 else w) *
    ∫ g, krInsertionOuter w outerUp l r t a g * W l r t a g ∂iidLaw ν

/-- Canonical coefficient left after the marked insertion Green rows are isolated. -/
def krInsertionCoefficient (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w : ℝ)
    (up outerUp : Bool) (W : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℝ → (ℕ → ℝ) → ℝ)
    (l r : ℕ) (a : ℝ) : ℝ :=
  ∑' t : ℕ × ℕ × ℕ, krInsertionCoefficientTerm ν f w up outerUp W l r t a

/-- The actual coefficient is measurable, without any separability assumption on the reward. -/
theorem measurable_krInsertionCoefficient (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (w : ℝ) (up outerUp : Bool)
    {W : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℝ → (ℕ → ℝ) → ℝ}
    (hW : ∀ l r t, Measurable (fun p : ℝ × (ℕ → ℝ) => W l r t p.1 p.2))
    (l r : ℕ) : Measurable (krInsertionCoefficient ν f w up outerUp W l r) := by
  apply Measurable.tsum
  intro t
  unfold krInsertionCoefficientTerm
  apply Measurable.mul
  · exact measurable_const.mul (measurable_krDens_param ν measurableSet_Icc hf
      measurable_const measurable_id measurable_const measurable_const _)
  · exact ((measurable_krInsertionOuter w outerUp l r t).mul (hW l r t)).stronglyMeasurable.integral_prod_right'.measurable


/-- A signed joint exterior reward is controlled on the actual survival event. -/
theorem krInsertion_outer_reward_bound (ν : ProbabilityMeasure ℝ) (w : ℝ) (outerUp : Bool)
    (l r : ℕ) (t : ℕ × ℕ × ℕ) (a : ℝ) {W : (ℕ → ℝ) → ℝ} {C : ℝ}
    (hW : Measurable W) (_hC : 0 ≤ C)
    (hB : ∀ g, krInsertionOuter w outerUp l r t a g ≠ 0 → |W g| ≤ C) :
    Integrable (fun g => krInsertionOuter w outerUp l r t a g*W g) (iidLaw ν) ∧
    |∫ g, krInsertionOuter w outerUp l r t a g*W g ∂iidLaw ν| ≤
      C*(krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) t.1 (if outerUp then 0 else w)*
        krSurv (Icc 0 w) (ν : Measure ℝ) 1 a t.2.2 (if outerUp then 0 else w)) := by
  have hmap : Measurable (fun g : ℕ → ℝ => (a,g)) := measurable_const.prodMk measurable_id
  have hm : Measurable (krInsertionOuter w outerUp l r t a) :=
    (measurable_krInsertionOuter w outerUp l r t).comp hmap
  have hi : Integrable (krInsertionOuter w outerUp l r t a) (iidLaw ν) :=
    kr_integrable_of_bdd (μ := iidLaw ν) (F := krInsertionOuter w outerUp l r t a) hm (M := 1) (fun g => by
      rw [abs_of_nonneg (krInsertionOuter_nonneg w outerUp l r t a g)]
      exact krInsertionOuter_le_one w outerUp l r t a g)
  have hb (g : ℕ → ℝ) : |krInsertionOuter w outerUp l r t a g*W g| ≤
      C*krInsertionOuter w outerUp l r t a g := by
    by_cases hz : krInsertionOuter w outerUp l r t a g = 0
    · simp only [hz,zero_mul,mul_zero,abs_zero,le_refl]
    · rw [abs_mul,abs_of_nonneg (krInsertionOuter_nonneg w outerUp l r t a g),mul_comm C]
      exact mul_le_mul_of_nonneg_left (hB g hz) (krInsertionOuter_nonneg w outerUp l r t a g)
  refine ⟨(hi.const_mul C).mono' (hm.mul hW).aestronglyMeasurable
    (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb g)),?_⟩
  have hh := norm_integral_le_of_norm_le
    (f := fun g => krInsertionOuter w outerUp l r t a g*W g) (hi.const_mul C)
    (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb g))
  simpa only [Real.norm_eq_abs,integral_const_mul,integral_krInsertionOuter] using hh

/-- The physical ordinary-pin Jacobian is at most its length plus the width. -/
theorem abs_krInsertionOtherFactor {w : ℝ} (hw : 0 ≤ w) (up : Bool) (m : ℕ) :
    |krInsertionOtherFactor w up m| ≤ (m : ℝ)+1+w := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  cases up <;> simp only [krInsertionOtherFactor,Bool.false_eq_true,if_false,if_true]
  · exact abs_le.mpr ⟨by linarith,by linarith⟩
  · rw [abs_of_nonneg (by positivity)]

/-- One actual coefficient term is dominated by the weighted other pin and both rows. -/
theorem krInsertion_coefficient_term_bound (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {w : ℝ} (hw : 0 ≤ w) (up outerUp : Bool)
    {W : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℝ → (ℕ → ℝ) → ℝ}
    (l r : ℕ) (t : ℕ × ℕ × ℕ) (a : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hW : Measurable (W l r t a))
    (hB : ∀ g, krInsertionOuter w outerUp l r t a g ≠ 0 → |W l r t a g| ≤ C) :
    |krInsertionCoefficientTerm ν f w up outerUp W l r t a| ≤
      C*(((t.2.1 : ℝ)+1+w)*
        krDens (Icc 0 w) ν f 1 a (t.2.1+1) (if up then w else 0) (if up then 0 else w))*
      (krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) t.1 (if outerUp then 0 else w)*
        krSurv (Icc 0 w) (ν : Measure ℝ) 1 a t.2.2 (if outerUp then 0 else w)) := by
  have hpin := krDens_nonneg (J := Icc 0 w) (β := 1) (a := a) ν hf0 (t.2.1+1)
    (if up then w else 0) (if up then 0 else w)
  have ho := (krInsertion_outer_reward_bound ν w outerUp l r t a hW hC hB).2
  unfold krInsertionCoefficientTerm
  rw [abs_mul,abs_mul,abs_of_nonneg hpin]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_right (abs_krInsertionOtherFactor hw up t.2.1) hpin)
    ho (abs_nonneg _) (mul_nonneg (by positivity) hpin)
  exact hh.trans_eq (by ring)


/-- All three actual exterior lengths are absolutely summable. Their coefficient
cost is two linear occupation budgets and one linear weighted-pin budget. -/
theorem krInsertion_coefficient_budget {D θ vlo vhi K L w A a : ℝ}
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a 1 a) (up outerUp : Bool)
    {ε M : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi/16) (hM : 0 ≤ M)
    {W : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℝ → (ℕ → ℝ) → ℝ}
    (hW : ∀ l r t, Measurable (W l r t a))
    (hWB : ∀ l r t g, krInsertionOuter w outerUp l r t a g ≠ 0 →
      |W l r t a g| ≤ M*Real.exp (ε*((t.1 : ℝ)+l+r+t.2.1+t.2.2+2)/w^2))
    (l r : ℕ) :
    let OB := Real.exp (3*ε)*((krCO D K L vlo vhi+4*krC₃ D K L/krKappa D vlo vhi)*(1+A)*w)
    let WB := Real.exp (3*ε)*((krCB D K L vlo vhi+264*krC₂ D K L/krKappa D vlo vhi^2)*(1+A)^2*w)
    Summable (fun t : ℕ × ℕ × ℕ => |krInsertionCoefficientTerm ν f w up outerUp W l r t a|) ∧
    |krInsertionCoefficient ν f w up outerUp W l r a| ≤
      (M*Real.exp (ε/w^2)*OB^2*WB)*
        (Real.exp (ε*(l : ℝ)/w^2)*Real.exp (ε*(r : ℝ)/w^2)) := by
  let b : ℝ := if outerUp then 0 else w
  let y : ℝ := if up then 0 else w
  let z : ℝ := if up then w else 0
  have hb : b=0 ∨ b=w := by cases outerUp <;> simp [b]
  have hy : y=0 ∨ y=w := by cases up <;> simp [y]
  have hz : z=0 ∨ z=w := by cases up <;> simp [z]
  let U (n : ℕ) := Real.exp (ε*(n : ℝ)/w^2)*krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) n b
  let V (n : ℕ) := Real.exp (ε*(n : ℝ)/w^2)*krSurv (Icc 0 w) (ν : Measure ℝ) 1 a n b
  let Q (n : ℕ) := Real.exp (ε*((n+1 : ℕ) : ℝ)/w^2)*
    (((n : ℝ)+1+w)*krDens (Icc 0 w) ν f 1 a (n+1) z y)
  let OB := Real.exp (3*ε)*((krCO D K L vlo vhi+4*krC₃ D K L/krKappa D vlo vhi)*(1+A)*w)
  let WB := Real.exp (3*ε)*((krCB D K L vlo vhi+264*krC₂ D K L/krKappa D vlo vhi^2)*(1+A)^2*w)
  let C := M*Real.exp (ε/w^2)*Real.exp (ε*(l : ℝ)/w^2)*Real.exp (ε*(r : ℝ)/w^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hU (n : ℕ) : 0 ≤ U n := mul_nonneg (Real.exp_nonneg _) (krSurv_nonneg H.hJ ν _ _ _ _)
  have hV (n : ℕ) : 0 ≤ V n := mul_nonneg (Real.exp_nonneg _) (krSurv_nonneg H.hJ ν _ _ _ _)
  have hQ (n : ℕ) : 0 ≤ Q n := mul_nonneg (Real.exp_nonneg _)
    (mul_nonneg (by linarith [H.hw0,(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (krDens_nonneg ν H.hf0 _ _ _))
  have hsU : Summable U := summable_expw_krSurv_bdry ν H.rev hb hε0 hε
  have hsV : Summable V := summable_expw_krSurv_bdry ν H hb hε0 hε
  have hsQ : Summable Q := summable_expw_weighted_krDens_bdry_pin ν H hz hy hε0 hε
  have hUB : (∑' n, U n) ≤ OB := tsum_expw_krSurv_bdry_le ν H.rev hb hε0 hε
  have hVB : (∑' n, V n) ≤ OB := tsum_expw_krSurv_bdry_le ν H hb hε0 hε
  have hQB : (∑' n, Q n) ≤ WB := tsum_expw_weighted_krDens_bdry_pin_le ν H hz hy hε0 hε
  have hOB0 : 0 ≤ OB := (tsum_nonneg hU).trans hUB
  have hWB0 : 0 ≤ WB := (tsum_nonneg hQ).trans hQB
  have hsQV := hsQ.mul_of_nonneg hsV hQ hV
  have hQV (p : ℕ × ℕ) : 0 ≤ Q p.1*V p.2 := mul_nonneg (hQ p.1) (hV p.2)
  have hsT := hsU.mul_of_nonneg hsQV hU hQV
  have hmaj (t : ℕ × ℕ × ℕ) : |krInsertionCoefficientTerm ν f w up outerUp W l r t a| ≤
      C*(U t.1*(Q t.2.1*V t.2.2)) := by
    have hh := krInsertion_coefficient_term_bound ν H.hf0 H.hw0.le up outerUp l r t a
      (show 0 ≤ M*Real.exp (ε*((t.1 : ℝ)+l+r+t.2.1+t.2.2+2)/w^2) by positivity)
      (hW l r t) (hWB l r t)
    apply hh.trans_eq
    dsimp only [C,U,Q,V,b,y,z]
    push_cast
    have he : Real.exp (ε*((t.1 : ℝ)+l+r+t.2.1+t.2.2+2)/w^2) =
      Real.exp (ε/w^2)*Real.exp (ε*(l : ℝ)/w^2)*Real.exp (ε*(r : ℝ)/w^2)*
        Real.exp (ε*(t.1 : ℝ)/w^2)*Real.exp (ε*((t.2.1 : ℝ)+1)/w^2)*Real.exp (ε*(t.2.2 : ℝ)/w^2) := by
      rw [← Real.exp_add,← Real.exp_add,← Real.exp_add,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  refine ⟨Summable.of_nonneg_of_le (fun t => abs_nonneg _) hmaj (hsT.mul_left C),?_⟩
  have hsum : (∑' t : ℕ × ℕ × ℕ, U t.1*(Q t.2.1*V t.2.2)) ≤ OB*(WB*OB) := by
    rw [← hsU.tsum_mul_tsum hsQV hsT,← hsQ.tsum_mul_tsum hsV hsQV]
    exact mul_le_mul hUB (mul_le_mul hQB hVB (tsum_nonneg hV) hWB0)
      (mul_nonneg (tsum_nonneg hQ) (tsum_nonneg hV)) hOB0
  have hh := tsum_of_norm_bounded (hsT.mul_left C).hasSum
    (fun t => show ‖krInsertionCoefficientTerm ν f w up outerUp W l r t a‖ ≤ _ from
      by simpa only [Real.norm_eq_abs] using hmaj t)
  change ‖krInsertionCoefficient ν f w up outerUp W l r a‖ ≤ _ at hh
  rw [tsum_mul_left] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left hsum hC)).trans_eq (by dsimp only [C]; ring)

end
end PGM
