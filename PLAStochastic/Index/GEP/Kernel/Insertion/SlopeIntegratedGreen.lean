import PLAStochastic.Index.GEP.Kernel.Insertion.GreenDecomposition
import PLAStochastic.Index.GEP.Kernel.Insertion.SlopeJump

/-!
# Slope integration of the actual insertion Green function

The finite width of the near-critical slope window multiplies the regular
and error budgets. The endpoint trace uses the moving-jump estimate.
-/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

/-- The exceptional endpoint equation is null for each spatial argument. -/
theorem kr_ae_slope_mul_ne_one (x : ℝ) : ∀ᵐ a ∂volume, a*x ≠ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  filter_upwards [volume.ae_ne (1/x)] with a ha
  exact fun h => ha ((eq_div_iff hx).2 h)

set_option maxHeartbeats 600000 in
/-- Localizing the established slope-split lemma keeps the exact window measure. -/
theorem krInsertion_near_integral_of_split {S : Set ℝ} (hS : MeasurableSet S)
    (hSI : S ⊆ Ioo (1/2 : ℝ) 2) {R LB EB JB GB : ℝ}
    {F : ℝ → ℝ → ℝ} {G E : ℝ → ℝ → ℂ} {j : ℝ → ℂ}
    (hG : Measurable fun p : ℝ × ℝ => G p.1 p.2)
    (hE : Measurable fun p : ℝ × ℝ => E p.1 p.2) (hj : Measurable j)
    (hEB : 0 ≤ EB) (hJB : 0 ≤ JB) (hGB : 0 ≤ GB)
    (hsplit : ∀ a ∈ S, ∀ x ∈ Icc 0 R, a*x ≠ 1 →
      (F a x : ℂ) = G a x+(if a*x < 1 then j a else 0)+E a x)
    (hL : ∀ a ∈ S, ∀ x y, ‖G a x-G a y‖ ≤ LB*|x-y|)
    (hErr : ∀ a ∈ S, ∀ x ∈ Icc 0 R, ‖E a x‖ ≤ EB)
    (hJump : ∀ a ∈ S, ‖j a‖ ≤ JB) (hSup : ∀ a ∈ S, ∀ x, ‖G a x‖ ≤ GB) :
    KernelApproxLip R (volume.real S*LB+4*JB) (volume.real S*EB)
      (fun x => ∫ a in S, F a x) := by
  classical
  let g : ℝ → ℝ → ℝ := fun a x => S.indicator (fun a => (G a x).re) a
  let e : ℝ → ℝ → ℝ := fun a x => S.indicator (fun a => (E a x).re) a
  let z : ℝ → ℝ := S.indicator (fun a => (j a).re)
  have gi (x : ℝ) : IntegrableOn (fun a => g a x) (Ioo (1/2 : ℝ) 2) := by
    apply (integrableOn_const (μ := volume) (s := Ioo (1/2 : ℝ) 2) (C := GB) (by simp)).mono'
      (((Complex.measurable_re.comp (hG.comp (measurable_id.prodMk measurable_const))).indicator hS).aestronglyMeasurable)
    apply ae_of_all
    intro a
    by_cases ha : a ∈ S
    · simpa only [g, indicator_of_mem ha, Real.norm_eq_abs, Function.comp_apply, id_eq] using
        (Complex.abs_re_le_norm (G a x)).trans (hSup a ha x)
    · simpa only [g, indicator_of_notMem ha, norm_zero] using hGB
  have ei (x : ℝ) (hx : x ∈ Icc 0 R) :
      IntegrableOn (fun a => e a x) (Ioo (1/2 : ℝ) 2) := by
    apply (integrableOn_const (μ := volume) (s := Ioo (1/2 : ℝ) 2) (C := EB) (by simp)).mono'
      (((Complex.measurable_re.comp (hE.comp (measurable_id.prodMk measurable_const))).indicator hS).aestronglyMeasurable)
    apply ae_of_all
    intro a
    by_cases ha : a ∈ S
    · simpa only [e, indicator_of_mem ha, Real.norm_eq_abs, Function.comp_apply, id_eq] using
        (Complex.abs_re_le_norm (E a x)).trans (hErr a ha x hx)
    · simpa only [e, indicator_of_notMem ha, norm_zero] using hEB
  have zb (a : ℝ) : |z a| ≤ JB := by
    by_cases ha : a ∈ S
    · simpa only [z, indicator_of_mem ha] using
        (Complex.abs_re_le_norm (j a)).trans (hJump a ha)
    · simpa only [z, indicator_of_notMem ha, abs_zero] using hJB
  have zi : IntervalIntegrable z volume (1/2 : ℝ) 2 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1/2 : ℝ) ≤ 2)]
    exact (integrableOn_const (μ := volume) (s := Ioo (1/2 : ℝ) 2) (C := JB) (by simp)).mono' (((Complex.measurable_re.comp hj).indicator hS).aestronglyMeasurable)
      (ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using zb a))
  have li : IntegrableOn (S.indicator fun _ : ℝ => LB) (Ioo (1/2 : ℝ) 2) :=
    (integrableOn_const (μ := volume) (s := Ioo (1/2 : ℝ) 2) (by simp)).indicator hS
  have ri : IntegrableOn (S.indicator fun _ : ℝ => EB) (Ioo (1/2 : ℝ) 2) :=
    (integrableOn_const (μ := volume) (s := Ioo (1/2 : ℝ) 2) (by simp)).indicator hS
  have hi (c : ℝ) : (∫ a in Ioo (1/2 : ℝ) 2, S.indicator (fun _ => c) a) =
      volume.real S*c := by
    rw [integral_indicator hS, Measure.restrict_restrict hS, inter_eq_left.mpr hSI,
      setIntegral_const, smul_eq_mul]
  have hI (x : ℝ) : (∫ a in Ioo (1/2 : ℝ) 2, S.indicator (fun a => F a x) a) =
      ∫ a in S, F a x := by
    rw [integral_indicator hS, Measure.restrict_restrict hS, inter_eq_left.mpr hSI]
  have h := kernelApproxLip_of_slope_split
    (H := fun a x => S.indicator (fun a => F a x) a)
    (h := g) (r := e) (f := z) (L := S.indicator fun _ => LB)
    (E := S.indicator fun _ => EB)
    (fun x _ => gi x) ei zi li ri hJB (ae_of_all _ zb) ?_ ?_ ?_
  · simpa only [hi, hI] using h
  · intro x hx
    filter_upwards [ae_restrict_of_ae (kr_ae_slope_mul_ne_one x)] with a ha
    by_cases has : a ∈ S
    · have hs := congrArg Complex.re (hsplit a has x hx ha)
      by_cases hax : a*x < 1
      · simpa [g,e,z,has,hax] using hs
      · simpa [g,e,z,has,hax] using hs
    · simp only [g,e,z,indicator_of_notMem has]
      by_cases hax : a*x < 1 <;> simp [hax,has]
  · intro x _ y _
    apply ae_of_all
    intro a
    by_cases ha : a ∈ S
    · simpa only [g,indicator_of_mem ha,Complex.sub_re] using
        (Complex.abs_re_le_norm (G a x-G a y)).trans (hL a ha x y)
    · simp only [g,indicator_of_notMem ha,sub_self,abs_zero,zero_mul,le_refl]
  · intro x hx
    apply ae_of_all
    intro a
    by_cases ha : a ∈ S
    · simpa only [e,indicator_of_mem ha] using
        (Complex.abs_re_le_norm (E a x)).trans (hErr a ha x hx)
    · simp only [e,indicator_of_notMem ha,abs_zero,le_refl]


set_option maxHeartbeats 1200000 in
/-- Actual signed insertion Green functions satisfy the near-window AL estimate.
The reward may couple both lengths; it only has to be measurable in slope. -/
theorem krInsertion_signed_near (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ cS KS : ℝ, 0 < cS ∧ 0 < KS ∧
    ∀ {K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
      {S : Set ℝ} (_hS : MeasurableSet S) (_hne : S.Nonempty)
      (_hSI : S ⊆ Ioo (1/2 : ℝ) 2)
      (_H : ∀ a ∈ S, KrBand D θ vlo vhi K L ν f w A a 1 a)
      (_hAw : A ≤ w) (up : Bool) {P : ℕ} (_hP : 12 ≤ P) (_hPw : (P : ℝ) ≤ w/8)
      {R : ℝ} (_hR0 : 0 ≤ R) (_hRw : R ≤ w/8)
      {ε : ℝ} (_hε0 : 0 ≤ ε) (_hε : ε ≤ krEps D vlo vhi)
      {v : (ℕ × ℕ) → ℝ → ℝ} (_hv : ∀ q, Measurable (v q))
      (_hvb : ∀ q a, a ∈ S → |v q a| ≤
        Real.exp (ε*(q.1 : ℝ)/w^2)*Real.exp (ε*(q.2 : ℝ)/w^2)),
    let VB := 2*Real.exp (3*ε)*krCV D K L vlo vhi*(1+A)*(Real.sqrt w/krFourthRoot P+1)
    let RB := 2*Real.exp (5*ε)*krCR D K L vlo vhi*(1+A)*((1+kBVClassRho D vlo vhi)/2)^(P/3-1)
    let BB := Real.exp (3*ε)*((krCG D K L vlo vhi+4*krC₄ D K L/krKappa D vlo vhi)*(1+A)*(1+Real.log w))
    let OB := Real.exp (3*ε)*((krCO D K L vlo vhi+4*krC₃ D K L/krKappa D vlo vhi)*(1+A)*w)
    let PB := Real.exp (3*ε)*((krCP D θ K L vlo vhi+12*krC₂ D K L/krKappa D vlo vhi)*(1+A)^2/Real.sqrt w)
    let ST := ((P+1 : ℕ) : ℝ)^2*Real.exp (2*ε*(P : ℝ)/w^2)*(KS*Real.exp (-cS*w))
    KernelApproxLip R (volume.real S*(4*VB*BB+8*D*VB)+4*(2*PB+8*RB))
      (volume.real S*(8*RB*OB+8*RB+ST))
      (fun x => ∫ a in S, ∑' q : ℕ × ℕ, v q a*
        kernelMarkedFullDens (Icc 0 w) ν f 1 a x q.1 q.2
          (if up then 0 else w) (if up then w else 0)) := by
  classical
  obtain ⟨cS,KS,hcS,hKS,hfull⟩ := krInsertion_signed_full D θ vlo vhi hD hθ hvlo hvhi
  refine ⟨cS,KS,hcS,hKS,?_⟩
  intro K L w A ν f S hS hne hSI H hAw up P hP hPw R hR0 hRw ε hε0 hε v hv hvb
  obtain ⟨a₀,ha₀⟩ := hne
  let a : ℝ → ℝ := fun s => if s ∈ S then s else a₀
  have ha : Measurable a := measurable_id.piecewise hS measurable_const
  have haS (s : ℝ) : a s ∈ S := by
    by_cases hs : s ∈ S
    · simpa only [a,if_pos hs] using hs
    · simpa only [a,if_neg hs] using ha₀
  have ha0 (s : ℝ) : 0 ≤ a s := by linarith [(hSI (haS s)).1]
  obtain ⟨_,G,E,j,hG,hE,hj,hs,hL,hErr,hJump,hSup⟩ := hfull ν ha ha0
    (fun s => H (a s) (haS s)) hAw up hP hPw hRw hε0 hε
    (fun q => (hv q).comp ha) (fun q s => hvb q (a s) (haS s))
  apply krInsertion_near_integral_of_split hS hSI hG hE hj
    ((norm_nonneg (E a₀ 0)).trans (hErr a₀ 0 ⟨le_rfl,hR0⟩))
    ((norm_nonneg (j a₀)).trans (hJump a₀))
    ((norm_nonneg (G a₀ 0)).trans (hSup a₀ 0))
  · intro s hsS x hx hax
    have has : a s = s := if_pos hsS
    simpa only [has,Function.comp_apply] using hs s x hx (by rw [has]; exact hax)
  · exact fun s _ x y => hL s x y
  · exact fun s _ x hx => hErr s x hx
  · exact fun s _ => hJump s
  · exact fun s _ x => hSup s x

end
end PGM
