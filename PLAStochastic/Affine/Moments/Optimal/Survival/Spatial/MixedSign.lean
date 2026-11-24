import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ExponentialIntegral
import PLAStochastic.Affine.Moments.Optimal.Survival.Image.Modes

/-! # The genuine mixed-sign spatial integral in the optimal image expansion -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- A mixed antiderivative for `(c*(u+v)-d)*exp(-h*u*v)`. -/
def imageMixedPrimitive (h c d u v : ℝ) : ℝ :=
  c/h^2*(Real.exp (-h*u*v)/u+Real.exp (-h*u*v)/v)-
    d/h*exponentialIntegralE1 (h*u*v)

def imageMixedInnerPrimitive (h c d u v : ℝ) : ℝ :=
  Real.exp (-h*u*v)*(-c*v/(h*u)-c/(h^2*u^2)-c/h+d/(h*u))

theorem hasDerivAt_imageMixedPrimitive {h u v : ℝ}
    (hh : 0<h) (hu : 0<u) (hv : 0<v) (c d : ℝ) :
    HasDerivAt (fun x => imageMixedPrimitive h c d x v)
      (imageMixedInnerPrimitive h c d u v) u := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (-h*x*v)) (-h*v*Real.exp (-h*u*v)) u := by
    convert! (((hasDerivAt_id u).const_mul (-h)).mul_const v).exp using 1
    dsimp
    ring
  have hE : HasDerivAt (fun x : ℝ => exponentialIntegralE1 (h*x*v))
      (-Real.exp (-(h*u*v))/u) u := by
    convert! (hasDerivAt_exponentialIntegralE1 (by positivity : 0<h*u*v)).comp u
      (((hasDerivAt_id u).const_mul h).mul_const v) using 1
    field_simp
  convert! (((he.div (hasDerivAt_id u) hu.ne').add (he.div_const v)).const_mul (c/h^2)).sub
    (hE.const_mul (d/h)) using 1
  dsimp only [imageMixedInnerPrimitive, id_eq]
  rw [show -(h*u*v) = -h*u*v by ring]
  field_simp
  ring

theorem hasDerivAt_imageMixedInnerPrimitive {h u : ℝ} (hh : 0<h) (hu : 0<u)
    (c d v : ℝ) :
    HasDerivAt (imageMixedInnerPrimitive h c d u)
      ((c*(u+v)-d)*Real.exp (-h*u*v)) v := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (-h*u*x))
      (-h*u*Real.exp (-h*u*v)) v := by
    convert! ((hasDerivAt_id v).const_mul (-h*u)).exp using 1
    dsimp
    ring
  have hl : HasDerivAt (fun x : ℝ => -c*x/(h*u)-c/(h^2*u^2)-c/h+d/(h*u))
      (-c/(h*u)) v := by
    convert! ((((hasDerivAt_id v).const_mul (-c)).div_const (h*u)).sub_const
      (c/(h^2*u^2)) |>.sub_const (c/h)).add_const (d/(h*u)) using 1
    ring
  convert! he.mul hl using 1
  field_simp
  ring

theorem integral_imageMixed_rectangle {h a b : ℝ} (hh : 0<h) (ha : 0<a) (hab : a≤b)
    (c d : ℝ) :
    (∫ u in a..b, ∫ v in a..b, (c*(u+v)-d)*Real.exp (-h*u*v)) =
      imageMixedPrimitive h c d b b-imageMixedPrimitive h c d a b-
        imageMixedPrimitive h c d b a+imageMixedPrimitive h c d a a := by
  have hb : 0<b := ha.trans_le hab
  have he (u : ℝ) (hu : u∈Icc a b) :
      (∫ v in a..b, (c*(u+v)-d)*Real.exp (-h*u*v)) =
        imageMixedInnerPrimitive h c d u b-imageMixedInnerPrimitive h c d u a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro v hv
      exact hasDerivAt_imageMixedInnerPrimitive hh (ha.trans_le hu.1) c d v
    · exact (by fun_prop : Continuous (fun v : ℝ => (c*(u+v)-d)*Real.exp (-h*u*v))).intervalIntegrable a b
  rw [intervalIntegral.integral_congr (fun u hu => he u (by simpa [uIcc_of_le hab] using hu))]
  have hd (u : ℝ) (hu : u∈uIcc a b) :
      HasDerivAt (fun x => imageMixedPrimitive h c d x b-imageMixedPrimitive h c d x a)
        (imageMixedInnerPrimitive h c d u b-imageMixedInnerPrimitive h c d u a) u := by
    have hu0 : 0<u := ha.trans_le ((by simpa only [uIcc_of_le hab] using hu : u∈Icc a b).1)
    exact (hasDerivAt_imageMixedPrimitive hh hu0 hb c d).sub
      (hasDerivAt_imageMixedPrimitive hh hu0 ha c d)
  have hi : IntervalIntegrable (fun u => imageMixedInnerPrimitive h c d u b-
      imageMixedInnerPrimitive h c d u a) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hu0 : 0<u := ha.trans_le ((by simpa only [uIcc_of_le hab] using hu : u∈Icc a b).1)
    have hc (v : ℝ) : ContinuousAt (fun x => imageMixedInnerPrimitive h c d x v) u := by
      unfold imageMixedInnerPrimitive
      fun_prop (disch := positivity)
    exact ((hc b).sub (hc a)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- The exact exponential-integral expression for a positive square. -/
theorem integral_imageMixed_closed {h a b : ℝ} (hh : 0<h) (ha : 0<a) (hab : a≤b)
    (c d : ℝ) :
    (∫ u in a..b, ∫ v in a..b, (c*(u+v)-d)*Real.exp (-h*u*v)) =
      2*c/h^2*(Real.exp (-h*a^2)/a-(1/a+1/b)*Real.exp (-h*a*b)+Real.exp (-h*b^2)/b)-
      d/h*(exponentialIntegralE1 (h*a^2)-2*exponentialIntegralE1 (h*a*b)+
        exponentialIntegralE1 (h*b^2)) := by
  rw [integral_imageMixed_rectangle hh ha hab]
  unfold imageMixedPrimitive
  rw [show h*b*a=h*a*b by ring,show -h*b*a= -h*a*b by ring,
    show h*a*a=h*a^2 by ring,show -h*a*a= -h*a^2 by ring,
    show h*b*b=h*b^2 by ring,show -h*b*b= -h*b^2 by ring]
  ring

/-- The manuscript's J_m, with arbitrary real positive m. -/
theorem integral_imageMixed_J {m T : ℝ} (hm : 0<m) (hT : 0<T) (c b : ℝ) :
    (∫ u in m..m+1, ∫ v in m..m+1, (c*(u+v)-b*T)*Real.exp (-(2/T)*u*v)) =
      c*T^2/2*(Real.exp (-(2/T)*m^2)/m-
        (1/m+1/(m+1))*Real.exp (-(2/T)*m*(m+1))+Real.exp (-(2/T)*(m+1)^2)/(m+1))-
      b*T^2/2*(exponentialIntegralE1 ((2/T)*m^2)-
        2*exponentialIntegralE1 ((2/T)*m*(m+1))+exponentialIntegralE1 ((2/T)*(m+1)^2)) := by
  rw [integral_imageMixed_closed (by positivity : 0<2/T) hm (by linarith)]
  field_simp

/-- The first mixed-sign image reduces to the actual J_m rectangle by two affine changes. -/
theorem integral_imageMixed_pos_neg {m T : ℝ} (c b : ℝ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      (c*(2*m+1-x+y)-b*T)*Real.exp (-((2*m+1-x+y)^2-(x+y-1)^2)/(2*T))) =
    (∫ u in m..m+1, ∫ v in m..m+1,
      (c*(u+v)-b*T)*Real.exp (-(2/T)*u*v)) := by
  let F : ℝ → ℝ → ℝ := fun u v => (c*(u+v)-b*T)*Real.exp (-(2/T)*u*v)
  have he (x y : ℝ) : (c*(2*m+1-x+y)-b*T)*
      Real.exp (-((2*m+1-x+y)^2-(x+y-1)^2)/(2*T))=F (m+1-x) (m+y) := by
    dsimp only [F]
    congr 1 <;> congr 1 <;> ring
  simp_rw [he,intervalIntegral.integral_comp_add_left]
  have hs := intervalIntegral.integral_comp_sub_left (fun u => ∫ v in m..m+1, F u v)
    (a:=0) (b:=1) (m+1)
  simpa only [add_zero,add_sub_cancel_right,sub_zero] using hs

/-- The other mixed-sign image gives the same rectangle. -/
theorem integral_imageMixed_neg_pos {m T : ℝ} (c b : ℝ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      (c*(2*m+1+x-y)-b*T)*Real.exp (-((2*m+1+x-y)^2-(x+y-1)^2)/(2*T))) =
    (∫ u in m..m+1, ∫ v in m..m+1,
      (c*(u+v)-b*T)*Real.exp (-(2/T)*u*v)) := by
  let F : ℝ → ℝ → ℝ := fun u v => (c*(u+v)-b*T)*Real.exp (-(2/T)*u*v)
  have he (x y : ℝ) : (c*(2*m+1+x-y)-b*T)*
      Real.exp (-((2*m+1+x-y)^2-(x+y-1)^2)/(2*T))=F (m+x) (m+1-y) := by
    dsimp only [F]
    congr 1 <;> congr 1 <;> ring
  simp_rw [he,intervalIntegral.integral_comp_sub_left]
  have hs := intervalIntegral.integral_comp_add_left (fun u => ∫ v in m..m+1, F u v)
    (a:=0) (b:=1) m
  simpa only [add_zero,add_sub_cancel_right,sub_zero] using hs

end BrownianAffine
