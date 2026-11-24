import PLAStochastic.Index.GEP.Response.OfInterfaces
import PLAStochastic.Index.GEP.Response.InfluenceDecomposition

/-!
# WP4: the joint response from its seven leaves

`jointResponse_of_leaves` composes JR §3–4 (`influenceDecomp_of_leaves`) with JR §5
(`jointResponse_of_interfaces`).  The seven leaves are the interface predicates of
`PLAStochastic/Index/GEP/Response/Defs.lean`.  Leaf `KappaBound` is proved in `PLAStochastic/Index/GEP/Response/KappaBound.lean`;
`PLAStochastic/Index/GEP/Additive/OfRemainingLeaves.lean` discharges it and the proved orbit closure.
`ScoreCalculus` is proved in `PLAStochastic/Index/GEP/Response/Score/ScoreCalculus.lean`; `PLAStochastic/Index/GEP/Additive/OfFiveLeaves.lean`
combines these results with the proved shadow defects, leaving five response
leaves open, including those using the rate (U).
-/

namespace PGM

theorem jointResponse_of_leaves (hSc : ScoreCalculus) (hC : KernelC) (hP : KernelPhi)
    (hD : DirectTerm) (hS : PointwiseSmall) (hQ : QuadResponse) (hk : KappaBound) :
    JointResponse :=
  jointResponse_of_interfaces hSc (influenceDecomp_of_leaves hC hP hD hS hQ hk)

end PGM
