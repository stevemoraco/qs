namespace PNPLeeSublemma3EdgeFirewall

/-- Set-theoretic firewall corresponding to the source's Sublemma-3 bookkeeping:
an edge explicitly chosen outside the critical walk cannot simultaneously be an
edge of that walk. -/
theorem outside_walk_not_inside
    {Edge : Type}
    (R : Edge → Prop)
    (es : Edge)
    (hout : ¬ R es) :
    ¬ R es := by
  exact hout

/-- A common-origin argument cannot be obtained merely from membership in one
walk and nonmembership in another.  This tiny model supplies all those stated
facts while the two edge origins differ. -/
theorem membership_data_do_not_force_common_origin :
    ∃ (Edge Vertex : Type)
      (R W : Edge → Prop)
      (init : Edge → Vertex)
      (er es : Edge),
      R er ∧ W es ∧ ¬ R es ∧ init er ≠ init es := by
  refine ⟨Bool, Bool, (fun e => e = false), (fun _ => True), (fun e => e), false, true, ?_⟩
  decide

/-- Pure logical form of the missing implication: without an additional premise,
`es ∈ W` and `es ∉ R` do not imply that `es` has the same origin as an edge
`er ∈ R`. -/
theorem no_common_origin_from_walk_difference :
    ¬ (∀ (Edge Vertex : Type)
        (R W : Edge → Prop)
        (init : Edge → Vertex)
        (er es : Edge),
        R er → W es → ¬ R es → init er = init es) := by
  intro h
  obtain ⟨Edge, Vertex, R, W, init, er, es, hR, hW, hout, hne⟩ :=
    membership_data_do_not_force_common_origin
  exact hne (h Edge Vertex R W init er es hR hW hout)

#print axioms outside_walk_not_inside
#print axioms membership_data_do_not_force_common_origin
#print axioms no_common_origin_from_walk_difference

end PNPLeeSublemma3EdgeFirewall
