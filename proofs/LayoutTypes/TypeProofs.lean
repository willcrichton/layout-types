import «LayoutTypes».Types
import «LayoutTypes».Layout
import «LayoutTypes».LayoutProofs

theorem Tcx.wf_if_check (Γ : Tcx) (e : Expr)
  (h : Γ.check e = Ty.document)
  : ∃ d, e.toDocument = some d ∧
    d.wf
  := by
  sorry

theorem Tcx.disjoint_if_check (Γ : Tcx) (e : Expr)
  (shaper : TextShaper)
  (h : Γ.check e = Ty.document)
  : ∃ d, e.toDocument = some d ∧
    (d.layout shaper).inner_disjoint
  := by
  obtain ⟨d, h_wf⟩ := Γ.wf_if_check e h
  exists d
  exact And.intro h_wf.left (d.layout_disjoint shaper h_wf.right)
