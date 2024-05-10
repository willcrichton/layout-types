import «LayoutTypes».Space

-- structure Tcx

-- def Tcx.para (_ : Tcx) (p : Para) : Prop :=
--   (p.line_height : ℚ) ≥ p.font_size

-- def Tcx.block (Γ : Tcx) (b : Block) : Prop :=
--   match b with
--   | Block.para p => Γ.para p

-- def Tcx.blocks (Γ : Tcx) (bs : List Block) : Prop :=
--   ∀ b ∈ bs, Γ.block b

-- def Tcx.document (Γ : Tcx) (d : Document) : Prop :=
--   Γ.blocks d.blocks
