import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LiftLets
import Mathlib.Tactic.FinCases

import «LayoutTypes».Document
import «LayoutTypes».DocumentProofs
import «LayoutTypes».Space
import «LayoutTypes».SpaceProofs
import «LayoutTypes».Layout
import «LayoutTypes».UtilsProofs

section WrapLines

-- TODO: this proof is false for lines greater than the width.
-- need to handle cutting lines?

-- def total_width (els : List Element) : ℚ⁺ :=
--   els.map (·.box.size.w) |>.sum

-- lemma lt_commutes {a b c : ℚ} (_ : a + b ≤ c) : b + a ≤ c := by
--   linarith

-- lemma wrap_lines_greedy.aux.preserves_width
--   (h_cur_bounded : total_width cur ≤ width)
--   (h_el_bounded : ∀ el ∈ els, el.box.size.w ≤ width)
--   : ∀ line ∈ wrap_lines_greedy.aux width els cur (total_width cur), total_width line ≤ width
--   := by
--   intro line h_in
--   induction els generalizing cur
--   all_goals simp [wrap_lines_greedy.aux] at h_in
--   case nil => rw [h_in]; assumption
--   case cons el els ih =>
--     apply Or.elim (Classical.em (width < total_width cur + el.box.size.w))
--     case left =>
--       intro h; simp [h] at h_in
--       cases h_in
--       case inl h' => rw [h']; assumption
--       case inr h' =>
--         apply ih [el]
--         simp [total_width]
--     case right =>
--       intro h; simp [h] at h_in
--       apply ih (el :: cur)
--       simp [total_width] at *; rw [←total_width] at *
--       apply lt_commutes h
--       simp [total_width] at *; rw [←total_width] at *
--       rw [(_ : total_width cur + el.box.size.w = el.box.size.w + total_width cur)] at h_in
--       assumption
--       apply add_comm

-- theorem wrap_lines_greedy.preserves_width
--   : ∀ line ∈ wrap_lines_greedy els width, (line.map (·.box.size.w)).sum ≤ width
--   := by
--   intro line h_in
--   apply wrap_lines_greedy.aux.preserves_width width els []
--   simp [total_width]
--   apply h_in

theorem wrapLinesGreedy.aux.mem
  (width : ℚ⁺) (el : Element) (els : List Element) (cur : List Element) (line : List Element) (x : ℚ⁺)
  (h_line_in : line ∈ wrapLinesGreedy.aux width els cur x)
  (h_el_in : el ∈ line)
  : el ∈ els ∨ el ∈ cur
  := by
  induction els generalizing cur x
  all_goals simp [aux] at h_line_in
  case nil =>
    rw [←h_line_in]
    apply Or.intro_right _ h_el_in
  case cons head tail ih =>
    cases Classical.em (width < x + head.box.size.w)
    case inl h =>
      simp [h] at h_line_in
      cases h_line_in
      case inl h =>
        rw [←h]
        apply Or.intro_right _ h_el_in
      case inr h =>
        have := ih [head] head.box.size.w h
        simp at this
        apply Or.intro_left
        simp [Or.comm.mp this]
    case inr h =>
      simp [h] at h_line_in
      cases ih (cur ++ [head]) (x + head.box.size.w) h_line_in
      case inl h =>
        apply Or.intro_left _ (List.mem_cons_of_mem head h)
      case inr h =>
        simp at *
        cases h
        all_goals simp [*]

theorem wrapLinesGreedy.mem
  (width : ℚ⁺) (el : Element) (els : List Element) (line : List Element)
  (h_line_in : line ∈ wrapLinesGreedy els width)
  (h_el_in : el ∈ line)
  : el ∈ els
  := by
  simp [wrapLinesGreedy] at h_line_in
  have := wrapLinesGreedy.aux.mem width el els [] line 0 h_line_in h_el_in
  simp at this
  assumption

theorem wrapLinesGreedy.preserves_disjoint
  (width : ℚ⁺) (els : List Element)
  (h_els_disjoint : ∀ el ∈ els, el.inner_disjoint)
  : ∀ line ∈ wrapLinesGreedy els width, ∀ el ∈ line, el.inner_disjoint
  := by
  intro line h_line_in el h_el_in
  apply h_els_disjoint
  exact wrapLinesGreedy.mem width el els line h_line_in h_el_in

end WrapLines

section LayoutMonotone

def valid_adjacent_fluid_els (el1 el2 : FluidEl) :=
  0 ≤ el1.nextMargin + el2.prevMargin

def valid_fluid_els (els : List FluidEl) :=
  List.Chain' valid_adjacent_fluid_els els

def valid_fluid_els.ge_zero (els : List FluidEl)
  (h : ∀ el ∈ els, 0 ≤ el.prevMargin ∧ 0 ≤ el.nextMargin)
  : valid_fluid_els els := by
  induction els
  case nil => trivial
  case cons el els ih =>
    have ih' := ih (forall_prop_of_tail h)
    apply List.Chain'.cons' ih'
    intro el' h_in
    cases els
    case nil => simp at h_in
    case cons el'' els =>
      simp at h_in
      rw [←h_in]
      let ⟨_, h_el⟩ := h el (by simp)
      let ⟨h_el'', _⟩ := h el'' (by simp)
      unfold valid_adjacent_fluid_els
      linarith

lemma layoutFluid.aux_non_emp {dim : Fin 2} {els : List FluidEl} {p : Pos} {el' : Element}
  (h : el' ∈ aux dim els p) : els ≠ [] := by
  induction els
  · contradiction
  · simp

-- def FluidEl.layoutFormula (el : FluidEl) (dim : Fin 2)  :=
--   el.prevMargin.toVec dim + el.el.box.size.nthVec dim + (1 + el.nextMargin).toVec dim

theorem layoutFluid.aux_monotone (dim : Fin 2) (els : List FluidEl) (p : Pos)
  (h_valid : valid_fluid_els els)
  : ∀ h_el' : el' ∈ aux dim els p,
    p.nth dim + (els.head (aux_non_emp h_el')).prevMargin ≤ el'.box.lo.nth dim
  := by
  intro h_el'
  induction' els using List.suffix_induction generalizing p
  all_goals simp [aux] at h_el'
  case cons el1 els ih h_el' =>
  cases els
  all_goals simp [aux] at h_el'
  case nil =>
    simp [h_el', Element.set_pos_changes_pos, Prod.nth_add_eq_toVec]
  case cons el2 els h_el' =>
    have h_valid := List.chain'_cons.mp h_valid
    cases h_el'
    case inl h_el' =>
      simp [h_el', Element.set_pos_changes_pos, Prod.nth_add_eq_toVec]
    case inr h_el' =>
    cases h_el'
    case inl h_el' =>
      simp [h_el', Element.set_pos_changes_pos]
      rw [add_assoc, add_assoc, add_assoc, add_comm, ←add_assoc, add_comm];
      rw [Prod.nth_dist ((p + el1.prevMargin.toVec dim)) _ dim];
      rw [←Prod.nth_add_eq_toVec]
      rw [le_add_iff_nonneg_right (p.nth dim + el1.prevMargin)]

      cases dim.two_eq_or
      case inl h_dim =>
        simp [h_dim, Rat.toVec, Prod.nthVec, Prod.nth]
        rw [add_assoc]; apply Rat.add_nonneg el1.el.box.size.1.prop
        apply Rat.add_nonneg (by trivial)
        exact h_valid.left
      case inr h_dim =>
        simp [h_dim, Rat.toVec, Prod.nthVec, Prod.nth]
        rw [add_assoc]; apply Rat.add_nonneg el1.el.box.size.2.prop
        apply Rat.add_nonneg (by trivial)
        exact h_valid.left

    case inr h_el' =>
      have h_suffix : els.IsStrictSuffix (el1 :: el2 :: els) := by
        existsi [el1, el2]
        constructor <;> simp

      cases els with
      | nil => trivial
      | cons el3 els =>
        -- TODO: rewrite this using layoutFormula
        have := ih (el3 :: els) h_suffix
          (p + el1.prevMargin.toVec dim
            + el1.el.box.size.nthVec dim + (1 + el1.nextMargin).toVec dim + el2.prevMargin.toVec dim
            + el2.el.box.size.nthVec dim + (1 + el2.nextMargin).toVec dim)
          (List.Chain'.tail h_valid.right)
          h_el'
        apply le_trans _ this; simp

        have h_el1_el2 := h_valid.left
        have := List.chain'_cons.mp h_valid.right
        have h_el2_el3 := this.left
        simp [valid_adjacent_fluid_els] at h_el1_el2 h_el2_el3

        -- TODO: try and abstract out this logic
        cases dim.two_eq_or
        case inl h_dim =>
          simp [h_dim, Rat.toVec, Prod.nthVec, Prod.nth]
          rw [add_assoc, add_assoc, add_assoc, add_assoc, add_assoc]
          rw [le_add_iff_nonneg_right (p.1 + el1.prevMargin)]
          apply Rat.add_nonneg el1.el.box.size.1.prop
          rw [add_assoc]; apply Rat.add_nonneg (by trivial)
          rw [←add_assoc]; apply Rat.add_nonneg h_el1_el2
          apply Rat.add_nonneg el2.el.box.size.1.prop
          rw [add_assoc]; apply Rat.add_nonneg (by trivial)
          exact h_el2_el3
        case inr h_dim =>
          simp [h_dim, Rat.toVec, Prod.nthVec, Prod.nth]
          rw [add_assoc, add_assoc, add_assoc, add_assoc, add_assoc]
          rw [le_add_iff_nonneg_right (p.2 + el1.prevMargin)]
          apply Rat.add_nonneg el1.el.box.size.2.prop
          rw [add_assoc]; apply Rat.add_nonneg (by trivial)
          rw [←add_assoc]; apply Rat.add_nonneg h_el1_el2
          apply Rat.add_nonneg el2.el.box.size.2.prop
          rw [add_assoc]; apply Rat.add_nonneg (by trivial)
          exact h_el2_el3

theorem layoutFluid.aux_disjoint (dim : Fin 2) (els : List FluidEl) (p : Pos)
  (h_valid : valid_fluid_els els)
  : elements_disjoint (layoutFluid.aux dim els p)
  := by
  induction els generalizing p
  all_goals simp [layoutFluid.aux, elements_disjoint] at *
  case cons el1 els ih =>
    cases els
    case nil => simp [aux]
    case cons el2 els =>
      let p' := p + el1.prevMargin.toVec dim + el1.el.box.size.nthVec dim + (1 + el1.nextMargin).toVec dim
      have ⟨h_el1_el2, h_valid_els⟩ := List.chain'_cons.mp h_valid
      constructor
      case left =>
        intro el' h_in
        simp [Element.disjoint, Element.set_pos_changes_pos]
        apply Box.disjoint_if_dim_disjoint _ _ dim
        simp
        have h_aux_mono := layoutFluid.aux_monotone dim (el2 :: els) p' (List.Chain'.tail h_valid) h_in
        suffices _ : (p + el1.prevMargin.toVec dim + el1.el.box.size).nth dim + 1 ≤ el'.box.pos.nth dim by
          linarith
        apply le_trans _ h_aux_mono
        simp [p']
        cases dim.two_eq_or
        case inl h =>
          simp [Prod.nth, Prod.nthVec, Rat.toVec, Element.set_pos_changes_pos, h] at *
          suffices _ : p.1 + el1.prevMargin + el1.el.box.size.1 + 1 ≤
            (p.1 + el1.prevMargin + el1.el.box.size.1 + 1) + (el1.nextMargin + el2.prevMargin)
            by linarith
          have := @le_add_iff_nonneg_right _ _ _ _ _ (p.1 + el1.prevMargin + el1.el.box.size.1 + 1) (el1.nextMargin + el2.prevMargin)
          exact this.mpr h_el1_el2
        case inr h =>
          simp [Prod.nth, Prod.nthVec, Rat.toVec, Element.set_pos_changes_pos, h] at *
          suffices _ : p.2 + el1.prevMargin + el1.el.box.size.2 + 1 ≤
            (p.2 + el1.prevMargin + el1.el.box.size.2 + 1) + (el1.nextMargin + el2.prevMargin)
            by linarith
          have := @le_add_iff_nonneg_right _ _ _ _ _ (p.2 + el1.prevMargin + el1.el.box.size.2 + 1) (el1.nextMargin + el2.prevMargin)
          exact this.mpr h_el1_el2
      case right =>
        exact ih p'.1 p'.2 h_valid_els

theorem layoutFluid.aux_inner_disjoint (dim : Fin 2) (els : List FluidEl) (p : Pos)
  (h_valid : valid_fluid_els els) (h_disjoint : ∀ el ∈ els, el.el.inner_disjoint)
  : ∀ el ∈ layoutFluid.aux dim els p, el.inner_disjoint
  := by
  induction els generalizing p
  case nil => simp [aux]
  case cons el els ih =>
      simp [aux]
      apply And.intro
      case left =>
        have := els.mem_cons_self el
        apply Element.set_pos_preserves_inner_disjoint _ _ (h_disjoint el (els.mem_cons_self el))
      case right =>
        intro el' h_in
        exact ih
          (p + el.prevMargin.toVec dim + el.el.box.size.nthVec dim + (1 + el.nextMargin).toVec dim)
          h_valid.tail (forall_prop_of_tail h_disjoint) el' h_in

theorem layoutFluid.disjoint (dim : Fin 2) (els : List FluidEl)
  (h_valid : valid_fluid_els els) (h_disjoint : ∀ el ∈ els, el.el.inner_disjoint)
  : (layoutFluid dim els).inner_disjoint
  := by
  simp [Element.inner_disjoint, layoutFluid]
  apply And.intro
  case left => exact layoutFluid.aux_disjoint dim els 0 h_valid
  case right => exact layoutFluid.aux_inner_disjoint dim els 0 h_valid h_disjoint

def layoutFluidX.disjoint := layoutFluid.disjoint 0
def layoutFluidY.disjoint := layoutFluid.disjoint 1

-- theorem layout_left_align.aux.preserves_height
--   (els : List Element)
--   (p : Pos)
--   (height : ℚ⁺)
--   (h_bounded : ∀ el ∈ els, el.box.size.h ≤ height)
--   : ∀ el ∈ layout_list_acc.aux leftAlign els p, el.pos.y = p.y ∧ el.box.size.h ≤ height
--   := by
--   induction els generalizing p
--   case nil => intro el h_in; have := height.prop; trivial
--   case cons el els ih =>
--     simp [
--       layout_list_acc.aux, Element.box, Frame.box, boxCover, Box.offset,
--       List.attach, List.attachWith, List.map_pmap,
--       Element.set_pos_changes_pos, Element.pos
--     ] at ih ⊢
--     let p' := leftAlign el p
--     have ih := ih p'.x p'.y (forall_prop_of_tail h_bounded)
--     apply And.intro
--     case left => simp [h_bounded]
--     case right =>
--       have : p.2 = p'.2 := by simp [p', leftAlign, Prod.nth_vec]
--       rw [this]
--       assumption

-- theorem layout_left_align.preserves_height
--   (els : List Element)
--   (height : ℚ⁺)
--   (h_bounded : ∀ el ∈ els, el.box.size.h ≤ height)
--   : ((layoutLeftAlign els).box.size.h : ℚ) ≤ height
--   := by
--   simp [layoutLeftAlign, fluidLayout]
--   cases els
--   case nil => have := height.prop; trivial
--   case cons el' els =>
--     simp [
--       Element.box, Frame.box, List.attach, List.attachWith, List.map_pmap, Box.offset,
--       Element.set_pos_changes_pos
--     ]
--     let els_layout := layout_list_acc.aux left_align els (left_align el' 0)
--     have h_aux_preserves := layout_left_align.aux.preserves_height els (left_align el' 0) height (forall_prop_of_tail h_bounded)
--     have : layout_list_acc.aux left_align els (left_align el' 0) = els_layout := rfl
--     rw [this] at h_aux_preserves ⊢

--     let b : Box := { pos := 0, size := el'.box.size }
--     let bs := (els_layout.map (·.box))

--     have := boxCover.size_eq_extrema_diff b bs
--     have h_extrema := (Prod.eq_iff_fst_eq_snd_eq.mp this).right
--     simp at h_extrema
--     rw [h_extrema]

--     have h_all_upper : ∀ b2 ∈ b :: bs, b2.hi.y ≤ height := by
--       intro b2 h_in
--       cases h_in
--       case head =>
--         have := h_bounded el' (List.mem_cons_self el' els)
--         simp [this]
--         trivial
--       case tail h_in =>
--         obtain ⟨el, ⟨h_in, h_eq⟩⟩ := List.mem_map.mp h_in
--         rw [←h_eq]
--         have := (h_aux_preserves el h_in)
--         simp [left_align, Prod.nth_vec, Element.pos] at this ⊢
--         exact add_le_of_nonpos_of_le (by simp [this.left]) this.right

--     have h_all_lower : ∀ b2 ∈ b :: bs, 0 ≤ b2.pos.y := by
--       intro b2 h_in
--       cases h_in
--       case head => simp
--       case tail h_in =>
--         obtain ⟨el, ⟨h_in, h_eq⟩⟩ := List.mem_map.mp h_in
--         rw [←h_eq]
--         have := (h_aux_preserves el h_in)
--         simp [left_align, Prod.nth_vec, Element.pos] at this ⊢
--         simp [this.left]

--     have h_max_bound := boxMax.bounded b bs 1 height h_all_upper
--     have h_min_bound := boxMin.bounded b bs 1 0 h_all_lower
--     simp [Prod.nth] at h_max_bound h_min_bound
--     linarith


-- theorem vert_stack.monotone (els : List Element) : layout_monotone block_stack 1 els := by
--   simp [layout_monotone, block_stack, Prod.nth, Element.set_pos_changes_pos, Prod.nth_vec]
--   intro el _ y
--   linarith

-- def layout_vert_stack.disjoint (els : List Element) :=
--   layout_list_acc.disjoint block_stack 1 els (vert_stack.monotone els)

-- theorem vert_fixed.monotone (els : List Element) (y : ℚ)
--   (h_height_bounded : ∀ el ∈ els, el.box.size.h < y)
--   : layout_monotone (vertFixed y) 1 els := by
--   simp [layout_monotone, vertFixed, Prod.nth, Element.set_pos_changes_pos, Prod.nth_vec]
--   intro el h_in y'
--   have := h_height_bounded el h_in
--   linarith

-- def layout_vert_fixed.disjoint (els : List Element) (y : ℚ) (h_height_bounded : ∀ el ∈ els, el.box.size.h < y) :=
--   layout_list_acc.disjoint (vert_fixed y) 1 els (vert_fixed.monotone els y h_height_bounded)

end LayoutMonotone


section InlineLayoutDisjoint

variable (icx : InlineLayoutCtx) (is : List Inline) (i : Inline)

theorem InlineLayoutCtx.collectInline_disjoint
  : ∀ el ∈ icx.collectInline i, el.inner_disjoint
  := by
  intro el h_in
  induction i generalizing icx
  case text =>
    simp [collectInline] at h_in
    rw [h_in]
    simp [Element.inner_disjoint]
  case bold is ih =>
    simp [collectInline, collectInlineSeq] at h_in
    obtain ⟨i, h⟩ := h_in
    exact ih i h.left {icx with bold := true} h.right

theorem InlineLayoutCtx.collectInline_height_bounded
  : ∀ el ∈ icx.collectInline i, el.box.size.h ≤ icx.fontSize
  := by
  intro el h_in
  induction i generalizing icx
  case text s =>
    simp [collectInline] at h_in
    rw [h_in]
    simp [Element.box]
    let shaped := icx.gcx.shaper icx.fontSize s
    have : icx.gcx.shaper icx.fontSize s = shaped := rfl
    rw [this]
    have := shaped.height_bounded
    apply this
  case bold is ih =>
    simp [collectInline, collectInlineSeq] at h_in
    obtain ⟨i, h⟩ := h_in
    exact ih i h.left {icx with bold := true} h.right

theorem InlineLayoutCtx.collectInlineSeq_disjoint
  : ∀ el ∈ icx.collectInlineSeq is, el.inner_disjoint
  := by
  intro el h_in
  simp [collectInlineSeq] at h_in
  obtain ⟨i, h⟩ := h_in
  exact icx.collectInline_disjoint i el h.right

theorem InlineLayoutCtx.collectInlineSeq_height_bounded
  : ∀ el ∈ icx.collectInlineSeq is, el.box.size.h ≤ icx.fontSize
  := by
  intro el h_in
  simp [collectInlineSeq] at h_in
  obtain ⟨i, h⟩ := h_in
  exact icx.collectInline_height_bounded i el h.right

theorem InlineLayoutCtx.layoutLines_disjoint
  (h_lineHeight_ge_zero : 0 ≤ icx.lineHeight)
  : (icx.layoutLines is).inner_disjoint
  := by
  simp [layoutLines]
  apply layoutFluidY.disjoint
  case h_disjoint =>
    intro el h_in
    simp at h_in
    obtain ⟨line, h⟩ := h_in
    rw [←h.right]
    apply layoutFluidX.disjoint
    case intro.h_valid =>
      apply valid_fluid_els.ge_zero
      intro el h_in
      simp at h_in; obtain ⟨el', ⟨_, h_eq⟩⟩ := h_in
      rw [←h_eq]; simp
    case intro.h_disjoint =>
      intro el h_in
      apply wrapLinesGreedy.preserves_disjoint icx.blockWidth (icx.collectInlineSeq is) _ line h.left
      obtain ⟨el', ⟨h_in, h_eq⟩⟩ := List.mem_map.mp h_in
      rw [←h_eq]; simp; assumption
      apply icx.collectInlineSeq_disjoint
  case h_valid =>
    apply valid_fluid_els.ge_zero
    intro el h_in
    simp at h_in
    obtain ⟨line, ⟨_, h_eq⟩⟩ := h_in
    rw [←h_eq]; simp
    exact h_lineHeight_ge_zero

end InlineLayoutDisjoint

section GlobalLayoutDisjoint

theorem GlobalLayoutCtx.layoutPara_disjoint (gcx : GlobalLayoutCtx) (p : Para)
  (h_wf : p.wf)
  : (gcx.layoutPara p).inner_disjoint
  := by
  unfold layoutPara; lift_lets; intro icx
  apply icx.layoutLines_disjoint _ h_wf

theorem GlobalLayoutCtx.layoutBlock_disjoint (gcx : GlobalLayoutCtx) (bk : BlockKind)
  (h_wf : bk.wf)
  : (gcx.layoutBlock bk).inner_disjoint
  := by
  cases bk
  case para p => exact gcx.layoutPara_disjoint p h_wf

theorem GlobalLayoutCtx.layoutBlockSeq_disjoint (gcx : GlobalLayoutCtx) (bs : List Block)
  (h_wf : block_seq_wf bs)
  : (gcx.layoutBlockSeq bs).inner_disjoint
  := by
  simp [layoutBlockSeq]
  apply layoutFluidY.disjoint
  case h_disjoint =>
    intro el h_in
    simp at h_in; obtain ⟨el, h⟩ := h_in
    rw [←h.right]
    apply gcx.layoutBlock_disjoint _ (h_wf.right el h.left)
  case h_valid =>
    have := h_wf.left
    apply (List.chain'_map _).mpr
    apply List.Chain'.imp _ h_wf.left
    intro b1 b2 h_ge
    simp [valid_adjacent_fluid_els]
    exact h_ge

theorem GlobalLayoutCtx.layoutDocument_disjoint (gcx : GlobalLayoutCtx) (d : Document)
  (h_wf : d.wf)
  : (gcx.layoutDocument d).inner_disjoint
  := by
  simp [layoutDocument]
  apply gcx.layoutBlockSeq_disjoint _ h_wf

theorem Document.layout_disjoint (d : Document)
  (h_wf : d.wf)
  : (d.layout shape).inner_disjoint
  := by
  unfold layout; lift_lets; intro gcx
  apply gcx.layoutDocument_disjoint _ h_wf
end GlobalLayoutDisjoint
