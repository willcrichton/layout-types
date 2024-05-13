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

theorem wrap_lines_greedy.aux.mem
  (width : ℚ⁺) (el : Element) (els : List Element) (cur : List Element) (line : List Element) (x : ℚ⁺)
  (h_line_in : line ∈ wrap_lines_greedy.aux width els cur x)
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

theorem wrap_lines_greedy.mem
  (width : ℚ⁺) (el : Element) (els : List Element) (line : List Element)
  (h_line_in : line ∈ wrap_lines_greedy els width)
  (h_el_in : el ∈ line)
  : el ∈ els
  := by
  simp [wrap_lines_greedy] at h_line_in
  have := wrap_lines_greedy.aux.mem width el els [] line 0 h_line_in h_el_in
  simp at this
  assumption

theorem wrap_lines_greedy.preserves_disjoint
  (width : ℚ⁺) (els : List Element)
  (h_els_disjoint : ∀ el ∈ els, el.inner_disjoint)
  : ∀ line ∈ wrap_lines_greedy els width, ∀ el ∈ line, el.inner_disjoint
  := by
  intro line h_line_in el h_el_in
  apply h_els_disjoint
  exact wrap_lines_greedy.mem width el els line h_line_in h_el_in

end WrapLines

theorem set_pos_inner_disjoint (e : Element) (p : Pos) (h_disj : e.inner_disjoint)
  : (e.setPos p).inner_disjoint
  := by
  cases e
  case text t =>
    obtain ⟨box, s, style⟩ := t
    simp [Element.setPos, Text.setPos, Element.inner_disjoint]
  case frame f =>
    obtain ⟨origin, els⟩ := f
    simp [Element.setPos, Frame.setPos, Element.inner_disjoint] at *
    assumption


section LayoutMonotone

def layout_monotone (f : AccUpdate) (dim : Fin 2) (els : List Element) : Prop :=
  ∀ el ∈ els, ∀ (p : Pos), (el.setPos p).box.hi.nth dim < (f el p).nth dim

def layout_monotone.cons (el : Element) (els : List Element) (h : layout_monotone f dim (el :: els))
  : layout_monotone f dim els := by
  unfold layout_monotone at *
  exact forall_prop_of_tail h

theorem layout_list_acc.aux_monotone (f : AccUpdate) (dim : Fin 2) (els : List Element) (p : Pos)
  (h_f_mono : layout_monotone f dim els)
  : ∀ el ∈ aux f els p, p.nth dim ≤ el.box.lo.nth dim
  := by
  intro el h_in
  induction els generalizing p
  case nil => simp [aux] at h_in
  case cons el' els ih =>
    simp [aux] at h_in
    cases h_in
    case inl h => simp [Element.set_pos_changes_pos, h]
    case inr h =>
      have := ih (f el' p) (h_f_mono.cons _ els) h
      apply LE.le.trans _ this
      have := h_f_mono el' (by simp) p
      simp [Element.set_pos_changes_pos] at this
      apply LE.le.trans _ (le_of_lt this)
      cases dim.two_eq_or
      case inl h' => simp [h', Prod.nth]
      case inr h' => simp [h' ,Prod.nth]

theorem layout_list_acc.aux_disjoint (f : AccUpdate) (dim : Fin 2) (els : List Element) (p : Pos)
  (h_f_mono : layout_monotone f dim els)
  : elements_disjoint (layout_list_acc.aux f els p)
  := by
  induction els generalizing p
  all_goals simp [layout_list_acc.aux, elements_disjoint] at *
  case cons el els ih =>
    apply And.intro
    case left =>
      intro el' h_in
      simp [Element.disjoint, Element.set_pos_changes_pos]
      apply Box.disjoint_if_dim_disjoint _ _ dim
      simp
      have h_f_mono' := h_f_mono el (by simp) p
      have h_aux_mono := layout_list_acc.aux_monotone f dim els (f el p) h_f_mono.cons
      cases dim.two_eq_or
      all_goals {
        simp [Prod.nth, Element.set_pos_changes_pos, *] at *
        apply lt_of_lt_of_le h_f_mono'
        apply h_aux_mono
        assumption
      }
    case right =>
      exact ih (f el p).1 (f el p).2 h_f_mono.cons

theorem layout_list_acc.aux_inner_disjoint (f : AccUpdate) (dim : Fin 2) (els : List Element) (p : Pos)
  (h_f_mono : layout_monotone f dim els) (h_disjoint : ∀ el ∈ els, el.inner_disjoint)
  : ∀ el ∈ layout_list_acc.aux f els p, el.inner_disjoint
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
        exact ih (f el p) h_f_mono.cons (forall_prop_of_tail h_disjoint) el' h_in

theorem layout_list_acc.disjoint (f : AccUpdate) (dim : Fin 2) (els : List Element)
  (h_f_mono : layout_monotone f dim els) (h_disjoint : ∀ el ∈ els, el.inner_disjoint)
  : (layout_list_acc f els).inner_disjoint
  := by
  simp [Element.inner_disjoint, layout_list_acc]
  apply And.intro
  case left => exact layout_list_acc.aux_disjoint f dim els 0  h_f_mono
  case right => exact layout_list_acc.aux_inner_disjoint f  dim els 0 h_f_mono h_disjoint

theorem left_align.monotone (els : List Element) : layout_monotone left_align 0 els := by
  simp [layout_monotone, left_align, Prod.nth, Element.set_pos_changes_pos, Prod.nth_vec]
  intro el _ y
  linarith

def layout_left_align.disjoint (els : List Element) :=
  layout_list_acc.disjoint left_align 0 els (left_align.monotone els)

theorem layout_left_align.aux.preserves_height
  (els : List Element)
  (p : Pos)
  (height : ℚ⁺)
  (h_bounded : ∀ el ∈ els, el.box.size.h ≤ height)
  : ∀ el ∈ layout_list_acc.aux left_align els p, el.pos.y = p.y ∧ el.box.size.h ≤ height
  := by
  induction els generalizing p
  case nil => intro el h_in; have := height.prop; trivial
  case cons el els ih =>
    simp [
      layout_list_acc.aux, Element.box, Frame.box, boxCover, Box.offset,
      List.attach, List.attachWith, List.map_pmap,
      Element.set_pos_changes_pos, Element.pos
    ] at ih ⊢
    let p' := left_align el p
    have ih := ih p'.x p'.y (forall_prop_of_tail h_bounded)
    apply And.intro
    case left => simp [h_bounded]
    case right =>
      have : p.2 = p'.2 := by simp [p', left_align, Prod.nth_vec]
      rw [this]
      assumption

theorem foobar {a b : ℚ} (h : a ≤ b) : 0 + a ≤ b := by
  exact add_le_of_nonpos_of_le rfl h

theorem layout_left_align.preserves_height
  (els : List Element)
  (height : ℚ⁺)
  (h_bounded : ∀ el ∈ els, el.box.size.h ≤ height)
  : ((layout_left_align els).box.size.h : ℚ) ≤ height
  := by
  simp [layout_left_align, layout_list_acc]
  cases els
  case nil => have := height.prop; trivial
  case cons el' els =>
    simp [
      Element.box, Frame.box, List.attach, List.attachWith, List.map_pmap, Box.offset,
      Element.set_pos_changes_pos
    ]
    let els_layout := layout_list_acc.aux left_align els (left_align el' 0)
    have h_aux_preserves := layout_left_align.aux.preserves_height els (left_align el' 0) height (forall_prop_of_tail h_bounded)
    have : layout_list_acc.aux left_align els (left_align el' 0) = els_layout := rfl
    rw [this] at h_aux_preserves ⊢

    let b : Box := { pos := 0, size := el'.box.size }
    let bs := (els_layout.map (·.box))

    have := boxCover.size_eq_extrema_diff b bs
    have h_extrema := (Prod.eq_iff_fst_eq_snd_eq.mp this).right
    simp at h_extrema
    rw [h_extrema]

    have h_all_upper : ∀ b2 ∈ b :: bs, b2.hi.y ≤ height := by
      intro b2 h_in
      cases h_in
      case head =>
        have := h_bounded el' (List.mem_cons_self el' els)
        simp [this]
        trivial
      case tail h_in =>
        obtain ⟨el, ⟨h_in, h_eq⟩⟩ := List.mem_map.mp h_in
        rw [←h_eq]
        have := (h_aux_preserves el h_in)
        simp [left_align, Prod.nth_vec, Element.pos] at this ⊢
        exact add_le_of_nonpos_of_le (by simp [this.left]) this.right

    have h_all_lower : ∀ b2 ∈ b :: bs, 0 ≤ b2.pos.y := by
      intro b2 h_in
      cases h_in
      case head => simp
      case tail h_in =>
        obtain ⟨el, ⟨h_in, h_eq⟩⟩ := List.mem_map.mp h_in
        rw [←h_eq]
        have := (h_aux_preserves el h_in)
        simp [left_align, Prod.nth_vec, Element.pos] at this ⊢
        simp [this.left]

    have h_max_bound := boxMax.bounded b bs 1 height h_all_upper
    have h_min_bound := boxMin.bounded b bs 1 0 h_all_lower
    simp [Prod.nth] at h_max_bound h_min_bound
    linarith


theorem vert_stack.monotone (els : List Element) : layout_monotone vert_stack 1 els := by
  simp [layout_monotone, vert_stack, Prod.nth, Element.set_pos_changes_pos, Prod.nth_vec]
  intro el _ y
  linarith

def layout_vert_stack.disjoint (els : List Element) :=
  layout_list_acc.disjoint vert_stack 1 els (vert_stack.monotone els)

theorem vert_fixed.monotone (els : List Element) (y : ℚ)
  (h_height_bounded : ∀ el ∈ els, el.box.size.h < y)
  : layout_monotone (vert_fixed y) 1 els := by
  simp [layout_monotone, vert_fixed, Prod.nth, Element.set_pos_changes_pos, Prod.nth_vec]
  intro el h_in y'
  have := h_height_bounded el h_in
  linarith

def layout_vert_fixed.disjoint (els : List Element) (y : ℚ) (h_height_bounded : ∀ el ∈ els, el.box.size.h < y) :=
  layout_list_acc.disjoint (vert_fixed y) 1 els (vert_fixed.monotone els y h_height_bounded)

end LayoutMonotone


section InlineLayoutDisjoint

variable (icx : InlineLayoutCtx) (is : List Inline) (i : Inline)

theorem InlineLayoutCtx.collect_inline_disjoint
  : ∀ el ∈ icx.collect_inline i, el.inner_disjoint
  := by
  intro el h_in
  induction i generalizing icx
  case text =>
    simp [collect_inline] at h_in
    rw [h_in]
    simp [Element.inner_disjoint]
  case bold is ih =>
    simp [collect_inline, collect_inline_seq] at h_in
    obtain ⟨i, h⟩ := h_in
    exact ih i h.left {icx with bold := true} h.right

theorem InlineLayoutCtx.collect_inline_height_bounded
  : ∀ el ∈ icx.collect_inline i, el.box.size.h ≤ icx.fontSize
  := by
  intro el h_in
  induction i generalizing icx
  case text s =>
    simp [collect_inline] at h_in
    rw [h_in]
    simp [Element.box]
    let shaped := icx.globalCtx.shaper icx.fontSize s
    have : icx.globalCtx.shaper icx.fontSize s = shaped := rfl
    rw [this]
    have := shaped.height_bounded
    apply this
  case bold is ih =>
    simp [collect_inline, collect_inline_seq] at h_in
    obtain ⟨i, h⟩ := h_in
    exact ih i h.left {icx with bold := true} h.right

theorem InlineLayoutCtx.collect_inline_seq_disjoint
  : ∀ el ∈ icx.collect_inline_seq is, el.inner_disjoint
  := by
  intro el h_in
  simp [collect_inline_seq] at h_in
  obtain ⟨i, h⟩ := h_in
  exact icx.collect_inline_disjoint i el h.right

theorem InlineLayoutCtx.collect_inline_seq_height_bounded
  : ∀ el ∈ icx.collect_inline_seq is, el.box.size.h ≤ icx.fontSize
  := by
  intro el h_in
  simp [collect_inline_seq] at h_in
  obtain ⟨i, h⟩ := h_in
  exact icx.collect_inline_height_bounded i el h.right

theorem InlineLayoutCtx.layout_lines_disjoint
  (h_fontSize_le_lineHeight : icx.fontSize ≤ icx.lineHeight)
  : (icx.layout_lines is).inner_disjoint
  := by
  simp [layout_lines]
  apply layout_vert_fixed.disjoint
  case h_disjoint =>
    intro el h_in
    simp at h_in
    obtain ⟨line, h⟩ := h_in
    rw [←h.right]
    apply layout_left_align.disjoint
    intro el h_in
    apply wrap_lines_greedy.preserves_disjoint icx.blockWidth (icx.collect_inline_seq is) _ line h.left
    assumption
    apply icx.collect_inline_seq_disjoint
  case h_height_bounded =>
    intro el h_in
    simp at h_in
    obtain ⟨line, h⟩ := h_in
    rw [←h.right]
    suffices (layout_left_align line).box.size.h ≤ icx.lineHeight by
      have h : {a b : ℚ} → a ≤ b → a < b + 1 := by intros; linarith
      exact h this
    apply layout_left_align.preserves_height line icx.lineHeight
    intro el_layout h_in
    have h_in_seq := wrap_lines_greedy.mem icx.blockWidth el_layout (icx.collect_inline_seq is) line h.left h_in
    have := icx.collect_inline_seq_height_bounded is el_layout h_in_seq
    exact LE.le.trans this h_fontSize_le_lineHeight

end InlineLayoutDisjoint

section GlobalLayoutDisjoint

variable (gcx : GlobalLayoutCtx) (p : Para) (b : Block) (bs : List Block) (d : Document)
  (shape : TextShaper)

theorem GlobalLayoutCtx.layout_para_disjoint
  (h_wf : p.wf)
  : (gcx.layout_para p).inner_disjoint
  := by
  unfold layout_para; lift_lets; intro icx
  apply icx.layout_lines_disjoint _ h_wf

theorem GlobalLayoutCtx.layout_block_disjoint
  (h_wf : b.wf)
  : (gcx.layout_block b).inner_disjoint
  := by
  cases b
  case para =>
    simp [Block.wf] at h_wf
    apply gcx.layout_para_disjoint _ h_wf

theorem GlobalLayoutCtx.layout_block_seq_disjoint
  (h_wf : ∀ b ∈ bs, b.wf)
  : (gcx.layout_block_seq bs).inner_disjoint
  := by
  simp [layout_block_seq]
  apply layout_vert_stack.disjoint
  intro el h_in
  simp at h_in; obtain ⟨el, h⟩ := h_in
  rw [←h.right]
  apply gcx.layout_block_disjoint _ (h_wf el h.left)

theorem GlobalLayoutCtx.layout_document_disjoint
  (h_wf : d.wf)
  : (gcx.layout_document d).inner_disjoint
  := by
  simp [layout_document]
  apply gcx.layout_block_seq_disjoint _ h_wf

theorem Document.layout_disjoint
  (h_wf : d.wf)
  : (d.layout shape).inner_disjoint
  := by
  unfold layout; lift_lets; intro gcx
  apply gcx.layout_document_disjoint _ h_wf
end GlobalLayoutDisjoint
