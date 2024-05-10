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

def total_width (els : List Element) : ℚ⁺ :=
  els.map (·.box.size.w) |>.sum

lemma lt_commutes {a b c : ℚ} (_ : a + b ≤ c) : b + a ≤ c := by
  linarith

section WrapLines

variable (width : ℚ⁺) (el : Element) (els : List Element) (cur : List Element) (line : List Element) (x : ℚ⁺)

lemma wrap_lines_greedy.aux.preserves_width
  (h_cur_bounded : total_width cur ≤ width)
  : ∀ line ∈ wrap_lines_greedy.aux width els cur (total_width cur), total_width line ≤ width
  := by
  intro line h_in
  induction els generalizing cur
  all_goals simp [wrap_lines_greedy.aux] at h_in
  case nil => rw [h_in]; assumption
  case cons el els ih =>
    apply Or.elim (Classical.em (width < total_width cur + el.box.size.w))
    case left =>
      intro h; simp [h] at h_in
      cases h_in
      case inl h' => rw [h']; assumption
      case inr h' => apply ih []; simp [total_width]; assumption
    case right =>
      intro h; simp [h] at h_in
      apply ih (el :: cur)
      simp [total_width] at *; rw [←total_width] at *
      apply lt_commutes h
      simp [total_width] at *; rw [←total_width] at *
      rw [(_ : total_width cur + el.box.size.w = el.box.size.w + total_width cur)] at h_in
      assumption
      apply add_comm

theorem wrap_lines_greedy.preserves_width
  : ∀ line ∈ wrap_lines_greedy els width, (line.map (·.box.size.w)).sum ≤ width
  := by
  intro line h_in
  apply wrap_lines_greedy.aux.preserves_width width els []
  simp [total_width]
  apply h_in


theorem wrap_lines_greedy.aux.mem
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
        have := ih [] 0 h
        simp at this
        apply Or.intro_left _ (List.mem_cons_of_mem head this)
    case inr h =>
      simp [h] at h_line_in
      cases ih (head :: cur) (x + head.box.size.w) h_line_in
      case inl h =>
        apply Or.intro_left _ (List.mem_cons_of_mem head h)
      case inr h =>
        cases List.mem_cons.mp h
        case inl h =>
          rw [h]
          apply Or.intro_left _ (List.mem_cons_self head tail)
        case inr h =>
          apply Or.intro_right _ h

theorem wrap_lines_greedy.mem
  (h_line_in : line ∈ wrap_lines_greedy els width)
  (h_el_in : el ∈ line)
  : el ∈ els
  := by
  simp [wrap_lines_greedy] at h_line_in
  have := wrap_lines_greedy.aux.mem width el els [] line 0 h_line_in h_el_in
  simp at this
  assumption

theorem wrap_lines_greedy.preserves_disjoint
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

variable (f : AccUpdate)
  (dim : Fin 2)
  (els : List Element)
  (p : Pos)
  (dim : Fin 2)
  (h_f_mono : layout_monotone f dim)

def layout_monotone : Prop :=
  ∀ (el : Element) (p : Pos),
  (el.setPos p).box.hi.nth dim < (f el p).nth dim

theorem layout_list_acc.aux_monotone
  : ∀ el ∈ aux f els p, p.nth dim ≤ el.box.lo.nth dim
  := by
  intro el h_in
  induction els generalizing p
  case nil => simp [aux] at h_in
  case cons el els ih =>
    simp [aux] at h_in
    cases h_in
    case inl h => simp [Element.set_pos_changes_pos, h]
    case inr h =>
      apply LE.le.trans _ (ih (f el p) h)
      apply LE.le.trans _ (le_of_lt (h_f_mono el p))
      simp [Element.set_pos_changes_pos]
      cases dim.two_eq_or
      case inl h' => simp [h', Prod.nth]
      case inr h' => simp [h' ,Prod.nth]

theorem layout_list_acc.aux_disjoint
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
      have h_f_mono' := h_f_mono el p
      have h_aux_mono := layout_list_acc.aux_monotone f els (f el p) dim h_f_mono
      cases dim.two_eq_or
      all_goals {
        simp [Prod.nth, Element.set_pos_changes_pos, *] at *
        apply lt_of_lt_of_le h_f_mono'
        apply h_aux_mono
        assumption
      }
    case right =>
      exact ih (f el p).1 (f el p).2

theorem layout_list_acc.aux_inner_disjoint
  (h_disjoint : ∀ el ∈ els, el.inner_disjoint)
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
        exact ih (f el p) (forall_prop_of_tail h_disjoint) el' h_in

theorem layout_list_acc.disjoint
  (h_disjoint : ∀ el ∈ els, el.inner_disjoint)
  : (layout_list_acc f els).inner_disjoint
  := by
  simp [Element.inner_disjoint, layout_list_acc]
  apply And.intro
  case left => exact layout_list_acc.aux_disjoint f els 0 dim h_f_mono
  case right => exact layout_list_acc.aux_inner_disjoint f els 0 h_disjoint

theorem left_align.monotone : layout_monotone left_align 0 := by
  simp [layout_monotone, left_align, Prod.nth, Element.set_pos_changes_pos, Prod.nth_vec]
  intro el x
  linarith

theorem vert_stack.monotone : layout_monotone vert_stack 1 := by
  simp [layout_monotone, vert_stack, Prod.nth, Element.set_pos_changes_pos, Prod.nth_vec]
  intro el y
  linarith

def layout_left_align.disjoint :=
  layout_list_acc.disjoint left_align els 0 left_align.monotone

def layout_vert_stack.disjoint :=
  layout_list_acc.disjoint vert_stack els 1 vert_stack.monotone

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

theorem InlineLayoutCtx.collect_inline_seq_disjoint
  : ∀ el ∈ icx.collect_inline_seq is, el.inner_disjoint
  := by
  intro el h_in
  simp [collect_inline_seq] at h_in
  obtain ⟨i, h⟩ := h_in
  exact icx.collect_inline_disjoint i el h.right

theorem InlineLayoutCtx.layout_lines_disjoint
  : (icx.layout_lines is).inner_disjoint
  := by
  simp [layout_lines]
  apply layout_vert_stack.disjoint
  intro el h_in
  simp at h_in
  obtain ⟨line, h⟩ := h_in
  rw [←h.right]
  apply layout_left_align.disjoint
  intro el h_in
  apply wrap_lines_greedy.preserves_disjoint icx.blockWidth (icx.collect_inline_seq is) _ line h.left
  assumption
  apply icx.collect_inline_seq_disjoint

end InlineLayoutDisjoint

section GlobalLayoutDisjoint

variable (gcx : GlobalLayoutCtx) (p : Para) (b : Block) (bs : List Block) (d : Document)
  (shape : TextShaper)

theorem GlobalLayoutCtx.layout_para_disjoint
  : (gcx.layout_para p).inner_disjoint
  := by
  unfold layout_para; lift_lets; intro icx
  apply icx.layout_lines_disjoint

theorem GlobalLayoutCtx.layout_block_disjoint
  : (gcx.layout_block b).inner_disjoint
  := by
  cases b
  case para => apply gcx.layout_para_disjoint

theorem GlobalLayoutCtx.layout_block_seq_disjoint
  : (gcx.layout_block_seq bs).inner_disjoint
  := by
  simp [layout_block_seq]
  apply layout_vert_stack.disjoint
  intro el h_in
  simp at h_in; obtain ⟨el, h⟩ := h_in
  rw [←h.right]
  apply gcx.layout_block_disjoint

theorem GlobalLayoutCtx.layout_document_disjoint
  : (gcx.layout_document d).inner_disjoint
  := by
  simp [layout_document]
  apply gcx.layout_block_seq_disjoint

theorem Document.layout_disjoint
  : (d.layout shape).inner_disjoint
  := by
  unfold layout; lift_lets; intro gcx
  apply gcx.layout_document_disjoint

end GlobalLayoutDisjoint
