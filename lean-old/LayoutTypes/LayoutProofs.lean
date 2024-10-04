import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip
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

example (p q r : Prop)
  : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  · intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩

section WrapLines

lemma lt_commutes {a b c : ℚ} (_ : a + b ≤ c) : b + a ≤ c := by
  linarith

lemma wrapLinesGreedy.aux.width_contained
  (width : ℚ⁺) (els : List Element) (cur : List Element)
  (h_cur_bounded : total_width cur ≤ width)
  (h_el_bounded : ∀ el ∈ els, el.box.size.w ≤ width)
  : ∀ line ∈ wrapLinesGreedy.aux width els cur, total_width line ≤ width
  := by
  intro line h_in
  induction els generalizing cur
  all_goals simp [aux] at h_in
  case nil => rw [h_in]; assumption
  case cons el els ih =>
    cases Classical.em (width < total_width cur + el.box.size.w)
    case inl h_lt =>
      simp [h_lt] at h_in
      cases h_in
      case inl h' => rw [h']; assumption
      case inr h' =>
        have h_el_width : total_width [el] ≤ width := by
          simp [total_width]
          apply h_el_bounded
          simp
        exact ih [el] h_el_width (forall_prop_of_tail h_el_bounded) h'
    case inr h_nlt =>
      simp [h_nlt] at h_in
      apply ih (cur ++ [el])
      case h_cur_bounded =>
        simp [total_width] at *; rw [←total_width] at *
        assumption
      case h_el_bounded => exact (forall_prop_of_tail h_el_bounded)
      case h_in => exact h_in

theorem wrapLinesGreedy.width_contained
  (h_el_bounded : ∀ el ∈ els, el.box.size.w ≤ width)
  : ∀ line ∈ wrapLinesGreedy els width, total_width line ≤ width
  := by
  intro line h_in
  apply wrapLinesGreedy.aux.width_contained width els []
  case h_cur_bounded => simp [total_width]
  case h_el_bounded => exact h_el_bounded
  case a => simp [wrapLinesGreedy] at h_in; assumption

theorem wrapLinesGreedy.aux.mem
  (width : ℚ⁺) (el : Element) (els : List Element) (cur : List Element) (line : List Element)
  (h_line_in : line ∈ wrapLinesGreedy.aux width els cur)
  (h_el_in : el ∈ line)
  : el ∈ els ∨ el ∈ cur
  := by
  induction els generalizing cur
  all_goals simp [aux] at h_line_in
  case nil =>
    rw [←h_line_in]
    apply Or.intro_right _ h_el_in
  case cons head tail ih =>
    cases Classical.em (width < total_width cur + head.box.size.w)
    case inl h =>
      simp [h] at h_line_in
      cases h_line_in
      case inl h =>
        rw [←h]
        apply Or.intro_right _ h_el_in
      case inr h =>
        have := ih [head] h
        simp at this
        apply Or.intro_left
        simp [Or.comm.mp this]
    case inr h =>
      simp [h] at h_line_in
      cases ih (cur ++ [head]) h_line_in
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
  have := wrapLinesGreedy.aux.mem width el els [] line h_line_in h_el_in
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

lemma layoutFluidAt.non_emp {dim : Fin 2} {els : List FluidEl} {p : Pos} {el' : Element}
  (h : el' ∈ layoutFluidAt dim els p) : els ≠ [] := by
  induction els
  · contradiction
  · simp

-- def FluidEl.layoutFormula (el : FluidEl) (dim : Fin 2)  :=
--   el.prevMargin.toVec dim + el.el.box.size.nthVec dim + (1 + el.nextMargin).toVec dim

theorem layoutFluidAt.monotone (dim : Fin 2) (els : List FluidEl) (p : Pos)
  (h_valid : valid_fluid_els els)
  : ∀ h_el' : el' ∈ layoutFluidAt dim els p,
    p.nth dim + (els.head (non_emp h_el')).prevMargin ≤ el'.box.lo.nth dim
  := by
  intro h_el'
  induction' els using List.suffix_induction generalizing p
  all_goals simp [layoutFluidAt] at h_el'
  case cons el1 els ih h_el' =>
  cases els
  all_goals simp [layoutFluidAt] at h_el'
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
        apply Rat.add_nonneg el1.el.box.size.1.prop
        exact h_valid.left
      case inr h_dim =>
        simp [h_dim, Rat.toVec, Prod.nthVec, Prod.nth]
        apply Rat.add_nonneg el1.el.box.size.2.prop
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
            + el1.el.box.size.nthVec dim + el1.nextMargin.toVec dim + el2.prevMargin.toVec dim
            + el2.el.box.size.nthVec dim + el2.nextMargin.toVec dim)
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
          suffices _ : 0 ≤ el1.el.box.size.1 + el1.nextMargin + el2.prevMargin + el2.el.box.size.1 + el2.nextMargin + el3.prevMargin by
            linarith
          rw [add_assoc, add_assoc, add_assoc, add_assoc]
          apply Rat.add_nonneg el1.el.box.size.1.prop
          rw [←add_assoc]; apply Rat.add_nonneg h_el1_el2
          apply Rat.add_nonneg el2.el.box.size.1.prop
          exact h_el2_el3
        case inr h_dim =>
          simp [h_dim, Rat.toVec, Prod.nthVec, Prod.nth]
          rw [add_assoc, add_assoc, add_assoc, add_assoc, add_assoc]
          rw [le_add_iff_nonneg_right (p.2 + el1.prevMargin)]
          apply Rat.add_nonneg el1.el.box.size.2.prop
          rw [←add_assoc]; apply Rat.add_nonneg h_el1_el2
          apply Rat.add_nonneg el2.el.box.size.2.prop
          exact h_el2_el3

theorem layoutFluidAt.disjoint (dim : Fin 2) (els : List FluidEl) (p : Pos)
  (h_valid : valid_fluid_els els)
  : elements_disjoint (layoutFluidAt dim els p)
  := by
  induction els generalizing p
  all_goals simp [layoutFluidAt, elements_disjoint] at *
  case cons el1 els ih =>
    cases els
    case nil => simp [layoutFluidAt]
    case cons el2 els =>
      let p' := p + el1.prevMargin.toVec dim + el1.el.box.size.nthVec dim + el1.nextMargin.toVec dim
      have ⟨h_el1_el2, h_valid_els⟩ := List.chain'_cons.mp h_valid
      constructor
      case left =>
        intro el' h_in
        simp [Element.disjoint, Element.set_pos_changes_pos]
        apply Box.disjoint_if_dim_disjoint _ _ dim
        simp
        have h_aux_mono := layoutFluidAt.monotone dim (el2 :: els) p' (List.Chain'.tail h_valid) h_in
        suffices _ : (p + el1.prevMargin.toVec dim + el1.el.box.size).nth dim ≤ el'.box.pos.nth dim by
          linarith
        apply le_trans _ h_aux_mono
        simp [p']
        cases dim.two_eq_or
        case inl h =>
          simp [Prod.nth, Prod.nthVec, Rat.toVec, Element.set_pos_changes_pos, h] at *
          suffices _ : p.1 + el1.prevMargin + el1.el.box.size.1 ≤
            (p.1 + el1.prevMargin + el1.el.box.size.1) + (el1.nextMargin + el2.prevMargin)
            by linarith
          have := @le_add_iff_nonneg_right _ _ _ _ _ (p.1 + el1.prevMargin + el1.el.box.size.1) (el1.nextMargin + el2.prevMargin)
          exact this.mpr h_el1_el2
        case inr h =>
          simp [Prod.nth, Prod.nthVec, Rat.toVec, Element.set_pos_changes_pos, h] at *
          suffices _ : p.2 + el1.prevMargin + el1.el.box.size.2 ≤
            (p.2 + el1.prevMargin + el1.el.box.size.2) + (el1.nextMargin + el2.prevMargin)
            by linarith
          have := @le_add_iff_nonneg_right _ _ _ _ _ (p.2 + el1.prevMargin + el1.el.box.size.2) (el1.nextMargin + el2.prevMargin)
          exact this.mpr h_el1_el2
      case right =>
        exact ih p'.1 p'.2 h_valid_els

theorem layoutFluidAt.inner_disjoint (dim : Fin 2) (els : List FluidEl) (p : Pos)
  (h_valid : valid_fluid_els els) (h_disjoint : ∀ el ∈ els, el.el.inner_disjoint)
  : ∀ el ∈ layoutFluidAt dim els p, el.inner_disjoint
  := by
  induction els generalizing p
  all_goals simp [layoutFluidAt]
  case cons el els ih =>
  constructor
  case left =>
    exact Element.set_pos_preserves_inner_disjoint _ _ (h_disjoint el (els.mem_cons_self el))
  case right =>
    exact ih
      (p + el.prevMargin.toVec dim + el.el.box.size.nthVec dim + el.nextMargin.toVec dim)
      h_valid.tail (forall_prop_of_tail h_disjoint)

theorem layoutFluid.disjoint (dim : Fin 2) (els : List FluidEl)
  (h_valid : valid_fluid_els els) (h_disjoint : ∀ el ∈ els, el.el.inner_disjoint)
  : (layoutFluid dim els).inner_disjoint
  := by
  simp [Element.inner_disjoint, layoutFluid]
  constructor
  case left => exact layoutFluidAt.disjoint dim els 0 h_valid
  case right => exact layoutFluidAt.inner_disjoint dim els 0 h_valid h_disjoint

def layoutFluidX.disjoint := layoutFluid.disjoint 0
def layoutFluidY.disjoint := layoutFluid.disjoint 1

def layoutFluidMainSize (els : List FluidEl) (dim : Fin 2) : ℚ :=
  els.map (λ el : FluidEl =>
    el.el.box.size.nth dim + el.prevMargin + el.nextMargin)
  |>.sum

def layoutFluidCrossSize (els : List FluidEl) (dim : Fin 2) : ℚ⁺ :=
  els.map (·.el.box.size.nth dim.other) |>.maximum |>.unbot' 0

-- def layoutFluidBox (els : List FluidEl) (dim : Fin 2) (p : Pos) : Box :=
--   { pos := 0, size := (layoutFluidMainSize els dim p, layoutFluidCrossSize els dim p)}


-- -- (e ⊔ b).size = f(e.size, b)

-- def layoutFluid.aux.main_size (els : List FluidEl) (dim : Fin 2) (p : Pos)
--   : (Frame.mk 0 (aux dim els p)).box.size.nth dim = layoutFluidMainSize els dim p
--   := by
--   induction els generalizing p
--   all_goals simp [
--     aux, Frame.box, Box.offset, boxCover, Box.zero_size_zero,
--     layoutFluidMainSize, -List.sum_map_add,
--   ]
--   case nil => simp [Prod.nth]
--   case cons el els ih =>
--     simp [
--       List.attach_map_val', List.foldl_map, -List.sum_map_add,
--       Element.set_pos_changes_pos
--     ]
--     -- (p + el.prevMargin.toVec dim +
--     -- (↑(Prod.nthVec el.el.box.size dim).1, ↑(Prod.nthVec el.el.box.size dim).2) +
--     --           (1 + el.nextMargin).toVec dim)
--     have := ih (p + el.prevMargin.toVec dim + el.el.box.size.nthVec dim + (1 + el.nextMargin).toVec dim)
--     simp [Frame.box, Box.offset, boxCover, List.attach_map_val', List.foldl_map,] at this

--     let b : Box := { pos := p + el.prevMargin.toVec dim, size := el.el.box.size }
--     rw [List.foldl_hom (· ⊔ b) (· ⊔ ·.box)]
--     rw [this]




-- theorem layoutFluid.aux.x_width (els : List FluidEl) (p : Pos)
--   : (Frame.mk 0 (aux 0 els p)).box.size.w.val = p.x + layoutFluidXWidth els
--   := by
--   induction els generalizing p
--   all_goals simp [
--     layoutFluidX, layoutFluid, layoutFluid.aux, Element.box,
--     Frame.box, Box.offset,
--     boxCover,
--     Box.zero_size_zero,
--     List.attach_map_val', -List.sum_map_add, List.foldl_map,
--     layoutFluidXWidth,
--     -- boxCover.width_eq_extrema_diff,
--     Element.set_pos_changes_pos, Rat.toVec, Prod.nthVec
--   ] at *
--   case cons el els ih =>
--     have :
--       p + (el.prevMargin, 0) + ((el.el.box.size.1 : ℚ), 0) + (1 + el.nextMargin, 0)
--       = (p.1 + el.prevMargin + el.el.box.size.w + 1 + el.nextMargin, p.2) := by
--       apply Prod.eq_iff_fst_eq_snd_eq.mpr; simp
--       linarith
--     rw [this]

--     have := ih (p.1 + el.prevMargin + el.el.box.size.w + 1 + el.nextMargin) p.2
--     let b : Box := { pos := p + (el.prevMargin, 0), size := el.el.box.size }
--     rw [List.foldl_hom (· ⊔ b) (· ⊔ ·.box)]
--     rw [this]



  -- cases els
  -- all_goals simp [
  --   layoutFluidX, layoutFluid, layoutFluid.aux,
  --   Element.box, Frame.box, List.attach_map_val', Element.set_pos_changes_pos
  -- ] at *
  -- case nil =>
    --simp [boxCover, Box.offset, boxSup, regionSize, Box.zero_pos_zero, Box.zero_size_zero]



end LayoutMonotone


section InlineLayoutDisjoint

theorem InlineLayoutCtx.collectInline_disjoint  (icx : InlineLayoutCtx) (i : Inline)
  : ∀ el ∈ icx.collectInline i, el.inner_disjoint
  := by
  intro el h_in
  induction i generalizing icx
  all_goals simp [collectInline, collectInlineSeq] at h_in
  case text =>
    rw [h_in]
    simp [Element.inner_disjoint]
  case bold is ih =>
    obtain ⟨i, h⟩ := h_in
    exact ih i h.left {icx with bold := true} h.right

theorem InlineLayoutCtx.collectInlineSeq_disjoint (icx : InlineLayoutCtx) (is : List Inline)
  : ∀ el ∈ icx.collectInlineSeq is, el.inner_disjoint
  := by
  intro el h_in
  simp [collectInlineSeq] at h_in
  obtain ⟨i, h⟩ := h_in
  exact icx.collectInline_disjoint i el h.right

theorem InlineLayoutCtx.layoutLines_disjoint (icx : InlineLayoutCtx) (is : List Inline)
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

-- theorem InlineLayoutCtx.layoutLines_width_contained (icx : InlineLayoutCtx) (is : List Inline)
--   : (icx.layoutLines is).box.size.w ≤ icx.blockWidth := by
--   simp [layoutLines]

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
