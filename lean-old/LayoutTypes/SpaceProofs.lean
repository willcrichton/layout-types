import «LayoutTypes».Space
import «LayoutTypes».UtilsProofs

theorem Box.zero_pos_zero : (0 : Box).pos = 0 := by rfl
theorem Box.zero_size_zero : (0 : Box).size = 0 := by rfl

theorem Box.sup_eq_pos_inf (b1 b2 : Box) : (b1 ⊔ b2).pos = b1.pos ⊓ b2.pos := by
  simp [Box.instSup, Region.instSup]

theorem Box.disjoint_if_dim_disjoint (b1 b2 : Box) (dim : Fin 2)
  (h : b1.hi.nth dim ≤ b2.lo.nth dim)
  : b1.disjoint b2
  := by
  simp [
    Box.disjoint, Region.disjoint, Region.overlaps, Region.contains,
    -not_and, Classical.not_and_iff_or_not_not
  ]
  cases dim.two_eq_or
  case inl h_eq =>
    simp [Prod.nth, h_eq] at h
    apply And.intro
    exact Or.intro_right _ (Or.intro_left _ h)
    apply Or.intro_right _ (Or.intro_left _ _)
    exact le_add_of_le_of_nonneg h b2.size.1.prop
  case inr h_eq =>
    simp [Prod.nth, h_eq] at h
    apply And.intro
    exact Or.intro_right _ (Or.intro_right _ h)
    apply Or.intro_right _ (Or.intro_right _ _)
    exact le_add_of_le_of_nonneg h b2.size.2.prop

theorem boxCover.size_eq_extrema_diff (b : Box) (bs : List Box) :
  (boxCover b bs).size = boxMax b bs - boxMin b bs
  := by
  simp [boxCover, boxMax, boxMin]
  induction bs generalizing b
  case nil => simp
  case cons b' bs ih =>
    simp
    have ih := ih (b ⊔ b')
    rw [ih.left]
    rw [ih.right]
    simp [
      max, min, WithTop.some, WithBot.some, regionSize,
      SemilatticeSup.toSup, Sup.sup, Option.liftOrGet,
      regionSize, Option.getD, Lattice.toInf, Inf.inf
    ]

theorem boxCover.width_eq_extrema_diff (b : Box) (bs : List Box) :
  (boxCover b bs).size.w = (boxMax b bs - boxMin b bs).x
  := by
  have h_diff := (boxCover.size_eq_extrema_diff b bs)
  have ⟨h_diff_w, _⟩ := Prod.mk.inj_iff.mp h_diff
  exact h_diff_w

theorem boxMin.bounded (b : Box) (bs : List Box) (dim : Fin 2) (n : ℚ)
  (h_bounded : ∀ b2 ∈ b :: bs, n ≤ b2.pos.nth dim) : n ≤ (boxMin b bs).nth dim
  := by
  simp [boxMin]
  induction bs generalizing b
  case nil => simp [h_bounded]
  case cons b' bs ih =>
    have ih := ih b' (forall_prop_of_tail h_bounded)
    cases dim.two_eq_or
    case inl h =>
      simp [h, Prod.nth] at *
      rw [List.foldl_hom (min b.pos.1) min min _ _ (by simp [min_assoc])]
      exact le_min h_bounded.left ih
    case inr h =>
      simp [h, Prod.nth] at *
      rw [List.foldl_hom (min b.pos.2) min min _ _ (by simp [min_assoc])]
      exact le_min h_bounded.left ih

theorem boxMax.bounded (b : Box) (bs : List Box) (dim : Fin 2) (n : ℚ)
  (h_bounded : ∀ b2 ∈ b :: bs, b2.hi.nth dim ≤ n) : (boxMax b bs).nth dim ≤ n
  := by
  simp [instHAdd, Add.add, -List.mem_cons] at h_bounded
  simp [boxMax]
  induction bs generalizing b
  all_goals simp [-List.mem_cons] at h_bounded ⊢
  case nil => assumption
  case cons b' bs ih =>
    have ih := ih b' (forall_prop_of_tail h_bounded)
    cases dim.two_eq_or
    case inl h =>
      simp [h, Prod.nth] at *
      rw [List.foldl_hom (max (b.pos.1 + b.size.1)) max max _ _ (by simp [max_assoc])]
      exact max_le h_bounded.left ih
    case inr h =>
      simp [h, Prod.nth] at *
      rw [List.foldl_hom (max (b.pos.2 + b.size.2)) max max _ _ (by simp [max_assoc])]
      exact max_le h_bounded.left ih
