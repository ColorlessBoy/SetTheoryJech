import Mathlib.SetTheory.ZFC.Basic

section
open ZFSet

-- do not use it in this Chapter
theorem setin_not_comm{a b : ZFSet} : ¬ (a ∈ b ∧ b ∈ a) := by
  by_contra h1
  obtain ⟨h1l, h1r⟩ := h1
  have h2: ∃ x ∈ ({a, b} : ZFSet), {a, b} ∩ x = ∅ := by
    apply regularity
    by_contra h
    rw [eq_empty] at h
    apply h a
    rw [mem_pair]
    left
    rfl
  have h3: b ∈ {a, b} ∩ a := by
    rw [mem_inter, mem_pair]
    exact ⟨(Or.inr rfl), h1r⟩
  have h4: a ∈ {a, b} ∩ b := by
    rw [mem_inter, mem_pair]
    exact ⟨(Or.inl rfl), h1l⟩
  rcases h2 with ⟨x, hx, xinter⟩
  rw [mem_pair] at hx
  rcases hx with (hx | hx)
  · rw [hx, eq_empty] at xinter
    apply xinter b h3
  rw [hx, eq_empty] at xinter
  apply xinter a h4

theorem pair_eq_singleton {s : ZFSet} : ({s, s} : ZFSet) = {s} := by
  ext x
  rw [mem_pair, mem_singleton]
  constructor
  rintro (xs | xs)
  exact xs
  exact xs
  apply Or.inl

theorem singleton_eq {a b : ZFSet} (h : ({a} : ZFSet) = {b}) : a = b := by
  rw [← mem_singleton]
  rw [← ext_iff.1 h a]
  rw [mem_singleton]

theorem pair_comm {a b : ZFSet} : ({a, b} : ZFSet) = {b, a} := by
  rw [ext_iff]
  intro x
  rw [mem_pair, mem_pair]
  apply Or.comm

theorem pair_eq {a b c d : ZFSet} (h1 : ({a, b} : ZFSet) = {c, d}) (h2: a = c) : b = d := by
  rw [h2] at h1
  by_cases h3: b = c
  · rw [h3, pair_eq_singleton] at h1
    symm
    rw [h3, ← mem_singleton, h1, mem_pair]
    right
    rfl
  have h4: b ∈ {c, d} := by
    rw [← h1, mem_pair]
    right
    rfl
  rw [mem_pair] at h4
  rcases h4 with h4 | h4
  · exfalso
    apply h3 h4
  exact h4

theorem pair_eq2 {a b c d : ZFSet} (h1 : ({a, b} : ZFSet) = {c, d}) (h2: a ≠ c) : a = d ∧ b = c := by
  constructor
  have h3: a ∈ {c, d} := by
    rw [← h1, mem_pair]
    left
    rfl
  rw [mem_pair] at h3
  rcases h3 with h3 | h3
  · exfalso
    apply h2 h3
  exact h3
  have h4 : c ∈ {a, b} := by
    rw [h1, mem_pair]
    left
    rfl
  rw [mem_pair] at h4
  rcases h4 with h4 | h4
  · symm at h4
    exfalso
    apply h2 h4
  symm
  exact h4

-- 1.1
theorem ordered_pair_eq {a b c d : ZFSet} : ({{a}, {a, b}} : ZFSet) = {{c}, {c, d}} ↔ a = c ∧ b = d := by
  constructor
  · by_cases h1 : a = c
    · rw [h1]
      intro h2
      constructor
      · rfl
      have h3 : {c, b} = {c, d} := by
        apply pair_eq h2 rfl
      apply pair_eq h3 rfl
    intro h2
    have h3 : ¬ {a} = {c} := by
      intro h3
      apply h1
      apply singleton_eq h3
    apply pair_eq2 h2 at h3
    have h4: a = c := by
      rw [← mem_singleton, ← h3.right, mem_pair]
      left
      rfl
    exfalso
    apply h1 h4
  rintro ⟨h1, h2⟩
  rw [h1, h2]

-- 1.2
theorem powerset_not_subset {x : ZFSet} : ¬ powerset x ⊆ x := by
  rintro h
  let sz := ZFSet.sep (fun (z : ZFSet) ↦ z ∉ z) x
  have h2 : sz ∈ x := by
    apply h
    rw [mem_powerset]
    intro z hz
    rw [mem_sep] at hz
    exact hz.left
  by_cases h3: sz ∈ sz
  · have h4: sz ∉ sz := by
      rw [mem_sep] at h3
      exact h3.right
    contradiction
  have h4: sz ∈ sz := by
    rw [mem_sep]
    exact ⟨h2, h3⟩
  contradiction

/--
inductive S ↔ (∅ ∈ S ∧ ∀ x ∈ S, x ∪ {x} ∈ S)
transitive S ↔ ∀ x ∈ S, x ⊆ S
-/

def inductiveSet (S : ZFSet) : Prop := ∅ ∈ S ∧ ∀ x ∈ S, x ∪ {x} ∈ S
def transitiveSet (S : ZFSet) : Prop := ∀ x, x ∈ S → x ⊆ S

theorem inductive_of_sub {X : ZFSet} (h1 : inductiveSet X) : inductiveSet (ZFSet.sep (fun (x: ZFSet) ↦ x ⊆ X) X) := by
  obtain ⟨h1l, h1r⟩ := h1
  constructor
  · rw [mem_sep]
    constructor
    · exact h1l
    exact empty_subset X
  intro x
  rw [mem_sep, mem_sep]
  rintro ⟨h2, h3⟩
  constructor
  · apply h1r x h2
  rintro z hz
  rw [mem_union] at hz
  rcases hz with hz1 | hz2
  · exact h3 hz1
  rw [mem_singleton] at hz2
  rw [hz2]
  exact h2

theorem inductive_of_inter{X Y : ZFSet} (h1: inductiveSet X) (h2: inductiveSet Y) : inductiveSet (X ∩ Y) := by
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  constructor
  · rw [mem_inter]
    exact ⟨h1l, h2l⟩
  rintro x
  rw [mem_inter, mem_inter]
  rintro ⟨xX, xY⟩
  exact ⟨h1r _ xX, h2r _ xY⟩

theorem inductive_omega : inductiveSet ZFSet.omega := by
  constructor
  · exact ZFSet.omega_zero
  intro n hn
  apply ZFSet.omega_succ at hn
  have h : n ∪ {n} = insert n n := by
    ext x
    rw [ZFSet.mem_insert_iff, ZFSet.mem_union, mem_singleton, Or.comm]
  rw [h]
  exact hn

-- Infinity 保证至少存在一个inductiveSet
-- Separation Schema 保证所有inductiveSet的交集是一个集合
-- 证明：所有inductiveSet的交集是一个inductiveSet
def indN := ZFSet.sep (fun x ↦ ∀ X, inductiveSet X → x ∈ X) ZFSet.omega
#check indN
theorem inductive_of_indN : inductiveSet indN := by
  unfold indN
  constructor
  · rw [mem_sep]
    constructor
    · apply inductive_omega.left
    intro X hX
    exact hX.left
  intro x hx
  rw [mem_sep]
  rw [mem_sep] at hx
  constructor
  · apply inductive_omega.right
    exact hx.left
  intro X hX
  obtain h3 := hx.right _ hX
  apply hX.right _ h3

-- 1.3.1
def subInductiveSet (X : ZFSet) := ZFSet.sep (fun x ↦ x = ∅ ∨ ∀ y ∈ x, y ∈ X) X
theorem inductive_of_subInductiveSet {X : ZFSet} (h1 : inductiveSet X) : inductiveSet (subInductiveSet X) := by
  unfold inductiveSet
  rw [subInductiveSet, mem_sep]
  constructor
  · exact ⟨h1.left, Or.inl rfl⟩
  intro x hx
  rw [mem_sep]
  rw [mem_sep] at hx
  constructor
  · exact h1.right _ hx.left
  right
  intro y hy
  rw [mem_union] at hy
  rcases hy with hy1 | hy2
  · rcases hx.right with hx1 | hx2
    rw [hx1] at hy1
    exfalso
    exact ZFSet.not_mem_empty _ hy1
    exact hx2 _ hy1
  rw [mem_singleton] at hy2
  rw [hy2]
  exact hx.left
-- 1.3.2
theorem transitive_of_indN : transitiveSet indN := by
  unfold transitiveSet indN
  intro x hx y hy1
  rw [mem_sep]
  rw [mem_sep] at hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain h2 := hx2 _ (inductive_of_subInductiveSet inductive_omega)
  rw [subInductiveSet, mem_sep] at h2
  rcases h2.right with h3 | h3
  · rw [h3] at hy1
    exfalso
    exact ZFSet.not_mem_empty _ hy1
  constructor
  · exact h3 _ hy1
  intro X hX
  obtain h4 := hx2 _ (inductive_of_subInductiveSet hX)
  rw [subInductiveSet, mem_sep] at h4
  rcases h4.right with h5 | h5
  · exfalso
    rw [h5] at hy1
    exact ZFSet.not_mem_empty _ hy1
  exact h5 _ hy1

def member_of_indN (n : ZFSet) := ZFSet.sep (fun m ↦ m ∈ n) indN
theorem all_of_member_of_indN : ∀ n ∈ indN, n = member_of_indN n := by
  intro n hn
  unfold indN at hn
  rw [mem_sep] at hn
  ext x
  rw [member_of_indN, mem_sep, indN, mem_sep]
  constructor
  · intro xn
    constructor
    · constructor
      · obtain h1 := hn.right _ (inductive_of_subInductiveSet inductive_omega)
        rw [subInductiveSet, mem_sep] at h1
        rcases h1.right with h2 | h2
        · exfalso
          rw [h2] at xn
          exact ZFSet.not_mem_empty _ xn
        exact h2 _ xn
      intro X hX
      obtain h1 := hn.right _ (inductive_of_subInductiveSet hX)
      rw [subInductiveSet, mem_sep] at h1
      rcases h1.right with h2 | h2
      · rw [h2] at xn
        exfalso
        exact ZFSet.not_mem_empty _ xn
      exact h2 _ xn
    exact xn
  intro hn2
  exact hn2.right

-- 1.4.1
theorem inductive_of_trans_of_inductiveSet {X : ZFSet} (h1 : inductiveSet X) : inductiveSet (ZFSet.sep (fun (x: ZFSet) ↦ transitiveSet x) X) := by
  unfold inductiveSet
  rw [mem_sep]
  constructor
  · apply And.intro h1.left
    unfold transitiveSet
    intro x hx
    exfalso
    exact ZFSet.not_mem_empty _ hx
  intro x hx
  rw [mem_sep]
  rw [mem_sep] at hx
  constructor
  · exact h1.right _ hx.left
  unfold transitiveSet
  rintro y hy z hz
  rw [mem_union]
  rw [mem_union] at hy
  left
  rcases hy with hy | hy
  · exact hx.right _ hy hz
  rw [mem_singleton] at hy
  rw [hy] at hz
  exact hz

-- 1.4.2
theorem transitive_of_member_of_indN : ∀ n ∈ indN, transitiveSet n := by
  intro n hn
  rw [indN, mem_sep] at hn
  rw [transitiveSet]
  intro x xn y yx
  obtain h1 := hn.right _ (inductive_of_trans_of_inductiveSet inductive_of_indN)
  rw [mem_sep] at h1
  obtain ⟨_, h1r⟩ := h1
  rw [transitiveSet] at h1r
  exact h1r _ xn yx

theorem transitive_of_empty : transitiveSet ∅ := by
  unfold transitiveSet
  intro x hx
  exfalso
  exact ZFSet.not_mem_empty _ hx

-- 1.5.1
theorem inductive_of_trans_and_notself {X : ZFSet} (h1 : inductiveSet X) : inductiveSet (ZFSet.sep (fun (x: ZFSet) ↦ transitiveSet x ∧ x ∉ x) X) := by
  rw [inductiveSet, mem_sep]
  constructor
  · constructor
    · exact h1.left
    exact ⟨transitive_of_empty, ZFSet.not_mem_empty _⟩
  intro x hx
  rw [mem_sep]
  rw [mem_sep] at hx
  obtain ⟨hx1, ⟨hx2, hx3⟩⟩ := hx
  rw [transitiveSet] at hx2
  constructor
  · exact h1.right _ hx1
  constructor
  · unfold transitiveSet
    intro y hy z hz
    rw [mem_union]
    rw [mem_union] at hy
    rcases hy with hy | hy
    · left
      exact hx2 _ hy hz
    rw [mem_singleton]
    rw [mem_singleton] at hy
    rw [hy] at hz
    left
    exact hz
  intro hxx
  rw [mem_union, mem_singleton] at hxx
  rcases hxx with hxx | hxx
  · obtain hxx2 := hx2 _ hxx
    apply hx3
    apply hxx2
    rw [mem_union, mem_singleton]
    right
    rfl
  apply hx3
  rw [ZFSet.ext_iff] at hxx
  apply (hxx _).mp
  rw [mem_union, mem_singleton]
  right
  rfl

-- 1.5.2
theorem not_self_of_indN : ∀ n ∈ indN, n ∉ n ∧ n ≠ n ∪ {n} := by
  intro n hn
  rw [indN, mem_sep] at hn
  obtain h1 := hn.right _ (inductive_of_trans_and_notself inductive_omega)
  rw [mem_sep] at h1
  constructor
  · exact h1.right.right
  intro hn2
  apply h1.right.right
  have : n ∈ n ∪ {n} := by
    rw [mem_union, mem_singleton]
    right
    rfl
  rw [← hn2] at this
  exact this

theorem transitive_of_next {x: ZFSet} (h1: transitiveSet x) : transitiveSet (x ∪ {x}) := by
  intro z hz w hw
  rw [mem_union]
  rw [mem_union, mem_singleton] at hz
  rcases hz with hz | hz
  · left
    exact h1 _ hz hw
  rw [hz] at hw
  left
  exact hw

-- 1.6
def inMinimal(X : ZFSet) := ZFSet.sep (fun x ↦ ∀ s ∈ X, s ∉ x) X
theorem inductive_of_trans_and_inminimal {X : ZFSet} (h1 : inductiveSet X) : inductiveSet (ZFSet.sep (fun (x: ZFSet) ↦ transitiveSet x ∧ ∀ y ⊆ x, y ≠ ∅ → inMinimal y ≠ ∅) X) := by
  rw [inductiveSet, mem_sep]
  constructor
  · constructor
    exact h1.left
    constructor
    · exact transitive_of_empty
    intro z hz1 hz2
    exfalso
    apply hz2
    ext w
    constructor
    · intro wz
      exfalso
      exact ZFSet.not_mem_empty _ (hz1 wz)
    intro hw
    exfalso
    exact ZFSet.not_mem_empty _ hw
  intro x
  rw [mem_sep, mem_sep]
  rintro ⟨h2, ⟨h3, h4⟩⟩
  constructor
  · exact h1.right _ h2
  constructor
  · exact transitive_of_next h3
  have hx1 : x ∉ x := by
    intro hx
    have hx11: {x} ⊆ x := by
      intro w hw
      rw [mem_singleton] at hw
      rw [hw]
      exact hx
    have h2: {x} ≠ ∅ := by
      intro h1
      apply ZFSet.not_mem_empty x
      rw [← h1, mem_singleton]
    apply h4 _ hx11 h2
    ext w
    rw [inMinimal, mem_sep]
    constructor
    · rintro ⟨h5, h6⟩
      obtain h7 := h6 _ h5
      rw [mem_singleton] at h5
      rw [h5] at h7
      exfalso
      apply h7 hx
    intro hw
    exfalso
    exact ZFSet.not_mem_empty _ hw
  have hx3 {z: ZFSet} (h1: z ⊆ x) : inMinimal z ⊆ inMinimal (z ∪ {x}) := by
    intro y hy
    rw [inMinimal, mem_sep, mem_union]
    rw [inMinimal, mem_sep] at hy
    constructor
    · left
      exact hy.left
    intro s hs sy
    rw [mem_union] at hs
    obtain tmp1 := h1 hy.left
    obtain tmp2 := h3 _ tmp1 sy
    rcases hs with hs | hs
    · exact hy.right _ hs sy
    rw [mem_singleton] at hs
    rw [hs] at tmp2
    exact hx1 tmp2
  intro y hy1 hy2
  by_cases hy3 : y ⊆ x
  · exact h4 _ hy3 hy2
  by_cases hy4: y = {x}
  · intro hy5
    rw [inMinimal, ZFSet.ext_iff] at hy5
    apply ZFSet.not_mem_empty x
    apply (hy5 _).mp
    rw [mem_sep]
    constructor
    · rw [hy4, mem_singleton]
    intro s sy
    rw [hy4, mem_singleton] at sy
    rw [sy]
    exact hx1
  have hy5 : ∃ z, z ≠ ∅ ∧ z ⊆ x ∧ y = z ∪ {x} := by
    use ZFSet.sep (fun s ↦ s ≠ x) y
    constructor
    · intro hy
      apply hy4
      ext z
      rw [mem_singleton]
      rw [ZFSet.ext_iff] at hy
      obtain hy5 := hy z
      rw [mem_sep] at hy5
      by_contra hy6
      push_neg at hy6
      rcases hy6 with hy6 | hy6
      · rw [hy5] at hy6
        exact ZFSet.not_mem_empty _ hy6
      obtain ⟨hy7, hy8⟩ := hy6
      have hy9: ∃ w, w ∈ y ∧ w ≠ x := by
        by_contra hy91
        push_neg at hy91
        apply hy2
        ext w
        obtain hy92 := hy91 w
        constructor
        · intro wy
          exfalso
          obtain hy93 := hy92 wy
          rw [hy8, ← hy93] at hy7
          exact hy7 wy
        intro wempty
        exfalso
        exact ZFSet.not_mem_empty _ wempty
      obtain ⟨w, hw⟩ := hy9
      obtain hy94 := hy w
      rw [mem_sep] at hy94
      rw [hy94] at hw
      exfalso
      exact ZFSet.not_mem_empty _ hw
    constructor
    · intro z zy
      rw [mem_sep] at zy
      obtain hy5 := hy1 zy.left
      rw [mem_union, mem_singleton] at hy5
      rcases hy5 with hy5 | hy5
      exact hy5
      exfalso
      exact zy.right hy5
    ext z
    rw [mem_union, mem_sep, mem_singleton]
    constructor
    · intro zy
      by_cases tmp: z = x
      right
      exact tmp
      left
      exact ⟨zy, tmp⟩
    rintro (⟨zy, _⟩ | hz)
    · exact zy
    rw [hz]
    by_contra hz2
    apply hy3
    intro w hw
    obtain hz3 := hy1 hw
    rw [mem_union] at hz3
    rcases hz3 with hz3 | hz3
    · exact hz3
    rw [mem_singleton] at hz3
    rw [hz3] at hw
    exfalso
    apply hz2 hw
  obtain ⟨z, ⟨hz1, ⟨ hz2, hz3 ⟩⟩⟩ := hy5
  rw [hz3]
  obtain hz4 := h4 _ hz2 hz1
  obtain hz5 := hx3 hz2
  by_contra hz6
  rw [hz6] at hz5
  apply hz4
  ext w
  constructor
  · intro wz
    apply hz5 wz
  intro wz
  exfalso
  exact ZFSet.not_mem_empty _ wz

-- 1.7
theorem none_empty_inminimal_of_none_empty_member_of_indN: ∀ X ⊆ indN, X ≠ ∅ → inMinimal X ≠ ∅ := by
  intro X hX1
  contrapose!
  intro hX2
  ext n
  constructor
  · intro xinX
    obtain hX3 := hX1 xinX
    by_cases hn1 : n ∩ X = ∅
    · rw [ZFSet.ext_iff] at hX2
      rw [← hX2]
      rw [inMinimal, mem_sep]
      apply And.intro xinX
      intro s sX sn
      rw [ZFSet.ext_iff] at hn1
      have hn3 : s ∈ n ∩ X := ZFSet.mem_inter.mpr ⟨sn, sX⟩
      exact ZFSet.not_mem_empty _ ((hn1 _).1 hn3)
    rw [indN, mem_sep] at hX3
    obtain ⟨_, hX3r⟩ := hX3
    have h1 := hX3r _ (inductive_of_trans_and_inminimal inductive_of_indN)
    rw [mem_sep] at h1
    have h2 := h1.right.right
    have h3 : (n ∩ X) ⊆ n := by
      intro s hs
      rw [mem_inter] at hs
      apply hs.left
    have h4 := h2 _ h3 hn1
    have h5 : inMinimal X ≠ ∅ := by
      contrapose! h4
      ext s
      rw [inMinimal, mem_sep]
      constructor
      · rintro ⟨hs1, hs2⟩
        rw [← h4, inMinimal, mem_sep]
        rw [mem_inter] at hs1
        apply And.intro hs1.right
        intro w wX
        obtain hs3 := hs2 w
        rw [mem_inter] at hs3
        by_cases wn: w ∈ n
        · exact hs3 ⟨wn, wX⟩
        contrapose! wn
        obtain h5 := h1.right.left
        rw [transitiveSet] at h5
        exact h5 _ hs1.left wn
      intro s0
      exfalso
      exact ZFSet.not_mem_empty _ s0
    exfalso
    exact h5 hX2
  intro hn
  exfalso
  exact ZFSet.not_mem_empty _ hn
end
