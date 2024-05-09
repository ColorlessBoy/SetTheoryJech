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

-- 1.8
theorem inductive_of_empty_and_next {X : ZFSet} (h1 : inductiveSet X) : inductiveSet (ZFSet.sep (fun (x: ZFSet) ↦ x = ∅ ∨ ∃ y ∈ X, x = y ∪ {y}) X) := by
  unfold inductiveSet
  constructor
  · rw [mem_sep]
    constructor
    · exact h1.left
    left
    rfl
  intro x
  rw [mem_sep, mem_sep]
  rintro ⟨hx1, hx2⟩
  constructor
  · apply h1.right
    rcases hx2 with hx2 | hx2
    · rw [hx2]
      exact h1.left
    obtain ⟨y, ⟨hy1, hy2⟩⟩ := hx2
    rw [hy2]
    exact h1.right _ hy1
  rcases hx2 with hx2 | _
  · right
    use ∅
    apply And.intro h1.left
    rw [hx2]
  right
  use x

-- 1.9
theorem induction_theorem {A : ZFSet} (h1 : A ⊆ indN) (h2: ∅ ∈ A) (h3: ∀ a ∈ A, a ∪ {a} ∈ A) : A = indN := by
  have h4: inductiveSet A := by
    unfold inductiveSet
    exact ⟨h2, h3⟩
  have h5: indN ⊆ A := by
    intro x hx
    unfold indN at hx
    rw [mem_sep] at hx
    exact hx.right _ h4
  ext x
  constructor
  · intro hx
    exact h1 hx
  intro hx
  exact h5 hx

--1.10
def subMaximal(X: ZFSet) := ZFSet.sep (fun x ↦ ¬ ∃ s ∈ X, x ⊆ s ∧ x ≠ s) X
def tFiniteSet (S : ZFSet) : Prop := ∀ x, x ≠ ∅ → x ⊆ ZFSet.powerset S → subMaximal x ≠ ∅
theorem empty_in_power_empty : ∀ x ∈ ZFSet.powerset ∅, x = ∅ := by
  intro x hx
  rw [ZFSet.mem_powerset] at hx
  rw [ZFSet.ext_iff]
  intro z
  constructor
  · intro zx
    exact hx zx
  intro z0
  exfalso
  exact ZFSet.not_mem_empty _ z0
theorem sub_of_power_empty {x : ZFSet} (h1: x ≠ ∅) (h2: x ⊆ ZFSet.powerset ∅) : x = {∅} := by
  rw [ZFSet.ext_iff]
  intro z
  rw [ZFSet.mem_singleton]
  constructor
  · intro zx
    exact empty_in_power_empty _ (h2 zx)
  intro zx
  rw [zx]
  contrapose! h1
  rw [ZFSet.ext_iff]
  intro s
  constructor
  · intro sx
    obtain hs:= empty_in_power_empty _ (h2 sx)
    rw [hs] at sx
    exfalso
    exact h1 sx
  intro s0
  exfalso
  exact ZFSet.not_mem_empty _ s0
theorem tfinite_empty : tFiniteSet ∅ := by
  unfold tFiniteSet
  intro x hx1 hx2 hx3
  obtain hx4 := sub_of_power_empty hx1 hx2
  have hx5 : ∅ ∈ subMaximal x := by
    rw [subMaximal, ZFSet.mem_sep, hx4]
    constructor
    · rw [mem_singleton]
    push_neg
    intro s hs1 _
    rw [mem_singleton] at hs1
    symm
    exact hs1
  rw [hx3] at hx5
  exact ZFSet.not_mem_empty _ hx5
theorem not_empty_to_exist {x : ZFSet} : x ≠ ∅ ↔ ∃ y, y ∈ x := by
  constructor
  · intro h
    contrapose! h
    rw [ZFSet.ext_iff]
    intro z
    constructor
    · intro hz
      exfalso
      exact h _ hz
    intro hz
    exfalso
    exact ZFSet.not_mem_empty _ hz
  intro h
  contrapose! h
  rw [h]
  exact ZFSet.not_mem_empty
theorem tfinite_n_of_indN : ZFSet.sep (fun n ↦ tFiniteSet n) indN = indN := by
  apply induction_theorem _ _ _
  · intro x hx
    rw [mem_sep] at hx
    exact hx.left
  · rw [mem_sep]
    exact ⟨inductive_of_indN.left, tfinite_empty⟩
  rintro s hs
  rw [mem_sep] at hs
  obtain ⟨hs1, hs2⟩ := hs
  rw [mem_sep]
  constructor
  · exact inductive_of_indN.right _ hs1
  rw [tFiniteSet]
  intro x hx1 hx2
  by_cases hx3: x ⊆ powerset s
  · exact hs2 _ hx1 hx3
  have hx4 : ∃ a ∈ x, s ∈ a := by
    contrapose! hx3
    intro a ha1
    obtain ha2 := hx3 _ ha1
    obtain ha3 := hx2 ha1
    rw [ZFSet.mem_powerset]
    rw [ZFSet.mem_powerset] at ha3
    intro b hb1
    obtain hb2 := ha3 hb1
    rw [ZFSet.mem_union] at hb2
    rcases hb2 with hb2 | hb2
    · exact hb2
    rw [ZFSet.mem_singleton] at hb2
    exfalso
    rw [hb2] at hb1
    exact ha2 hb1
  obtain ⟨b, ⟨hb1, hb2⟩⟩ := hx4
  have hb3 {b:ZFSet} (h : b ∈ x) : b \ {s} ∈ powerset s := by
    rw [ZFSet.mem_powerset]
    intro c hc1
    rw [ZFSet.mem_diff] at hc1
    obtain hb3 := hx2 h
    rw [ZFSet.mem_powerset] at hb3
    obtain hc2 := hb3 hc1.left
    rw [ZFSet.mem_union] at hc2
    rcases hc2 with hc2 | hc2
    · exact hc2
    exfalso
    exact hc1.right hc2
  have hb4 {b:ZFSet} (h : s ∈ b) : b \ {s} ∪ {s} = b := by
    rw [ZFSet.ext_iff]
    intro c
    rw [ZFSet.mem_union, ZFSet.mem_diff]
    constructor
    · rintro (⟨hc1, _⟩ | hc2)
      exact hc1
      rw [ZFSet.mem_singleton] at hc2
      rw [← hc2] at h
      exact h
    intro hc1
    rw [ZFSet.mem_singleton]
    by_cases hc2 : c = s
    · right
      exact hc2
    left
    exact ⟨hc1, hc2⟩
  let y := ZFSet.sep (fun a ↦ a ∈ x ∨ a ∪ {s} ∈ x) (powerset s)
  have hy1 {b:ZFSet} (h1 : b ∈ x) (h2 : s ∈ b): b \ {s} ∈ y := by
    rw [ZFSet.mem_sep]
    constructor
    · exact hb3 h1
    right
    rw [hb4 h2]
    exact h1
  have hy2: y ≠ ∅ := by
    apply not_empty_to_exist.mpr
    use b \ {s}
    exact hy1 hb1 hb2
  have hy3: y ⊆ powerset s := by
    intro a ha1
    rw [ZFSet.mem_sep] at ha1
    exact ha1.left
  obtain hy4 := hs2 _ hy2 hy3
  obtain ⟨c, hc⟩ := not_empty_to_exist.mp hy4
  rw [subMaximal, ZFSet.mem_sep] at hc
  obtain ⟨hc1, hc2⟩ := hc
  rw [ZFSet.mem_sep] at hc1
  obtain ⟨hc3, hc4⟩ := hc1
  push_neg at hc2
  apply not_empty_to_exist.mpr
  rcases hc4 with hc4 | hc4
  · by_cases hc5 : c ∪ {s} ∈ x
    · use c ∪ {s}
      rw [subMaximal, ZFSet.mem_sep]
      apply And.intro hc5
      push_neg
      intro d hd1 hd2
      have hd3 : s ∈ d := by
        apply hd2
        rw [ZFSet.mem_union, ZFSet.mem_singleton]
        right
        rfl
      obtain hd4 := hy1 hd1 hd3
      obtain hd5 := hc2 _ hd4
      have hd6 : c ⊆ d \ {s} := by
        intro e he
        rw [ZFSet.mem_diff]
        constructor
        · apply hd2
          rw [ZFSet.mem_union]
          left
          exact he
        rw [ZFSet.mem_singleton]
        intro he2
        rw [he2] at he
        rw [ZFSet.mem_powerset] at hc3
        apply hc3 at he
        exact (not_self_of_indN s hs1).left he
      apply hd5 at hd6
      rw [hd6]
      apply hb4 hd3
    use c
    rw [subMaximal, ZFSet.mem_sep]
    apply And.intro hc4
    push_neg
    intro d hd1 hd2
    apply hc2 d _ hd2
    rw [ZFSet.mem_sep, ZFSet.mem_powerset]
    constructor
    · intro e he1
      obtain hd3 := hx2 hd1
      rw [ZFSet.mem_powerset] at hd3
      obtain he2 := hd3 he1
      rw [ZFSet.mem_union] at he2
      rcases he2 with he2 | he2
      · exact he2
      rw [ZFSet.mem_singleton] at he2
      rw [he2] at he1
      have hd4: c ⊆ d \ {s} := by
        intro f hf1
        rw [ZFSet.mem_diff, ZFSet.mem_singleton]
        constructor
        · exact hd2 hf1
        intro hf2
        rw [hf2] at hf1
        rw [ZFSet.mem_powerset] at hc3
        apply hc3 at hf1
        exact (not_self_of_indN _ hs1).left hf1
      have hd5: d \ {s} ∈ y := by
        apply hy1 hd1 he1
      apply hc2 _ hd5 at hd4
      rw [hd4] at hc5
      rw [hb4 he1] at hc5
      exfalso
      apply hc5 hd1
    left
    exact hd1
  use c ∪ {s}
  rw [subMaximal, ZFSet.mem_sep]
  apply And.intro hc4
  push_neg
  intro d hd1 hd2
  have hd3 : d \ {s} ∈ y := by
    apply hy1 hd1
    apply hd2
    rw [ZFSet.mem_union, ZFSet.mem_singleton]
    right
    rfl
  have hd4 : c ⊆ d \ {s} := by
    intro e he1
    rw [ZFSet.mem_diff, ZFSet.mem_singleton]
    constructor
    apply hd2
    rw [ZFSet.mem_union]
    left
    exact he1
    intro he2
    rw [he2] at he1
    rw [ZFSet.mem_powerset] at hc3
    apply hc3 at he1
    exact (not_self_of_indN _ hs1).left he1
  obtain hd5 := hc2 _ hd3 hd4
  rw [hd5]
  apply hb4
  apply hd2
  rw [ZFSet.mem_union, ZFSet.mem_singleton]
  right
  rfl

-- 1.11.1
theorem not_tfinite_indN : ¬ tFiniteSet indN := by
  rw [tFiniteSet]
  push_neg
  use indN
  constructor
  · apply not_empty_to_exist.mpr
    use ∅
    apply inductive_of_indN.left
  constructor
  · intro n hn
    rw [ZFSet.mem_powerset]
    exact transitive_of_indN _ hn
  rw [ZFSet.ext_iff]
  intro n
  constructor
  intro hn
  rw [subMaximal, ZFSet.mem_sep] at hn
  obtain ⟨hn1, hn2⟩ := hn
  exfalso
  apply hn2
  use n ∪ {n}
  constructor
  · apply inductive_of_indN.right _ hn1
  constructor
  · intro x hx
    rw [ZFSet.mem_union]
    left
    exact hx
  apply (not_self_of_indN _ hn1).right
  intro hn
  exfalso
  exact ZFSet.not_mem_empty _ hn
-- 1.11.2
theorem empty_subMaximal_indN : subMaximal indN = ∅ := by
  rw [ZFSet.ext_iff]
  intro n
  rw [subMaximal, mem_sep]
  constructor
  · rintro ⟨hn1, hn2⟩
    exfalso
    apply hn2
    use n ∪ {n}
    constructor
    · apply inductive_of_indN.right _ hn1
    constructor
    · intro x hx
      rw [ZFSet.mem_union]
      left
      exact hx
    apply (not_self_of_indN _ hn1).right
  intro hn
  exfalso
  exact ZFSet.not_mem_empty _ hn
end

-- 1.12
def isFunc (f: ZFSet) (X: ZFSet) (Y: ZFSet) := ∀ x ∈ X, ∃! y ∈ Y, x.pair y ∈ f
def injective (f: ZFSet) (X: ZFSet) (Y: ZFSet) := ∀ x₁ ∈ X, ∀ y₁ ∈ Y, ∀ x₂ ∈ X, ∀ y₂ ∈ Y, (x₁.pair y₁) ∈ f → (x₂.pair y₂) ∈ f → y₁ = y₂ → x₁ = x₂
def surjective (f: ZFSet) (X: ZFSet) (Y: ZFSet) := ∀ y ∈ Y, ∃ x ∈ X, x.pair y ∈ f
def finiteSet (X: ZFSet) := ∃ Y ∈ indN, ∃ f, (isFunc f X Y) ∧ (injective f X Y)
def preimage (f: ZFSet) (X: ZFSet) (Y: ZFSet) := ZFSet.sep (fun x ↦ ∃ y ∈ Y, x.pair y ∈ f) X
def image (f: ZFSet) (X: ZFSet) (Y: ZFSet) := ZFSet.sep (fun y ↦ ∃ x ∈ X, x.pair y ∈ f) Y

theorem finite_to_tfinite (h: finiteSet S) : tFiniteSet S := by
  rw [tFiniteSet]
  intro PX hPX1 hPX2
  apply not_empty_to_exist.mpr
  obtain ⟨Y, ⟨hY, ⟨F, ⟨hF1, hF2⟩⟩⟩⟩ := h
  let imgPX := ZFSet.sep (fun t ↦ (preimage F S t) ∈ PX ∧ image F (preimage F S t) Y = t) (ZFSet.powerset Y)
  have eqhpx {px: ZFSet} (hpx: px ∈ PX) : preimage F S (image F px Y) = px := by
    rw [ZFSet.ext_iff]
    intro z
    rw [preimage, ZFSet.mem_sep]
    constructor
    · rintro ⟨hz1, ⟨w, ⟨hw1, hw2⟩⟩⟩
      rw [image, ZFSet.mem_sep] at hw1
      obtain ⟨hw3, ⟨a, ha⟩⟩ := hw1
      have : z = a := by
        apply hF2 _ hz1 _ hw3 _ _ _ hw3 hw2 ha.right
        rfl
        obtain tmp1 := hPX2 hpx
        rw [ZFSet.mem_powerset] at tmp1
        exact tmp1 ha.left
      rw [this]
      exact ha.left
    intro hz
    obtain tmp1 := hPX2 hpx
    rw [ZFSet.mem_powerset] at tmp1
    apply And.intro (tmp1 hz)
    obtain ⟨yz, hyz, _⟩ := hF1 _ (tmp1 hz)
    use yz
    apply And.intro _ hyz.right
    rw [image, ZFSet.mem_sep]
    apply And.intro hyz.left
    use z
    exact ⟨hz, hyz.right⟩
  have himgPX1 : imgPX ≠ ∅ := by
    rw [not_empty_to_exist] at hPX1
    obtain ⟨px, hpx⟩ := hPX1
    rw [not_empty_to_exist]
    use image F px Y
    rw [ZFSet.mem_sep]
    constructor
    · rw [ZFSet.mem_powerset]
      intro t ht
      rw [image, ZFSet.mem_sep] at ht
      exact ht.left
    rw [eqhpx hpx]
    exact ⟨hpx, rfl⟩
  have himgPX2 : imgPX ⊆ ZFSet.powerset Y := by
    intro y hy
    rw [ZFSet.mem_sep] at hy
    exact hy.left
  have hY2 : tFiniteSet Y := by
    rw [← tfinite_n_of_indN, ZFSet.mem_sep] at hY
    exact hY.right
  obtain himgS3 := hY2 _ himgPX1 himgPX2
  rw [not_empty_to_exist] at himgS3
  obtain ⟨subY, hsubY⟩ := himgS3
  rw [subMaximal, ZFSet.mem_sep, ZFSet.mem_sep] at hsubY
  obtain ⟨⟨hsubY1, hsubY2, hsubY4⟩, hsubY3⟩ := hsubY
  use preimage F S subY
  rw [subMaximal, ZFSet.mem_sep]
  constructor
  · exact hsubY2
  contrapose! hsubY3
  obtain ⟨s, ⟨hs1, hs2, hs3⟩⟩ := hsubY3
  use image F s Y
  constructor
  · rw [ZFSet.mem_sep, ZFSet.mem_powerset]
    constructor
    · intro t ht
      rw [image, ZFSet.mem_sep] at ht
      exact ht.left
    have : preimage F S (image F s Y) = s := by
      rw [ZFSet.ext_iff]
      intro t
      constructor
      · intro ht
        rw [preimage, ZFSet.mem_sep] at ht
        obtain ⟨a, ha1, ha2⟩ := ht.right
        rw [image, ZFSet.mem_sep] at ha1
        obtain ⟨b, hb1, hb2⟩ := ha1.right
        obtain hb3 := hPX2 hs1
        rw [ZFSet.mem_powerset] at hb3
        obtain hb4 := hb3 hb1
        have : b = t := by
          apply hF2 _ hb4 _ ha1.left _ ht.left _ ha1.left hb2 ha2
          rfl
        rw [← this]
        exact hb1
      intro ts
      rw [preimage, ZFSet.mem_sep]
      obtain ht1 := hPX2 hs1
      rw [ZFSet.mem_powerset] at ht1
      apply And.intro (ht1 ts)
      obtain ⟨y2, ⟨hy2l, hy2r⟩, _⟩ := hF1 t (ht1 ts)
      use y2
      constructor
      · rw [image, ZFSet.mem_sep]
        apply And.intro hy2l
        use t
      exact hy2r
    rw [this]
    exact ⟨hs1, rfl⟩
  rw [ZFSet.mem_powerset] at hsubY1
  constructor
  · intro t ht
    rw [image, ZFSet.mem_sep]
    apply And.intro (hsubY1 ht)
    rw [← hsubY4, image, ZFSet.mem_sep] at ht
    obtain ⟨a, ⟨ha1, ha2⟩⟩ := ht.right
    use a
    apply And.intro _ ha2
    exact hs2 ha1
  contrapose! hs3
  rw [hs3]
  rw [ZFSet.ext_iff]
  intro t
  rw [preimage, ZFSet.mem_sep]
  obtain hs4 := hPX2 hs1
  rw [ZFSet.mem_powerset] at hs4
  constructor
  · intro ⟨h1, h2⟩
    obtain ⟨w, ⟨hw1, hw2⟩⟩ := h2
    rw [image, ZFSet.mem_sep] at hw1
    obtain ⟨hw3, ⟨a, ha1, ha2⟩⟩ := hw1
    have : t = a := by apply hF2 _ h1 _ hw3 _ (hs4 ha1) _ hw3 hw2 ha2 rfl
    rw [this]
    exact ha1
  intro ht
  apply And.intro (hs4 ht)
  obtain ⟨w, hw1, _⟩ := hF1 _ (hs4 ht)
  use w
  constructor
  · rw [image, ZFSet.mem_sep]
    apply And.intro hw1.left
    use t
    exact ⟨ht, hw1.right⟩
  exact hw1.right
