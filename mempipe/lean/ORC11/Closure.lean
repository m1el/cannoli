import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Relation

/-!
# Deciding transitive closures on finite supports

Floyd–Warshall, proved: the transitive closure of a decidable relation whose
edges stay within a finite list of nodes, computed as a `Finset` of pairs.
-/

namespace ORC11.Closure

variable {α : Type} [DecidableEq α] (r : α → α → Prop)

/-- Paths of `r` whose intermediate nodes lie in `S`. -/
inductive Via (S : Finset α) : α → α → Prop
  | single {a b : α} : r a b → Via S a b
  | tail {a b c : α} : Via S a b → b ∈ S → r b c → Via S a c

variable {r}

omit [DecidableEq α] in
theorem Via.trans {S : Finset α} {a b c : α} (h1 : Via r S a b) (hb : b ∈ S)
    (h2 : Via r S b c) : Via r S a c := by
  induction h2 with
  | single h => exact .tail h1 hb h
  | tail _ hm hr ih => exact .tail ih hm hr

omit [DecidableEq α] in
theorem Via.mono {S T : Finset α} (hST : S ⊆ T) {a b : α} (h : Via r S a b) : Via r T a b := by
  induction h with
  | single h => exact .single h
  | tail _ hm hr ih => exact .tail ih (hST hm) hr

omit [DecidableEq α] in
theorem Via.transGen {S : Finset α} {a b : α} (h : Via r S a b) : Relation.TransGen r a b := by
  induction h with
  | single h => exact .single h
  | tail _ _ hr ih => exact .tail ih hr

/-- Paths through `insert v S` visit `v` at most once, after dropping cycles. -/
theorem via_insert {S : Finset α} {v a b : α} :
    Via r (insert v S) a b ↔ Via r S a b ∨ (Via r S a v ∧ Via r S v b) := by
  constructor
  · intro h
    induction h with
    | single h => exact .inl (.single h)
    | @tail c d _ hm hr ih =>
      rcases Finset.mem_insert.1 hm with rfl | hm
      · rcases ih with ih | ⟨ih, -⟩ <;> exact .inr ⟨ih, .single hr⟩
      · rcases ih with ih | ⟨ih1, ih2⟩
        · exact .inl (.tail ih hm hr)
        · exact .inr ⟨ih1, .tail ih2 hm hr⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact h.mono (Finset.subset_insert _ _)
    · exact (h1.mono (Finset.subset_insert _ _)).trans (Finset.mem_insert_self _ _)
        (h2.mono (Finset.subset_insert _ _))

/-- With every edge inside `U`, the transitive closure only needs
intermediate nodes of `U`. -/
theorem transGen_iff_via {U : Finset α} (hU : ∀ a b, r a b → a ∈ U ∧ b ∈ U) {a b : α} :
    Relation.TransGen r a b ↔ Via r U a b := by
  refine ⟨fun h => ?_, Via.transGen⟩
  induction h with
  | single h => exact .single h
  | tail _ hr ih => exact .tail ih (hU _ _ hr).1 hr

variable (r) [DecidableRel r]

/-- Floyd–Warshall: the `r`-paths between nodes of `U` through intermediate
nodes of `vs`. -/
def fw (U : List α) : List α → Finset (α × α)
  | [] => (U.toFinset ×ˢ U.toFinset).filter fun p => r p.1 p.2
  | v :: vs =>
    let W := fw U vs
    W ∪ (U.toFinset ×ˢ U.toFinset).filter fun p => (p.1, v) ∈ W ∧ (v, p.2) ∈ W

variable {r}

theorem fw_univ {U : List α} (vs : List α) {a b : α} (h : (a, b) ∈ fw r U vs) : a ∈ U ∧ b ∈ U := by
  induction vs with
  | nil => simp only [fw, Finset.mem_filter, Finset.mem_product, List.mem_toFinset] at h; exact h.1
  | cons v vs ih =>
    simp only [fw, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
      List.mem_toFinset] at h
    rcases h with h | h
    · exact ih h
    · exact h.1

theorem mem_fw {U : List α} (hU : ∀ a b, r a b → a ∈ U ∧ b ∈ U) (vs : List α) {a b : α} :
    (a, b) ∈ fw r U vs ↔ Via r vs.toFinset a b := by
  -- every path starts and ends in `U`
  have hends : ∀ {S : Finset α} {a b : α}, Via r S a b → a ∈ U ∧ b ∈ U := by
    intro S a b h
    induction h with
    | single h => exact hU _ _ h
    | tail _ _ hr ih => exact ⟨ih.1, (hU _ _ hr).2⟩
  induction vs generalizing a b with
  | nil =>
    simp only [fw, Finset.mem_filter, Finset.mem_product, List.mem_toFinset, List.toFinset_nil]
    constructor
    · rintro ⟨-, h⟩; exact .single h
    · intro h
      cases h with
      | single h => exact ⟨hU _ _ h, h⟩
      | tail _ hm _ => exact absurd hm (Finset.notMem_empty _)
  | cons v vs ih =>
    simp only [fw, Finset.mem_union, Finset.mem_filter, Finset.mem_product, List.mem_toFinset,
      List.toFinset_cons, ih]
    rw [via_insert]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact .inl h
      · exact .inr h
    · rintro (h | h)
      · exact .inl h
      · exact .inr ⟨⟨(hends h.1).1, (hends h.2).2⟩, h⟩

/-- Deciding `TransGen r` by Floyd–Warshall over a list `U` containing
every edge. -/
theorem transGen_iff_fw {U : List α} (hU : ∀ a b, r a b → a ∈ U ∧ b ∈ U) {a b : α} :
    Relation.TransGen r a b ↔ (a, b) ∈ fw r U U := by
  rw [mem_fw hU, transGen_iff_via (U := U.toFinset)]
  intro a b h; simpa using hU a b h

theorem reflTransGen_iff_fw {U : List α} (hU : ∀ a b, r a b → a ∈ U ∧ b ∈ U) {a b : α} :
    Relation.ReflTransGen r a b ↔ a = b ∨ (a, b) ∈ fw r U U := by
  rw [Relation.reflTransGen_iff_eq_or_transGen, transGen_iff_fw hU, eq_comm]

end ORC11.Closure
