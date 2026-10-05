/-
  Children of the 22 channel parents.  One-parameter children are checked here (`check1` plus direct
  certificates below a raised base); two-parameter children are checked in `PerpData.lean` and `ParData.lean`.
-/
import TwoBlack.Remaining

namespace TwoBlack

/-- A one-corridor family as a general family (near blocks first, then far blocks). -/
def toFamD (F : Fam1) : FamD := ⟨[F.δ], F.near.map (fun b => (b, [])) ++ F.far.map (fun b => (b, [0]))⟩

theorem toFamD_cells (F : Fam1) (n : Nat) : (toFamD F).cells [n] = F.cells n := by
  simp [toFamD, FamD.cells, FamD.cell, Fam1.cells, List.map_append, List.map_map, Function.comp_def,
    List.foldl]

/-- A one-parameter child: family, the base it must cover, and checker hints (base `H.n ≥ base`). -/
structure Kid1 where
  F : Fam1
  base : Nat
  H : Hint1

def Kid1.ok (k : Kid1) : Bool :=
  check1 k.F k.H && (List.range (k.H.n - k.base)).all (fun i => certB (k.F.cells (k.base + i)) 6000)

theorem Kid1.reaches (k : Kid1) (h : k.ok = true) : FamReaches (toFamD k.F, [k.base]) := by
  simp only [Kid1.ok, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hc, hslab⟩ := h
  intro m ⟨hlen, hge⟩
  match m, hlen with
  | [n], _ =>
    have hn : k.base ≤ n := by have := hge 0 (by simp); simpa using this
    simp only at hn ⊢
    rw [toFamD_cells]
    rcases Nat.lt_or_ge n k.H.n with hlt | hge'
    · have := certB_sound _ _ (hslab (n - k.base) (by omega))
      rw [show k.base + (n - k.base) = n by omega] at this
      exact this
    · have := check1_sound k.F k.H hc (n - k.H.n)
      rw [show k.H.n + (n - k.H.n) = n by omega] at this
      exact this

structure ChanEntry where
  z0 : Pt
  kids1 : List Kid1
  kids2 : List (FamD × List Nat)

def ChanEntry.kids (e : ChanEntry) : List (FamD × List Nat) :=
  e.kids1.map (fun k => (toFamD k.F, [k.base])) ++ e.kids2

def kidsIn (tab : List ChanEntry) (F : Fam1) : List (FamD × List Nat) :=
  match tab.find? (fun e => [e.z0] == F.far) with
  | some e => e.kids
  | none => []

theorem mem_kidsIn {tab : List ChanEntry} {F : Fam1} {c : FamD × List Nat} (h : c ∈ kidsIn tab F) :
    ∃ e ∈ tab, (∃ k ∈ e.kids1, c = (toFamD k.F, [k.base])) ∨ c ∈ e.kids2 := by
  unfold kidsIn at h
  split at h
  · next e he =>
    refine ⟨e, List.mem_of_find?_eq_some he, ?_⟩
    simp only [ChanEntry.kids, List.mem_append, List.mem_map] at h
    rcases h with ⟨k, hk, rfl⟩ | h
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr h
  · simp at h

/-- **Theorem A from the two remaining mathematical statements.**  If the child partition (Lemma 6.3,
one corridor) holds for the 22 channel parents with the child lists in `tab`, every one-parameter child
passes its check, and every two-parameter child reaches the highway (Proposition 5.2, two corridors), then
every state with at most two black cells reaches the highway. -/
theorem two_black_of_partition (tab : List ChanEntry) (hcp : ConcreteParentsOK)
    (hpart : ∀ p ∈ level1Families, ChildPartition1 p.1 40 (kidsIn tab p.1))
    (hk1 : tab.all (fun e => e.kids1.all Kid1.ok) = true)
    (hk2 : ∀ e ∈ tab, ∀ c ∈ e.kids2, FamReaches c) :
    ∀ s, AtMostTwoBlack s → ReachesP104 s := by
  apply two_black_of
  apply parentsOK_of hcp
  apply channelParentsOK_of (kidsIn tab) hpart
  intro p _ c hc
  obtain ⟨e, he, ⟨k, hk, rfl⟩ | h2⟩ := mem_kidsIn hc
  · have := List.all_eq_true.mp (List.all_eq_true.mp hk1 e he) k hk
    exact Kid1.reaches k this
  · exact hk2 e he c h2

end TwoBlack
