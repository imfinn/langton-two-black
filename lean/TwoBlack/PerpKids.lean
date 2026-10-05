/-
  The perpendicular two-parameter children of the channel parents, discharged by `check2p` (plus slab
  families below a raised base, by `check1`).
-/
import TwoBlack.Check2

namespace TwoBlack

def toFam2? (c : FamD) : Option Fam2 :=
  match c.vs with
  | [δ1, δ2] =>
    if c.blocks.all (fun b => b.2 == [] || b.2 == [0] || b.2 == [1] || b.2 == [0, 1]) then
      some ⟨δ1, δ2, c.blocks.map (fun b => (b.1, b.2.contains 0, b.2.contains 1))⟩
    else none
  | _ => none

theorem toFam2_cells {c : FamD} {F : Fam2} (h : toFam2? c = some F) (a b : Nat) :
    c.cells [a, b] = F.cells a b := by
  unfold toFam2? at h
  split at h
  · next δ1 δ2 hvs =>
    split at h
    · next hall =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [FamD.cells, Fam2.cells, List.map_map]
      apply List.map_congr_left
      intro blk hblk
      have hb := List.all_eq_true.mp hall blk hblk
      simp only [Bool.or_eq_true, beq_iff_eq] at hb
      simp only [Function.comp, FamD.cell, Fam2.cell, hvs]
      rcases hb with ((h0 | h0) | h0) | h0 <;> rw [h0] <;>
        simp [List.foldl, Pt.add_zero] <;> apply Pt.ext' <;> simp
    · simp at h
  · simp at h

def isPerp (c : FamD) : Bool :=
  match c.vs with
  | [δ1, δ2] => δ2.phi δ1.v == 0
  | _ => false

/-- A perpendicular child with its hints and the hints for its slabs `n₁ = n0₁ + i` below the base. -/
def perpOK (c : FamD × List Nat) (H : Hint2) (slabs : List Hint1) : Bool :=
  match toFam2? c.1, c.2 with
  | some F, [n1, n2] =>
    check2p F H && decide (H.b0 ≤ n2) && decide (n1 ≤ H.a0) && slabs.length == H.a0 - n1 &&
      (List.range (H.a0 - n1)).all (fun i => Kid1.ok ⟨F.col2 (n1 + i), n2, slabs.getD i ⟨0, 0, 0, [], 0, ⟨0, 0⟩, 0⟩⟩)
  | _, _ => false

theorem perpOK_sound (c : FamD × List Nat) (H : Hint2) (slabs : List Hint1) (h : perpOK c H slabs = true) :
    FamReaches c := by
  unfold perpOK at h
  split at h
  · next F n1 n2 hF hb =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨⟨hc, hb0⟩, ha0⟩, _⟩, hsl⟩ := h
    intro m ⟨hlen, hge⟩
    rw [hb] at hlen hge
    match m, hlen with
    | [m1, m2], _ =>
      have h1 : n1 ≤ m1 := by have := hge 0 (by simp); simpa using this
      have h2 : n2 ≤ m2 := by have := hge 1 (by simp); simpa using this
      rw [toFam2_cells hF]
      rcases Nat.lt_or_ge m1 H.a0 with hlt | hge'
      · -- a slab below the base
        have hk := hsl (m1 - n1) (by omega)
        rw [show n1 + (m1 - n1) = m1 by omega] at hk
        have := Kid1.reaches _ hk [m2] ⟨rfl, fun i hi => by
          have : i = 0 := by simp at hi; omega
          subst this; simpa using h2⟩
        simp only [toFamD_cells] at this
        rw [initState_sameCells (F.col2_same m1 m2)]
        exact this
      · have := check2p_sound F H hc (m1 - H.a0) (m2 - H.b0)
        rw [show H.a0 + (m1 - H.a0) = m1 by omega, show H.b0 + (m2 - H.b0) = m2 by omega] at this
        exact this
  · simp at h

/-- every perpendicular two-parameter child in `tab` has a matching verified entry in `ptab` -/
def perpCovered (tab : List ChanEntry) (ptab : List ((FamD × List Nat) × Hint2 × List Hint1)) : Bool :=
  tab.all (fun e => e.kids2.all (fun c => !isPerp c.1 || ptab.any (fun p => p.1 == c && perpOK p.1 p.2.1 p.2.2)))

theorem perpCovered_sound {tab : List ChanEntry} {ptab : List ((FamD × List Nat) × Hint2 × List Hint1)}
    (h : perpCovered tab ptab = true) :
    ∀ e ∈ tab, ∀ c ∈ e.kids2, isPerp c.1 = true → FamReaches c := by
  intro e he c hc hp
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h e he) c hc
  simp only [hp, Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨p, _, hpc, hok⟩ := h1
  rw [← hpc]
  exact perpOK_sound p.1 p.2.1 p.2.2 hok

end TwoBlack
