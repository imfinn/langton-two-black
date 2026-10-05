# Every Langton's ant start with at most two black cells reaches the period-104 highway

**Draft, 5 October 2026 (revision 4).** Standalone write-up of the two-cell result from the research notes "finite crossing certificate" (*note 1*), "attacking the general case" (*note 2*) and "a highway calculus" (*note 3*).
- Revision 2 replaced the proof sketches of the structure and completeness lemmas with complete proofs and checkable hypotheses, and reran the computation under them.
- Revision 3 adds a Lean 4 formalization (§9). It repairs a gap in the proof of Lemma 4.1 that the formalization found. It makes Lemma 6.1 self-contained and restricts the partition lemma to the case Theorem A uses, d ≤ 1, with an explicit image lemma. It also adds a span-ownership guard and an exact-arithmetic coverage test.
- Revision 4 completes the formalization. Lemma 6.3 for the 22 channel parents is proved in Lean by a new one-step argument (Lemma 6.4, Corollary 6.5), so Theorem A is machine-checked with no remaining hypothesis.

## Abstract

We prove, with computer assistance, that the classical Langton's ant started from any configuration with at most two black cells, placed anywhere in the plane, with the ant at any cell and facing any direction, eventually follows a translating highway of period 104 with one of the four standard drifts. The computation also identifies it as the standard highway in every case it certifies.

The proof organizes all such starts into finitely many *corridor families*. A family is an infinite set of configurations parametrized by the lengths of highway corridors joining debris sites. A *corridor lemma* shows that lengthening a corridor by one highway period inserts exactly one period into every traversal of that corridor and changes nothing else. One verified run therefore settles a whole family.

A recursive enumeration classifies the second cell by the phase of the first cell's trajectory in which it is first read. We prove that this enumeration is exhaustive.

The verifying computation simulated about 134 billion ant updates. It was cross-checked in four further ways:
- 201,124 step-exact predictions for additional family members;
- a direct test of the exhaustiveness lemma on larger members;
- an independent re-implementation of the family checker in a second language;
- an independent highway detector, applied to sampled configurations.

**Theorem A is proved in Lean 4 (§9), with no hypotheses and no `sorry`.** The formalization proves in general:
- the half-plane certificate and the corridor lemma;
- Lemma 5.1 (with a checkable form of (H3)) and Proposition 5.2 for one and two corridors, with sound executable checkers;
- tail descent;
- the partition lemma for parents without a corridor;
- for the one-corridor channel parents, a one-step lemma (Lemma 6.4) and a partition check that is sound for every member.

The specific cases are discharged by verified computation. That covers about 4.5 million concrete cases, about 100,000 families, and the partition check on each of the 22 channel parents. As a by-product the formalization gives an independent proof of the one-black theorem.

The one-black-cell case was proved earlier, and checked in Lean, by Hao Ke (2026).

---

## 1. Statement and context

At each update the ant reads the colour of its cell. It turns right on white and left on black, flips the cell, and steps forward. A configuration is a finite set of black cells; every other cell is white.

**Theorem A.** Let Q ⊂ ℤ² have at most two cells. From the board whose black cells are Q, with the ant at any cell and facing any direction, the ant eventually follows a period-104 highway with a standard drift. That is, from some time on, what the ant observes at each update (its cell, its heading and the colour it reads) repeats every 104 updates, up to a translation by one of the four vectors (±2, ±2).

This is Ke's predicate, and it is the statement proved in Lean (§9). The C++ checker proves more for every run it certifies: the turn word is the 104-letter word of the blank-start highway, up to a cyclic shift. That identification is not part of the Lean statement.

**Context.**
- The ant's trajectory is unbounded from every finite start (Bunimovich–Troubetzkoy; the extremal-corner argument attributed to Cohen and Kong, recorded by Gale 1993).
- The highway conjecture, that every finite start reaches a highway, is open.
- Gajardo, Lutfalla and Rao (2024) study highways of generalized ants. Lutfalla (2025) shows that some generalized ants have finite starts that never reach a highway.
- For the classical ant, Hao Ke (2026) gives a Lean-checked proof that every start with **exactly one** black cell reaches the period-104 highway. His proof classifies first contact into 22 affine channels, 21 ordinary and one "phase-72" backscattering channel. He states that his work does not cover two black cells.

Dirgová Luptáková and Pospíchal (2015) explored perturbed initial settings experimentally on a finite grid. They observed that the highway was always reached and noted that no proof is known. Experiments of this kind cover cells within a bounded window. The present result is, to our knowledge, the first to cover two black cells at unbounded relative distance. This is a statement about the literature we found, not a priority claim.

Our method agrees with Ke's on the one-cell case. The 22 channels are the 22 tail classes of Section 6, and his phase-72 channel is our single two-transit shuttle class.

We checked this in coordinates; both works use the same conventions (north = +y, blank drift (−2,−2)).
- Ke's entry state E, after 9,977 updates, has the ant at (−15, 10), so his exceptional head is h₇₂ = (−17, 2).
- Our shuttle class has representative (−57, −38) = h₇₂ + 20·(−2,−2), so it lies on his channel.
- None of our other 21 representatives lies on that channel.
- Two transits give a delay of 2 · 104 = 208 updates per unit of depth (Proposition 5.2), which is his t_hit(n) = t_hit(0) + 208n.
- At depth 40 the reverse highway runs from update 67,335 for 59 periods. Both our C++ checker and the independent Python simulator find it. Two features are new here: the corridor calculus, which handles any number of corridors, and the recursive classification.

## 2. Preliminaries

### 2.1 Runs

Translations and quarter-turn rotations commute with the dynamics, so we place the ant at the origin facing north. The **run** of a configuration Q is the sequence of states (B(t), p(t), h(t)), where:
- B(t) is the set of black cells before update t;
- p(t) is the cell read at update t;
- h(t) is the heading on arrival at p(t).

We write φ_v(z) = sgn(vₓ)x + sgn(v_y)y for a diagonal vector v = (±2, ±2); then φ_v(v) = 4.

**Lemma 2.1 (first-difference coupling).** Suppose two runs have states at times t and t′ that agree on a set G ⊂ ℤ² under a translation τ, so B′(t′) ∩ τG = τ(B(t) ∩ G), and have poses related by τ. Then for every k ≥ 0 such that the first run reads only cells of G at times t, …, t+k−1, the states at times t+k and t′+k are related in the same way.

*Proof.* Induction on k. The cell read lies in G, so both runs read the same colour, make the same turn, perform the same flip (inside G), and move by the same vector. ∎

**Lemma 2.2 (half-plane certificate; note 1, Lemma 1).** Let u ≠ 0 and let G = {z : u·z > A}. Suppose that at times s and t = s + P:
- the poses satisfy p(t) = p(s) + u and h(t) = h(s);
- the run reads only cells of G at times s, …, t;
- the boards satisfy B(t) ∩ (G + u) = (B(s) ∩ G) + u.

Then p(r+P) = p(r) + u and h(r+P) = h(r) for every r ≥ s.

*Proof.* By Lemma 2.1, the run from t is the u-translate of the run from s for as long as the run from s stays in G. Suppose the run from s first leaves G at some time r > t. Then the run from t first leaves G + u at time r + P. But G + u ⊂ G, and the run from t passes through p(r), which is outside G and hence outside G + u, at time r < r + P. This is a contradiction. ∎

A **certificate** is an instance of Lemma 2.2 with P = 104 and u diagonal, with one more requirement: every cell first touched before s − 312 lies outside G. A certificate is **standard** if the 104 colours read on [s, t) form the blank-start highway word up to a cyclic shift. A standard certificate proves that the run eventually follows the standard highway.

The checker finds the first such t that is a multiple of 104 with t ≥ 520. It recovers B(s) from B(t) by undoing the reads of [s, t), which the reversibility of the update makes exact.

### 2.2 Families

A **family** 𝓕 consists of:
- parameters i = 0, …, d−1, with diagonal drifts vᵢ and functionals φᵢ = φ_{vᵢ};
- blocks b with base offsets b⁰ and masks M_b ⊂ {0, …, d−1}.

The member at n ∈ ℕ^d has black cells b(n) = b⁰ + Σ_{i∈M_b} nᵢvᵢ. We call b *beyond* corridor i if i ∈ M_b, and write eᵢ for the i-th unit vector.

## 3. Corridor data and the conditions

Fix a member n and its run, observed up to the time T of its first standard certificate. Fix a parameter i, and write φ = φᵢ and v = vᵢ.

**Transits and switch times.**
1. *Endpoints.* D₀ is the largest φ over the origin and the blocks not beyond i; C₀ is the smallest φ over the blocks beyond i. We require C₀ − D₀ ≥ 60. The midline is μ = (D₀ + C₀)/2, rounded toward zero.
2. *Periodic runs.* A periodic run is a maximal interval [b, e] of length at least 520 on which p(w+104) − p(w) = σv and h(w+104) = h(w), with σ = ±1 fixed.
3. *Transits.* Every time w at which the path crosses μ (that is, φ(p(w)) and φ(p(w+1)) lie on opposite sides) must fall in [b, e+104] for some periodic run. One exception: a crossing after the certificate's start s counts if the certified drift is ±v. A periodic run containing an odd number of crossings is a **transit**, and an even number is rejected. Transits alternate in direction, the first having σ = +1 ("outward").
4. *Switch time.* For each transit, the switch time m is the first w ∈ [b, e] with w + 104 < T that minimizes |φ(p(w)) − μ|.
5. *Span.* The transit's **span** is the largest interval inside [b, e+104] that contains m and on which D₀ − 16 ≤ φ(p) ≤ C₀ + 16. It must end at least 104 updates after m. A single highway may traverse several parallel corridors in series; each corridor owns only the part of it inside its own stretch.

**Sides and zones.**
- Reads outside all spans are *site reads*.
- A site read is on the *near side* if an even number of spans end before it, and on the *far side* otherwise.
- **D** is the maximum of D₀ and the φ-values of near-side site reads. **C** is the minimum of C₀ and the φ-values of far-side site reads.
- The **band** is D + 8 < φ < C − 8.
- For a cell z, its **index** is ℓ(z) = ⌊(φ(z) − D)/4⌋.

**Conditions on corridor i.**
- **(C1)** D + 40 < C.
- **(C2)** Every switch time m satisfies D + 16 < φ(p(m)) < C − 16, p(m+104) = p(m) + σv and h(m+104) = h(m).
- **(C3)** At every switch time m, B(m+104)(w) = B(m)(w − σv) for every w in the band.
- **(C4)** Let m₀ = 0 < m₁ < m₂ < … be the switch times. On [m_j, m_{j+1} + 104), with the last interval running to T, every read satisfies φ < C − 16 if j is even and φ > D + 16 if j is odd.
- **(C5)** The certified highway stays in the final relation region forever. If the number of transits is even, its drift has φ(u) ≤ 0 and its φ-values on [s, T) are below C − 16. If odd, φ(u) ≥ 0 and its φ-values on [s, T) are above D + 16.

**Conditions between corridors.**
- **(S8)** Corridors with parallel drifts have disjoint bands.
- **(H1′)** For i ≠ j, no insertion window [m, m+104] of corridor i meets a span of corridor j.
- **(H3)** For every ordered pair i ≠ j with vⱼ = ±vᵢ, let Δ = φⱼ(vᵢ) ∈ {±4}.
  - *(a) Side.* Corridor j's band lies in corridor i's far zone (σ = far, i.e. φᵢ ≥ Cᵢ) or near zone (σ = near, φᵢ ≤ Dᵢ).
  - *(b) Transits.* Every span of j lies in corridor-i phases of side σ, outside i's insertion windows. (A corridor-i phase changes after each window [m, m+104].)
  - *(c) Foreign material.* The foreign items are: reads inside i's insertion windows, reads on i's other side, the blocks on i's other side, and the origin when σ = far. Set ρ = Δ if σ = near and ρ = −Δ if σ = far. If ρ > 0, all foreign items have φⱼ ≥ Cⱼ; if ρ < 0, all have φⱼ ≤ Dⱼ. If the certified highway is foreign, its φⱼ-drift has the sign of ρ, or is zero.
  - *(d) Extrema.* If ρ > 0, Cⱼ is attained by non-foreign material, and C₀ⱼ by a non-foreign block. If ρ < 0, the same holds for Dⱼ and D₀ⱼ.

A family is **verified at n** if the run of member n has a standard certificate and satisfies (C1)–(C5) for every corridor, together with (S8), (H1′) and (H3).

## 4. The corridor lemma

Fix n and i satisfying (C1)–(C5) for corridor i. Let m₁ < … < m_J be its switch times, and set Λ(t) = 104 · #{j : m_j < t}. Let ε(t) ∈ {0, 1} be the parity of the number of switches before t: ε = 1 means far, the relation after an outward switch.

**Lemma 4.1 (corridor lemma).** Run n + eᵢ is run n with one period inserted at every switch. Precisely, for every time t outside the insertion windows:

* **Near phase** (ε(t) = 0). The poses satisfy p_{n+eᵢ}(t+Λ(t)) = p_n(t). The boards satisfy
  - B_{n+eᵢ}(t+Λ)(z) = B_n(t)(z) for φ(z) < C − 4, and
  - B_{n+eᵢ}(t+Λ)(z) = B_n(t)(z − v) for φ(z) ≥ C − 12.
* **Far phase** (ε(t) = 1). The poses satisfy p_{n+eᵢ}(t+Λ(t)) = p_n(t) + v. The boards satisfy
  - B_{n+eᵢ}(t+Λ)(z) = B_n(t)(z − v) for φ(z) > D + 12, and
  - B_{n+eᵢ}(t+Λ)(z) = B_n(t)(z) for φ(z) ≤ D + 16.

Inside a window [m, m+104], both descriptions hold, with lags Λ and Λ + 104. The run of n + eᵢ follows the run of n in this way forever, and its certificate time is T + 104J.

*Proof.* This proof is machine-checked in Lean: theorem `corridor` in `TwoBlack/Corridor.lean`. We follow it.

Write R_id for the near-phase statement and R_tr for the far-phase statement, each taken at a given lag. For a relation interval q, let I_q = [m_q, m_{q+1} + 104], closed at the right end. Here m₀ = 0, and I_J = [m_J, ∞). We show by induction on q that the relation of parity q holds on all of I_q, at lag 104q. Because consecutive intervals overlap exactly on the windows, this is the statement.

1. **Persistence** (`Rid_persist`, `Rtr_persist`).
   - Suppose R_id holds at a time and run n reads only cells with φ < C − 16 for k steps. Then it still holds k steps later. The identity half is Lemma 2.1 on {φ < C − 4}. For the translated half, run n + eᵢ does not visit any z with φ(z) ≥ C − 12, because its positions equal run n's. And run n does not visit z − v, because φ(z − v) ≥ C − 16.
   - R_tr is symmetric: Lemma 2.1 on {φ > D + 8} with translation v, and the cells with φ ≤ D + 16 are visited by neither run.

   By (C4), run n reads in the correct region throughout I_q.
2. **Start.** R_id holds at time 0, as an initial relation between the two configurations: the far blocks are translated by v and the near blocks are untouched. For one-corridor families this is proved in general (`fam_init`).
3. **Outward switch at m** (`switch_out`). Suppose R_id holds at m + 104, at lag L. We derive R_tr at m, at lag L + 104. During the window, (C4) puts every read in D + 16 < φ < C − 16, so cells outside that range keep their colour through the window.
   - *Pose:* p′ = p(m + 104) = p(m) + v by (C2).
   - *Translated half, φ(w) > D + 8,* writing z = w + v:
     - if φ(z) < C − 8, then B′(z) = B_n(m + 104)(z) = B_n(m)(z − v), by R_id and then (C3);
     - if φ(z) ≥ C − 12, then B′(z) = B_n(m + 104)(z − v) = B_n(m)(z − v), by R_id and then because z − v has φ ≥ C − 16 and so is untouched in the window.
   - *Identity half, φ(z) ≤ D + 16:* B′(z) = B_n(m + 104)(z) = B_n(m)(z), since z is untouched in the window.
4. **Inward switch at m** (`switch_in`). Suppose R_tr holds at m + 104, at lag L. We derive R_id at m, at lag L + 104.
   - *Pose:* p′ = p(m + 104) + v = p(m).
   - *Identity half, φ(z) < C − 4:*
     - if φ(z) > D + 12, then R_tr at w = z − v and (C3) give B′(z) = B_n(m)(z);
     - otherwise, R_tr's identity half and the untouched window give the same.
   - *Translated half, φ(z) ≥ C − 12:* B′(z) = B_n(m + 104)(z − v) = B_n(m)(z − v), by R_tr and then because z − v has φ ≥ C − 16.

   The earlier draft omitted this translated half after an inward switch. It is needed, and holds by this argument; the formalization found the omission.
5. **After the last switch.** The last interval I_J is unbounded. By (C4), (C5) and the periodicity of the certified highway, run n reads in the final relation region forever. So the relation never breaks. ∎

*Remarks.*
- (C2)'s range condition D + 16 < φ(p(m)) < C − 16 follows from (C4) on the window, so the Lean statement omits it.
- The Lean statement also needs consecutive windows to be disjoint, m_{j+1} > m_j + 104. The checker verifies this.

**Corollary 4.2.** For every k ≥ 1, run n + keᵢ is run n with k periods inserted at every switch. For one-corridor families, this is proved in Lean by iterating Lemma 4.1 with Lemma 5.1(a) (`corridor_succ`), giving Proposition 5.2 (`corridor_family`, `check1_sound`).

## 5. Structure preservation

**Lemma 5.1.** Suppose 𝓕 is verified at n. Then for every i and every k ≥ 1, 𝓕 is verified at n + keᵢ, with the following data:

(a) **Corridor i.** The same number of transits; zones (Dᵢ, Cᵢ + 4k); switch times at the translated copies of the original ones.

(b) **Corridor j ⊥ vᵢ.** The same transits, zones and switch-time positions, at the images of the original times.

(c) **Corridor j with vⱼ = ±vᵢ.** The same transits, at the images of the original times. The zones, the midline, the span bounds and the switch positions all shift by s = Δk if σ = far and by 0 if σ = near.

(d) (S8), (H1′) and (H3) hold in run n + keᵢ.

These statements cover the six points one must check for each other corridor j:
1. the temporal order of its phases;
2. the correspondence of its transits;
3. its switch times;
4. its board relation (C3);
5. its zones;
6. the absence of any new interaction with another corridor.

*Proof.* Induction on k; we give the step from n to n + eᵢ.

**(a)** Choose the new switch time m′ = m + Λ + 104, the image of m under the post-switch relation. Then p(m′) = p_n(m) + v for an outward switch. Its φ-value is φ(p_n(m)) + 4, which lies in (D + 20, C − 12) ⊂ (D + 16, (C + 4) − 16). The pose condition holds because R_tr is valid on [m, m + 104]. For (C3) at m′ and w in (D + 8, C − 4):
- if φ(w) > D + 16, R_tr at both times reduces the claim to run n's (C3) at w − v, which lies in run n's band;
- if D + 8 < φ(w) ≤ D + 16, both sides read near content that is frozen and identical. Here run n's (C3) at w, together with B_n(m)(w − v) = B_n(m+104)(w − v) (run n reads only φ > D + 16 during [m, m+104]), gives the claim.

For the zones: near-side site reads are unchanged, and far-side site reads and far blocks move up by 4, so the zones are (D, C + 4). The block endpoints become (D₀, C₀ + 4), so μ′ = μ + 2. Near-side reads stay below μ and far-side reads stay above μ + 4, so every crossing of μ′ lies in a lengthened transit. Span bounds and (C4) shift consistently; the windows satisfy both relations; (C5) is a translated or identical copy. Inward switches are symmetric.

**(b) vⱼ ⊥ vᵢ.** Translation by vᵢ leaves φⱼ unchanged. By (H1′), each span of j lies inside a single phase of corridor i, so it maps to a translated (or identical) copy shifted by a constant lag. Its switch maps to the image time, and (C2) carries over. For (C3) at the image time, Corollary 4.2 relates run n + eᵢ's board to run n's board by z ↦ z − j(z)vᵢ. Here j(z) depends only on φᵢ(z), and w − σvⱼ has the same φᵢ as w. So (C3) at w in run n + eᵢ reduces to (C3) at w − j(w)vᵢ in run n. That cell is still in j's band, because φⱼ(vᵢ) = 0.

Every read of run n + eᵢ is a copy of a read of run n with the same φⱼ: inserted window reads are copies of i's window reads. By (H1′), an i-window contains no j-switch window, so every copy occurs in the same corridor-j interval as its original. Hence (C4), the zones and the crossing structure of j are unchanged, and the certified highway's φⱼ-values and drift are unchanged, giving (C5).

**(c) vⱼ = ±vᵢ.** By (H3a,b), all of j's spans, switch windows and band content lie on side σ of corridor i, away from i's windows. They shift uniformly by s. The foreign items of (H3c), including the inserted i-window copies (which are translates of foreign window reads by 0, vᵢ, …), move relative to j's structure by ρ per step, so they move away from j's band. Hence they never enter it and never cross j's midline.

By (H3d), the relevant extremum of j's zones, and of its block endpoints, is attained by non-foreign material. The other extremum receives no foreign contribution at all, because foreign items lie in the single zone Z given by the sign of ρ. So Dⱼ, Cⱼ, D₀ⱼ and C₀ⱼ all shift by exactly s, and μⱼ shifts by s. Foreign reads in Z already satisfied j's relation constraint at their times, since a foreign read in the far zone during a near phase would already violate (C4). Moving away preserves that. So (C1)–(C5) hold with every quantity shifted by s.

**(d)** Insertion windows and spans map monotonically, so (H1′) persists. Sides, foreign sets and the extrema conditions of (H3) are preserved by the uniform shifts just described. This holds for (i, j) directly, and for (j, i) because corridor i's zones grow only at the end facing away from corridor j's material. (S8) persists because parallel bands shift together with their zones. ∎

**Proposition 5.2.** If 𝓕 is verified at n, then every member n′ ≥ n (componentwise) eventually follows the standard highway, with certificate time

T(n′) = T(n) + Σᵢ 104 · tᵢ · (n′ᵢ − nᵢ),

where tᵢ is the number of corridor-i transits.

*Proof.* Raise one parameter at a time, applying Lemma 5.1 and then Lemma 4.1. ∎

**Adaptive bases.** If verification fails at n₀, the checker raises the offending parameter and retries. Once 𝓕 is verified at some n ≥ n₀, every member with some coordinate nᵢ′ ∈ [n₀ᵢ, nᵢ) is covered by the family obtained by freezing that coordinate (a *slab*), which is proved recursively.

## 6. Adding one cell anywhere

Let 𝓕 be verified at n. Write τ_div for the last first-read time of a block; blocks never read are ignored. A **new cell** is a cell S, not a block, that the run first reads after τ_div. Since the run of 𝓕(n) ∪ {S} agrees with the run of 𝓕(n) until S is read (Lemma 2.1), to add one cell anywhere it suffices to classify new cells.

**Scope.** Theorem A applies the extension only to parents with **at most one parameter**: the blank start, the level-1 entries, and the slabs of level-1 families. This section is written for that case, d ≤ 1. Where it matters, we write v for the drift of the single corridor and k = n′ − n. The general case d ≥ 2, needed for three cells, is discussed at the end of the section.

**Children.** For each new cell z of the base run, first read at time t, the extension creates one of the following.

1. **Site child**, if t is outside the span of the corridor and before the certificate start s. The cell z is attached to the frame of that phase: it moves with the corridor (its mask contains the parameter) if and only if the ant is on the far side at time t.
2. **Footprint child**, if t lies in a span:
   - near child if ℓ(z) < 10, not moving with the corridor;
   - far child if ℓ(z) > 10, moving with the corridor;
   - **split child** if ℓ(z) = 10, one per footprint class. The corridor is replaced by two corridors of the same drift, a near part of length t′ ≥ 10 and a far part of length s′ ≥ n − 10. The blocks that were beyond the corridor become beyond both.
3. **Tail-near child**, if t ≥ s but t is before the tail cutoff T₂ (defined below). The mask is the final frame.
4. **Tail child.** Let ψ = φ_u for the certified drift u, so that ψ(u) = 4. Let t₁ = s + 104L for the least L ≥ 1 such that every read in [t₁, t₁+104) has ψ greater than ψ_pre + 4. Here ψ_pre is the largest ψ of any read before s and of any block. Set T₂ = t₁ + 104·40. Each cell z₀ first read in [t₁, t₁+104) gives a family with a new corridor of drift u, with S = z₀ + j·u for j ≥ 40, beyond the final frame. (Cells first read in [t₁, T₂) are the members j < 40 and appear among the tail-near children.)

*Span ownership.* With one corridor there is nothing to decide: spans of different corridors cannot overlap. For use with d ≥ 2, the checker now rejects any extension in which a new cell is first read inside the spans of two different corridors. On all parents of Theorem A the guard never fires; the level-1 extension output is byte-identical with and without it.

**(F1) Footprint periodicity.** For every span that lies after τ_div, both of the following must be invariant under ±v on the index range 10 ≤ ℓ ≤ ℓ_hi:
- the set of cells read during the span;
- the subset of new cells.

Here ℓ_hi is one more than the largest index of a switch position.

**Lemma 6.1 (descent along the tail).** If a cell z is first read at a time m ≥ t₁ + 104, then z − u is first read at time m − 104. Consequently, if z is first read at m ≥ t₁ + 104j, then z = z₀ + j·u, where z₀ = p(m − 104j) is first read at m − 104j. In particular every cell first read at a time m ≥ T₂ is z₀ + j·u for the cell z₀ = p(m − 104j) first read in [t₁, t₁+104), with j ≥ 40.

*Proof.* By Lemma 2.2 the run is periodic after s: p(w + 104) = p(w) + u for every w ≥ s. Write any time w ≥ t₁ as w₀ + 104i with w₀ ∈ [t₁, t₁+104). Then ψ(p(w)) = ψ(p(w₀)) + 4i > ψ_pre + 4 + 4i. In particular every read at a time ≥ t₁ + 104 has ψ > ψ_pre + 8.

Now let z be first read at m ≥ t₁ + 104. Since m − 104 ≥ s, periodicity gives p(m − 104) = z − u, so z − u is read by time m − 104. Suppose it were read earlier, at some r < m − 104.
- If r ≥ s, periodicity gives p(r + 104) = z with r + 104 < m, contradicting the choice of m.
- If r < s, then ψ(z − u) ≤ ψ_pre. But ψ(z − u) = ψ(z) − 4 > ψ_pre + 4, a contradiction.

So z − u is first read at m − 104. The second statement follows by applying the first j times; each application is legitimate because the times m − 104i, for i < j, are all ≥ t₁ + 104. For the last statement, take j with m − 104j ∈ [t₁, t₁+104); then m ≥ T₂ forces j ≥ 40. ∎

**Lemma 6.2 (images of reads).** Let d = 1, suppose 𝓕 is verified at n, and let n′ = n + k. By Lemma 4.1 iterated with Lemma 5.1(a) (Corollary 4.2), every read of run n′ is of exactly one of two kinds.
- *Image reads.* For each time t of run n outside the insertion windows, run n′ reads the cell ι_t(p(t)) at a time θ(t), where ι_t(z) = z in a near phase and ι_t(z) = z + kv in a far phase. The map θ is strictly increasing.
- *Inserted reads.* For each switch m, run n′ reads the cells p(w) + jv, for w ∈ [m, m+104] and 0 ≤ j ≤ k, inside the stretched window. (For an inward switch, read p(w) − jv + kv.)

Then:
1. every window read of run n, and hence every inserted read of run n′, has D + 16 < φ < C − 16 + 4k;
2. every near-side site read z has φ(z) ≤ D, and every far-side site read z has φ(z) ≥ C;
3. if z is a site read of run n at time t, then ι_t(z) is first read in run n′ at time θ(t) if and only if z is first read in run n at time t.

*Proof.*
1. Each window [m, m+104] lies in two consecutive relation intervals of (C4), one of each parity. So its reads satisfy both φ < C − 16 and φ > D + 16. Translating by jv with 0 ≤ j ≤ k adds 4j to φ.
2. This is the definition of D and C as the maximum and minimum over the near-side and far-side site reads.
3. Take a near-side site read z at time t, so φ(z) ≤ D. Every earlier read of the same cell z in run n happened in a near phase, because far-phase reads have φ > D + 16 by (C4). Such reads have image z at an earlier image time. Conversely, suppose run n′ reads z = ι_t(z) at a time before θ(t). That read is either an image read or an inserted read.
   - It cannot be an inserted read, since those have φ > D + 16 by part 1.
   - It cannot be the image of a far-phase read p(t″), since φ(p(t″) + kv) > D + 16 + 4k > φ(z).
   - So it is the image of a near-phase read p(t″) = z with t″ < t, because θ is increasing.

   Hence z is first read in run n′ at θ(t) exactly when it is first read in run n at t. Far-side site reads are symmetric: ι_t(z) = z + kv has φ ≥ C + 4k. Near-phase reads have φ < C − 16 by (C4), and inserted reads have φ < C − 16 + 4k by part 1. ∎

**Lemma 6.3 (partition).** Let d ≤ 1, suppose 𝓕 is verified at n, and suppose (F1) holds. Then for every member n′ ≥ n, every new cell S of run n′ belongs to at least one of the following categories, and the configuration 𝓕(n′) ∪ {S} is the corresponding child member:

| Category | Child | Child parameters |
|---|---|---|
| Site | site child of the cell ι⁻¹(S) | n′ |
| Near footprint (ℓ < 10) | near child | n′ |
| Far footprint (ℓ > 10 + k) | far child | n′ |
| Middle footprint (10 ≤ ℓ ≤ 10 + k) | split child | (t′, s′) = (ℓ, n′ − ℓ) |
| Tail-near | tail-near child | n′ |
| Tail | tail child | (n′, j), j ≥ 40 |

For d = 0 there is no corridor, run n′ is run n, and only the site, tail-near and tail rows occur.

*Proof.* We place each new cell S of run n′, first read at time t′, by the kind of read made at t′.
- *Site.* Suppose t′ = θ(t) for a site time t of run n (outside spans, before s). By Lemma 6.2(3), S = ι_t(z) where z = p(t) is first read at t, so z is a new cell of run n in the site category. Its site child has the moving bit set exactly when ι_t adds kv, so the child member at parameter n′ is 𝓕(n′) ∪ {S}.
- *Footprints.* Suppose t′ falls inside the image of a span, including its stretched window. In run n′ the span's reads are three pieces:
  - the images of the span's reads before the window, which are identical copies;
  - the inserted copies p(w) + jv, for 0 ≤ j ≤ k;
  - the images of the reads after the window, translated by kv.

  On a periodic run, p(w + 104) = p(w) + v. So in run n′ these three pieces form the same periodic highway segment as in run n, lengthened by k periods. By (F1), on the index range 10 ≤ ℓ ≤ ℓ_hi of run n, both the span's read set and its new cells are the periodic pattern of that highway. In run n′, the same holds on 10 ≤ ℓ′ ≤ ℓ_hi + k. Above that range, run n′ is the kv-translate of run n above ℓ_hi. Below index 10, run n′ is identical to run n. Hence the new cells of run n′ at index ℓ′ are:
  - for ℓ′ < 10: those of run n (near children);
  - for 10 ≤ ℓ′ ≤ 10 + k: the class representatives at index 10, translated by (ℓ′ − 10)v (split child with t′ = ℓ′ ≥ 10, s′ = n′ − ℓ′ ≥ n − 10);
  - for ℓ′ > 10 + k: those of run n at index ℓ′ − k, translated by kv (far children).
- *Tail-near and tail.* The certified highway of run n′ is the image of that of run n, with the same drift u, and by (C5) it lies in the final relation region. So ψ_pre(n′) is attained by the image of the same material, shifted by kv when that material moves with the corridor, and the margin defining t₁ holds for the image window. New cells first read in [s, T₂) of run n′ are images of tail-near cells of run n, by the argument of the site case. Those first read at or after T₂ are covered by Lemma 6.1. ∎

### 6.1 The channel parents: a one-step proof of Lemma 6.3

Theorem A uses Lemma 6.3 with d = 1 only for the 22 channel parents. Each has one far block b(n) = z₀ + n·v on drift v = (−2,−2), base n = 40, and no near block. 21 of them have one switch; the shuttle has two. For these parents the formal proof (§9) replaces the footprint argument by a shorter one. It needs neither (F1) nor Lemma 6.2. Here a **new cell of member n** is a cell that the run of member n reads, but not up to the time τ(n) at which it first reads its block.

In this section the zones D < C are data rather than the extremes of §3. For one corridor, Lemmas 4.1 and 5.1(a) use D and C only through (C1)–(C4) and the initial relation, so any values that satisfy these conditions may be used. The formal proof treats them the same way.

**Lemma 6.4 (one step).** Suppose a channel parent satisfies the corridor hypotheses of Lemma 4.1 for the members n and n + 1, with J ∈ {1, 2} switches m₁ < m₂ and zones D < C. Suppose also the following:
- member n first reads its block b at τ, with m₁ + 104 ≤ τ, and τ < m₂ if J = 2;
- φ(b) ≥ C − 4;
- (P-out) p(t + 104) = p(t) + v whenever t < m₁ and φ(p(t)) > D + 12;
- (P-ret) if J = 2: p(t + 104) = p(t) − v whenever t ≥ m₂ and φ(p(t)) > D + 16.

Then member n + 1 first reads its block at τ + 104, and for every new cell S of member n + 1:
- if φ(S) ≤ D + 16, then S is a new cell of member n;
- if φ(S) > D + 16, then S − v is a new cell of member n.

*Proof.* Write p and p′ for the read positions of members n and n + 1. Lemma 4.1, applied to positions only, gives:
- p′(t) = p(t) for t ≤ m₁ + 104;
- p′(t + 104) = p(t) + v for m₁ ≤ t (and t ≤ m₂ + 104 if J = 2);
- p′(t + 208) = p(t) for t ≥ m₂, if J = 2.

Every time after m₁ + 104 is t + 104 with m₁ ≤ t (and t < m₂ + 104 if J = 2), the second form, or t + 208 with t ≥ m₂, the third form. By (C4), reads at times t < m₁ + 104 have φ < C − 16, and reads in relation interval 1, m₁ ≤ t (< m₂ + 104 if J = 2), have φ > D + 16.

*The block.* p′(τ + 104) = p(τ) + v = b + v. Could member n + 1 read b + v at an earlier time t′? Not with t′ < m₁ + 104, since φ(b + v) ≥ C. Not with t′ ≥ m₁ + 104 either, since then p(t′ − 104) = b before τ.

*Near case, φ(S) ≤ D + 16.* Suppose member n read S at some t ≤ τ. Then t < m₁, since interval-1 reads have φ > D + 16. So member n + 1 also reads S at t, before τ + 104, which is a contradiction. Now member n + 1 reads S at some t′ > τ + 104. That read is not of the second form, because those reads are p(t) + v with φ > D + 20. So J = 2, and S = p(t′ − 208) with t′ − 208 ≥ m₂ > τ.

*Far case, φ(S) > D + 16.* Suppose member n read S − v at some t ≤ τ.
- If t ≥ m₁, member n + 1 reads S at t + 104 ≤ τ + 104.
- If t < m₁, then φ(S − v) > D + 12, so (P-out) gives p(t + 104) = S. Member n + 1 reads S at t + 104 < m₁ + 104 ≤ τ + 104.

Either way this is a contradiction. Now member n + 1 reads S at some t′ > τ + 104.
- If the read has the second form, S − v = p(t′ − 104) is read by member n.
- If it has the third form, S = p(t) with t ≥ m₂ and φ(S) > D + 16, so (P-ret) gives S − v = p(t + 104). ∎

**The hypotheses hold for every member.**
- Lemma 5.1(a) gives the corridor hypotheses for every member, with m₁(n + k) = m₁ + 104k, m₂(n + k) = m₂ + 208k and C(n + k) = C + 4k.
- Lemma 6.4 itself gives τ(n + k) = τ + 104k.
- (P-out) holds for every member because, until a member reads its block, its run is the blank run. The blank run is v-periodic after update 10,504, and its earlier reads have φ ≤ 31 ≤ D + 12.
- (P-ret) transfers from member n. Relation interval 2 of member n + k is that of member n delayed by 208k, with the same positions. At the base member, (P-ret) is checked directly from m₂ to the certificate start s. After s it holds vacuously: the reads in [s, s + 104) have φ ≤ D + 16, and φ(u) ≤ 0 for the certified drift u, since J is even.

**Corollary 6.5 (unrolling).** Every new cell of member n + k is S₀ + r·v, where S₀ is a new cell of member n and 0 ≤ r ≤ k. Moreover r = k unless φ(S₀) ≤ D + 16, and r = 0 unless φ(S₀) > D + 12.

*Proof.* Apply Lemma 6.4 k times. Each far step lowers φ by 4. Once a cell is in the near case it stays there. ∎

**The children.** A new cell S₀ of the base member therefore determines one child that covers all of its images:
- if φ(S₀) ≤ D + 12, the cell stays put: the one-parameter child with S₀ fixed;
- if D + 12 < φ(S₀) ≤ D + 16, the images are S₀ + r·v for 0 ≤ r ≤ k: the split child with representative S₀ and parameters (10 + r, 30 + k − r);
- if φ(S₀) > D + 16, the image is S₀ + k·v: the one-parameter child in which S₀ moves with the block.

New cells of the base member first read at or after the tail cutoff T₂ are reduced by Lemma 6.1 to cells z₀ + j·u, where z₀ is first read in the tail window and j ≥ 40. Each such z₀ gets a tail child of one of two kinds:
- if φ(z₀) > D + 16 and φ(u) ≥ 0, the tail moves with the block; every class member has φ > D + 16, so r = k;
- if φ(z₀) ≤ D + 12 and φ(u) ≤ 0, the tail stays put; every class member has φ ≤ D + 12, so r = 0.

For the 21 one-switch parents every new cell has φ > D + 16, because after τ the run stays far, so every child moves with the block. For the shuttle we take D = 52 instead of the site maximum 25. The corridor hypotheses still hold with D = 52, and the band D + 12 < φ ≤ D + 16 is then exactly the split index ℓ = 10 of the extension. With these choices the children prescribed above are exactly the children the extension produced. Every prescribed child is in the C++ list, and every listed child is used; `gen_lean_part.py` reports this for each parent.

**The case d ≥ 2.** Three cells would need Lemma 6.3 for two-parameter parents. Two additional points are then needed:
- an injectivity argument for images under several corridors, choosing a separating corridor and treating perpendicular and parallel drifts separately;
- the span-ownership rule above.

Neither is needed for Theorem A, and we do not claim the d ≥ 2 case here.

## 7. Proof of Theorem A

**Level 1.** The blank family has no parameters. The checker certifies its run with start s = 10,504 and certificate time T = 10,608. The highway itself begins about 10,000 updates in.

Extending it yields:
- 2,432 single-cell configurations (site and tail-near children);
- 22 tail families, each with one corridor of drift (−2,−2) and base 40.

All 2,432 configurations certify. All 22 families verify at base 40 with no slabs: 21 have one transit, and one is a shuttle with two transits. Every single-cell configuration is one of these, or has its cell never read by the blank run, in which case the run is the blank run (Lemma 2.1).

**Level 2.** Every level-1 entry is extended at its verified base, together with every slab below it, and every child is proved. Families are proved by Proposition 5.2 with adaptive bases; concrete configurations are certified directly.

**Assembly.** Let Q = {c₁, c₂}, and normalize the pose.
- If the run never reads either cell, it is the blank run.
- Otherwise let F be the first cell of Q that the run reads. Until then the run is the blank run, so F is the first cell of Q read by the blank run, and {F} is a member of a level-1 entry.
- The run of Q equals the run of {F} until that run reads the other cell S (Lemma 2.1).
- If it never does, the run of {F} settles the case.
- Otherwise S is a new cell of the run of {F}. By Lemma 6.3, Q is a member of a level-2 child, and that child is proved. ∎

This assembly is formalized as `two_black_canonical` and `two_black_of` (§9). In Lean the case split is on the first-read time of F. The 2,432 concrete parents are discharged by `check0 [F]`. The channel parents are discharged by Lemma 6.3 for d = 1, proved as in §6.1 (`checkPart_sound`), together with the children's family theorems. The result is `theoremA`.

## 8. The computation

All runs use the strengthened checker of this draft, with conditions (C1)–(C5), (S8), (H1′), (H3) and (F1).

| | Parents | Children | Families proved | Concrete runs | Slabs | Step-exact cross-checks | Failures |
|---|---:|---:|---:|---:|---:|---:|---:|
| Level 1 | blank | 2,454 | 22 | 2,432 | 0 | 44 | 0 |
| Level 2, first cell a family | 22 | 45,958 | 46,552 | 32,057 | 32,628 | 94,116 | 0 |
| Level 2, first cell concrete | 2,432 | 4,504,595 | 53,504 | 4,454,293 | 768 | 107,008 | 0 |
| **Level 2 total** | 2,454 | **4,550,553** | **100,056** | **4,486,350** | **33,396** | **201,124** | **0** |

Notes on the table:
- Each level-2 run first re-proves its level-1 parents (and the blank start), so the level-2 rows already include the level-1 proofs.
- The two level-2 halves together simulated 134,046,238,976 ant updates.
- "Families proved" counts every family the prover settles, including the one-parameter slabs that adaptive bases create, so it can exceed the number of family children.
- "Concrete runs" includes slab members certified directly.
- Each concrete level-1 parent has exactly 22 tail children (2,432 × 22 = 53,504), one per channel of the blank highway.

Corridor statistics over all proved families: 88,420 corridors with one transit, 10,141 with two, 1,962 with three, 38 with four, and 1 with five. Multi-transit corridors (shuttles) are therefore common, and the lemmas are exercised well beyond the one-transit case.

**Cross-checks.**
1. *Step-exact prediction.* For every proved family, members at n + eᵢ and n + 5eᵢ were run directly. Each certified at exactly the time predicted by Proposition 5.2. *(Numbers in the table.)*
2. *Exhaustiveness test (Lemma 6.3).* Lemma 6.3 says that the children made at the base cover every new cell of every larger member. We tested this directly in two ways.
   - *In the checker.* We ran 3,092 members: 30 random members n′ ∈ base + [1, 60] of each of the 22 level-1 families, and each of the 2,432 concrete level-1 entries. Every one of their 6,751,301 new cells was matched to **exactly one** child member with parameters at or above that child's base. None was uncovered.
   - *Independently, in Python* (`indep_cover.py`). This test ignores the categories of Section 6. For a configuration 𝓕(n′) ∪ {z}, it decides membership in a child by solving the child's affine block equations in exact integer arithmetic, over every bijection between child blocks and cells. Pivot rows with nonzero determinant are chosen, the solution is checked for divisibility, and the full system is then verified. It uses its own simulator, the independent certifier of item 3, and a longer horizon (certificate time + 104·80 rather than + 104·56), so it also tests Lemma 6.1 beyond the extension's window.
     - Parents: all 22 level-1 families at n′ = base + {0, 1, 2, 3, 5, 9, 17, 33, 61}, and every 16th concrete level-1 entry (152).
     - Result: 350 members, 962,875 new cells, **0 uncovered, 0 multiply covered**.
     - Mutation check (`mutation_test.py`, log `runs/mutation.out`). We damaged the child lists of one concrete parent and one family parent: deleting all new-corridor children, deleting each of 20 random children, and moving each of 20 random children's new block by one cell. Every one of the 82 damaged lists made the test report gaps; the undamaged lists report none.
3. *Independent checker* (`indep_family.py`). A second implementation of Sections 2–5 in Python, written from the definitions above, re-ran 1,086 proved families. It compared the verdict and all recorded data: certificate time, transit counts, zones Dᵢ and Cᵢ, and every switch time. The sample consisted of:
   - every 150th family proof of the family half (311);
   - **all** 506 two-parameter families (the only ones where (S8), (H1′) and (H3) are active), with 1 to 3 transits per corridor;
   - 269 tail families from a 1/40 shard of the concrete half.

   The Python implementation accepted all 1,086 families, and all their data agreed exactly.
4. *Independent detector.* Note 1's crossing-certificate detector, which uses eight cut families and full half-plane board comparison, confirmed that every one of 3,004 configurations sampled from this run (every 1,500th concrete run) reaches the standard highway. It simulated 79.6 million updates. On the earlier run it confirmed 4,969 of 4,969.

## 9. Formalization in Lean

The directory `lean/` contains a Lean 4 development (`TwoBlack`, Lean 4.30.0, the core library only, no Mathlib). Every theorem listed below is proved with no `sorry`. The main result is

```lean
theorem theoremA : ∀ s, AtMostTwoBlack s → ReachesP104 s
```

with no hypotheses (`TwoBlack/Main.lean`). `#print axioms` shows only the standard axioms (`propext`, `Quot.sound`, `Classical.choice`). Theorems that rest on a finite computation also use the auxiliary axiom generated by `native_decide`; that is, they trust Lean's compiler to evaluate a Boolean checker. This is the same trust model as Ke's one-black development.

**Proved in general.**

| Paper | Lean (`TwoBlack/…`) | Content |
|---|---|---|
| §2.1 | `Basic`, `Pose`: `run_shiftS`, `run_rotS`, `reaches_of_canonical` | dynamics; translation and rotation invariance; reduction to the canonical pose |
| Lemma 2.1 | `Coupling`: `agree_run` | first-difference coupling |
| Lemma 2.2 | `Highway`: `halfplane_forever`, `reaches_of_certificate` | half-plane certificate ⇒ the period-104 highway (`ReachesP104`, Ke's predicate) |
| Lemma 4.1 | `Corridor`: `corridor` | the corridor lemma, for any number of switches |
| Lemma 4.1, last line | `Succ`: `corridor_reaches` | the highway transfers from member n to member n + eᵢ |
| Lemma 5.1(a) | `Succ`: `corridor_succ` | one corridor: the hypotheses hold again for the next member |
| Prop. 5.2, d = 1 | `Succ`: `corridor_family` | every member of a verified one-corridor family reaches the highway |
| Lemma 5.1(b) | `Perp`: `perp_succ`, `H1p_succ` | a perpendicular corridor keeps its hypotheses when the other corridor is lengthened, given (H1′); its switch j moves by the corridor-1 lag 104·q(j) |
| Prop. 5.2, two perpendicular corridors | `Perp`: `perp_family` | every member of a two-corridor family with perpendicular drifts reaches the highway |
| Lemma 5.1(c) | `Par`: `par_succ`, `ParHyp` | a parallel corridor keeps its hypotheses when the other is lengthened; when it lies beyond, its zones move by Δ = φ₂(v₁) |
| Prop. 5.2, two parallel corridors | `Par`: `par_family` | every member of a two-corridor family with parallel drifts reaches the highway |
| §3 checker, d = 2 | `Check2`, `Check2Par`: `check2p_sound`, `check2par_sound` | executable checkers for two-corridor families, sound by `perp_family` and `par_family` |
| §3 checker, d = 1 | `Check`: `check1`, `check1_sound` | an executable checker for one-corridor families and its soundness theorem |
| Lemma 6.1 | `Tail`: `descent` | descent along the tail |
| Lemma 2.1, unread case | `Tail`: `reaches_add_unread` | a cell that is never read changes nothing |
| Lemma 6.3, d = 0 | `Parent0`: `check0`, `check0_sound`, `certB_sound` | the partition for parents without a corridor; certificates are searched for inside Lean |
| §7 | `TheoremA`: `two_black_of`, `concrete_of_table` | the assembly of Theorem A |
| Lemma 6.1 on the blank run | `Remaining`: `deep_is_channel` | the first cells read after the blank cutoff lie on the 22 channels |
| §7, channel half | `Remaining`: `channelParentsOK_of`; `Channels`: `two_black_of_partition`, `Kid1.reaches` | reduction of `ChannelParentsOK` to the child partition and to the children's family theorems |
| Lemma 6.4 | `Step`: `step_first`, `step_new` | the one-step lemma |
| §6.1, hypotheses | `Step`: `step_chain`, `posmap2`, `pos_eq_blank_upto`, `blank_facts` | the one-step hypotheses for every member |
| Corollary 6.5 | `Step`: `unroll` | unrolling |
| Lemma 6.3, channel parents | `PartCheck`: `checkPart`, `checkPart_sound` | an executable partition check on member 40, sound for every member |

**Proved with computation (`native_decide`).**
- `level1_families_reach`: every depth j ≥ 40 on each of the 22 one-cell channels reaches the highway. This checks the 22 families, including Ke's exceptional channel, which has two switches.
- `one_black : ∀ s, ExactlyOneBlack s → ReachesP104 s`. This is Ke's theorem, with the same predicate, by an independent route: the blank run as a d = 0 parent, 2,432 certificates searched for in Lean, the 22 channel families, Lemma 6.1, and pose normalization.
- `concreteParentsOK`: for each of the 2,432 cells F that the blank run reads before its tail cutoff, adding any later cell gives the highway. This runs `check0 [F]` on every such parent: about 4.5 million certificate searches and 53,504 one-corridor families. A coverage pass (`coverLoop`) shows that the table lists exactly the blank run's first reads. Every check passes. This took 32 modules and about 17 CPU-hours of compiled evaluation.
- `hpart_proved`: Lemma 6.3 for the 22 channel parents. `checkPart` runs on member 40 of each parent (`TwoBlack/PartData.lean`); all 22 pass in about 25 seconds.

**The statements.**
1. `two_black : ChannelParentsOK → ∀ s, AtMostTwoBlack s → ReachesP104 s`.
   - `AtMostTwoBlack s` holds when the black cells of s form a list of length at most 2; the ant may be anywhere, facing any direction.
   - `ChannelParentsOK` says: for every cell F that the blank run first reads at or after its tail cutoff, adding any cell not yet read gives the highway. By Lemma 6.1, formalized as `deep_is_channel`, these F are exactly the cells z₀ + j·(−2,−2), j ≥ 40, on the 22 channels.
2. `two_black'` replaces `ChannelParentsOK` with the two mathematical statements the paper uses for it. This is the shape the referee asked for.
   - `hpart : ∀ p ∈ level1Families, ChildPartition1 p.1 40 (kidsIn chanTable p.1)`. This is Lemma 6.3 for the 22 one-corridor channel parents, the referee's `child_partition`. For every member j ≥ 40, once the parent's block has been read, every cell S not yet read is either never read, or completes the member to a member of one of the listed child families. The child lists in `chanTable` are the extension computed by the C++ checker: 45,452 one-parameter and 506 two-parameter children.
   - `hk2 : ∀ e ∈ chanTable, ∀ c ∈ e.kids2, FamReaches c`: Proposition 5.2 for the 506 two-parameter children.
3. `two_black_final : (hpart) → ∀ s, AtMostTwoBlack s → ReachesP104 s`. This discharges `hk2` as well:
   - the 286 perpendicular children by `check2p`, sound by Lemma 5.1(b);
   - the 220 parallel children by `check2par`, sound by Lemma 5.1(c);
   - their 572 slab families by `check1`.

   The 45,452 one-parameter children are checked by `chanTable_ok`, which runs `check1` with direct certificates for any members below a raised base. All pass; the check takes 22 modules and about one CPU-hour.
4. `theoremA : ∀ s, AtMostTwoBlack s → ReachesP104 s` is `two_black_final hpart_proved`. **Theorem A is proved in Lean with no hypotheses.**
   - The full build completes (261 jobs, no `sorry`).
   - `#print axioms theoremA` lists only `propext`, `Quot.sound` and `Classical.choice`, plus the 61 `native_decide` axioms of the computations (`runs/axioms.out`).

**The Lean form of (H3).** `ParHyp` asks for less than (H3):
- *side:* every switch of corridor 2 falls in a corridor-1 phase of one side σ, away from corridor-1 windows (H1′);
- *band:* corridor 2's band lies in corridor 1's zone on side σ;
- *zone:* every foreign read lies beyond corridor 2's zones, on the side of the sign of ρ. A foreign read is one made in a corridor-1 phase of the other side; this includes every corridor-1 window read.

The extrema clause (H3d) is not needed. In Lean the zones D, C are data that only have to satisfy (C1)–(C4); they are not recomputed from the run. The margin of 40 in (C1) absorbs the single ±4 step of a foreign read, and the direction condition on ρ is what lets the hypothesis iterate.

**How `hpart` is proved.** The proof follows §6.1.
- `StepHyp` collects the hypotheses of Lemma 6.4, and `step_first` and `step_new` prove its two conclusions.
- `step_chain` establishes the hypotheses for every member of a parent from facts about member 40. The corridor hypotheses come from `check1`, (P-out) from the blank run (`blank_facts`, `pos_eq_blank_upto`), and (P-ret) by transport (`posmap2`).
- `unroll` is Corollary 6.5.

`checkPart F H P ks` is one pass over member 40. It checks the following:
- the parent's corridor hypotheses (`check1`), with J ∈ {1, 2}, and that the block is first read at the hinted time, between the switches;
- D ≥ 19, so that the blank run's early reads (φ ≤ 31) satisfy (P-out);
- for J = 2, the periodicity (P-ret) of the returning transit up to the certificate, and that the tail stays in the near zone;
- the tail margin of Lemma 6.1;
- for each cell first read after the block and before the tail cutoff, that the child prescribed by §6.1 is in `ks`, and for each cell first read in the tail window, that its tail child is in `ks`.

`checkPart_sound` turns a passing check into `ChildPartition1 F 40 ks` for every member j ≥ 40. Here `ks = kidsIn chanTable F` is exactly the C++ child list whose members are proved in `two_black_final`. The two-switch parent uses D = 52 (§6.1); all other hints are those of `level1Families`.

`TwoBlack/PartMut.lean` is a mutation test, built separately with `lake build TwoBlack.PartMut`. Each of the following makes `checkPart` fail:
- removing child 0, child 500 or the last (tail) child of the first parent;
- removing child 0 or all split children of the two-switch parent;
- using D = 25 for the two-switch parent.

The undamaged inputs pass.

**What the formalization changed.**
- It found the gap in the proof of Lemma 4.1, now repaired (step 4 of §4).
- It showed that (C2)'s range condition is implied by (C4).
- It made window disjointness, m_{j+1} > m_j + 104, an explicit hypothesis.
- It fixed the exact form of the relations: the two halves of each relation overlap, and the overlap is consistent because of (C3) and the untouched windows.
- It replaced the footprint argument for Lemma 6.3 on the channel parents with Lemma 6.4. Lemma 6.4 needs neither (F1) nor Lemma 6.2, only the periodicity of the two transits at the points where it is used.

## 10. Trust boundary

Theorem A is proved in Lean as `theoremA`, with no hypotheses. Its correctness rests on three things.
- **Lean's kernel**, which checks every proof.
- **Lean's compiler**, which evaluates the 61 Boolean checks closed by `native_decide`. They cover:
  - the blank run;
  - the 22 channel families;
  - the 2,432 concrete parents (32 chunks) and the coverage pass over them;
  - the channel children (22 modules, plus the perpendicular and parallel checks);
  - the partition check.

  This is the same trust model as Ke's one-black development. A check evaluated by the kernel alone is out of reach at this scale.
- **The definitions**, which must say what Theorem A says.
  - `run` implements the RL rule: north = +y; turn right on white and left on black, flip the cell, step. `State.dir` is the heading on arrival.
  - `AtMostTwoBlack s` says that the black cells of s form a list of length at most 2. The ant's position and heading are arbitrary.
  - `ReachesP104` is Ke's predicate: the observations are eventually 104-periodic with one of the four standard drifts.

The C++ checker and the Python scripts are no longer part of the trust base. They produce hints and child lists, and Lean verifies everything it uses. The cross-checks of §8 remain as independent evidence that the implementations agree. Theorem A no longer depends on them; in particular it does not depend on (F1), which only the C++ checker tests.

## 11. Outlook: three cells

Taking the recursion one level further, to three cells, the corridor checker fails on a specific, geometrically clear class (note 3). There, one corridor parameter stretches two *different* parallel highway tracks.

For example, F → S lies on one track, while a later highway T → origin runs on a parallel track whose length grows with the same parameter. Direct simulation of these families reaches the standard highway in every member tested. The outcome changes only at isolated parameter values near the base.

This points to replacing corridors by an **interaction graph**:
- vertices are debris sites;
- edges are exact highway transits, each with its own track, phase and periodic wake;
- each edge length is an affine function of the parameters, so one parameter may lengthen several edges at once;
- the parameter values where outcomes change become resonance hyperplanes, handled by splitting parameter space into polyhedral cells.

Lemmas 4.1 and 5.1 should carry over edge by edge, with tubes around tracks replacing half-plane bands, but this has not been checked.

On the formal side, Lemma 6.4 suggests a route to the partition lemma for d ≥ 2. Instead of footprint periodicity, it uses the periodicity of each transit exactly where the one-step argument needs it, together with a near/far threshold for each corridor.

**A correction to note 3's outlook.** Unboundedness forbids endless back-and-forth only within a *fixed* bounded network of sites. It does not exclude finitely many logical sites producing ever longer tracks, new debris states, or an unbounded counter encoded in corridor lengths. A route to the general conjecture through finite interaction closure therefore needs a finiteness or monotonicity theorem specific to the RL rule. This agrees with the obstruction in note 2: the generic tools hold for generalized ants, some of which provably avoid highways. It also agrees with Ke's observation that reversible systems with growing history can simulate universal computation.

## References

- L. A. Bunimovich, S. E. Troubetzkoy, *Recurrence properties of Lorentz lattice gas cellular automata*, J. Stat. Phys. 67 (1992).
- D. Gale, *The industrious ant*, Math. Intelligencer 15 (1993) — the Cohen–Kong extremal argument.
- I. Dirgová Luptáková, J. Pospíchal, *How random is spatiotemporal chaos of Langton's ant?*, J. Appl. Math. Stat. Inform. 11(2) (2015) 5–13, doi:10.1515/jamsi-2015-0008.
- A. Gajardo, V. H. Lutfalla, M. Rao, *Ants on the highway*, arXiv:2409.10124 (2024).
- V. H. Lutfalla, *Sideways on the highways*, arXiv:2505.05426 (2025); *The LLLR generalised Langton's ant*, arXiv:2506.10482 (2025).
- K. R. Etse, *How Long Can the Escaping Ant Be Confined?*, MFCS 2026, LIPIcs 49.
- A. Jillhewar, *Finite-Support Periodic Highways of Langton's Ant*, Research Square preprint (2026).
- H. Ke, *Every One-Black-Cell Langton Ant Reaches the Period-104 Highway: A Lean-Checked Proof*, Zenodo (2026), doi:10.5281/zenodo.22086968; repository kehao95/langtons-ant-core.
