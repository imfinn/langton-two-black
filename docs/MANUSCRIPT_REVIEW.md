# Substantive comparison of manuscript sections 9 and 10

Line numbers refer to the supplied `TWO_BLACK_CELLS (2).md`, which is byte-identical to `paper/TWO_BLACK_CELLS.md`. This review covers every substantive paragraph, table row and bullet in sections 9–10; headings, blank lines and table delimiters contain no additional claims. Where a line has several claims, separate rows distinguish them. Fresh execution results are recorded in `AUDIT.md` and `audit/2026-10-05/`; a supplied log is never treated as a successful rerun.

## Recommended corrections

1. Replace “with no hypotheses” throughout with “with no remaining auxiliary hypotheses beyond the initial cardinality condition”.
2. Replace line 433's “only the standard axioms” with the actual list: three standard axioms and 61 generated native-computation axioms. Explain that the kernel checks soundness/assembly proof terms relative to these computations; compiled execution, not kernel reduction, supplies their truth.
3. Replace “exactly” in the claims about `coverLoop` and `deep_is_channel` with the coverage/containment statement actually proved. Keep exact table agreement as separately identified independent computational evidence. Avoid implying `ChildPartition1` establishes uniqueness or disjointness.
4. State the precise observation predicate, and keep standard-word identification and operational statistics in the external-computation evidence category.
5. Label timings, discovery history, referee requests and historical simulation counts as documentary claims. Provide machine and command details for timings.
6. Add complete regeneration instructions and note the supplied parallel generator's missing `par_covered` theorem. The maintained generator repairs this while preserving the original proof files.

Suggested replacement for the opening trust paragraph:

> Theorem A has no remaining auxiliary hypotheses beyond `AtMostTwoBlack s`. A fresh Lean 4.30.0 build checks the mathematical soundness and assembly proofs, and compiled Boolean checks discharge the finite obligations through `native_decide`. Its axiom report contains `propext`, `Quot.sound`, `Classical.choice`, and 61 generated native-computation axioms. Consequently the validation trusts the Lean kernel and native compilation/execution stack. The C++ and Python generators supply untrusted candidate data; Lean checks all properties of those data needed by the theorem.

## Line-by-line comparison

| Line(s) | Claim | Assessment | Artifact comparison / recommendation |
|---|---|---|---|
| 427 | Toolchain, core-only development, no sorry | Supported | `lean-toolchain`, `lakefile.toml`, source scan; fresh build result is separately recorded in AUDIT. |
| 430 | Main declaration | Supported | Matches `Main.lean`; the qualified name is `TwoBlack.theoremA`. |
| 433 | No hypotheses | Correct wording | The declaration still has `AtMostTwoBlack s` as its premise. Say “no remaining auxiliary hypotheses”. |
| 433 | Only standard axioms | Correction required | This sentence excludes the native axioms, contradicting its next sentence and line 484. State the three standard axioms plus all 61 generated computation axioms together. |
| 433 | Compiler evaluates Boolean checker; same trust model as Ke | Qualify | Correct in outline. Include native evaluator/runtime, compiled core/Std, toolchain and platform. Ke's pinned source uses the same Lean version and native tactic; his entire development was not audited here. |
| 439 | Dynamics and pose normalization | Supported | `Basic.step`; `Pose.run_shiftS`, `run_rotS`, `reaches_of_canonical` prove arbitrary translations and quarter-turn rotations. |
| 440 | First-difference coupling | Supported | `Coupling.agree_run` has the region/read hypotheses needed for the coupling. |
| 441 | Half-plane implies highway; Ke predicate | Supported, qualify meaning | `Highway.halfplane_forever` and `reaches_of_certificate` prove infinite observation periodicity. Ke's pinned semantics agree in substance; no cross-project equivalence theorem is supplied. |
| 442 | Corridor, arbitrary switch count | Supported | `Corridor.corridor` quantifies over any J with the stated separation, window, and zone conditions. |
| 443 | Highway transfer to next member | Supported | `Succ.corridor_reaches` transports the observation conclusion through the corridor relation. |
| 444 | One-corridor succession | Supported | `Succ.corridor_succ` preserves the hypotheses after lengthening. |
| 445 | All members of a one-corridor family | Supported | `Succ.corridor_family` inducts over all natural k, not a finite list of tested depths. |
| 446 | Perpendicular succession and H1′ | Supported | `Perp.perp_succ` and `H1p_succ` use zero cross-projections and transport switch timing by the phase lag. |
| 447 | All perpendicular two-parameter members | Supported | `Perp.perp_family` uses double induction and the required initial relations. |
| 448 | Parallel succession and zone shift | Supported | `Par.par_succ` uses `ParHyp`; the zone shift is the cross-projection Δ on the selected side. |
| 449 | All parallel two-parameter members | Supported | `Par.par_family` proves both parameters by induction, with its sufficient hypotheses. |
| 450 | Two-corridor checker soundness | Supported | `check2p_sound` / `check2par_sound` turn finite checker success into universal family statements. |
| 451 | One-corridor checker soundness | Supported | `check1_sound` connects finite support and finite reads to `CorridorHyp`, extending the tail to all time. |
| 452 | Tail descent | Supported | `Tail.descent` quantifies over any descent depth. |
| 453 | Unread cell changes nothing | Qualify wording | `reaches_add_unread` proves observation equivalence and transfers the highway; the board itself does differ at the unread cell. |
| 454 | Concrete-parent partition and internal certificate search | Supported | `Parent0.check0_sound`, `certB_sound`: search success implies a genuine half-plane certificate; finite windows plus descent cover arbitrary second cells. |
| 455 | Final assembly | Supported | `TheoremA.two_black_of` handles cardinality and pose; `concrete_of_table` handles the concrete obligations. |
| 456 | Late first reads lie on channels | Supported | `Remaining.deep_is_channel` proves this forward containment. |
| 457 | Channel reduction and child reachability | Supported | `channelParentsOK_of`, `two_black_of_partition`, and `Kid1.reaches` connect the exact child lists and their bases. |
| 458 | One-step lemma | Supported | `StepHyp.step_first` / `StepHyp.step_new` prove the first-read shift and new-cell alternatives. |
| 459 | Hypotheses for every member | Supported | `step_chain`, `posmap2`, `pos_eq_blank_upto`, `blank_facts` supply the all-depth hypotheses. |
| 460 | Unrolling | Supported | `Step.unroll` iterates the one-step transport with explicit near/far inequalities. |
| 461 | Member-40 partition checker universally sound | Supported | `PartCheck.checkPart_sound` proves `ChildPartition1 F 40 ks`, quantifying over all j ≥ 40. Its ordinary proof also uses the native-verified blank-run fact via `blank_facts` / `blank_check`; it is not native-axiom-free. |
| 464 | 22 families, including two-switch exception | Supported | `Level1.level1_checks` checks 22 literal entries; `level1_families_reach` is an ordinary soundness consequence of that native equality. |
| 465 | One-black theorem, arbitrary pose, independent route | Supported with scope | `General.one_black` assembles blank-parent checks, families, descent, and pose. “Same predicate” is an informal semantic comparison, not shared definitions. No independent audit of Ke's proof or historical independence claim was performed. |
| 466 | 2,432 concrete parents; 53,504 family entries | Supported | Independent source/dump counts agree. Native chunk checks and `concrete_of_table` establish required parent reachability. |
| 466 | Adding any later cell | Clarify | The precise statement requires the second cell to be unread through the first cell's first-read time; “later” refers to time, not spatial distance. |
| 466 | About 4.5 million certificate searches | Separate evidence | This is an operational statistic, not a Lean theorem. The check code really searches; this audit did not instrument all search counts. |
| 466 | Table lists exactly first reads | Overstatement of checker | `coverLoop` returns true at horizon zero regardless of remaining table. It validates ordered coverage and divergence bounds, ignores `PEntry.tau`, and permits extra trailing entries. Independent Python replay confirms the supplied 2,432-entry table is exact, but the Lean soundness theorem states only necessary coverage. |
| 466 | 32 modules and 17 CPU-hours | Mixed | 32 chunk modules is confirmed. CPU-hours are historical performance evidence, not a formal result or a universal reproducibility estimate; cite machine/toolchain/log and report fresh wall time separately. |
| 467 | Partition check on 22 member-40 runs | Supported | `PartData.part_checks` proves all 22 Boolean results; `hpart_proved` applies soundness. |
| 467 | 25 seconds | Historical timing | Machine-specific. Report the fresh build time for PartData separately. |
| 470 | two_black type | Supported | Matches `Final.two_black`. |
| 471 | At most two cells and arbitrary pose | Supported | `AtMostTwoBlack` is exact support equality to a list of length ≤ 2; duplicates do not introduce a bound or an omission. |
| 472 | ChannelParentsOK | Supported | Its definition quantifies over all late blank first reads and all second cells unread through that time. |
| 472 | deep_is_channel proves these are exactly the 22 rays | Overstatement of named theorem | The declaration proves late first read ⇒ membership in a listed ray. It does not state the converse or uniqueness. Replace “exactly” with “lie on”, or supply a separate converse result. |
| 473 | two_black′ reduces to two obligations; referee request | Mixed | The type matches. The referee/history explanation is documentary and cannot be established from Lean. |
| 474 | hpart statement and child counts | Supported, clarify partition | `ChildPartition1` proves coverage by at least one listed family or never-read status. It does not assert disjointness or unique classification. Counts 45,452 and 506 are independently checked source counts. |
| 475 | hk2 universal reachability for two-parameter children | Supported | Matches the second assumption of `Final.two_black'`. |
| 476 | two_black_final discharges hk2 | Supported | `two_black''` uses `perpCovered_sound perp_covered`; `two_black_final` uses `parCovered_sound par_covered`. |
| 477 | 286 perpendicular children | Supported | All required actual family identities are covered by the native `perp_covered` check and its soundness proof. |
| 478 | 220 parallel children | Supported | All required actual family identities are covered by `par_covered` and its soundness proof. The supplied generator fails to emit this declaration and needs repair. |
| 479 | 572 slabs | Supported | 120 perpendicular plus 452 parallel slab hints. `Kid1.ok` also uses direct certificates when a slab's checker base is raised. |
| 481 | 45,452 children, checks, raised bases | Supported | 22 `chan*_ok` native checks combine into `chanTable_ok`; `Kid1.reaches` covers members below a raised base with direct certificates. |
| 481 | One CPU-hour | Historical timing | Not certified by Lean; fresh module times and hardware are recorded separately. |
| 482 | theoremA = two_black_final hpart_proved | Supported, correct wording | Exact source term. Replace “no hypotheses” with “no remaining auxiliary hypotheses beyond AtMostTwoBlack”. |
| 483 | Build completes, 261 jobs, no sorry | Reproduction required | The fresh build log and exit status determine this; supplied logs were not accepted as evidence. Job count depends on the build target/configuration. |
| 484 | Three standard plus 61 native axioms | Reproduction required | This is the expected grouping from source. The fresh axiom output and extracted list are authoritative. It is not a kernel-only proof. |
| 486 | ParHyp weaker than paper H3 | Supported | The final theorem uses the stated sufficient hypotheses. It does not separately certify every extra condition in the C++ verifier or all formulations in the paper. |
| 487 | side condition | Supported | `ParHyp.h1p` and `side` fix the side for switches and keep windows separated. |
| 488 | band condition | Supported | `ParHyp.band` / `bandB` place the corridor-2 strip on the required corridor-1 side. |
| 489 | foreign-read zone condition | Supported | `ParHyp.zone` / `zoneLoopB` cover foreign phases and windows with the sign of the transported drift. |
| 491 | Extrema not needed; hints D,C; separation and sign | Supported | Ordinary `par_succ` proves preservation without an extrema premise; the executable checker verifies the zones and tail extension. The hints themselves are not assumed true. |
| 493 | Proof follows §6.1 | Supported in substance | The chain `step_chain` → `unroll` → `checkPart_sound` matches the described one-step argument. |
| 494 | StepHyp and two conclusions | Supported | Corresponding structures/declarations are present with ordinary proofs. |
| 495 | check1, P-out from blank, P-ret by transport | Supported | The code explicitly supplies those ingredients; there is no missing all-depth hypothesis. `blank_facts` inherits the native `blank_check` premise. |
| 496 | unroll is Corollary 6.5 | Supported | The source statement and induction implement the stated unrolling. |
| 498 | One pass over member 40 | Minor wording | One finite member is checked, but the implementation contains several simulator passes and nested checks. Say “a finite check of member 40”. |
| 499 | Corridor hypotheses, J ∈ {1,2}, hinted first block read | Supported | `checkPart` and `partLoop` enforce these conditions; no first-read hint is merely assumed. |
| 500 | D ≥ 19 and blank φ ≤ 31 | Supported | The guard and `blank_facts` establish the bound needed for P-out. |
| 501 | Two-switch return periodicity and near tail | Supported | `perLoop` compares the shifted positions on the return (the P-ret premise is positional); `readsB` verifies the near tail period and transport extends it. |
| 502 | Tail margin | Supported | Finite pre-read and window inequalities feed the ordinary descent theorem. |
| 503 | Finite and tail child membership | Supported | `kidOK`, `tailOK`, and `partLoop` compare exact family expressions and bases with the supplied `ks`. |
| 505 | checkPart_sound for every j ≥ 40 | Supported | There is no upper bound on j or on the second cell in the soundness statement. |
| 505 | Exactly the C++ child list | Separate provenance | The Lean theorem uses a list of literals and checks coverage/reachability. Agreement with the archived and fresh C++ output was independently compared; the generator program itself is not certified. |
| 505 | Two-switch D = 52; other hints from Level1 | Supported | Verified by comparing `PartData` and `Level1Data`. This special zone choice is an actual checker input, not a missing assumption. |
| 507 | Separate PartMut target | Supported | The file is excluded from the root theorem import graph. Run `lake build TwoBlack.PartMut` separately. |
| 508 | Remove first, middle, tail child | Reproduction required | Three negative native examples are supplied; fresh test results are recorded in AUDIT. |
| 509 | Remove exceptional first or all split children | Reproduction required | Two negative examples use the exceptional parent and the exact split bases [10,30]. |
| 510 | Exceptional D = 25 fails | Reproduction required | The supplied `wrong_zone` example checks this mutation. |
| 512 | Undamaged inputs pass | Reproduction required | `ok0` and `ok19` are positive controls; fresh test results matter, not the included log. |
| 515 | Formalization found historical gap, now repaired | Mixed | The present overlapping-relation/untouched-region argument is inspected and formalized. Discovery history cannot be inferred from this one archive; no prior revisions were audited. |
| 516 | C2 range follows from C4 | Supported in substance | The formal corridor uses C4 for the needed bounds rather than assuming a separate switch-range clause. |
| 517 | Explicit disjoint windows | Supported | `CorridorHyp` requires the strict m_j + 104 < m_(j+1) gap. |
| 518 | Overlapping relation halves, consistency | Supported | `Rid`, `Rtr`, switch proofs, C3, and untouched regions enforce the actual overlap and its use. |
| 519 | One-step proof removes F1/Lemma 6.2 | Supported for theorem chain | The imported channel partition proof uses `StepHyp` and return/outbound periodicity, with no F1 premise or call to the C++ checker. |
| 523 | No hypotheses; three correctness ingredients | Correct wording | Retain the cardinality premise, and distinguish a formal theorem relative to generated native axioms from the metatheoretic/compiler and interpretation trust. |
| 524 | Kernel checks every proof | Clarification required | It checks the ordinary proof terms relative to their axioms. It does not independently reduce these 61 Boolean computations to true. Lean 4.30.0's native tactic inserts an auxiliary axiom after compiled evaluation. |
| 525 | Compiler and 61 Boolean checks | Supported, expand trust | These are aggregate checks over tables. Trusted compiled core/Std operations, native evaluator/runtime, host compilation/linking and hardware are also involved. |
| 526 | Blank run | Supported | Two native premises cover the blank parent and a blank highway certificate. |
| 527 | 22 channel families | Supported | One aggregate native `level1_checks` premise. |
| 528 | 32 parent chunks and coverage | Supported | 32 native chunk equalities plus `cover_ok`. |
| 529 | Channel children and two-corridor checks | Supported | 22 native child-module equalities plus `perp_covered` and `par_covered`, including slabs and exact child matching. |
| 530 | Partition | Supported | One aggregate native `part_checks` premise; ordinary `checkPart_sound` extends it universally. |
| 532 | Same trust model as Ke | Qualify | Consistent with the pinned one-black source using Lean 4.30.0/native_decide. Do not imply this audit has revalidated all of Ke's artifacts. |
| 532 | Kernel-only check out of reach | Uncertified practical assessment | Performance claim, not a mathematical impossibility result. Say a kernel-reduction build was not supplied or measured and is expected to be much more expensive. |
| 533 | Definitions must match intended theorem | Supported | Manual semantic inspection is necessary; a successful compiler does not verify the informal English interpretation. |
| 534 | RL convention and heading on arrival | Supported | Exact `Basic.step` implementation; true means black, false means white. |
| 535 | Cardinality and arbitrary pose | Supported | The list condition captures support cardinality, including zero cells; normalization is proved rather than a distance-limited simulation. |
| 536 | Eventual 104 observations, four drifts; Ke predicate | Supported, qualify | Equivalent in substance to Ke's pinned semantics. Spell out position/heading/read-color observations and distinguish whole-board equality, the standard turn word, and least period. |
| 538 | C++/Python not in proof trust base | Supported for theorem | The build uses Lean source literals and its own compiled modules; no external solver or file-output truth is assumed. Lean verifies sufficient coverage and reachability, not every sentence printed by the generators. |
| 538 | Cross-checks independent evidence and no F1 dependency | Supported, delimit reruns | The fresh cross-check subset is documented in AUDIT. The huge 134-billion-update run and all historical §8 totals were not independently repeated. F1 and standard turn-word/statistical assertions remain external evidence. |

## Literature and novelty

Lean does not certify publication priority, novelty, attribution, or the literature survey. A limited primary-source search and inspection of Hao Ke's repository support acknowledging his prior one-black theorem. This audit did not establish an exhaustive priority search for two black cells. Preserve the manuscript's “to our knowledge” qualification; do not promote it to an unconditional first-proof claim. See `ACKNOWLEDGEMENTS.md` for the pinned source and citation.
