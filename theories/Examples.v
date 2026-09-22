From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import Syntax Automaton Construction StringConstraints
  LookaheadSemantics LookaheadDerivatives LookaheadDecision SemanticDFA PeriodicDisplay.
Import ListNotations.

Definition nat_eqb_spec : forall x y, Nat.eqb x y = true <-> x = y := Nat.eqb_eq.

Definition paper : regex nat :=
  Concat (Star (Atom 120))
    (Star (Plus (Concat (Atom 120) (Atom 120)) (Atom 121))).

Definition paper_ce := machine (build_ce Nat.eqb paper).
Definition paper_q := machine (build_quotient Nat.eqb paper).

Example paper_ce_states : state_count (machine (build_ce Nat.eqb paper)) = 5.
Proof. reflexivity. Qed.

Example paper_quotient_states :
  state_count (machine (build_quotient Nat.eqb paper)) = 3.
Proof. reflexivity. Qed.

Example paper_accepts_xxy :
  acceptb (machine (build_ce Nat.eqb paper)) [120;120;121] = true.
Proof. reflexivity. Qed.

Example paper_quotient_accepts_xxy :
  acceptb (machine (build_quotient Nat.eqb paper)) [120;120;121] = true.
Proof. reflexivity. Qed.

Example paper_ce_transitions :
  trans paper_ce 0 120 = [1;2] /\ trans paper_ce 0 121 = [4] /\
  trans paper_ce 1 120 = [1;2] /\ trans paper_ce 1 121 = [4] /\
  trans paper_ce 2 120 = [3] /\ trans paper_ce 2 121 = [] /\
  trans paper_ce 3 120 = [2] /\ trans paper_ce 3 121 = [4] /\
  trans paper_ce 4 120 = [2] /\ trans paper_ce 4 121 = [4].
Proof. repeat split; reflexivity. Qed.

Example paper_quotient_transitions :
  trans paper_q 0 120 = [0;1] /\ trans paper_q 0 121 = [2] /\
  trans paper_q 1 120 = [2] /\ trans paper_q 1 121 = [] /\
  trans paper_q 2 120 = [1] /\ trans paper_q 2 121 = [2].
Proof. repeat split; reflexivity. Qed.

(** ICFP 2027, Eq. (11), p.7: all four pair-quotient calculations. *)
Example pair_quotient_ab_cd_1 :
  pair_word_quotient Nat.eqb [0] ([0; 1], [2; 3]) =
  Some ([1], [2; 3]).
Proof. reflexivity. Qed.

Example pair_quotient_ab_cd_2 :
  pair_word_quotient Nat.eqb [0; 1] ([0; 1], [2; 3]) =
  Some ([], [2; 3]).
Proof. reflexivity. Qed.

Example pair_quotient_ab_cd_3 :
  pair_word_quotient Nat.eqb [0; 1; 2] ([0; 1], [2; 3]) =
  Some ([], [3]).
Proof. reflexivity. Qed.

Example pair_quotient_ab_cd_4 :
  pair_word_quotient Nat.eqb [0; 1; 2; 3] ([0; 1], [2; 3]) =
  Some ([], []).
Proof. reflexivity. Qed.

(** Paper Example 1, rendered Eq. (30)--(31). *)
Definition wab : rewpla nat := WPlus (WAtom 0) (WAtom 1).
Definition example1_r : rewpla nat :=
  WPlus (WLookahead (WConcat (WAtom 0) (WAtom 1))) (WAtom 0).
Definition example1_s : rewpla nat := WStar wab.
Definition example1_e : rewpla nat := WConcat example1_r example1_s.

Compute simplified_symbol_derivative Nat.eqb 0 example1_r.
Compute simplified_symbol_derivative Nat.eqb 0 example1_s.
Compute simplified_symbol_derivative Nat.eqb 0 example1_e.

Example paper_eq30_r :
  simplified_symbol_derivative Nat.eqb 0 example1_r =
    (WEps, WLookahead (WAtom 1)).
Proof. vm_compute. reflexivity. Qed.

Example paper_eq30_s :
  simplified_symbol_derivative Nat.eqb 0 example1_s = (example1_s, WZero).
Proof. vm_compute. reflexivity. Qed.

Example paper_eq31 :
  simplified_symbol_derivative Nat.eqb 0 example1_e =
    (WPlus example1_s (WConcat (WLookahead (WAtom 1)) example1_s),
      WLookahead (WAtom 1)).
Proof. vm_compute. reflexivity. Qed.

(** Paper Example 2, Eq. (42), including its full-pair semantic reduction. *)
Definition example2_prefix :=
  WConcat (WAtom 0) (WPlus (WAtom 1) (WAtom 2)).
Definition example2_branch :=
  WConcat (WLookahead (WConcat (WAtom 0) (WAtom 1))) example2_prefix.
Definition example2 := WPlus example2_branch (WConcat (WAtom 0) (WAtom 3)).

Definition example2_generator_display (r : rewpla nat) :=
  match r with
  | WLookahead s => WLookahead (rewpla_simplify s)
  | _ => rewpla_simplify r
  end.

Example paper_eq42 :
  map example2_generator_display (continuation_generators Nat.eqb example2) =
    [WPlus (WAtom 1) (WAtom 2); WAtom 3; WEps] /\
  map example2_generator_display (constraint_generators Nat.eqb example2) =
    [WLookahead (WAtom 1); WLookahead WEps].
Proof. vm_compute. reflexivity || auto. Qed.

Lemma two_atoms_semantics x y p :
  rewpla_denote Nat.eqb (WConcat (WAtom x) (WAtom y)) p <-> p = ([x;y], []).
Proof.
  simpl. unfold lang_concat. split.
  - intros [q [t [-> [-> Hout]]]].
    rewrite constraint_concat_empty_context in Hout. now inversion Hout.
  - intros ->. exists ([x], []), ([y], []). repeat split.
Qed.

Lemma example2_prefix_semantics p :
  rewpla_denote Nat.eqb example2_prefix p <->
    p = ([0;1], []) \/ p = ([0;2], []).
Proof.
  unfold example2_prefix. eapply iff_trans.
  - apply lang_concat_union_right.
  - change (rewpla_denote Nat.eqb (WConcat (WAtom 0) (WAtom 1)) p \/
      rewpla_denote Nat.eqb (WConcat (WAtom 0) (WAtom 2)) p <->
      p = ([0;1], []) \/ p = ([0;2], [])).
    rewrite !two_atoms_semantics. tauto.
Qed.

Lemma example2_branch_semantics p :
  rewpla_denote Nat.eqb example2_branch p <-> p = ([0;1], []).
Proof.
  unfold example2_branch. split.
  - intros [q [t [Hq [Ht Hout]]]].
    destruct Hq as [s [Hs ->]]. apply two_atoms_semantics in Hs. subst s.
    apply example2_prefix_semantics in Ht. destruct Ht as [Ht | Ht]; subst t;
      simpl in Hout; inversion Hout; reflexivity.
  - intros ->. exists ([],[0;1]), ([0;1], []). repeat split.
    + exists ([0;1], []). split.
      * apply two_atoms_semantics. reflexivity.
      * reflexivity.
    + apply example2_prefix_semantics. now left.
Qed.

Theorem paper_example2_pair_semantics p :
  rewpla_denote Nat.eqb example2 p <->
    p = ([0;1], []) \/ p = ([0;3], []).
Proof.
  change (rewpla_denote Nat.eqb example2_branch p \/
    rewpla_denote Nat.eqb (WConcat (WAtom 0) (WAtom 3)) p <->
    p = ([0;1], []) \/ p = ([0;3], [])).
  rewrite example2_branch_semantics, two_atoms_semantics. tauto.
Qed.

Theorem paper_example2_after_a_pair_semantics :
  lang_equiv
    (rewpla_denote Nat.eqb (word_derivative Nat.eqb [0] example2))
    (rewpla_denote Nat.eqb (WPlus (WAtom 1) (WAtom 3))).
Proof.
  eapply lang_equiv_trans.
  - apply word_derivative_correct. exact nat_eqb_spec.
  - intro p. change ((exists q, rewpla_denote Nat.eqb example2 q /\
      pair_word_quotient Nat.eqb [0] q = Some p) <->
      p = ([1], []) \/ p = ([3], [])). split.
    + intros [q [Hq Hout]]. apply paper_example2_pair_semantics in Hq.
      destruct Hq as [Hq | Hq]; subst q; simpl in Hout; inversion Hout; subst;
        simpl; auto.
    + intros [Hp | Hp]; subst p.
      * exists ([0;1], []). split; [apply paper_example2_pair_semantics; now left|reflexivity].
      * exists ([0;3], []). split; [apply paper_example2_pair_semantics; now right|reflexivity].
Qed.

Print Assumptions paper_example2_pair_semantics.
Print Assumptions paper_example2_after_a_pair_semantics.

Definition example2_unconstrained :=
  WPlus (WConcat (WAtom 0) (WAtom 1)) (WConcat (WAtom 0) (WAtom 3)).
Definition example2_residual_states :=
  [example2_unconstrained; WPlus (WAtom 1) (WAtom 3); WEps; WZero].
Definition example2_reaching_words : list (list nat) := [ []; [0]; [0;1]; [1] ].

Lemma example2_unconstrained_semantics p :
  rewpla_denote Nat.eqb example2_unconstrained p <->
    p = ([0;1], []) \/ p = ([0;3], []).
Proof.
  change (rewpla_denote Nat.eqb (WConcat (WAtom 0) (WAtom 1)) p \/
    rewpla_denote Nat.eqb (WConcat (WAtom 0) (WAtom 3)) p <->
    p = ([0;1], []) \/ p = ([0;3], [])).
  now rewrite !two_atoms_semantics.
Qed.

Lemma example2_unconstrained_equiv :
  lang_equiv (rewpla_denote Nat.eqb example2)
    (rewpla_denote Nat.eqb example2_unconstrained).
Proof. intro p. rewrite paper_example2_pair_semantics, example2_unconstrained_semantics. tauto. Qed.

Example example2_residual_table_closed :
  rewpla_paper_states_closedb Nat.eqb (fun n => n) [0;1;2;3]
    example2_residual_states = true.
Proof. vm_compute. reflexivity. Qed.

Example example2_witnesses_compute :
  map (fun w => rewpla_paper_word_step Nat.eqb (fun n => n)
    w example2_unconstrained) example2_reaching_words = example2_residual_states.
Proof. vm_compute. reflexivity. Qed.

Lemma example2_normalized_residual_correct w :
  lang_equiv (rewpla_denote Nat.eqb (word_derivative Nat.eqb w example2))
    (rewpla_denote Nat.eqb
      (rewpla_paper_word_step Nat.eqb (fun n => n) w example2_unconstrained)).
Proof.
  eapply lang_equiv_trans; [apply word_derivative_correct; exact nat_eqb_spec|].
  eapply lang_equiv_trans.
  - apply pair_language_word_quotient_compat. exact example2_unconstrained_equiv.
  - apply lang_equiv_sym, rewpla_paper_word_step_correct_M. exact nat_eqb_spec.
Qed.

Lemma example2_residual_states_reachable :
  semantic_reachable Nat.eqb example2 example2_residual_states.
Proof.
  intros r Hr. rewrite <- example2_witnesses_compute in Hr.
  apply in_map_iff in Hr as [w [<- Hw]]. exists w.
  apply lang_equiv_sym, example2_normalized_residual_correct.
Qed.

Lemma example2_residual_states_distinct :
  semantic_distinct Nat.eqb example2_residual_states.
Proof.
  unfold example2_residual_states. change
    ((forall s, In s [WPlus (WAtom 1) (WAtom 3);WEps;WZero] ->
      ~ lang_equiv (rewpla_denote Nat.eqb example2_unconstrained)
        (rewpla_denote Nat.eqb s)) /\
      semantic_distinct Nat.eqb [WPlus (WAtom 1) (WAtom 3);WEps;WZero]).
  split.
  - intros s Hs H. destruct Hs as [<-|[<-|[<-|[]]]];
      pose proof (H ([0;1], [])) as Hp; clear H;
      rewrite example2_unconstrained_semantics in Hp;
      cbv [rewpla_denote lang_union lang_one lang_zero] in Hp; intuition congruence.
  - change ((forall s, In s [WEps;WZero] ->
      ~ lang_equiv (rewpla_denote Nat.eqb (WPlus (WAtom 1) (WAtom 3)))
        (rewpla_denote Nat.eqb s)) /\ semantic_distinct Nat.eqb [WEps;WZero]).
    split.
    + intros s Hs H. destruct Hs as [<-|[<-|[]]];
        pose proof (H ([1], [])) as Hp; clear H;
        cbv [rewpla_denote lang_union lang_one lang_zero] in Hp; intuition congruence.
    + change ((forall s, In s [WZero] ->
        ~ lang_equiv (rewpla_denote Nat.eqb WEps) (rewpla_denote Nat.eqb s)) /\
        semantic_distinct Nat.eqb [WZero]).
      split; [|split; [intros s Hs; contradiction|exact I]]. intros s [<-|[]] H.
      pose proof (H ([], [])) as Hp.
      cbv [rewpla_denote lang_one lang_zero] in Hp. tauto.
Qed.

Theorem paper_example2_four_semantic_states :
  length example2_residual_states = 4 /\
  semantic_distinct Nat.eqb example2_residual_states /\
  semantic_reachable Nat.eqb example2 example2_residual_states /\
  forall w : list nat, (forall a, In a w -> In a [0;1;2;3]) ->
    exists e, In e example2_residual_states /\
      lang_equiv (rewpla_denote Nat.eqb (word_derivative Nat.eqb w example2))
        (rewpla_denote Nat.eqb e).
Proof.
  split; [reflexivity|]. split; [exact example2_residual_states_distinct|].
  split; [exact example2_residual_states_reachable|]. intros w Hw.
  exists (rewpla_paper_word_step Nat.eqb (fun n => n) w example2_unconstrained).
  split.
  - eapply rewpla_paper_states_closedb_all_words.
    + exact nat_eqb_spec.
    + exact example2_residual_table_closed.
    + now left.
    + exact Hw.
  - apply example2_normalized_residual_correct.
Qed.

Print Assumptions paper_example2_four_semantic_states.

(** [LA(a)] and [a] have the same projected word but different pair
    languages; the two witnesses below exercise both sides explicitly. *)
Example lookahead_a_pair :
  rewpla_denote Nat.eqb (WLookahead (WAtom 0)) ([], [0]).
Proof. exists ([0], []). now split. Qed.

Example atom_a_not_lookahead_pair :
  ~ rewpla_denote Nat.eqb (WAtom 0) ([], [0]).
Proof. simpl. discriminate. Qed.

Example lookahead_a_projected :
  rewpla_language Nat.eqb (WLookahead (WAtom 0)) [0].
Proof. exists ([], [0]). split; [apply lookahead_a_pair|reflexivity]. Qed.

Example atom_a_projected : rewpla_language Nat.eqb (WAtom 0) [0].
Proof. exists ([0], []). split; reflexivity. Qed.

(** Eq. (19) boundary cases. *)
Example lambda1_atom_false :
  ~ rewpla_has_empty_main Nat.eqb (WAtom 0).
Proof. intros [v H]. simpl in H. discriminate. Qed.

Example lambda1_lookahead_true :
  rewpla_has_empty_main Nat.eqb (WLookahead (WAtom 0)).
Proof. exists [0]. apply lookahead_a_pair. Qed.

Example lambda1_incompatible_concat_false :
  ~ rewpla_has_empty_main Nat.eqb
      (WConcat (WLookahead (WAtom 0)) (WLookahead (WAtom 1))).
Proof.
  intros [v [p [q [Hp [Hq Hout]]]]].
  destruct Hp as [x [Hx Hp]]. simpl in Hx. subst x p.
  destruct Hq as [x [Hx Hq]]. simpl in Hx. subst x q.
  simpl in Hout. discriminate.
Qed.

(** The exact user expression, with both repetition stars inside LA and with
    the powers 3 and 5 expanded into ordinary concatenation nodes. *)
Definition wthree : rewpla nat :=
  WConcat wab (WConcat wab wab).

Definition wfive : rewpla nat :=
  WConcat wab (WConcat wab (WConcat wab (WConcat wab wab))).

Definition requested_rewpla : rewpla nat :=
  WConcat
    (WConcat (WConcat (WStar wab) (WAtom 0))
      (WLookahead (WStar wthree)))
    (WLookahead (WStar wfive)).

(** The public debugging value contains every state, shortest witness,
    acceptance bit, residual vector and both outgoing transitions.  Use the
    following command interactively when the full 182-entry Rocq term is
    desired (the CLI JSON interface is normally easier to inspect):

    [Compute Mod15Example.requested_derivative_debug_states.]

    For actual derived REwPLA ASTs in addition to the bitvectors:
    [Compute requested_derivative_regex_states.] *)
Compute length Mod15Example.requested_derivative_debug_states.
Compute firstn 3 Mod15Example.requested_derivative_debug_states.
Compute length requested_derivative_regex_states.
Compute firstn 1 requested_derivative_regex_states.

Example requested_rewpla_exact_state_count :
  RequestedStateEnumeration.semantic_derivative_state_count
    RequestedStateEnumeration.requested_semantic_derivative_enumeration = 182.
Proof. exact RequestedStateEnumeration.requested_derivative_state_count_exact. Qed.

Print Assumptions requested_rewpla_exact_state_count.
Print Assumptions RequestedCorrespondence.requested_word_derivative_correspondence.
Print Assumptions RequestedCorrespondence.mod15_residual_language_injective.
Print Assumptions RequestedStateEnumeration.every_replay_in_values.
Print Assumptions RequestedStateEnumeration.requested_states_semantically_unique.
Print Assumptions requested_printed_regexes_semantically_unique.

(** Mechanization extension to paper Section 4.3 ACI: executable canonical
    representatives for commutativity, associativity and idempotence of [+]. *)
Definition aci_nat (r : rewpla nat) : rewpla nat :=
  rewpla_aci_normalize Nat.eqb (fun n => n) r.

Example aci_comm_ab :
  aci_nat (WPlus (WAtom 0) (WAtom 1)) =
  aci_nat (WPlus (WAtom 1) (WAtom 0)).
Proof. vm_compute. reflexivity. Qed.

Example aci_comm_ab_same_class :
  rewpla_aci_equiv Nat.eqb (fun n => n)
    (WPlus (WAtom 0) (WAtom 1))
    (WPlus (WAtom 1) (WAtom 0)).
Proof. exact aci_comm_ab. Qed.

Example aci_assoc_abc :
  aci_nat (WPlus (WPlus (WAtom 0) (WAtom 1)) (WAtom 2)) =
  aci_nat (WPlus (WAtom 0) (WPlus (WAtom 1) (WAtom 2))).
Proof. vm_compute. reflexivity. Qed.

Example aci_idempotent_a :
  aci_nat (WPlus (WAtom 0) (WAtom 0)) = aci_nat (WAtom 0).
Proof. vm_compute. reflexivity. Qed.

Example aci_zero_a :
  aci_nat (WPlus (WAtom 0) WZero) = aci_nat (WAtom 0).
Proof. vm_compute. reflexivity. Qed.

(** The two first-symbol derivatives are structurally different before ACI,
    but collapse to one state after the verified normalization. *)
Definition aci_state_merge_example : rewpla nat :=
  WPlus (WConcat (WAtom 0) (WPlus (WAtom 0) (WAtom 1)))
    (WConcat (WAtom 1) (WPlus (WAtom 1) (WAtom 0))).

Definition aci_raw_step (a : nat) (r : rewpla nat) : rewpla nat :=
  rewpla_simplify
    (derivative_merge (simplified_symbol_derivative Nat.eqb a r)).

Example aci_raw_first_derivatives_differ :
  rewpla_eqb Nat.eqb (aci_raw_step 0 aci_state_merge_example)
    (aci_raw_step 1 aci_state_merge_example) = false.
Proof. vm_compute. reflexivity. Qed.

Example aci_first_derivatives_merge :
  aci_nat (aci_raw_step 0 aci_state_merge_example) =
  aci_nat (aci_raw_step 1 aci_state_merge_example).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions aci_comm_ab.
Print Assumptions aci_assoc_abc.
Print Assumptions aci_idempotent_a.
Print Assumptions aci_first_derivatives_merge.

Example aci_canonical_normal_forms_reduce_duplicates :
  length (normal_forms [WAtom 0; WAtom 0] []) = 8 /\
  length (canonical_normal_forms Nat.eqb (fun n => n)
    [WAtom 0; WAtom 0] []) = 4.
Proof. vm_compute. auto. Qed.

(** The proposed three-term aa display omits the single shifted assertions.
    The exact pair (epsilon, bb) distinguishes it from the true derivative. *)
Definition requested_proposed_aa : rewpla bool :=
  WPlus RequestedCorrespondence.requested_rewpla_bool
    (WPlus RequestedCorrespondence.requested_context_product
      (WConcat
        (@PeriodicDisplay.shifted_assertion bool RequestedCorrespondence.sigma_regex 3 1)
        (@PeriodicDisplay.shifted_assertion bool RequestedCorrespondence.sigma_regex 5 1))).

Example requested_aa_derivative_contains_empty_main_bb :
  rewpla_denote Bool.eqb
    (word_derivative Bool.eqb [true;true]
      RequestedCorrespondence.requested_rewpla_bool) ([], [false;false]).
Proof.
  apply (proj2 (RequestedCorrespondence.requested_word_derivative_correspondence
    [true;true] ([], [false;false]))).
  vm_compute. right. now split.
Qed.

Example requested_proposed_aa_omits_empty_main_bb :
  ~ rewpla_denote Bool.eqb requested_proposed_aa ([], [false;false]).
Proof.
  unfold requested_proposed_aa.
  change (~ (rewpla_denote Bool.eqb RequestedCorrespondence.requested_rewpla_bool
    ([], [false;false]) \/
    rewpla_denote Bool.eqb RequestedCorrespondence.requested_context_product
      ([], [false;false]) \/
    rewpla_denote Bool.eqb
      (WConcat
        (@PeriodicDisplay.shifted_assertion bool RequestedCorrespondence.sigma_regex 3 1)
        (@PeriodicDisplay.shifted_assertion bool RequestedCorrespondence.sigma_regex 5 1))
      ([], [false;false]))).
  intros [H|[H|H]].
  - apply RequestedCorrespondence.requested_rewpla_semantics in H.
    destruct H as [[w Hw] _].
    apply (f_equal (@length bool)) in Hw. rewrite length_app in Hw. simpl in Hw. lia.
  - apply RequestedCorrespondence.requested_context_product_semantics in H.
    destruct H as [_ H]. discriminate H.
  - destruct H as [[u1 v1] [[u2 v2] [H1 [H2 Hout]]]].
    apply (proj1 (@PeriodicDisplay.shifted_assertion_semantics bool Bool.eqb
      RequestedCorrespondence.bool_eqb_spec RequestedCorrespondence.sigma_regex
      RequestedCorrespondence.matches_sigma_iff 3 1 u1 v1 ltac:(lia))) in H1.
    apply (proj1 (@PeriodicDisplay.shifted_assertion_semantics bool Bool.eqb
      RequestedCorrespondence.bool_eqb_spec RequestedCorrespondence.sigma_regex
      RequestedCorrespondence.matches_sigma_iff 5 1 u2 v2 ltac:(lia))) in H2.
    destruct H1 as [-> H1]. destruct H2 as [-> H2].
    pose proof (@constraint_concat_preservation bool Bool.eqb RequestedCorrespondence.bool_eqb_spec
      [] v1 [] v2 [false;false] Hout) as [_ Hprefix].
    destruct Hprefix as [suffix Heq].
    apply (f_equal (@length bool)) in Heq. rewrite length_app in Heq. simpl in Heq.
    apply Nat.eqb_eq in H2. rewrite Nat.mod_small in H2 by (simpl; lia). lia.
Qed.

Example requested_proposed_aa_is_not_derivative :
  ~ lang_equiv (rewpla_denote Bool.eqb
      (word_derivative Bool.eqb [true;true] RequestedCorrespondence.requested_rewpla_bool))
    (rewpla_denote Bool.eqb requested_proposed_aa).
Proof.
  intro H. apply requested_proposed_aa_omits_empty_main_bb.
  apply (proj1 (H ([], [false;false]))).
  exact requested_aa_derivative_contains_empty_main_bb.
Qed.

Print Assumptions requested_proposed_aa_is_not_derivative.

Print Assumptions aci_canonical_normal_forms_reduce_duplicates.
