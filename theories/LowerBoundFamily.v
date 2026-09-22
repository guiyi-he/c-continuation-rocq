From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import StringConstraints Syntax LookaheadSemantics
  ConstraintExpansion LookaheadDerivatives LookaheadDecision SemanticDFA
  DerivativeLowerBound.
Import ListNotations.
Set Implicit Arguments.

(** * The concrete lower-bound family of paper Section 4.3 *)

Inductive lower_symbol :=
| LBa | LBb | LBc | LBx (i : nat) | LBhash.

Definition lower_symbol_eqb (x y : lower_symbol) : bool :=
  match x, y with
  | LBa, LBa | LBb, LBb | LBc, LBc | LBhash, LBhash => true
  | LBx i, LBx j => Nat.eqb i j
  | _, _ => false
  end.

Lemma lower_symbol_eqb_spec x y :
  lower_symbol_eqb x y = true <-> x = y.
Proof.
  destruct x, y; simpl;
    try (split; [discriminate|intro H; discriminate]);
    try (split; intro H; reflexivity).
  rewrite Nat.eqb_eq. split; intro H; [now subst|now inversion H].
Qed.

Fixpoint regex_sum {A} (xs : list A) : regex A :=
  match xs with
  | [] => Zero
  | x :: xs' => Plus (Atom x) (regex_sum xs')
  end.

Lemma matches_regex_sum {A} (xs : list A) w :
  matches (regex_sum xs) w <-> exists x, In x xs /\ w = [x].
Proof.
  induction xs as [|x xs IH]; simpl.
  - split; [intro H; inversion H|intros [y [[] _]]].
  - split.
    + intro H. inversion H; subst.
      * match goal with Ha : matches (Atom x) _ |- _ => inversion Ha; subst end.
        exists x. split; [now left|reflexivity].
      * match goal with Hs : matches (regex_sum xs) _ |- _ =>
          apply IH in Hs as [y [Hy ->]]
        end.
        exists y. split; [now right|reflexivity].
    + intros [y [[<-|Hy] ->]].
      * apply M_PlusL. constructor.
      * apply M_PlusR, IH. exists y. now split.
Qed.

Definition core_atoms k : list lower_symbol :=
  [LBa; LBb; LBc] ++ map LBx (seq 0 k).

Definition core_regex k : regex lower_symbol := regex_sum (core_atoms k).
Definition core_symbol k (a : lower_symbol) : Prop := In a (core_atoms k).
Definition core_word k (w : list lower_symbol) : Prop := Forall (core_symbol k) w.

Lemma matches_core_regex k w :
  matches (core_regex k) w <-> exists a, core_symbol k a /\ w = [a].
Proof. apply matches_regex_sum. Qed.

Lemma core_word_app k u v :
  core_word k (u ++ v) <-> core_word k u /\ core_word k v.
Proof. unfold core_word. now rewrite Forall_app. Qed.

Lemma core_a k : core_symbol k LBa.
Proof. unfold core_symbol, core_atoms. simpl. auto. Qed.
Lemma core_b k : core_symbol k LBb.
Proof. unfold core_symbol, core_atoms. simpl. auto. Qed.
Lemma core_c k : core_symbol k LBc.
Proof. unfold core_symbol, core_atoms. simpl. auto. Qed.

Lemma core_x k i : i < k -> core_symbol k (LBx i).
Proof.
  intro Hi. unfold core_symbol, core_atoms. apply in_app_iff. right.
  apply in_map. apply in_seq. lia.
Qed.

Lemma core_not_hash k : ~ core_symbol k LBhash.
Proof.
  unfold core_symbol, core_atoms. rewrite in_app_iff. intros [H|H].
  - simpl in H. destruct H as [H|[H|[H|[]]]]; discriminate.
  - apply in_map_iff in H as [i [H _]]. discriminate.
Qed.

Lemma matches_core_star k w :
  matches (Star (core_regex k)) w <-> core_word k w.
Proof.
  split.
  - intro H. remember (Star (core_regex k)) as sr eqn:Hsr in H.
    induction H; inversion Hsr; subst.
    + constructor.
    + apply (proj2 (core_word_app k _ _)). split.
      apply matches_core_regex in H0 as [a [Ha ->]].
      unfold core_word. now constructor.
      apply IHmatches2. reflexivity.
  - intro H. induction H as [|a w Ha Hw IH].
    + constructor.
    + change (matches (Star (core_regex k)) ([a] ++ w)).
      apply M_StarApp.
      * discriminate.
      * apply matches_core_regex. exists a. now split.
      * exact IH.
Qed.

Definition lower_assertion k i : rewpla lower_symbol :=
  WLookahead (embed_regex
    (Concat (Star (core_regex k)) (Atom (LBx i)))).

Definition has_core_x k i (z : list lower_symbol) : Prop :=
  exists pre, core_word k pre /\ word_prefix (pre ++ [LBx i]) z.

Lemma lower_assertion_satisfies k i u z :
  suffix_satisfies lower_symbol_eqb (lower_assertion k i) u z <->
  u = [] /\ has_core_x k i z.
Proof.
  unfold lower_assertion.
  rewrite suffix_satisfies_lookahead. split.
  - intros [-> [[m c] [Hden Hprefix]]].
    apply (proj1 (embed_regex_semantics lower_symbol_eqb
      lower_symbol_eqb_spec _ (m,c))) in Hden.
    destruct Hden as [w [Heq Hmatch]]. inversion Heq; subst m c.
    inversion Hmatch; subst.
    match goal with Hs : matches (Star (core_regex k)) ?pre,
                    Hx : matches (Atom (LBx i)) ?tail |- _ =>
      inversion Hx; subst tail;
      split; [reflexivity|exists pre; split]
    end.
    + now apply matches_core_star.
    + change (word_prefix ((u ++ [LBx i]) ++ []) z) in Hprefix.
      now rewrite app_nil_r in Hprefix.
  - intros [-> [pre [Hcore Hprefix]]]. split; [reflexivity|].
    exists (pre ++ [LBx i], []). split.
    + apply (proj2 (embed_regex_semantics lower_symbol_eqb
        lower_symbol_eqb_spec _ (pre ++ [LBx i], []))).
      exists (pre ++ [LBx i]). split; [reflexivity|].
      apply M_Concat; [now apply matches_core_star|constructor].
    + change (word_prefix ((pre ++ [LBx i]) ++ []) z).
      now rewrite app_nil_r.
Qed.

Definition lower_choice k i : rewpla lower_symbol :=
  WPlus (WAtom LBb) (WConcat (WAtom LBc) (lower_assertion k i)).

Lemma lower_choice_satisfies k i u z :
  suffix_satisfies lower_symbol_eqb (lower_choice k i) u z <->
  u = [LBb] \/ (u = [LBc] /\ has_core_x k i z).
Proof.
  unfold lower_choice. rewrite suffix_satisfies_plus,
    suffix_satisfies_atom,
    (suffix_satisfies_concat lower_symbol_eqb lower_symbol_eqb_spec). split.
  - intros [->|[x [y [Hxy [Hx Hy]]]]]; [now left|].
    apply suffix_satisfies_atom in Hx.
    apply lower_assertion_satisfies in Hy as [-> Hreq].
    subst x. simpl in Hxy. subst u. now right.
  - intros [->|[-> Hreq]].
    + now left.
    + right. exists [LBc], []. split; [reflexivity|]. split.
      * apply suffix_satisfies_atom. reflexivity.
      * apply lower_assertion_satisfies. now split.
Qed.

Fixpoint lower_choices k (is : list nat) : rewpla lower_symbol :=
  match is with
  | [] => WEps
  | i :: is' => WConcat (lower_choice k i) (lower_choices k is')
  end.

Definition selected_symbols (is S : list nat) : list lower_symbol :=
  map (fun i => if existsb (Nat.eqb i) S then LBc else LBb) is.

Lemma selected_symbols_core k is S :
  core_word k (selected_symbols is S).
Proof.
  unfold selected_symbols, core_word. apply Forall_forall.
  intros x Hx. apply in_map_iff in Hx as [i [<- _]].
  destruct (existsb (Nat.eqb i) S); [apply core_c|apply core_b].
Qed.

Lemma selected_symbols_no_x is S j : ~ In (LBx j) (selected_symbols is S).
Proof.
  unfold selected_symbols. intro H. apply in_map_iff in H as [i [H _]].
  destruct (existsb (Nat.eqb i) S); discriminate.
Qed.

Lemma nat_mem_existsb i S : existsb (Nat.eqb i) S = true <-> In i S.
Proof.
  rewrite existsb_exists. split.
  - intros [j [Hj Hij]]. apply Nat.eqb_eq in Hij. now subst.
  - intro Hi. exists i. split; [exact Hi|apply Nat.eqb_refl].
Qed.

Lemma has_core_x_before_hash k i core :
  core_word k core ->
  (has_core_x k i (core ++ [LBhash]) <-> In (LBx i) core).
Proof.
  intro Hcore. unfold has_core_x. split.
  - intros [pre [_ [tail Heq]]].
    assert (Hin : In (LBx i) (core ++ [LBhash])).
    { rewrite Heq, <- app_assoc. apply in_app_iff. right. simpl. auto. }
    apply in_app_iff in Hin as [Hin|Hin]; [exact Hin|].
    simpl in Hin. destruct Hin as [H|[]]. discriminate.
  - intro Hin. apply in_split in Hin as [left [right Heq]].
    exists left. split.
    + unfold core_word in *. subst core.
      apply Forall_app in Hcore as [Hleft _]. exact Hleft.
    + exists (right ++ [LBhash]). subst core.
      rewrite <- !app_assoc. reflexivity.
Qed.

Theorem lower_choices_selected_satisfies k is S core :
  core_word k core ->
  (suffix_satisfies lower_symbol_eqb (lower_choices k is)
      (selected_symbols is S) (core ++ [LBhash]) <->
   forall i, In i is -> In i S -> In (LBx i) core).
Proof.
  intro Hcore. revert core Hcore.
  induction is as [|i is IH]; intros core Hcore; simpl [lower_choices selected_symbols].
  - rewrite suffix_satisfies_eps. split.
    + intros _. intros j [] _.
    + intros _. reflexivity.
  - rewrite (suffix_satisfies_concat lower_symbol_eqb lower_symbol_eqb_spec).
    remember (existsb (Nat.eqb i) S) as hit eqn:Hhit.
    destruct hit.
    + split.
      * intros [u [u' [Hout [Hchoice Hrest]]]].
        apply lower_choice_satisfies in Hchoice as [Hu|[Hu Hreq]].
        { subst u. simpl in Hout. discriminate. }
        subst u. simpl in Hout. inversion Hout; subst u'.
        assert (Hxi : In (LBx i) core).
        { assert (Hcombined : core_word k (selected_symbols is S ++ core)).
          { apply (proj2 (core_word_app k _ _)).
            split; [apply selected_symbols_core|exact Hcore]. }
          assert (Hin : In (LBx i) (selected_symbols is S ++ core)).
          { apply (proj1 (has_core_x_before_hash
              (k:=k) i Hcombined)).
            destruct Hreq as [pre [Hpre Hp]].
            exists pre. split; [exact Hpre|].
            replace ((selected_symbols is S ++ core) ++ [LBhash])
              with (selected_symbols is S ++ (core ++ [LBhash])).
            - exact Hp.
            - apply app_assoc. }
          apply in_app_iff in Hin as [Hin|Hin]; [|exact Hin].
          exfalso. now apply (selected_symbols_no_x is S i). }
        assert (Htail : forall j, In j is -> In j S -> In (LBx j) core).
        { apply (proj1 (IH core Hcore)). exact Hrest. }
        intros j [<-|Hj] HjS; [exact Hxi|now apply Htail].
      * intro Hall.
        exists [LBc], (selected_symbols is S). split; [reflexivity|]. split.
        -- apply lower_choice_satisfies. right. split; [reflexivity|].
           assert (Hcombined : core_word k (selected_symbols is S ++ core)).
           { apply (proj2 (core_word_app k _ _)).
             split; [apply selected_symbols_core|exact Hcore]. }
           assert (Hleft : has_core_x k i
               ((selected_symbols is S ++ core) ++ [LBhash])).
           { apply (proj2 (has_core_x_before_hash
               (k:=k) i Hcombined)).
             apply in_app_iff. right. apply Hall; [now left|].
             apply nat_mem_existsb. symmetry. exact Hhit. }
           destruct Hleft as [pre [Hpre Hp]]. exists pre. split; [exact Hpre|].
           replace (selected_symbols is S ++ (core ++ [LBhash]))
             with ((selected_symbols is S ++ core) ++ [LBhash]).
           ++ exact Hp.
           ++ symmetry. apply app_assoc.
        -- apply (proj2 (IH core Hcore)).
           intros j Hj HjS. apply Hall; [now right|exact HjS].
    + split.
      * intros [u [u' [Hout [Hchoice Hrest]]]].
        apply lower_choice_satisfies in Hchoice as [Hu|[Hu Hreq]].
        2:{ subst u. simpl in Hout. discriminate. }
        subst u. simpl in Hout. inversion Hout; subst u'.
        assert (Htail : forall j, In j is -> In j S -> In (LBx j) core).
        { apply (proj1 (IH core Hcore)). exact Hrest. }
        intros j [<-|Hj] HjS.
        -- apply nat_mem_existsb in HjS. congruence.
        -- now apply Htail.
      * intro Hall.
        exists [LBb], (selected_symbols is S). split; [reflexivity|]. split.
        -- apply lower_choice_satisfies. now left.
        -- apply (proj2 (IH core Hcore)).
           intros j Hj HjS. apply Hall; [now right|exact HjS].
Qed.

Definition lower_block k (S : list nat) : list lower_symbol :=
  LBa :: selected_symbols (seq 0 k) S.

Fixpoint lower_family_prefix k (F : list (list nat)) : list lower_symbol :=
  match F with
  | [] => []
  | sset :: F' => lower_block k sset ++ lower_family_prefix k F'
  end.

Definition lower_test (T : list nat) : list lower_symbol :=
  map LBx T ++ [LBhash].

Definition lower_suffix_regex k : regex lower_symbol :=
  Concat (Star (core_regex k)) (Atom LBhash).

Definition lower_expression k : rewpla lower_symbol :=
  WConcat (embed_regex (Star (core_regex k)))
    (WConcat (WAtom LBa)
      (WConcat (lower_choices k (seq 0 k))
        (embed_regex (lower_suffix_regex k)))).

Definition valid_middle_set k (S : list nat) : Prop :=
  In S (middle_subsets k).

Definition valid_middle_family k (F : list (list nat)) : Prop :=
  forall S, In S F -> valid_middle_set k S.

Lemma valid_middle_set_length k S : valid_middle_set k S -> length S = k / 2.
Proof.
  unfold valid_middle_set, middle_subsets. intro H.
  now apply combinations_members_length in H.
Qed.

Lemma valid_middle_set_range k S i :
  valid_middle_set k S -> In i S -> i < k.
Proof.
  unfold valid_middle_set, middle_subsets. intros HS Hi.
  pose proof (combinations_members_source (k / 2) (seq 0 k) S HS i Hi)
    as Hseq.
  apply in_seq in Hseq. lia.
Qed.

Lemma selected_symbols_length is S :
  length (selected_symbols is S) = length is.
Proof. unfold selected_symbols. apply length_map. Qed.

Lemma selected_symbols_no_a is S : ~ In LBa (selected_symbols is S).
Proof.
  unfold selected_symbols. intro H. apply in_map_iff in H as [i [H _]].
  destruct (existsb (Nat.eqb i) S); discriminate.
Qed.

Lemma selected_symbols_no_hash is S : ~ In LBhash (selected_symbols is S).
Proof.
  unfold selected_symbols. intro H. apply in_map_iff in H as [i [H _]].
  destruct (existsb (Nat.eqb i) S); discriminate.
Qed.

Lemma lower_family_prefix_core k F : core_word k (lower_family_prefix k F).
Proof.
  induction F as [|S F IH]; simpl; [constructor|].
  unfold core_word in *. constructor; [apply core_a|].
  apply Forall_app. split; [apply selected_symbols_core|exact IH].
Qed.

Lemma lower_family_prefix_no_x k F i :
  ~ In (LBx i) (lower_family_prefix k F).
Proof.
  induction F as [|S F IH].
  - simpl. tauto.
  - cbn [lower_family_prefix lower_block]. intros [H|H]; [discriminate|].
    apply in_app_iff in H as [H|H].
    + now apply (selected_symbols_no_x (seq 0 k) S i).
    + now apply IH.
Qed.

Lemma lower_family_prefix_no_hash k F :
  ~ In LBhash (lower_family_prefix k F).
Proof.
  induction F as [|S F IH].
  - simpl. tauto.
  - cbn [lower_family_prefix lower_block]. intros [H|H]; [discriminate|].
    apply in_app_iff in H as [H|H].
    + now apply (selected_symbols_no_hash (seq 0 k) S).
    + now apply IH.
Qed.

Lemma lower_test_core_without_hash k T :
  valid_middle_set k T -> core_word k (map LBx T).
Proof.
  intros HT. unfold core_word. apply Forall_forall.
  intros x Hx. apply in_map_iff in Hx as [i [<- Hi]].
  apply core_x. now apply (valid_middle_set_range k T i HT Hi).
Qed.

Lemma lower_test_no_a T : ~ In LBa (lower_test T).
Proof.
  unfold lower_test. rewrite in_app_iff. intros [H|H].
  - apply in_map_iff in H as [i [H _]]. discriminate.
  - simpl in H. destruct H as [H|[]]. discriminate.
Qed.

Lemma lower_test_no_hash_prefix T : ~ In LBhash (map LBx T).
Proof.
  intro H. apply in_map_iff in H as [i [H _]]. discriminate.
Qed.

Lemma no_marker_split {X} (marker : X) xs rest pre after :
  ~ In marker xs ->
  xs ++ rest = pre ++ marker :: after ->
  exists pre', pre = xs ++ pre' /\ rest = pre' ++ marker :: after.
Proof.
  revert pre. induction xs as [|x xs IH]; intros pre Hnone Heq; simpl in *.
  - exists pre. now split.
  - destruct pre as [|p pre].
    + inversion Heq; subst x. exfalso. apply Hnone. now left.
    + inversion Heq; subst p. destruct (IH pre) as [pre' [-> Hrest]].
      * intro Hin. apply Hnone. now right.
      * exact H1.
      * exists pre'. split; [reflexivity|exact Hrest].
Qed.

Lemma equal_length_app_prefix {X} (xs ys rest tail : list X) :
  length xs = length ys -> xs ++ rest = ys ++ tail -> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen Heq;
    simpl in *; try discriminate; [reflexivity|].
  inversion Heq; subst y. f_equal. apply IH; [lia|exact H1].
Qed.

Theorem lower_family_block_parser k F T pre bits tail :
  lower_family_prefix k F ++ lower_test T =
    pre ++ LBa :: bits ++ tail ->
  length bits = k ->
  exists S, In S F /\ bits = selected_symbols (seq 0 k) S.
Proof.
  revert pre bits tail. induction F as [|S F IH]; intros pre bits tail Heq Hlen.
  - simpl in Heq. exfalso. apply (lower_test_no_a T).
    rewrite Heq. apply in_app_iff. right. simpl. now left.
  - simpl in Heq. unfold lower_block in Heq. simpl in Heq.
    destruct pre as [|p pre].
    + injection Heq as HrestEq.
      exists S. split; [now left|].
      symmetry. eapply equal_length_app_prefix.
      * rewrite selected_symbols_length, length_seq. symmetry. exact Hlen.
      * rewrite <- app_assoc in HrestEq. exact HrestEq.
    + injection Heq as Hp HrestEq. subst p.
      destruct (no_marker_split LBa
        (selected_symbols (seq 0 k) S)
        (lower_family_prefix k F ++ lower_test T) pre (bits ++ tail))
        as [pre' [Hpre Hrest]].
      * apply selected_symbols_no_a.
      * rewrite <- app_assoc in HrestEq. exact HrestEq.
      * subst pre. destruct (IH pre' bits tail) as [S' [HS' Hbits]].
        -- exact Hrest.
        -- exact Hlen.
        -- exists S'. split; [now right|exact Hbits].
Qed.

Lemma lower_suffix_regex_matches k w :
  matches (lower_suffix_regex k) w <->
  exists core, w = core ++ [LBhash] /\ core_word k core.
Proof.
  unfold lower_suffix_regex. split.
  - intro H. inversion H; subst.
    match goal with Hstar : matches (Star (core_regex k)) ?core,
                    Hhash : matches (Atom LBhash) ?last |- _ =>
      inversion Hhash; subst last;
      exists core; split; [reflexivity|now apply matches_core_star]
    end.
  - intros [core [-> Hcore]].
    apply M_Concat; [now apply matches_core_star|constructor].
Qed.

Lemma denote_implies_suffix_satisfies r u v :
  rewpla_denote lower_symbol_eqb r (u,v) ->
  suffix_satisfies lower_symbol_eqb r u v.
Proof.
  intro H. exists v. split; [exact H|apply word_prefix_refl].
Qed.

Theorem lower_expression_suffix_characterization k full z :
  suffix_satisfies lower_symbol_eqb (lower_expression k) full z <->
  exists pre bits core,
    full = pre ++ (LBa :: bits ++ (core ++ [LBhash])) /\
    core_word k pre /\ core_word k core /\
    suffix_satisfies lower_symbol_eqb (lower_choices k (seq 0 k))
      bits ((core ++ [LBhash]) ++ z).
Proof.
  unfold lower_expression.
  rewrite (suffix_satisfies_concat lower_symbol_eqb lower_symbol_eqb_spec).
  split.
  - intros [pre [rest [Hfull [Hpre Hrest]]]].
    apply (proj1 (suffix_satisfies_concat lower_symbol_eqb
      lower_symbol_eqb_spec _ _ _ _)) in Hrest.
    destruct Hrest as [a [rest' [Hrest [Ha Hrest']]]].
    apply (proj1 (suffix_satisfies_concat lower_symbol_eqb
      lower_symbol_eqb_spec _ _ _ _)) in Hrest'.
    destruct Hrest' as [bits [suffix [Hsuffix [Hchoices Hfinal]]]].
    apply (suffix_satisfies_embed lower_symbol_eqb lower_symbol_eqb_spec)
      in Hpre.
    apply matches_core_star in Hpre.
    apply suffix_satisfies_atom in Ha. subst a.
    apply (suffix_satisfies_embed lower_symbol_eqb lower_symbol_eqb_spec)
      in Hfinal.
    apply lower_suffix_regex_matches in Hfinal as [core [Hcoreword Hcore]].
    subst suffix rest' rest full.
    exists pre, bits, core. repeat split; try assumption.
  - intros [pre [bits [core [Hfull [Hpre [Hcore Hchoices]]]]]].
    exists pre, (LBa :: bits ++ (core ++ [LBhash])). split.
    + exact Hfull.
    + split.
      * apply (suffix_satisfies_embed lower_symbol_eqb lower_symbol_eqb_spec),
          matches_core_star. exact Hpre.
      * apply (proj2 (suffix_satisfies_concat lower_symbol_eqb
          lower_symbol_eqb_spec _ _ _ _)).
        exists [LBa], (bits ++ (core ++ [LBhash])). split; [reflexivity|].
        split.
        -- apply suffix_satisfies_atom. reflexivity.
        -- apply (proj2 (suffix_satisfies_concat lower_symbol_eqb
             lower_symbol_eqb_spec _ _ _ _)).
           exists bits, (core ++ [LBhash]). split; [reflexivity|]. split.
           ++ exact Hchoices.
           ++ apply (suffix_satisfies_embed lower_symbol_eqb
                lower_symbol_eqb_spec), lower_suffix_regex_matches.
              exists core. now split.
Qed.

Lemma ending_marker_prefix_unique {X} (marker : X) core u v :
  ~ In marker core ->
  u ++ v = core ++ [marker] ->
  (exists pre, u = pre ++ [marker]) ->
  u = core ++ [marker] /\ v = [].
Proof.
  intros Hnone Heq [pre Hu]. destruct v as [|x xs].
  - split; [now rewrite app_nil_r in Heq|reflexivity].
  - exfalso. apply Hnone.
    assert (Hin : In marker u).
    { subst u. apply in_app_iff. right. simpl. now left. }
    assert (HinRemove : In marker (removelast (u ++ x :: xs))).
    { rewrite removelast_app by discriminate. apply in_app_iff. now left. }
    rewrite Heq, removelast_last in HinRemove. exact HinRemove.
Qed.

Lemma lower_full_core k F T :
  valid_middle_set k T ->
  core_word k (lower_family_prefix k F ++ map LBx T).
Proof.
  intro HT. apply (proj2 (core_word_app k _ _)). split.
  - apply lower_family_prefix_core.
  - now apply lower_test_core_without_hash.
Qed.

Lemma lower_full_core_no_hash k F T :
  ~ In LBhash (lower_family_prefix k F ++ map LBx T).
Proof.
  rewrite in_app_iff. intros [H|H].
  - now apply (lower_family_prefix_no_hash k F).
  - now apply (lower_test_no_hash_prefix T).
Qed.

Theorem lower_expression_projected_exact k F T :
  valid_middle_set k T ->
  (rewpla_language lower_symbol_eqb (lower_expression k)
      (lower_family_prefix k F ++ lower_test T) <->
   rewpla_denote lower_symbol_eqb (lower_expression k)
      (lower_family_prefix k F ++ lower_test T, [])).
Proof.
  intro HT. unfold rewpla_language, project_language. split.
  - intros [[u v] [Hden Hproj]].
    pose proof (denote_implies_suffix_satisfies
      (lower_expression k) u v Hden)
      as Hsat.
    apply lower_expression_suffix_characterization in Hsat
      as [pre [bits [core [Hu _]]]].
    assert (Huend : exists before, u = before ++ [LBhash]).
    { subst u. exists (pre ++ (LBa :: bits ++ core)).
      rewrite (app_assoc bits core [LBhash]).
      exact (app_assoc pre (LBa :: bits ++ core) [LBhash]). }
    unfold lower_test in Hproj.
    rewrite app_assoc in Hproj.
    destruct (@ending_marker_prefix_unique lower_symbol LBhash
      (lower_family_prefix k F ++ map LBx T) u v
      (lower_full_core_no_hash k F T) Hproj Huend) as [-> ->].
    replace (lower_family_prefix k F ++ lower_test T)
      with ((lower_family_prefix k F ++ map LBx T) ++ [LBhash]).
    + exact Hden.
    + unfold lower_test. symmetry. apply app_assoc.
  - intro Hden. exists (lower_family_prefix k F ++ lower_test T, []).
    split; [exact Hden|]. unfold constraint_projection. simpl. now rewrite app_nil_r.
Qed.

Lemma lower_choice_main_length k i u z :
  suffix_satisfies lower_symbol_eqb (lower_choice k i) u z -> length u = 1.
Proof.
  intro H. apply lower_choice_satisfies in H as [->|[-> _]]; reflexivity.
Qed.

Lemma lower_choices_main_length k is u z :
  suffix_satisfies lower_symbol_eqb (lower_choices k is) u z ->
  length u = length is.
Proof.
  revert u z. induction is as [|i is IH]; intros u z H; simpl in *.
  - apply suffix_satisfies_eps in H. now subst.
  - apply (proj1 (suffix_satisfies_concat lower_symbol_eqb
      lower_symbol_eqb_spec _ _ _ _)) in H.
    destruct H as [x [y [-> [Hx Hy]]]]. rewrite length_app.
    rewrite (lower_choice_main_length Hx), (IH _ _ Hy). reflexivity.
Qed.

Lemma lower_family_prefix_app k F G :
  lower_family_prefix k (F ++ G) =
  lower_family_prefix k F ++ lower_family_prefix k G.
Proof.
  induction F as [|S F IH]; simpl; [reflexivity|].
  now rewrite IH, app_assoc.
Qed.

Lemma lower_full_x_membership k F T i :
  In (LBx i) (lower_family_prefix k F ++ lower_test T) -> In i T.
Proof.
  unfold lower_test. rewrite in_app_iff. intros [H|H].
  - exfalso. now apply (lower_family_prefix_no_x k F i).
  - apply in_app_iff in H as [H|H].
    + apply in_map_iff in H as [j [Heq Hj]]. inversion Heq. now subst.
    + simpl in H. destruct H as [H|[]]. discriminate.
Qed.

Lemma suffix_satisfies_empty_exact r u :
  suffix_satisfies lower_symbol_eqb r u [] <->
  rewpla_denote lower_symbol_eqb r (u, []).
Proof.
  unfold suffix_satisfies, constraint_expansion. simpl. split.
  - intros [v [H [tail Heq]]]. symmetry in Heq.
    apply app_eq_nil in Heq as [-> ->]. exact H.
  - intro H. exists []. split; [exact H|apply word_prefix_refl].
Qed.

Lemma lower_word_reassociate {X : Type} (m : X) b s a x h :
  (b ++ (m :: (s ++ a))) ++ (x ++ h) =
  b ++ (m :: (s ++ ((a ++ x) ++ h))).
Proof.
  induction b as [|q b IH]; simpl.
  - f_equal. induction s as [|q s IHs]; simpl; [apply app_assoc|].
    now f_equal.
  - now f_equal.
Qed.

Theorem lower_bound_membership k F T :
  valid_middle_family k F -> valid_middle_set k T ->
  (rewpla_language lower_symbol_eqb (lower_expression k)
      (lower_family_prefix k F ++ lower_test T) <->
   exists S, In S F /\ incl S T).
Proof.
  intros HF HT. rewrite (lower_expression_projected_exact k F T HT).
  rewrite <- suffix_satisfies_empty_exact.
  rewrite lower_expression_suffix_characterization. split.
  - intros [pre [bits [core [Hfull [Hpre [Hcore Hchoices]]]]]].
    simpl in Hchoices. rewrite app_nil_r in Hchoices.
    assert (Hlen : length bits = k).
    { pose proof (@lower_choices_main_length k (seq 0 k) bits
        (core ++ [LBhash]) Hchoices) as Hlen'.
      now rewrite length_seq in Hlen'. }
    destruct (@lower_family_block_parser k F T pre bits (core ++ [LBhash])
      Hfull Hlen) as [S [HS Hbits]].
    exists S. split; [exact HS|]. intros i Hi.
    assert (HiRange : i < k).
    { apply (valid_middle_set_range k S i (HF S HS) Hi). }
    assert (HxiCore : In (LBx i) core).
    { subst bits.
      pose proof (proj1 (@lower_choices_selected_satisfies
        k (seq 0 k) S core Hcore) Hchoices) as HallChoices.
      apply HallChoices; [apply in_seq; lia|exact Hi]. }
    apply (lower_full_x_membership k F T i).
    rewrite Hfull. apply in_app_iff. right. simpl. right.
    apply in_app_iff. right. apply in_app_iff. now left.
  - intros [S [HS HST]]. apply in_split in HS as [before [after HFsplit]].
    subst F.
    set (pre := lower_family_prefix k before).
    set (bits := selected_symbols (seq 0 k) S).
    set (core := lower_family_prefix k after ++ map LBx T).
    exists pre, bits, core. repeat split.
    + unfold pre, bits, core, lower_test. simpl.
      rewrite lower_family_prefix_app. simpl.
      exact (@lower_word_reassociate lower_symbol LBa
        (lower_family_prefix k before) (selected_symbols (seq 0 k) S)
        (lower_family_prefix k after) (map LBx T) [LBhash]).
    + unfold pre. apply lower_family_prefix_core.
    + unfold core. apply (proj2 (core_word_app k _ _)). split.
      * apply lower_family_prefix_core.
      * now apply lower_test_core_without_hash.
    + simpl. rewrite app_nil_r. unfold bits.
      assert (Hcore' : core_word k core).
      { unfold core. apply (proj2 (core_word_app k _ _)). split.
        - apply lower_family_prefix_core.
        - now apply lower_test_core_without_hash. }
      apply (proj2 (@lower_choices_selected_satisfies
        k (seq 0 k) S core Hcore')).
      intros i _ Hi. unfold core. apply in_app_iff. right.
      apply in_map. now apply HST.
Qed.

(** The two finite enumerators used by the lower-bound construction are
    canonical: every generated list follows the order of its source.  The
    following lemmas make that fact constructive, so the separation argument
    below does not rely on classical extensionality for finite sets. *)

Lemma subsets_members_source {X : Type} (xs ys : list X) :
  In ys (subsets xs) -> forall y, In y ys -> In y xs.
Proof.
  revert ys. induction xs as [|x xs IH]; intros ys Hys y Hy; simpl in *.
  - destruct Hys as [<-|[]]. contradiction.
  - apply in_app_iff in Hys as [Hys|Hys].
    + right. eapply IH; eauto.
    + apply in_map_iff in Hys as [zs [<- Hzs]].
      destruct Hy as [<-|Hy]; [now left|right; eapply IH; eauto].
Qed.

Lemma combinations_member_nodup {X : Type} k (xs ys : list X) :
  NoDup xs -> In ys (combinations k xs) -> NoDup ys.
Proof.
  revert k ys. induction xs as [|x xs IH]; intros [|k] ys Hnd Hys;
    simpl in Hys.
  - destruct Hys as [<-|[]]. constructor.
  - contradiction.
  - destruct Hys as [<-|[]]. constructor.
  - inversion Hnd as [|? ? Hnot Htail]; subst.
    apply in_app_iff in Hys as [Hys|Hys].
    + eapply IH; eauto.
    + apply in_map_iff in Hys as [zs [<- Hzs]]. constructor.
      * intro Hx. apply Hnot. eapply combinations_members_source; eauto.
      * eapply IH; eauto.
Qed.

Lemma combinations_extensional_unique {X : Type}
    (eq_dec : forall x y : X, {x = y} + {x <> y}) k
    (xs ys zs : list X) :
  NoDup xs ->
  In ys (combinations k xs) -> In zs (combinations k xs) ->
  (forall q, In q ys <-> In q zs) -> ys = zs.
Proof.
  revert k ys zs. induction xs as [|x xs IH];
    intros [|k] ys zs Hnd Hys Hzs Heq; simpl in *.
  - destruct Hys as [<-|[]]. destruct Hzs as [<-|[]]. reflexivity.
  - contradiction.
  - destruct Hys as [<-|[]]. destruct Hzs as [<-|[]]. reflexivity.
  - inversion Hnd as [|? ? Hnot Htail]; subst.
    apply in_app_iff in Hys as [Hys|Hys];
      apply in_app_iff in Hzs as [Hzs|Hzs].
    + eapply IH; eauto.
    + apply in_map_iff in Hzs as [zs' [<- Hzs']]. exfalso.
      assert (Hin : In x ys) by (apply (proj2 (Heq x)); now left).
      apply Hnot. exact (@combinations_members_source X (S k) xs ys Hys x Hin).
    + apply in_map_iff in Hys as [ys' [<- Hys']]. exfalso.
      assert (Hin : In x zs) by (apply (proj1 (Heq x)); now left).
      apply Hnot. exact (@combinations_members_source X (S k) xs zs Hzs x Hin).
    + apply in_map_iff in Hys as [ys' [<- Hys']].
      apply in_map_iff in Hzs as [zs' [<- Hzs']]. f_equal.
      eapply IH; eauto. intro q. destruct (eq_dec q x) as [->|Hneq].
      * assert (Hny : ~ In x ys').
        { intro Hin. apply Hnot.
          exact (@combinations_members_source X k xs ys' Hys' x Hin). }
        assert (Hnz : ~ In x zs').
        { intro Hin. apply Hnot.
          exact (@combinations_members_source X k xs zs' Hzs' x Hin). }
        tauto.
      * split; intro Hq.
        -- pose proof (proj1 (Heq q) (or_intror Hq)) as H.
           destruct H as [H|H]; [now symmetry in H|exact H].
        -- pose proof (proj2 (Heq q) (or_intror Hq)) as H.
           destruct H as [H|H]; [now symmetry in H|exact H].
Qed.

Lemma subsets_extensional_unique {X : Type}
    (eq_dec : forall x y : X, {x = y} + {x <> y})
    (xs ys zs : list X) :
  NoDup xs ->
  In ys (subsets xs) -> In zs (subsets xs) ->
  (forall q, In q ys <-> In q zs) -> ys = zs.
Proof.
  revert ys zs. induction xs as [|x xs IH];
    intros ys zs Hnd Hys Hzs Heq; simpl in *.
  - destruct Hys as [<-|[]]. destruct Hzs as [<-|[]]. reflexivity.
  - inversion Hnd as [|? ? Hnot Htail]; subst.
    apply in_app_iff in Hys as [Hys|Hys];
      apply in_app_iff in Hzs as [Hzs|Hzs].
    + eapply IH; eauto.
    + apply in_map_iff in Hzs as [zs' [<- Hzs']]. exfalso.
      assert (Hin : In x ys) by (apply (proj2 (Heq x)); now left).
      apply Hnot. exact (@subsets_members_source X xs ys Hys x Hin).
    + apply in_map_iff in Hys as [ys' [<- Hys']]. exfalso.
      assert (Hin : In x zs) by (apply (proj1 (Heq x)); now left).
      apply Hnot. exact (@subsets_members_source X xs zs Hzs x Hin).
    + apply in_map_iff in Hys as [ys' [<- Hys']].
      apply in_map_iff in Hzs as [zs' [<- Hzs']]. f_equal.
      eapply IH; eauto. intro q. destruct (eq_dec q x) as [->|Hneq].
      * assert (Hny : ~ In x ys').
        { intro Hin. apply Hnot.
          exact (@subsets_members_source X xs ys' Hys' x Hin). }
        assert (Hnz : ~ In x zs').
        { intro Hin. apply Hnot.
          exact (@subsets_members_source X xs zs' Hzs' x Hin). }
        tauto.
      * split; intro Hq.
        -- pose proof (proj1 (Heq q) (or_intror Hq)) as H.
           destruct H as [H|H]; [now symmetry in H|exact H].
        -- pose proof (proj2 (Heq q) (or_intror Hq)) as H.
           destruct H as [H|H]; [now symmetry in H|exact H].
Qed.

Lemma list_membership_difference {X : Type}
    (eq_dec : forall x y : X, {x = y} + {x <> y}) (xs ys : list X) :
  (forall q, In q xs <-> In q ys) \/
  exists q, (In q xs /\ ~ In q ys) \/ (~ In q xs /\ In q ys).
Proof.
  assert (scan : forall us vs : list X,
      incl us vs \/ exists q, In q us /\ ~ In q vs).
  { intros us vs. induction us as [|u us IH].
    - now left.
    - destruct (in_dec eq_dec u vs) as [Hu|Hu].
      + destruct IH as [HI|[q [Hq Hnq]]].
        * left. intros q [<-|Hq]; [exact Hu|now apply HI].
        * right. exists q. split; [now right|exact Hnq].
      + right. exists u. split; [now left|exact Hu]. }
  destruct (scan xs ys) as [Hxy|[q [Hqx Hnqy]]].
  - destruct (scan ys xs) as [Hyx|[q [Hqy Hnqx]]].
    + left. intro q. split; auto.
    + right. exists q. now right.
  - right. exists q. now left.
Qed.

Lemma nodup_map_cons {X : Type} (x : X) (xss : list (list X)) :
  NoDup xss -> NoDup (map (cons x) xss).
Proof.
  intro Hnd. induction Hnd as [|ys yss Hnot Hnd IH]; simpl.
  - constructor.
  - constructor; [|exact IH]. intro Hin.
    apply in_map_iff in Hin as [zs [Heq Hzs]].
    injection Heq as Heq. subst zs. contradiction.
Qed.

Lemma combinations_nodup {X : Type} k (xs : list X) :
  NoDup xs -> NoDup (combinations k xs).
Proof.
  revert k. induction xs as [|x xs IH]; intros [|k] Hnd; simpl.
  - repeat constructor; simpl; tauto.
  - constructor.
  - repeat constructor; simpl; tauto.
  - inversion Hnd as [|? ? Hnot Htail]; subst. apply NoDup_app.
    + now apply IH.
    + apply nodup_map_cons. now apply IH.
    + intros ys Hys Hin. apply in_map_iff in Hin as [zs [<- Hzs]].
      apply Hnot. eapply (@combinations_members_source X (S k) xs
        (x :: zs) Hys x).
      now left.
Qed.

Lemma subsets_nodup {X : Type} (xs : list X) :
  NoDup xs -> NoDup (subsets xs).
Proof.
  induction xs as [|x xs IH]; intro Hnd; simpl.
  - repeat constructor; simpl; tauto.
  - inversion Hnd as [|? ? Hnot Htail]; subst. apply NoDup_app.
    + now apply IH.
    + apply nodup_map_cons. now apply IH.
    + intros ys Hys Hin. apply in_map_iff in Hin as [zs [<- Hzs]].
      apply Hnot. eapply (@subsets_members_source X xs (x :: zs) Hys x).
      now left.
Qed.

Lemma middle_subsets_nodup k : NoDup (middle_subsets k).
Proof.
  unfold middle_subsets. apply combinations_nodup, seq_NoDup.
Qed.

Lemma valid_middle_set_nodup k S :
  valid_middle_set k S -> NoDup S.
Proof.
  unfold valid_middle_set, middle_subsets. intro HS.
  eapply combinations_member_nodup; [apply seq_NoDup|exact HS].
Qed.

Lemma lower_bound_family_valid k F :
  In F (lower_bound_families k) -> valid_middle_family k F.
Proof.
  unfold lower_bound_families, valid_middle_family, valid_middle_set.
  intros HF S HS. eapply subsets_members_source; eauto.
Qed.

Lemma valid_middle_inclusion_equal k S T :
  valid_middle_set k S -> valid_middle_set k T -> incl S T -> S = T.
Proof.
  intros HS HT HST.
  apply (@combinations_extensional_unique nat Nat.eq_dec (k / 2)
    (seq 0 k) S T).
  - apply seq_NoDup.
  - exact HS.
  - exact HT.
  - intro i. split; [now apply HST|].
    apply (NoDup_length_incl (@valid_middle_set_nodup k S HS)).
    + rewrite (@valid_middle_set_length k S HS),
        (@valid_middle_set_length k T HT). lia.
    + exact HST.
Qed.

Lemma distinct_lower_bound_families_differ k F G :
  In F (lower_bound_families k) -> In G (lower_bound_families k) ->
  F <> G ->
  exists S, (In S F /\ ~ In S G) \/ (~ In S F /\ In S G).
Proof.
  intros HF HG Hneq.
  destruct (list_membership_difference (list_eq_dec Nat.eq_dec) F G)
    as [Heq|Hdiff]; [|exact Hdiff]. exfalso. apply Hneq.
  unfold lower_bound_families in HF, HG.
  exact (@subsets_extensional_unique (list nat) (list_eq_dec Nat.eq_dec)
    (middle_subsets k) F G (middle_subsets_nodup k) HF HG Heq).
Qed.

Lemma lower_bound_families_nodup k : NoDup (lower_bound_families k).
Proof.
  unfold lower_bound_families. apply subsets_nodup, middle_subsets_nodup.
Qed.

Definition lower_prefixes k : list (list lower_symbol) :=
  map (lower_family_prefix k) (lower_bound_families k).

Lemma lower_families_language_separated k F G :
  In F (lower_bound_families k) -> In G (lower_bound_families k) ->
  F <> G ->
  language_separated
    (rewpla_language lower_symbol_eqb (lower_expression k))
    (lower_family_prefix k F) (lower_family_prefix k G).
Proof.
  intros HF HG Hneq.
  pose proof (@lower_bound_family_valid k F HF) as HFvalid.
  pose proof (@lower_bound_family_valid k G HG) as HGvalid.
  destruct (@distinct_lower_bound_families_differ k F G HF HG Hneq)
    as [S [[HSF HnSG]|[HnSF HSG]]].
  - assert (HS : valid_middle_set k S) by now apply HFvalid.
    exists (lower_test S). left. split.
    + apply (proj2 (@lower_bound_membership k F S HFvalid HS)).
      exists S. split; [exact HSF|apply incl_refl].
    + intro Haccept.
      apply (proj1 (@lower_bound_membership k G S HGvalid HS)) in Haccept.
      destruct Haccept as [U [HUG HUS]]. apply HnSG.
      pose proof (HGvalid U HUG) as HU.
      assert (U = S) by now apply (@valid_middle_inclusion_equal k U S HU HS HUS).
      now subst U.
  - assert (HS : valid_middle_set k S) by now apply HGvalid.
    exists (lower_test S). right. split.
    + intro Haccept.
      apply (proj1 (@lower_bound_membership k F S HFvalid HS)) in Haccept.
      destruct Haccept as [U [HUF HUS]]. apply HnSF.
      pose proof (HFvalid U HUF) as HU.
      assert (U = S) by now apply (@valid_middle_inclusion_equal k U S HU HS HUS).
      now subst U.
    + apply (proj2 (@lower_bound_membership k G S HGvalid HS)).
      exists S. split; [exact HSG|apply incl_refl].
Qed.

Lemma lower_prefixes_separated_aux k fs :
  incl fs (lower_bound_families k) -> NoDup fs ->
  prefixes_separated
    (rewpla_language lower_symbol_eqb (lower_expression k))
    (map (lower_family_prefix k) fs).
Proof.
  intros Hin Hnd. induction fs as [|F fs IH]; simpl; [exact I|].
  inversion Hnd as [|? ? Hnot Htail]; subst. split.
  - intros v Hv. apply in_map_iff in Hv as [G [<- HG]].
    apply lower_families_language_separated.
    + apply Hin. now left.
    + apply Hin. now right.
    + intro Heq. subst G. contradiction.
  - apply IH.
    + intros G HG. apply Hin. now right.
    + exact Htail.
Qed.

Theorem lower_prefixes_separated k :
  prefixes_separated
    (rewpla_language lower_symbol_eqb (lower_expression k))
    (lower_prefixes k).
Proof.
  unfold lower_prefixes. apply lower_prefixes_separated_aux.
  - apply incl_refl.
  - apply lower_bound_families_nodup.
Qed.

(** Paper Section 4.3 lower bound, in the artifact's derivative semantics.
    The result is exact (not merely asymptotic): the expression has at least
    [2 ^ binomial k (k/2)] pairwise different reachable residuals, under both
    projected-word and complete pair-language equivalence. *)
Theorem lower_expression_derivative_lower_bound k :
  exists derivatives : list (rewpla lower_symbol),
    length derivatives = 2 ^ binomial k (k / 2) /\
    projected_distinct lower_symbol_eqb derivatives /\
    semantic_distinct lower_symbol_eqb derivatives /\
    semantic_reachable lower_symbol_eqb (lower_expression k) derivatives.
Proof.
  destruct (@separated_prefixes_derivative_count lower_symbol
      lower_symbol_eqb lower_symbol_eqb_spec (lower_expression k)
      (lower_prefixes k) (lower_prefixes_separated k))
    as [ds [Hlen [Hprojected [Hsemantic Hreachable]]]].
  exists ds. repeat split; try assumption.
  rewrite Hlen. unfold lower_prefixes. rewrite length_map.
  apply lower_bound_families_length.
Qed.

(** The other half of the paper theorem: every finite deterministic machine
    recognizing the projected language has at least the same many states.
    Instantiating [states] with the state set of a minimal DFA yields the
    stated minimal-DFA lower bound. *)
Theorem lower_expression_finite_dfa_lower_bound k (Q : Type)
    (step : Q -> lower_symbol -> Q) initial final states :
  deterministic_recognizes step initial final
    (rewpla_language lower_symbol_eqb (lower_expression k)) ->
  (forall w, In (deterministic_run step initial w) states) ->
  2 ^ binomial k (k / 2) <= length states.
Proof.
  intros Hrecognizes Hstates.
  pose proof (@separated_prefixes_finite_dfa_lower_bound lower_symbol Q
    step initial final
    (rewpla_language lower_symbol_eqb (lower_expression k))
    (lower_prefixes k) states Hrecognizes Hstates
    (lower_prefixes_separated k)) as Hbound.
  unfold lower_prefixes in Hbound. rewrite length_map,
    lower_bound_families_length in Hbound. exact Hbound.
Qed.

Lemma regex_sum_width {A : Type} (xs : list A) :
  alphabetic_width (regex_sum xs) = length xs.
Proof. induction xs as [|x xs IH]; simpl; lia. Qed.

Lemma embed_regex_width {A : Type} (r : regex A) :
  rewpla_width (embed_regex r) = alphabetic_width r.
Proof. induction r; simpl; lia. Qed.

Lemma core_atoms_length k : length (core_atoms k) = k + 3.
Proof.
  unfold core_atoms. rewrite length_app, length_map, length_seq. simpl. lia.
Qed.

Lemma core_regex_width k : alphabetic_width (core_regex k) = k + 3.
Proof. unfold core_regex. rewrite regex_sum_width. apply core_atoms_length. Qed.

Lemma lower_assertion_width k i : rewpla_width (lower_assertion k i) = k + 4.
Proof.
  unfold lower_assertion. simpl rewpla_width. rewrite embed_regex_width.
  change (alphabetic_width (core_regex k) + 1 = k + 4).
  rewrite core_regex_width.
  lia.
Qed.

Lemma lower_choice_width k i : rewpla_width (lower_choice k i) = k + 6.
Proof.
  unfold lower_choice.
  change (1 + (1 + rewpla_width (lower_assertion k i)) = k + 6).
  rewrite lower_assertion_width. lia.
Qed.

Lemma lower_choices_width k is :
  rewpla_width (lower_choices k is) = length is * (k + 6).
Proof.
  induction is as [|i is IH]; [reflexivity|].
  change (rewpla_width (lower_choice k i) +
    rewpla_width (lower_choices k is) = S (length is) * (k + 6)).
  rewrite lower_choice_width, IH. lia.
Qed.

Lemma lower_suffix_regex_width k :
  alphabetic_width (lower_suffix_regex k) = k + 4.
Proof.
  unfold lower_suffix_regex.
  change (alphabetic_width (core_regex k) + 1 = k + 4).
  rewrite core_regex_width. lia.
Qed.

(** The displayed constraint family from the end of Section 4.3:
    [LA(epsilon)] together with one [LA(V_k^* x_i)] for every index. *)
Definition lower_constraint_basis k : list (rewpla lower_symbol) :=
  WLookahead WEps :: map (lower_assertion k) (seq 0 k).

Lemma lower_assertion_injective k i j :
  lower_assertion k i = lower_assertion k j -> i = j.
Proof. unfold lower_assertion. now injection 1. Qed.

Lemma lower_assertions_nodup k is :
  NoDup is -> NoDup (map (lower_assertion k) is).
Proof.
  intro Hnd. induction Hnd as [|i is Hnot Hnd IH]; simpl.
  - constructor.
  - constructor; [|exact IH]. intro Hin.
    apply in_map_iff in Hin as [j [Heq Hj]].
    apply lower_assertion_injective in Heq. subst j. contradiction.
Qed.

Theorem lower_constraint_basis_nodup k : NoDup (lower_constraint_basis k).
Proof.
  unfold lower_constraint_basis. constructor.
  - intro Hin. apply in_map_iff in Hin as [i [Heq _]].
    unfold lower_assertion in Heq. discriminate.
  - apply lower_assertions_nodup, seq_NoDup.
Qed.

Theorem lower_constraint_basis_length k :
  length (lower_constraint_basis k) = k + 1.
Proof.
  unfold lower_constraint_basis. simpl. rewrite length_map, length_seq. lia.
Qed.

(** The exact alphabetic width claimed for the Section 4.3 witness family. *)
Theorem lower_expression_width k :
  rewpla_width (lower_expression k) = k * k + 8 * k + 8.
Proof.
  unfold lower_expression.
  change
    (rewpla_width (embed_regex (Star (core_regex k))) +
      (1 + (rewpla_width (lower_choices k (seq 0 k)) +
        rewpla_width (embed_regex (lower_suffix_regex k)))) =
     k * k + 8 * k + 8).
  rewrite !embed_regex_width.
  change
    (alphabetic_width (core_regex k) +
      (1 + (rewpla_width (lower_choices k (seq 0 k)) +
        alphabetic_width (lower_suffix_regex k))) =
     k * k + 8 * k + 8).
  rewrite core_regex_width, lower_choices_width, length_seq,
    lower_suffix_regex_width. nia.
Qed.

Print Assumptions lower_assertion_satisfies.
Print Assumptions lower_choice_satisfies.
Print Assumptions lower_choices_selected_satisfies.
Print Assumptions lower_family_block_parser.
Print Assumptions lower_expression_suffix_characterization.
Print Assumptions lower_expression_projected_exact.
Print Assumptions lower_bound_membership.
Print Assumptions lower_expression_derivative_lower_bound.
Print Assumptions lower_expression_finite_dfa_lower_bound.
Print Assumptions lower_expression_width.
Print Assumptions lower_constraint_basis_length.
