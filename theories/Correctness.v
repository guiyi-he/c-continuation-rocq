From Stdlib Require Import List Bool Arith Lia Relation_Definitions.
From CCont Require Import Syntax Automaton Construction Canonical.
Import ListNotations.

Set Implicit Arguments.

Section Facts.
Context {A : Type} (eqb : A -> A -> bool).
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma linearized_positions_nodup (r : regex A) :
  NoDup (positions (linearize r)).
Proof. rewrite positions_regex_atoms. apply linearize_atoms_nodup. Qed.

Lemma linearized_position_ids (r : regex A) :
  map fst (positions (linearize r)) = seq 1 (alphabetic_width r).
Proof.
  rewrite positions_regex_atoms. unfold linearize.
  apply linearize_from_indices.
Qed.

Lemma linearized_position_lookup (r : regex A) p :
  In p (positions (linearize r)) ->
  nth_position (positions (linearize r)) (fst p) = Some p.
Proof.
  intro Hp. apply In_nth_error in Hp. destruct Hp as [i Hi].
  pose proof (@map_nth_error _ _ fst i (positions (linearize r)) p Hi) as Hmap.
  rewrite linearized_position_ids, nth_error_seq in Hmap.
  destruct (i <? alphabetic_width r) eqn:Hlt; [|discriminate].
  inversion Hmap as [Hid]. unfold nth_position. exact Hi.
Qed.

Definition state_source (r : regex A) q (source : regex (position A)) : Prop :=
  (q = 0 /\ source = linearize r) \/
  exists p, nth_position (positions (linearize r)) q = Some p /\
            source = ccontinuation eqb p (linearize r).

Lemma state_source_continuation r q source :
  state_source r q source ->
  continuation_at eqb (linearize r) (positions (linearize r)) q = source.
Proof.
  intros [[-> ->]|[p [Hp ->]]]; [reflexivity|].
  unfold continuation_at. now rewrite Hp.
Qed.

Lemma state_source_canonical r q source :
  state_source r q source -> canonical_pd eqb (linearize r) source.
Proof.
  intros [[-> ->]|[p [Hp ->]]].
  - apply (base_derivatives_canonical eqb eqb_spec). apply linearized_positions_nodup.
  - apply (continuation_derivatives_canonical eqb eqb_spec).
    apply linearized_positions_nodup.
Qed.

Lemma state_source_positions r q source p :
  state_source r q source -> In p (positions source) ->
  In p (positions (linearize r)).
Proof.
  intros [[-> ->]|[x [Hx ->]]] Hp; [exact Hp|].
  eapply positions_ccontinuation; eauto.
Qed.

Lemma ce_transition_source r q source a t :
  state_source r q source -> In t (trans (machine (build_ce eqb r)) q a) ->
  exists p, In p (positions (linearize r)) /\ fst p = t /\ snd p = a /\
    cderive eqb p source = ccontinuation eqb p (linearize r) /\
    state_source r t (ccontinuation eqb p (linearize r)).
Proof.
  intros Hsource Ht. unfold build_ce in Ht; simpl in Ht.
  apply (targets_spec eqb eqb_spec) in Ht.
  destruct Ht as [p [Hp [Hid [Ha Hd]]]]. exists p.
  rewrite (state_source_continuation Hsource) in Hd.
  split; [exact Hp|]. split; [exact Hid|]. split; [exact Ha|]. split; [exact Hd|].
  right. exists p. split; [|reflexivity]. rewrite <- Hid.
  now apply linearized_position_lookup.
Qed.

Definition accepts_from (M : automaton A) q w : Prop :=
  exists t, nfa_run M q w t /\ finalb M t = true.

Theorem ce_accepts_from_correct (r : regex A) :
  forall w q source, state_source r q source ->
  (accepts_from (machine (build_ce eqb r)) q w <->
   exists pw, matches source pw /\ map snd pw = w).
Proof.
  induction w as [|a w IH]; intros q source Hsource.
  - split.
    + intros [t [Hrun Hfin]]. inversion Hrun; subst t.
      exists []. split; [|reflexivity]. apply nullable_correct.
      rewrite <- (state_source_continuation Hsource). exact Hfin.
    + intros [pw [Hm Hmap]]. apply map_eq_nil in Hmap. subst pw.
      exists q. split; [constructor|]. apply nullable_correct in Hm.
      unfold build_ce; simpl. rewrite (state_source_continuation Hsource). exact Hm.
  - split.
    + intros [t [Hrun Hfin]]. inversion Hrun; subst.
      pose proof (ce_transition_source (r:=r) (q:=q) (source:=source)
        a q0 Hsource H2) as Hstep.
      destruct Hstep as [p [Hp [Hid [Ha [Hd Htarget]]]]].
      specialize (IH q0 (ccontinuation eqb p (linearize r)) Htarget).
      assert (accepts_from (machine (build_ce eqb r)) q0 w) as Hacc.
      { exists t. split; [exact H4|exact Hfin]. }
      apply IH in Hacc.
      destruct Hacc as [pw [Hpw Hmap]]. exists (p :: pw). split.
      * pose proof (canonical_one_step eqb_spec (base:=linearize r)
          (source:=source) p pw (state_source_canonical Hsource)) as Hsem.
        apply (proj2 Hsem). split; assumption.
      * simpl. now rewrite Ha, Hmap.
    + intros [pw [Hm Hmap]]. destruct pw as [|p pw]; simpl in Hmap; [discriminate|].
      inversion Hmap; subst.
      pose proof Hm as Hmatch.
      pose proof (state_source_canonical Hsource) as Hcan.
      pose proof (canonical_one_step eqb_spec (base:=linearize r)
        (source:=source) p pw Hcan) as Hsem.
      apply (proj1 Hsem) in Hm.
      destruct Hm as [Hd Hrest].
      assert (In p (positions source)) as Hps.
      { apply (pderive_complete eqb eqb_spec) in Hmatch.
        destruct Hmatch as [d [Hdin _]].
        eapply (pderive_has_position eqb eqb_spec); eauto. }
      pose proof (state_source_positions p Hsource Hps) as Hpbase.
      set (t := fst p).
      assert (In t (trans (machine (build_ce eqb r)) q (snd p))) as Htrans.
      { unfold build_ce; simpl. apply (targets_spec eqb eqb_spec).
        exists p. split; [exact Hpbase|]. split; [reflexivity|].
        split; [reflexivity|]. rewrite (state_source_continuation Hsource). exact Hd. }
      assert (state_source r t (ccontinuation eqb p (linearize r))) as Htarget.
      { right. exists p. split; [|reflexivity]. unfold t.
        now apply linearized_position_lookup. }
      specialize (IH t (ccontinuation eqb p (linearize r)) Htarget).
      assert (accepts_from (machine (build_ce eqb r)) t (map snd pw)) as Hacc.
      { apply (proj2 IH). exists pw. split; [exact Hrest|reflexivity]. }
      destruct Hacc as [u [Hrun Hfin]]. exists u. split; [econstructor; eauto|exact Hfin].
Qed.

Theorem build_ce_correct (r : regex A) w :
  acceptb (machine (build_ce eqb r)) w = true <-> matches r w.
Proof.
  rewrite acceptb_spec. change
    (accepts_from (machine (build_ce eqb r)) 0 w <-> matches r w).
  assert (state_source r 0 (linearize r)) as Hinitial by (left; auto).
  pose proof (ce_accepts_from_correct (r:=r) (q:=0)
    (source:=linearize r) w Hinitial) as Hce.
  rewrite Hce.
  rewrite linearize_language_iff. tauto.
Qed.

Lemma quotient_targets_spec (base : automaton A) cs q a k :
  In k (quotient_targets base cs q a) <->
  exists t, In t (trans base q a) /\ k = class_index t cs.
Proof.
  unfold quotient_targets.
  assert (Hfold : forall xs acc,
    In k (fold_left (fun acc t => add (class_index t cs) acc) xs acc) <->
    In k acc \/ exists t, In t xs /\ k = class_index t cs).
  { induction xs as [|t ts IH]; intro acc; simpl.
    - split.
      + intro H. now left.
      + intros [H|[x [H _]]]; [exact H|contradiction].
    - rewrite IH, add_spec. split.
      + intros [[->|Hacc]|[x [Hx He]]].
        * right. exists t. auto.
        * now left.
        * right. exists x. auto.
      + intros [Hacc|[x [[->|Hx] He]]].
        * left. now right.
        * left. now left.
        * right. exists x. auto. }
  rewrite Hfold. simpl. tauto.
Qed.

Lemma quotient_targets_class_spec (base : automaton A) cs c a k :
  In k (quotient_targets_class base cs c a) <->
  exists q, In q c /\ exists t, In t (trans base q a) /\ k = class_index t cs.
Proof.
  unfold quotient_targets_class.
  assert (Hfold : forall xs acc,
    In k (fold_left (fun acc q => union (quotient_targets base cs q a) acc) xs acc) <->
    In k acc \/ exists q, In q xs /\ In k (quotient_targets base cs q a)).
  { induction xs as [|q qs IH]; intro acc; simpl.
    - split.
      + intro H. now left.
      + intros [H|[x [H _]]]; [exact H|contradiction].
    - rewrite IH, union_spec. split.
      + intros [[Hnew|Hacc]|[x [Hx Hk]]].
        * right. exists q. auto.
        * now left.
        * right. exists x. auto.
      + intros [Hacc|[x [[->|Hx] Hk]]].
        * left. now right.
        * left. now left.
        * right. exists x. auto. }
  rewrite Hfold. simpl. split.
  - intros [Hnil|[q [Hq Hk]]]; [contradiction|]. apply quotient_targets_spec in Hk.
    destruct Hk as [t [Ht He]]. exists q. split; auto. exists t. auto.
  - intros [q [Hq [t [Ht He]]]]. right. exists q. split; auto.
    apply quotient_targets_spec. exists t. auto.
Qed.

Lemma class_index_contains q cs :
  In q (concat cs) -> In q (nth (class_index q cs) cs []).
Proof.
  induction cs as [|c cs IH]; simpl; [contradiction|].
  rewrite in_app_iff. intro H. destruct (memb q c) eqn:E.
  - now apply memb_spec in E.
  - apply IH. destruct H as [H|H]; [apply memb_spec in H; congruence|exact H].
Qed.

Lemma insert_class_covers lr ps q cs x :
  x = q \/ In x (concat cs) ->
  In x (concat (insert_class eqb q cs lr ps)).
Proof.
  induction cs as [|c cs IH]; intros Hx.
  - simpl in *. destruct Hx as [->|H]; [now left|contradiction].
  - destruct c as [|h c].
    + simpl in *. destruct Hx as [Hx|Hx]; [left; symmetry; exact Hx|right; exact Hx].
    + cbn [insert_class]. destruct (regex_eqb eqb
        (erased_cont eqb lr ps q) (erased_cont eqb lr ps h)) eqn:E.
      * simpl. rewrite !in_app_iff. simpl.
        simpl in Hx. rewrite in_app_iff in Hx. intuition congruence.
      * simpl. rewrite in_app_iff.
        destruct Hx as [Heq|Hin].
        -- right. right. apply IH. left. exact Heq.
        -- simpl in Hin. destruct Hin as [Hh|Hin].
           ++ left. exact Hh.
           ++ apply in_app_iff in Hin. destruct Hin as [Hc|Hcs].
              ** right. left. exact Hc.
              ** right. right. apply IH. now right.
Qed.

Lemma fold_insert_covers lr ps xs cs q :
  In q xs \/ In q (concat cs) ->
  In q (concat (fold_left (fun acc x => insert_class eqb x acc lr ps) xs cs)).
Proof.
  revert cs; induction xs as [|x xs IH]; intro cs; simpl.
  - intros [H|H]; [contradiction|exact H].
  - intros [[->|Hxs]|Hcs].
    + apply IH. right. apply insert_class_covers. now left.
    + apply IH. now left.
    + apply IH. right. apply insert_class_covers. now right.
Qed.

Lemma classes_of_covers (r : regex A) q :
  In q (seq 0 (S (alphabetic_width r))) -> In q (concat (classes_of eqb r)).
Proof.
  intro H. unfold classes_of. apply fold_insert_covers. now left.
Qed.

Definition same_key lr ps (c : list nat) : Prop :=
  forall q t, In q c -> In t c -> erased_cont eqb lr ps q = erased_cont eqb lr ps t.

Lemma insert_class_sound lr ps q cs :
  Forall (same_key lr ps) cs -> Forall (same_key lr ps) (insert_class eqb q cs lr ps).
Proof.
  induction cs as [|c cs IH]; intro Hall; simpl.
  - constructor; [intros x y [->|[]] [->|[]]; reflexivity|constructor].
  - inversion Hall as [|? ? Hc Hcs]; subst. destruct c as [|h c].
    + constructor.
      * intros x y [->|[]] [->|[]]; reflexivity.
      * exact Hcs.
    + destruct (regex_eqb eqb (erased_cont eqb lr ps q)
        (erased_cont eqb lr ps h)) eqn:E.
      * constructor; [|exact Hcs]. intros x y Hx Hy.
        apply in_app_iff in Hx, Hy. simpl in Hx, Hy.
        apply (regex_eqb_spec eqb eqb_spec) in E.
        destruct Hx as [Hx|[->|[]]], Hy as [Hy|[->|[]]].
        -- eapply Hc; eauto.
        -- transitivity (erased_cont eqb lr ps h); [eapply Hc; eauto; now left|symmetry; exact E].
        -- transitivity (erased_cont eqb lr ps h); [exact E|eapply Hc; eauto; now left].
        -- reflexivity.
      * constructor; [exact Hc|]. apply IH. exact Hcs.
Qed.

Lemma classes_of_sound (r : regex A) :
  Forall (same_key (linearize r) (positions (linearize r))) (classes_of eqb r).
Proof.
  unfold classes_of.
  assert (Hfold : forall xs cs,
    Forall (same_key (linearize r) (positions (linearize r))) cs ->
    Forall (same_key (linearize r) (positions (linearize r)))
      (fold_left (fun acc q => insert_class eqb q acc (linearize r)
        (positions (linearize r))) xs cs)).
  { induction xs as [|q qs IH]; intros cs Hcs; simpl; [exact Hcs|].
    apply IH. now apply insert_class_sound. }
  apply Hfold. constructor.
Qed.

Lemma nth_class_sound (r : regex A) k :
  same_key (linearize r) (positions (linearize r))
    (nth k (classes_of eqb r) []).
Proof.
  pose proof (classes_of_sound r) as H.
  destruct (lt_dec k (length (classes_of eqb r))).
  - apply (proj1 (Forall_forall _ _) H). apply nth_In. exact l.
  - rewrite nth_overflow by lia. intros q t Hq. contradiction.
Qed.

Lemma linearized_positions_length (r : regex A) :
  length (positions (linearize r)) = alphabetic_width r.
Proof.
  pose proof (f_equal (@length nat) (linearized_position_ids r)) as H.
  now rewrite length_map, length_seq in H.
Qed.

Lemma state_source_of_bound (r : regex A) q :
  In q (seq 0 (S (alphabetic_width r))) ->
  exists source, state_source r q source.
Proof.
  rewrite in_seq. intros [_ Hq]. destruct q as [|i].
  - exists (linearize r). now left.
  - assert (i < length (positions (linearize r))) by (rewrite linearized_positions_length; lia).
    apply nth_error_Some in H. destruct (nth_error (positions (linearize r)) i) as [p|] eqn:E;
      [|contradiction].
    exists (ccontinuation eqb p (linearize r)). right. exists p. auto.
Qed.

Lemma insert_class_subset lr ps q cs x :
  In x (concat (insert_class eqb q cs lr ps)) -> x = q \/ In x (concat cs).
Proof.
  induction cs as [|c cs IH]; simpl; intro H.
  - simpl in H. intuition congruence.
  - destruct c as [|h c].
    + simpl in H. destruct H as [->|H]; auto.
    + cbn [insert_class] in H. destruct (regex_eqb eqb
        (erased_cont eqb lr ps q) (erased_cont eqb lr ps h)); simpl in H.
      * destruct H as [Hh|H].
        -- right. simpl. now left.
        -- apply in_app_iff in H. destruct H as [Hcq|Hcs].
           ++ apply in_app_iff in Hcq. destruct Hcq as [Hc|[->|[]]].
              ** right. simpl. right. apply in_app_iff. now left.
              ** now left.
           ++ right. simpl. right. apply in_app_iff. now right.
      * destruct H as [Hh|H].
        -- right. simpl. now left.
        -- apply in_app_iff in H. destruct H as [Hc|Hins].
           ++ right. simpl. right. apply in_app_iff. now left.
           ++ apply IH in Hins. destruct Hins as [->|Hcs]; [now left|].
              right. simpl. right. apply in_app_iff. now right.
Qed.

Lemma fold_insert_subset lr ps xs cs q :
  In q (concat (fold_left (fun acc x => insert_class eqb x acc lr ps) xs cs)) ->
  In q xs \/ In q (concat cs).
Proof.
  revert cs; induction xs as [|x xs IH]; intro cs; simpl; intro H.
  - now right.
  - apply IH in H. destruct H as [H|H]; [now left; right|].
    apply insert_class_subset in H. destruct H as [->|H]; [now left; left|now right].
Qed.

Lemma classes_of_subset (r : regex A) q :
  In q (concat (classes_of eqb r)) -> In q (seq 0 (S (alphabetic_width r))).
Proof.
  unfold classes_of. intro H. apply fold_insert_subset in H.
  destruct H as [H|H]; [exact H|contradiction].
Qed.

Lemma class_member_state_source (r : regex A) k q :
  In q (nth k (classes_of eqb r) []) -> exists source, state_source r q source.
Proof.
  intro Hq. apply state_source_of_bound. apply classes_of_subset.
  apply in_concat. exists (nth k (classes_of eqb r) []). split; auto.
  apply nth_In. destruct (nth_error (classes_of eqb r) k) eqn:E; [|].
  - apply nth_error_Some. congruence.
  - exfalso. apply nth_error_None in E. rewrite nth_overflow in Hq by exact E. contradiction.
Qed.

Lemma state_source_in_bound (r : regex A) q source :
  state_source r q source -> In q (seq 0 (S (alphabetic_width r))).
Proof.
  intros [[-> _]|[p [Hp _]]].
  - rewrite in_seq. lia.
  - unfold nth_position in Hp. destruct q as [|i]; [discriminate|].
    pose proof Hp as Hnth.
    apply nth_error_In in Hp.
    pose proof (@map_nth_error _ _ fst i (positions (linearize r)) p Hnth) as Hmap.
    rewrite linearized_position_ids, nth_error_seq in Hmap.
    destruct (i <? alphabetic_width r) eqn:E; [|discriminate].
    apply Nat.ltb_lt in E. rewrite in_seq. lia.
Qed.

Definition quotient_state_source (r : regex A) k (source : regex A) : Prop :=
  exists q marked,
    In q (nth k (classes_of eqb r) []) /\ state_source r q marked /\
    source = erase marked.

Lemma class_source_for_member (r : regex A) k q marked :
  In q (nth k (classes_of eqb r) []) -> state_source r q marked ->
  quotient_state_source r k (erase marked).
Proof. intros Hq Hs. exists q, marked. auto. Qed.

Lemma class_source_member_key (r : regex A) k source q marked :
  quotient_state_source r k source ->
  In q (nth k (classes_of eqb r) []) -> state_source r q marked ->
  source = erase marked.
Proof.
  intros [x [mx [Hx [Hmx ->]]]] Hq Hmarked.
  pose proof (nth_class_sound r k x q Hx Hq) as Hkey.
  unfold erased_cont in Hkey.
  rewrite (state_source_continuation Hmx), (state_source_continuation Hmarked) in Hkey.
  exact Hkey.
Qed.

Lemma quotient_transition_exact (r : regex A) k a j :
  In j (trans (machine (build_quotient eqb r)) k a) <->
  exists q t,
    In q (nth k (classes_of eqb r) []) /\
    In t (trans (machine (build_ce eqb r)) q a) /\
    j = class_index t (classes_of eqb r).
Proof.
  unfold build_quotient; simpl. rewrite quotient_targets_class_spec. split.
  - intros [q [Hq [t [Ht He]]]]. exists q, t. auto.
  - intros [q [t [Hq [Ht He]]]]. exists q. split; auto. exists t. auto.
Qed.

Lemma quotient_final_exact (r : regex A) k :
  finalb (machine (build_quotient eqb r)) k = true <->
  exists q, In q (nth k (classes_of eqb r) []) /\
    finalb (machine (build_ce eqb r)) q = true.
Proof. unfold build_quotient; simpl. apply any_final_spec. Qed.

Theorem quotient_accepts_from_correct (r : regex A) :
  forall w k source, quotient_state_source r k source ->
  (accepts_from (machine (build_quotient eqb r)) k w <-> matches source w).
Proof.
  induction w as [|a w IH]; intros k source Hsource.
  - split.
    + intros [t [Hrun Hfin]]. inversion Hrun; subst t.
      apply quotient_final_exact in Hfin. destruct Hfin as [qx [Hq Hqfin]].
      destruct (class_member_state_source r k qx Hq) as [marked Hmarked].
      pose proof (class_source_member_key Hsource Hq Hmarked) as Hkey.
      rewrite Hkey.
      assert (matches marked []) as Hempty.
      { apply nullable_correct. unfold build_ce in Hqfin; simpl in Hqfin.
        now rewrite (state_source_continuation Hmarked) in Hqfin. }
      apply erase_matches in Hempty. exact Hempty.
    + intro Hm. exists k. split; [constructor|]. apply quotient_final_exact.
      destruct Hsource as [q [marked [Hq [Hmarked Hkey]]]]. exists q. split; auto.
      unfold build_ce; simpl. rewrite (state_source_continuation Hmarked).
      rewrite <- nullable_erase. apply nullable_correct. now rewrite <- Hkey.
  - split.
    + intros [u [Hrun Hfin]].
      inversion Hrun as [|p0 a0 next w0 t0 Htrans Htail]; subst.
      apply quotient_transition_exact in Htrans.
      destruct Htrans as [qx [tx [Hq [Ht Heqclass]]]]. subst next.
      destruct (class_member_state_source r k qx Hq) as [marked Hmarked].
      pose proof (class_source_member_key Hsource Hq Hmarked) as Hkey.
      pose proof (ce_transition_source (r:=r) (q:=qx) (source:=marked)
        a tx Hmarked Ht) as Hstep.
      destruct Hstep as [p [Hp [Hid [Ha [Hd Htarget]]]]].
      assert (In tx (concat (classes_of eqb r))) as Htc.
      { apply classes_of_covers. now apply state_source_in_bound with (source:=ccontinuation eqb p (linearize r)). }
      pose proof (class_index_contains tx (classes_of eqb r) Htc) as Htclass.
      pose proof (class_source_for_member (r:=r)
        (class_index tx (classes_of eqb r)) (q:=tx)
        (marked:=ccontinuation eqb p (linearize r)) Htclass Htarget)
        as Hnextsource.
      specialize (IH (class_index tx (classes_of eqb r))
        (erase (ccontinuation eqb p (linearize r))) Hnextsource).
      assert (accepts_from (machine (build_quotient eqb r))
        (class_index tx (classes_of eqb r)) w) as Hacc.
      { exists u. auto. }
      apply IH in Hacc.
      apply erase_reflects_matches in Hacc. destruct Hacc as [pw [Hpw Hmap]].
      pose proof (canonical_one_step eqb_spec (base:=linearize r)
        (source:=marked) p pw (state_source_canonical Hmarked)) as Hone.
      assert (matches marked (p :: pw)) as Hmarked_word.
      { apply (proj2 Hone). split; assumption. }
      apply erase_matches in Hmarked_word. simpl in Hmarked_word.
      rewrite Hkey. now rewrite Ha, Hmap in Hmarked_word.
    + intro Hm. destruct Hsource as [q [marked [Hq [Hmarked Hkey]]]].
      rewrite Hkey in Hm. apply erase_reflects_matches in Hm.
      destruct Hm as [pw [Hpw Hmap]]. destruct pw as [|p pw]; simpl in Hmap; [discriminate|].
      inversion Hmap; subst.
      pose proof (canonical_one_step eqb_spec (base:=linearize r)
        (source:=marked) p pw (state_source_canonical Hmarked)) as Hone.
      apply (proj1 Hone) in Hpw. destruct Hpw as [Hd Hrest].
      assert (In p (positions marked)) as Hpm.
      { pose proof (proj2 Hone (conj Hd Hrest)) as Hall.
        apply (pderive_complete eqb eqb_spec) in Hall.
        destruct Hall as [d [Hdin _]]. eapply (pderive_has_position eqb eqb_spec); eauto. }
      pose proof (state_source_positions p Hmarked Hpm) as Hpbase.
      set (t := fst p).
      assert (In t (trans (machine (build_ce eqb r)) q (snd p))) as Ht.
      { unfold build_ce; simpl. apply (targets_spec eqb eqb_spec). exists p.
        split; [exact Hpbase|]. split; [reflexivity|]. split; [reflexivity|].
        rewrite (state_source_continuation Hmarked). exact Hd. }
      assert (state_source r t (ccontinuation eqb p (linearize r))) as Htarget.
      { right. exists p. split; [|reflexivity]. unfold t. now apply linearized_position_lookup. }
      assert (In t (concat (classes_of eqb r))) as Htc.
      { apply classes_of_covers. now apply state_source_in_bound with
          (source:=ccontinuation eqb p (linearize r)). }
      pose proof (class_index_contains t (classes_of eqb r) Htc) as Htclass.
      pose proof (class_source_for_member (r:=r)
        (class_index t (classes_of eqb r)) (q:=t)
        (marked:=ccontinuation eqb p (linearize r)) Htclass Htarget)
        as Hnextsource.
      specialize (IH (class_index t (classes_of eqb r))
        (erase (ccontinuation eqb p (linearize r))) Hnextsource).
      apply erase_matches in Hrest. rename Hrest into Herase.
      apply (proj2 IH) in Herase. destruct Herase as [u [Hrun Hfin]].
      exists u. split; [econstructor; [|exact Hrun]|exact Hfin].
      apply quotient_transition_exact. exists q, t. auto.
Qed.

Theorem build_quotient_correct (r : regex A) w :
  acceptb (machine (build_quotient eqb r)) w = true <-> matches r w.
Proof.
  rewrite acceptb_spec. change
    (accepts_from (machine (build_quotient eqb r))
       (class_index 0 (classes_of eqb r)) w <-> matches r w).
  assert (In 0 (seq 0 (S (alphabetic_width r)))) as Hzero.
  { rewrite in_seq. lia. }
  pose proof (classes_of_covers (q:=0) r Hzero) as Hcovered.
  pose proof (class_index_contains 0 (classes_of eqb r) Hcovered) as Hclass.
  assert (state_source r 0 (linearize r)) as Hinitial by (left; auto).
  pose proof (class_source_for_member (r:=r)
    (class_index 0 (classes_of eqb r)) (q:=0) (marked:=linearize r)
    Hclass Hinitial) as Hquotient_initial.
  pose proof (quotient_accepts_from_correct (r:=r) w
    (k:=class_index 0 (classes_of eqb r))
    (source:=erase (linearize r)) Hquotient_initial) as Hcorrect.
  rewrite Hcorrect, erase_linearize. reflexivity.
Qed.

Theorem build_ce_state_count (r : regex A) :
  state_count (machine (build_ce eqb r)) = S (alphabetic_width r).
Proof. reflexivity. Qed.

Theorem build_position_is_ce (r : regex A) :
  build_position eqb r = build_ce eqb r.
Proof. reflexivity. Qed.

Definition ce_equiv (r : regex A) (x y : nat) : Prop :=
  let lr := linearize r in let ps := positions lr in
  erase (continuation_at eqb lr ps x) = erase (continuation_at eqb lr ps y).

Theorem ce_equiv_refl r : forall x, ce_equiv r x x.
Proof. intros x; unfold ce_equiv; reflexivity. Qed.

Theorem ce_equiv_sym r : forall x y, ce_equiv r x y -> ce_equiv r y x.
Proof. intros x y; unfold ce_equiv; now symmetry. Qed.

Theorem ce_equiv_trans r : forall x y z, ce_equiv r x y -> ce_equiv r y z -> ce_equiv r x z.
Proof. intros x y z; unfold ce_equiv; now transitivity (erase (continuation_at eqb (linearize r) (positions (linearize r)) y)). Qed.

Theorem ce_equiv_dec r x y :
  regex_eqb eqb
    (erase (continuation_at eqb (linearize r) (positions (linearize r)) x))
    (erase (continuation_at eqb (linearize r) (positions (linearize r)) y)) = true
  <-> ce_equiv r x y.
Proof. unfold ce_equiv. apply regex_eqb_spec, eqb_spec. Qed.

Theorem ce_initial_zero (r : regex A) :
  initial (machine (build_ce eqb r)) = 0.
Proof. reflexivity. Qed.

Theorem ce_initial_continuation (r : regex A) :
  info_continuation (hd
    {| info_id := 0; info_position := None; info_members := [];
       info_continuation := Zero; info_final := false |}
    (infos (build_ce eqb r))) = linearize r.
Proof.
  unfold build_ce. simpl. reflexivity.
Qed.

Theorem ce_final_exact (r : regex A) q :
  finalb (machine (build_ce eqb r)) q = true <->
  nullable (continuation_at eqb (linearize r) (positions (linearize r)) q) = true.
Proof. reflexivity. Qed.

Theorem ce_transition_exact (r : regex A) q a t :
  In t (trans (machine (build_ce eqb r)) q a) <->
  exists p,
    In p (positions (linearize r)) /\ fst p = t /\ snd p = a /\
    cderive eqb p
      (continuation_at eqb (linearize r) (positions (linearize r)) q) =
    ccontinuation eqb p (linearize r).
Proof.
  unfold build_ce; simpl. apply targets_spec, eqb_spec.
Qed.

Theorem quotient_state_bound (r : regex A) :
  state_count (machine (build_quotient eqb r)) <= S (alphabetic_width r).
Proof.
  unfold build_quotient, classes_of. simpl.
  assert (Hins : forall q cs,
    length (insert_class eqb q cs (linearize r) (positions (linearize r))) <= S (length cs)).
  { intros q cs. induction cs as [|c cs IHc]; simpl; [lia|].
    destruct c as [|x c]; simpl; [lia|].
    destruct (regex_eqb eqb
      (erased_cont eqb (linearize r) (positions (linearize r)) q)
      (erased_cont eqb (linearize r) (positions (linearize r)) x)); simpl; lia. }
  assert (Hfold : forall qs cs,
    length (fold_left
      (fun (cs : list (list nat)) (q : nat) =>
         insert_class eqb q cs (linearize r) (positions (linearize r))) qs cs)
    <= length cs + length qs).
  { induction qs as [|q qs IH]; intros cs; simpl; [lia|].
    specialize (IH (insert_class eqb q cs (linearize r) (positions (linearize r)))).
    specialize (Hins q cs). simpl in *. lia. }
  specialize (Hfold (seq 0 (S (alphabetic_width r))) []).
  rewrite length_seq in Hfold. simpl in Hfold. exact Hfold.
Qed.

End Facts.

Print Assumptions erase_linearize.
Print Assumptions linearize_preserves_language.
Print Assumptions build_ce_state_count.
Print Assumptions ce_equiv_dec.
Print Assumptions ce_transition_exact.
Print Assumptions quotient_state_bound.
Print Assumptions build_ce_correct.
Print Assumptions build_quotient_correct.
