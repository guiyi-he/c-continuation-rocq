From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import Syntax Automaton.
Import ListNotations.

Set Implicit Arguments.

Section Construction.
Context {A : Type} (eqb : A -> A -> bool).
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Definition pos_eqb (p q : position A) : bool :=
  Nat.eqb (fst p) (fst q) && eqb (snd p) (snd q).

Lemma pos_eqb_spec p q : pos_eqb p q = true <-> p = q.
Proof.
  destruct p as [n a], q as [m b]; unfold pos_eqb; simpl.
  rewrite andb_true_iff, Nat.eqb_eq, eqb_spec. split.
  - intros [-> ->]. reflexivity.
  - intro H. inversion H; subst. auto.
Qed.

Fixpoint positions (r : regex (position A)) : list (position A) :=
  match r with
  | Zero | Eps => []
  | Atom p => [p]
  | Plus r s | Concat r s => positions r ++ positions s
  | Star r => positions r
  end.

Lemma positions_regex_atoms r : positions r = regex_atoms r.
Proof. induction r; simpl; congruence. Qed.

Fixpoint first (r : regex (position A)) : list (position A) :=
  match r with
  | Zero | Eps => []
  | Atom p => [p]
  | Plus r s => first r ++ first s
  | Concat r s => if nullable r then first r ++ first s else first r
  | Star r => first r
  end.

Fixpoint cderive (p : position A) (r : regex (position A)) : regex (position A) :=
  match r with
  | Zero | Eps => Zero
  | Atom q => if pos_eqb p q then Eps else Zero
  | Plus r s => let d := cderive p r in if is_zero d then cderive p s else d
  | Concat r s => let d := cderive p r in
      if is_zero d then if nullable r then cderive p s else Zero
      else smart_concat d s
  | Star r => smart_concat (cderive p r) (Star r)
  end.

(** Antimirov-style derivatives over the marked alphabet.  They are used only
    in the proof: [cderive] is the canonical representative selected from this
    list on linearized expressions and their continuations. *)
Fixpoint pderive (p : position A) (r : regex (position A))
  : list (regex (position A)) :=
  match r with
  | Zero | Eps => []
  | Atom q => if pos_eqb p q then [Eps] else []
  | Plus r s => pderive p r ++ pderive p s
  | Concat r s =>
      map (fun d => smart_concat d s) (pderive p r) ++
      if nullable r then pderive p s else []
  | Star r => map (fun d => smart_concat d (Star r)) (pderive p r)
  end.

Lemma in_map_smart_concat p r s d :
  In d (map (fun x => smart_concat x s) (pderive p r)) <->
  exists x, In x (pderive p r) /\ d = smart_concat x s.
Proof. rewrite in_map_iff. split; intros [x [E H]]; exists x; auto. Qed.

Lemma pderive_sound p r d w :
  In d (pderive p r) -> matches d w -> matches r (p :: w).
Proof.
  revert d w; induction r as [| |q|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r IH];
    intros d w Hd Hm; simpl in Hd.
  - contradiction.
  - contradiction.
  - destruct (pos_eqb p q) eqn:E; simpl in Hd; [|contradiction].
    destruct Hd as [Hd|[]]. subst d. apply pos_eqb_spec in E. subst q.
    inversion Hm; subst. constructor.
  - apply in_app_iff in Hd. destruct Hd as [Hd|Hd].
    + apply M_PlusL. eapply IH1; eauto.
    + apply M_PlusR. eapply IH2; eauto.
  - apply in_app_iff in Hd. destruct Hd as [Hd|Hd].
    + apply in_map_iff in Hd. destruct Hd as [x [Ex Hx]]. subst d.
      apply smart_concat_correct in Hm. inversion Hm; subst.
      replace (p :: u ++ v) with ((p :: u) ++ v) by reflexivity.
      apply M_Concat; [eapply IH1; eauto|assumption].
    + destruct (nullable r1) eqn:En; simpl in Hd; [|contradiction].
      replace (p :: w) with ([] ++ p :: w) by reflexivity.
      apply M_Concat.
      * apply nullable_correct. exact En.
      * eapply IH2; eauto.
  - apply in_map_iff in Hd. destruct Hd as [x [Ex Hx]]. subst d.
    apply smart_concat_correct in Hm. inversion Hm; subst.
    replace (p :: u ++ v) with ((p :: u) ++ v) by reflexivity.
    apply M_StarApp.
    + discriminate.
    + eapply IH; eauto.
    + assumption.
Qed.

Lemma pderive_complete p r w :
  matches r (p :: w) -> exists d, In d (pderive p r) /\ matches d w.
Proof.
  intro Hm. remember (p :: w) as z eqn:Ez. revert p w Ez.
  induction Hm; intros p0 w0 Ez; try discriminate.
  - inversion Ez; subst. exists Eps. simpl.
    rewrite (proj2 (pos_eqb_spec p0 p0) eq_refl). split; [now left|apply M_Eps].
  - destruct (IHHm p0 w0 Ez) as [d [Hd Hdw]]. exists d. simpl.
    split; [apply in_app_iff; left; exact Hd|exact Hdw].
  - destruct (IHHm p0 w0 Ez) as [d [Hd Hdw]]. exists d. simpl.
    split; [apply in_app_iff; right; exact Hd|exact Hdw].
  - destruct u as [|x u].
    + simpl in Ez. subst v.
      destruct (IHHm2 p0 w0 eq_refl) as [d [Hd Hdw]]. exists d. simpl.
      apply nullable_correct in Hm1. rewrite Hm1, in_app_iff.
      split; [right; exact Hd|exact Hdw].
    + simpl in Ez. inversion Ez; subst x.
      destruct (IHHm1 p0 u eq_refl) as [d [Hd Hdu]].
      exists (smart_concat d s). simpl. split.
      * apply in_app_iff. left. apply in_map_iff. exists d. split; [reflexivity|exact Hd].
      * apply smart_concat_correct.
        apply M_Concat; assumption.
  - destruct u as [|x u].
    + contradiction H. reflexivity.
    + simpl in Ez. inversion Ez; subst x.
      destruct (IHHm1 p0 u eq_refl) as [d [Hd Hdu]].
      exists (smart_concat d (Star r)). simpl. split.
      * apply in_map_iff. exists d. split; [reflexivity|exact Hd].
      * apply smart_concat_correct.
        apply M_Concat; assumption.
Qed.

Theorem pderive_correct p r w :
  matches r (p :: w) <-> exists d, In d (pderive p r) /\ matches d w.
Proof. split; [apply pderive_complete|intros [d [Hd Hm]]; eapply pderive_sound; eauto]. Qed.

Fixpoint ccontinuation (p : position A) (r : regex (position A)) : regex (position A) :=
  match r with
  | Zero | Eps => Zero
  | Atom q => if pos_eqb p q then Eps else Zero
  | Plus r s => let c := ccontinuation p r in
      if is_zero c then ccontinuation p s else c
  | Concat r s => let c := ccontinuation p r in
      if is_zero c then ccontinuation p s else smart_concat c s
  | Star r => smart_concat (ccontinuation p r) (Star r)
  end.

Definition nth_position (ps : list (position A)) (q : nat) : option (position A) :=
  match q with 0 => None | S n => nth_error ps n end.

Definition continuation_at (lr : regex (position A)) (ps : list (position A)) (q : nat) :=
  match nth_position ps q with None => lr | Some p => ccontinuation p lr end.

Definition label_at (ps : list (position A)) (q : nat) : option A :=
  match nth_position ps q with None => None | Some p => Some (snd p) end.

Fixpoint targets (ps : list (position A)) (lr source : regex (position A))
  (a : A) : list nat :=
  match ps with
  | [] => []
  | p :: ps =>
      if eqb (snd p) a &&
         regex_eqb pos_eqb (cderive p source) (ccontinuation p lr)
      then fst p :: targets ps lr source a
      else targets ps lr source a
  end.

Lemma targets_spec ps lr source a q :
  In q (targets ps lr source a) <->
  exists p, In p ps /\ fst p = q /\ snd p = a /\
    cderive p source = ccontinuation p lr.
Proof.
  induction ps as [|p ps IH].
  - cbn [targets]. split; [contradiction|intros [x [H]]; contradiction].
  - cbn [targets].
    destruct (eqb (snd p) a &&
      regex_eqb pos_eqb (cderive p source) (ccontinuation p lr)) eqn:E; cbn.
    + rewrite andb_true_iff in E. destruct E as [Ea Ed].
      apply eqb_spec in Ea. apply (regex_eqb_spec pos_eqb pos_eqb_spec) in Ed.
      rewrite IH. split.
      * intros [Hq|H].
        -- exists p. repeat split; auto.
        -- destruct H as [x [Hx Hrest]]. exists x. auto.
      * intros [x [[Hx0|Hx] [Hq [Ha Hd]]]].
        -- subst x. left. exact Hq.
        -- right. exists x. auto.
    + rewrite IH. split.
      * intros [x [Hx Hrest]]. exists x. auto.
      * intros [x [[Hx|Hx] [Hq [Ha Hd]]]].
        -- subst x. exfalso. apply Bool.andb_false_iff in E.
           destruct E as [E|E].
           ++ apply eqb_spec in Ha. congruence.
           ++ rewrite (proj2 (regex_eqb_spec pos_eqb pos_eqb_spec _ _) Hd) in E. discriminate.
        -- exists x. auto.
Qed.

Definition build_ce (r : regex A) : built_automaton A (regex (position A)) :=
  let lr := linearize r in
  let ps := positions lr in
  let n := alphabetic_width r in
  let cont q := continuation_at lr ps q in
  let M := {| state_count := S n;
              initial := 0;
              finalb := fun q => nullable (cont q);
              trans := fun q a => targets ps lr (cont q) a |} in
  {| machine := M;
     infos := map (fun q =>
       {| info_id := q; info_position := nth_position ps q;
          info_members := [q]; info_continuation := cont q;
          info_final := nullable (cont q) |}) (seq 0 (S n)) |}.

Definition build_position (r : regex A) : built_automaton A (regex (position A)) :=
  build_ce r.

Definition erased_cont (lr : regex (position A)) (ps : list (position A)) q : regex A :=
  erase (continuation_at lr ps q).

Fixpoint find_class (x : regex A) (classes : list (list nat))
  (lr : regex (position A)) (ps : list (position A)) : option nat :=
  match classes with
  | [] => None
  | c :: cs =>
      match c with
      | [] => find_class x cs lr ps
      | q :: _ => if regex_eqb eqb x (erased_cont lr ps q)
                  then Some 0 else option_map S (find_class x cs lr ps)
      end
  end.

Fixpoint insert_class (q : nat) (classes : list (list nat))
  (lr : regex (position A)) (ps : list (position A)) : list (list nat) :=
  match classes with
  | [] => [[q]]
  | c :: cs =>
      match c with
      | [] => [q] :: cs
      | x :: _ => if regex_eqb eqb (erased_cont lr ps q) (erased_cont lr ps x)
                  then (c ++ [q]) :: cs else c :: insert_class q cs lr ps
      end
  end.

Definition classes_of (r : regex A) : list (list nat) :=
  let lr := linearize r in let ps := positions lr in
  fold_left (fun cs q => insert_class q cs lr ps)
            (seq 0 (S (alphabetic_width r))) [].

Fixpoint class_index (q : nat) (cs : list (list nat)) : nat :=
  match cs with
  | [] => 0
  | c :: cs => if memb q c then 0 else S (class_index q cs)
  end.

Definition representative (c : list nat) : nat := hd 0 c.

Definition quotient_targets (base : automaton A) (cs : list (list nat)) q a : list nat :=
  fold_left (fun acc t => add (class_index t cs) acc) (trans base q a) [].

Definition quotient_targets_class (base : automaton A) (cs : list (list nat))
  (c : list nat) a : list nat :=
  fold_left (fun acc q => union (quotient_targets base cs q a) acc) c [].

Definition build_quotient (r : regex A) : built_automaton A (regex (position A)) :=
  let ce := build_ce r in let base := machine ce in
  let lr := linearize r in let ps := positions lr in let cs := classes_of r in
  let M := {| state_count := length cs;
              initial := class_index 0 cs;
              finalb := fun k => any_final base (nth k cs []);
              trans := fun k a => quotient_targets_class base cs (nth k cs []) a |} in
  {| machine := M;
     infos := mapi (fun k c => let q := representative c in
       {| info_id := k; info_position := nth_position ps q;
          info_members := c; info_continuation := continuation_at lr ps q;
          info_final := finalb base q |}) cs |}.

End Construction.

Arguments build_ce {A} eqb _.
Arguments build_position {A} eqb _.
Arguments build_quotient {A} eqb _.
