From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import StringConstraints Syntax LookaheadSemantics
  LookaheadDerivatives LookaheadDecision.
Import ListNotations.
Set Implicit Arguments.

(** * Parameterized periodic assertions

    An executable specialization of the paper's full-pair derivative DFA.
    Periods, the common modulus, alphabet and final prefix letter are parameters.
    No state count or expression-specific transition table is assumed. *)
Module PeriodicAutomaton.

Definition parameters_validb modulus periods :=
  negb (Nat.eqb modulus 0) && negb (Nat.eqb (length periods) 0) &&
  forallb (fun p => negb (Nat.eqb p 0) && Nat.eqb (modulus mod p) 0) periods.

Theorem parameters_validb_sound modulus periods :
  parameters_validb modulus periods = true ->
  modulus <> 0 /\ periods <> [] /\
  Forall (fun p => p <> 0 /\ Nat.divide p modulus) periods.
Proof.
  unfold parameters_validb. rewrite !Bool.andb_true_iff, !Bool.negb_true_iff,
    !Nat.eqb_neq. intros [[Hmod Hnon] Hperiods].
  split; [exact Hmod|]. split.
  - intro Hnil. subst. simpl in Hnon. contradiction.
  - apply Forall_forall. intros p Hp.
    apply forallb_forall with (x := p) in Hperiods; [|exact Hp].
    apply Bool.andb_true_iff in Hperiods as [Hpos Hdiv].
    apply Bool.negb_true_iff, Nat.eqb_neq in Hpos.
    split; [exact Hpos|]. apply Nat.mod_divide; [exact Hpos|].
    now apply Nat.eqb_eq.
Qed.

Fixpoint bitvec_eqb (x y : PeriodicFamily.bitvec) :=
  match x,y with
  | [],[] => true
  | a::x',b::y' => Bool.eqb a b && bitvec_eqb x' y'
  | _,_ => false
  end.

Lemma bitvec_eqb_spec x y : bitvec_eqb x y = true <-> x = y.
Proof.
  revert y. induction x as [|a x IH]; intros [|b y]; simpl.
  - tauto.
  - split; discriminate.
  - split; discriminate.
  - rewrite Bool.andb_true_iff, IH.
    destruct a,b; simpl; split; intros H; intuition congruence.
Qed.

Definition states_closedb {A} eqb (trigger : A) base_bits alphabet states :=
  forallb (fun s => forallb (fun a =>
    existsb (bitvec_eqb (PeriodicFamily.step eqb trigger base_bits s a)) states)
    alphabet) states.

Theorem states_closedb_sound {A} eqb (trigger : A) base_bits alphabet states :
  states_closedb eqb trigger base_bits alphabet states = true ->
  forall s a, In s states -> In a alphabet ->
    In (PeriodicFamily.step eqb trigger base_bits s a) states.
Proof.
  unfold states_closedb. intros H s a Hs Ha.
  apply forallb_forall with (x := s) in H; [|exact Hs].
  apply forallb_forall with (x := a) in H; [|exact Ha].
  apply existsb_exists in H as [t [Ht Heq]].
  apply bitvec_eqb_spec in Heq. now rewrite Heq.
Qed.

Section Alphabet.
Context {A : Type}.
Variable eqb : A -> A -> bool.
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.
Variable sigma : regex A.
Hypothesis sigma_one : forall w, matches sigma w <-> length w = 1.
Variable trigger : A.

Fixpoint power (r : regex A) (n : nat) : regex A :=
  match n with
  | 0 => Eps
  | 1 => r
  | S n' => Concat r (power r n')
  end.

Lemma power_length n w : matches (power sigma n) w <-> length w = n.
Proof.
  revert w. induction n as [|n IH]; intro w.
  - simpl. split; [intro H; inversion H; reflexivity|].
    intro H. apply length_zero_iff_nil in H. subst. constructor.
  - destruct n as [|n]; [simpl; apply sigma_one|].
    simpl. split.
    + intro H. inversion H; subst.
      apply sigma_one in H2. apply IH in H4.
      rewrite length_app, H2, H4. lia.
    + intro Hlen. destruct w as [|b w]; [discriminate|].
      change (matches (Concat sigma (power sigma (S n))) ([b] ++ w)).
      constructor.
      * apply sigma_one. reflexivity.
      * apply IH. simpl in Hlen. lia.
Qed.

Lemma power_star n w : n > 0 ->
  (matches (Star (power sigma n)) w <-> exists k, length w = n * k).
Proof.
  intro Hn. split.
  - intro H. remember (Star (power sigma n)) as sr.
    induction H; inversion Heqsr; subst.
    + exists 0. now rewrite Nat.mul_0_r.
    + apply power_length in H0.
      destruct IHmatches2 as [k Hk]; [reflexivity|].
      exists (S k). rewrite length_app, H0, Hk. nia.
  - intros [k Hlen]. revert w Hlen. induction k as [|k IH]; intros w Hlen.
    + rewrite Nat.mul_0_r in Hlen. apply length_zero_iff_nil in Hlen.
      subst w. constructor.
    + assert (Hkn : n <= length w) by nia.
      rewrite <- (firstn_skipn n w) at 1. apply M_StarApp.
      * intro Hnil. apply (f_equal (@length A)) in Hnil.
        rewrite length_firstn, Nat.min_l in Hnil; [simpl in Hnil; lia|exact Hkn].
      * apply power_length. rewrite length_firstn, Nat.min_l by exact Hkn.
        reflexivity.
      * apply IH. rewrite skipn_length. nia.
Qed.

Definition assertion n := WLookahead (embed_regex (Star (power sigma n))).

Lemma assertion_semantics n u v : n > 0 ->
  (rewpla_denote eqb (assertion n) (u, v) <->
    u = [] /\ Nat.eqb (length v mod n) 0 = true).
Proof.
  intro Hn. unfold assertion. split.
  - intros [p [Hp Hout]].
    apply (proj1 (embed_regex_semantics eqb eqb_spec _ p)) in Hp.
    destruct Hp as [w [-> Hw]].
    unfold constraint_projection in Hout. simpl in Hout.
    rewrite app_nil_r in Hout. inversion Hout; subst.
    split; [reflexivity|]. apply Nat.eqb_eq.
    apply (proj2 (Nat.mod_divides (length w) n ltac:(lia))).
    now apply (proj1 (power_star (n := n) w Hn)).
  - intros [-> Hv]. exists (v, []). split.
    + apply (proj2 (embed_regex_semantics eqb eqb_spec _ (v, []))).
      exists v. split; [reflexivity|]. apply (proj2 (power_star (n := n) v Hn)).
      apply (proj1 (Nat.mod_divides (length v) n ltac:(lia))).
      now apply Nat.eqb_eq.
    + unfold constraint_projection. simpl. now rewrite app_nil_r.
Qed.

(** Zero-width languages containing the identity combine by union. This is
    a consequence of partial prefix join, rather than an intersection rule. *)
Lemma zero_width_concat_union c d :
  empty_main_language (rewpla_denote eqb c) ->
  empty_main_language (rewpla_denote eqb d) ->
  rewpla_denote eqb c ([], []) -> rewpla_denote eqb d ([], []) ->
  lang_equiv (rewpla_denote eqb (WConcat c d))
    (rewpla_denote eqb (WPlus c d)).
Proof.
  intros Hc Hd Hc0 Hd0 out. simpl. unfold lang_concat, lang_union. split.
  - intros [[u v] [[u' v'] [Hp [Hq Hout]]]].
    pose proof (Hc (u,v) Hp) as Hu. pose proof (Hd (u',v') Hq) as Hu'.
    simpl in Hu, Hu'. subst u u'.
    pose proof (constraint_concat_result_shape eqb [] v [] v' Hout)
      as [t ->].
    destruct (empty_pair_concat_is_operand eqb eqb_spec v v' Hout)
      as [Heq | Heq]; subst t; auto.
  - intros [H|H].
    + exists out, ([], []). repeat split; try assumption.
      apply constraint_concat_right_identity. exact eqb_spec.
    + exists ([], []), out. repeat split; try assumption.
      apply constraint_concat_left_identity. exact eqb_spec.
Qed.

Definition suffixb periods n := Nat.eqb n 0 || PeriodicFamily.periodsb periods n.
Fixpoint assertions periods :=
  match periods with
  | [] => WEps
  | n :: ns => WConcat (assertion n) (assertions ns)
  end.

Lemma assertions_semantics periods u v :
  Forall (fun n => n > 0) periods ->
  (rewpla_denote eqb (assertions periods) (u, v) <->
    u = [] /\ suffixb periods (length v) = true).
Proof.
  intro Hperiods. revert u v.
  induction Hperiods as [|n ns Hn Hns IH]; intros u v.
  - unfold assertions, suffixb, PeriodicFamily.periodsb. simpl.
    unfold lang_one. rewrite Bool.orb_false_r, Nat.eqb_eq.
    split.
    + intro H. inversion H. subst. simpl. auto.
    + intros [-> Hv]. apply length_zero_iff_nil in Hv. now subst.
  - change (rewpla_denote eqb (WConcat (assertion n) (assertions ns)) (u,v)
      <-> u = [] /\ suffixb (n::ns) (length v) = true).
    eapply iff_trans.
    + apply zero_width_concat_union.
      * intros [x y] Hxy. apply assertion_semantics in Hxy; [exact (proj1 Hxy)|exact Hn].
      * intros [x y] Hxy. apply IH in Hxy. exact (proj1 Hxy).
      * apply assertion_semantics; [exact Hn|]. split; [reflexivity|].
        simpl. rewrite Nat.mod_0_l by lia. reflexivity.
      * apply IH. split; [reflexivity|]. unfold suffixb. reflexivity.
    +
    change (rewpla_denote eqb (assertion n) (u,v) \/
      rewpla_denote eqb (assertions ns) (u,v) <->
      u = [] /\ suffixb (n :: ns) (length v) = true).
    rewrite assertion_semantics by exact Hn. rewrite IH.
    unfold suffixb, PeriodicFamily.periodsb. simpl.
    rewrite !Bool.orb_true_iff. tauto.
Qed.

Lemma suffixb_nonempty periods n :
  periods <> [] -> Forall (fun p => p > 0) periods ->
  suffixb periods n = PeriodicFamily.periodsb periods n.
Proof.
  intros Hnon Hpos. unfold suffixb.
  destruct (Nat.eqb n 0) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. subst n.
  destruct periods as [|p ps]; [contradiction|].
  inversion Hpos; subst. unfold PeriodicFamily.periodsb. simpl.
  rewrite Nat.mod_0_l by lia. reflexivity.
Qed.

Definition prefix := embed_regex (Concat (Star sigma) (Atom trigger)).
Definition expression periods := WConcat prefix (assertions periods).

Lemma sigma_star w : matches (Star sigma) w.
Proof.
  induction w as [|b w IH]; [constructor|].
  change (matches (Star sigma) ([b] ++ w)). apply M_StarApp.
  - discriminate.
  - apply sigma_one. reflexivity.
  - exact IH.
Qed.

Lemma prefix_semantics u v :
  rewpla_denote eqb prefix (u,v) <->
    v = [] /\ PeriodicFamily.ends_in trigger u.
Proof.
  unfold prefix. rewrite embed_regex_semantics by exact eqb_spec.
  split.
  - intros [w [Hpair H]]. inversion Hpair; subst.
    inversion H; subst. inversion H4; subst.
    split; [reflexivity|]. eexists. reflexivity.
  - intros [-> [x ->]]. exists (x ++ [trigger]). split; [reflexivity|].
    constructor; [apply sigma_star|constructor].
Qed.

Theorem expression_semantics periods u v :
  periods <> [] -> Forall (fun p => p > 0) periods ->
  (rewpla_denote eqb (expression periods) (u,v) <->
    PeriodicFamily.ends_in trigger u /\
    PeriodicFamily.periodsb periods (length v) = true).
Proof.
  intros Hnon Hpos. unfold expression. simpl. unfold lang_concat. split.
  - intros [[x c] [[y d] [H1 [H2 Hout]]]].
    apply prefix_semantics in H1 as [-> Hx].
    apply assertions_semantics in H2 as [-> Hd]; [|exact Hpos].
    unfold constraint_concat in Hout. simpl in Hout. rewrite app_nil_r in Hout.
    destruct d; inversion Hout; subst; split; try exact Hx;
      rewrite <- suffixb_nonempty by assumption; exact Hd.
  - intros [Hu Hv]. exists (u, []), ([],v). repeat split.
    + apply prefix_semantics. now split.
    + apply assertions_semantics; [exact Hpos|]. split; [reflexivity|].
      now rewrite suffixb_nonempty by assumption.
    + unfold constraint_concat. simpl. rewrite app_nil_r. destruct v; reflexivity.
Qed.

Lemma accepts_zeros (modulus : nat) (w : list A) :
  PeriodicFamily.accepts (PeriodicFamily.zeros modulus) w = false.
Proof.
  destruct modulus as [|m]; [induction w; simpl; assumption || reflexivity|].
  rewrite PeriodicFamily.accepts_nth by (rewrite PeriodicFamily.zeros_length; lia).
  unfold PeriodicFamily.zeros. apply nth_repeat.
Qed.

Lemma ends_in_nonempty u : PeriodicFamily.ends_in trigger u -> u <> [].
Proof.
  intros [x ->] H. apply (f_equal (@length A)) in H.
  rewrite app_length in H. simpl in H. lia.
Qed.

Theorem initial_correspondence periods modulus :
  periods <> [] -> Forall (fun p => p > 0) periods ->
  lang_equiv (rewpla_denote eqb (expression periods))
    (PeriodicFamily.residual_language trigger
      (fun v => PeriodicFamily.periodsb periods (length v))
      (PeriodicFamily.zeros modulus)).
Proof.
  intros Hnon Hpos [u v]. rewrite expression_semantics by assumption.
  unfold PeriodicFamily.residual_language. simpl. rewrite accepts_zeros.
  pose proof (ends_in_nonempty (u := u)). intuition discriminate.
Qed.

Fixpoint run modulus periods (s : PeriodicFamily.bitvec) (w : list A) :=
  match w with
  | [] => s
  | a :: w' => run modulus periods
      (PeriodicFamily.step eqb trigger (PeriodicFamily.base modulus periods) s a) w'
  end.

Lemma run_length modulus periods w s :
  length s = modulus -> length (run modulus periods s w) = modulus.
Proof.
  revert s. induction w as [|a w IH]; intros s Hs; simpl; [exact Hs|].
  apply IH. rewrite PeriodicFamily.step_length;
    [exact Hs|rewrite PeriodicFamily.base_length; symmetry; exact Hs].
Qed.

Theorem run_quotient_correspondence modulus periods w s :
  modulus <> 0 ->
  Forall (fun p => p <> 0 /\ Nat.divide p modulus) periods ->
  length s = modulus ->
  lang_equiv
    (pair_language_word_quotient eqb w
      (PeriodicFamily.residual_language trigger
        (fun v => PeriodicFamily.periodsb periods (length v)) s))
    (PeriodicFamily.residual_language trigger
      (fun v => PeriodicFamily.periodsb periods (length v))
      (run modulus periods s w)).
Proof.
  intros Hmod Hperiods. revert s.
  induction w as [|a w IH]; intros s Hs; simpl.
  - intro p. unfold pair_language_word_quotient. split.
    + intros [q [Hq Hout]]. inversion Hout; subst. exact Hq.
    + intro Hp. exists p. now split.
  - eapply lang_equiv_trans.
    + apply pair_language_word_quotient_cons.
    + eapply lang_equiv_trans.
      * apply pair_language_word_quotient_compat.
        apply PeriodicFamily.residual_symbol_quotient; [exact eqb_spec| |].
        -- rewrite PeriodicFamily.base_length. symmetry. exact Hs.
        -- intro v. apply PeriodicFamily.accepts_base; assumption.
      * apply IH. rewrite PeriodicFamily.step_length;
          [exact Hs|rewrite PeriodicFamily.base_length; symmetry; exact Hs].
Qed.

Theorem word_derivative_correspondence modulus periods w :
  modulus <> 0 -> periods <> [] ->
  Forall (fun p => p <> 0 /\ Nat.divide p modulus) periods ->
  lang_equiv (rewpla_denote eqb (word_derivative eqb w (expression periods)))
    (PeriodicFamily.residual_language trigger
      (fun v => PeriodicFamily.periodsb periods (length v))
      (run modulus periods (PeriodicFamily.zeros modulus) w)).
Proof.
  intros Hmod Hnon Hperiods. eapply lang_equiv_trans.
  - apply word_derivative_correct. exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply pair_language_word_quotient_compat. apply initial_correspondence.
      * exact Hnon.
      * eapply Forall_impl; [|exact Hperiods]. intros p [Hp _]. lia.
    + apply run_quotient_correspondence; try assumption.
      apply PeriodicFamily.zeros_length.
Qed.

Theorem dfa_accept_correct modulus periods w :
  modulus <> 0 -> periods <> [] ->
  Forall (fun p => p <> 0 /\ Nat.divide p modulus) periods ->
  (hd false (run modulus periods (PeriodicFamily.zeros modulus) w) = true
    <-> rewpla_language eqb (expression periods) w).
Proof.
  intros Hmod Hnon Hperiods.
  pose proof (word_derivative_correspondence w Hmod Hnon Hperiods
    ([], [])) as Hpair.
  unfold PeriodicFamily.residual_language, PeriodicFamily.accepts in Hpair.
  simpl in Hpair.
  rewrite <- rewpla_nullable_correct in Hpair by exact eqb_spec.
  pose proof (rewpla_acceptb_correct eqb eqb_spec (expression periods) w) as Haccept.
  unfold rewpla_acceptb in Haccept. tauto.
Qed.

Definition residue_regex modulus i :=
  Concat (power sigma i) (Star (power sigma modulus)).

Lemma residue_regex_correct modulus i w :
  modulus > 0 -> i < modulus ->
  (matches (residue_regex modulus i) w <-> length w mod modulus = i).
Proof.
  intros Hmod Hi. unfold residue_regex. split.
  - intro H. inversion H; subst. apply power_length in H2.
    apply (proj1 (power_star (n := modulus) v Hmod)) in H4 as [k Hk].
    rewrite length_app, H2, Hk.
    replace (i + modulus * k) with (i + k * modulus) by lia.
    rewrite Nat.mod_add by lia. now apply Nat.mod_small.
  - intro Hres. assert (Hlower : i <= length w).
    { pose proof (Nat.mod_le (length w) modulus). lia. }
    rewrite <- (firstn_skipn i w) at 1. apply M_Concat.
    + apply power_length. rewrite length_firstn, Nat.min_l by exact Hlower.
      reflexivity.
    + apply (proj2 (power_star (n := modulus) (skipn i w) Hmod)).
      exists (length w / modulus). rewrite length_skipn.
      pose proof (Nat.div_mod (length w) modulus ltac:(lia)). nia.
Qed.

Definition selected_regex modulus (s : PeriodicFamily.bitvec) :=
  fold_right (fun i rest => Plus (residue_regex modulus i) rest) Zero
    (filter (fun i => nth i s false) (seq 0 modulus)).

Lemma selected_regex_correct modulus s w :
  modulus > 0 -> length s = modulus ->
  (matches (selected_regex modulus s) w <-> PeriodicFamily.accepts s w = true).
Proof.
  intros Hmod Hs. unfold selected_regex.
  assert (Hfold : forall ids,
    matches (fold_right (fun i rest => Plus (residue_regex modulus i) rest)
      Zero ids) w <->
    exists i, In i ids /\ matches (residue_regex modulus i) w).
  { induction ids as [|i ids IH]; simpl.
    - split; [intro H; inversion H|intros [i [H _]]; contradiction].
    - split.
      + intro H. inversion H; subst.
        * exists i. split; [now left|assumption].
        * match goal with
          | Hrest : matches (fold_right _ Zero ids) w |- _ =>
              apply (proj1 IH) in Hrest as [j [Hj Hmatch]]
          end. exists j. split; [now right|exact Hmatch].
      + intros [j [[<-|Hj] Hmatch]].
        * apply M_PlusL. exact Hmatch.
        * apply M_PlusR, (proj2 IH). exists j. now split. }
  rewrite Hfold, PeriodicFamily.accepts_nth by lia. rewrite Hs.
  split.
  - intros [i [Hin Hmatch]]. apply filter_In in Hin as [Hseq Hbit].
    apply in_seq in Hseq. simpl in Hseq.
    apply residue_regex_correct in Hmatch; [|exact Hmod|lia].
    now rewrite Hmatch.
  - intro Hbit. exists (length w mod modulus). split.
    + apply filter_In. split.
      * apply in_seq. split; [lia|apply Nat.mod_upper_bound; lia].
      * exact Hbit.
    + apply residue_regex_correct;
        [exact Hmod|apply Nat.mod_upper_bound; lia|reflexivity].
Qed.

Definition representative modulus periods s :=
  WPlus (expression periods) (WLookahead (embed_regex (selected_regex modulus s))).

Theorem representative_correct modulus periods s :
  modulus > 0 -> periods <> [] -> Forall (fun p => p > 0) periods ->
  length s = modulus ->
  lang_equiv (rewpla_denote eqb (representative modulus periods s))
    (PeriodicFamily.residual_language trigger
      (fun v => PeriodicFamily.periodsb periods (length v)) s).
Proof.
  intros Hmod Hnon Hpos Hs [u v]. unfold representative.
  change (rewpla_denote eqb (expression periods) (u,v) \/
    rewpla_denote eqb (WLookahead (embed_regex (selected_regex modulus s))) (u,v)
    <-> PeriodicFamily.residual_language trigger
      (fun v => PeriodicFamily.periodsb periods (length v)) s (u,v)).
  rewrite expression_semantics by assumption.
  assert (Hla : rewpla_denote eqb
    (WLookahead (embed_regex (selected_regex modulus s))) (u,v) <->
    u = [] /\ PeriodicFamily.accepts s v = true).
  { split.
    - intros [p [Hp Hout]].
      apply (proj1 (embed_regex_semantics eqb eqb_spec _ p)) in Hp.
      destruct Hp as [w [-> Hw]]. unfold constraint_projection in Hout.
      simpl in Hout. rewrite app_nil_r in Hout. inversion Hout; subst u v.
      split; [reflexivity|]. now apply (proj1 (selected_regex_correct s w Hmod Hs)).
    - intros [-> Hv]. exists (v, []). split.
      + apply (proj2 (embed_regex_semantics eqb eqb_spec _ (v, []))).
        exists v. split; [reflexivity|].
        now apply (proj2 (selected_regex_correct s v Hmod Hs)).
      + unfold constraint_projection. simpl. now rewrite app_nil_r. }
  rewrite Hla. unfold PeriodicFamily.residual_language. simpl.
  pose proof (ends_in_nonempty (u := u)). tauto.
Qed.

Theorem representative_word_derivative_correct modulus periods w :
  modulus <> 0 -> periods <> [] ->
  Forall (fun p => p <> 0 /\ Nat.divide p modulus) periods ->
  lang_equiv (rewpla_denote eqb (word_derivative eqb w (expression periods)))
    (rewpla_denote eqb (representative modulus periods
      (run modulus periods (PeriodicFamily.zeros modulus) w))).
Proof.
  intros Hmod Hnon Hperiods. eapply lang_equiv_trans.
  - apply (word_derivative_correspondence (modulus := modulus) w); assumption.
  - apply lang_equiv_sym, representative_correct; try assumption; try lia.
    + eapply Forall_impl; [|exact Hperiods]. intros p [Hp _]. lia.
    + apply run_length, PeriodicFamily.zeros_length.
Qed.

(** Bit equality is exactly full pair-language equality for every modulus.
    Context probes of lengths 0..modulus-1 distinguish all bits. *)
Theorem residual_language_eq_iff modulus suffix x y :
  modulus > 0 -> length x = modulus -> length y = modulus ->
  (lang_equiv (PeriodicFamily.residual_language trigger suffix x)
    (PeriodicFamily.residual_language trigger suffix y) <-> x = y).
Proof.
  intros Hmod Hx Hy. split.
  - intro Hequiv. apply (nth_ext x y false false ltac:(lia)). intros n Hn.
    pose proof (Hequiv ([], repeat trigger n)) as Hprobe.
    unfold PeriodicFamily.residual_language in Hprobe. simpl in Hprobe.
    assert (Haccept : PeriodicFamily.accepts x (repeat trigger n) = true <->
      PeriodicFamily.accepts y (repeat trigger n) = true) by intuition discriminate.
    rewrite !PeriodicFamily.accepts_nth in Haccept by lia.
    rewrite !repeat_length, Hx, Hy, Nat.mod_small in Haccept by lia.
    destruct (nth n x false), (nth n y false); intuition discriminate.
  - intros ->. apply lang_equiv_refl.
Qed.

(** Parsing associates adjacent assertions to the left. Associativity and
    the identity law relate that syntax to the expression proved above. *)
Fixpoint append_assertions r periods :=
  match periods with
  | [] => r
  | n :: ns => append_assertions (WConcat r (assertion n)) ns
  end.

Lemma append_assertions_correct r periods :
  lang_equiv (rewpla_denote eqb (append_assertions r periods))
    (rewpla_denote eqb (WConcat r (assertions periods))).
Proof.
  revert r. induction periods as [|n ns IH]; intro r; simpl.
  - apply lang_equiv_sym, lang_concat_one_right. exact eqb_spec.
  - eapply lang_equiv_trans.
    + apply IH.
    + apply lang_concat_assoc. exact eqb_spec.
Qed.

Theorem after_trigger_display_correct modulus periods :
  modulus <> 0 -> periods <> [] ->
  Forall (fun p => p <> 0 /\ Nat.divide p modulus) periods ->
  lang_equiv (rewpla_denote eqb
    (word_derivative eqb [trigger] (expression periods)))
    (rewpla_denote eqb (WPlus (expression periods) (assertions periods))).
Proof.
  intros Hmod Hnon Hperiods. eapply lang_equiv_trans.
  - apply (word_derivative_correspondence (modulus := modulus) [trigger]); assumption.
  - intros [u v].
    change (PeriodicFamily.residual_language trigger
      (fun v => PeriodicFamily.periodsb periods (length v))
      (PeriodicFamily.step eqb trigger (PeriodicFamily.base modulus periods)
        (PeriodicFamily.zeros modulus) trigger) (u,v) <->
      rewpla_denote eqb (expression periods) (u,v) \/
      rewpla_denote eqb (assertions periods) (u,v)).
    assert (Hpos : Forall (fun p => p > 0) periods).
    { eapply Forall_impl; [|exact Hperiods]. intros p [Hp _]. lia. }
    rewrite expression_semantics, assertions_semantics by assumption.
    rewrite suffixb_nonempty by assumption.
    unfold PeriodicFamily.residual_language, PeriodicFamily.step. simpl.
    rewrite (proj2 (eqb_spec trigger trigger) eq_refl).
    rewrite PeriodicFamily.accepts_union.
    2:{ rewrite PeriodicFamily.rotate_length, PeriodicFamily.zeros_length,
          PeriodicFamily.base_length. reflexivity. }
    rewrite PeriodicFamily.accepts_base by assumption.
    rewrite <- (@PeriodicFamily.accepts_cons A (PeriodicFamily.zeros modulus) trigger v).
    rewrite accepts_zeros. simpl.
    pose proof (ends_in_nonempty (u := u)). tauto.
Qed.

Theorem closed_table_run_membership modulus periods alphabet states w s :
  states_closedb eqb trigger (PeriodicFamily.base modulus periods)
    alphabet states = true -> In s states ->
  (forall a, In a w -> In a alphabet) ->
  In (run modulus periods s w) states.
Proof.
  intros Hclosed. revert s. induction w as [|a w IH]; intros s Hs Hw; simpl.
  - exact Hs.
  - apply IH.
    + eapply states_closedb_sound; [exact Hclosed|exact Hs|].
      apply Hw. now left.
    + intros b Hb. apply Hw. now right.
Qed.

Theorem closed_table_dfa_accept_correct modulus periods alphabet states :
  parameters_validb modulus periods = true ->
  states_closedb eqb trigger (PeriodicFamily.base modulus periods)
    alphabet states = true ->
  In (PeriodicFamily.zeros modulus) states ->
  forall w, (forall a, In a w -> In a alphabet) ->
    In (run modulus periods (PeriodicFamily.zeros modulus) w) states /\
    (hd false (run modulus periods (PeriodicFamily.zeros modulus) w) = true
      <-> rewpla_language eqb (expression periods) w).
Proof.
  intros Hvalid Hclosed Hzero w Hw.
  destruct (parameters_validb_sound modulus periods Hvalid) as [Hmod [Hnon Hperiods]].
  split.
  - eapply closed_table_run_membership; eassumption.
  - apply dfa_accept_correct; assumption.
Qed.

End Alphabet.
End PeriodicAutomaton.

Print Assumptions PeriodicAutomaton.expression_semantics.
Print Assumptions PeriodicAutomaton.word_derivative_correspondence.
Print Assumptions PeriodicAutomaton.dfa_accept_correct.
Print Assumptions PeriodicAutomaton.representative_word_derivative_correct.
Print Assumptions PeriodicAutomaton.residual_language_eq_iff.
Print Assumptions PeriodicAutomaton.closed_table_dfa_accept_correct.
