From Stdlib Require Import List Bool.
From CCont Require Import StringConstraints LookaheadSemantics
  LookaheadDerivatives LookaheadDecision PositiveCongruence.
Import ListNotations.

Set Implicit Arguments.

(** Executable normal forms for the positive-lookahead congruence (P1)--(P11).

    A normal form is a finite idempotent sum of words.  Concatenation is
    flattened inside each word, and every maximal block of positive logical
    atoms is sorted and deduplicated.  Once union and concatenation have been
    distributed, the only non-unit logical atoms left in a word are
    lookaheads, so precisely those blocks are subject to (P10)--(P11). *)

Definition positive_factorb {A} (r : rewpla A) : bool :=
  match r with
  | WLookahead _ => true
  | _ => false
  end.

Fixpoint positive_insert_factor {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (x : rewpla A) (xs : list (rewpla A)) : list (rewpla A) :=
  match xs with
  | [] => [x]
  | y :: ys =>
      if positive_factorb y then
        if rewpla_eqb eqb x y then y :: ys
        else if rewpla_term_ltb atom_code x y then x :: y :: ys
        else y :: positive_insert_factor eqb atom_code x ys
      else x :: y :: ys
  end.

Fixpoint positive_word_normalize {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (xs : list (rewpla A)) : list (rewpla A) :=
  match xs with
  | [] => []
  | x :: xs' =>
      let ys := positive_word_normalize eqb atom_code xs' in
      if positive_factorb x
      then positive_insert_factor eqb atom_code x ys
      else x :: ys
  end.

Fixpoint positive_word_build {A} (xs : list (rewpla A)) : rewpla A :=
  match xs with
  | [] => WEps
  | [x] => x
  | x :: xs' => WConcat x (positive_word_build xs')
  end.

Fixpoint positive_sum_insert {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (x : rewpla A) (xs : list (rewpla A)) : list (rewpla A) :=
  match xs with
  | [] => [x]
  | y :: ys =>
      if rewpla_eqb eqb x y then y :: ys
      else if rewpla_term_ltb atom_code x y then x :: y :: ys
      else y :: positive_sum_insert eqb atom_code x ys
  end.

Fixpoint positive_sum_normalize {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (xs : list (rewpla A)) : list (rewpla A) :=
  match xs with
  | [] => []
  | x :: xs' => positive_sum_insert eqb atom_code x
      (positive_sum_normalize eqb atom_code xs')
  end.

Definition positive_sum_build {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (xss : list (list (rewpla A))) : rewpla A :=
  aci_union_build
    (positive_sum_normalize eqb atom_code
      (map positive_word_build xss)).

Fixpoint positive_logicalb {A} (r : rewpla A) : bool :=
  match r with
  | WZero | WEps | WLookahead _ => true
  | WPlus p q | WConcat p q => positive_logicalb p && positive_logicalb q
  | WAtom _ | WStar _ => false
  end.

Fixpoint positive_dnf {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (r : rewpla A) : list (list (rewpla A)) :=
  match r with
  | WZero => []
  | WEps => [[]]
  | WAtom a => [[WAtom a]]
  | WPlus p q =>
      positive_dnf eqb atom_code p ++ positive_dnf eqb atom_code q
  | WConcat p q =>
      if positive_logicalb p && rewpla_eqb eqb p q then
        positive_dnf eqb atom_code p
      else flat_map
        (fun xs =>
          map (fun ys =>
            positive_word_normalize eqb atom_code (xs ++ ys))
            (positive_dnf eqb atom_code q))
        (positive_dnf eqb atom_code p)
  | WStar p =>
      [[WStar (positive_sum_build eqb atom_code
        (positive_dnf eqb atom_code p))]]
  | WLookahead p =>
      [[WLookahead (positive_sum_build eqb atom_code
        (positive_dnf eqb atom_code p))]]
  end.

Definition rewpla_positive_normalize {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (r : rewpla A) : rewpla A :=
  positive_sum_build eqb atom_code (positive_dnf eqb atom_code r).

Definition rewpla_positive_symbol_step {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (a : A) (r : rewpla A) : rewpla A :=
  rewpla_positive_normalize eqb atom_code
    (rewpla_paper_symbol_step eqb atom_code a r).

Fixpoint rewpla_positive_word_step {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (w : list A) (r : rewpla A) : rewpla A :=
  match w with
  | [] => r
  | a :: w' => rewpla_positive_word_step eqb atom_code w'
      (rewpla_positive_symbol_step eqb atom_code a r)
  end.

Definition rewpla_positive_states_closedb {A}
    (eqb : A -> A -> bool) (atom_code : A -> nat)
    (alphabet : list A) (states : list (rewpla A)) : bool :=
  forallb (fun q => forallb (fun a =>
    existsb (rewpla_eqb eqb
      (rewpla_positive_symbol_step eqb atom_code a q)) states)
    alphabet) states.

Section CongruenceCorrectness.
Context {A : Type}.
Variable eqb : A -> A -> bool.
Variable atom_code : A -> nat.
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma positive_logicalb_sound (r : rewpla A) :
  positive_logicalb r = true -> positive_logical r.
Proof.
  induction r; simpl; intro H; try discriminate;
    try (constructor; assumption).
  - apply andb_true_iff in H as [Hp Hq].
    apply PL_plus; [apply IHr1|apply IHr2]; assumption.
  - apply andb_true_iff in H as [Hp Hq].
    apply PL_concat; [apply IHr1|apply IHr2]; assumption.
Qed.

Lemma positive_factorb_logical (r : rewpla A) :
  positive_factorb r = true -> positive_logical r.
Proof. destruct r; simpl; try discriminate; constructor. Qed.

Lemma positive_word_build_cons (x : rewpla A) xs :
  WConcat x (positive_word_build xs) ==p positive_word_build (x :: xs).
Proof.
  destruct xs as [|y ys]; simpl.
  - apply PC_concat_eps_right.
  - apply PC_refl.
Qed.

Lemma positive_union_build_cons (x : rewpla A) xs :
  WPlus x (aci_union_build xs) ==p aci_union_build (x :: xs).
Proof.
  destruct xs as [|y ys]; simpl.
  - apply PC_plus_zero_right.
  - apply PC_refl.
Qed.

Lemma positive_insert_factor_congruent (x : rewpla A) xs :
  positive_factorb x = true ->
  WConcat x (positive_word_build xs) ==p
    positive_word_build (positive_insert_factor eqb atom_code x xs).
Proof.
  intro Hx. induction xs as [|y ys IH]; simpl.
  - apply PC_concat_eps_right.
  - destruct (positive_factorb y) eqn:Hy.
    + destruct (rewpla_eqb eqb x y) eqn:Hxy.
      * apply (proj1 (rewpla_eqb_spec eqb eqb_spec x y)) in Hxy. subst y.
        eapply PC_trans.
        -- apply PC_concat_congr; [apply PC_refl|].
           apply PC_sym, positive_word_build_cons.
        -- eapply PC_trans; [apply PC_concat_assoc|].
           eapply PC_trans.
           ++ apply PC_concat_congr.
              ** apply PC_constraint_idem.
                 now apply positive_factorb_logical.
              ** apply PC_refl.
           ++ apply positive_word_build_cons.
      * destruct (rewpla_term_ltb atom_code x y) eqn:Hlt.
        -- change (WConcat x (positive_word_build (y :: ys)) ==p
             positive_word_build (x :: y :: ys)).
           apply positive_word_build_cons.
        -- eapply PC_trans.
           ++ apply PC_concat_congr; [apply PC_refl|].
              apply PC_sym, positive_word_build_cons.
           ++ eapply PC_trans; [apply PC_concat_assoc|].
              eapply PC_trans.
              ** apply PC_concat_congr.
                 --- apply PC_constraint_comm;
                       now apply positive_factorb_logical.
                 --- apply PC_refl.
              ** eapply PC_trans.
                 --- apply PC_sym, PC_concat_assoc.
                 --- eapply PC_trans.
                     +++ apply PC_concat_congr; [apply PC_refl|apply IH].
                     +++ apply positive_word_build_cons.
    + change (WConcat x (positive_word_build (y :: ys)) ==p
         positive_word_build (x :: y :: ys)).
      apply positive_word_build_cons.
Qed.

Lemma positive_word_normalize_congruent xs :
  positive_word_build xs ==p
    positive_word_build (positive_word_normalize eqb atom_code xs).
Proof.
  induction xs as [|x xs IH]; simpl; [apply PC_refl|].
  eapply PC_trans.
  - apply PC_sym, positive_word_build_cons.
  - eapply PC_trans.
    + apply PC_concat_congr; [apply PC_refl|exact IH].
    + destruct (positive_factorb x) eqn:Hx.
      * now apply positive_insert_factor_congruent.
      * apply positive_word_build_cons.
Qed.

Lemma positive_sum_insert_congruent (x : rewpla A) xs :
  WPlus x (aci_union_build xs) ==p
    aci_union_build (positive_sum_insert eqb atom_code x xs).
Proof.
  induction xs as [|y ys IH]; simpl.
  - apply PC_plus_zero_right.
  - destruct (rewpla_eqb eqb x y) eqn:Hxy.
    + apply (proj1 (rewpla_eqb_spec eqb eqb_spec x y)) in Hxy. subst y.
      eapply PC_trans.
      * apply PC_plus_congr; [apply PC_refl|].
        apply PC_sym, positive_union_build_cons.
      * eapply PC_trans; [apply PC_plus_assoc|].
        eapply PC_trans.
        -- apply PC_plus_congr; [apply PC_plus_idem|apply PC_refl].
        -- apply positive_union_build_cons.
    + destruct (rewpla_term_ltb atom_code x y) eqn:Hlt.
      * change (WPlus x (aci_union_build (y :: ys)) ==p
           aci_union_build (x :: y :: ys)).
        apply positive_union_build_cons.
      * eapply PC_trans.
        -- apply PC_plus_congr; [apply PC_refl|].
           apply PC_sym, positive_union_build_cons.
        -- eapply PC_trans; [apply PC_plus_assoc|].
           eapply PC_trans.
           ++ apply PC_plus_congr; [apply PC_plus_comm|apply PC_refl].
           ++ eapply PC_trans.
              ** apply PC_sym, PC_plus_assoc.
              ** eapply PC_trans.
                 --- apply PC_plus_congr; [apply PC_refl|exact IH].
                 --- apply positive_union_build_cons.
Qed.

Lemma positive_sum_normalize_congruent xs :
  aci_union_build xs ==p
    aci_union_build (positive_sum_normalize eqb atom_code xs).
Proof.
  induction xs as [|x xs IH]; simpl; [apply PC_refl|].
  eapply PC_trans.
  - apply PC_sym, positive_union_build_cons.
  - eapply PC_trans.
    + apply PC_plus_congr; [apply PC_refl|exact IH].
    + apply positive_sum_insert_congruent.
Qed.

Lemma positive_sum_build_raw_congruent xss :
  aci_union_build (map positive_word_build xss) ==p
    positive_sum_build eqb atom_code xss.
Proof.
  unfold positive_sum_build. apply positive_sum_normalize_congruent.
Qed.

Lemma positive_union_build_append (xs ys : list (rewpla A)) :
  aci_union_build (xs ++ ys) ==p
    WPlus (aci_union_build xs) (aci_union_build ys).
Proof.
  induction xs as [|x xs IH]; simpl.
  - apply PC_sym, PC_plus_zero_left.
  - eapply PC_trans.
    + apply PC_sym, positive_union_build_cons.
    + eapply PC_trans.
      * apply PC_plus_congr; [apply PC_refl|exact IH].
      * eapply PC_trans; [apply PC_plus_assoc|].
        apply PC_plus_congr; [apply positive_union_build_cons|apply PC_refl].
Qed.

Lemma positive_union_build_forall2 (xs ys : list (rewpla A)) :
  Forall2 (@positive_congruence A) xs ys ->
  aci_union_build xs ==p aci_union_build ys.
Proof.
  intro H. induction H; simpl; [apply PC_refl|].
  eapply PC_trans.
  - apply PC_sym, positive_union_build_cons.
  - eapply PC_trans.
    + apply PC_plus_congr; eassumption.
    + apply positive_union_build_cons.
Qed.

Lemma positive_concat_word_append (xs ys : list (rewpla A)) :
  WConcat (positive_word_build xs) (positive_word_build ys) ==p
    positive_word_build (xs ++ ys).
Proof.
  induction xs as [|x xs IH]; simpl.
  - apply PC_concat_eps_left.
  - eapply PC_trans.
    + apply PC_concat_congr.
      * apply PC_sym, positive_word_build_cons.
      * apply PC_refl.
    + eapply PC_trans.
      * apply PC_sym, PC_concat_assoc.
      * eapply PC_trans.
        -- apply PC_concat_congr; [apply PC_refl|exact IH].
        -- apply positive_word_build_cons.
Qed.

Lemma positive_concat_one_union (x : rewpla A) (ys : list (rewpla A)) :
  WConcat x (aci_union_build ys) ==p
    aci_union_build (map (WConcat x) ys).
Proof.
  induction ys as [|y ys IH]; simpl.
  - apply PC_concat_zero_right.
  - eapply PC_trans.
    + apply PC_concat_congr; [apply PC_refl|].
      apply PC_sym, positive_union_build_cons.
    + eapply PC_trans; [apply PC_left_distrib|].
      eapply PC_trans.
      * apply PC_plus_congr; [apply PC_refl|exact IH].
      * apply positive_union_build_cons.
Qed.

Definition positive_expression_products
    (xs ys : list (rewpla A)) : list (rewpla A) :=
  flat_map (fun x => map (WConcat x) ys) xs.

Lemma positive_concat_union_products
    (xs ys : list (rewpla A)) :
  WConcat (aci_union_build xs) (aci_union_build ys) ==p
    aci_union_build (positive_expression_products xs ys).
Proof.
  induction xs as [|x xs IH]; simpl.
  - apply PC_concat_zero_left.
  - eapply PC_trans.
    + apply PC_concat_congr.
      * apply PC_sym, positive_union_build_cons.
      * apply PC_refl.
    + eapply PC_trans; [apply PC_right_distrib|].
      eapply PC_trans.
      * apply PC_plus_congr; [apply positive_concat_one_union|exact IH].
      * apply PC_sym, positive_union_build_append.
Qed.

Lemma positive_word_product_map_congruent
    (xs : list (rewpla A)) (yss : list (list (rewpla A))) :
  aci_union_build
      (map (fun ys =>
        WConcat (positive_word_build xs) (positive_word_build ys)) yss)
    ==p
  aci_union_build
      (map positive_word_build
        (map (fun ys =>
          positive_word_normalize eqb atom_code (xs ++ ys)) yss)).
Proof.
  induction yss as [|ys yss IH]; simpl; [apply PC_refl|].
  eapply PC_trans.
  - apply PC_sym, positive_union_build_cons.
  - eapply PC_trans.
    + apply PC_plus_congr.
      * eapply PC_trans; [apply positive_concat_word_append|].
        apply positive_word_normalize_congruent.
      * exact IH.
    + apply positive_union_build_cons.
Qed.

Lemma positive_word_products_congruent
    (xss yss : list (list (rewpla A))) :
  aci_union_build
      (positive_expression_products
        (map positive_word_build xss) (map positive_word_build yss))
    ==p
  aci_union_build
      (map positive_word_build
        (flat_map (fun xs =>
          map (fun ys =>
            positive_word_normalize eqb atom_code (xs ++ ys)) yss) xss)).
Proof.
  induction xss as [|xs xss IH]; simpl; [apply PC_refl|].
  eapply PC_trans.
  - apply positive_union_build_append.
  - eapply PC_trans.
    + apply PC_plus_congr.
      * rewrite map_map. apply positive_word_product_map_congruent.
      * exact IH.
    + rewrite map_app. apply PC_sym, positive_union_build_append.
Qed.

End CongruenceCorrectness.

Section NormalizerCorrectness.
Context {A : Type}.
Variable eqb : A -> A -> bool.
Variable atom_code : A -> nat.
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma positive_dnf_raw_congruent (r : rewpla A) :
  r ==p aci_union_build
    (map positive_word_build (positive_dnf eqb atom_code r)).
Proof.
  induction r as [| |a|p IHp q IHq|p IHp q IHq|p IHp|p IHp];
    cbn [positive_dnf map].
  - apply PC_refl.
  - apply PC_refl.
  - apply PC_refl.
  - eapply PC_trans.
    + apply PC_plus_congr; [exact IHp|exact IHq].
    + rewrite map_app.
      apply PC_sym, positive_union_build_append; exact eqb_spec.
  - destruct (positive_logicalb p && rewpla_eqb eqb p q)
      eqn:Hlogical.
    + apply andb_true_iff in Hlogical as [Hp Hpq].
      apply (proj1 (rewpla_eqb_spec eqb eqb_spec p q)) in Hpq.
      subst q. eapply PC_trans.
      * apply PC_constraint_idem.
        now apply positive_logicalb_sound.
      * exact IHp.
    + eapply PC_trans.
      * apply PC_concat_congr; [exact IHp|exact IHq].
      * eapply PC_trans.
        -- apply positive_concat_union_products; exact eqb_spec.
        -- apply positive_word_products_congruent; exact eqb_spec.
  - eapply PC_trans.
    + apply PC_star_congr.
      eapply PC_trans; [exact IHp|].
      apply positive_sum_build_raw_congruent; exact eqb_spec.
    + apply PC_refl.
  - eapply PC_trans.
    + apply PC_lookahead_congr.
      eapply PC_trans; [exact IHp|].
      apply positive_sum_build_raw_congruent; exact eqb_spec.
    + apply PC_refl.
Qed.

Theorem rewpla_positive_normalize_congruent (r : rewpla A) :
  r ==p rewpla_positive_normalize eqb atom_code r.
Proof.
  unfold rewpla_positive_normalize.
  eapply PC_trans with (s := aci_union_build
    (map positive_word_build (positive_dnf eqb atom_code r))).
  - now apply positive_dnf_raw_congruent.
  - now apply positive_sum_build_raw_congruent.
Qed.

Theorem rewpla_positive_normalize_correct_M (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb (rewpla_positive_normalize eqb atom_code r))
    (rewpla_denote eqb r).
Proof.
  apply (positive_congruence_sound_M eqb eqb_spec).
  apply PC_sym, rewpla_positive_normalize_congruent.
Qed.

Definition rewpla_positive_equiv (r s : rewpla A) : Prop :=
  rewpla_positive_normalize eqb atom_code r =
  rewpla_positive_normalize eqb atom_code s.

Theorem rewpla_positive_equiv_sound (r s : rewpla A) :
  rewpla_positive_equiv r s -> r ==p s.
Proof.
  unfold rewpla_positive_equiv. intro H.
  eapply PC_trans.
  - apply rewpla_positive_normalize_congruent.
  - rewrite H. apply PC_sym, rewpla_positive_normalize_congruent.
Qed.

Theorem rewpla_positive_symbol_step_correct_M a (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb
      (rewpla_positive_symbol_step eqb atom_code a r))
    (pair_language_symbol_quotient eqb a (rewpla_denote eqb r)).
Proof.
  unfold rewpla_positive_symbol_step. eapply lang_equiv_trans.
  - apply rewpla_positive_normalize_correct_M.
  - apply rewpla_paper_symbol_step_correct_M. exact eqb_spec.
Qed.

Theorem rewpla_positive_word_step_correct_M w (r : rewpla A) :
  lang_equiv
    (rewpla_denote eqb
      (rewpla_positive_word_step eqb atom_code w r))
    (pair_language_word_quotient eqb w (rewpla_denote eqb r)).
Proof.
  revert r. induction w as [|a w IH]; intro r; simpl.
  - intro q. unfold pair_language_word_quotient. split.
    + intro Hq. exists q. now split.
    + intros [p [Hp Hstep]]. inversion Hstep; subst p. exact Hp.
  - eapply lang_equiv_trans.
    + apply IH.
    + eapply lang_equiv_trans.
      * apply pair_language_word_quotient_compat.
        apply rewpla_positive_symbol_step_correct_M.
      * apply lang_equiv_sym, pair_language_word_quotient_cons.
Qed.

(** The CLI first applies the already proved lookahead laws from Eq. (35),
    then the (P1)--(P11) normal form.  Equality of these executable keys is
    a sound state merge even when the first stage uses semantic equations
    beyond the generated positive congruence. *)
Definition rewpla_merged_key (r : rewpla A) : rewpla A :=
  rewpla_positive_normalize eqb atom_code (rewpla_paper_normalize eqb r).

Theorem rewpla_merged_key_correct_M (r : rewpla A) :
  lang_equiv (rewpla_denote eqb (rewpla_merged_key r))
    (rewpla_denote eqb r).
Proof.
  unfold rewpla_merged_key. eapply lang_equiv_trans.
  - apply rewpla_positive_normalize_correct_M.
  - apply rewpla_paper_normalize_correct_M. exact eqb_spec.
Qed.

Theorem rewpla_merged_key_equal_sound_M (r s : rewpla A) :
  rewpla_merged_key r = rewpla_merged_key s ->
  lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s).
Proof.
  intro H. eapply lang_equiv_trans.
  - apply lang_equiv_sym, rewpla_merged_key_correct_M.
  - rewrite H. apply rewpla_merged_key_correct_M.
Qed.

Theorem rewpla_positive_state_equal_sound_M (r s : rewpla A) :
  r = s -> lang_equiv (rewpla_denote eqb r) (rewpla_denote eqb s).
Proof. intros ->. apply lang_equiv_refl. Qed.

Theorem rewpla_positive_state_equal_final (r s : rewpla A) :
  r = s -> rewpla_nullable r = rewpla_nullable s.
Proof. congruence. Qed.

Theorem rewpla_positive_state_equal_step a (r s : rewpla A) :
  r = s ->
  rewpla_positive_symbol_step eqb atom_code a r =
  rewpla_positive_symbol_step eqb atom_code a s.
Proof. congruence. Qed.

Theorem rewpla_positive_word_step_accept_correct
    (r : rewpla A) w :
  rewpla_nullable (rewpla_positive_word_step eqb atom_code w r) = true
    <-> rewpla_language eqb r w.
Proof.
  rewrite rewpla_nullable_correct by exact eqb_spec.
  pose proof (rewpla_positive_word_step_correct_M w r ([], [])) as Hword.
  pose proof (rewpla_paper_word_step_correct_M eqb atom_code eqb_spec
    w r ([], [])) as Hpaper.
  pose proof (rewpla_paper_word_step_accept_correct
    eqb atom_code eqb_spec r w) as Haccept.
  rewrite rewpla_nullable_correct in Haccept by exact eqb_spec.
  tauto.
Qed.

Theorem rewpla_positive_states_closedb_sound alphabet states :
  rewpla_positive_states_closedb eqb atom_code alphabet states = true ->
  forall q a, In q states -> In a alphabet ->
    In (rewpla_positive_symbol_step eqb atom_code a q) states.
Proof.
  unfold rewpla_positive_states_closedb. intros H q a Hq Ha.
  apply forallb_forall with (x := q) in H; [|exact Hq].
  apply forallb_forall with (x := a) in H; [|exact Ha].
  apply existsb_exists in H as [t [Ht Heq]].
  apply (proj1 (rewpla_eqb_spec eqb eqb_spec _ _)) in Heq.
  now subst t.
Qed.

Theorem rewpla_positive_states_closedb_all_words alphabet states :
  rewpla_positive_states_closedb eqb atom_code alphabet states = true ->
  forall (r : rewpla A) w, In r states ->
    (forall a, In a w -> In a alphabet) ->
    In (rewpla_positive_word_step eqb atom_code w r) states.
Proof.
  intros Hclosed r w. revert r.
  induction w as [|a w IH]; intros r Hr Hw; simpl.
  - exact Hr.
  - apply IH.
    + apply (rewpla_positive_states_closedb_sound alphabet states
        Hclosed r a Hr). apply Hw. now left.
    + intros b Hb. apply Hw. now right.
Qed.

Theorem rewpla_positive_saturated_dfa_accept_correct
    alphabet states (r : rewpla A) :
  rewpla_positive_states_closedb eqb atom_code alphabet states = true ->
  In r states ->
  forall w, (forall a, In a w -> In a alphabet) ->
    In (rewpla_positive_word_step eqb atom_code w r) states /\
    (rewpla_nullable (rewpla_positive_word_step eqb atom_code w r) = true
      <-> rewpla_language eqb r w).
Proof.
  intros Hclosed Hr w Hw. split.
  - eapply rewpla_positive_states_closedb_all_words; eauto.
  - apply rewpla_positive_word_step_accept_correct.
Qed.

End NormalizerCorrectness.

Print Assumptions rewpla_positive_normalize_congruent.
Print Assumptions rewpla_positive_equiv_sound.
Print Assumptions rewpla_positive_symbol_step_correct_M.
Print Assumptions rewpla_positive_word_step_correct_M.
Print Assumptions rewpla_merged_key_equal_sound_M.
Print Assumptions rewpla_positive_word_step_accept_correct.
Print Assumptions rewpla_positive_saturated_dfa_accept_correct.
