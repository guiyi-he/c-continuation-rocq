From Stdlib Require Import List Bool Arith Lia.
From CCont Require Import StringConstraints Syntax LookaheadSemantics
  ConstraintExpansion LookaheadDerivatives LowerBoundFamily
  TightLowerBoundFamily.
Import ListNotations.
Set Implicit Arguments.

(** * Executable automaton for the linear-width lower-bound family

    The generic positive-congruence normalizer distributes the body [U^k]
    of the periodic assertion.  This file instead records an assertion as an
    obligation on one of the [k] input phases.  Completed matches are kept as
    an antichain of obligation vectors: if [x] is included in [y], then [y]
    can never accept a continuation that [x] rejects. *)
Module TightAutomaton.

Definition bitvec := list bool.
Definition family := list bitvec.

Fixpoint bitvec_eqb (x y : bitvec) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => Bool.eqb a b && bitvec_eqb x' y'
  | _, _ => false
  end.

Lemma bitvec_eqb_spec x y : bitvec_eqb x y = true <-> x = y.
Proof.
  revert y. induction x as [|a x IH]; intros [|b y]; simpl.
  - tauto.
  - split; discriminate.
  - split; discriminate.
  - rewrite Bool.andb_true_iff, IH, Bool.eqb_true_iff.
    intuition congruence.
Qed.

Fixpoint bitvec_subsetb (x y : bitvec) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => (negb a || b) && bitvec_subsetb x' y'
  | _, _ => false
  end.

Definition bitvec_subset (x y : bitvec) : Prop :=
  length x = length y /\
  forall i, i < length x -> nth i x false = true -> nth i y false = true.

Lemma bitvec_subsetb_spec x y :
  bitvec_subsetb x y = true <-> bitvec_subset x y.
Proof.
  revert y. induction x as [|a x IH]; intros [|b y]; simpl.
  - unfold bitvec_subset. simpl. tauto.
  - unfold bitvec_subset. simpl. split; [discriminate|intros [H _]; discriminate].
  - unfold bitvec_subset. simpl. split; [discriminate|intros [H _]; discriminate].
  - rewrite Bool.andb_true_iff, IH. unfold bitvec_subset in *.
    split.
    + intros [Hab [Hlen Htail]]. split; [simpl; lia|].
      intros [|i] Hi Hbit; simpl in *.
      * destruct a, b; simpl in Hab, Hbit; try discriminate; reflexivity.
      * apply Htail; [lia|exact Hbit].
    + intros [Hlen Hall]. split.
      * destruct a, b; simpl; try reflexivity.
        specialize (Hall 0 ltac:(simpl; lia) eq_refl). discriminate.
      * split; [simpl in Hlen; lia|].
        intros i Hi Hbit. apply (Hall (S i)); simpl; [lia|exact Hbit].
Qed.

Lemma bitvec_subset_refl x : bitvec_subset x x.
Proof. split; [reflexivity|auto]. Qed.

Lemma bitvec_subset_trans x y z :
  bitvec_subset x y -> bitvec_subset y z -> bitvec_subset x z.
Proof.
  intros [Hxy Hx] [Hyz Hy]. split; [lia|].
  intros i Hi Hbit. apply Hy; [lia|]. apply Hx; assumption.
Qed.

Definition bitvec_strict_subsetb x y :=
  bitvec_subsetb x y && negb (bitvec_eqb x y).

Fixpoint bitvec_weight (x : bitvec) : nat :=
  match x with
  | [] => 0
  | b :: x' => (if b then 1 else 0) + bitvec_weight x'
  end.

Lemma bitvec_subset_weight_le x y :
  bitvec_subset x y -> bitvec_weight x <= bitvec_weight y.
Proof.
  revert y. induction x as [|a x IH]; intros [|b y] Hsub;
    unfold bitvec_subset in Hsub; simpl in *; try lia.
  destruct Hsub as [Hlen Hall].
  assert (Htail : bitvec_subset x y).
  { split; [lia|]. intros i Hi Hbit.
    apply (Hall (S i)); simpl; [lia|exact Hbit]. }
  specialize (IH y Htail). destruct a, b; simpl in *; try lia.
  specialize (Hall 0 ltac:(simpl; lia) eq_refl). discriminate.
Qed.

Lemma bitvec_subset_weight_eq x y :
  bitvec_subset x y -> bitvec_weight x = bitvec_weight y -> x = y.
Proof.
  revert y. induction x as [|a x IH]; intros [|b y] Hsub Hweight.
  - reflexivity.
  - unfold bitvec_subset in Hsub. destruct Hsub as [Hlen _].
    simpl in Hlen. discriminate.
  - unfold bitvec_subset in Hsub. destruct Hsub as [Hlen _].
    simpl in Hlen. discriminate.
  - unfold bitvec_subset in Hsub. simpl in Hsub, Hweight.
    destruct Hsub as [Hlen Hall].
    assert (Htail : bitvec_subset x y).
    { split; [lia|]. intros i Hi Hbit.
      apply (Hall (S i)); simpl; [lia|exact Hbit]. }
    destruct a, b; simpl in Hweight.
    + f_equal. apply IH; [exact Htail|lia].
    + specialize (Hall 0 ltac:(simpl; lia) eq_refl). discriminate.
    + assert (bitvec_weight x <= bitvec_weight y) by
          now apply bitvec_subset_weight_le.
      lia.
    + f_equal. apply IH; [exact Htail|lia].
Qed.

Lemma bitvec_strict_subsetb_weight x y :
  bitvec_strict_subsetb x y = true -> bitvec_weight x < bitvec_weight y.
Proof.
  unfold bitvec_strict_subsetb. rewrite Bool.andb_true_iff.
  intros [Hsub Hneq]. apply bitvec_subsetb_spec in Hsub.
  apply Bool.negb_true_iff in Hneq.
  pose proof (bitvec_subset_weight_le Hsub) as Hle.
  destruct (Nat.eq_dec (bitvec_weight x) (bitvec_weight y)) as [Heq|Hne];
    [|lia].
  apply bitvec_subset_weight_eq in Heq; [|exact Hsub]. subst y.
  rewrite (proj2 (bitvec_eqb_spec x x) eq_refl) in Hneq. discriminate.
Qed.

Fixpoint all_bitvecs (k : nat) : list bitvec :=
  match k with
  | 0 => [[]]
  | S k' =>
      map (cons false) (all_bitvecs k') ++
      map (cons true) (all_bitvecs k')
  end.

Lemma all_bitvecs_length_member k x :
  In x (all_bitvecs k) <-> length x = k.
Proof.
  revert x. induction k as [|k IH]; intros x; simpl.
  - split.
    + intros [H|H]; [now subst x|contradiction].
    + intro H. apply length_zero_iff_nil in H. now left.
  - rewrite in_app_iff. split.
    + intros [H|H]; apply in_map_iff in H as [y [<- Hy]];
        simpl; rewrite (proj1 (IH y) Hy); reflexivity.
    + intro Hlen. destruct x as [|b x]; [discriminate|].
      destruct b.
      * right. apply in_map_iff. exists x. split; [reflexivity|].
        apply IH. simpl in Hlen. lia.
      * left. apply in_map_iff. exists x. split; [reflexivity|].
        apply IH. simpl in Hlen. lia.
Qed.

Definition family_covers (f : family) (target : bitvec) : Prop :=
  exists obligations, In obligations f /\ bitvec_subset obligations target.

Definition family_normalize k (f : family) : family :=
  filter
    (fun obligations =>
      existsb (bitvec_eqb obligations) f &&
      negb (existsb
        (fun smaller => bitvec_strict_subsetb smaller obligations) f))
    (all_bitvecs k).

Lemma family_normalize_sound k f obligations :
  In obligations (family_normalize k f) -> In obligations f.
Proof.
  unfold family_normalize. intro H.
  apply filter_In in H as [_ Hkeep].
  apply Bool.andb_true_iff in Hkeep as [Hin _].
  apply existsb_exists in Hin as [same [Hsame Heq]].
  apply bitvec_eqb_spec in Heq. now subst same.
Qed.

Lemma family_normalize_complete k f obligations :
  (forall x, In x f -> length x = k) ->
  In obligations f ->
  exists minimal,
    In minimal (family_normalize k f) /\ bitvec_subset minimal obligations.
Proof.
  intros Hlength Hin.
  remember (bitvec_weight obligations) as fuel eqn:Hfuel.
  revert obligations Hfuel Hin.
  induction fuel using lt_wf_ind; intros obligations Hfuel Hin.
  destruct (existsb
      (fun smaller => bitvec_strict_subsetb smaller obligations) f) eqn:Hsmaller.
  - apply existsb_exists in Hsmaller as [smaller [Hsin Hstrict]].
    assert (Hmeasure : bitvec_weight smaller < fuel).
    { rewrite Hfuel. now apply bitvec_strict_subsetb_weight. }
    unfold bitvec_strict_subsetb in Hstrict.
    apply Bool.andb_true_iff in Hstrict as [Hsub _].
    apply bitvec_subsetb_spec in Hsub.
    destruct (H (bitvec_weight smaller) Hmeasure smaller eq_refl Hsin)
      as [minimal [Hmin Hminsub]].
    exists minimal. split; [exact Hmin|].
    eapply bitvec_subset_trans; eauto.
  - exists obligations. split.
    + unfold family_normalize. apply filter_In. split.
      * apply all_bitvecs_length_member. now apply Hlength.
      * apply Bool.andb_true_iff. split.
        -- apply existsb_exists. exists obligations. split; [exact Hin|].
           apply bitvec_eqb_spec. reflexivity.
        -- now apply Bool.negb_true_iff.
    + apply bitvec_subset_refl.
Qed.

Theorem family_normalize_covers k f target :
  (forall x, In x f -> length x = k) -> length target = k ->
  (family_covers (family_normalize k f) target <-> family_covers f target).
Proof.
  intros Hlength Htarget. split.
  - intros [x [Hx Hsub]]. exists x. split;
      [now apply family_normalize_sound in Hx|exact Hsub].
  - intros [x [Hx Hsub]].
    destruct (@family_normalize_complete k f x Hlength Hx)
      as [minimal [Hmin Hminsub]].
    exists minimal. split; [exact Hmin|].
    eapply bitvec_subset_trans; eauto.
Qed.

Fixpoint bitvec_update (i : nat) (value : bool) (x : bitvec) : bitvec :=
  match i, x with
  | 0, _ :: xs => value :: xs
  | S i', b :: xs => b :: bitvec_update i' value xs
  | _, [] => []
  end.

Definition bitvec_set i x := bitvec_update i true x.
Definition bitvec_clear i x := bitvec_update i false x.
Definition zero_bits k : bitvec := repeat false k.

Definition rotate_bits (x : bitvec) : bitvec :=
  match x with
  | [] => []
  | b :: x' => x' ++ [b]
  end.

Lemma bitvec_update_length i value x :
  length (bitvec_update i value x) = length x.
Proof.
  revert i. induction x as [|b x IH]; intros [|i]; simpl; auto.
Qed.

Definition family_add k obligations f :=
  family_normalize k (obligations :: f).

Definition family_clear k i f :=
  family_normalize k (map (bitvec_clear i) f).

Definition advance_obligations (symbol : tight_symbol) (x : bitvec) : bitvec :=
  rotate_bits
    (match symbol with
     | TLx => bitvec_clear 0 x
     | _ => x
     end).

Definition advance_family k symbol f :=
  family_normalize k (map (advance_obligations symbol) f).

Fixpoint process_obligations (x : bitvec) (w : list tight_symbol) : bitvec :=
  match w with
  | [] => x
  | a :: w' => process_obligations (advance_obligations a x) w'
  end.

Definition singleton_bits k i : bitvec :=
  map (fun j => Nat.eqb j i) (seq 0 k).

Definition phase_accept k i (w : list tight_symbol) : Prop :=
  exists pre tail,
    w = pre ++ TLx :: tail /\ length pre mod k = i.

Definition previous_phase k i :=
  if Nat.eqb i 0 then k - 1 else i - 1.

Fixpoint scan_bits (k : nat) (pending : bitvec)
    (bits : list tight_symbol) : bitvec :=
  match bits with
  | [] => pending
  | TLb :: bits' => scan_bits k (rotate_bits pending) bits'
  | TLc :: bits' =>
      scan_bits k (bitvec_set 0 (rotate_bits pending)) bits'
  | _ :: bits' => scan_bits k pending bits'
  end.

Lemma rotate_bits_length x : length (rotate_bits x) = length x.
Proof.
  destruct x as [|b x]; simpl; [reflexivity|].
  rewrite length_app. simpl. lia.
Qed.

Lemma bitvec_subset_cons a x b y :
  bitvec_subset (a :: x) (b :: y) <->
  (a = true -> b = true) /\ bitvec_subset x y.
Proof.
  unfold bitvec_subset. simpl. split.
  - intros [Hlen Hall]. split.
    + intro Ha. apply (Hall 0); simpl; [lia|exact Ha].
    + split; [lia|]. intros i Hi Hbit.
      apply (Hall (S i)); simpl; [lia|exact Hbit].
  - intros [Hhead [Hlen Hall]]. split; [simpl; lia|].
    intros [|i] Hi Hbit; simpl in *.
    + now apply Hhead.
    + apply Hall; [lia|exact Hbit].
Qed.

Lemma bitvec_subset_app x y x' y' :
  bitvec_subset x y -> bitvec_subset x' y' ->
  bitvec_subset (x ++ x') (y ++ y').
Proof.
  revert y. induction x as [|a x IH]; intros y Hxy Htail.
  - destruct y as [|b y].
    + simpl. exact Htail.
    + unfold bitvec_subset in Hxy. simpl in Hxy.
      destruct Hxy as [Hlen _]. discriminate.
  - destruct y as [|b y].
    + unfold bitvec_subset in Hxy. simpl in Hxy.
      destruct Hxy as [Hlen _]. discriminate.
    + apply bitvec_subset_cons in Hxy as [Hab Hxy]. simpl.
      apply bitvec_subset_cons. split; [exact Hab|].
      now apply IH with (y := y).
Qed.

Lemma bitvec_update_subset i value x y :
  bitvec_subset x y ->
  bitvec_subset (bitvec_update i value x) (bitvec_update i value y).
Proof.
  revert i y. induction x as [|a x IH]; intros i y Hsub.
  - destruct y as [|b y].
    + destruct i; simpl; apply bitvec_subset_refl.
    + unfold bitvec_subset in Hsub. simpl in Hsub.
      destruct Hsub as [Hlen _]. discriminate.
  - destruct y as [|b y].
    + unfold bitvec_subset in Hsub. simpl in Hsub.
      destruct Hsub as [Hlen _]. discriminate.
    + apply bitvec_subset_cons in Hsub as [Hab Htail].
      destruct i as [|i]; simpl.
      * apply bitvec_subset_cons. split; [tauto|exact Htail].
      * apply bitvec_subset_cons. split; [exact Hab|]. now apply IH.
Qed.

Lemma rotate_bits_subset x y :
  bitvec_subset x y -> bitvec_subset (rotate_bits x) (rotate_bits y).
Proof.
  intros Hsub. destruct x as [|a x], y as [|b y].
  - simpl. apply bitvec_subset_refl.
  - unfold bitvec_subset in Hsub. simpl in Hsub.
    destruct Hsub as [Hlen _]. discriminate.
  - unfold bitvec_subset in Hsub. simpl in Hsub.
    destruct Hsub as [Hlen _]. discriminate.
  - simpl. apply bitvec_subset_cons in Hsub as [Hab Htail].
    apply bitvec_subset_app; [exact Htail|].
    apply bitvec_subset_cons. split; [exact Hab|apply bitvec_subset_refl].
Qed.

Lemma advance_obligations_subset a x y :
  bitvec_subset x y ->
  bitvec_subset (advance_obligations a x) (advance_obligations a y).
Proof.
  intro Hsub. unfold advance_obligations. apply rotate_bits_subset.
  destruct a; try exact Hsub. now apply bitvec_update_subset.
Qed.

Lemma process_obligations_subset x y w :
  bitvec_subset x y ->
  bitvec_subset (process_obligations x w) (process_obligations y w).
Proof.
  revert x y. induction w as [|a w IH]; intros x y Hsub; simpl;
    [exact Hsub|].
  apply IH. now apply advance_obligations_subset.
Qed.

Lemma bitvec_subset_zero_eq k x :
  length x = k -> bitvec_subset x (zero_bits k) -> x = zero_bits k.
Proof.
  unfold zero_bits in *.
  revert x. induction k as [|k IH]; intros [|a x] Hlen Hsub;
    simpl in Hlen; try discriminate; [reflexivity|].
  simpl. apply bitvec_subset_cons in Hsub as [Ha Htail].
  destruct a; [specialize (Ha eq_refl); discriminate|].
  f_equal. apply IH; [lia|exact Htail].
Qed.

Lemma bitvec_update_app_left i value x y : i < length x ->
  bitvec_update i value (x ++ y) = bitvec_update i value x ++ y.
Proof.
  revert i. induction x as [|b x IH]; intros [|i] Hi; simpl in *;
    try lia; [reflexivity|]. now rewrite IH by lia.
Qed.

Lemma bitvec_update_app_at_end value x b y :
  bitvec_update (length x) value (x ++ b :: y) = x ++ value :: y.
Proof. induction x as [|a x IH]; simpl; [reflexivity|now rewrite IH]. Qed.

Lemma bitvec_update_same i value x : i < length x ->
  bitvec_update i value (bitvec_update i value x) =
  bitvec_update i value x.
Proof.
  revert i. induction x as [|b x IH]; intros [|i] Hi; simpl in *;
    try lia; [reflexivity|]. now rewrite IH by lia.
Qed.

Lemma bitvec_update_commute i j vi vj x : i <> j ->
  bitvec_update i vi (bitvec_update j vj x) =
  bitvec_update j vj (bitvec_update i vi x).
Proof.
  revert i j. induction x as [|b x IH]; intros [|i] [|j] Hneq;
    simpl; try contradiction; try reflexivity.
  now rewrite IH by lia.
Qed.

Lemma advance_set_obligation k a q i :
  2 <= k -> length q = k -> i < k ->
  advance_obligations a (bitvec_set i q) =
  if (tight_symbol_eqb a TLx && Nat.eqb i 0)%bool
  then advance_obligations a q
  else bitvec_set (previous_phase k i) (advance_obligations a q).
Proof.
  intros Hk Hlen Hi. unfold bitvec_set, advance_obligations.
  destruct q as [|b q]; [simpl in Hlen; lia|].
  destruct i as [|i].
  - simpl. destruct a; simpl; unfold previous_phase; simpl.
    all: try reflexivity;
      replace (k - 1) with (length q) by (simpl in Hlen; lia);
      symmetry; apply bitvec_update_app_at_end.
  - simpl in Hi. unfold previous_phase. simpl Nat.eqb.
    assert (Hiq : i < length q) by (simpl in Hlen; lia).
    destruct a; simpl;
      try (replace (i - 0) with i by lia);
      try (rewrite bitvec_update_app_left by lia; reflexivity).
Qed.

Lemma advance_obligations_length a x :
  length (advance_obligations a x) = length x.
Proof.
  unfold advance_obligations. rewrite rotate_bits_length.
  destruct a; try reflexivity. apply bitvec_update_length.
Qed.

Lemma process_obligations_length x w :
  length (process_obligations x w) = length x.
Proof.
  revert x. induction w as [|a w IH]; intro x; simpl; [reflexivity|].
  rewrite IH. apply advance_obligations_length.
Qed.

Lemma singleton_bits_length k i : length (singleton_bits k i) = k.
Proof. unfold singleton_bits. now rewrite length_map, length_seq. Qed.

Lemma zero_bits_length k : length (zero_bits k) = k.
Proof. apply repeat_length. Qed.

Lemma scan_bits_length k pending bits :
  length pending = k -> length (scan_bits k pending bits) = k.
Proof.
  revert pending. induction bits as [|a bits IH]; intros pending Hlen;
    simpl; [exact Hlen|].
  destruct a; apply IH.
  - exact Hlen.
  - now rewrite rotate_bits_length.
  - unfold bitvec_set. rewrite bitvec_update_length, rotate_bits_length.
    exact Hlen.
  - exact Hlen.
  - exact Hlen.
  - exact Hlen.
  - exact Hlen.
Qed.

Lemma successor_mod_previous k i n : 2 <= k -> i < k ->
  (S n mod k = i <-> n mod k = previous_phase k i).
Proof.
  intros Hk Hi. unfold previous_phase.
  replace (S n) with (n + 1) by lia.
  rewrite Nat.add_mod by lia.
  replace (1 mod k) with 1 by (symmetry; apply Nat.mod_small; lia).
  remember (n mod k) as r eqn:Hr.
  assert (Hrlt : r < k).
  { subst r. apply Nat.mod_upper_bound. lia. }
  destruct (Nat.eqb i 0) eqn:Hi0.
  - apply Nat.eqb_eq in Hi0. subst i.
    destruct (Nat.eq_dec r (k - 1)) as [->|Hne].
    + replace (k - 1 + 1) with k by lia.
      rewrite Nat.mod_same by lia. split; reflexivity.
    + rewrite Nat.mod_small by lia. split; intro H; lia.
  - apply Nat.eqb_neq in Hi0.
    destruct (Nat.eq_dec r (k - 1)) as [->|Hne].
    + replace (k - 1 + 1) with k by lia.
      rewrite Nat.mod_same by lia. split; intro H; lia.
    + rewrite Nat.mod_small by lia. split; intro H; lia.
Qed.

Lemma phase_accept_cons k i a w : 2 <= k -> i < k ->
  (phase_accept k i (a :: w) <->
   (i = 0 /\ a = TLx) \/ phase_accept k (previous_phase k i) w).
Proof.
  intros Hk Hi. unfold phase_accept. split.
  - intros [pre [tail [Heq Hmod]]]. destruct pre as [|p pre].
    + simpl in Heq, Hmod. inversion Heq; subst a w.
      rewrite Nat.mod_small in Hmod by lia.
      left. split; [now symmetry|reflexivity].
    + simpl in Heq. inversion Heq; subst p w. right.
      exists pre, tail. split; [reflexivity|].
      apply (proj1 (@successor_mod_previous k i (length pre) Hk Hi)).
      exact Hmod.
  - intros [[-> ->]|[pre [tail [Heq Hmod]]]].
    + exists [], w. simpl. split; [reflexivity|].
      apply Nat.mod_small. lia.
    + exists (a :: pre), tail. simpl. split.
      * now rewrite Heq.
      * apply (proj2 (@successor_mod_previous k i (length pre) Hk Hi)).
        exact Hmod.
Qed.

Lemma previous_phase_bound k i : 2 <= k -> i < k ->
  previous_phase k i < k.
Proof.
  intros Hk Hi. unfold previous_phase.
  destruct (Nat.eqb i 0) eqn:Hi0.
  - apply Nat.eqb_eq in Hi0. subst i. lia.
  - apply Nat.eqb_neq in Hi0. lia.
Qed.

Lemma rotate_zero_bits k : rotate_bits (zero_bits k) = zero_bits k.
Proof.
  destruct k as [|k].
  - reflexivity.
  - unfold zero_bits, rotate_bits. simpl.
    induction k as [|k IH].
    + reflexivity.
    + simpl in *. now rewrite IH.
Qed.

Lemma advance_zero_bits k a :
  advance_obligations a (zero_bits k) = zero_bits k.
Proof.
  unfold advance_obligations. destruct a; try apply rotate_zero_bits.
  destruct k as [|k]; [reflexivity|].
  change (rotate_bits (zero_bits (S k)) = zero_bits (S k)).
  apply rotate_zero_bits.
Qed.

Lemma process_zero_bits k w :
  process_obligations (zero_bits k) w = zero_bits k.
Proof.
  induction w as [|a w IH]; [reflexivity|]. simpl.
  now rewrite advance_zero_bits.
Qed.

Lemma bitvec_set_zero_nonzero k i : i < k ->
  bitvec_set i (zero_bits k) <> zero_bits k.
Proof.
  revert i. induction k as [|k IH]; intros [|i] Hi; try lia.
  - unfold bitvec_set, zero_bits. simpl. discriminate.
  - unfold bitvec_set, zero_bits. simpl.
    intro Heq. inversion Heq. now apply (IH i ltac:(lia)).
Qed.

Lemma bitvec_set_nonzero k q i : length q = k -> i < k ->
  bitvec_set i q <> zero_bits k.
Proof.
  revert q i. induction k as [|k IH]; intros q i Hlen Hi.
  - lia.
  - destruct q as [|b q]; [discriminate|]. destruct i as [|i].
    + unfold bitvec_set, zero_bits. simpl. discriminate.
    + unfold bitvec_set, zero_bits. simpl.
      intro Heq. inversion Heq as [[Htail]].
      apply (IH q i); [simpl in Hlen; lia|lia|exact H].
Qed.

Lemma process_set_obligation k q i w :
  2 <= k -> length q = k -> i < k ->
  (process_obligations (bitvec_set i q) w = zero_bits k <->
   process_obligations q w = zero_bits k /\ phase_accept k i w).
Proof.
  intros Hk. revert q i. induction w as [|a w IH]; intros q i Hlen Hi.
  - simpl. split.
    + intro Hset. exfalso.
      now apply (@bitvec_set_nonzero k q i Hlen Hi).
    + intros [_ Hphase]. unfold phase_accept in Hphase.
      destruct Hphase as [pre [tail [Heq _]]]. destruct pre; discriminate.
  - simpl process_obligations.
    rewrite (@advance_set_obligation k a q i Hk Hlen Hi).
    rewrite (@phase_accept_cons k i a w Hk Hi).
    destruct (tight_symbol_eqb a TLx && Nat.eqb i 0)%bool eqn:Hdone.
    + apply Bool.andb_true_iff in Hdone as [Ha Hi0].
      apply tight_symbol_eqb_spec in Ha. apply Nat.eqb_eq in Hi0.
      subst a i. simpl. tauto.
    + apply Bool.andb_false_iff in Hdone.
      rewrite IH.
      * assert (Himmediate : ~ (i = 0 /\ a = TLx)).
        { intros [-> ->]. destruct Hdone as [Hdone|Hdone]; simpl in Hdone;
            discriminate. }
        tauto.
      * now rewrite advance_obligations_length.
      * now apply previous_phase_bound.
Qed.

Lemma phase_accept_zero_tight k core : 0 < k -> tight_core_word core ->
  (phase_accept k 0 core <-> tight_phase_hit k (core ++ [TLhash])).
Proof.
  intros Hk Hcore. unfold phase_accept, tight_phase_hit. split.
  - intros [pre [tail [Hcoreeq Hmod]]].
    apply (proj1 (Nat.mod_divides (length pre) k ltac:(lia))) in Hmod.
    destruct Hmod as [n Hlen].
    exists n, pre, (tail ++ [TLhash]). repeat split.
    + rewrite Nat.mul_comm. exact Hlen.
    + rewrite Hcoreeq in Hcore.
      now apply (proj1 (tight_core_word_app _ _)) in Hcore.
    + rewrite Hcoreeq. rewrite <- app_assoc. reflexivity.
  - intros [n [pre [tail [Hlen [Hpre Heq]]]]].
    assert (Hat : tight_at (length pre) (core ++ [TLhash]) = Some TLx).
    { rewrite Heq. apply tight_at_of_split. }
    assert (Hbound : length pre < length core + 1).
    { pose proof (@tight_at_some_bound tight_symbol (length pre)
                    (core ++ [TLhash]) TLx Hat) as H.
      rewrite length_app in H. simpl in H.
      lia. }
    assert (Hstrict : length pre < length core).
    { destruct (Nat.eq_dec (length pre) (length core)) as [Heqlen|Hne].
      - rewrite Heqlen in Hat.
        replace (length core) with (length core + 0) in Hat by lia.
        rewrite tight_at_app_right in Hat. simpl in Hat. discriminate.
      - lia. }
    rewrite tight_at_app_left in Hat by exact Hstrict.
    destruct (@tight_at_split tight_symbol (length pre) core TLx Hat)
      as [before [after [Hsplit Hbefore]]].
    exists before, after. split; [exact Hsplit|].
    apply (proj2 (Nat.mod_divides (length before) k ltac:(lia))).
    exists n. rewrite Hbefore, Hlen. now rewrite Nat.mul_comm.
Qed.

Definition tight_bit_word (w : list tight_symbol) : Prop :=
  Forall (fun a => a = TLb \/ a = TLc) w.

Lemma tight_bit_word_core w : tight_bit_word w -> tight_core_word w.
Proof.
  unfold tight_bit_word, tight_core_word.
  apply Forall_impl. intros a Ha. destruct Ha as [Ha|Ha]; subst a;
    [apply tight_core_b|apply tight_core_c].
Qed.

Lemma scan_process_characterization k pending bits future :
  2 <= k -> length pending = k -> tight_bit_word bits ->
  tight_core_word future ->
  (process_obligations (scan_bits k pending bits) future = zero_bits k <->
   process_obligations pending (bits ++ future) = zero_bits k /\
   tight_bits_accept k bits (future ++ [TLhash])).
Proof.
  intros Hk. revert pending future.
  induction bits as [|a bits IH]; intros pending future Hlen Hbits Hfuture.
  - simpl. tauto.
  - inversion Hbits as [|a' bits' Ha Hbits']; subst a' bits'.
    destruct Ha as [Ha|Ha].
    + subst a. simpl scan_bits. simpl tight_bits_accept.
      rewrite (@IH (rotate_bits pending) future).
      * unfold advance_obligations. simpl. tauto.
      * now rewrite rotate_bits_length.
      * exact Hbits'.
      * exact Hfuture.
    + subst a. simpl scan_bits. simpl tight_bits_accept.
      rewrite (@IH (bitvec_set 0 (rotate_bits pending)) future).
      * rewrite (@process_set_obligation k (rotate_bits pending) 0
          (bits ++ future) Hk).
        -- rewrite (@phase_accept_zero_tight k (bits ++ future)); [|lia|].
           ++ replace ((bits ++ future) ++ [TLhash]) with
                (bits ++ future ++ [TLhash]) by
                (rewrite app_assoc; reflexivity).
              replace (advance_obligations TLc pending) with
                (rotate_bits pending) by reflexivity.
              intuition congruence.
           ++ apply (proj2 (tight_core_word_app _ _)). split;
                [now apply tight_bit_word_core|exact Hfuture].
        -- now rewrite rotate_bits_length.
        -- lia.
      * unfold bitvec_set. rewrite bitvec_update_length, rotate_bits_length.
        exact Hlen.
      * exact Hbits'.
      * exact Hfuture.
Qed.

Corollary scan_bits_accept_characterization k bits future :
  2 <= k -> tight_bit_word bits -> tight_core_word future ->
  (process_obligations (scan_bits k (zero_bits k) bits) future = zero_bits k
   <-> tight_bits_accept k bits (future ++ [TLhash])).
Proof.
  intros Hk Hbits Hfuture.
  rewrite (@scan_process_characterization k (zero_bits k) bits future Hk
    (zero_bits_length k) Hbits Hfuture).
  rewrite process_zero_bits. tauto.
Qed.

Lemma tight_bits_accept_bit_word k bits suffix :
  tight_bits_accept k bits suffix -> tight_bit_word bits.
Proof.
  induction bits as [|a bits IH]; simpl; intro Haccept.
  - constructor.
  - destruct Haccept as [[Ha|[Ha _]] Hrest]; subst a; constructor.
    + now left.
    + now apply IH.
    + now right.
    + now apply IH.
Qed.

(** Residual constraints created by the tight assertion contain only core
    letters.  This invariant is what makes the final [#] a genuine end marker
    also for the projected language [L_pi]. *)
Lemma tight_core_word_residual v u :
  tight_core_word v -> tight_core_word (residual tight_symbol_eqb v u).
Proof.
  intro Hv. unfold residual.
  destruct (left_quotient tight_symbol_eqb u v) as [z|] eqn:Hquot.
  - apply (@left_quotient_spec tight_symbol tight_symbol_eqb
      tight_symbol_eqb_spec u v z) in Hquot. subst v.
    apply (proj1 (tight_core_word_app _ _)) in Hv. exact (proj2 Hv).
  - constructor.
Qed.

Lemma tight_core_word_join u v t :
  tight_core_word u -> tight_core_word v ->
  join tight_symbol_eqb u v = Some t -> tight_core_word t.
Proof.
  intros Hu Hv Hjoin. apply (@join_result tight_symbol tight_symbol_eqb
    tight_symbol_eqb_spec u v t) in Hjoin.
  destruct Hjoin as [[_ ->]|[_ ->]]; assumption.
Qed.

Lemma constraint_concat_residual_core u v u' v' out :
  tight_core_word v -> tight_core_word v' ->
  constraint_concat tight_symbol_eqb (u,v) (u',v') = Some out ->
  tight_core_word (snd out).
Proof.
  intros Hv Hv' Hconcat. unfold constraint_concat in Hconcat. simpl in Hconcat.
  destruct (join tight_symbol_eqb v (u' ++ v')) as [outer|] eqn:Houter;
    [|discriminate].
  destruct (join tight_symbol_eqb (residual tight_symbol_eqb v u') v')
    as [result|] eqn:Hresult; [|discriminate].
  inversion Hconcat; subst out. simpl.
  eapply tight_core_word_join;
    [exact (@tight_core_word_residual v u' Hv)|exact Hv'|].
  exact Hresult.
Qed.

Fixpoint core_lookaheads (r : rewpla tight_symbol) : Prop :=
  match r with
  | WZero | WEps | WAtom _ => True
  | WPlus p q | WConcat p q => core_lookaheads p /\ core_lookaheads q
  | WStar p => core_lookaheads p
  | WLookahead p => forall u v,
      rewpla_denote tight_symbol_eqb p (u,v) -> tight_core_word (u ++ v)
  end.

Lemma core_lookaheads_residual_core r u v :
  core_lookaheads r -> rewpla_denote tight_symbol_eqb r (u,v) ->
  tight_core_word v.
Proof.
  revert u v. induction r; intros u v Hcore Hden; simpl in Hcore, Hden.
  - contradiction.
  - inversion Hden. constructor.
  - inversion Hden. constructor.
  - destruct Hcore as [Hr Hs]. destruct Hden as [Hden|Hden].
    + now apply IHr1 with (u := u).
    + now apply IHr2 with (u := u).
  - destruct Hcore as [Hr Hs].
    destruct Hden as [[ur vr] [[us vs] [Hleft [Hright Hconcat]]]].
    exact (@constraint_concat_residual_core ur vr us vs (u,v)
      (IHr1 ur vr Hr Hleft) (IHr2 us vs Hs Hright) Hconcat).
  - destruct Hden as [n Hpower]. revert u v Hpower.
    induction n as [|n IH]; intros u v Hpower; simpl in Hpower.
    + inversion Hpower. constructor.
    + destruct Hpower as [[up vp] [[uq vq] [Hp [Hq Hconcat]]]].
      exact (@constraint_concat_residual_core up vp uq vq (u,v)
        (IH up vp Hp) (IHr uq vq Hcore Hq) Hconcat).
  - destruct Hden as [[up vp] [Hp Heq]]. inversion Heq; subst u v.
    unfold constraint_projection. simpl. now apply Hcore.
Qed.

Lemma matches_tight_phase_core k w :
  0 < k -> matches (tight_phase_regex k) w -> tight_core_word w.
Proof.
  intros Hk Hmatch. unfold tight_phase_regex in Hmatch.
  inversion Hmatch; subst.
  match goal with
  | Hstar : matches (Star (tight_period_regex k)) ?pre,
    Hx : matches (Atom TLx) ?last |- _ =>
      apply (proj1 (matches_tight_period_star (k := k) pre Hk)) in Hstar
        as [Hpre _]; inversion Hx; subst last
  end.
  apply (proj2 (tight_core_word_app _ _)). split; [exact Hpre|].
  constructor; [apply tight_core_x|constructor].
Qed.

Lemma tight_factor_core_lookaheads k : 0 < k ->
  core_lookaheads (tight_factor k).
Proof.
  intro Hk. unfold tight_factor, tight_assertion. simpl.
  repeat split; try exact I.
  intros u v Hden.
  change (rewpla_denote tight_symbol_eqb
    (embed_regex (tight_phase_regex k)) (u,v)) in Hden.
  apply (proj1 (embed_regex_semantics tight_symbol_eqb
    tight_symbol_eqb_spec _ (u,v))) in Hden.
  destruct Hden as [w [Hpair Hmatch]]. inversion Hpair; subst u v.
  simpl. rewrite app_nil_r. exact (@matches_tight_phase_core k w Hk Hmatch).
Qed.

Lemma concat_empty_left_residual u u' v' out :
  constraint_concat tight_symbol_eqb (u,[]) (u',v') = Some out ->
  snd out = v'.
Proof.
  destruct u'; simpl; intro H; inversion H; reflexivity.
Qed.

Lemma tight_core_prefix_before_hash v core tail :
  tight_core_word v -> tight_core_word core ->
  word_prefix v (core ++ [TLhash] ++ tail) -> word_prefix v core.
Proof.
  revert v. induction core as [|a core IH]; intros [|b v] Hv Hcore Hprefix.
  - apply word_prefix_nil.
  - inversion Hv as [|? ? Hb _]; subst.
    destruct Hprefix as [z Hz]. simpl in Hz. inversion Hz; subst b.
    now apply tight_core_not_hash in Hb.
  - apply word_prefix_nil.
  - inversion Hv as [|? ? Hb Hv']; subst.
    inversion Hcore as [|? ? Ha Hcore']; subst.
    destruct Hprefix as [z Hz]. simpl in Hz. inversion Hz; subst b.
    destruct (@IH v Hv' Hcore') as [rest Hrest].
    { exists z. exact H1. }
    exists rest. simpl. now f_equal.
Qed.

Lemma concat_core_before_hash_empty u v core out :
  tight_core_word v -> tight_core_word core ->
  constraint_concat tight_symbol_eqb (u,v) (core ++ [TLhash],[]) = Some out ->
  snd out = [].
Proof.
  intros Hv Hcore Hconcat.
  destruct (@constraint_concat_result_shape tight_symbol tight_symbol_eqb
    u v (core ++ [TLhash]) [] out Hconcat) as [t Hshape].
  subst out. simpl.
  pose proof (@constraint_concat_preservation tight_symbol tight_symbol_eqb
    tight_symbol_eqb_spec u v (core ++ [TLhash]) [] t Hconcat) as [Hprefix _].
  assert (Hvcore : word_prefix v core).
  { apply (@tight_core_prefix_before_hash v core t Hv Hcore).
    now rewrite app_assoc. }
  assert (Hvfull : word_prefix v (core ++ [TLhash])).
  { eapply word_prefix_trans; [exact Hvcore|]. exists [TLhash]. reflexivity. }
  unfold constraint_concat in Hconcat. simpl in Hconcat.
  rewrite (residual_consumed tight_symbol_eqb tight_symbol_eqb_spec Hvfull)
    in Hconcat.
  rewrite app_nil_r in Hconcat.
  destruct (join tight_symbol_eqb v (core ++ [TLhash])) eqn:Hjoin;
    inversion Hconcat; reflexivity.
Qed.

Lemma embed_denote_residual_nil (r : regex tight_symbol) u v :
  rewpla_denote tight_symbol_eqb (embed_regex r) (u,v) ->
  v = [] /\ matches r u.
Proof.
  intro Hden. apply (proj1 (embed_regex_semantics tight_symbol_eqb
    tight_symbol_eqb_spec r (u,v))) in Hden.
  destruct Hden as [w [Hpair Hmatch]]. inversion Hpair; now subst.
Qed.

Lemma tight_tail_denote_shape u v :
  rewpla_denote tight_symbol_eqb
    (WConcat (WAtom TLd)
      (WConcat (embed_regex (Star tight_core_regex)) (WAtom TLhash)))
    (u,v) ->
  exists core, u = [TLd] ++ core ++ [TLhash] /\
    tight_core_word core /\ v = [].
Proof.
  simpl. intros [[ud vd] [[ur vr] [Hd [Hrest Houter]]]].
  inversion Hd; subst ud vd.
  destruct Hrest as [[uc vc] [[uh vh] [Hcore [Hhash Hinner]]]].
  inversion Hhash; subst uh vh.
  change (rewpla_denote tight_symbol_eqb
    (embed_regex (Star tight_core_regex)) (uc,vc)) in Hcore.
  apply embed_denote_residual_nil in Hcore as [-> Hmatch].
  apply matches_tight_core_star in Hmatch.
  destruct (@constraint_concat_result_shape tight_symbol tight_symbol_eqb
    uc [] [TLhash] [] (ur,vr) Hinner) as [t Hshape].
  inversion Hshape; subst ur vr.
  pose proof (@concat_empty_left_residual uc [TLhash] []
    (uc ++ [TLhash], t) Hinner) as Ht. simpl in Ht. subst t.
  destruct (@constraint_concat_result_shape tight_symbol tight_symbol_eqb
    [TLd] [] (uc ++ [TLhash]) [] (u,v) Houter) as [t Hshape2].
  inversion Hshape2; subst u v.
  pose proof (@concat_empty_left_residual [TLd] (uc ++ [TLhash]) []
    ([TLd] ++ uc ++ [TLhash], t) Houter) as Ht2. simpl in Ht2. subst t.
  exists uc. repeat split; assumption || reflexivity.
Qed.

Theorem tight_expression_denote_residual_nil k u v :
  0 < k -> rewpla_denote tight_symbol_eqb (tight_expression k) (u,v) ->
  v = [].
Proof.
  intros Hk Hden. unfold tight_expression in Hden. simpl in Hden.
  destruct Hden as [[u0 v0] [[ur0 vr0] [H0 [Hr0 Hcat0]]]].
  change (rewpla_denote tight_symbol_eqb
    (embed_regex (Star tight_core_regex)) (u0,v0)) in H0.
  assert (Hv0 : v0 = []) by now apply embed_denote_residual_nil in H0.
  subst v0.
  destruct Hr0 as [[ua va] [[ur1 vr1] [Ha [Hr1 Hcat1]]]].
  inversion Ha; subst ua va.
  destruct Hr1 as [[ue ve] [[ur2 vr2] [He [Hr2 Hcat2]]]].
  change (rewpla_denote tight_symbol_eqb
    (embed_regex (Star (Atom TLe))) (ue,ve)) in He.
  assert (Hve : ve = []) by now apply embed_denote_residual_nil in He.
  subst ve.
  destruct Hr2 as [[ubits vbits] [[utail vtail]
    [Hbits [Htail Hcat3]]]].
  change (rewpla_denote tight_symbol_eqb
    (WStar (tight_factor k)) (ubits,vbits)) in Hbits.
  change (rewpla_denote tight_symbol_eqb
    (WConcat (WAtom TLd)
      (WConcat (embed_regex (Star tight_core_regex)) (WAtom TLhash)))
    (utail,vtail)) in Htail.
  assert (Hvbits : tight_core_word vbits).
  { eapply core_lookaheads_residual_core; [simpl|exact Hbits].
    now apply tight_factor_core_lookaheads. }
  destruct (tight_tail_denote_shape Htail) as
    [core [Hutail [Hcore ->]]].
  subst utail.
  assert (Hcoretail : tight_core_word ([TLd] ++ core)).
  { apply (proj2 (tight_core_word_app _ _)). split.
    - constructor; [apply tight_core_d|constructor].
    - exact Hcore. }
  assert (Hvr2 : vr2 = []).
  { replace ([TLd] ++ core ++ [TLhash])
      with (([TLd] ++ core) ++ [TLhash]) in Hcat3 by now rewrite app_assoc.
    pose proof (@concat_core_before_hash_empty ubits vbits
      ([TLd] ++ core) (ur2,vr2) Hvbits Hcoretail Hcat3) as Hempty.
    simpl in Hempty. exact Hempty. }
  subst vr2.
  assert (Hvr1 : vr1 = []).
  { pose proof (@concat_empty_left_residual ue ur2 [] (ur1,vr1) Hcat2).
    simpl in H. exact H. }
  subst vr1.
  assert (Hvr0 : vr0 = []).
  { pose proof (@concat_empty_left_residual [TLa] ur1 [] (ur0,vr0) Hcat1).
    simpl in H. exact H. }
  subst vr0.
  pose proof (@concat_empty_left_residual u0 ur0 [] (u,v) Hcat0) as Hfinal.
  simpl in Hfinal. exact Hfinal.
Qed.

Lemma snoc_injective {A : Type} (u v : list A) a b :
  u ++ [a] = v ++ [b] -> u = v /\ a = b.
Proof.
  intro H. apply (f_equal (@rev A)) in H. rewrite !rev_app_distr in H.
  simpl in H. inversion H as [[Hab Hrev]]. split.
  - apply (f_equal (@rev A)) in Hrev. now rewrite !rev_involutive in Hrev.
  - congruence.
Qed.

(** Prefix-side parser relations.  They are deliberately phrased with
    snoc constructors, so each transition of the executable scanner has a
    matching logical constructor. *)
Inductive padding_candidate : list tight_symbol -> Prop :=
| PaddingStart pre : tight_core_word pre ->
    padding_candidate (pre ++ [TLa])
| PaddingExtend w : padding_candidate w ->
    padding_candidate (w ++ [TLe]).

Inductive bits_candidate (k : nat) : list tight_symbol -> bitvec -> Prop :=
| BitsStartB w : padding_candidate w ->
    bits_candidate k (w ++ [TLb]) (zero_bits k)
| BitsStartC w : padding_candidate w ->
    bits_candidate k (w ++ [TLc]) (bitvec_set 0 (zero_bits k))
| BitsExtendB w obligations : bits_candidate k w obligations ->
    bits_candidate k (w ++ [TLb]) (rotate_bits obligations)
| BitsExtendC w obligations : bits_candidate k w obligations ->
    bits_candidate k (w ++ [TLc])
      (bitvec_set 0 (rotate_bits obligations)).

Inductive completed_candidate (k : nat) : list tight_symbol -> bitvec -> Prop :=
| CompletePadding w : padding_candidate w ->
    completed_candidate k (w ++ [TLd]) (zero_bits k)
| CompleteBits w obligations : bits_candidate k w obligations ->
    completed_candidate k (w ++ [TLd]) (rotate_bits obligations)
| CompleteExtend w obligations a : completed_candidate k w obligations ->
    tight_core_symbol a ->
    completed_candidate k (w ++ [a]) (advance_obligations a obligations).

Lemma padding_candidate_snoc w a :
  padding_candidate (w ++ [a]) <->
  (a = TLa /\ tight_core_word w) \/
  (a = TLe /\ padding_candidate w).
Proof.
  split.
  - intro H. inversion H; subst.
    + destruct (snoc_injective _ _ _ _ H0) as [-> Ha].
      left. split; [now symmetry|assumption].
    + destruct (snoc_injective _ _ _ _ H0) as [-> Ha].
      right. split; [now symmetry|assumption].
  - intros [[-> Hcore]|[-> Hpad]].
    + now apply PaddingStart.
    + now apply PaddingExtend.
Qed.

Lemma bits_candidate_snoc k w a q :
  bits_candidate k (w ++ [a]) q <->
  (a = TLb /\
    ((padding_candidate w /\ q = zero_bits k) \/
     exists old, bits_candidate k w old /\ q = rotate_bits old)) \/
  (a = TLc /\
    ((padding_candidate w /\ q = bitvec_set 0 (zero_bits k)) \/
     exists old, bits_candidate k w old /\
       q = bitvec_set 0 (rotate_bits old))).
Proof.
  split.
  - intro H. inversion H; subst.
    + destruct (snoc_injective _ _ _ _ H0) as [-> Ha].
      left. split; [now symmetry|now left].
    + destruct (snoc_injective _ _ _ _ H0) as [-> Ha].
      right. split; [now symmetry|now left].
    + destruct (snoc_injective _ _ _ _ H0) as [-> Ha].
      left. split; [now symmetry|right]. eauto.
    + destruct (snoc_injective _ _ _ _ H0) as [-> Ha].
      right. split; [now symmetry|right]. eauto.
  - intros [[-> [[Hpad ->]|[old [Hold ->]]]]|
            [-> [[Hpad ->]|[old [Hold ->]]]]].
    + now apply BitsStartB.
    + now apply BitsExtendB.
    + now apply BitsStartC.
    + now apply BitsExtendC.
Qed.

Lemma completed_candidate_snoc k w a q :
  completed_candidate k (w ++ [a]) q <->
  (a = TLd /\
    ((padding_candidate w /\ q = zero_bits k) \/
     exists old, bits_candidate k w old /\ q = rotate_bits old)) \/
  (tight_core_symbol a /\
    exists old, completed_candidate k w old /\
      q = advance_obligations a old).
Proof.
  split.
  - intro H. inversion H; subst.
    + destruct (snoc_injective _ _ _ _ H0) as [-> Ha].
      left. split; [now symmetry|now left].
    + destruct (snoc_injective _ _ _ _ H0) as [-> Ha].
      left. split; [now symmetry|right]. eauto.
    + destruct (snoc_injective _ _ _ _ H0) as [-> Ha].
      right. split; [now rewrite <- Ha|]. exists obligations.
      split; [assumption|now subst a].
  - intros [[-> [[Hpad ->]|[old [Hold ->]]]]|
            [Hcore [old [Hold ->]]]].
    + now apply CompletePadding.
    + now apply CompleteBits.
    + now apply CompleteExtend.
Qed.

Lemma bits_candidate_length k w q :
  bits_candidate k w q -> length q = k.
Proof.
  intro H. induction H; try apply zero_bits_length.
  - unfold bitvec_set. now rewrite bitvec_update_length, zero_bits_length.
  - now rewrite rotate_bits_length.
  - unfold bitvec_set. now rewrite bitvec_update_length, rotate_bits_length.
Qed.

Lemma completed_candidate_length k w q :
  completed_candidate k w q -> length q = k.
Proof.
  intro H. induction H.
  - apply zero_bits_length.
  - rewrite rotate_bits_length. now apply bits_candidate_length in H.
  - rewrite advance_obligations_length. exact IHcompleted_candidate.
Qed.

Lemma tight_core_word_snoc w a :
  tight_core_word w -> tight_core_symbol a -> tight_core_word (w ++ [a]).
Proof.
  intros Hw Ha. apply (proj2 (tight_core_word_app _ _)). split; [exact Hw|].
  constructor; [exact Ha|constructor].
Qed.

Lemma padding_candidate_core w : padding_candidate w -> tight_core_word w.
Proof.
  intro H. induction H.
  - apply tight_core_word_snoc; [exact H|apply tight_core_a].
  - apply tight_core_word_snoc; [exact IHpadding_candidate|apply tight_core_e].
Qed.

Lemma bits_candidate_core k w q : bits_candidate k w q -> tight_core_word w.
Proof.
  intro H. induction H; apply tight_core_word_snoc.
  - now apply padding_candidate_core.
  - apply tight_core_b.
  - now apply padding_candidate_core.
  - apply tight_core_c.
  - exact IHbits_candidate.
  - apply tight_core_b.
  - exact IHbits_candidate.
  - apply tight_core_c.
Qed.

Lemma completed_candidate_core k w q :
  completed_candidate k w q -> tight_core_word w.
Proof.
  intro H. induction H; apply tight_core_word_snoc.
  - now apply padding_candidate_core.
  - apply tight_core_d.
  - now apply bits_candidate_core in H.
  - apply tight_core_d.
  - exact IHcompleted_candidate.
  - exact H0.
Qed.

Inductive partial_state : Type :=
| PartialNone
| PartialPadding
| PartialBits (obligations : bitvec).

Definition partial_step k (partial : partial_state) symbol : partial_state :=
  match symbol with
  | TLa => PartialPadding
  | TLe =>
      match partial with PartialPadding => PartialPadding | _ => PartialNone end
  | TLb =>
      match partial with
      | PartialPadding => PartialBits (zero_bits k)
      | PartialBits obligations => PartialBits (rotate_bits obligations)
      | PartialNone => PartialNone
      end
  | TLc =>
      match partial with
      | PartialPadding => PartialBits (bitvec_set 0 (zero_bits k))
      | PartialBits obligations =>
          PartialBits (bitvec_set 0 (rotate_bits obligations))
      | PartialNone => PartialNone
      end
  | TLd | TLx | TLhash => PartialNone
  end.

Definition completion_obligation k (partial : partial_state) : option bitvec :=
  match partial with
  | PartialPadding => Some (zero_bits k)
  | PartialBits obligations => Some (rotate_bits obligations)
  | PartialNone => None
  end.

Definition completed_step k partial completed symbol : family :=
  match symbol with
  | TLd =>
      match completion_obligation k partial with
      | Some obligations =>
          family_add k obligations (advance_family k TLd completed)
      | None => advance_family k TLd completed
      end
  | _ => advance_family k symbol completed
  end.

Definition partial_rep k w (partial : partial_state) : Prop :=
  (partial = PartialPadding <-> padding_candidate w) /\
  forall q, (partial = PartialBits q <-> bits_candidate k w q).

Lemma partial_step_correct k w partial a :
  partial_rep k w partial -> tight_core_word w -> tight_core_symbol a ->
  partial_rep k (w ++ [a]) (partial_step k partial a).
Proof.
  intros [Hpad Hbits] Hcore Ha. unfold partial_rep, partial_step.
  rewrite padding_candidate_snoc.
  destruct a, partial; simpl in *; try contradiction;
    split; try (intuition congruence).
  all: intro q; rewrite bits_candidate_snoc; simpl;
    try (intuition congruence).
  - split; [discriminate|].
    intros [[_ [[Hp _]|[old [Hb _]]]]|[Hbad _]].
    + apply (proj2 Hpad) in Hp. discriminate.
    + apply (proj2 (Hbits old)) in Hb. discriminate.
    + discriminate.
  - split.
    + intro Heq. inversion Heq; subst q. left. split; [reflexivity|].
      left. split; [apply (proj1 Hpad); reflexivity|reflexivity].
    + intros [[_ [[_ ->]|[old [Hb _]]]]|[Hbad _]].
      * reflexivity.
      * apply (proj2 (Hbits old)) in Hb. discriminate.
      * discriminate.
  - split.
    + intro Heq. inversion Heq; subst q. left. split; [reflexivity|right].
      exists obligations. split; [apply (proj1 (Hbits obligations)); reflexivity|].
      reflexivity.
    + intros [[_ [[Hp _]|[old [Hb ->]]]]|[Hbad _]].
      * apply (proj2 Hpad) in Hp. discriminate.
      * apply (proj2 (Hbits old)) in Hb. inversion Hb. reflexivity.
      * discriminate.
  - split; [discriminate|].
    intros [[Hbad _]|[_ [[Hp _]|[old [Hb _]]]]].
    + discriminate.
    + apply (proj2 Hpad) in Hp. discriminate.
    + apply (proj2 (Hbits old)) in Hb. discriminate.
  - split.
    + intro Heq. inversion Heq; subst q. right. split; [reflexivity|].
      left. split; [apply (proj1 Hpad); reflexivity|reflexivity].
    + intros [[Hbad _]|[_ [[_ ->]|[old [Hb _]]]]].
      * discriminate.
      * reflexivity.
      * apply (proj2 (Hbits old)) in Hb. discriminate.
  - split.
    + intro Heq. inversion Heq; subst q. right. split; [reflexivity|right].
      exists obligations. split; [apply (proj1 (Hbits obligations)); reflexivity|].
      reflexivity.
    + intros [[Hbad _]|[_ [[Hp _]|[old [Hb ->]]]]].
      * discriminate.
      * apply (proj2 Hpad) in Hp. discriminate.
      * apply (proj2 (Hbits old)) in Hb. inversion Hb. reflexivity.
Qed.

Lemma completion_obligation_correct k w partial q :
  partial_rep k w partial ->
  (completion_obligation k partial = Some q <->
   (padding_candidate w /\ q = zero_bits k) \/
   exists old, bits_candidate k w old /\ q = rotate_bits old).
Proof.
  intros [Hpad Hbits]. destruct partial; simpl.
  - split; [discriminate|]. intros [[H _]|[old [H _]]].
    + apply (proj2 Hpad) in H. discriminate.
    + specialize (Hbits old). apply (proj2 Hbits) in H. discriminate.
  - split.
    + intro H. inversion H. left. split; [now apply Hpad|reflexivity].
    + intros [[H ->]|[old [H _]]].
      * reflexivity.
      * specialize (Hbits old). apply (proj2 Hbits) in H. discriminate.
  - split.
    + intro H. inversion H; subst q. right. exists obligations.
      split; [now apply Hbits|reflexivity].
    + intros [[H _]|[old [H Hold]]].
      * apply (proj2 Hpad) in H. discriminate.
      * apply (proj2 (Hbits old)) in H. inversion H. subst old q.
        reflexivity.
Qed.

Definition completed_rep k w (completed : family) : Prop :=
  (forall q, In q completed -> length q = k) /\
  forall target, length target = k ->
    (family_covers completed target <->
     exists q, completed_candidate k w q /\ bitvec_subset q target).

Lemma family_normalize_lengths k f q :
  In q (family_normalize k f) -> length q = k.
Proof.
  unfold family_normalize. intro H. apply filter_In in H as [H _].
  now apply all_bitvecs_length_member.
Qed.

Lemma family_covers_cons q f target :
  family_covers (q :: f) target <->
  bitvec_subset q target \/ family_covers f target.
Proof.
  unfold family_covers. split.
  - intros [x [[Hx|Hx] Hsub]].
    + subst x. now left.
    + right. exists x. now split.
  - intros [Hsub|[x [Hx Hsub]]].
    + exists q. split; [now left|exact Hsub].
    + exists x. split; [now right|exact Hsub].
Qed.

Lemma family_add_covers k q f target :
  length q = k -> (forall x, In x f -> length x = k) ->
  length target = k ->
  (family_covers (family_add k q f) target <->
   bitvec_subset q target \/ family_covers f target).
Proof.
  intros Hq Hf Htarget. unfold family_add.
  rewrite family_normalize_covers; [apply family_covers_cons| |exact Htarget].
  intros x [<-|Hx]; [exact Hq|now apply Hf].
Qed.

Lemma advance_family_lengths k a f q :
  In q (advance_family k a f) -> length q = k.
Proof. apply family_normalize_lengths. Qed.

Lemma family_add_lengths k q f x :
  In x (family_add k q f) -> length x = k.
Proof. apply family_normalize_lengths. Qed.

Definition extended_candidate k w a q : Prop :=
  exists old, completed_candidate k w old /\
    q = advance_obligations a old.

Definition completion_base k w q : Prop :=
  (padding_candidate w /\ q = zero_bits k) \/
  exists old, bits_candidate k w old /\ q = rotate_bits old.

Lemma completed_candidate_extend_iff k w a q :
  tight_core_symbol a -> a <> TLd ->
  (completed_candidate k (w ++ [a]) q <-> extended_candidate k w a q).
Proof.
  intros Hcore Hneq. rewrite completed_candidate_snoc.
  unfold extended_candidate. split.
  - intros [[Heq _]|[_ H]]; [contradiction|exact H].
  - intro H. right. now split.
Qed.

Lemma completed_candidate_d_iff k w q :
  completed_candidate k (w ++ [TLd]) q <->
  completion_base k w q \/ extended_candidate k w TLd q.
Proof.
  rewrite completed_candidate_snoc. unfold completion_base, extended_candidate.
  split.
  - intros [[_ H]|[_ H]]; [now left|now right].
  - intros [H|H]; [left|right]; split; try reflexivity;
      [exact H|apply tight_core_d|exact H].
Qed.

Lemma completion_base_length k w q : completion_base k w q -> length q = k.
Proof.
  intros [[_ ->]|[old [Hold ->]]].
  - apply zero_bits_length.
  - rewrite rotate_bits_length. now apply bits_candidate_length in Hold.
Qed.

Lemma advance_family_rep k w f a :
  completed_rep k w f ->
  (forall target, length target = k ->
    (family_covers (advance_family k a f) target <->
     exists q, extended_candidate k w a q /\ bitvec_subset q target)).
Proof.
  intros [Hlength Hrep] target Htarget. unfold advance_family.
  rewrite family_normalize_covers.
  - split.
    + intros [mapped [Hmapped Hsub]]. apply in_map_iff in Hmapped
        as [stored [Hmapped Hstored]]. subst mapped.
      assert (Hstored_len : length stored = k) by now apply Hlength.
      assert (Hcover : family_covers f stored).
      { exists stored. split; [exact Hstored|apply bitvec_subset_refl]. }
      apply (proj1 (Hrep stored Hstored_len)) in Hcover
        as [raw [Hraw Hrawsub]].
      exists (advance_obligations a raw). split.
      * unfold extended_candidate. exists raw. now split.
      * eapply bitvec_subset_trans; [apply advance_obligations_subset;
          exact Hrawsub|exact Hsub].
    + intros [mapped [[raw [Hraw ->]] Hsub]].
      pose proof (completed_candidate_length Hraw) as Hrawlen.
      assert (Hcover : family_covers f raw).
      { apply (proj2 (Hrep raw Hrawlen)). exists raw.
        split; [exact Hraw|apply bitvec_subset_refl]. }
      destruct Hcover as [stored [Hstored Hstoredsub]].
      exists (advance_obligations a stored). split.
      * apply in_map. exact Hstored.
      * eapply bitvec_subset_trans; [apply advance_obligations_subset;
          exact Hstoredsub|exact Hsub].
  - intros x Hx. apply in_map_iff in Hx as [old [<- Hold]].
    rewrite advance_obligations_length. now apply Hlength.
  - exact Htarget.
Qed.

Lemma completed_step_correct k w partial completed a :
  partial_rep k w partial -> completed_rep k w completed ->
  tight_core_symbol a ->
  completed_rep k (w ++ [a]) (completed_step k partial completed a).
Proof.
  intros Hpartial Hcompleted Hcore.
  pose proof (@advance_family_rep k w completed a Hcompleted) as Hadvance.
  destruct Hcompleted as [Hlength Hrep].
  unfold completed_rep. split.
  - intros q Hq. unfold completed_step in Hq. destruct a; simpl in Hq;
      try (now apply advance_family_lengths in Hq).
    destruct (completion_obligation k partial) eqn:Hnew;
      [now apply family_add_lengths in Hq|now apply advance_family_lengths in Hq].
  - intros target Htarget. unfold completed_step. destruct a.
    + setoid_rewrite (@completed_candidate_extend_iff k w TLa _ Hcore
        ltac:(discriminate)). exact (Hadvance target Htarget).
    + setoid_rewrite (@completed_candidate_extend_iff k w TLb _ Hcore
        ltac:(discriminate)). exact (Hadvance target Htarget).
    + setoid_rewrite (@completed_candidate_extend_iff k w TLc _ Hcore
        ltac:(discriminate)). exact (Hadvance target Htarget).
    + setoid_rewrite (@completed_candidate_d_iff k w).
      specialize (Hadvance target Htarget).
      destruct (completion_obligation k partial) as [fresh|] eqn:Hfresh.
      * rewrite family_add_covers.
        -- rewrite Hadvance. split.
           ++ intros [Hsub|[q [Hext Hsub]]].
              ** exists fresh. split; [left|exact Hsub].
                 apply (proj1 (@completion_obligation_correct k w partial fresh
                   Hpartial)). exact Hfresh.
              ** exists q. split; [now right|exact Hsub].
           ++ intros [q [[Hbase|Hext] Hsub]].
              ** left.
                 apply (proj2 (@completion_obligation_correct k w partial q
                   Hpartial)) in Hbase.
                 rewrite Hfresh in Hbase. inversion Hbase. subst q. exact Hsub.
              ** right. exists q. now split.
        -- apply (proj1 (@completion_obligation_correct k w partial fresh
             Hpartial)) in Hfresh. now apply completion_base_length in Hfresh.
        -- intros x Hx. now apply advance_family_lengths in Hx.
        -- exact Htarget.
      * rewrite Hadvance. split.
        -- intros [q [Hext Hsub]]. exists q. split; [now right|exact Hsub].
        -- intros [q [[Hbase|Hext] Hsub]].
           ++ apply (proj2 (@completion_obligation_correct k w partial q
                 Hpartial)) in Hbase.
              rewrite Hfresh in Hbase. discriminate.
           ++ exists q. now split.
    + setoid_rewrite (@completed_candidate_extend_iff k w TLe _ Hcore
        ltac:(discriminate)). exact (Hadvance target Htarget).
    + setoid_rewrite (@completed_candidate_extend_iff k w TLx _ Hcore
        ltac:(discriminate)). exact (Hadvance target Htarget).
    + exfalso. now apply tight_core_not_hash.
Qed.

Inductive state : Type :=
| Running (partial : partial_state) (completed : family)
| Accepting
| Dead.

Definition initial : state := Running PartialNone [].

Definition finalb (s : state) : bool :=
  match s with Accepting => true | _ => false end.

Definition family_has_empty k f : bool :=
  existsb (bitvec_eqb (zero_bits k)) f.

Definition step_running k partial completed symbol : state :=
  match symbol with
  | TLhash =>
      if family_has_empty k completed then Accepting else Dead
  | _ => Running (partial_step k partial symbol)
      (completed_step k partial completed symbol)
  end.

Definition step k (s : state) (symbol : tight_symbol) : state :=
  match s with
  | Running partial completed => step_running k partial completed symbol
  | Accepting | Dead => Dead
  end.

Fixpoint run k (s : state) (w : list tight_symbol) : state :=
  match w with
  | [] => s
  | a :: w' => run k (step k s a) w'
  end.

Definition accepts k w := finalb (run k initial w).

Lemma run_app k s u v : run k s (u ++ v) = run k (run k s u) v.
Proof.
  revert s. induction u as [|a u IH]; intro s; simpl; [reflexivity|].
  apply IH.
Qed.

Lemma padding_candidate_nonempty w : padding_candidate w -> w <> [].
Proof.
  intro H. induction H; intro Heq; apply (f_equal (@length tight_symbol)) in Heq;
    rewrite length_app in Heq; simpl in Heq; lia.
Qed.

Lemma bits_candidate_nonempty k w q : bits_candidate k w q -> w <> [].
Proof.
  intro H. induction H; intro Heq; apply (f_equal (@length tight_symbol)) in Heq;
    rewrite length_app in Heq; simpl in Heq; lia.
Qed.

Lemma completed_candidate_nonempty k w q : completed_candidate k w q -> w <> [].
Proof.
  intro H. induction H; intro Heq; apply (f_equal (@length tight_symbol)) in Heq;
    rewrite length_app in Heq; simpl in Heq; lia.
Qed.

Lemma initial_partial_rep k : partial_rep k [] PartialNone.
Proof.
  split.
  - split; [discriminate|]. intro H. exfalso.
    now apply (padding_candidate_nonempty H).
  - intro q. split; [discriminate|]. intro H. exfalso.
    now apply (bits_candidate_nonempty H).
Qed.

Lemma initial_completed_rep k : completed_rep k [] [].
Proof.
  split.
  - intros q H. contradiction.
  - intros target Htarget. split.
    + intros [q [H _]]. contradiction.
    + intros [q [H _]]. exfalso. now apply (completed_candidate_nonempty H).
Qed.

Theorem run_core_rep k w : tight_core_word w ->
  exists partial completed,
    run k initial w = Running partial completed /\
    partial_rep k w partial /\ completed_rep k w completed.
Proof.
  induction w as [|a w IHw] using rev_ind; intro Hcore.
  - exists PartialNone, []. split; [reflexivity|]. split.
    + apply initial_partial_rep.
    + apply initial_completed_rep.
  - apply (proj1 (tight_core_word_app _ _)) in Hcore as [Hw Ha].
    inversion Ha as [|a' rest Ha' Hnil]; subst a' rest.
    destruct (IHw Hw) as [partial [completed [Hrun [Hpartial Hcompleted]]]].
    rewrite run_app, Hrun. simpl run.
    exists (partial_step k partial a),
      (completed_step k partial completed a). split.
    + unfold step, step_running. destruct a; try reflexivity.
      exfalso. now apply tight_core_not_hash.
    + split.
      * now apply partial_step_correct.
      * now apply completed_step_correct.
Qed.

Lemma step_to_running_core k s a partial completed :
  step k s a = Running partial completed -> tight_core_symbol a.
Proof.
  destruct s as [p f| |].
  - destruct a; cbn [step step_running]; intro H; try discriminate;
      try apply tight_core_a; try apply tight_core_b; try apply tight_core_c;
      try apply tight_core_d; try apply tight_core_e; try apply tight_core_x.
    destruct (family_has_empty k f); discriminate.
  - destruct a; discriminate.
  - destruct a; discriminate.
Qed.

Lemma run_to_running_core k s w partial completed :
  run k s w = Running partial completed ->
  (exists p f, s = Running p f) /\ tight_core_word w.
Proof.
  revert s. induction w as [|a w IH]; intros s Hrun.
  - simpl in Hrun. split.
    + destruct s; inversion Hrun; subst. eauto.
    + constructor.
  - simpl in Hrun. destruct (IH (step k s a) Hrun)
      as [[p [f Hstep]] Hw].
    split.
    + destruct s; simpl in Hstep; try discriminate. eauto.
    + constructor.
      * now apply (@step_to_running_core k s a p f).
      * exact Hw.
Qed.

Lemma family_has_empty_spec k f :
  family_has_empty k f = true <-> In (zero_bits k) f.
Proof.
  unfold family_has_empty. rewrite existsb_exists. split.
  - intros [q [Hq Heq]]. apply bitvec_eqb_spec in Heq. now subst q.
  - intro H. exists (zero_bits k). split; [exact H|].
    apply bitvec_eqb_spec. reflexivity.
Qed.

Lemma completed_rep_has_empty k w f : completed_rep k w f ->
  (family_has_empty k f = true <->
   completed_candidate k w (zero_bits k)).
Proof.
  intros [Hlength Hrep]. rewrite family_has_empty_spec. split.
  - intro Hin. assert (Hcover : family_covers f (zero_bits k)).
    { exists (zero_bits k). split; [exact Hin|apply bitvec_subset_refl]. }
    apply (proj1 (Hrep (zero_bits k) (zero_bits_length k))) in Hcover
      as [q [Hq Hsub]].
    assert (q = zero_bits k).
    { apply bitvec_subset_zero_eq; [now apply completed_candidate_length in Hq|exact Hsub]. }
    now subst q.
  - intro Hcandidate.
    assert (Hcover : family_covers f (zero_bits k)).
    { apply (proj2 (Hrep (zero_bits k) (zero_bits_length k))).
      exists (zero_bits k). split; [exact Hcandidate|apply bitvec_subset_refl]. }
    destruct Hcover as [q [Hq Hsub]].
    assert (q = zero_bits k).
    { apply bitvec_subset_zero_eq; [now apply Hlength|exact Hsub]. }
    now subst q.
Qed.

Theorem accepts_completed_candidate k full :
  accepts k full = true <->
  exists body, full = body ++ [TLhash] /\
    completed_candidate k body (zero_bits k).
Proof.
  unfold accepts. split.
  - intro Haccept.
    assert (Hrun : run k initial full = Accepting).
    { destruct (run k initial full); simpl in Haccept; try discriminate;
        reflexivity. }
    induction full as [|x full IH] using rev_ind.
    + discriminate.
    + rewrite run_app in Hrun. simpl run in Hrun.
      remember (run k initial full) as before eqn:Hbefore.
      destruct before as [p f| |].
      2:{ destruct x; discriminate. }
      2:{ destruct x; discriminate. }
      destruct x; cbn [step step_running] in Hrun; try discriminate.
      destruct (family_has_empty k f) eqn:Hempty; inversion Hrun.
      destruct (@run_to_running_core k initial full p f (eq_sym Hbefore))
        as [_ Hcore].
      destruct (@run_core_rep k full Hcore)
        as [p' [f' [Hsame [Hp Hf]]]].
      rewrite <- Hbefore in Hsame. inversion Hsame; subst p' f'.
      exists full. split; [reflexivity|].
      now apply (proj1 (@completed_rep_has_empty k full f Hf)).
  - intros [body [-> Hcandidate]].
    pose proof (completed_candidate_core Hcandidate) as Hcore.
    destruct (@run_core_rep k body Hcore)
      as [partial [completed [Hrun [_ Hcompleted]]]].
    rewrite run_app, Hrun. simpl run. cbn [step step_running].
    rewrite (proj2 (@completed_rep_has_empty k body completed Hcompleted)
      Hcandidate). reflexivity.
Qed.

Lemma scan_bits_app k pending u v :
  scan_bits k pending (u ++ v) = scan_bits k (scan_bits k pending u) v.
Proof.
  revert pending. induction u as [|a u IH]; intro pending; simpl;
    [reflexivity|]. destruct a; apply IH.
Qed.

Lemma process_obligations_app q u v :
  process_obligations q (u ++ v) =
  process_obligations (process_obligations q u) v.
Proof.
  revert q. induction u as [|a u IH]; intro q; simpl;
    [reflexivity|apply IH].
Qed.

Lemma padding_candidate_append w pad :
  padding_candidate w -> Forall (eq TLe) pad ->
  padding_candidate (w ++ pad).
Proof.
  intros Hw. revert w Hw. induction pad as [|a pad IH]; intros w Hw Hpad.
  - now rewrite app_nil_r.
  - inversion Hpad; subst a.
    replace (w ++ TLe :: pad) with ((w ++ [TLe]) ++ pad)
      by (rewrite <- app_assoc; reflexivity).
    apply IH; [now apply PaddingExtend|assumption].
Qed.

Lemma padding_candidate_characterization w :
  padding_candidate w <->
  exists pre pad,
    w = pre ++ [TLa] ++ pad /\ tight_core_word pre /\
    Forall (eq TLe) pad.
Proof.
  split.
  - intro H. induction H.
    + exists pre, []. split; [reflexivity|]. split; [assumption|constructor].
    + destruct IHpadding_candidate as [pre [pad [-> [Hpre Hpad]]]].
      exists pre, (pad ++ [TLe]). repeat split; try assumption.
      * now rewrite !app_assoc.
      * apply Forall_app. split; [exact Hpad|constructor; [reflexivity|constructor]].
  - intros [pre [pad [-> [Hpre Hpad]]]].
    rewrite app_assoc. apply padding_candidate_append; [now apply PaddingStart|exact Hpad].
Qed.

Lemma bits_candidate_append k w q more :
  bits_candidate k w q -> tight_bit_word more ->
  bits_candidate k (w ++ more) (scan_bits k q more).
Proof.
  intros Hbits. revert w q Hbits.
  induction more as [|a more IH]; intros w q Hbits Hmore.
  - simpl. now rewrite app_nil_r.
  - inversion Hmore as [|a' more' Ha Htail]; subst a' more'.
    destruct Ha as [Hab|Hac].
    + subst a. replace (w ++ TLb :: more) with ((w ++ [TLb]) ++ more)
        by (rewrite <- app_assoc; reflexivity).
      apply IH; [now apply BitsExtendB|assumption].
    + subst a. replace (w ++ TLc :: more) with ((w ++ [TLc]) ++ more)
        by (rewrite <- app_assoc; reflexivity).
      apply IH; [now apply BitsExtendC|assumption].
Qed.

Lemma bits_candidate_from_padding k w bits :
  padding_candidate w -> tight_bit_word bits -> bits <> [] ->
  bits_candidate k (w ++ bits) (scan_bits k (zero_bits k) bits).
Proof.
  intros Hpad Hbits Hnon. destruct bits as [|a bits]; [contradiction|].
  inversion Hbits as [|a' bits' Ha Htail]; subst a' bits'.
  destruct Ha as [Hab|Hac].
  - subst a. simpl scan_bits. replace (w ++ TLb :: bits) with ((w ++ [TLb]) ++ bits)
      by (rewrite <- app_assoc; reflexivity).
    rewrite rotate_zero_bits.
    apply bits_candidate_append; [now apply BitsStartB|assumption].
  - subst a. simpl scan_bits. replace (w ++ TLc :: bits) with ((w ++ [TLc]) ++ bits)
      by (rewrite <- app_assoc; reflexivity).
    rewrite rotate_zero_bits.
    apply bits_candidate_append; [now apply BitsStartC|assumption].
Qed.

Lemma bits_candidate_characterization k w q :
  bits_candidate k w q <->
  exists pre pad bits,
    w = pre ++ [TLa] ++ pad ++ bits /\ tight_core_word pre /\
    Forall (eq TLe) pad /\ tight_bit_word bits /\ bits <> [] /\
    q = scan_bits k (zero_bits k) bits.
Proof.
  split.
  - intro H. induction H.
    + apply padding_candidate_characterization in H as
        [pre [pad [-> [Hpre Hpad]]]].
      exists pre, pad, [TLb].
      split; [now rewrite !app_assoc|]. split; [exact Hpre|].
      split; [exact Hpad|]. split.
      * constructor; [now left|constructor].
      * split; [discriminate|]. simpl. symmetry. apply rotate_zero_bits.
    + apply padding_candidate_characterization in H as
        [pre [pad [-> [Hpre Hpad]]]].
      exists pre, pad, [TLc].
      split; [now rewrite !app_assoc|]. split; [exact Hpre|].
      split; [exact Hpad|]. split.
      * constructor; [now right|constructor].
      * split; [discriminate|]. simpl. now rewrite rotate_zero_bits.
    + destruct IHbits_candidate as
        [pre [pad [bits [-> [Hpre [Hpad [Hword [Hnon Hq]]]]]]]].
      exists pre, pad, (bits ++ [TLb]). repeat split; try assumption.
      * now rewrite !app_assoc.
      * apply Forall_app. split; [exact Hword|constructor; [now left|constructor]].
      * intro Hnil. apply (f_equal (@length tight_symbol)) in Hnil.
        rewrite length_app in Hnil. simpl in Hnil. lia.
      * rewrite scan_bits_app. simpl. now rewrite <- Hq.
    + destruct IHbits_candidate as
        [pre [pad [bits [-> [Hpre [Hpad [Hword [Hnon Hq]]]]]]]].
      exists pre, pad, (bits ++ [TLc]). repeat split; try assumption.
      * now rewrite !app_assoc.
      * apply Forall_app. split; [exact Hword|constructor; [now right|constructor]].
      * intro Hnil. apply (f_equal (@length tight_symbol)) in Hnil.
        rewrite length_app in Hnil. simpl in Hnil. lia.
      * rewrite scan_bits_app. simpl. now rewrite <- Hq.
  - intros [pre [pad [bits [-> [Hpre [Hpad [Hword [Hnon ->]]]]]]]].
    replace (pre ++ [TLa] ++ pad ++ bits)
      with ((pre ++ [TLa] ++ pad) ++ bits)
      by (rewrite <- app_assoc; reflexivity).
    apply bits_candidate_from_padding; try assumption.
    apply padding_candidate_characterization. exists pre, pad. repeat split; assumption.
Qed.

Lemma completed_candidate_append k w q core :
  completed_candidate k w q -> tight_core_word core ->
  completed_candidate k (w ++ core) (process_obligations q core).
Proof.
  intros Hcompleted. revert w q Hcompleted.
  induction core as [|a core IH]; intros w q Hcompleted Hcore.
  - simpl. now rewrite app_nil_r.
  - inversion Hcore; subst. replace (w ++ a :: core) with ((w ++ [a]) ++ core)
      by (rewrite <- app_assoc; reflexivity).
    apply IH.
    + simpl. now apply CompleteExtend.
    + assumption.
Qed.

Definition completed_shape k w q : Prop :=
  exists pre pad bits core,
    w = pre ++ [TLa] ++ pad ++ bits ++ [TLd] ++ core /\
    tight_core_word pre /\ Forall (eq TLe) pad /\
    tight_bit_word bits /\ tight_core_word core /\
    q = process_obligations (scan_bits k (zero_bits k) bits)
      ([TLd] ++ core).

Lemma completed_candidate_characterization k w q :
  completed_candidate k w q <-> completed_shape k w q.
Proof.
  split.
  - intro H. induction H.
    + apply padding_candidate_characterization in H as
        [pre [pad [-> [Hpre Hpad]]]].
      exists pre, pad, [], [].
      split.
      * rewrite !app_nil_r. rewrite <- !app_assoc. reflexivity.
      * split; [exact Hpre|]. split; [exact Hpad|].
        split; [constructor|]. split; [constructor|].
        simpl. symmetry. apply advance_zero_bits.
    + apply bits_candidate_characterization in H as
        [pre [pad [bits [-> [Hpre [Hpad [Hword [Hnon Hq]]]]]]]].
      exists pre, pad, bits, [].
      split; [now rewrite !app_nil_r, !app_assoc|].
      split; [exact Hpre|]. split; [exact Hpad|].
      split; [exact Hword|]. split; [constructor|].
      simpl. unfold advance_obligations. simpl. now rewrite <- Hq.
    + destruct IHcompleted_candidate as
        [pre [pad [bits [core [-> [Hpre [Hpad [Hbits [Hcore Hq]]]]]]]]].
      exists pre, pad, bits, (core ++ [a]). repeat split; try assumption.
      * now rewrite !app_assoc.
      * apply tight_core_word_snoc; assumption.
      * replace ([TLd] ++ core ++ [a]) with (([TLd] ++ core) ++ [a])
          by (symmetry; apply app_assoc).
        rewrite process_obligations_app. simpl. simpl in Hq.
        now rewrite <- Hq.
  - intros [pre [pad [bits [core
      [-> [Hpre [Hpad [Hbits [Hcore ->]]]]]]]]].
    assert (Hpadding : padding_candidate (pre ++ [TLa] ++ pad)).
    { apply padding_candidate_characterization. exists pre, pad.
      repeat split; assumption. }
    destruct bits as [|b bits].
    + simpl. replace (pre ++ TLa :: pad ++ TLd :: core)
        with (((pre ++ [TLa] ++ pad) ++ [TLd]) ++ core).
      2:{ rewrite <- !app_assoc. reflexivity. }
      rewrite advance_zero_bits.
      apply (@completed_candidate_append k
        ((pre ++ [TLa] ++ pad) ++ [TLd]) (zero_bits k) core);
        [now apply CompletePadding|exact Hcore].
    + assert (Hnon : b :: bits <> []) by discriminate.
      assert (Hbc : bits_candidate k
          ((pre ++ [TLa] ++ pad) ++ (b :: bits))
          (scan_bits k (zero_bits k) (b :: bits))).
      { apply bits_candidate_from_padding; assumption. }
      simpl process_obligations. cbn [advance_obligations].
      replace (pre ++ [TLa] ++ pad ++ (b :: bits) ++ [TLd] ++ core)
        with ((((pre ++ [TLa] ++ pad) ++ (b :: bits)) ++ [TLd]) ++ core)
        by (rewrite <- !app_assoc; reflexivity).
      apply (@completed_candidate_append k
        (((pre ++ [TLa] ++ pad) ++ (b :: bits)) ++ [TLd])
        (rotate_bits (scan_bits k (zero_bits k) (b :: bits))) core);
        [now apply CompleteBits|exact Hcore].
Qed.

Theorem accepts_suffix_correct k full : 2 <= k ->
  (accepts k full = true <->
   suffix_satisfies tight_symbol_eqb (tight_expression k) full []).
Proof.
  intro Hk. rewrite accepts_completed_candidate.
  rewrite tight_expression_suffix_characterization. split.
  - intros [body [-> Hcandidate]].
    apply completed_candidate_characterization in Hcandidate.
    destruct Hcandidate as [pre [pad [bits [core
      [Hbody [Hpre [Hpad [Hbits [Hcore Hzero]]]]]]]]].
    exists pre, pad, bits, core. repeat split; try assumption.
    + rewrite Hbody. now rewrite !app_assoc.
    + apply (proj2 (@tight_factor_star_satisfies k bits
        ([TLd] ++ core ++ [TLhash]) ltac:(lia))).
      assert (Hfuture : tight_core_word ([TLd] ++ core)).
      { apply (proj2 (tight_core_word_app _ _)). split.
        - constructor; [apply tight_core_d|constructor].
        - exact Hcore. }
      apply (proj1 (@scan_bits_accept_characterization k bits
        ([TLd] ++ core) Hk Hbits Hfuture)).
      symmetry. exact Hzero.
  - intros [pre [pad [bits [core
      [Hfull [Hpre [Hpad [Hcore Hstar]]]]]]]].
    assert (Hbits : tight_bit_word bits).
    { apply (proj1 (@tight_factor_star_satisfies k bits
        ([TLd] ++ core ++ [TLhash]) ltac:(lia))) in Hstar.
      now apply (@tight_bits_accept_bit_word k bits
        ([TLd] ++ core ++ [TLhash])). }
    assert (Haccept : tight_bits_accept k bits
        (([TLd] ++ core) ++ [TLhash])).
    { apply (proj1 (@tight_factor_star_satisfies k bits
        ([TLd] ++ core ++ [TLhash]) ltac:(lia))) in Hstar.
      exact Hstar. }
    assert (Hfuture : tight_core_word ([TLd] ++ core)).
    { apply (proj2 (tight_core_word_app _ _)). split.
      - constructor; [apply tight_core_d|constructor].
      - exact Hcore. }
    assert (Hzero : process_obligations
        (scan_bits k (zero_bits k) bits) ([TLd] ++ core) = zero_bits k).
    { apply (proj2 (@scan_bits_accept_characterization k bits
        ([TLd] ++ core) Hk Hbits Hfuture)). exact Haccept. }
    exists (pre ++ [TLa] ++ pad ++ bits ++ [TLd] ++ core).
    split.
    + rewrite Hfull. now rewrite !app_assoc.
    + apply completed_candidate_characterization. unfold completed_shape.
      exists pre, pad, bits, core. repeat split; try assumption.
      symmetry. exact Hzero.
Qed.

Theorem tight_expression_projected_exact_all k w : 0 < k ->
  (rewpla_language tight_symbol_eqb (tight_expression k) w <->
   rewpla_denote tight_symbol_eqb (tight_expression k) (w, [])).
Proof.
  intro Hk. unfold rewpla_language, project_language. split.
  - intros [[u v] [Hden Hprojection]].
    assert (Hv : v = []) by
      now apply (@tight_expression_denote_residual_nil k u v Hk Hden).
    subst v. unfold constraint_projection in Hprojection. simpl in Hprojection.
    rewrite app_nil_r in Hprojection. now subst u.
  - intro Hden. exists (w, []). split; [exact Hden|].
    unfold constraint_projection. simpl. now rewrite app_nil_r.
Qed.

Theorem dfa_accept_correct k w : 2 <= k ->
  (accepts k w = true <->
   rewpla_language tight_symbol_eqb (tight_expression k) w).
Proof.
  intro Hk. rewrite accepts_suffix_correct by exact Hk.
  rewrite tight_suffix_satisfies_empty_exact.
  rewrite tight_expression_projected_exact_all by lia. reflexivity.
Qed.

Definition partial_state_eqb (x y : partial_state) : bool :=
  match x, y with
  | PartialNone, PartialNone | PartialPadding, PartialPadding => true
  | PartialBits p, PartialBits q => bitvec_eqb p q
  | _, _ => false
  end.

Fixpoint family_eqb (x y : family) : bool :=
  match x, y with
  | [], [] => true
  | p :: x', q :: y' => bitvec_eqb p q && family_eqb x' y'
  | _, _ => false
  end.

Definition state_eqb (x y : state) : bool :=
  match x, y with
  | Running ux fx, Running uy fy =>
      partial_state_eqb ux uy && family_eqb fx fy
  | Accepting, Accepting | Dead, Dead => true
  | _, _ => false
  end.

Lemma partial_state_eqb_spec x y : partial_state_eqb x y = true <-> x = y.
Proof.
  destruct x, y; simpl; try (split; discriminate); try tauto.
  rewrite bitvec_eqb_spec. constructor; congruence.
Qed.

Lemma family_eqb_spec x y : family_eqb x y = true <-> x = y.
Proof.
  revert y. induction x as [|p x IH]; intros [|q y]; simpl;
    try (split; discriminate); try tauto.
  rewrite Bool.andb_true_iff, bitvec_eqb_spec, IH.
  intuition congruence.
Qed.

Lemma state_eqb_spec x y : state_eqb x y = true <-> x = y.
Proof.
  destruct x, y; simpl; try (split; discriminate); try tauto.
  rewrite Bool.andb_true_iff, partial_state_eqb_spec, family_eqb_spec.
  intuition congruence.
Qed.

Definition states_closedb k alphabet states :=
  forallb (fun s => forallb (fun a =>
    existsb (state_eqb (step k s a)) states) alphabet) states.

Lemma states_closedb_sound k alphabet states :
  states_closedb k alphabet states = true ->
  forall s a, In s states -> In a alphabet -> In (step k s a) states.
Proof.
  unfold states_closedb. intros H s a Hs Ha.
  apply forallb_forall with (x := s) in H; [|exact Hs].
  apply forallb_forall with (x := a) in H; [|exact Ha].
  apply existsb_exists in H as [t [Ht Heq]].
  apply state_eqb_spec in Heq. now rewrite Heq.
Qed.

Lemma closed_table_run_membership k alphabet states w s :
  states_closedb k alphabet states = true -> In s states ->
  (forall a, In a w -> In a alphabet) ->
  In (run k s w) states.
Proof.
  intros Hclosed. revert s. induction w as [|a w IH]; intros s Hs Hw; simpl.
  - exact Hs.
  - apply IH.
    + eapply states_closedb_sound; [exact Hclosed|exact Hs|].
      apply Hw. now left.
    + intros b Hb. apply Hw. now right.
Qed.

Theorem closed_table_dfa_accept_correct k alphabet states :
  2 <= k -> states_closedb k alphabet states = true ->
  In initial states ->
  forall w, (forall a, In a w -> In a alphabet) ->
    In (run k initial w) states /\
    (accepts k w = true <->
     rewpla_language tight_symbol_eqb (tight_expression k) w).
Proof.
  intros Hk Hclosed Hinitial w Hw. split.
  - eapply closed_table_run_membership; eassumption.
  - now apply dfa_accept_correct.
Qed.

End TightAutomaton.

Print Assumptions TightAutomaton.family_normalize_covers.
Print Assumptions TightAutomaton.tight_expression_denote_residual_nil.
Print Assumptions TightAutomaton.dfa_accept_correct.
Print Assumptions TightAutomaton.states_closedb_sound.
Print Assumptions TightAutomaton.closed_table_dfa_accept_correct.
