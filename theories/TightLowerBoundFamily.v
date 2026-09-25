From Stdlib Require Import List Bool Arith Lia PeanoNat.
From CCont Require Import StringConstraints Syntax LookaheadSemantics
  ConstraintExpansion LookaheadDerivatives LookaheadDecision SemanticDFA
  DerivativeLowerBound LowerBoundFamily.
Import ListNotations.
Set Implicit Arguments.

(** * A linear-width double-exponential lower-bound family

    Unlike [LowerBoundFamily], this construction uses a fixed alphabet and
    one syntactic lookahead occurrence.  Iteration starts that same periodic
    obligation at different phases.  The phase replaces the growing family
    of marker letters in the older witness. *)

Inductive tight_symbol :=
| TLa | TLb | TLc | TLd | TLe | TLx | TLhash.

Definition tight_symbol_eqb (x y : tight_symbol) : bool :=
  match x, y with
  | TLa, TLa | TLb, TLb | TLc, TLc | TLd, TLd
  | TLe, TLe | TLx, TLx | TLhash, TLhash => true
  | _, _ => false
  end.

Lemma tight_symbol_eqb_spec x y :
  tight_symbol_eqb x y = true <-> x = y.
Proof.
  destruct x, y; simpl; split; intro H; try reflexivity; discriminate.
Qed.

Definition tight_core_atoms : list tight_symbol :=
  [TLa; TLb; TLc; TLd; TLe; TLx].

Definition tight_core_regex : regex tight_symbol :=
  regex_sum tight_core_atoms.

Definition tight_core_symbol (a : tight_symbol) : Prop :=
  In a tight_core_atoms.

Definition tight_core_word (w : list tight_symbol) : Prop :=
  Forall tight_core_symbol w.

Fixpoint regex_repeat {A : Type} (r : regex A) (n : nat) : regex A :=
  match n with
  | 0 => Eps
  | S n' => Concat r (regex_repeat r n')
  end.

Definition tight_period_regex k : regex tight_symbol :=
  regex_repeat tight_core_regex k.

Definition tight_phase_regex k : regex tight_symbol :=
  Concat (Star (tight_period_regex k)) (Atom TLx).

Definition tight_assertion k : rewpla tight_symbol :=
  WLookahead (embed_regex (tight_phase_regex k)).

Definition tight_factor k : rewpla tight_symbol :=
  WPlus (WAtom TLb) (WConcat (WAtom TLc) (tight_assertion k)).

(** [TLe*] is deliberately between the record marker and the bit block.
    The lower-bound words use exactly [k-2] copies.  Consequently every
    record has length [2*k], and the constraint started by bit [i] sees test
    position [i] at distance divisible by [k]. *)
Definition tight_expression k : rewpla tight_symbol :=
  WConcat (embed_regex (Star tight_core_regex))
    (WConcat (WAtom TLa)
      (WConcat (embed_regex (Star (Atom TLe)))
        (WConcat (WStar (tight_factor k))
          (WConcat (WAtom TLd)
            (WConcat (embed_regex (Star tight_core_regex))
              (WAtom TLhash)))))).

Definition tight_bits k (S : list nat) : list tight_symbol :=
  map (fun i => if existsb (Nat.eqb i) S then TLc else TLb) (seq 0 k).

Definition tight_record k (S : list nat) : list tight_symbol :=
  TLa :: repeat TLe (k - 2) ++ tight_bits k S ++ [TLd].

Fixpoint tight_family_prefix k (F : list (list nat)) : list tight_symbol :=
  match F with
  | [] => []
  | subset :: F' => tight_record k subset ++ tight_family_prefix k F'
  end.

Definition tight_query k (T : list nat) : list tight_symbol :=
  map (fun i => if existsb (Nat.eqb i) T then TLx else TLe) (seq 0 k).

Definition tight_test k (T : list nat) : list tight_symbol :=
  tight_query k T ++ [TLhash].

Lemma tight_core_atoms_length : length tight_core_atoms = 6.
Proof. reflexivity. Qed.

Lemma regex_repeat_width {A : Type} (r : regex A) n :
  alphabetic_width (regex_repeat r n) = n * alphabetic_width r.
Proof. induction n; simpl; lia. Qed.

Lemma tight_core_regex_width : alphabetic_width tight_core_regex = 6.
Proof.
  unfold tight_core_regex. rewrite regex_sum_width, tight_core_atoms_length.
  reflexivity.
Qed.

Lemma tight_phase_regex_width k :
  alphabetic_width (tight_phase_regex k) = 6 * k + 1.
Proof.
  unfold tight_phase_regex, tight_period_regex. simpl.
  rewrite regex_repeat_width, tight_core_regex_width. lia.
Qed.

Lemma tight_factor_width k : rewpla_width (tight_factor k) = 6 * k + 3.
Proof.
  unfold tight_factor.
  change (1 + (1 + rewpla_width (tight_assertion k)) = 6 * k + 3).
  unfold tight_assertion.
  change
    (1 + (1 + rewpla_width (embed_regex (tight_phase_regex k))) =
     6 * k + 3).
  rewrite embed_regex_width, tight_phase_regex_width. lia.
Qed.

(** Exact alphabetic width: linear in the phase count [k]. *)
Theorem tight_expression_width k :
  rewpla_width (tight_expression k) = 6 * k + 19.
Proof.
  unfold tight_expression.
  change
    (alphabetic_width (Star tight_core_regex) +
      (1 + (alphabetic_width (Star (Atom TLe)) +
        (rewpla_width (WStar (tight_factor k)) +
          (1 + (alphabetic_width (Star tight_core_regex) + 1))))) =
     6 * k + 19).
  cbn [alphabetic_width rewpla_width].
  rewrite tight_core_regex_width, tight_factor_width.
  lia.
Qed.

Lemma tight_bits_length k S : length (tight_bits k S) = k.
Proof. unfold tight_bits. now rewrite length_map, length_seq. Qed.

Lemma tight_query_length k T : length (tight_query k T) = k.
Proof. unfold tight_query. now rewrite length_map, length_seq. Qed.

Lemma tight_record_length k S : 2 <= k -> length (tight_record k S) = 2 * k.
Proof.
  intro Hk. unfold tight_record.
  change
    (length ([TLa] ++ repeat TLe (k - 2) ++ tight_bits k S ++ [TLd]) =
     2 * k).
  rewrite !length_app, repeat_length, tight_bits_length. simpl. lia.
Qed.

Lemma tight_core_a : tight_core_symbol TLa.
Proof. unfold tight_core_symbol, tight_core_atoms. simpl. tauto. Qed.
Lemma tight_core_b : tight_core_symbol TLb.
Proof. unfold tight_core_symbol, tight_core_atoms. simpl. tauto. Qed.
Lemma tight_core_c : tight_core_symbol TLc.
Proof. unfold tight_core_symbol, tight_core_atoms. simpl. tauto. Qed.
Lemma tight_core_d : tight_core_symbol TLd.
Proof. unfold tight_core_symbol, tight_core_atoms. simpl. tauto. Qed.
Lemma tight_core_e : tight_core_symbol TLe.
Proof. unfold tight_core_symbol, tight_core_atoms. simpl. tauto. Qed.
Lemma tight_core_x : tight_core_symbol TLx.
Proof. unfold tight_core_symbol, tight_core_atoms. simpl. tauto. Qed.

Lemma tight_core_not_hash : ~ tight_core_symbol TLhash.
Proof.
  unfold tight_core_symbol, tight_core_atoms. simpl.
  intros [H|[H|[H|[H|[H|[H|[]]]]]]]; discriminate.
Qed.

Lemma tight_core_word_app u v :
  tight_core_word (u ++ v) <-> tight_core_word u /\ tight_core_word v.
Proof. unfold tight_core_word. now rewrite Forall_app. Qed.

Lemma tight_core_word_firstn n w :
  tight_core_word w -> tight_core_word (firstn n w).
Proof.
  revert w. induction n as [|n IH]; intros [|a w] H; simpl; constructor.
  - now inversion H.
  - apply IH. now inversion H.
Qed.

Lemma tight_core_word_skipn n w :
  tight_core_word w -> tight_core_word (skipn n w).
Proof.
  revert w. induction n as [|n IH]; intros [|a w] H; simpl; try assumption;
    try constructor.
  apply IH. now inversion H.
Qed.

Lemma matches_tight_core_regex w :
  matches tight_core_regex w <->
  exists a, tight_core_symbol a /\ w = [a].
Proof. apply matches_regex_sum. Qed.

Lemma matches_regex_repeat_core k w :
  matches (regex_repeat tight_core_regex k) w <->
  length w = k /\ tight_core_word w.
Proof.
  revert w. induction k as [|k IH]; intro w; simpl.
  - split.
    + intro H. inversion H; subst. now split; constructor.
    + intros [Hlen _]. destruct w; [constructor|discriminate].
  - split.
    + intro H. inversion H; subst.
      match goal with
      | Hc : matches tight_core_regex ?u,
        Hr : matches (regex_repeat tight_core_regex k) ?v |- _ =>
          apply matches_tight_core_regex in Hc as [a [Ha ->]];
          apply IH in Hr as [Hlen Hcore]
      end.
      split; [simpl; lia|now constructor].
    + intros [Hlen Hcore]. destruct w as [|a w]; [discriminate|].
      inversion Hcore as [|? ? Ha Hw]; subst.
      apply M_Concat with (u := [a]) (v := w).
      * apply matches_tight_core_regex. exists a. now split.
      * apply IH. split; [simpl in Hlen; lia|exact Hw].
Qed.

Lemma concat_words_core ws :
  Forall tight_core_word ws -> tight_core_word (concat_words ws).
Proof.
  intro H. induction H; simpl; [constructor|].
  now apply (proj2 (tight_core_word_app _ _)).
Qed.

Lemma concat_words_length_period k (ws : list (list tight_symbol)) :
  Forall (fun w => length w = k) ws ->
  length (concat_words ws) = length ws * k.
Proof.
  intro H. induction H; simpl; [reflexivity|].
  rewrite length_app, H, IHForall. lia.
Qed.

Lemma matches_tight_period_star k w : 0 < k ->
  (matches (Star (tight_period_regex k)) w <->
   tight_core_word w /\ exists n, length w = n * k).
Proof.
  intro Hk. split.
  - intro H.
    destruct (matches_star_factors tight_symbol_eqb tight_symbol_eqb_spec H)
      as [ws [Hws Hcat]]. subst w.
    assert (Hcores : Forall tight_core_word ws).
    { eapply Forall_impl; [|exact Hws]. intros q Hq.
      unfold tight_period_regex in Hq.
      now apply matches_regex_repeat_core in Hq. }
    split; [now apply concat_words_core|].
    exists (length ws). apply concat_words_length_period.
    eapply Forall_impl; [|exact Hws]. intros q Hq.
    unfold tight_period_regex in Hq.
    now apply matches_regex_repeat_core in Hq.
  - intros [Hcore [n Hlen]]. revert w Hcore Hlen.
    induction n as [|n IH]; intros w Hcore Hlen.
    + simpl in Hlen. apply length_zero_iff_nil in Hlen. subst. constructor.
    + assert (Htake : length (firstn k w) = k).
      { rewrite length_firstn. rewrite Hlen. lia. }
      assert (Hdrop : length (skipn k w) = n * k).
      { rewrite length_skipn, Hlen. lia. }
      rewrite <- (firstn_skipn k w).
      apply M_StarApp.
      * intro Hnil. rewrite Hnil in Htake. simpl in Htake. lia.
      * unfold tight_period_regex. apply matches_regex_repeat_core.
        split; [exact Htake|].
        now apply tight_core_word_firstn.
      * apply IH.
        -- now apply tight_core_word_skipn.
        -- exact Hdrop.
Qed.

Definition tight_phase_hit k (z : list tight_symbol) : Prop :=
  exists n pre tail,
    length pre = n * k /\ tight_core_word pre /\
    z = pre ++ TLx :: tail.

Lemma tight_phase_regex_matches k z : 0 < k ->
  (exists w, matches (tight_phase_regex k) w /\ word_prefix w z) <->
  tight_phase_hit k z.
Proof.
  intro Hk. unfold tight_phase_hit. split.
  - intros [w [Hw [tail Hz]]]. unfold tight_phase_regex in Hw.
    inversion Hw as [| | | |r s pre last Hstar Hx| |]; subst.
    inversion Hx; subst last.
    apply (proj1 (matches_tight_period_star (k:=k) pre Hk)) in Hstar
      as [Hcore [n Hlen]].
    exists n, pre, tail.
    repeat split; try assumption.
    symmetry. exact (app_assoc pre [TLx] tail).
  - intros [n [pre [tail [Hlen [Hcore Hz]]]]].
    exists (pre ++ [TLx]). split.
    + unfold tight_phase_regex. apply M_Concat.
      * apply (proj2 (matches_tight_period_star (k:=k) pre Hk)).
        split; [exact Hcore|now exists n].
      * constructor.
    + exists tail. subst z. now rewrite <- app_assoc.
Qed.

Lemma tight_assertion_satisfies k u z : 0 < k ->
  (suffix_satisfies tight_symbol_eqb (tight_assertion k) u z <->
   u = [] /\ tight_phase_hit k z).
Proof.
  intro Hk. unfold tight_assertion.
  rewrite suffix_satisfies_lookahead. split.
  - intros [-> [[m c] [Hden Hprefix]]].
    apply (proj1 (embed_regex_semantics tight_symbol_eqb
      tight_symbol_eqb_spec _ (m,c))) in Hden.
    destruct Hden as [w [Heq Hmatch]]. inversion Heq; subst m c.
    split; [reflexivity|].
    apply (proj1 (tight_phase_regex_matches (k:=k) z Hk)).
    exists w. split; [exact Hmatch|].
    unfold constraint_projection in Hprefix. simpl in Hprefix.
    now rewrite app_nil_r in Hprefix.
  - intros [-> Hhit]. split; [reflexivity|].
    apply (proj2 (tight_phase_regex_matches (k:=k) z Hk)) in Hhit.
    destruct Hhit as [w [Hmatch Hprefix]].
    exists (w, []). split.
    + apply (proj2 (embed_regex_semantics tight_symbol_eqb
        tight_symbol_eqb_spec _ (w,[]))).
      exists w. now split.
    + unfold constraint_projection. simpl. now rewrite app_nil_r.
Qed.

Lemma tight_factor_satisfies k u z : 0 < k ->
  (suffix_satisfies tight_symbol_eqb (tight_factor k) u z <->
   u = [TLb] \/ (u = [TLc] /\ tight_phase_hit k z)).
Proof.
  intro Hk. unfold tight_factor. rewrite suffix_satisfies_plus,
    suffix_satisfies_atom,
    (suffix_satisfies_concat tight_symbol_eqb tight_symbol_eqb_spec).
  split.
  - intros [->|[x [y [Hxy [Hx Hy]]]]]; [now left|].
    apply suffix_satisfies_atom in Hx.
    apply (proj1 (tight_assertion_satisfies (k:=k) y z Hk)) in Hy
      as [-> Hreq].
    subst x. simpl in Hxy. subst u. now right.
  - intros [->|[-> Hreq]].
    + now left.
    + right. exists [TLc], []. split; [reflexivity|]. split.
      * apply suffix_satisfies_atom. reflexivity.
      * apply (proj2 (tight_assertion_satisfies (k:=k) [] z Hk)).
        now split.
Qed.

Section StarUnfold.
Context {A : Type} (eqb : A -> A -> bool).
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma lang_power_succ_left (R : constraint_language A) n :
  lang_equiv (lang_power eqb R (S n))
    (lang_concat eqb R (lang_power eqb R n)).
Proof.
  induction n as [|n IH].
  - simpl. eapply lang_equiv_trans.
    + apply lang_concat_one_left; exact eqb_spec.
    + apply lang_equiv_sym. apply lang_concat_one_right; exact eqb_spec.
  - simpl. eapply lang_equiv_trans.
    + apply lang_concat_compat; [exact IH|apply lang_equiv_refl].
    + apply lang_concat_assoc; exact eqb_spec.
Qed.

End StarUnfold.

Lemma tight_factor_main_length k u z : 0 < k ->
  suffix_satisfies tight_symbol_eqb (tight_factor k) u z -> length u = 1.
Proof.
  intro Hk. intro H.
  apply (proj1 (tight_factor_satisfies (k:=k) u z Hk)) in H.
  destruct H as [->|[-> _]]; reflexivity.
Qed.

(** One iteration is peeled from the left.  This is the semantic reason the
    single syntactic assertion can create [k] independently phased tests. *)
Lemma tight_factor_star_cons k s bits z : 0 < k ->
  (suffix_satisfies tight_symbol_eqb (WStar (tight_factor k))
      (s :: bits) z <->
   suffix_satisfies tight_symbol_eqb (tight_factor k) [s] (bits ++ z) /\
   suffix_satisfies tight_symbol_eqb (WStar (tight_factor k)) bits z).
Proof.
  intro Hk. unfold suffix_satisfies, constraint_expansion. split.
  - intros [res [[n Hpow] Hres]]. destruct n as [|n].
    + simpl in Hpow. unfold lang_one in Hpow. discriminate.
    + apply (proj1 (lang_power_succ_left tight_symbol_eqb
        tight_symbol_eqb_spec (rewpla_denote tight_symbol_eqb (tight_factor k)) n
        (s :: bits, res))) in Hpow.
      assert (Hexpanded :
        constraint_expansion
          (lang_concat tight_symbol_eqb
            (rewpla_denote tight_symbol_eqb (tight_factor k))
            (lang_power tight_symbol_eqb
              (rewpla_denote tight_symbol_eqb (tight_factor k)) n))
          (s :: bits, z)).
      { exists res. now split. }
      apply (proj1 (constraint_expansion_concat tight_symbol_eqb
        tight_symbol_eqb_spec _ _ (s :: bits, z))) in Hexpanded.
      destruct Hexpanded as
        [u [v [u' [v' [Hu [Hu' [Hmain [Hv Hv']]]]]]]].
      assert (Hulen : length u = 1).
      { apply (tight_factor_main_length (k:=k) (u:=u) (z:=u' ++ z) Hk).
        exists v. now split. }
      destruct u as [|a u]; [discriminate|].
      destruct u as [|a' u]; [|simpl in Hulen; lia].
      simpl in Hmain. inversion Hmain; subst a u'.
      split.
      * exists v. now split.
      * exists v'. split; [now exists n|exact Hv'].
  - intros [[v [Hv Hvp]] [v' [[n Hn] Hv'p]]].
    assert (Hexpanded : suffix_concat
        (rewpla_denote tight_symbol_eqb (tight_factor k))
        (lang_power tight_symbol_eqb
          (rewpla_denote tight_symbol_eqb (tight_factor k)) n)
        (s :: bits, z)).
    { exists [s], v, bits, v'. repeat split; try assumption. }
    apply (proj2 (constraint_expansion_concat tight_symbol_eqb
      tight_symbol_eqb_spec _ _ (s :: bits, z))) in Hexpanded.
    destruct Hexpanded as [res [Hconcat Hres]]. exists res. split; [|exact Hres].
    exists (S n).
    apply (proj2 (lang_power_succ_left tight_symbol_eqb
      tight_symbol_eqb_spec (rewpla_denote tight_symbol_eqb (tight_factor k)) n
      (s :: bits, res))).
    exact Hconcat.
Qed.

Fixpoint tight_bits_accept (k : nat) (bits suffix : list tight_symbol) : Prop :=
  match bits with
  | [] => True
  | s :: bits' =>
      (s = TLb \/ (s = TLc /\ tight_phase_hit k (bits' ++ suffix))) /\
      tight_bits_accept k bits' suffix
  end.

Lemma tight_factor_star_satisfies k bits z : 0 < k ->
  (suffix_satisfies tight_symbol_eqb (WStar (tight_factor k)) bits z <->
   tight_bits_accept k bits z).
Proof.
  intro Hk. revert z. induction bits as [|s bits IH]; intro z.
  - split.
    + intros [res [[n Hn] Hprefix]].
      assert (n = 0).
      { destruct n; [reflexivity|].
        apply (proj1 (lang_power_succ_left tight_symbol_eqb
          tight_symbol_eqb_spec (rewpla_denote tight_symbol_eqb (tight_factor k)) n
          ([],res))) in Hn.
        destruct Hn as [[u v] [[u' v'] [Hu [Hu' Hcat]]]].
        destruct (@constraint_concat_result_shape tight_symbol tight_symbol_eqb
          u v u' v' ([],res) Hcat) as [t Hshape].
        pose proof (f_equal fst Hshape) as Hmain. simpl in Hmain.
        pose proof (f_equal snd Hshape) as Hres. simpl in Hres.
        assert (length u = 1).
        { apply (tight_factor_main_length (k:=k) (u:=u) (z:=u' ++ res) Hk).
          exists v. split; [exact Hu|].
          assert (Hcat' : constraint_concat tight_symbol_eqb (u,v) (u',v') =
              Some (u ++ u', t)) by now rewrite <- Hshape.
          pose proof (constraint_concat_preservation tight_symbol_eqb
            tight_symbol_eqb_spec u v u' v' Hcat') as [Hv _].
          now rewrite <- Hres in Hv. }
        symmetry in Hmain. apply app_eq_nil in Hmain as [Hu0 _].
        subst u. simpl in H. discriminate. }
      subst n. exact I.
    + intros _. exists []. split; [now exists 0|apply word_prefix_nil].
  - rewrite tight_factor_star_cons by exact Hk. simpl tight_bits_accept.
    rewrite IH, (tight_factor_satisfies (k:=k) [s] (bits ++ z) Hk).
    assert ([s] = [TLb] <-> s = TLb) as Hsb by
      (split; [congruence|intros ->; reflexivity]).
    assert ([s] = [TLc] <-> s = TLc) as Hsc by
      (split; [congruence|intros ->; reflexivity]).
    rewrite Hsb, Hsc.
    tauto.
Qed.

(** A small index operation kept local to the witness proof.  Using an
    option-valued operation makes the phase arithmetic independent of any
    library convention for total list indexing. *)
Fixpoint tight_at {A : Type} (n : nat) (w : list A) : option A :=
  match n, w with
  | 0, a :: _ => Some a
  | S n', _ :: w' => tight_at n' w'
  | _, _ => None
  end.

Lemma tight_at_some_bound {A : Type} n (w : list A) a :
  tight_at n w = Some a -> n < length w.
Proof.
  revert n. induction w as [|x w IH]; intros [|n] H; simpl in *;
    try discriminate; [lia|].
  specialize (IH n H). lia.
Qed.

Lemma tight_at_in {A : Type} n (w : list A) a :
  tight_at n w = Some a -> In a w.
Proof.
  revert n. induction w as [|x w IH]; intros [|n] H; simpl in *;
    try discriminate.
  - inversion H; now left.
  - right. now apply (IH n).
Qed.

Lemma tight_at_app_left {A : Type} n (u v : list A) :
  n < length u -> tight_at n (u ++ v) = tight_at n u.
Proof.
  revert n. induction u as [|x u IH]; intros [|n] H; simpl in *;
    try lia; [reflexivity|].
  apply IH. lia.
Qed.

Lemma tight_at_app_right {A : Type} n (u v : list A) :
  tight_at (length u + n) (u ++ v) = tight_at n v.
Proof.
  revert n. induction u as [|x u IH]; intro n; simpl; [reflexivity|].
  now rewrite IH.
Qed.

Lemma tight_at_split {A : Type} n (w : list A) a :
  tight_at n w = Some a ->
  exists pre tail, w = pre ++ a :: tail /\ length pre = n.
Proof.
  revert n. induction w as [|x w IH]; intros [|n] H; simpl in H;
    try discriminate.
  - inversion H; subst x. exists [], w. now split.
  - destruct (IH n H) as [pre [tail [-> Hlen]]].
    exists (x :: pre), tail. simpl. split; [reflexivity|lia].
Qed.

Lemma tight_at_of_split {A : Type} (pre : list A) a tail :
  tight_at (length pre) (pre ++ a :: tail) = Some a.
Proof.
  induction pre as [|x pre IH]; simpl; [reflexivity|exact IH].
Qed.

Definition tight_no_x (w : list tight_symbol) : Prop := ~ In TLx w.

Lemma tight_at_map_seq {A : Type} (f : nat -> A) start len i : i < len ->
  tight_at i (map f (seq start len)) = Some (f (start + i)).
Proof.
  revert start i. induction len as [|len IH]; intros start [|i] Hi;
    simpl in *; try lia.
  - now rewrite Nat.add_0_r.
  - rewrite IH by lia.
    replace (start + S i) with (S start + i) by lia. reflexivity.
Qed.

Lemma tight_at_query k T i : i < k ->
  tight_at i (tight_query k T) =
    Some (if existsb (Nat.eqb i) T then TLx else TLe).
Proof.
  intro Hi. unfold tight_query. rewrite tight_at_map_seq by exact Hi.
  now rewrite Nat.add_0_l.
Qed.

Lemma tight_at_query_x_iff k T i : i < k ->
  (tight_at i (tight_query k T) = Some TLx <-> In i T).
Proof.
  intro Hi. rewrite tight_at_query by exact Hi.
  rewrite <- nat_mem_existsb.
  destruct (existsb (Nat.eqb i) T); simpl; split; intro H;
    try reflexivity; try discriminate.
Qed.

Lemma tight_query_core k T : tight_core_word (tight_query k T).
Proof.
  unfold tight_query, tight_core_word. apply Forall_forall.
  intros s Hs. apply in_map_iff in Hs as [i [<- _]].
  destruct (existsb (Nat.eqb i) T); [apply tight_core_x|apply tight_core_e].
Qed.

Lemma tight_phase_hit_core_hash k core :
  tight_core_word core ->
  (tight_phase_hit k (core ++ [TLhash]) <->
   exists n, n * k < length core /\ tight_at (n * k) core = Some TLx).
Proof.
  intro Hcore. split.
  - intros [n [pre [tail [Hlen [Hpre Hz]]]]].
    assert (Hat : tight_at (n * k) (core ++ [TLhash]) = Some TLx).
    { rewrite <- Hlen, Hz. apply tight_at_of_split. }
    assert (Hbound : n * k < length (core ++ [TLhash])).
    { apply (@tight_at_some_bound tight_symbol (n * k)
        (core ++ [TLhash]) TLx). exact Hat. }
    rewrite length_app in Hbound. simpl in Hbound.
    assert (Hlt : n * k < length core).
    { destruct (Nat.eq_dec (n * k) (length core)) as [Heq|Hneq]; [|lia].
      replace (n * k) with (length core + 0) in Hat by lia.
      rewrite tight_at_app_right in Hat. discriminate. }
    exists n. split; [exact Hlt|].
    rewrite (@tight_at_app_left tight_symbol (n * k) core [TLhash] Hlt)
      in Hat. exact Hat.
  - intros [n [Hlt Hat]].
    destruct (@tight_at_split tight_symbol (n * k) core TLx Hat)
      as [pre [tail [Hsplit Hlen]]].
    exists n, pre, (tail ++ [TLhash]). repeat split.
    + now rewrite Hlen.
    + subst core. apply (proj1 (tight_core_word_app _ _)) in Hcore.
      exact (proj1 Hcore).
    + subst core. now rewrite <- app_assoc.
Qed.

Lemma tight_multiple_offset_unique k base i j m n :
  0 < k -> i < k -> j < k ->
  base + i = m * k -> base + j = n * k -> i = j.
Proof.
  intros Hk Hi Hj Hmi Hnj.
  destruct (Nat.le_ge_cases i j) as [Hij|Hji].
  - assert (Hmn : m <= n).
    { apply (proj2 (Nat.mul_le_mono_pos_r m n k Hk)). lia. }
    assert (Hdiff : j = i + (n - m) * k).
    { rewrite Nat.mul_sub_distr_r. lia. }
    destruct (n - m) as [|q] eqn:Hq; simpl in Hdiff; lia.
  - assert (Hnm : n <= m).
    { apply (proj2 (Nat.mul_le_mono_pos_r n m k Hk)). lia. }
    assert (Hdiff : i = j + (m - n) * k).
    { rewrite Nat.mul_sub_distr_r. lia. }
    destruct (m - n) as [|q] eqn:Hq; simpl in Hdiff; lia.
Qed.

(** The phase-selection lemma.  [pre] may contain any number of complete
    records.  Its length equation says that query position [i] is the next
    position congruent to zero modulo [k]. *)
Lemma tight_phase_hit_aligned k pre T i m :
  0 < k -> i < k -> tight_core_word pre -> tight_no_x pre ->
  length pre + i = m * k ->
  (tight_phase_hit k (pre ++ tight_query k T ++ [TLhash]) <-> In i T).
Proof.
  intros Hk Hi Hcore Hnox Halign.
  replace (pre ++ tight_query k T ++ [TLhash]) with
    ((pre ++ tight_query k T) ++ [TLhash]) by
    (symmetry; apply app_assoc).
  rewrite (@tight_phase_hit_core_hash k (pre ++ tight_query k T)).
  2:{ apply (proj2 (tight_core_word_app _ _)).
      split; [exact Hcore|apply tight_query_core]. }
  split.
  - intros [n [Hbound Hat]].
    assert (Hnotleft : ~ n * k < length pre).
    { intro Hleft.
      rewrite (@tight_at_app_left tight_symbol (n * k) pre
        (tight_query k T) Hleft) in Hat.
      apply Hnox. now apply (@tight_at_in tight_symbol (n * k) pre TLx Hat). }
    assert (Hbase : length pre <= n * k) by lia.
    set (j := n * k - length pre).
    assert (Hdecomp : n * k = length pre + j) by (unfold j; lia).
    rewrite Hdecomp, tight_at_app_right in Hat.
    rewrite length_app, tight_query_length in Hbound.
    assert (Hj : j < k) by lia.
    assert (Hij : i = j).
    { eapply tight_multiple_offset_unique; eauto. }
    rewrite Hij. apply (proj1 (@tight_at_query_x_iff k T j Hj)). exact Hat.
  - intro Hin. exists m. split.
    + rewrite length_app, tight_query_length. lia.
    + rewrite <- Halign, tight_at_app_right.
      now apply (proj2 (@tight_at_query_x_iff k T i Hi)).
Qed.

Definition tight_bits_from start len (S : list nat) : list tight_symbol :=
  map (fun i => if existsb (Nat.eqb i) S then TLc else TLb)
    (seq start len).

Lemma tight_bits_from_zero k S : tight_bits_from 0 k S = tight_bits k S.
Proof. reflexivity. Qed.

Lemma tight_bits_from_succ start len subset :
  tight_bits_from start (S len) subset =
  (if existsb (Nat.eqb start) subset then TLc else TLb) ::
    tight_bits_from (S start) len subset.
Proof. reflexivity. Qed.

Lemma tight_bits_from_length start len S :
  length (tight_bits_from start len S) = len.
Proof. unfold tight_bits_from. now rewrite length_map, length_seq. Qed.

Lemma tight_bits_from_core start len S :
  tight_core_word (tight_bits_from start len S).
Proof.
  unfold tight_bits_from, tight_core_word. apply Forall_forall.
  intros s Hs. apply in_map_iff in Hs as [i [<- _]].
  destruct (existsb (Nat.eqb i) S); [apply tight_core_c|apply tight_core_b].
Qed.

Lemma tight_bits_from_no_x start len S :
  tight_no_x (tight_bits_from start len S).
Proof.
  unfold tight_no_x, tight_bits_from. intro H.
  apply in_map_iff in H as [i [H _]].
  destruct (existsb (Nat.eqb i) S); discriminate.
Qed.

Lemma tight_record_core k S : tight_core_word (tight_record k S).
Proof.
  unfold tight_record, tight_core_word. constructor; [apply tight_core_a|].
  apply Forall_app. split.
  - generalize (k - 2). intro n. induction n; simpl; constructor;
      auto using tight_core_e.
  - apply Forall_app. split.
    + rewrite <- tight_bits_from_zero. apply tight_bits_from_core.
    + constructor; [apply tight_core_d|constructor].
Qed.

Lemma tight_record_no_x k S : tight_no_x (tight_record k S).
Proof.
  unfold tight_no_x, tight_record. intro H. simpl in H.
  destruct H as [H|H]; [discriminate|].
  apply in_app_iff in H as [H|H].
  - apply repeat_spec in H. discriminate.
  - apply in_app_iff in H as [H|H].
    + rewrite <- tight_bits_from_zero in H.
      now apply (tight_bits_from_no_x 0 k S).
    + simpl in H. destruct H as [H|[]]. discriminate.
Qed.

Lemma tight_family_prefix_core k F :
  tight_core_word (tight_family_prefix k F).
Proof.
  induction F as [|S F IH]; simpl; [constructor|].
  change (tight_core_word (tight_record k S ++ tight_family_prefix k F)).
  apply (proj2 (tight_core_word_app _ _)).
  split; [apply tight_record_core|exact IH].
Qed.

Lemma tight_family_prefix_no_x k F :
  tight_no_x (tight_family_prefix k F).
Proof.
  induction F as [|S F IH]; simpl.
  - unfold tight_no_x. tauto.
  - change (tight_no_x (tight_record k S ++ tight_family_prefix k F)).
    unfold tight_no_x in *. rewrite in_app_iff. intros [H|H].
    + now apply (@tight_record_no_x k S).
    + now apply IH.
Qed.

Lemma tight_family_prefix_length k F : 2 <= k ->
  length (tight_family_prefix k F) = length F * (2 * k).
Proof.
  intro Hk. induction F as [|subset F IH]; simpl; [reflexivity|].
  change (length (tight_record k subset ++ tight_family_prefix k F) =
    S (length F) * (2 * k)).
  rewrite length_app, tight_record_length by exact Hk. rewrite IH. lia.
Qed.

Lemma tight_bits_accept_from k start len subset F T :
  2 <= k -> start + len = k ->
  (tight_bits_accept k (tight_bits_from start len subset)
      ([TLd] ++ tight_family_prefix k F ++ tight_test k T) <->
   forall i, In i (seq start len) -> In i subset -> In i T).
Proof.
  intros Hk Hsum. revert start Hsum.
  induction len as [|len IH]; intros start Hsum.
  - cbn [tight_bits_from]. split.
    + intros _. intros i Hi _. inversion Hi.
    + intros _. exact I.
  - rewrite tight_bits_from_succ. simpl tight_bits_accept.
    assert (Hpos : 0 < k) by lia.
    assert (Hstart : start < k) by lia.
    set (rest := tight_bits_from (S start) len subset).
    set (pre := rest ++ [TLd] ++ tight_family_prefix k F).
    assert (Hprecore : tight_core_word pre).
    { unfold pre. apply (proj2 (tight_core_word_app _ _)). split.
      - unfold rest. apply tight_bits_from_core.
      - constructor; [apply tight_core_d|].
        apply tight_family_prefix_core. }
    assert (Hprenox : tight_no_x pre).
    { unfold tight_no_x, pre. rewrite in_app_iff. intros [Hx|Hx].
      - unfold rest in Hx. now apply (tight_bits_from_no_x (S start) len subset).
      - simpl in Hx. destruct Hx as [Hx|Hx]; [discriminate|].
        now apply (@tight_family_prefix_no_x k F). }
    assert (Hprelen : length pre + start =
        (1 + 2 * length F) * k).
    { unfold pre, rest. rewrite !length_app, tight_bits_from_length.
      rewrite tight_family_prefix_length by exact Hk. simpl. nia. }
    assert (Hphase :
      tight_phase_hit k
        (rest ++ ([TLd] ++ tight_family_prefix k F ++ tight_test k T)) <->
      In start T).
    { replace
        (rest ++ ([TLd] ++ tight_family_prefix k F ++ tight_test k T))
        with (pre ++ tight_query k T ++ [TLhash]).
      - eapply tight_phase_hit_aligned; eauto.
      - unfold pre, tight_test. now rewrite !app_assoc. }
    rewrite Hphase.
    assert (Htail :
      tight_bits_accept k rest
        ([TLd] ++ tight_family_prefix k F ++ tight_test k T) <->
      forall i, In i (seq (S start) len) -> In i subset -> In i T).
    { unfold rest. apply IH. lia. }
    rewrite Htail. simpl seq.
    destruct (existsb (Nat.eqb start) subset) eqn:Hmem; simpl.
    + assert (Hstartmem : In start subset).
      { apply nat_mem_existsb. exact Hmem. }
      split.
      * intros [Hchoice Hrest] i [<-|Hi] His.
        -- destruct Hchoice as [Hbad|[_ HstartT]];
             [discriminate|exact HstartT].
        -- now apply Hrest.
      * intro Hall. split.
        -- right. split; [reflexivity|].
           apply Hall; [now left|exact Hstartmem].
        -- intros i Hi His. apply Hall; [now right|exact His].
    + assert (Hstartnot : ~ In start subset).
      { intro Hin. apply nat_mem_existsb in Hin. congruence. }
      split.
      * intros [_ Hrest] i [<-|Hi] His.
        -- contradiction.
        -- now apply Hrest.
      * intro Hall. split; [now left|].
        intros i Hi His. apply Hall; [now right|exact His].
Qed.

Theorem tight_bits_accept_characterization k subset F T : 2 <= k ->
  (tight_bits_accept k (tight_bits k subset)
      ([TLd] ++ tight_family_prefix k F ++ tight_test k T) <->
   forall i, i < k -> In i subset -> In i T).
Proof.
  intro Hk. rewrite <- tight_bits_from_zero.
  rewrite (@tight_bits_accept_from k 0 k subset F T Hk) by lia.
  split.
  - intros H i Hi His. apply H; [apply in_seq; lia|exact His].
  - intros H i Hi His. apply H; [apply in_seq in Hi; lia|exact His].
Qed.

Lemma matches_tight_core_star w :
  matches (Star tight_core_regex) w <-> tight_core_word w.
Proof.
  split.
  - intro H. remember (Star tight_core_regex) as sr eqn:Hsr in H.
    induction H; inversion Hsr; subst.
    + constructor.
    + apply (proj2 (tight_core_word_app _ _)). split.
      * apply matches_tight_core_regex in H0 as [a [Ha ->]].
        constructor; [exact Ha|constructor].
      * apply IHmatches2. reflexivity.
  - intro H. induction H as [|a w Ha Hw IH].
    + constructor.
    + change (matches (Star tight_core_regex) ([a] ++ w)).
      apply M_StarApp.
      * discriminate.
      * apply matches_tight_core_regex. exists a. now split.
      * exact IH.
Qed.

Lemma matches_e_star w :
  matches (Star (Atom TLe)) w <-> Forall (eq TLe) w.
Proof.
  split.
  - intro H. remember (Star (Atom TLe)) as sr eqn:Hsr in H.
    induction H; inversion Hsr; subst.
    + constructor.
    + match goal with Ha : matches (Atom TLe) ?u |- _ =>
        inversion Ha; subst u
      end.
      constructor; [reflexivity|]. apply IHmatches2. reflexivity.
  - intro H. induction H as [|a w Ha Hw IH].
    + constructor.
    + subst a. change (matches (Star (Atom TLe)) ([TLe] ++ w)).
      apply M_StarApp; [discriminate|constructor|exact IH].
Qed.

(** A syntax-directed characterization of the complete witness.  It keeps
    the continuation seen by the factor star explicit; this is what later
    connects the outer parser to [tight_bits_accept_characterization]. *)
Theorem tight_expression_suffix_characterization k full z :
  suffix_satisfies tight_symbol_eqb (tight_expression k) full z <->
  exists pre pad bits core,
    full = pre ++ [TLa] ++ pad ++ bits ++ [TLd] ++ core ++ [TLhash] /\
    tight_core_word pre /\ Forall (eq TLe) pad /\ tight_core_word core /\
    suffix_satisfies tight_symbol_eqb (WStar (tight_factor k)) bits
      ([TLd] ++ core ++ [TLhash] ++ z).
Proof.
  unfold tight_expression.
  rewrite (suffix_satisfies_concat tight_symbol_eqb tight_symbol_eqb_spec).
  split.
  - intros [pre [r1 [Hfull [Hpre Hr1]]]].
    apply (proj1 (suffix_satisfies_concat tight_symbol_eqb
      tight_symbol_eqb_spec _ _ _ _)) in Hr1.
    destruct Hr1 as [a [r2 [Hr1 [Ha Hr2]]]].
    apply (proj1 (suffix_satisfies_concat tight_symbol_eqb
      tight_symbol_eqb_spec _ _ _ _)) in Hr2.
    destruct Hr2 as [pad [r3 [Hr2 [Hpad Hr3]]]].
    apply (proj1 (suffix_satisfies_concat tight_symbol_eqb
      tight_symbol_eqb_spec _ _ _ _)) in Hr3.
    destruct Hr3 as [bits [r4 [Hr3 [Hbits Hr4]]]].
    apply (proj1 (suffix_satisfies_concat tight_symbol_eqb
      tight_symbol_eqb_spec _ _ _ _)) in Hr4.
    destruct Hr4 as [d [r5 [Hr4 [Hd Hr5]]]].
    apply (proj1 (suffix_satisfies_concat tight_symbol_eqb
      tight_symbol_eqb_spec _ _ _ _)) in Hr5.
    destruct Hr5 as [core [h [Hr5 [Hcore Hh]]]].
    apply (suffix_satisfies_embed tight_symbol_eqb tight_symbol_eqb_spec)
      in Hpre. apply matches_tight_core_star in Hpre.
    apply suffix_satisfies_atom in Ha. subst a.
    apply (suffix_satisfies_embed tight_symbol_eqb tight_symbol_eqb_spec)
      in Hpad. apply matches_e_star in Hpad.
    apply suffix_satisfies_atom in Hd. subst d.
    apply (suffix_satisfies_embed tight_symbol_eqb tight_symbol_eqb_spec)
      in Hcore. apply matches_tight_core_star in Hcore.
    apply suffix_satisfies_atom in Hh. subst h.
    subst r1 r2 r3 r4 r5 full.
    exists pre, pad, bits, core. repeat split; try assumption;
      now rewrite !app_assoc.
  - intros [pre [pad [bits [core
      [Hfull [Hpre [Hpad [Hcore Hbits]]]]]]]].
    exists pre, ([TLa] ++ pad ++ bits ++ [TLd] ++ core ++ [TLhash]).
    split; [exact Hfull|]. split.
    + apply (suffix_satisfies_embed tight_symbol_eqb tight_symbol_eqb_spec),
        matches_tight_core_star. exact Hpre.
    + apply (proj2 (suffix_satisfies_concat tight_symbol_eqb
        tight_symbol_eqb_spec _ _ _ _)).
      exists [TLa], (pad ++ bits ++ [TLd] ++ core ++ [TLhash]).
      split; [reflexivity|]. split.
      * apply suffix_satisfies_atom. reflexivity.
      * apply (proj2 (suffix_satisfies_concat tight_symbol_eqb
          tight_symbol_eqb_spec _ _ _ _)).
        exists pad, (bits ++ [TLd] ++ core ++ [TLhash]).
        split; [reflexivity|]. split.
        -- apply (suffix_satisfies_embed tight_symbol_eqb
             tight_symbol_eqb_spec), matches_e_star. exact Hpad.
        -- apply (proj2 (suffix_satisfies_concat tight_symbol_eqb
             tight_symbol_eqb_spec _ _ _ _)).
           exists bits, ([TLd] ++ core ++ [TLhash]).
           split; [reflexivity|]. split.
           ++ replace (([TLd] ++ core ++ [TLhash]) ++ z) with
                ([TLd] ++ core ++ [TLhash] ++ z) by
                (rewrite !app_assoc; reflexivity).
              exact Hbits.
           ++
           apply (proj2 (suffix_satisfies_concat tight_symbol_eqb
             tight_symbol_eqb_spec _ _ _ _)).
           exists [TLd], (core ++ [TLhash]). split; [reflexivity|]. split.
           { apply suffix_satisfies_atom. reflexivity. }
           { apply (proj2 (suffix_satisfies_concat tight_symbol_eqb
               tight_symbol_eqb_spec _ _ _ _)).
             exists core, [TLhash]. split; [reflexivity|]. split.
             - apply (suffix_satisfies_embed tight_symbol_eqb
                 tight_symbol_eqb_spec), matches_tight_core_star.
               exact Hcore.
             - apply suffix_satisfies_atom. reflexivity. }
Qed.

Lemma tight_core_word_no_hash w :
  tight_core_word w -> ~ In TLhash w.
Proof.
  intros Hcore Hin. unfold tight_core_word in Hcore.
  apply Forall_forall with (x:=TLhash) in Hcore; [|exact Hin].
  now apply tight_core_not_hash.
Qed.

Lemma tight_full_core k F T :
  tight_core_word (tight_family_prefix k F ++ tight_query k T).
Proof.
  apply (proj2 (tight_core_word_app _ _)).
  split; [apply tight_family_prefix_core|apply tight_query_core].
Qed.

Lemma tight_full_no_hash k F T :
  ~ In TLhash (tight_family_prefix k F ++ tight_query k T).
Proof. apply tight_core_word_no_hash, tight_full_core. Qed.

Lemma tight_denote_implies_suffix r u v :
  rewpla_denote tight_symbol_eqb r (u,v) ->
  suffix_satisfies tight_symbol_eqb r u v.
Proof. intro H. exists v. split; [exact H|apply word_prefix_refl]. Qed.

Theorem tight_expression_projected_exact k F T :
  rewpla_language tight_symbol_eqb (tight_expression k)
      (tight_family_prefix k F ++ tight_test k T) <->
  rewpla_denote tight_symbol_eqb (tight_expression k)
      (tight_family_prefix k F ++ tight_test k T, []).
Proof.
  unfold rewpla_language, project_language. split.
  - intros [[u v] [Hden Hproj]].
    pose proof (tight_denote_implies_suffix
      (tight_expression k) u v Hden) as Hsat.
    apply tight_expression_suffix_characterization in Hsat
      as [pre [pad [bits [core [Hu _]]]]].
    assert (Huend : exists before, u = before ++ [TLhash]).
    { subst u. exists (pre ++ [TLa] ++ pad ++ bits ++ [TLd] ++ core).
      now rewrite !app_assoc. }
    unfold tight_test in Hproj. rewrite app_assoc in Hproj.
    destruct (@ending_marker_prefix_unique tight_symbol TLhash
      (tight_family_prefix k F ++ tight_query k T) u v
      (tight_full_no_hash k F T) Hproj Huend) as [-> ->].
    replace (tight_family_prefix k F ++ tight_test k T)
      with ((tight_family_prefix k F ++ tight_query k T) ++ [TLhash]).
    + exact Hden.
    + unfold tight_test. symmetry. apply app_assoc.
  - intro Hden. exists (tight_family_prefix k F ++ tight_test k T, []).
    split; [exact Hden|]. unfold constraint_projection. simpl.
    now rewrite app_nil_r.
Qed.

Lemma tight_suffix_satisfies_empty_exact r u :
  suffix_satisfies tight_symbol_eqb r u [] <->
  rewpla_denote tight_symbol_eqb r (u, []).
Proof.
  unfold suffix_satisfies, constraint_expansion. simpl. split.
  - intros [v [H [tail Heq]]]. symmetry in Heq.
    apply app_eq_nil in Heq as [-> ->]. exact H.
  - intro H. exists []. split; [exact H|apply word_prefix_refl].
Qed.

Lemma tight_family_prefix_app k F G :
  tight_family_prefix k (F ++ G) =
  tight_family_prefix k F ++ tight_family_prefix k G.
Proof.
  induction F as [|S F IH]; simpl; [reflexivity|].
  now rewrite IH, app_assoc.
Qed.

Lemma tight_bits_from_no_a start len S :
  ~ In TLa (tight_bits_from start len S).
Proof.
  unfold tight_bits_from. intro H. apply in_map_iff in H as [i [H _]].
  destruct (existsb (Nat.eqb i) S); discriminate.
Qed.

Lemma tight_bits_from_no_d start len S :
  ~ In TLd (tight_bits_from start len S).
Proof.
  unfold tight_bits_from. intro H. apply in_map_iff in H as [i [H _]].
  destruct (existsb (Nat.eqb i) S); discriminate.
Qed.

Lemma tight_bits_from_no_e start len S :
  ~ In TLe (tight_bits_from start len S).
Proof.
  unfold tight_bits_from. intro H. apply in_map_iff in H as [i [H _]].
  destruct (existsb (Nat.eqb i) S); discriminate.
Qed.

Lemma tight_record_payload_no_a k S :
  ~ In TLa (repeat TLe (k - 2) ++ tight_bits k S ++ [TLd]).
Proof.
  rewrite !in_app_iff. intros [H|[H|H]].
  - apply repeat_spec in H. discriminate.
  - rewrite <- tight_bits_from_zero in H.
    now apply (tight_bits_from_no_a 0 k S).
  - simpl in H. destruct H as [H|[]]. discriminate.
Qed.

Lemma tight_test_no_a k T : ~ In TLa (tight_test k T).
Proof.
  unfold tight_test, tight_query. rewrite in_app_iff. intros [H|H].
  - apply in_map_iff in H as [i [H _]].
    destruct (existsb (Nat.eqb i) T); discriminate.
  - simpl in H. destruct H as [H|[]]. discriminate.
Qed.

(** Locate the record selected by the leading [U* a]. *)
Theorem tight_family_record_parser k F T pre body :
  tight_family_prefix k F ++ tight_test k T = pre ++ TLa :: body ->
  exists before S after,
    F = before ++ S :: after /\
    pre = tight_family_prefix k before /\
    body = repeat TLe (k - 2) ++ tight_bits k S ++
      TLd :: (tight_family_prefix k after ++ tight_test k T).
Proof.
  revert pre body. induction F as [|S F IH]; intros pre body Heq.
  - simpl in Heq. exfalso. apply (tight_test_no_a k T).
    rewrite Heq. apply in_app_iff. right. now left.
  - change
      (((TLa :: (repeat TLe (k - 2) ++ tight_bits k S ++ [TLd])) ++
        tight_family_prefix k F) ++ tight_test k T =
       pre ++ TLa :: body) in Heq.
    destruct pre as [|p pre].
    + simpl in Heq. injection Heq as Hbody.
      exists [], S, F. simpl. repeat split; try reflexivity.
      rewrite <- !app_assoc in Hbody. simpl in Hbody. symmetry. exact Hbody.
    + simpl in Heq. injection Heq as Hp Htail. subst p.
      destruct (no_marker_split TLa
        (repeat TLe (k - 2) ++ tight_bits k S ++ [TLd])
        (tight_family_prefix k F ++ tight_test k T)
        pre body) as [pre' [Hpre Hrest]].
      * apply tight_record_payload_no_a.
      * now rewrite <- app_assoc in Htail.
      * destruct (IH pre' body Hrest)
          as [before [S' [after [HF [Hpre' Hbody]]]]].
        exists (S :: before), S', after. repeat split.
        -- simpl. now rewrite HF.
        -- simpl. rewrite Hpre, Hpre'. reflexivity.
        -- exact Hbody.
Qed.

Lemma tight_bits_accept_symbols k bits z :
  tight_bits_accept k bits z ->
  Forall (fun s => s = TLb \/ s = TLc) bits.
Proof.
  revert z. induction bits as [|s bits IH]; intros z H; simpl in *.
  - constructor.
  - destruct H as [Hs Htail]. constructor.
    + destruct Hs as [->|[-> _]]; auto.
    + now apply (IH z).
Qed.

Lemma tight_bits_accept_no_e k bits z :
  tight_bits_accept k bits z -> ~ In TLe bits.
Proof.
  intros Hacc Hin. pose proof (@tight_bits_accept_symbols k bits z Hacc) as Hall.
  apply Forall_forall with (x:=TLe) in Hall; [|exact Hin].
  destruct Hall; discriminate.
Qed.

Lemma tight_bits_accept_no_d k bits z :
  tight_bits_accept k bits z -> ~ In TLd bits.
Proof.
  intros Hacc Hin. pose proof (@tight_bits_accept_symbols k bits z Hacc) as Hall.
  apply Forall_forall with (x:=TLd) in Hall; [|exact Hin].
  destruct Hall; discriminate.
Qed.

Lemma marker_split_unique {A : Type} (marker : A) xs ys r s :
  ~ In marker xs -> ~ In marker ys ->
  xs ++ marker :: r = ys ++ marker :: s -> xs = ys /\ r = s.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hx Hy Heq;
    simpl in *.
  - inversion Heq. now split.
  - inversion Heq; subst y. exfalso. apply Hy. now left.
  - inversion Heq; subst x. exfalso. apply Hx. now left.
  - inversion Heq; subst y. destruct (IH ys) as [Hxy Hrs].
    + intro Hin. apply Hx. now right.
    + intro Hin. apply Hy. now right.
    + exact H1.
    + subst ys. now split.
Qed.

Lemma e_prefix_decomposition_unique p q xs ys :
  Forall (eq TLe) p -> Forall (eq TLe) q ->
  Forall (fun s => s <> TLe) xs -> Forall (fun s => s <> TLe) ys ->
  xs <> [] -> p ++ xs = q ++ ys -> p = q /\ xs = ys.
Proof.
  revert q. induction p as [|a p IH]; intros q Hp Hq Hxs Hys Hne Heq.
  - inversion Hp; subst. destruct q as [|b q].
    + simpl in Heq. subst ys. now split.
    + inversion Hq as [|? ? Hb Hq']; subst b. simpl in Heq.
      destruct xs as [|x0 xs]; [contradiction|].
      inversion Heq; subst x0. inversion Hxs as [|? ? Hxe _].
      contradiction.
  - inversion Hp as [|? ? Ha Hp']; subst a. destruct q as [|b q].
    + simpl in Heq. destruct ys as [|y ys]; [discriminate|].
      inversion Heq; subst y. inversion Hys as [|? ? Hye _].
      contradiction.
    + inversion Hq as [|? ? Hb Hq']; subst b. simpl in Heq.
      injection Heq as Htail.
      destruct (IH q Hp' Hq' Hxs Hys Hne Htail) as [-> ->].
      now split.
Qed.

Lemma repeat_e_forall n : Forall (eq TLe) (repeat TLe n).
Proof. induction n; simpl; constructor; auto. Qed.

Lemma tight_bits_forall_not_e k S :
  Forall (fun s => s <> TLe) (tight_bits k S).
Proof.
  apply Forall_forall. intros s Hin Heq. subst s.
  rewrite <- tight_bits_from_zero in Hin.
  now apply (tight_bits_from_no_e 0 k S).
Qed.

Lemma tight_bits_forall_not_d k S :
  Forall (fun s => s <> TLd) (tight_bits k S).
Proof.
  apply Forall_forall. intros s Hin Heq. subst s.
  rewrite <- tight_bits_from_zero in Hin.
  now apply (tight_bits_from_no_d 0 k S).
Qed.

Lemma forall_eq_no_d pad : Forall (eq TLe) pad -> ~ In TLd pad.
Proof.
  intros Hall Hin. apply Forall_forall with (x:=TLd) in Hall;
    [discriminate|exact Hin].
Qed.

Lemma forall_app_not_d u v :
  Forall (fun s : tight_symbol => s <> TLd) u ->
  Forall (fun s => s <> TLd) v -> ~ In TLd (u ++ v).
Proof.
  intros Hu Hv. rewrite in_app_iff. intros [Hin|Hin].
  - apply Forall_forall with (x:=TLd) in Hu; [contradiction|exact Hin].
  - apply Forall_forall with (x:=TLd) in Hv; [contradiction|exact Hin].
Qed.

Lemma tight_record_word_reassociate b pad bits rest query :
  (b ++ (TLa :: (pad ++ bits ++ [TLd])) ++ rest) ++
      (query ++ [TLhash]) =
  b ++ [TLa] ++ pad ++ bits ++ [TLd] ++
      (rest ++ query) ++ [TLhash].
Proof.
  induction b as [|x b IHb]; simpl.
  - f_equal. induction pad as [|p pad IHpad]; simpl.
    + induction bits as [|q bits IHbits]; simpl.
      * f_equal. apply app_assoc.
      * now f_equal.
    + now f_equal.
  - now f_equal.
Qed.

(** Central membership lemma: a family word is accepted exactly when one of
    its encoded middle-layer sets is included in the query set. *)
Theorem tight_bound_membership k F T :
  2 <= k -> valid_middle_family k F -> valid_middle_set k T ->
  (rewpla_language tight_symbol_eqb (tight_expression k)
      (tight_family_prefix k F ++ tight_test k T) <->
   exists S, In S F /\ incl S T).
Proof.
  intros Hk HF HT. rewrite tight_expression_projected_exact.
  rewrite <- tight_suffix_satisfies_empty_exact.
  rewrite tight_expression_suffix_characterization. split.
  - intros [pre [pad [bits [core
      [Hfull [Hpre [Hpad [Hcore Hstar]]]]]]]].
    simpl in Hstar.
    apply (proj1 (@tight_factor_star_satisfies k bits
      ([TLd] ++ core ++ [TLhash]) ltac:(lia))) in Hstar.
    assert (Hloc :
      tight_family_prefix k F ++ tight_test k T =
      pre ++ TLa :: (pad ++ bits ++ TLd :: (core ++ [TLhash]))).
    { rewrite Hfull. simpl. now rewrite !app_assoc. }
    destruct (tight_family_record_parser k F T pre
      (pad ++ bits ++ TLd :: (core ++ [TLhash])) Hloc)
      as [before [S [after [HFsplit [HpreEq Hbody]]]]].
    assert (Hchosen : In S F).
    { rewrite HFsplit. apply in_app_iff. right. now left. }
    assert (HleftNoD : ~ In TLd (pad ++ bits)).
    { rewrite in_app_iff. intros [Hin|Hin].
      - now apply (forall_eq_no_d Hpad).
      - now apply (@tight_bits_accept_no_d k bits
          ([TLd] ++ core ++ [TLhash]) Hstar). }
    assert (HrightNoD :
      ~ In TLd (repeat TLe (k - 2) ++ tight_bits k S)).
    { apply forall_app_not_d.
      - apply Forall_forall. intros s Hin ->.
        apply repeat_spec in Hin. discriminate.
      - apply tight_bits_forall_not_d. }
    assert (Hmarker :
      (pad ++ bits) ++ TLd :: (core ++ [TLhash]) =
      (repeat TLe (k - 2) ++ tight_bits k S) ++
        TLd :: (tight_family_prefix k after ++ tight_test k T)).
    { rewrite (app_assoc pad bits
        (TLd :: (core ++ [TLhash]))) in Hbody.
      rewrite (app_assoc (repeat TLe (k - 2)) (tight_bits k S)
        (TLd :: (tight_family_prefix k after ++ tight_test k T))) in Hbody.
      exact Hbody. }
    destruct (marker_split_unique TLd
      (pad ++ bits) (repeat TLe (k - 2) ++ tight_bits k S)
      (core ++ [TLhash])
      (tight_family_prefix k after ++ tight_test k T)
      HleftNoD HrightNoD Hmarker) as [Hbefore Hafter].
    assert (HbitsNoE : Forall (fun s => s <> TLe) bits).
    { apply Forall_forall. intros s Hin ->.
      now apply (@tight_bits_accept_no_e k bits
        ([TLd] ++ core ++ [TLhash]) Hstar). }
    assert (HbitsNonempty : tight_bits k S <> []).
    { intro Hnil. pose proof (tight_bits_length k S).
      rewrite Hnil in H. simpl in H. lia. }
    destruct (@e_prefix_decomposition_unique
      (repeat TLe (k - 2)) pad (tight_bits k S) bits
      (repeat_e_forall (k - 2)) Hpad
      (tight_bits_forall_not_e k S) HbitsNoE HbitsNonempty
      (eq_sym Hbefore)) as [_ HbitsEq].
    assert (HcoreEq : core = tight_family_prefix k after ++ tight_query k T).
    { unfold tight_test in Hafter.
      rewrite app_assoc in Hafter. now apply app_inv_tail in Hafter. }
    subst bits core.
    exists S. split; [exact Hchosen|].
    replace
      ([TLd] ++ (tight_family_prefix k after ++ tight_query k T) ++ [TLhash])
      with ([TLd] ++ tight_family_prefix k after ++ tight_test k T)
      in Hstar by (unfold tight_test; now rewrite <- app_assoc).
    pose proof (proj1 (@tight_bits_accept_characterization
      k S after T Hk) Hstar) as Hacc.
    intros i Hi. apply Hacc.
    + eapply valid_middle_set_range; [apply HF; exact Hchosen|exact Hi].
    + exact Hi.
  - intros [S [HS HST]]. apply in_split in HS as [before [after HFsplit]].
    subst F.
    set (pre := tight_family_prefix k before).
    set (pad := repeat TLe (k - 2)).
    set (bits := tight_bits k S).
    set (core := tight_family_prefix k after ++ tight_query k T).
    exists pre, pad, bits, core. repeat split.
    + unfold pre, pad, bits, core, tight_test.
      rewrite tight_family_prefix_app. cbn [tight_family_prefix tight_record].
      apply tight_record_word_reassociate.
    + unfold pre. apply tight_family_prefix_core.
    + unfold pad. apply repeat_e_forall.
    + unfold core. apply (proj2 (tight_core_word_app _ _)).
      split; [apply tight_family_prefix_core|apply tight_query_core].
    + apply (proj2 (@tight_factor_star_satisfies k bits
        ([TLd] ++ core ++ [TLhash]) ltac:(lia))).
      unfold bits, core.
      replace
        ([TLd] ++ (tight_family_prefix k after ++ tight_query k T) ++ [TLhash])
        with ([TLd] ++ tight_family_prefix k after ++ tight_test k T)
        by (unfold tight_test; now rewrite <- app_assoc).
      apply (proj2 (@tight_bits_accept_characterization k S after T Hk)).
      intros i Hi HiS. now apply HST.
Qed.

Definition tight_prefixes k : list (list tight_symbol) :=
  map (tight_family_prefix k) (lower_bound_families k).

Lemma tight_families_language_separated k F G :
  2 <= k ->
  In F (lower_bound_families k) -> In G (lower_bound_families k) ->
  F <> G ->
  language_separated
    (rewpla_language tight_symbol_eqb (tight_expression k))
    (tight_family_prefix k F) (tight_family_prefix k G).
Proof.
  intros Hk HF HG Hneq.
  pose proof (@lower_bound_family_valid k F HF) as HFvalid.
  pose proof (@lower_bound_family_valid k G HG) as HGvalid.
  destruct (@distinct_lower_bound_families_differ k F G HF HG Hneq)
    as [S [[HSF HnSG]|[HnSF HSG]]].
  - assert (HS : valid_middle_set k S) by now apply HFvalid.
    exists (tight_test k S). left. split.
    + apply (proj2 (@tight_bound_membership k F S Hk HFvalid HS)).
      exists S. split; [exact HSF|apply incl_refl].
    + intro Haccept.
      apply (proj1 (@tight_bound_membership k G S Hk HGvalid HS)) in Haccept.
      destruct Haccept as [U [HUG HUS]]. apply HnSG.
      pose proof (HGvalid U HUG) as HU.
      assert (U = S) by
        now apply (@valid_middle_inclusion_equal k U S HU HS HUS).
      now subst U.
  - assert (HS : valid_middle_set k S) by now apply HGvalid.
    exists (tight_test k S). right. split.
    + intro Haccept.
      apply (proj1 (@tight_bound_membership k F S Hk HFvalid HS)) in Haccept.
      destruct Haccept as [U [HUF HUS]]. apply HnSF.
      pose proof (HFvalid U HUF) as HU.
      assert (U = S) by
        now apply (@valid_middle_inclusion_equal k U S HU HS HUS).
      now subst U.
    + apply (proj2 (@tight_bound_membership k G S Hk HGvalid HS)).
      exists S. split; [exact HSG|apply incl_refl].
Qed.

Lemma tight_prefixes_separated_aux k fs :
  2 <= k -> incl fs (lower_bound_families k) -> NoDup fs ->
  prefixes_separated
    (rewpla_language tight_symbol_eqb (tight_expression k))
    (map (tight_family_prefix k) fs).
Proof.
  intros Hk Hin Hnd. induction fs as [|F fs IH]; simpl; [exact I|].
  inversion Hnd as [|? ? Hnot Htail]; subst. split.
  - intros v Hv. apply in_map_iff in Hv as [G [<- HG]].
    apply tight_families_language_separated; try assumption.
    + apply Hin. now left.
    + apply Hin. now right.
    + intro Heq. subst G. contradiction.
  - apply IH.
    + intros G HG. apply Hin. now right.
    + exact Htail.
Qed.

Theorem tight_prefixes_separated k : 2 <= k ->
  prefixes_separated
    (rewpla_language tight_symbol_eqb (tight_expression k))
    (tight_prefixes k).
Proof.
  intro Hk. unfold tight_prefixes. apply tight_prefixes_separated_aux.
  - exact Hk.
  - apply incl_refl.
  - apply lower_bound_families_nodup.
Qed.

(** Exact derivative lower bound for an expression of width [6*k+19]. *)
Theorem tight_expression_derivative_lower_bound k : 2 <= k ->
  exists derivatives : list (rewpla tight_symbol),
    length derivatives = 2 ^ binomial k (k / 2) /\
    projected_distinct tight_symbol_eqb derivatives /\
    semantic_distinct tight_symbol_eqb derivatives /\
    semantic_reachable tight_symbol_eqb (tight_expression k) derivatives.
Proof.
  intro Hk.
  destruct (@separated_prefixes_derivative_count tight_symbol
      tight_symbol_eqb tight_symbol_eqb_spec (tight_expression k)
      (tight_prefixes k) (@tight_prefixes_separated k Hk))
    as [ds [Hlen [Hprojected [Hsemantic Hreachable]]]].
  exists ds. repeat split; try assumption.
  rewrite Hlen. unfold tight_prefixes. rewrite length_map.
  apply lower_bound_families_length.
Qed.

(** Myhill--Nerode form: every finite deterministic recognizer has at least
    [2^(binomial k (floor(k/2)))] states. *)
Theorem tight_expression_finite_dfa_lower_bound k (Q : Type)
    (step : Q -> tight_symbol -> Q) initial final states :
  2 <= k ->
  deterministic_recognizes step initial final
    (rewpla_language tight_symbol_eqb (tight_expression k)) ->
  (forall w, In (deterministic_run step initial w) states) ->
  2 ^ binomial k (k / 2) <= length states.
Proof.
  intros Hk Hrecognizes Hstates.
  pose proof (@separated_prefixes_finite_dfa_lower_bound tight_symbol Q
    step initial final
    (rewpla_language tight_symbol_eqb (tight_expression k))
    (tight_prefixes k) states Hrecognizes Hstates
    (@tight_prefixes_separated k Hk)) as Hbound.
  unfold tight_prefixes in Hbound. rewrite length_map,
    lower_bound_families_length in Hbound. exact Hbound.
Qed.

Print Assumptions tight_expression_width.
Print Assumptions tight_phase_hit_aligned.
Print Assumptions tight_bound_membership.
Print Assumptions tight_expression_derivative_lower_bound.
Print Assumptions tight_expression_finite_dfa_lower_bound.
