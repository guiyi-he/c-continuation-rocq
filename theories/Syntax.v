From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Set Implicit Arguments.

Inductive regex (A : Type) : Type :=
| Zero
| Eps
| Atom (a : A)
| Plus (r s : regex A)
| Concat (r s : regex A)
| Star (r : regex A).

Arguments Zero {A}.
Arguments Eps {A}.
Arguments Atom {A} _.
Arguments Plus {A} _ _.
Arguments Concat {A} _ _.
Arguments Star {A} _.

Fixpoint nullable {A} (r : regex A) : bool :=
  match r with
  | Zero | Atom _ => false
  | Eps | Star _ => true
  | Plus r s => nullable r || nullable s
  | Concat r s => nullable r && nullable s
  end.

Fixpoint alphabetic_width {A} (r : regex A) : nat :=
  match r with
  | Zero | Eps => 0
  | Atom _ => 1
  | Plus r s | Concat r s => alphabetic_width r + alphabetic_width s
  | Star r => alphabetic_width r
  end.

Fixpoint regex_eqb {A} (eqb : A -> A -> bool) (r s : regex A) : bool :=
  match r, s with
  | Zero, Zero | Eps, Eps => true
  | Atom a, Atom b => eqb a b
  | Plus a b, Plus c d | Concat a b, Concat c d =>
      regex_eqb eqb a c && regex_eqb eqb b d
  | Star a, Star b => regex_eqb eqb a b
  | _, _ => false
  end.

Lemma regex_eqb_spec {A} (eqb : A -> A -> bool)
  (Heq : forall x y, eqb x y = true <-> x = y) :
  forall r s, regex_eqb eqb r s = true <-> r = s.
Proof.
  induction r; destruct s; simpl; try (split; intro H; [discriminate|congruence]).
  - tauto.
  - tauto.
  - split.
    + intro H. apply Heq in H. now subst.
    + intro H. inversion H; subst. apply Heq. reflexivity.
  - rewrite andb_true_iff, IHr1, IHr2. split.
    + intros [H1 H2]. now subst.
    + intro H; inversion H; subst; auto.
  - rewrite andb_true_iff, IHr1, IHr2. split.
    + intros [H1 H2]. now subst.
    + intro H; inversion H; subst; auto.
  - rewrite IHr. split; intro H; [now subst|now inversion H].
Qed.

Definition is_zero {A} (r : regex A) : bool :=
  match r with Zero => true | _ => false end.

Definition smart_plus {A} (r s : regex A) : regex A :=
  match r, s with Zero, x => x | x, Zero => x | _, _ => Plus r s end.

Definition smart_concat {A} (r s : regex A) : regex A :=
  match r, s with
  | Zero, _ | _, Zero => Zero
  | Eps, x => x
  | x, Eps => x
  | _, _ => Concat r s
  end.

Inductive matches {A} : regex A -> list A -> Prop :=
| M_Eps : matches Eps []
| M_Atom a : matches (Atom a) [a]
| M_PlusL r s w : matches r w -> matches (Plus r s) w
| M_PlusR r s w : matches s w -> matches (Plus r s) w
| M_Concat r s u v : matches r u -> matches s v -> matches (Concat r s) (u ++ v)
| M_Star0 r : matches (Star r) []
| M_StarApp r u v : u <> [] -> matches r u -> matches (Star r) v ->
    matches (Star r) (u ++ v).

Lemma nullable_correct {A} (r : regex A) : nullable r = true <-> matches r [].
Proof.
  induction r; simpl.
  - split; [discriminate|inversion 1].
  - split; constructor; constructor.
  - split; [discriminate|inversion 1].
  - rewrite orb_true_iff, IHr1, IHr2. split.
    + intros [H|H]; [apply M_PlusL|apply M_PlusR]; assumption.
    + inversion 1; subst; auto.
  - rewrite andb_true_iff, IHr1, IHr2. split.
    + intros [H1 H2]. change (matches (Concat r1 r2) (@nil A ++ @nil A)).
      now constructor.
    + intro H; inversion H; subst.
      match goal with
      | E : ?u ++ ?v = [] |- _ => apply app_eq_nil in E as [-> ->]
      end.
      auto.
  - split; [constructor|intros; reflexivity].
Qed.

Lemma no_match_zero {A} w : ~ matches (@Zero A) w.
Proof. inversion 1. Qed.

Lemma concat_zero_l {A} (r : regex A) w : ~ matches (Concat Zero r) w.
Proof. intro H; inversion H; subst; match goal with H0 : matches Zero _ |- _ => inversion H0 end. Qed.

Lemma concat_zero_r {A} (r : regex A) w : ~ matches (Concat r Zero) w.
Proof. intro H; inversion H; subst; match goal with H0 : matches Zero _ |- _ => inversion H0 end. Qed.

Lemma concat_eps_l {A} (r : regex A) w :
  matches (Concat Eps r) w <-> matches r w.
Proof.
  split.
  - intro H; inversion H; subst.
    match goal with He : matches Eps ?u |- _ => inversion He; subst end.
    assumption.
  - intro H. replace w with ([] ++ w) by reflexivity.
    apply M_Concat; [constructor|exact H].
Qed.

Lemma concat_eps_r {A} (r : regex A) w :
  matches (Concat r Eps) w <-> matches r w.
Proof.
  split.
  - intro H; inversion H; subst.
    match goal with He : matches Eps ?u |- _ => inversion He; subst end.
    now rewrite app_nil_r in *.
  - intro H. rewrite <- app_nil_r at 1.
    apply M_Concat; [exact H|constructor].
Qed.

Lemma smart_concat_correct {A} (r s : regex A) w :
  matches (smart_concat r s) w <-> matches (Concat r s) w.
Proof.
  destruct r, s; simpl; try tauto;
    try (split; [intro H; contradiction (no_match_zero H)|intro H; contradiction (concat_zero_l H)]);
    try (split; [intro H; contradiction (no_match_zero H)|intro H; contradiction (concat_zero_r H)]);
    try symmetry; try apply concat_eps_l; try apply concat_eps_r.
Qed.

Lemma smart_plus_correct {A} (r s : regex A) w :
  matches (smart_plus r s) w <-> matches (Plus r s) w.
Proof.
  destruct r, s; simpl; try tauto.
  all: split; intro H.
  all: try now constructor.
  all: inversion H; subst; try assumption;
    match goal with Hz : matches Zero _ |- _ => inversion Hz end.
Qed.

Definition position (A : Type) := (nat * A)%type.

Fixpoint linearize_from {A} (n : nat) (r : regex A) : regex (position A) * nat :=
  match r with
  | Zero => (Zero, n)
  | Eps => (Eps, n)
  | Atom a => (Atom (S n, a), S n)
  | Plus r s =>
      let '(r', n') := linearize_from n r in
      let '(s', n'') := linearize_from n' s in (Plus r' s', n'')
  | Concat r s =>
      let '(r', n') := linearize_from n r in
      let '(s', n'') := linearize_from n' s in (Concat r' s', n'')
  | Star r => let '(r', n') := linearize_from n r in (Star r', n')
  end.

Definition linearize {A} (r : regex A) : regex (position A) := fst (linearize_from 0 r).

Fixpoint erase {A} (r : regex (position A)) : regex A :=
  match r with
  | Zero => Zero | Eps => Eps | Atom p => Atom (snd p)
  | Plus r s => Plus (erase r) (erase s)
  | Concat r s => Concat (erase r) (erase s)
  | Star r => Star (erase r)
  end.

Lemma nullable_erase {A} (r : regex (position A)) : nullable (erase r) = nullable r.
Proof. induction r; simpl; try congruence; now rewrite ?IHr, ?IHr1, ?IHr2. Qed.

Lemma linearize_from_counter {A} (r : regex A) n :
  snd (linearize_from n r) = n + alphabetic_width r.
Proof.
  revert n; induction r; intros n; simpl; try lia.
  - destruct (linearize_from n r1) eqn:E1; simpl.
    destruct (linearize_from n0 r2) eqn:E2; simpl.
    pose proof (IHr1 n); pose proof (IHr2 n0). rewrite E1, E2 in *. simpl in *. lia.
  - destruct (linearize_from n r1) eqn:E1; simpl.
    destruct (linearize_from n0 r2) eqn:E2; simpl.
    pose proof (IHr1 n); pose proof (IHr2 n0). rewrite E1, E2 in *. simpl in *. lia.
  - destruct (linearize_from n r) eqn:E. simpl.
    pose proof (IHr n). rewrite E in *. exact H.
Qed.

Lemma erase_linearize_from {A} (r : regex A) n :
  erase (fst (linearize_from n r)) = r.
Proof.
  revert n; induction r; intros n; simpl; try reflexivity.
  - destruct (linearize_from n r1) eqn:E1.
    destruct (linearize_from n0 r2) eqn:E2. simpl.
    pose proof (IHr1 n) as H1; pose proof (IHr2 n0) as H2.
    rewrite E1 in H1; rewrite E2 in H2; simpl in H1, H2. now rewrite H1, H2.
  - destruct (linearize_from n r1) eqn:E1.
    destruct (linearize_from n0 r2) eqn:E2. simpl.
    pose proof (IHr1 n) as H1; pose proof (IHr2 n0) as H2.
    rewrite E1 in H1; rewrite E2 in H2; simpl in H1, H2. now rewrite H1, H2.
  - destruct (linearize_from n r) eqn:E. simpl.
    pose proof (IHr n) as H; rewrite E in H; simpl in H. now rewrite H.
Qed.

Theorem erase_linearize {A} (r : regex A) : erase (linearize r) = r.
Proof. apply erase_linearize_from. Qed.

Fixpoint regex_atoms {A} (r : regex A) : list A :=
  match r with
  | Zero | Eps => []
  | Atom a => [a]
  | Plus r s | Concat r s => regex_atoms r ++ regex_atoms s
  | Star r => regex_atoms r
  end.

Lemma linearize_from_indices {A} (r : regex A) n :
  map fst (regex_atoms (fst (linearize_from n r))) =
  seq (S n) (alphabetic_width r).
Proof.
  revert n; induction r; intro n; simpl; try reflexivity.
  - destruct (linearize_from n r1) as [lr nr] eqn:E1.
    destruct (linearize_from nr r2) as [ls ns] eqn:E2. simpl.
    pose proof (IHr1 n) as H1; rewrite E1 in H1; simpl in H1.
    pose proof (IHr2 nr) as H2; rewrite E2 in H2; simpl in H2.
    pose proof (linearize_from_counter r1 n) as Hn; rewrite E1 in Hn; simpl in Hn.
    transitivity (map fst (regex_atoms lr) ++ map fst (regex_atoms ls)).
    + apply map_app.
    + rewrite H1, H2, Hn. rewrite <- seq_app. f_equal; lia.
  - destruct (linearize_from n r1) as [lr nr] eqn:E1.
    destruct (linearize_from nr r2) as [ls ns] eqn:E2. simpl.
    pose proof (IHr1 n) as H1; rewrite E1 in H1; simpl in H1.
    pose proof (IHr2 nr) as H2; rewrite E2 in H2; simpl in H2.
    pose proof (linearize_from_counter r1 n) as Hn; rewrite E1 in Hn; simpl in Hn.
    transitivity (map fst (regex_atoms lr) ++ map fst (regex_atoms ls)).
    + apply map_app.
    + rewrite H1, H2, Hn. rewrite <- seq_app. f_equal; lia.
  - destruct (linearize_from n r) as [lr nr] eqn:E. simpl.
    pose proof (IHr n) as H; rewrite E in H; exact H.
Qed.

Theorem linearize_atoms_nodup {A} (r : regex A) :
  NoDup (regex_atoms (linearize r)).
Proof.
  apply (NoDup_map_inv fst). unfold linearize.
  rewrite linearize_from_indices. apply seq_NoDup.
Qed.

Lemma erase_matches {A} (r : regex (position A)) w :
  matches r w -> matches (erase r) (map snd w).
Proof.
  intros H; induction H; simpl.
  - constructor.
  - constructor.
  - now constructor.
  - now constructor.
  - rewrite map_app. econstructor; eauto.
  - constructor.
  - rewrite map_app. econstructor; eauto. intros E.
    apply H. destruct u; simpl in *; congruence.
Qed.

Lemma erase_reflects_matches {A} (r : regex (position A)) w :
  matches (erase r) w ->
  exists pw, matches r pw /\ map snd pw = w.
Proof.
  intro Hm. remember (erase r) as e eqn:E. revert r E.
  induction Hm; intros source Es;
    destruct source as [| |pos|z1 z2|z1 z2|zz]; simpl in Es; try discriminate.
  - exists []; split; [constructor|reflexivity].
  - inversion Es; subst. exists [pos]. split; [constructor|reflexivity].
  - inversion Es; subst. destruct (IHHm _ eq_refl) as [pw [Hp Hw]].
    exists pw. split; [now constructor|exact Hw].
  - inversion Es; subst. destruct (IHHm _ eq_refl) as [pw [Hp Hw]].
    exists pw. split; [now constructor|exact Hw].
  - inversion Es; subst.
    destruct (IHHm1 _ eq_refl) as [pu [Hu Eu]].
    destruct (IHHm2 _ eq_refl) as [pv [Hv Ev]].
    exists (pu ++ pv). split; [now apply M_Concat|].
    transitivity (map snd pu ++ map snd pv); [apply map_app|now rewrite Eu, Ev].
  - inversion Es; subst. exists []. split; [constructor|reflexivity].
  - inversion Es; subst.
    destruct (IHHm1 _ eq_refl) as [pu [Hu Eu]].
    destruct (IHHm2 (Star zz) eq_refl) as [pv [Hv Ev]].
    exists (pu ++ pv). split.
    + apply M_StarApp; auto. intro Epu. apply H.
      apply (f_equal (map snd)) in Epu. simpl in Epu. now rewrite Eu in Epu.
    + transitivity (map snd pu ++ map snd pv); [apply map_app|now rewrite Eu, Ev].
Qed.

Theorem erase_language_iff {A} (r : regex (position A)) w :
  matches (erase r) w <-> exists pw, matches r pw /\ map snd pw = w.
Proof.
  split; [apply erase_reflects_matches|].
  intros [pw [Hm Hw]]. apply erase_matches in Hm. now rewrite Hw in Hm.
Qed.

Theorem linearize_preserves_language {A} (r : regex A) w :
  matches (linearize r) w -> matches r (map snd w).
Proof.
  intro H. apply erase_matches in H. now rewrite erase_linearize in H.
Qed.

Fixpoint annotate_from {A} (n : nat) (w : list A) : list (position A) :=
  match w with
  | [] => []
  | a :: w => (S n, a) :: annotate_from (S n) w
  end.

Lemma map_snd_annotate_from {A} n (w : list A) :
  map snd (annotate_from n w) = w.
Proof. revert n; induction w; intros n; simpl; [reflexivity|]. now f_equal. Qed.

(** Linearization also reflects the language.  The marked witness depends on
    the branch and on how concatenations/stars split the word, so it is stated
    existentially rather than by [annotate_from]. *)
Lemma linearize_from_reflects_language {A} (r : regex A) n w :
  matches r w ->
  exists pw, matches (fst (linearize_from n r)) pw /\ map snd pw = w.
Proof.
  intro Hm. revert n.
  induction Hm; intro n; simpl.
  - exists []; split; [constructor|reflexivity].
  - exists [(S n, a)]; split; [constructor|reflexivity].
  - destruct (linearize_from n r) as [lr nr] eqn:Er.
    destruct (linearize_from nr s) as [ls ns] eqn:Es. simpl.
    specialize (IHHm n). rewrite Er in IHHm. simpl in IHHm.
    destruct IHHm as [pw [Hp Hw]]. exists pw. split; [now constructor|exact Hw].
  - destruct (linearize_from n r) as [lr nr] eqn:Er.
    destruct (linearize_from nr s) as [ls ns] eqn:Es. simpl.
    pose proof (linearize_from_counter r n) as Hnr. rewrite Er in Hnr. simpl in Hnr.
    specialize (IHHm nr). rewrite Es in IHHm. simpl in IHHm.
    destruct IHHm as [pw [Hp Hw]]. exists pw. split; [now constructor|exact Hw].
  - destruct (linearize_from n r) as [lr nr] eqn:Er.
    destruct (linearize_from nr s) as [ls ns] eqn:Es. simpl.
    specialize (IHHm1 n). rewrite Er in IHHm1. simpl in IHHm1.
    specialize (IHHm2 nr). rewrite Es in IHHm2. simpl in IHHm2.
    destruct IHHm1 as [pu [Hu Eu]], IHHm2 as [pv [Hv Ev]].
    exists (pu ++ pv). split.
    + econstructor; eauto.
    + transitivity (map snd pu ++ map snd pv).
      * apply map_app.
      * now rewrite Eu, Ev.
  - destruct (linearize_from n r) as [lr nr] eqn:Er. simpl.
    exists []; split; [constructor|reflexivity].
  - destruct (linearize_from n r) as [lr nr] eqn:Er. simpl.
    specialize (IHHm1 n). rewrite Er in IHHm1. simpl in IHHm1.
    specialize (IHHm2 n). simpl in IHHm2. rewrite Er in IHHm2. simpl in IHHm2.
    destruct IHHm1 as [pu [Hu Eu]], IHHm2 as [pv [Hv Ev]].
    exists (pu ++ pv). split.
    + apply M_StarApp.
      * intro E. apply H. apply (f_equal (map snd)) in E.
        simpl in E. rewrite Eu in E. exact E.
      * exact Hu.
      * exact Hv.
    + transitivity (map snd pu ++ map snd pv).
      * apply map_app.
      * now rewrite Eu, Ev.
Qed.

Theorem linearize_language_iff {A} (r : regex A) w :
  matches r w <->
  exists pw, matches (linearize r) pw /\ map snd pw = w.
Proof.
  split.
  - apply linearize_from_reflects_language.
  - intros [pw [Hp Hw]]. apply linearize_preserves_language in Hp.
    now rewrite Hw in Hp.
Qed.
