From Stdlib Require Import List Bool Arith.
Import ListNotations.

Set Implicit Arguments.

Record automaton (A : Type) := {
  state_count : nat;
  initial : nat;
  finalb : nat -> bool;
  trans : nat -> A -> list nat
}.

Fixpoint memb (x : nat) (xs : list nat) : bool :=
  match xs with [] => false | y :: ys => Nat.eqb x y || memb x ys end.

Definition add (x : nat) (xs : list nat) : list nat :=
  if memb x xs then xs else xs ++ [x].

Fixpoint union (xs ys : list nat) : list nat :=
  match xs with [] => ys | x :: xs => union xs (add x ys) end.

Fixpoint step_from {A} (M : automaton A) (qs : list nat) (a : A) : list nat :=
  match qs with [] => [] | q :: qs => union (trans M q a) (step_from M qs a) end.

Fixpoint run {A} (M : automaton A) (qs : list nat) (w : list A) : list nat :=
  match w with [] => qs | a :: w => run M (step_from M qs a) w end.

Fixpoint any_final {A} (M : automaton A) (qs : list nat) : bool :=
  match qs with [] => false | q :: qs => finalb M q || any_final M qs end.

Definition acceptb {A} (M : automaton A) (w : list A) : bool :=
  any_final M (run M [initial M] w).

Lemma memb_spec x xs : memb x xs = true <-> In x xs.
Proof.
  induction xs as [|y ys IH]; simpl.
  - split; [discriminate|contradiction].
  - rewrite Bool.orb_true_iff, Nat.eqb_eq, IH. split.
    + intros [->|H]; simpl; auto.
    + intros [->|H]; auto.
Qed.

Lemma add_spec x y xs : In y (add x xs) <-> y = x \/ In y xs.
Proof.
  unfold add. destruct (memb x xs) eqn:E.
  - apply memb_spec in E. split.
    + intro Hy. right. exact Hy.
    + intros [->|Hy]; auto.
  - rewrite in_app_iff. simpl. split.
    + intros [H|[->|[]]]; auto.
    + intros [->|H].
      * right. auto.
      * left. exact H.
Qed.

Lemma union_spec xs ys q : In q (union xs ys) <-> In q xs \/ In q ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys; simpl.
  - tauto.
  - rewrite IH, add_spec. simpl. split.
    + intros [Hxs|[->|Hy]]; auto.
    + intros [[->|Hxs]|Hy]; auto.
Qed.

Lemma step_from_spec {A} (M : automaton A) qs a q :
  In q (step_from M qs a) <->
  exists p, In p qs /\ In q (trans M p a).
Proof.
  induction qs as [|p ps IH]; simpl.
  - split; [contradiction|intros [x [H]]; contradiction].
  - rewrite union_spec, IH. split.
    + intros [H|[x [Hx Ht]]].
      * exists p. auto.
      * exists x. auto.
    + intros [x [[->|Hx] Ht]].
      * auto.
      * right. exists x. auto.
Qed.

Inductive nfa_run {A} (M : automaton A) : nat -> list A -> nat -> Prop :=
| NRun_nil q : nfa_run M q [] q
| NRun_cons p a q w t : In q (trans M p a) -> nfa_run M q w t ->
    nfa_run M p (a :: w) t.

Lemma run_spec {A} (M : automaton A) qs w q :
  In q (run M qs w) <->
  exists p, In p qs /\ nfa_run M p w q.
Proof.
  revert qs; induction w as [|a w IH]; intros qs; simpl.
  - split.
    + intro H. exists q. split; [exact H|constructor].
    + intros [p [Hp Hrun]]. inversion Hrun; subst; assumption.
  - rewrite IH. split.
    + intros [p [Hp Hrun]]. apply step_from_spec in Hp.
      destruct Hp as [s [Hs Hsp]]. exists s. split; [exact Hs|].
      econstructor; eauto.
    + intros [p [Hp Hrun]]. inversion Hrun; subst.
      exists q0. split; auto. apply step_from_spec. exists p. auto.
Qed.

Lemma any_final_spec {A} (M : automaton A) qs :
  any_final M qs = true <-> exists q, In q qs /\ finalb M q = true.
Proof.
  induction qs as [|q qs IH]; simpl.
  - split; [discriminate|intros [x [H]]; contradiction].
  - rewrite Bool.orb_true_iff, IH. split.
    + intros [H|[x [Hx Hf]]].
      * exists q. auto.
      * exists x. auto.
    + intros [x [[->|Hx] Hf]].
      * auto.
      * right. exists x. auto.
Qed.

Theorem acceptb_spec {A} (M : automaton A) w :
  acceptb M w = true <->
  exists q, nfa_run M (initial M) w q /\ finalb M q = true.
Proof.
  unfold acceptb. rewrite any_final_spec. split.
  - intros [q [Hq Hf]]. apply run_spec in Hq.
    destruct Hq as [p [[Hp|Hp] Hrun]].
    + subst p. exists q. auto.
    + contradiction.
  - intros [q [Hrun Hf]]. exists q. split; auto.
    apply run_spec. exists (initial M). split; [now left|exact Hrun].
Qed.

Fixpoint mapi_from {A B} (n : nat) (f : nat -> A -> B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: xs => f n x :: mapi_from (S n) f xs
  end.

Definition mapi {A B} (f : nat -> A -> B) (xs : list A) : list B :=
  mapi_from 0 f xs.

Record state_info (A : Type) (R : Type) := {
  info_id : nat;
  info_position : option (nat * A);
  info_members : list nat;
  info_continuation : R;
  info_final : bool
}.

Record built_automaton (A R : Type) := {
  machine : automaton A;
  infos : list (state_info A R)
}.
