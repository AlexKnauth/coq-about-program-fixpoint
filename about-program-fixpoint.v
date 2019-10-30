Require Import Arith.PeanoNat.
Require Import Arith.EqNat.
Require Import Arith.Wf_nat.
Require Import Program.Wf.

(* Example use of progdef, on a function `f` defined as a program fixpoint:
   Lemma def_f x : f x = <<body-of-f>>.
   Proof.
     destruct x.
     - reflexivity.
     - progdef f. reflexivity.
   Qed. *)
Ltac progdef func :=
  let x := fresh "x" in let f := fresh "f" in let g := fresh "g" in let Heq := fresh "Heq" in
  unfold func; rewrite fix_sub_eq;
  [ simpl; fold func
  | intros x f g Heq; destruct x; [ reflexivity | f_equal; apply Heq ] ].

(* ------------------------------------------------------ *)

Program Fixpoint f1 (x : nat) {measure x} : nat :=
  match x with
  | 0    => 0
  | S x' => S (f1 x')
  end.

Lemma def_f1 x : f1 x = match x with | 0 => 0 | S x' => S (f1 x') end.
Proof.
  destruct x.
  - reflexivity.
  - progdef f1. reflexivity.
Qed.

Lemma f1_id x : f1 x = x.
Proof.
  induction x as [| x IHx].
  - reflexivity.
  - rewrite def_f1.
    rewrite IHx.
    reflexivity.
Qed.

(* ------------------------------------------------------ *)

(* Occurrence Typing / Logical Types for Untyped Languages / Flow Stuff *)
Definition if_eq A c : (c = true -> A) -> (c = false -> A) -> A :=
  match c with
  | true  => fun t _ => t eq_refl
  | false => fun _ e => e eq_refl
  end.
Arguments if_eq {A} c t e.

Program Fixpoint f2 (x : nat) {measure x} : nat :=
  if_eq (x =? 0)
        (fun xeq0 => 0)
        (fun xne0 => S (f2 (x - 1))).
Next Obligation.
  assert (x <> 0) as xne0'. { apply (beq_nat_false x 0 xne0). }
  destruct x.
  - contradiction.
  - simpl. rewrite Nat.sub_0_r. apply le_n.
Qed.

Lemma def_f2 x : f2 x = if_eq (x =? 0) (fun xeq0 => 0) (fun xne0 => S (f2 (x - 1))).
Proof.
  destruct x.
  - reflexivity.
  - WfExtensionality.unfold_sub f2 (f2 (S x)).
    simpl.
    fold_sub f2.
    reflexivity.
Qed.

Lemma f2_id x : f2 x = x.
Proof.
  induction x as [| x IHx].
  - reflexivity.
  - rewrite def_f2.
    simpl.
    rewrite Nat.sub_0_r.
    rewrite IHx.
    reflexivity.
Qed.
