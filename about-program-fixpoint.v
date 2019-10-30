Require Import mathcomp.ssreflect.all_ssreflect.
Require Import Program.Wf.
Set Bullet Behavior "Strict Subproofs".

(* Transforms a coq_nat less-than into ssreflect's less-than *)
Ltac leP_of_coq_nat :=
  match goal with
  | |- (_ < _)%coq_nat => apply/leP
  | _                  => idtac
  end.

Obligation Tactic := Tactics.program_simpl; leP_of_coq_nat; try done.

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
  case: x.
  - done.
  - move=> x'.
    by progdef f1.
Qed.

Lemma f1_id x : f1 x = x.
Proof.
  elim: x.
  - done.
  - move=> x' IHx'.
    by rewrite def_f1 IHx'.
Qed.

(* ------------------------------------------------------ *)

(* Occurrence Typing / Logical Types for Untyped Languages / Flow Stuff *)
Definition if_eq A c : (c = true -> A) -> (c = false -> A) -> A :=
  match c with
  | true  => fun t _ => t erefl
  | false => fun _ e => e erefl
  end.
Arguments if_eq {A} c t e.

Program Fixpoint f2 (x : nat) {measure x} : nat :=
  if_eq (x == 0)
        (fun xeq0 => 0)
        (fun xne0 => S (f2 (x - 1))).
Next Obligation.
  move: f2 => _.
  case: x xne0.
  - done.
  - move=> x' _.
    by rewrite subn1.
Qed.

Lemma def_f2 x : f2 x = if_eq (x == 0) (fun xeq0 => 0) (fun xne0 => S (f2 (x - 1))).
Proof.
  case: x.
  - done.
  - move=> x.
    WfExtensionality.unfold_sub f2 (f2 (S x)).
    simpl.
    fold_sub f2.
    done.
Qed.

Lemma f2_id x : f2 x = x.
Proof.
  elim: x.
  - done.
  - move=> x IHx.
    by rewrite def_f2 subn1 IHx.
Qed.

(* ------------------------------------------------------ *)

Definition collatz_next (x : nat) : nat :=
  if Nat.even x
  then x./2
  else (3 * x) + 1.

(* repeat until local minimum *)
Program Fixpoint f3 (x : nat) {measure x} : nat :=
  let y := collatz_next x in
  if_eq (y < x)
        (fun yltx => f3 y)
        (fun _    => x).

Lemma not_lt_3xp1x x : 3 * x + 1 < x = false.
Proof.
  apply/eqP.
  by rewrite addn1 mulSn -2!addnS addKn.
Qed.

Lemma f3_not_even_id x : (Nat.even x = false) -> (f3 x = x).
Proof.
  move=> oddx.
  WfExtensionality.unfold_sub f3 (f3 x).
  unfold collatz_next.
  by rewrite oddx not_lt_3xp1x.
Qed.

