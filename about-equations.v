Require Import mathcomp.ssreflect.all_ssreflect.
From Equations Require Import Equations.
Require Import Arith.Wf_nat.
Set Bullet Behavior "Strict Subproofs".

(* Transforms a coq_nat less-than into ssreflect's less-than *)
Ltac leP_of_coq_nat :=
  match goal with
  | |- (_ < _)%coq_nat => apply/leP
  | _                  => idtac
  end.

Show Obligation Tactic.
Obligation Tactic :=
  Tactics.program_simplify; Tactics.equations_simpl;
    try Tactics.program_solve_wf;
    leP_of_coq_nat; try done.

(* ------------------------------------------------------ *)

Equations f1 (x : nat) : nat by wf x lt :=
  f1 0       := 0 ;
  f1 (S xm1) := S (f1 xm1).

Lemma def_f1 x : f1 x = match x with | 0 => 0 | S xm1 => S (f1 xm1) end.
Proof. by apply: f1_unfold_eq. Qed.

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

Equations f2 (x : nat) : nat by wf x lt :=
  f2 x := if_eq (x == 0)
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
Proof. by apply: f2_unfold_eq. Qed.

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
Equations f3 (x : nat) : nat by wf x lt :=
  f3 x
  :=
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
  rewrite f3_equation_1.
  unfold collatz_next.
  by rewrite oddx not_lt_3xp1x.
Qed.

(* ------------------------------------------------------ *)

(* repeat until local minimum, generic *)
Equations repeat_while_smaller A (size : A -> nat) (f : A -> A) (a : A) : A by wf (size a) lt :=
  repeat_while_smaller A size f a
  :=
  let b := f a in
  if_eq (size b < size a)
        (fun blta => repeat_while_smaller A size f b)
        (fun nlt  => a).

Lemma repeat_while_smaller_ind :
  forall (A : Set) (size : A -> nat) (P : A -> Prop),
    (forall (a : A),
        (forall (b : A), (size b < size a) -> P b)
        ->
        P a)
    ->
    (forall (a : A), P a).
Proof.
  move=> A size P H a.
  apply:
    (lt_wf_ind
       (size a)
       (fun (sa : nat) => forall (a : A), (sa = size a) -> (P a))).
  - move=> sa IHa a' Heqsa.
    apply: (H a').
    move=> b blta.
    move/ltP in blta.
    rewrite -Heqsa in blta.
    by apply: (IHa (size b) blta b erefl).
  - done.
Qed.

Lemma repeat_while_smaller_preserves_reflexive_transitive :
  forall
    (A : Set)
    (R : A -> A -> Prop)
    (Rrefl : forall a, R a a)
    (Rtrans : forall a b c, R a b -> R b c -> R a c)
    (size : A -> nat)
    (step1 : A -> A)
    (Rstep1 : forall a, R a (step1 a)),
    (* --------------------- *)
    forall a, R a (repeat_while_smaller A size step1 a).
Proof.
  move=> A R Rrefl Rtrans size step1 Rstep1.
  apply: (repeat_while_smaller_ind A size (fun a => R a (repeat_while_smaller A size step1 a))).
  - move=> a IHa.
    rewrite repeat_while_smaller_equation_1.
    remember (step1 a) as b => //=.
    case blta: (size b < size a) => //=.
    apply: Rtrans.
    + by apply: Rstep1.
    + rewrite -Heqb.
      by apply: IHa.
Qed.
