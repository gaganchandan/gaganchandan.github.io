From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.

Inductive aexp : Type :=
  | Num : nat -> aexp
  | Id : string -> aexp
  | Plus : aexp -> aexp -> aexp
  | Mult : aexp -> aexp -> aexp
  | Minus : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | True : bexp
  | False : bexp
  | Eq : aexp -> aexp -> bexp
  | Leq : aexp -> aexp -> bexp
  | Not : bexp -> bexp
  | And : bexp -> bexp -> bexp.

Inductive stmt : Type :=
  | Assign : string -> aexp -> stmt
  | Skip : stmt
  | Seq : stmt -> stmt -> stmt
  | If : bexp -> stmt -> stmt -> stmt
  | While : bexp -> stmt -> stmt.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (x : string) 
                    (v : A) (m : total_map A) :=
  fun x' => if String.eqb x x' then v else m x'.

 Notation "x '!->' v ';' m" := (t_update x v m)
                              (at level 100, v at next level, right associativity).

Definition state := total_map nat.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | Num n => n
  | Id x => st x
  | Plus a1 a2 => (aeval st a1) + (aeval st a2)
  | Mult a1 a2 => (aeval st a1) * (aeval st a2)
  | Minus a1 a2 => (aeval st a1) - (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | True => true
  | False => false
  | Eq a1 a2 => (aeval st a1) =? (aeval st a2)
  | Leq a1 a2 => (aeval st a1) <=? (aeval st a2)
  | Not b1 => negb (beval st b1)
  | And b1 b2 => andb (beval st b1) (beval st b2)
  end.

Inductive seval : state -> stmt -> state -> Prop :=
  | E_Skip : forall (st : state), seval st (Skip) st
  | E_Seq : forall (st1 st2 st3 : state) (s1 s2 : stmt), 
      seval st1 s1 st2 ->
      seval st2 s2 st3 ->
      seval st1 (Seq s1 s2) st3
  | E_Assign : forall (st : state) (a : aexp) (n : nat) (x : string), 
      aeval st a = n -> seval st (Assign x a) (t_update x n st)
  | E_IfTrue : forall (st1 st2 : state) (b : bexp) (s1 s2 : stmt), 
      beval st1 b = true ->
      seval st1 s1 st2 ->
      seval st1 (If b s1 s2) st2
  | E_IfFalse : forall (st1 st2 : state) (b : bexp) (s1 s2 : stmt), 
      beval st1 b = false ->
      seval st1 s2 st2 ->
      seval st1 (If b s1 s2) st2
  | E_WhileFalse : forall (st : state) (b : bexp) (s : stmt),
      beval st b = false -> 
      seval st (While b s) st
  | E_WhileTrue : forall (st1 st2 st3: state) (b : bexp) (s : stmt),
      beval st1 b = true ->
      seval st1 s st2 ->
      seval st2 (While b s) st3 ->
      seval st1 (While b s) st3.

Definition factorial : stmt :=
  Seq (Assign "x" (Num 3))
  (Seq (Assign "y" (Num 1))
  (While (Not(Eq(Id "x")(Num 1)))
  (Seq(Assign "y" (Mult (Id "y") (Id "x")))
  (Assign "x" (Minus (Id "x") (Num 1)))))).

Theorem factorial_3 : forall st : state, 
  seval (st) factorial ("x" !-> 1; "y" !-> 6; "x" !-> 2; "y" !-> 3; "y" !-> 1; "x" !-> 3; st).
Proof.
  intros st. eapply E_Seq.
  - apply E_Assign. reflexivity.
  - eapply E_Seq.
    + apply E_Assign. reflexivity.
    + eapply E_WhileTrue.
      * reflexivity.
      * eapply E_Seq.
        -- apply E_Assign. reflexivity.
        -- apply E_Assign. reflexivity.
      * eapply E_WhileTrue.
        -- reflexivity.
        -- eapply E_Seq.
          ++ apply E_Assign. reflexivity.
          ++ apply E_Assign. reflexivity.
        -- eapply E_WhileFalse. reflexivity. 
Qed.

Definition sequiv (s1 s2 : stmt) : Prop :=
  forall (st1 st2 : state), seval st1 s1 st2 <-> seval st1 s2 st2.

Theorem skip_stmt : forall (s : stmt), sequiv s (Seq Skip s).
Proof. 
  intros s st st'. split; intros H.
  - eapply E_Seq.
    + apply E_Skip.
    + assumption.
  - inversion H. subst. inversion H3. subst. assumption.
Qed.
