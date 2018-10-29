Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import PeanoNat.


(* Option monad utilities *)
Definition bind{A B: Type} (x : option A) (f : A -> B) :=
  match x with
  | None => None
  | Some x => Some (f x)
  end.

(* Variables are just a nat *)
Definition Var := nat.

(* Registers (infinite) map nats to Z *)
Definition Regs := nat -> Z.

Fixpoint get (var : Var) (r : Regs) := r var.

Fixpoint put (var : Var) v (r : Regs) :=
  fun var' => if var' =? var then v else r var'.

(* Registers are zeroed by default *)
Definition emptyRegs :=
  fun (var' : Var) => Z0.

Inductive Stmt :=
  | SAdd (a b c : Var) (* a = b + c *)
  | SIf (cond : Var) (trueEval falseEval : Stmt) (* if cond == 0 then falseEval else trueEval *)
  | SSeq (s1 s2 : Stmt) (* s1 ; s2 *)
  | SLit (a : Var) (v : Z) (* a = $v *)
  | SNop
  .

Open Scope Z_scope.

Definition inc_eval_log (inc : Z) (res : option (Z * Regs)) :=
  bind res (fun x => ((fst x) + inc, snd x)).

Fixpoint eval_stmt_log (fuel : nat) (s : Stmt) (r : Regs) :=
  match fuel with
  | O => None
  | S f => match s with
           | SAdd a b c => Some (1, put a ((get b r) + (get c r)) r)
           | SIf cond trueEval falseEval => if (Z.eqb (get cond r) 0%Z) then
                                              inc_eval_log 1 (eval_stmt_log f falseEval r)
                                            else
                                              inc_eval_log 1 (eval_stmt_log f trueEval r)
           | SSeq s1 s2 => match eval_stmt_log f s1 r with
                           | None => None
                           | Some (count, r') => inc_eval_log count (eval_stmt_log f s2 r')
                           end
           | SLit a v => Some (1, put a v r)
           | SNop => Some (1, r)
           end
  end.

Close Scope Z_scope.

Definition var_a := 1.
Definition var_b := 2.
Definition var_tmp := 3.

(* Test stmt, loads n into var_a and doubles it *)
Definition eg_double_stmt n :=
  SSeq (SLit var_a n) (SAdd var_a var_a var_a).

Definition eg_double_res n := (eval_stmt_log 5 (eg_double_stmt n) emptyRegs).

Definition eg_double_instructions n := bind (eg_double_res n) fst.
Definition eg_double_regs n := bind (eg_double_res n) snd.
Definition eg_double_val n := bind (eg_double_regs n) (get var_a).

Lemma eg_double_5_correct : eg_double_val 5%Z = Some 10%Z.
Proof. reflexivity. Qed.

Lemma eg_double_neg12_correct : eg_double_val (Z.neg 12) = Some (Z.neg 24).
Proof. reflexivity. Qed.

Inductive Instr :=
  | IAdd (a b c : Var)
  | IJump (pc : nat) 
  | IBeqz (a : Var) (pc : nat)
  | IImm (a : Var) (v : Z)
  | INop
  .

Fixpoint compile_stmt (s : Stmt) :=
  match s with
  | SAdd a b c => [IAdd a b c]
  | SIf c t f => match (compile_stmt t) with
                 | t' => match (compile_stmt f) with
                         | f' => [IBeqz c (1 + (length t'))] ++ t' ++ [IJump (length f')] ++ f'
                         end
                 end
  | SSeq s1 s2 => (compile_stmt s1) ++ (compile_stmt s2)
  | SLit a v => [IImm a v]
  | SNop => [INop]
  end.

Fixpoint eval_instr_log_single i pc regs :=
  match i with
  | IAdd a b c => (1%Z, put a ((get b regs) + (get c regs)) regs, pc + 1)
  | IJump pc' => (1%Z, regs, pc + pc' + 1)
  | IBeqz a pc' => (1%Z, regs, if (Z.eqb (get a regs) 0%Z) then pc + pc' + 1 else pc + 1)
  | IImm a v => (1%Z, put a v regs, pc + 1)
  | INop => (1%Z, regs, pc + 1)
  end.

Fixpoint eval_instr_log fuel (instrs : list Instr) regs pc :=
  match nth_error instrs pc with
  | None => Some (0%Z, regs, pc) (* Execution has completed *)
  | Some i => match fuel with
              | 0 => None
              | S f => let '(count', regs', pc') := (eval_instr_log_single i pc regs) in
                       match (eval_instr_log f instrs regs' pc') with
                       | None => None
                       | Some (count'', regs'', pc'') => Some (Z.add count' count'', regs'', pc'')
                       end
               end
  end.

Definition get_compiled_result (s: Stmt) (result_var : Var) :=
  match eval_instr_log 100 (compile_stmt s)emptyRegs 0 with
  | None => None
  | Some (count, regs, pc) => Some (get result_var regs)
  end.

Fixpoint stmt_list_to_stmt l :=
  match l with
  | [] => SNop
  | hd :: tl => SSeq hd (stmt_list_to_stmt tl)
  end.

(* if (a == 5) then b = 500 else b = 100 *)

Definition eg_cond_stmt a := stmt_list_to_stmt
  [
    (SLit var_a a);
    (SLit var_tmp (Z.neg 5));
    (SAdd var_a var_a var_tmp);
    (SIf var_a 
      (SLit var_b 100) 
      (SLit var_b 500)
    )
  ].

Lemma eg_cond_5_correct : get_compiled_result (eg_cond_stmt 5%Z) var_b = Some 500%Z.
Proof. reflexivity. Qed.

Lemma eg_cond_neg12_correct : get_compiled_result (eg_cond_stmt (Z.neg 12)) var_b = Some 100%Z.
Proof. reflexivity. Qed.

Lemma inc_log : forall n fuel s ir countH Hfr p,
  eval_stmt_log fuel s ir = Some p ->
  inc_eval_log n (Some p) = Some (countH, Hfr) ->
  countH = Z.add (fst p) n.
Proof.
intros.
destruct fuel.
- discriminate.
- inversion H0. reflexivity.
Qed.

Lemma beq_equivalence : forall instrs pc var pc' regs fuel count fregs1 fpc1 fregs2 fpc2 countRest,
  nth_error instrs pc = Some (IBeqz var pc') ->
  get var regs = 0%Z ->
  eval_instr_log (S fuel) instrs regs pc = Some (count, fregs1, fpc1) ->
  eval_instr_log fuel instrs regs (pc + pc' + 1) = Some(countRest, fregs2, fpc2) ->
  count = (countRest + 1)%Z.
Proof.
intros.
simpl in H1. rewrite H in H1. unfold eval_instr_log_single in H1. rewrite H0 in H1. simpl in H1.
rewrite H2 in H1. inversion H1.
destruct countRest.
- reflexivity.
- destruct p.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
- simpl. reflexivity.
Qed.

Open Scope Z_scope.

Lemma bounded_instrs : forall (s : Stmt) (fuel : nat) (ir : Regs) countL countH Hfr Lfr pcf,
  eval_stmt_log fuel s ir = Some (countH, Hfr) ->
  eval_instr_log fuel (compile_stmt s) ir 0 = Some (countL, Lfr, pcf) ->
  countL < 3 * countH.
Proof.
intros.
generalize dependent s.
generalize dependent countL.
generalize dependent countH.
induction fuel.
- discriminate.
- destruct s.
  + (* s = SAdd a b c *) 
    intros. inversion H.
    destruct fuel.
    * inversion H0. reflexivity. 
    * inversion H0. reflexivity.
  + (* s = SIf cond trueEval falseEval *)
    admit.
  + (* s = SSeq s1 s2 *)
    admit.
  + (* s = SLit a v *)
    intros. inversion H.
    destruct fuel.
    * inversion H0. reflexivity.
    * inversion H0. reflexivity.
  + (* s = SNop *)
    intros. inversion H.
    destruct fuel.
    * inversion H0. reflexivity.
    * inversion H0. reflexivity.
Admitted.