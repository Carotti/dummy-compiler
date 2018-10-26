Require Import Coq.ZArith.BinInt.
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
  .

Definition inc_eval_log (res : option (Z * Regs)) (inc : Z) :=
  bind res (fun x => (Z.add (fst x) inc, snd x)).

Fixpoint eval_stmt_log (s : Stmt) (fuel : nat) (r : Regs) :=
  match fuel with
  | O => None
  | S f => match s with
           | SAdd a b c => Some (1%Z, put a ((get b r) + (get c r)) r)
           | SIf cond trueEval falseEval => if (Z.eqb (get cond r) 0%Z) then
                                              inc_eval_log (eval_stmt_log falseEval f r) 1%Z
                                            else
                                              inc_eval_log (eval_stmt_log trueEval f r) 1%Z
           | SSeq s1 s2 => match eval_stmt_log s1 f r with
                           | None => None
                           | Some (count, r') => inc_eval_log (eval_stmt_log s2 f r') count
                           end
           | SLit a v => Some (1%Z, put a v r)
           end
  end.

Definition var_1 := 1.
Definition var_a := 2.

(* Test stmt, loads n into var_a and doubles it *)
Definition eg_double_stmt n :=
  SSeq (SLit var_a n) (SAdd var_a var_a var_a).

Definition eg_double_res n := (eval_stmt_log (eg_double_stmt n) 5 emptyRegs).

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
  .

Fixpoint compile_stmt (s : Stmt) :=
  match s with
  | SAdd a b c => [IAdd a b c]
  | SIf c t f => match (compile_stmt t) with
                 | t' => match (compile_stmt f) with
                         | f' => [IBeqz c (length t')] ++ t' ++ [IJump (length f')] ++ f'
                         end
                 end
  | SSeq s1 s2 => (compile_stmt s1) ++ (compile_stmt s2)
  | SLit a v => [IImm a v]
  end.

Fixpoint eval_instr_log_single i regs pc :=
  match i with
  | IAdd a b c => (1%Z, put a ((get b regs) + (get c regs)) regs, pc + 1)
  | IJump pc' => (1%Z, regs, pc')
  | IBeqz a pc' => (1%Z, regs, if (Z.eqb (get a regs) 0%Z) then pc' else pc + 1)
  | IImm a v => (1%Z, put a v regs, pc + 1)
  end.

Fixpoint eval_instr_log (instrs : list Instr) fuel regs pc :=
  match fuel with
  | 0 => None
  | S f => match nth_error instrs pc with
           | None => Some (0%Z, regs, pc) (* Execution has completed *)
           | Some i => match (eval_instr_log_single i regs pc) with
                       | (count', regs', pc') => match (eval_instr_log instrs f regs' pc') with
                                               | None => None
                                               | Some (count'', regs'', pc'') => Some (Z.add count' count'', regs'', pc'')
                                               end
                       end
           end 
  end.

Definition get_compiled_result (s: Stmt) (result_var : Var) :=
  match eval_instr_log (compile_stmt s) 100 emptyRegs 0 with
  | None => None
  | Some (count, regs, pc) => Some (get result_var regs)
  end.

Compute get_compiled_result (eg_double_stmt 7) var_a.