Require Import Coq.ZArith.BinInt.
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

Fixpoint put (r : Regs) (var : Var) v :=
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
           | SAdd a b c => Some (1%Z, put r a ((get b r) + (get c r)))
           | SIf cond trueEval falseEval => if (Z.eqb (get cond r) 0%Z) then
                                              inc_eval_log (eval_stmt_log falseEval f r) 1%Z
                                            else
                                              inc_eval_log (eval_stmt_log trueEval f r) 1%Z
           | SSeq s1 s2 => match eval_stmt_log s1 f r with
                           | None => None
                           | Some (count, r') => inc_eval_log (eval_stmt_log s2 f r') count
                           end
           | SLit a v => Some (1%Z, put r a v)
           end
  end.

Definition var_1 := 1.
Definition var_a := 2.

(* Test stmt, loads 5 into var_a and doubles it *)
Definition eg_double_stmt :=
  SSeq (SLit var_a 5%Z) (SAdd var_a var_a var_a).

Definition eg_double_res := (eval_stmt_log eg_double_stmt 5 emptyRegs).

Definition eg_double_instructions := bind eg_double_res fst.
Definition eg_double_regs := bind eg_double_res snd.
Definition eg_double_val := bind eg_double_regs (get var_a).

Lemma eg_double_val_correct : eg_double_val = Some 10%Z.
Proof. reflexivity. Qed.
