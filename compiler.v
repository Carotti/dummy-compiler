Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import PeanoNat.
Require Import Coq.Arith.Arith.

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

Definition get (var : Var) (r : Regs) := r var.

Definition put (var : Var) v (r : Regs) :=
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
  | IExit (* Terminate execution *)
  .

Fixpoint compile_stmt_rec (s : Stmt) :=
  match s with
  | SAdd a b c => [IAdd a b c]
  | SIf c t f => match (compile_stmt_rec t) with
                 | t' => match (compile_stmt_rec f) with
                         | f' => [IBeqz c (1 + (length t'))] ++ t' ++ [IJump (length f')] ++ f'
                         end
                 end
  | SSeq s1 s2 => (compile_stmt_rec s1) ++ (compile_stmt_rec s2)
  | SLit a v => [IImm a v]
  | SNop => [INop]
  end.

(* Append an exit to the instructions *)
Definition compile_stmt (s : Stmt) := compile_stmt_rec s ++ [IExit].

Fixpoint eval_instr_log_single i pc regs :=
  match i with
  | IAdd a b c => (1%Z, put a ((get b regs) + (get c regs)) regs, pc + 1)
  | IJump pc' => (1%Z, regs, pc + pc' + 1)
  | IBeqz a pc' => (1%Z, regs, if (Z.eqb (get a regs) 0%Z) then pc + pc' + 1 else pc + 1)
  | IImm a v => (1%Z, put a v regs, pc + 1)
  | INop => (1%Z, regs, pc + 1)
  | IExit => (0%Z, regs, pc) (* Loop til we run out of fuel *)
  end.

Record InstrMachineLog := mkInstrMachineLog {
  Iregs : Regs;
  Ipc : nat;
  Icount : Z;
}.

Definition emptyMachineLog := mkInstrMachineLog emptyRegs 0 0.

Definition with_Iregs r m := mkInstrMachineLog r m.(Ipc) m.(Icount).
Definition with_Ipc p m := mkInstrMachineLog m.(Iregs) p m.(Icount).
Definition with_Icount c m := mkInstrMachineLog m.(Iregs) m.(Ipc) c.

Definition inc_count (n : Z) m := with_Icount (m.(Icount) + n) m.
Definition inc_pc p m := with_Ipc ((m.(Ipc) + p)) m.

Definition add_regs a b c m := with_Iregs (put a ((get b m.(Iregs)) + (get c m.(Iregs))) m.(Iregs)) m.
Definition load_imm a v m := with_Iregs (put a v m.(Iregs)) m.


Fixpoint eval_instr_log fuel (m : InstrMachineLog) (instrs : list Instr) : option InstrMachineLog :=
  match fuel with
  | O => None
  | S fuel' => match nth_error instrs m.(Ipc) with
              | None => None (* Should never happen *)
              | Some i => match i with
                          | IAdd a b c => eval_instr_log fuel' (inc_count 1 (inc_pc 1 (add_regs a b c (m)))) instrs
                          | IJump pc' => eval_instr_log fuel' (inc_count 1 (inc_pc (pc' + 1) m)) instrs
                          | IBeqz a pc' => eval_instr_log fuel' (inc_count 1 (inc_pc (if (Z.eqb (get a m.(Iregs)) 0%Z) then pc' + 1 else 1) m)) instrs
                          | IImm a v => eval_instr_log fuel' (inc_count 1 (inc_pc 1 (load_imm a v m))) instrs
                          | INop => eval_instr_log fuel' (inc_count 1 (inc_pc 1 m)) instrs
                          | IExit => Some m
                          end
              end
  end.

Definition get_compiled_result (s: Stmt) (result_var : Var) :=
  match eval_instr_log 100 emptyMachineLog (compile_stmt s) with
  | None => None
  | Some m => Some (get result_var m.(Iregs))
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

Lemma n_sub_n : forall (n : nat),
  n - n = O.
Proof.
induction n.
- reflexivity.
- apply IHn.
Qed.

Lemma fetch_insts : forall (instsBefore instsAfter : list Instr) x rest n ,
  n = (length instsBefore) ->
  nth_error (instsBefore ++ (x :: rest) ++ instsAfter) n = Some x.
Proof.
intros.
rewrite app_assoc.
rewrite nth_error_app1.
- rewrite nth_error_app2.
  + simpl. rewrite H. rewrite n_sub_n. reflexivity.
  + rewrite H. reflexivity.
- induction instsBefore.
  + simpl. rewrite H. simpl. omega.
  + simpl. rewrite app_length. rewrite H. simpl. omega.
Qed.

Lemma next_inst : forall (before after: list Instr) a b,
  before ++ a :: b :: after = (before ++ [a]) ++ [b] ++ after.
Proof.
intros.
induction before.
- reflexivity.
- simpl. f_equal. apply IHbefore.
Qed.

Open Scope Z_scope.

Lemma bounded_instrs :
forall (fuelL fuelH : nat) (s : Stmt) (ir : Regs) ipc
countL countH Hfr mi mf allInsts instsBefore instsAfter insts,
  eval_stmt_log fuelH s ir = Some (countH, Hfr) ->
  eval_instr_log fuelL mi allInsts = Some mf ->
  mi = mkInstrMachineLog ir ipc 0 ->
  mf.(Icount) = countL ->
  compile_stmt s = insts ->
  allInsts = instsBefore ++ insts ++ instsAfter ->
  ipc = length instsBefore ->
  countL < 3 * countH.
Proof.
induction fuelH.
- discriminate.
- destruct s.
  + (* s = SAdd a b c *) 
    intros. inversion H.
    destruct fuelL.
    * discriminate.
    * rewrite H1 in H0. rewrite H4 in H0. rewrite H5 in H0. simpl in H0. 
      rewrite <- H3 in H0. unfold compile_stmt in H0. unfold compile_stmt_rec in H0.
      simpl ([_] ++ [_]) in H0. pose proof fetch_insts as Hfetch1.
      specialize (Hfetch1 instsBefore instsAfter (IAdd a b c) [IExit] (length instsBefore)).
      rewrite Hfetch1 in H0.
      destruct fuelL. (* Exit instruction *)
        ** discriminate.
        ** simpl in H0. rewrite next_inst in H0.
           pose proof fetch_insts as Hfetch2.
           specialize (Hfetch2 (instsBefore ++ [IAdd a b c]) instsAfter IExit []).
           specialize (Hfetch2 (Nat.add (length instsBefore) 1)).
           rewrite app_length in Hfetch2.
           rewrite Hfetch2 in H0.
           *** unfold add_regs in H0. simpl in H0. rewrite H8 in H0.
               compute in H0. inversion H0. rewrite <- H9 in H2. simpl in H2.
               rewrite <- H2. reflexivity.
           *** reflexivity.
        ** reflexivity.
  + (* s = SIf cond trueEval falseEval *)
    admit.
  + (* s = SSeq s1 s2 *)
    admit.
  + (* s = SLit a v *)
    admit.
  + (* s = SNop *)
    admit.
Admitted.