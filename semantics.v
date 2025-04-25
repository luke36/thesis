Require Import Unicode.Utf8_core.
Require Import Strings.String.
Require Import ZArith.ZArith.
Require Import QArith.QArith.
Require Import Lists.List.

Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import FP.SetsFixedpoints.

Require Import thesis.interval.
Require Import thesis.lang.

Local Open Scope Z.
Local Open Scope sets.

(* Semantics. *)

Inductive cell :=
| CEmp: cell
| CZ: I → Z → cell (* fractional permission *)
| CUndef: cell
| CFun: string → cell.

Definition writable (v: cell): Prop :=
  match v with CZ q _ => q = I1 | CUndef => True | _ => False end.

Definition heap := Z → cell.

Definition stack := Z → Z.

Definition regs := reg → Z.

Definition LΣ: Type := regs * stack * heap.

#[ global ] Notation "'rg' x" := (fst (fst x)) (at level 1).
#[ global ] Notation "'st' x" := (snd (fst x)) (at level 1).
Notation "'hp'" := snd (only parsing).

Definition sem_ok: Type :=
  (string * list Z * heap + LΣ) → (Z * heap + LΣ) → Prop.

Definition sem_er: Type :=
  (string * list Z * heap + LΣ) → Prop.

Definition equal_but (l: Z) (σ σ': heap): Prop := ∀ l', l ≠ l' → σ l' = σ' l'.

(* Machine Code. *)

Definition ins_sem_ok := LΣ → LΣ → Prop.
Definition ins_sem_er := LΣ → Prop.

Definition set_reg r n: LΣ → LΣ → Prop :=
  λ σ σ', rg σ' r = n ∧ (∀ r', r' ≠ r → r' ≠ PC → rg σ r = rg σ' r)
        ∧ st σ = st σ' ∧ hp σ = hp σ'.

Definition inc_pc (n: Z): LΣ → LΣ → Prop := λ σ σ', rg σ' PC = rg σ PC + n.

Definition eval_nop_ok: ins_sem_ok := inc_pc 1.

Definition eval_jmp_ok (r₁ r₂: reg): ins_sem_ok :=
  λ σ σ', rg σ r₁ > 0 ∧ set_reg PC (rg σ PC + rg σ r₂) σ σ' 
        ∨ rg σ r₁ <= 0 ∧ set_reg PC (rg σ PC + 3) σ σ'.

Section eval_call.

  Variable χ_ok: sem_ok.
  Variable χ_er: sem_er.

  Fixpoint hold_arg_rec (i: Z) (vs: list Z) (σ: LΣ): Prop :=
    match vs with
    | nil => True
    | cons v vs' =>
        (match i with
         | 0 => rg σ R0 = v
         | 1 => rg σ R1 = v
         | _ => st σ (rg σ SP) = v
         end) ∧ hold_arg_rec (i + 1) vs' σ
    end.

  Definition before_call (vs: list Z) (h: heap) (σ: LΣ): Prop :=
    hold_arg_rec 0 vs σ ∧ h = hp σ.

  Definition ret_reg := R0.

  Definition callee_saved (r: reg): Prop :=
    match r with SP | R4 | R5 => True | _ => False end.

  Definition well_preserve (σ σ': LΣ): Prop :=
    (∀ l, l < rg σ SP → st σ l = st σ' l)
  ∧ (∀ r, callee_saved r → rg σ r = rg σ' r).

  Let eval_call_ok_mach r: ins_sem_ok :=
    λ σ σ', ∃ σ₁ σ₂, (¬ ∃ f, hp σ (rg σ r) = CFun f) 
          ∧ set_reg PC (rg σ r) σ σ₁ ∧ set_reg PC (rg σ PC + 2) σ₂ σ'
          ∧ χ_ok (inr σ₁) (inr σ₂).

  Let eval_call_ok_c r: ins_sem_ok :=
    λ σ σ', ∃ f vs τ₁ n τ₂,
        hp σ (rg σ r) = CFun f
      ∧ before_call vs τ₁ σ
      ∧ χ_ok (inl (f, vs, τ₁)) (inl (n, τ₂))
      ∧ τ₂ = hp σ'
      ∧ well_preserve σ σ'
      ∧ inc_pc 2 σ σ'
      ∧ rg σ' ret_reg = n.

  Let eval_call_er_mach r: ins_sem_er :=
    λ σ, ∃ σ₁, (¬ ∃ f, hp σ (rg σ r) = CFun f) ∧ set_reg PC (rg σ r) σ σ₁ ∧  χ_er (inr σ₁).

  Let eval_call_er_c r: ins_sem_er :=
    λ σ, ∃ f vs τ₁,
        hp σ (rg σ r) = CFun f
      ∧ before_call vs τ₁ σ
      ∧ χ_er (inl (f, vs, τ₁)).

  Definition eval_call_ok r := eval_call_ok_mach r ∪ eval_call_ok_c r.
  Definition eval_call_er r := eval_call_er_mach r ∪ eval_call_er_c r.

End eval_call.

Definition eval_const_ok n r: ins_sem_ok :=
  λ σ σ', r ≠ PC ∧ set_reg r n σ σ' ∧ inc_pc 3 σ σ'.
Definition eval_const_er (n: Z) r: ins_sem_er :=
  λ _, r = PC.
Definition eval_arith_op (op: arith_op): Z → Z → Z :=
  match op with OAdd => Z.add | OSub => Z.sub | OMul => Z.mul end.

Definition eval_arith_ok op r₁ r₂ :=
  λ σ σ', r₂ ≠ PC ∧ set_reg r₂ (op (rg σ r₂) (rg σ r₁)) σ σ' ∧ inc_pc 3 σ σ'.
Definition eval_arith_er (op: arith_op) (r₁ r₂: reg): ins_sem_er :=
  λ _, r₂ = PC.

Definition eval_load_ok r₁ r₂ :=
  λ σ σ', ∃ q n, hp σ (rg σ r₁) = CZ q n ∧ set_reg r₂ n σ σ' ∧ inc_pc 3 σ σ'.
Definition eval_load_er r₁ r₂: ins_sem_er :=
  λ σ, r₂ = PC ∨ ¬ ∃ q n, hp σ (rg σ r₁) = CZ q n.

Definition only_inc_pc (n: Z): LΣ → LΣ → Prop :=
  λ σ σ', rg σ' PC = rg σ PC + n ∧ ∀ r, r ≠ PC → rg σ r = rg σ' r.

Definition eval_store_ok r₁ r₂: ins_sem_ok :=
  λ σ σ', writable (hp σ (rg σ r₂)) ∧ only_inc_pc 3 σ σ' ∧ st σ = st σ'
        ∧ hp σ' (rg σ r₂) = CZ I1 (rg σ r₁) ∧ equal_but (rg σ r₂) (hp σ) (hp σ').
Definition eval_store_er (r₁ r₂: reg): ins_sem_er :=
  λ σ, ¬ writable (hp σ (rg σ r₂)).

Definition eval_load_stack_ok r₁ r₂ :=
  λ σ σ', set_reg r₂ (st σ (rg σ r₁)) σ σ' ∧ inc_pc 3 σ σ'.
Definition eval_load_stack_er (r₁ r₂: reg): ins_sem_er :=
  λ _, r₂ = PC.

Definition eval_store_stack_ok r₁ r₂: ins_sem_ok :=
  λ σ σ', only_inc_pc 3 σ σ' ∧ hp σ = hp σ'
        ∧ st σ' (rg σ r₂) = rg σ r₁ ∧ ∀ l, l ≠ (rg σ r₂) → st σ l = st σ' l.

Section eval_ins.

  Variable χ_ok: sem_ok.
  Variable χ_er: sem_er.

  Definition eval_ins_ok i :=
    match i with
    | IErr => ∅
    | INop => eval_nop_ok
    | IRet => ∅
    | ICall r => eval_call_ok χ_ok r
    | IJmp r n => eval_jmp_ok r n
    | IConst n r => eval_const_ok n r
    | IArith op r₁ r₂ => eval_arith_ok (eval_arith_op op) r₁ r₂
    | ILoad r₁ r₂ => eval_load_ok r₁ r₂
    | IStore r₁ r₂ => eval_store_ok r₁ r₂
    | ILoadStack r₁ r₂ => eval_load_stack_ok r₁ r₂
    | IStoreStack r₁ r₂ => eval_store_stack_ok r₁ r₂
    end.

  Definition eval_ins_er i :=
    match i with
    | IErr => Sets.full
    | INop => ∅
    | IRet => ∅
    | ICall r => eval_call_er χ_er r
    | IJmp r n => ∅
    | IConst n r => eval_const_er n r
    | IArith op r₁ r₂ => eval_arith_er op r₁ r₂
    | ILoad r₁ r₂ => eval_load_er r₁ r₂
    | IStore r₁ r₂ => eval_store_er r₁ r₂
    | ILoadStack r₁ r₂ => eval_load_stack_er r₁ r₂
    | IStoreStack r₁ r₂ => ∅
    end.

  Definition cur_ins: LΣ → ins :=
    λ σ,
      match hp σ (rg σ PC) with
      | CZ _ n =>
          match decode n with
          | inl (inl i) => i
          | inl (inr f) =>
              match hp σ (rg σ PC + 1) with
              | CZ _ n => f n
              | _ => IErr
              end
          | inr f =>
              match hp σ (rg σ PC + 1), hp σ (rg σ PC + 2) with
              | CZ _ n, CZ _ m => f n m
              | _, _ => IErr
              end
          end
      | _ => IErr
      end.

  Definition final: LΣ → Prop := λ σ, cur_ins σ = IRet.

  Definition step: LΣ → LΣ → Prop := λ σ σ', eval_ins_ok (cur_ins σ) σ σ'. 

  Definition abort: LΣ → Prop := λ σ, eval_ins_er (cur_ins σ) σ.

  Inductive steps: LΣ → LΣ → Type :=
  | ss_nil: ∀ σ, steps σ σ
  | ss_cons: ∀ σ σ₁ σ', step σ σ₁ → steps σ₁ σ' → steps σ σ'.

  #[ global ] Arguments ss_nil {σ}.
  #[ global ] Arguments ss_cons {σ σ₁ σ'}.

  Definition eval_mach_ok: LΣ → LΣ → Prop := λ σ σ', ∃ _: steps σ σ', final σ'.

  Definition eval_mach_er: LΣ → Prop := λ σ, ∃ σ' (_: steps σ σ'), abort σ'.

End eval_ins.

(* Machine Code End. *)

Definition expr_sem_ok := heap → Z → heap → Prop.

Definition expr_sem_er := heap → Prop.

Definition expr_sem: Type := expr_sem_ok * expr_sem_er.

Notation "'ok'" := fst (only parsing).
Notation "'er'" := snd (only parsing).

Definition pure n: expr_sem_ok := λ σ m σ', n = m ∧ σ = σ'.

Definition eval_val (x: Z): expr_sem := (pure x, ∅).

Definition eval_bind (e₁: expr_sem) (e₂: Z → expr_sem): expr_sem :=
  (λ σ n σ', ∃ m σ₁, ok e₁ σ m σ₁ ∧ ok (e₂ m) σ₁ n σ',
   λ σ, er e₁ σ ∨ ∃ n σ₁, ok e₁ σ n σ₁ ∧ er (e₂ n) σ₁).

Definition eval_fix (e: expr_sem → expr_sem): expr_sem :=
  let Ok := Lfix (λ X, ok (e (X, ∅))) in
  let Er := Lfix (λ X, er (e (Ok, X))) in
  (Ok, Er).

Definition eval_skip: expr_sem := (λ σ _ σ', σ = σ', ∅).

Definition eval_error: expr_sem := (∅, Sets.full).

Definition eval_choice (e₁ e₂: expr_sem): expr_sem := (ok e₁ ∪ ok e₂, er e₁ ∪ er e₂).

Definition eval_assume (e: Z): expr_sem := (λ σ _ σ', e ≠ 0 ∧ σ = σ', ∅).

Definition eval_fun_addr (f: string): expr_sem := (λ σ l σ', σ = σ' ∧ σ l = CFun f, ∅).

Section eval_call.

  Variable χ_ok: sem_ok.
  Variable χ_er: sem_er.

  Let eval_call_ok_c (e: Z) (es: list Z): expr_sem_ok :=
    λ σ n σ', ∃ f, σ e = CFun f ∧ χ_ok (inl (f, es, σ)) (inl (n, σ')).

  Let eval_call_ok_mach (e: Z) (es: list Z): expr_sem_ok :=
    λ σ n σ', ∃ τ₁ τ₂,
        ¬ (∃ f, σ e = CFun f)
      ∧ before_call es σ τ₁ ∧ rg τ₁ PC = e
      ∧ χ_ok (inr τ₁) (inr τ₂)
      ∧ rg τ₂ ret_reg = n ∧ well_preserve τ₁ τ₂
      ∧ σ' = (hp τ₂).

  Let eval_call_er_c (e: Z) (es: list Z): expr_sem_er :=
    λ σ, ∃ f, σ e = CFun f ∧ χ_er (inl (f, es, σ)).

  Let eval_call_er_mach (e: Z) (es: list Z): expr_sem_er :=
    λ σ, ¬ (∃ f, σ e = CFun f) ∧ ∃ τ₁,
          before_call es σ τ₁ ∧ χ_er (inr τ₁)
        ∨ ∃ τ₂, χ_ok (inr τ₁) (inr τ₂)
              ∧ ¬ well_preserve τ₁ τ₂.
  
  Definition eval_call (e: Z) (es: list Z): expr_sem :=
    (eval_call_ok_c e es ∪ eval_call_ok_mach e es,
     eval_call_er_c e es ∪ eval_call_er_mach e es).

End eval_call.

Definition eval_store (e₁ e₂: Z): expr_sem :=
  (λ σ _ σ', writable (σ e₁) ∧ σ' e₁ = CZ I1 e₂ ∧ equal_but e₁ σ σ',
   λ σ, ¬ writable (σ e₁)).

Definition eval_load (e: Z): expr_sem :=
  (λ σ n σ', ∃ q, σ e = CZ q n ∧ σ = σ',
   λ σ, ¬ ∃ q n, σ e = CZ q n).

Definition eval_comp_op (op: compare_op): Z → Z → Prop :=
  match op with OEq => eq | OLe => Z.le | OLt => Z.lt end.

Definition eval_arith op (e₁ e₂: Z): expr_sem := (pure (op e₁ e₂), ∅).

Definition eval_comp op (e₁ e₂: Z): expr_sem :=
  (λ σ n σ', (op e₁ e₂ ∧ n = 1 ∨ (¬ op e₁ e₂) ∧ n = 0) ∧ σ = σ', ∅).

Section eval_expr.

  Variable χ_ok: sem_ok.
  Variable χ_er: sem_er.

  Fixpoint eval_expr' (e: expr Z expr_sem): expr_sem :=
    match e with
    | EVar x => eval_val x
    | EFixVar x => x
    | EVal n => eval_val n
    | EBind e₁ e₂ => eval_bind (eval_expr' e₁) (λ n, eval_expr' (e₂ n))
    | EFix e => eval_fix (λ x, eval_expr' (e x))
    | ESkip => eval_skip
    | EError => eval_error
    | EChoice e₁ e₂ => eval_choice (eval_expr' e₁) (eval_expr' e₂)
    | EAssume e => eval_assume e
    | EFunAddr f => eval_fun_addr f
    | ECall e es => eval_call χ_ok χ_er e es
    | EStore e₁ e₂ => eval_store e₁ e₂
    | ELoad e => eval_load e
    | EArith op e₁ e₂ => eval_arith (eval_arith_op op) e₁ e₂
    | EComp op e₁ e₂ => eval_comp (eval_comp_op op) e₁ e₂
    | _ => (∅, ∅)
    end.

  Definition eval_expr (e: Expr) := eval_expr' (e Z expr_sem).

  Definition eval_fun_ok (f: Fun): string → list Z → expr_sem_ok :=
    λ f' vs σ n σ', f' = fst f ∧ ok (eval_expr' (snd f Z expr_sem vs)) σ n σ'.

  Definition eval_fun_er (f: Fun): string → list Z → expr_sem_er :=
    λ f' vs σ, f' = fst f ∧ er (eval_expr' (snd f Z expr_sem vs)) σ.

End eval_expr.

Definition eval_prog_ok χ_ok χ_er (p: prog): sem_ok :=
  λ x y,
    (∃ f vs σ n σ' F,
        x = inl (f, vs, σ) ∧ y = inl (n, σ')
      ∧ In F p ∧ eval_fun_ok χ_ok χ_er F f vs σ n σ')
  ∨ (∃ σ σ',
        x = inr σ ∧ y = inr σ'
      ∧ eval_mach_ok χ_ok σ σ').

Definition eval_prog_er χ_ok χ_er (p: prog): sem_er :=
  λ x,
    (∃ f vs σ F,
        x = inl (f, vs, σ)
      ∧ In F p ∧ eval_fun_er χ_ok χ_er F f vs σ)
  ∨ (∃ σ,
        x = inr σ
      ∧ eval_mach_er χ_ok χ_er σ).

Definition eval_ok (p: prog): sem_ok :=
  Lfix (λ X, eval_prog_ok X ∅ p).

Definition eval_er (p: prog): sem_er :=
  Lfix (λ X, eval_prog_er (eval_ok p) X p).

(* Semantics End. *)
