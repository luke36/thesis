Require Import Unicode.Utf8_core.
Require Import Lists.List. Import ListNotations.
Require Import Strings.String.
Require Import ZArith.ZArith.
Local Open Scope string.
Local Open Scope Z.

(* Language. *)

Inductive arith_op :=
| OAdd | OSub | OMul.

Inductive compare_op :=
| OEq | OLe | OLt.

Inductive expr (V: Type) (W: Type) :=
| EVar: V → expr V W
| EFixVar: W → expr V W
| EVal: Z → expr V W
| EBind: expr V W → (V → expr V W) → expr V W
| EFix: (W → expr V W) → expr V W
| ESkip: expr V W
| EError: expr V W
| EChoice: expr V W → expr V W → expr V W
| EAssume: V → expr V W
| EFunAddr: string → expr V W
| ECall: V → list V → expr V W
| EAlloc: V → expr V W
| EDealloc: V → expr V W
| EStore: V → V → expr V W
| ELoad: V → expr V W
| EArith: arith_op → V → V → expr V W
| EComp: compare_op → V → V → expr V W.

Arguments EVar {V} {W}.
Arguments EFixVar {V} {W}.
Arguments EVal {V} {W}.
Arguments EBind {V} {W}.
Arguments EFix {V} {W}.
Arguments ESkip {V} {W}.
Arguments EError {V} {W}.
Arguments EChoice {V} {W}.
Arguments EAssume {V} {W}.
Arguments EFunAddr {V} {W}.
Arguments ECall {V} {W}.
Arguments EAlloc {V} {W}.
Arguments EDealloc {V} {W}.
Arguments EStore {V} {W}.
Arguments ELoad {V} {W}.
Arguments EArith {V} {W}.
Arguments EComp {V} {W}.

Definition Expr := ∀ V W, expr V W.

Definition Fun: Type := string * ∀ V W, list V → expr V W.

Definition prog := list Fun.

Inductive cexpr (V: Type) :=
| CEVar: V → cexpr V
| CEVal: Z → cexpr V
| CEBind: cexpr V → (V → cexpr V) → cexpr V
| CEWhile: cexpr V → cexpr V → cexpr V
| CESkip: cexpr V
| CEIf: cexpr V → cexpr V → cexpr V → cexpr V
| CEFunAddr: string → cexpr V
| CECall: cexpr V → list (cexpr V) → cexpr V
| CEAlloc: cexpr V → cexpr V
| CEDealloc: cexpr V → cexpr V
| CEStore: cexpr V → cexpr V → cexpr V
| CELoad: cexpr V → cexpr V
| CEArith: arith_op → cexpr V → cexpr V → cexpr V
| CEComp: compare_op → cexpr V → cexpr V → cexpr V.

Arguments CEVar {V}.
Arguments CEVal {V}.
Arguments CEBind {V}.
Arguments CEWhile {V}.
Arguments CESkip {V}.
Arguments CEIf {V}.
Arguments CEFunAddr {V}.
Arguments CECall {V}.
Arguments CEAlloc {V}.
Arguments CEDealloc {V}.
Arguments CEStore {V}.
Arguments CELoad {V}.
Arguments CEArith {V}.
Arguments CEComp {V}.

Definition CExpr := ∀ V, cexpr V.

Section compile.

  Variable V W: Type.

  Section compile_call.

    Variable compile: cexpr V → expr V W.

    Fixpoint compile_call (es: list (cexpr V)) (k: list V → expr V W) :=
      match es with
      | nil => k nil
      | cons e es' => EBind (compile e) (λ v, compile_call es' (λ vs, k (cons v vs)))
      end.

  End compile_call.

  Definition EIf c e₁ e₂: expr V W :=
    (EBind c (λ c,
         EChoice (EBind (EAssume c) (λ _, e₁))
                 (EBind (EBind (EVal 0) (λ z, (EComp OEq c z))) (λ nc, EBind (EAssume nc) (λ _, e₂))))).

  Fixpoint compile (ce: cexpr V): expr V W :=
    match ce with
    | CEVar x => EVar x
    | CEVal n => EVal n
    | CEBind e₁ e₂ => EBind (compile e₁) (λ v, compile (e₂ v))
    | CEWhile c e => EFix (λ v, EIf (compile c) (EBind (compile e) (λ _, EFixVar v)) ESkip)
    | CESkip => ESkip
    | CEIf c e₁ e₂ => EIf (compile c) (compile e₁) (compile e₂)
    | CEFunAddr f => EFunAddr f
    | CECall e es => EBind (compile e) (λ f, compile_call compile es (λ vs, ECall f vs))
    | CEAlloc e => EBind (compile e) (λ v, EAlloc v)
    | CEDealloc e => EBind (compile e) (λ v, EDealloc v)
    | CEStore e₁ e₂ => EBind (compile e₁) (λ l, EBind (compile e₂) (λ v, EStore l v))
    | CELoad e => EBind (compile e) (λ v, ELoad v)
    | CEArith op e₁ e₂ => EBind (compile e₁) (λ v₁, EBind (compile e₂) (λ v₂, EArith op v₁ v₂))
    | CEComp op e₁ e₂ => EBind (compile e₁) (λ v₁, EBind (compile e₂) (λ v₂, EComp op v₁ v₂))
    end.

End compile.

Definition Compile (ce: CExpr): Expr := λ V W, compile _ _ (ce V).

Inductive reg :=
| PC: reg | SP: reg | R0: reg | R1: reg | R2: reg | R3: reg | R4: reg | R5: reg.

Inductive ins :=
| IErr: ins | INop: ins | IRet: ins
| ICall: reg → ins
| IJmp: reg → Z → ins
| IConst: Z → reg → ins
| IArith: arith_op → reg → reg → ins
| ILoad: reg → reg → ins
| IStore: reg → reg → ins
| ILoadStack: reg → reg → ins
| IStoreStack: reg → reg → ins.

Definition decode_reg (k: reg → ins) (r: Z): ins :=
  match r with
  | 0 => k PC | 1 => k SP | 2 => k R0 | 3 => k R1
  | 4 => k R2 | 5 => k R3 | 6 => k R4 | 7 => k R5
  | _ => IErr
  end.

Definition decode (n: Z): ins + (Z → ins) + (Z → Z → ins) :=
  match n with
  | 0 => inl (inl INop)
  | 1 => inl (inl IRet)
  | 2 => inl (inr (decode_reg ICall))
  | 3 => inr (λ n m, decode_reg (λ r, IJmp r m) n)
  | 4 => inr (λ n, decode_reg (IConst n))
  | 5 => inr (λ n m, decode_reg (λ r, decode_reg (IArith OAdd r) m) n)
  | 6 => inr (λ n m, decode_reg (λ r, decode_reg (IArith OSub r) m) n)
  | 7 => inr (λ n m, decode_reg (λ r, decode_reg (IArith OMul r) m) n)
  | 8 => inr (λ n m, decode_reg (λ r, decode_reg (ILoad r) m) n)
  | 9 => inr (λ n m, decode_reg (λ r, decode_reg (IStore r) m) n)
  | 10 => inr (λ n m, decode_reg (λ r, decode_reg (ILoadStack r) m) n)
  | 11 => inr (λ n m, decode_reg (λ r, decode_reg (IStoreStack r) m) n)
  | _ => inl (inl IErr)
  end.

Definition encode_reg (r: reg) :=
  match r with
  | PC => 0 | SP => 1 | R0 => 2 | R1 => 3
  | R2 => 4 | R3 => 5 | R4 => 6 | R5 => 7
  end.

Definition encode (i: ins): list Z :=
  match i with
  | INop => [0]
  | IRet => [1]
  | ICall r => [2; encode_reg r]
  | IJmp r n => [3; encode_reg r; n]
  | IConst n r => [4; n; encode_reg r]
  | IArith OAdd r₁ r₂ => [5; encode_reg r₁; encode_reg r₂]
  | IArith OSub r₁ r₂ => [6; encode_reg r₁; encode_reg r₂]
  | IArith OMul r₁ r₂ => [7; encode_reg r₁; encode_reg r₂]
  | ILoad r₁ r₂ => [8; encode_reg r₁; encode_reg r₂]
  | IStore r₁ r₂ => [9; encode_reg r₁; encode_reg r₂]
  | ILoadStack r₁ r₂ => [10; encode_reg r₁; encode_reg r₂]
  | IStoreStack r₁ r₂ => [11; encode_reg r₁; encode_reg r₂]
  | _ => [12]
  end.

Lemma decode_encode: ∀ i,
    match encode i with
    | [n] => decode n = inl (inl i)
    | [n;m] =>
        match decode n with
        | inl (inr f) => f m = i
        | _ => False
        end
    | [n;m;p] =>
        match decode n with
        | inr f => f m p = i
        | _ => False
        end
    | _ => False
    end.
Proof.
  intros i.
  destruct i; simpl; try reflexivity;
  try (destruct r; simpl; reflexivity);
  try (destruct r; destruct r0; reflexivity).
  destruct a; destruct r; destruct r0; reflexivity.
Qed.

(* Language End. *)
