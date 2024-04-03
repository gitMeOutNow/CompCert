(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract syntax and semantics for AArch64 assembly language *)

Require Import Coqlib Zbits Maps.
Require Import AST Integers Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Locations Conventions Asm.
Require Import Coq.Lists.List.
Import ListNotations.
Require Stacklayout.

(** * Abstract syntax *)


Definition processor_id := Z.
Definition processor_reg := (processor_id * preg) % type.
(* 
Definition preg_uri: Type := (processor_id * preg) % type.
Definition ireg_uri: Type := (processor_id * ireg) % type.
Definition freg_uri: Type := (processor_id * freg) % type. *)
(* 
Definition preg_comp_to_uri: (processor_id * preg) % type -> preg_uri := fun x => x.

Coercion preg_comp_to_uri: (processor_id * preg) % type >-> preg_uri.

Inductive processor_reg : Type :=
 | preg_to_proc_reg: preg_uri -> processor_reg
 | ireg_to_proc_reg: ireg_uri -> processor_reg
 | freg_to_proc_reg: freg_uri -> processor_reg. 


Coercion preg_to_proc_reg: preg_uri>-> processor_reg.
Coercion ireg_to_proc_reg: ireg_uri>-> processor_reg.
Coercion freg_to_proc_reg: freg_uri>-> processor_reg. *)

Remark pr_eq:
  forall (r1 r2: processor_reg), {r1 = r2} + {r1 <> r2}.
Proof.
    (* decide equality. destruct p; destruct p0; decide equality. apply preg_eq. apply Z.eq_dec.
    decide equality. destruct p. apply ireg_eq; destruct a; apply ireg_eq. apply ireg_eq.
    decide equality. apply Z.eq_dec.
    decide equality. apply freg_eq. apply Z.eq_dec.  *)

    decide equality. apply preg_eq. apply Z.eq_dec.
Qed.

Remark pr_eq_identity:
    forall (r: processor_reg), r = r.
Proof. reflexivity. Qed.

Module PREq.
  Definition t := processor_reg.
  Definition eq := pr_eq.
End PREq. 



Module PRmap := EMap(PREq).

Inductive instruction: Type :=
  (** Branches *)
  | Pb (lbl: label) (pid: processor_id)                                            (**r branch *)
  | Pbc (c: testcond) (lbl: label) (pid: processor_id)                             (**r conditional branch *)
  | Pbl (id: ident) (sg: signature) (pid: processor_id)                            (**r jump to function and link *)
  | Pbs (id: ident) (sg: signature) (pid: processor_id)                            (**r jump to function *)
  | Pblr (r: ireg) (sg: signature) (pid: processor_id)                             (**r indirect jump and link *)
  | Pbr (r: ireg) (sg: signature) (pid: processor_id)                              (**r indirect jump *)
  | Pret (r: ireg) (pid: processor_id)                                             (**r return *)
  | Pcbnz (sz: isize) (r: ireg) (lbl: label) (pid: processor_id)                   (**r branch if not zero *)
  | Pcbz (sz: isize) (r: ireg) (lbl: label) (pid: processor_id)                    (**r branch if zero *)
  | Ptbnz (sz: isize) (r: ireg) (n: int) (lbl: label) (pid: processor_id)          (**r branch if bit n is not zero *)
  | Ptbz (sz: isize) (r: ireg) (n: int) (lbl: label) (pid: processor_id)           (**r branch if bit n is zero *)
  (** Memory loads and stores *)
  | Pldrw (rd: ireg) (a: addressing) (pid: processor_id)                           (**r load int32 *)
  | Pldrw_a (rd: ireg) (a: addressing) (pid: processor_id)                         (**r load int32 as any32 *)
  | Pldrx (rd: ireg) (a: addressing) (pid: processor_id)                           (**r load int64 *)
  | Pldrx_a (rd: ireg) (a: addressing) (pid: processor_id)                         (**r load int64 as any64 *)
  | Pldrb (sz: isize) (rd: ireg) (a: addressing) (pid: processor_id)               (**r load int8, zero-extend *)
  | Pldrsb (sz: isize) (rd: ireg) (a: addressing) (pid: processor_id)              (**r load int8, sign-extend *)
  | Pldrh (sz: isize) (rd: ireg) (a: addressing) (pid: processor_id)               (**r load int16, zero-extend *)
  | Pldrsh (sz: isize) (rd: ireg) (a: addressing) (pid: processor_id)              (**r load int16, sign-extend *)
  | Pldrzw (rd: ireg) (a: addressing) (pid: processor_id)                          (**r load int32, zero-extend to int64 *)
  | Pldrsw (rd: ireg) (a: addressing) (pid: processor_id)                          (**r load int32, sign-extend to int64 *)
  | Pldp (rd1 rd2: ireg) (a: addressing) (pid: processor_id)                        (**r load two int64 *)
  | Pstrw (rs: ireg) (a: addressing) (pid: processor_id)                           (**r store int32 *)
  | Pstrw_a (rs: ireg) (a: addressing) (pid: processor_id)                         (**r store int32 as any32 *)
  | Pstrx (rs: ireg) (a: addressing) (pid: processor_id)                           (**r store int64 *)
  | Pstrx_a (rs: ireg) (a: addressing) (pid: processor_id)                         (**r store int64 as any64 *)
  | Pstrb (rs: ireg) (a: addressing) (pid: processor_id)                           (**r store int8 *)
  | Pstrh (rs: ireg) (a: addressing) (pid: processor_id)                           (**r store int16 *)
  | Pstp (rs1 rs2: ireg) (a: addressing) (pid: processor_id)                       (**r store two int64 *)
  (** Integer arithmetic, immediate *)
  | Paddimm (sz: isize) (rd: iregsp) (r1: iregsp) (n: Z) (pid: processor_id)       (**r addition *)
  | Psubimm (sz: isize) (rd: iregsp) (r1: iregsp) (n: Z) (pid: processor_id)       (**r subtraction *)
  | Pcmpimm (sz: isize) (r1: ireg) (n: Z) (pid: processor_id)                      (**r compare *)
  | Pcmnimm (sz: isize) (r1: ireg) (n: Z) (pid: processor_id)                      (**r compare negative *)
  (** Move integer register *)
  | Pmov (rd: iregsp) (r1: iregsp) (pid: processor_id) 
  (** Logical, immediate *)
  | Pandimm (sz: isize) (rd: ireg) (r1: ireg0) (n: Z) (pid: processor_id)          (**r and *)
  | Peorimm (sz: isize) (rd: ireg) (r1: ireg0) (n: Z) (pid: processor_id)          (**r xor *)
  | Porrimm (sz: isize) (rd: ireg) (r1: ireg0) (n: Z) (pid: processor_id)          (**r or *)
  | Ptstimm (sz: isize) (r1: ireg) (n: Z) (pid: processor_id)                      (**r and, then set flags *)
  (** Move wide immediate *)
  | Pmovz (sz: isize) (rd: ireg) (n: Z) (pos: Z) (pid: processor_id)               (**r move [n << pos] to [rd] *)
  | Pmovn (sz: isize) (rd: ireg) (n: Z) (pos: Z) (pid: processor_id)               (**r move [NOT(n << pos)] to [rd] *)
  | Pmovk (sz: isize) (rd: ireg) (n: Z) (pos: Z) (pid: processor_id)               (**r insert 16 bits of [n] at [pos] in rd *)
  (** PC-relative addressing *)
  | Padrp (rd: ireg) (id: ident) (ofs: ptrofs) (pid: processor_id)                 (**r set [rd] to high address of [id + ofs] *)
  | Paddadr (rd: ireg) (r1: ireg) (id: ident) (ofs: ptrofs) (pid: processor_id)    (**r add the low address of [id + ofs] *)
  (** Bit-field operations *)
  | Psbfiz (sz: isize) (rd: ireg) (r1: ireg) (r: int) (s: Z) (pid: processor_id)   (**r sign extend and shift left *)
  | Psbfx (sz: isize) (rd: ireg) (r1: ireg) (r: int) (s: Z) (pid: processor_id)    (**r shift right and sign extend *)
  | Pubfiz (sz: isize) (rd: ireg) (r1: ireg) (r: int) (s: Z) (pid: processor_id)   (**r zero extend and shift left *)
  | Pubfx (sz: isize) (rd: ireg) (r1: ireg) (r: int) (s: Z) (pid: processor_id)    (**r shift right and zero extend *)
  (** Integer arithmetic, shifted register *)
  | Padd (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op) (pid: processor_id)  (**r addition *)
  | Psub (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op) (pid: processor_id)  (**r subtraction *)
  | Pcmp (sz: isize) (r1: ireg0) (r2: ireg) (s: shift_op) (pid: processor_id)      (**r compare *)
  | Pcmn (sz: isize) (r1: ireg0) (r2: ireg) (s: shift_op) (pid: processor_id)      (**r compare negative *)
  (** Integer arithmetic, extending register *)
  | Paddext (rd: iregsp) (r1: iregsp) (r2: ireg) (x: extend_op) (pid: processor_id)(**r int64-int32 add *)
  | Psubext (rd: iregsp) (r1: iregsp) (r2: ireg) (x: extend_op) (pid: processor_id)(**r int64-int32 sub *)
  | Pcmpext (r1: ireg) (r2: ireg) (x: extend_op) (pid: processor_id)               (**r int64-int32 cmp *)
  | Pcmnext (r1: ireg) (r2: ireg) (x: extend_op) (pid: processor_id)               (**r int64-int32 cmn *)
  (** Logical, shifted register *)
  | Pand (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op) (pid: processor_id)  (**r and *)
  | Pbic (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op) (pid: processor_id)  (**r and-not *)
  | Peon (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op) (pid: processor_id)  (**r xor-not *)
  | Peor (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op) (pid: processor_id)  (**r xor *)
  | Porr (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op) (pid: processor_id)  (**r or *)
  | Porn (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op) (pid: processor_id)   (**r or-not *)
  | Ptst (sz: isize) (r1: ireg0) (r2: ireg) (s: shift_op) (pid: processor_id)      (**r and, then set flags *)
  (** Variable shifts *)
  | Pasrv (sz: isize) (rd: ireg) (r1 r2: ireg) (pid: processor_id)                 (**r arithmetic right shift *)
  | Plslv (sz: isize) (rd: ireg) (r1 r2: ireg) (pid: processor_id)                 (**r left shift *)
  | Plsrv (sz: isize) (rd: ireg) (r1 r2: ireg) (pid: processor_id)                 (**r logical right shift *)
  | Prorv (sz: isize) (rd: ireg) (r1 r2: ireg) (pid: processor_id)                 (**r rotate right *)
  (** Bit operations *)
  | Pcls (sz: isize) (rd r1: ireg) (pid: processor_id)                             (**r count leading sign bits *)
  | Pclz (sz: isize) (rd r1: ireg) (pid: processor_id)                             (**r count leading zero bits *)
  | Prev (sz: isize) (rd r1: ireg) (pid: processor_id)                             (**r reverse bytes *)
  | Prev16 (sz: isize) (rd r1: ireg) (pid: processor_id)                           (**r reverse bytes in each 16-bit word *)
  | Prbit (sz: isize) (rd r1: ireg) (pid: processor_id)                            (**r reverse bits *)
  (** Conditional data processing *)
  | Pcsel (rd: ireg) (r1 r2: ireg) (c: testcond) (pid: processor_id)               (**r int conditional move *)
  | Pcset (rd: ireg) (c: testcond) (pid: processor_id)                             (**r set to 1/0 if cond is true/false *)
(*
  | Pcsetm (rd: ireg) (c: testcond) (pid: processor_id)                            (**r set to -1/0 if cond is true/false *)
*)
  (** Integer multiply/divide *)
  | Pmadd (sz: isize) (rd: ireg) (r1 r2: ireg) (r3: ireg0) (pid: processor_id)     (**r multiply-add *)
  | Pmsub (sz: isize) (rd: ireg) (r1 r2: ireg) (r3: ireg0) (pid: processor_id)     (**r multiply-sub *)
  | Psmulh (rd: ireg) (r1 r2: ireg) (pid: processor_id)                            (**r signed multiply high *)
  | Pumulh (rd: ireg) (r1 r2: ireg) (pid: processor_id)                            (**r unsigned multiply high *)
  | Psdiv (sz: isize) (rd: ireg) (r1 r2: ireg) (pid: processor_id)                 (**r signed division *)
  | Pudiv (sz: isize) (rd: ireg) (r1 r2: ireg) (pid: processor_id)                 (**r unsigned division *)
  (** Floating-point loads and stores *)
  | Pldrs (rd: freg) (a: addressing) (pid: processor_id)                           (**r load float32 (single precision) *)
  | Pldrd (rd: freg) (a: addressing) (pid: processor_id)                           (**r load float64 (double precision) *)
  | Pldrd_a (rd: freg) (a: addressing) (pid: processor_id)                         (**r load float64 as any64 *)
  | Pstrs (rs: freg) (a: addressing) (pid: processor_id)                           (**r store float32 *)
  | Pstrd (rs: freg) (a: addressing) (pid: processor_id)                           (**r store float64 *)
  | Pstrd_a (rs: freg) (a: addressing) (pid: processor_id)                         (**r store float64 as any64 *)
  (** Floating-point move *)
  | Pfmov (rd r1: freg) (pid: processor_id) 
  | Pfmovimms (rd: freg) (f: float32) (pid: processor_id)                          (**r load float32 constant *)
  | Pfmovimmd (rd: freg) (f: float) (pid: processor_id)                            (**r load float64 constant *)
  | Pfmovi (fsz: fsize) (rd: freg) (r1: ireg0) (pid: processor_id)                 (**r copy int reg to FP reg *)
  (** Floating-point conversions *)
  | Pfcvtds (rd r1: freg) (pid: processor_id)                                      (**r convert float32 to float64 *)
  | Pfcvtsd (rd r1: freg) (pid: processor_id)                                      (**r convert float64 to float32 *)
  | Pfcvtzs (isz: isize) (fsz: fsize) (rd: ireg) (r1: freg) (pid: processor_id)    (**r convert float to signed int *)
  | Pfcvtzu (isz: isize) (fsz: fsize) (rd: ireg) (r1: freg) (pid: processor_id)    (**r convert float to unsigned int *)
  | Pscvtf (fsz: fsize) (isz: isize) (rd: freg) (r1: ireg) (pid: processor_id)     (**r convert signed int to float *)
  | Pucvtf (fsz: fsize) (isz: isize) (rd: freg) (r1: ireg) (pid: processor_id)     (**r convert unsigned int to float *)
  (** Floating-point arithmetic *)
  | Pfabs (sz: fsize) (rd r1: freg) (pid: processor_id)                            (**r absolute value *)
  | Pfneg (sz: fsize) (rd r1: freg) (pid: processor_id)                            (**r negation *)
  | Pfsqrt (sz: fsize) (rd r1: freg) (pid: processor_id)                           (**r square root *)
  | Pfadd (sz: fsize) (rd r1 r2: freg) (pid: processor_id)                         (**r addition *)
  | Pfdiv (sz: fsize) (rd r1 r2: freg) (pid: processor_id)                         (**r division *)
  | Pfmul (sz: fsize) (rd r1 r2: freg) (pid: processor_id)                         (**r multiplication *)
  | Pfnmul (sz: fsize) (rd r1 r2: freg) (pid: processor_id)                        (**r multiply-negate *)
  | Pfsub (sz: fsize) (rd r1 r2: freg) (pid: processor_id)                         (**r subtraction *)
  | Pfmadd (sz: fsize) (rd r1 r2 r3: freg) (pid: processor_id)                     (**r [rd = r3 + r1 * r2] *)
  | Pfmsub (sz: fsize) (rd r1 r2 r3: freg) (pid: processor_id)                     (**r [rd = r3 - r1 * r2] *)
  | Pfnmadd (sz: fsize) (rd r1 r2 r3: freg) (pid: processor_id)                    (**r [rd = - r3 - r1 * r2] *)
  | Pfnmsub (sz: fsize) (rd r1 r2 r3: freg) (pid: processor_id)                    (**r [rd = - r3 + r1 * r2] *)
  | Pfmax (sz: fsize) (rd r1 r2: freg) (pid: processor_id)                         (**r maximum *)
  | Pfmin (sz: fsize) (rd r1 r2: freg) (pid: processor_id)                         (**r minimum *)
  (** Floating-point comparison *)
  | Pfcmp (sz: fsize) (r1 r2: freg) (pid: processor_id)                            (**r compare [r1] and [r2] *)
  | Pfcmp0 (sz: fsize) (r1: freg) (pid: processor_id)                              (**r compare [r1] and [+0.0] *)
  (** Floating-point conditional select *)
  | Pfsel (rd r1 r2: freg) (cond: testcond) (pid: processor_id) 
  (** Pseudo-instructions *)
  | Pallocframe (sz: Z) (linkofs: ptrofs) (pid: processor_id)                      (**r allocate new stack frame *)
  | Pfreeframe (sz: Z) (linkofs: ptrofs) (pid: processor_id)                       (**r deallocate stack frame and restore previous frame *)
  | Plabel (lbl: label) (pid: processor_id)                                        (**r define a code label *)
  | Ploadsymbol (rd: ireg) (id: ident) (pid: processor_id)                         (**r load the address of [id] *)
  | Pcvtsw2x (rd: ireg) (r1: ireg) (pid: processor_id)                             (**r sign-extend 32-bit int to 64-bit *)
  | Pcvtuw2x (rd: ireg) (r1: ireg) (pid: processor_id)                             (**r zero-extend 32-bit int to 64-bit *)
  | Pcvtx2w (rd: ireg) (pid: processor_id)                                         (**r retype a 64-bit int as a 32-bit int *)
  | Pbtbl (r1: ireg) (tbl: list label) (pid: processor_id)                         (**r N-way branch through a jump table *)
  | Pbuiltin (ef: external_function)
             (args: list (builtin_arg preg)) (res: builtin_res preg) (pid: processor_id)   (**r built-in function (pseudo) *)
  | Pnop (pid: processor_id)                                                            (**r no operation *)
  | Pcfi_adjust (ofs: int) (pid: processor_id)                                     (**r .cfi_adjust debug directive *)
  | Pcfi_rel_offset (ofs: int) (pid: processor_id)                                 (**r .cfi_rel_offset debug directive *)
  | Pincpc (pid: processor_id) (** my own thing, represents incrementing PC*)
.


(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and condition bits to either [Vzero] or [Vone]. *)


(** Map of processor id + regcode to val for that processor*)
Definition allregsets := PRmap.t val.



(* Bidirectionality hint -> helps convert processor_id, preg -> PRMap.t*)
Arguments pair {_ _} & _ _.

Definition ir0w (ars: allregsets) (r: ireg0) (pid: processor_id) : val :=
  match r with RR0 r => ars (pid, (IR r)) | XZR => Vint Int.zero end.
Definition ir0x (ars: allregsets) (r: ireg0) (pid: processor_id) : val :=
  match r with RR0 r => ars (pid, (IR r)) | XZR => Vlong Int64.zero end.

(** Concise notations for accessing and updating the values of registers. *)
Notation "a @ b" := (a b) (at level 1, only parsing).
Notation "a @ b <- c" := (PRmap.set b c a) (at level 1, b at next level).
Notation "a @@ c @@> b" := (ir0w a b c) (at level 1, only parsing).
Notation "a @@@ c @@@> b" := (ir0x a b c) (at level 1, only parsing).

Inductive outcome: Type := 
    | MemSimNext: allregsets -> mem -> outcome
    | MemSimJumpOut: allregsets -> mem -> outcome
    | MemSimStuck: outcome.


Definition goto_label (f: function) (lbl: label) (ars: allregsets) (pid: processor_id) (m: mem) :=
    match label_pos lbl 0 (fn_code f) with
    | None => MemSimStuck
    | Some pos =>
        match ars@(pid, PC) with
        | Vptr b ofs => MemSimJumpOut (ars@(pid, PC ) <- (Vptr b (Ptrofs.repr pos))) m
        | _ => MemSimStuck
        end
    end.

Definition eval_testcond (c: testcond) (ars: allregsets) (pid: processor_id): option bool :=
    match c with
    | TCeq =>                             (**r equal *)
        match ars@(pid, CZ) with
        | Vint n => Some (Int.eq n Int.one)
        | _ => None
        end
    | TCne =>                             (**r not equal *)
        match ars@(pid, CZ) with
        | Vint n => Some (Int.eq n Int.zero)
        | _ => None
        end
    | TClo =>                             (**r unsigned less than  *)
        match ars@(pid, CC) with
        | Vint n => Some (Int.eq n Int.zero)
        | _ => None
        end
    | TCls =>                             (**r unsigned less or equal *)
        match ars@(pid, CC), ars@(pid, CZ) with
        | Vint c, Vint z => Some (Int.eq c Int.zero || Int.eq z Int.one)
        | _, _ => None
        end
    | TChs =>                             (**r unsigned greater or equal *)
        match ars@(pid, CC) with
        | Vint n => Some (Int.eq n Int.one)
        | _ => None
        end
    | TChi =>                             (**r unsigned greater *)
        match ars@(pid, CC), ars@(pid, CZ) with
        | Vint c, Vint z => Some (Int.eq c Int.one && Int.eq z Int.zero)
        | _, _ => None
        end
    | TClt =>                             (**r signed less than *)
        match ars@(pid, CV), ars@(pid, CN) with
        | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.one)
        | _, _ => None
        end
    | TCle =>                             (**r signed less or equal *)
        match ars@(pid, CV), ars@(pid, CN), ars@(pid, CZ) with
        | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.one || Int.eq z Int.one)
        | _, _, _ => None
        end
    | TCge =>                             (**r signed greater or equal *)
        match ars@(pid, CV), ars@(pid, CN) with
        | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.zero)
        | _, _ => None
        end
    | TCgt =>                             (**r signed greater *)
        match ars@(pid, CV), ars@(pid, CN), ars@(pid, CZ) with
        | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.zero && Int.eq z Int.zero)
        | _, _, _ => None
        end
    | TCpl =>                             (**r positive *)
        match ars@(pid, CN) with
        | Vint n => Some (Int.eq n Int.zero)
        | _ => None
        end
    | TCmi =>                             (**r negative *)
        match ars@(pid, CN) with
        | Vint n => Some (Int.eq n Int.one)
        | _ => None
        end
    end.

Section RELSEM.
Variable ge: genv.


Definition eval_addressing (a: addressing) (ars: allregsets) (pid: processor_id): val :=
  match a with
  | ADimm base n => Val.addl ars@(pid, base) (Vlong n)
  | ADreg base r => Val.addl ars@(pid, base)  ars@(pid, r)
  | ADlsl base r n => Val.addl ars@(pid, base) (Val.shll ars@(pid, r) (Vint n))
  | ADsxt base r n => Val.addl ars@(pid, base) (Val.shll (Val.longofint ars@(pid, r)) (Vint n))
  | ADuxt base r n => Val.addl ars@(pid, base) (Val.shll (Val.longofintu ars@(pid, r)) (Vint n))
  | ADadr base id ofs => Val.addl ars@(pid, base) (symbol_low ge id ofs)
  | ADpostincr base n => Vundef (* not modeled yet *)
  end.

Definition exec_load (chunk: memory_chunk) (transf: val -> val)
    (a: addressing) (r: preg) (ars: allregsets) (pid: processor_id) (m: mem)  :=
    match Mem.loadv chunk m (eval_addressing a ars pid) with
    | None => MemSimStuck
    | Some v => MemSimNext (ars@(pid, r) <- (transf v)) m
    end.

Definition exec_store (chunk: memory_chunk)
    (a: addressing) (v: val)
    (ars: allregsets) (pid: processor_id) (m: mem) :=
match Mem.storev chunk m (eval_addressing a ars pid) v with
| None => MemSimStuck
| Some m' => MemSimNext ars m'
end.

Definition compare_int (ars: allregsets) (v1 v2: val) (m: mem) (pid: processor_id) :=
  ars@(pid, CN) <- (Val.negative (Val.sub v1 v2))
  @(pid, CZ)  <- (Val.cmpu (Mem.valid_pointer m) Ceq v1 v2)
  @(pid, CC)  <- (Val.cmpu (Mem.valid_pointer m) Cge v1 v2)
  @(pid, CV)  <- (Val.sub_overflow v1 v2).

Definition compare_long (ars: allregsets) (v1 v2: val) (m: mem) (pid: processor_id) :=
  ars@(pid, CN) <- (Val.negativel (Val.subl v1 v2))
  @(pid, CZ)  <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq v1 v2))
  @(pid, CC)  <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Cge v1 v2))
  @(pid, CV)  <- (Val.subl_overflow v1 v2).

  Definition compare_float (ars: allregsets) (v1 v2: val) (pid: processor_id) :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 =>
      ars@(pid, CN) <- (Val.of_bool (Float.cmp Clt f1 f2))
        @(pid, CZ) <- (Val.of_bool (Float.cmp Ceq f1 f2))
        @(pid, CC) <- (Val.of_bool (negb (Float.cmp Clt f1 f2)))
        @(pid, CV) <- (Val.of_bool (negb (Float.ordered f1 f2)))
  | _, _ =>
      ars@(pid, CN) <- Vundef
      @(pid, CZ) <- Vundef
      @(pid, CC) <- Vundef
      @(pid, CV) <- Vundef
  end.

Definition compare_single (ars: allregsets) (v1 v2: val) (pid: processor_id) :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 =>
      ars@(pid, CN) <- (Val.of_bool (Float32.cmp Clt f1 f2))
      @(pid, CZ) <- (Val.of_bool (Float32.cmp Ceq f1 f2))
      @(pid, CC) <- (Val.of_bool (negb (Float32.cmp Clt f1 f2)))
      @(pid, CV) <- (Val.of_bool (negb (Float32.ordered f1 f2)))
  | _, _ =>
      ars@(pid, CN) <- Vundef
      @(pid, CZ) <- Vundef
      @(pid, CC) <- Vundef
      @(pid, CV) <- Vundef
  end.

Definition eval_memsim_instr (f: function) (i: instruction) (ars: allregsets) (m: mem) : outcome :=
    match i with
    (** Branches *)
    | Pb lbl pid =>
        goto_label f lbl ars pid m
    | Pbc cond lbl pid =>
        match eval_testcond cond ars pid with
        | Some true => goto_label f lbl ars pid m
        | Some false => MemSimNext ars m
        | None => MemSimStuck
        end
    | Pbl id sg pid =>
        MemSimNext (ars@ (pid, RA)  <- (Val.offset_ptr ars@ (pid, PC)  Ptrofs.one) @ (pid, PC) <- (Genv.symbol_address ge id Ptrofs.zero)) m
    | Pbs id sg pid =>
        MemSimNext (ars@ (pid , PC)  <- (Genv.symbol_address ge id Ptrofs.zero)) m
    | Pblr r sg pid =>
        MemSimNext (ars@ (pid , RA)  <- (Val.offset_ptr ars@ (pid , PC)  Ptrofs.one) @ (pid, PC) <- (ars@ (pid , r)) ) m
    | Pbr r sg pid =>
        MemSimNext (ars@ (pid , PC)  <- (ars@ (pid , r)) ) m
    | Pret r pid =>
        MemSimNext (ars@ (pid , PC)  <- (ars@ (pid , r)) ) m
    | Pcbnz sz r lbl pid =>
        match eval_testzero sz ars@ (pid , r ) m with
        | Some true => MemSimNext ars m
        | Some false => goto_label f lbl ars pid m
        | None => MemSimStuck
        end
    | Pcbz sz r lbl pid =>
        match eval_testzero sz ars@ (pid , r ) m with
        | Some true => goto_label f lbl ars pid m
        | Some false => MemSimNext ars m
        | None => MemSimStuck
        end
    | Ptbnz sz r n lbl pid =>
        match eval_testbit sz ars@ (pid , r ) n with
        | Some true => goto_label f lbl ars pid m
        | Some false => MemSimNext ars m
        | None => MemSimStuck
        end
    | Ptbz sz r n lbl pid =>
        match eval_testbit sz ars@ (pid , r ) n with
        | Some true => MemSimNext ars m
        | Some false => goto_label f lbl ars pid m
        | None => MemSimStuck
        end
    (** Memory loads and stores *)
    | Pldrw rd a pid =>
        exec_load Mint32 (fun v => v) a rd ars pid m
    | Pldrw_a rd a pid =>
        exec_load Many32 (fun v => v) a rd ars pid m
    | Pldrx rd a pid =>
        exec_load Mint64 (fun v => v) a rd ars pid m
    | Pldrx_a rd a pid =>
        exec_load Many64 (fun v => v) a rd ars pid m
    | Pldrb W rd a pid =>
        exec_load Mint8unsigned (fun v => v) a rd ars pid m
    | Pldrb X rd a pid =>
        exec_load Mint8unsigned Val.longofintu a rd ars pid m
    | Pldrsb W rd a pid =>
        exec_load Mint8signed (fun v => v) a rd ars pid m
    | Pldrsb X rd a pid =>
        exec_load Mint8signed Val.longofint a rd ars pid m
    | Pldrh W rd a pid =>
        exec_load Mint16unsigned (fun v => v) a rd ars pid m
    | Pldrh X rd a pid =>
        exec_load Mint16unsigned Val.longofintu a rd ars pid m
    | Pldrsh W rd a pid =>
        exec_load Mint16signed (fun v => v) a rd ars pid m
    | Pldrsh X rd a pid =>
        exec_load Mint16signed Val.longofint a rd ars pid m
    | Pldrzw rd a pid =>
        exec_load Mint32 Val.longofintu a rd ars pid m
    | Pldrsw rd a pid =>
        exec_load Mint32 Val.longofint a rd ars pid m
    | Pstrw r a pid =>
        exec_store Mint32 a ars@(pid, r) ars pid m
    | Pstrw_a r a pid =>
        exec_store Many32 a  ars@(pid, r) ars pid m
    | Pstrx r a pid =>
        exec_store Mint64 a  ars@(pid, r) ars pid m
    | Pstrx_a r a pid =>
        exec_store Many64 a  ars@(pid, r) ars pid m
    | Pstrb r a pid =>
        exec_store Mint8unsigned a ars@(pid, r) ars pid m
    | Pstrh r a pid =>
        exec_store Mint16unsigned a ars@(pid, r) ars pid m
    (** Integer arithmetic, immediate *)
    | Paddimm W rd r1 n pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.add ars@ (pid, r1)  (Vint (Int.repr n))))) m
    | Paddimm X rd r1 n pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.addl ars@ (pid, r1)  (Vlong (Int64.repr n))))) m
    | Psubimm W rd r1 n pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.sub ars@ (pid, r1)  (Vint (Int.repr n))))) m
    | Psubimm X rd r1 n pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.subl ars@ (pid, r1)  (Vlong (Int64.repr n))))) m
    | Pcmpimm W r1 n pid =>
        MemSimNext ((compare_int ars ars@(pid, r1)  (Vint (Int.repr n)) m) pid ) m
    | Pcmpimm X r1 n pid =>
        MemSimNext ((compare_long ars ars@ (pid, r1)  (Vlong (Int64.repr n)) m) pid ) m
    | Pcmnimm W r1 n pid =>
        MemSimNext ((compare_int ars ars@ (pid, r1)  (Vint (Int.neg (Int.repr n))) m) pid) m
    | Pcmnimm X r1 n pid =>
        MemSimNext ((compare_long ars ars@ (pid, r1)  (Vlong (Int64.neg (Int64.repr n))) m) pid) m
    (** Move integer register *)
    | Pmov rd r1 pid =>
        MemSimNext ( (ars@ (pid, rd)  <- (ars@ (pid, r1) ))) m
    (** Logical, immediate *)
    | Pandimm W rd r1 n pid =>
        MemSimNext ((ars@(pid, rd)  <- (Val.and (ars@@ pid @@> r1) (Vint (Int.repr n))))) m
    | Pandimm X rd r1 n pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.andl (ars@@@ pid @@@> r1) (Vlong (Int64.repr n))))) m
    | Peorimm W rd r1 n pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.xor (ars@@ pid @@> r1)  (Vint (Int.repr n))))) m
    | Peorimm X rd r1 n pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.xorl (ars@@@ pid @@@> r1) (Vlong (Int64.repr n))))) m
    | Porrimm W rd r1 n pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.or (ars@@ pid @@> r1) (Vint (Int.repr n))))) m
    | Porrimm X rd r1 n pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.orl (ars@@ pid @@> r1) (Vlong (Int64.repr n))))) m
    | Ptstimm W r1 n pid =>
        MemSimNext (compare_int ars (Val.and ars@ (pid, r1)  (Vint (Int.repr n))) (Vint Int.zero) m pid) m
    | Ptstimm X r1 n pid =>
        MemSimNext ((compare_long ars (Val.andl ars@ (pid, r1)  (Vlong (Int64.repr n))) (Vlong Int64.zero) m pid)) m
    (** Move wide immediate *)
    | Pmovz W rd n pos pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Vint (Int.repr (Z.shiftl n pos))))) m
    | Pmovz X rd n pos pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Vlong (Int64.repr (Z.shiftl n pos))))) m
    | Pmovn W rd n pos pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Vint (Int.repr (Z.lnot (Z.shiftl n pos)))))) m
    | Pmovn X rd n pos pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Vlong (Int64.repr (Z.lnot (Z.shiftl n pos)))))) m
    | Pmovk W rd n pos pid =>
        MemSimNext ((ars@ (pid, rd)  <- (insert_in_int ars@ (pid, rd)  n pos 16))) m
    | Pmovk X rd n pos pid =>
        MemSimNext ((ars@ (pid, rd)  <- (insert_in_long ars@ (pid, rd)  n pos 16))) m
    (** PC-relative addressing *)
    | Padrp rd id ofs pid =>
        MemSimNext ((ars@ (pid, rd)  <- (symbol_high ge id ofs))) m
    | Paddadr rd r1 id ofs pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.addl ars@ (pid, r1)  (symbol_low ge id ofs)))) m
    (** Bit-field operations *)
    | Psbfiz W rd r1 r s pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.shl (Val.sign_ext s ars@ (pid, r1) ) (Vint r)))) m
    | Psbfiz X rd r1 r s pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.shll (Val.sign_ext_l s ars@ (pid, r1) ) (Vint r)))) m
    | Psbfx W rd r1 r s pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.sign_ext s (Val.shr ars@ (pid, r1)  (Vint r))))) m
    | Psbfx X rd r1 r s pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.sign_ext_l s (Val.shrl ars@ (pid, r1)  (Vint r))))) m
    | Pubfiz W rd r1 r s pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.shl (Val.zero_ext s ars@ (pid, r1) ) (Vint r)))) m
    | Pubfiz X rd r1 r s pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.shll (Val.zero_ext_l s ars@ (pid, r1) ) (Vint r)))) m
    | Pubfx W rd r1 r s pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.zero_ext s (Val.shru ars@ (pid, r1)  (Vint r))))) m
    | Pubfx X rd r1 r s pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.zero_ext_l s (Val.shrlu ars@ (pid, r1)  (Vint r))))) m
    (** Integer arithmetic, shifted register *)
    | Padd W rd r1 r2 s pid =>
        MemSimNext (ars@ (pid, rd)  <- (Val.add ars@@ pid @@> r1 (eval_shift_op_int ars@ (pid, r2)  s))) m
    | Padd X rd r1 r2 s pid =>
        MemSimNext (ars@ (pid, rd)  <- (Val.addl ars@@@pid @@@> r1 (eval_shift_op_long ars@ (pid, r2)  s))) m
    | Psub W rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.sub ars@@pid @@> r1 (eval_shift_op_int ars@ (pid, r2)  s)))) m
    | Psub X rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.subl ars@@@ pid@@@> r1 (eval_shift_op_long ars@ (pid, r2)  s)))) m
    | Pcmp W r1 r2 s pid =>
        MemSimNext (compare_int ars (ars@@pid@@>r1) (eval_shift_op_int ars@(pid, r2)  s) m pid) m
    | Pcmp X r1 r2 s pid =>
        MemSimNext ((compare_long ars ars@@@pid@@@>r1) (eval_shift_op_long ars@ (pid, r2)  s) m pid) m
    | Pcmn W r1 r2 s pid =>
        MemSimNext (compare_int ars ars@@pid@@>r1 (Val.neg (eval_shift_op_int ars@ (pid, r2)  s)) m pid) m
    | Pcmn X r1 r2 s pid =>
        MemSimNext ((compare_long ars ars@@@pid@@@>r1 (Val.negl (eval_shift_op_long ars@ (pid, r2)  s)) m pid)) m
    (** Integer arithmetic, extending register *)
    | Paddext rd r1 r2 x pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.addl ars@ (pid, r1)  (eval_extend ars@ (pid, r2)  x)))) m
    | Psubext rd r1 r2 x pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.subl ars@ (pid, r1)  (eval_extend ars@ (pid, r2)  x)))) m
    | Pcmpext r1 r2 x pid =>
        MemSimNext ((compare_long ars ars@ (pid, r1)  (eval_extend ars@ (pid, r2)  x) m pid)) m
    | Pcmnext r1 r2 x pid =>
        MemSimNext ((compare_long ars ars@ (pid, r1)  (Val.negl (eval_extend ars@ (pid, r2)  x)) m pid)) m
    (** Logical, shifted register *)
    | Pand W rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.and ars@@pid@@>r1 (eval_shift_op_int ars@ (pid , r2)  s)))) m
    | Pand X rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.andl ars@@@pid@@@>r1 (eval_shift_op_long ars@ (pid , r2)  s)))) m
    | Pbic W rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.and ars@@pid@@>r1 (Val.notint (eval_shift_op_int ars@ (pid , r2)  s))))) m
    | Pbic X rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.andl ars@@@pid@@@>r1 (Val.notl (eval_shift_op_long ars@ (pid , r2)  s))))) m
    | Peon W rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.xor ars@@pid@@>r1 (Val.notint (eval_shift_op_int ars@ (pid , r2)  s))))) m
    | Peon X rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.xorl ars@@@pid@@@>r1 (Val.notl (eval_shift_op_long ars@ (pid , r2)  s))))) m
    | Peor W rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.xor ars@@pid@@>r1 (eval_shift_op_int ars@ (pid , r2)  s)))) m
    | Peor X rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.xorl ars@@@pid@@@>r1 (eval_shift_op_long ars@ (pid , r2)  s)))) m
    | Porr W rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.or ars@@pid@@>r1 (eval_shift_op_int ars@ (pid , r2)  s)))) m
    | Porr X rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.orl ars@@@pid@@@>r1 (eval_shift_op_long ars@ (pid , r2)  s)))) m
    | Porn W rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.or ars@@pid@@>r1 (Val.notint (eval_shift_op_int ars@ (pid , r2)  s))))) m
    | Porn X rd r1 r2 s pid =>
        MemSimNext ((ars@ (pid , rd)  <- (Val.orl ars@@@pid@@@>r1 (Val.notl (eval_shift_op_long ars@ (pid , r2)  s))))) m
    | Ptst W r1 r2 s pid =>
        MemSimNext ((compare_int ars (Val.and ars@@pid@@>r1 (eval_shift_op_int ars@ (pid , r2)  s)) (Vint Int.zero) m pid)) m
    | Ptst X r1 r2 s pid =>
        MemSimNext ((compare_long ars (Val.andl ars@@@pid@@@>r1 (eval_shift_op_long ars@ (pid , r2)  s)) (Vlong Int64.zero) m pid)) m
    (*** Variable shifts *)
    | Pasrv W rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.shr ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Pasrv X rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.shrl ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Plslv W rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.shl ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Plslv X rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.shll ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Plsrv W rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.shru ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Plsrv X rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.shrlu ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Prorv W rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.ror ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Prorv X rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.rorl ars@ (pid, r1)  ars@ (pid, r2) ))) m
    (** Conditional data processing *)
    | Pcsel rd r1 r2 cond pid =>
        let v :=
            match eval_testcond cond ars pid with
            | Some true => ars@ (pid, r1) 
            | Some false => ars@ (pid, r2) 
            | None => Vundef
            end in
        MemSimNext ((ars@ (pid, rd)  <- v)) m
    | Pcset rd cond pid =>
        let v :=
            match eval_testcond cond ars pid with
            | Some true => Vint Int.one
            | Some false => Vint Int.zero
            | None => Vundef
            end in
        MemSimNext ((ars@ (pid, rd)  <- v)) m
    (** Integer multiply/divide *)
    | Pmadd W rd r1 r2 r3 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.add ars@@pid@@>r3 (Val.mul ars@ (pid, r1)  ars@ (pid, r2) )))) m
    | Pmadd X rd r1 r2 r3 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.addl ars@@@pid@@@>r3 (Val.mull ars@ (pid, r1)  ars@ (pid, r2) )))) m
    | Pmsub W rd r1 r2 r3 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.sub ars@@pid@@>r3 (Val.mul ars@ (pid, r1)  ars@ (pid, r2) )))) m
    | Pmsub X rd r1 r2 r3 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.subl ars@@@pid@@@>r3 (Val.mull ars@ (pid, r1)  ars@ (pid, r2) )))) m
    | Psmulh rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.mullhs ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Pumulh rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.mullhu ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Psdiv W rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.divs ars@ (pid, r1)  ars@ (pid, r2) )))) m
    | Psdiv X rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.divls ars@ (pid, r1)  ars@ (pid, r2) )))) m
    | Pudiv W rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.divu ars@ (pid, r1)  ars@ (pid, r2) )))) m
    | Pudiv X rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.divlu ars@ (pid, r1)  ars@ (pid, r2) )))) m
    (** Floating-point loads and stores *)
    | Pldrs rd a pid =>
        exec_load Mfloat32 (fun v => v) a rd ars pid m
    | Pldrd rd a pid =>
        exec_load Mfloat64 (fun v => v) a rd ars pid m
    | Pldrd_a rd a pid =>
        exec_load Many64 (fun v => v) a rd ars pid m
    | Pstrs r a pid =>
        exec_store Mfloat32 a ars@ (pid, r ) ars pid m
    | Pstrd r a pid =>
        exec_store Mfloat64 a ars@ (pid, r ) ars pid m
    | Pstrd_a r a pid =>
        exec_store Many64 a ars@ (pid, r ) ars pid m
    (** Floating-point move *)
    | Pfmov rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (ars@ (pid, r1) ))) m
    | Pfmovimms rd f pid =>
        MemSimNext ((ars@ (pid, X16) <- Vundef @(pid, rd) <- (Vsingle f))) m
    | Pfmovimmd rd f pid =>
        MemSimNext ((ars@ (pid, X16) <- Vundef @(pid, rd) <- (Vfloat f))) m
    | Pfmovi S rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (float32_of_bits ars@@pid@@>r1))) m
    | Pfmovi D rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (float64_of_bits ars@@@pid@@@>r1))) m
    (** Floating-point conversions *)
    | Pfcvtds rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.floatofsingle ars@ (pid, r1) ))) m
    | Pfcvtsd rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.singleoffloat ars@ (pid, r1) ))) m
    | Pfcvtzs W S rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.intofsingle ars@ (pid, r1) )))) m
    | Pfcvtzs W D rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.intoffloat ars@ (pid, r1) )))) m
    | Pfcvtzs X S rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.longofsingle ars@ (pid, r1) )))) m
    | Pfcvtzs X D rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.longoffloat ars@ (pid, r1) )))) m
    | Pfcvtzu W S rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.intuofsingle ars@ (pid, r1) )))) m
    | Pfcvtzu W D rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.intuoffloat ars@ (pid, r1) )))) m
    | Pfcvtzu X S rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.longuofsingle ars@ (pid, r1) )))) m
    | Pfcvtzu X D rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.longuoffloat ars@ (pid, r1) )))) m
    | Pscvtf S W rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.singleofint ars@ (pid, r1) )))) m
    | Pscvtf D W rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.floatofint ars@ (pid, r1) )))) m
    | Pscvtf S X rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.singleoflong ars@ (pid, r1) )))) m
    | Pscvtf D X rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.floatoflong ars@ (pid, r1) )))) m
    | Pucvtf S W rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.singleofintu ars@ (pid, r1) )))) m
    | Pucvtf D W rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.floatofintu ars@ (pid, r1) )))) m
    | Pucvtf S X rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.singleoflongu ars@ (pid, r1) )))) m
    | Pucvtf D X rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.floatoflongu ars@ (pid, r1) )))) m
    (** Floating-point arithmetic *)
    | Pfabs S rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.absfs ars@ (pid, r1) ))) m
    | Pfabs D rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.absf ars@ (pid, r1) ))) m
    | Pfneg S rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.negfs ars@ (pid, r1) ))) m
    | Pfneg D rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.negf ars@ (pid, r1) ))) m
    | Pfadd S rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.addfs ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Pfadd D rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.addf ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Pfdiv S rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.divfs ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Pfdiv D rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.divf ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Pfmul S rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.mulfs ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Pfmul D rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.mulf ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Pfnmul S rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.negfs (Val.mulfs ars@ (pid, r1)  ars@ (pid, r2) )))) m
    | Pfnmul D rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.negf (Val.mulf ars@ (pid, r1)  ars@ (pid, r2) )))) m
    | Pfsub S rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.subfs ars@ (pid, r1)  ars@ (pid, r2) ))) m
    | Pfsub D rd r1 r2 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.subf ars@ (pid, r1)  ars@ (pid, r2) ))) m
    (** Floating-point comparison *)
    | Pfcmp S r1 r2 pid =>
        MemSimNext ((compare_single ars ars@ (pid, r1)  ars@ (pid, r2) pid )) m
    | Pfcmp D r1 r2 pid =>
        MemSimNext ((compare_float ars ars@ (pid, r1)  ars@ (pid, r2) pid )) m
    | Pfcmp0 S r1 pid =>
        MemSimNext ((compare_single ars ars@ (pid, r1)  (Vsingle Float32.zero) pid)) m
    | Pfcmp0 D r1 pid =>
        MemSimNext ((compare_float ars ars@ (pid, r1)  (Vfloat Float.zero) pid)) m
    (** Floating-point conditional select *)
    | Pfsel rd r1 r2 cond pid =>
        let v :=
            match eval_testcond cond ars pid with
            | Some true => ars@ (pid, r1) 
            | Some false => ars@ (pid, r2) 
            | None => Vundef
            end in
        MemSimNext ((ars@ (pid, rd)  <- v)) m
    (** Pseudo-instructions *)
    | Pallocframe sz pos pid =>
        let (m1, stk) := Mem.alloc m 0 sz in
        let sp := (Vptr stk Ptrofs.zero) in
        match Mem.storev Mint64 m1 (Val.offset_ptr sp pos) ars@ (pid, SP)  with
        | None => MemSimStuck
        | Some m2 => MemSimNext ((ars @ (pid, X15) <- (ars@ (pid, SP) ) @(pid, SP) <- sp @(pid, X16) <- Vundef)) m2
        end
    | Pfreeframe sz pos pid =>
        match Mem.loadv Mint64 m (Val.offset_ptr ars@ (pid, SP)  pos) with
        | None => MemSimStuck
        | Some v =>
            match ars@ (pid, SP)  with
            | Vptr stk ofs =>
                match Mem.free m stk 0 sz with
                | None => MemSimStuck
                | Some m' => MemSimNext ((ars@ (pid, SP)  <- v @(pid, X16) <- Vundef)) m'
                end
            | _ => MemSimStuck
            end
        end
    | Plabel lbl pid =>
        MemSimNext ars m
    | Ploadsymbol rd id pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Genv.symbol_address ge id Ptrofs.zero))) m
    | Pcvtsw2x rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.longofint ars@ (pid, r1) ))) m
    | Pcvtuw2x rd r1 pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.longofintu ars@ (pid, r1) ))) m
    | Pcvtx2w rd pid =>
        MemSimNext ((ars@ (pid, rd)  <- (Val.loword ars@ (pid, rd) ))) m
    | Pbtbl r tbl pid =>
        match (ars@ (pid, X16)  <- Vundef)@(pid, r) with
        | Vint n =>
            match list_nth_z tbl (Int.unsigned n) with
            | None => MemSimStuck
            | Some lbl => goto_label f lbl (ars@ (pid, X16) <- Vundef) pid m
            end
        | _ => MemSimStuck
        end
    | Pcfi_rel_offset _ pid =>
        MemSimNext ars m
    | Pbuiltin ef args res pid => MemSimStuck    (**r treated specially below *)
    (** The following instructions and directives are not generated directly
        by Asmgen, so we do not model them. *)
    | Pldp _ _ _ _ => MemSimStuck
    | Pstp _ _ _ _  => MemSimStuck
    | Pcls _ _ _ _ => MemSimStuck
    | Pclz _ _ _ _ => MemSimStuck
    | Prev _ _ _ _ => MemSimStuck
    | Prev16 _ _ _ _ => MemSimStuck
    | Prbit _ _ _ _ => MemSimStuck
    | Pfsqrt _ _ _ _ => MemSimStuck
    | Pfmadd _ _ _ _ _ _ => MemSimStuck
    | Pfmsub _ _ _ _ _ _ => MemSimStuck
    | Pfnmadd _ _ _ _ _ _ => MemSimStuck
    | Pfnmsub _ _ _ _ _ _ => MemSimStuck
    | Pfmax _ _ _ _ _ => MemSimStuck
    | Pfmin _ _ _ _ _ => MemSimStuck
    | Pnop _ => MemSimStuck
    | Pincpc pid => MemSimNext (ars@(pid, PC) <- (Val.offset_ptr ars@(pid,PC) Ptrofs.one)) m
    | Pcfi_adjust _ _ =>
        MemSimStuck
    end.


(** Execution of the instruction at [rs@PC]. *)

End RELSEM.






(** asm to mem sim - turns ISA into a series of memsim semantics*)
(** separates most operations into the actual operation and incrementing the PC - this lets us reorder more easily since we 
dont update the PC in every operation*)

(** translates loads/stores into memory dispatches and acknowledgements*)
(** Takes in a processor id*)
Definition asm_to_memsim (asm_i: Asm.instruction) (pid: processor_id): list instruction := 
    match asm_i with 
    | Asm.Pb lbl    => [Pb lbl pid]                                               (**r branch *)
    | Asm.Pbc c lbl  => [Pbc c lbl pid; Pincpc pid]                             (**r conditional branch *)
    | Asm.Pbl id sg  => [Pbl id sg pid]                              (**r jump to function and link *)
    | Asm.Pbs id sg => [Pbs id sg pid]                                  (**r jump to function *)
    | Asm.Pblr r sg => [Pblr r sg pid]                                 (**r indirect jump and link *)
    | Asm.Pbr r sg => [Pbr r sg pid]                                   (**r indirect jump *)
    | Asm.Pret r => [Pret r pid]                                        (**r return *)
    | Asm.Pcbnz sz r lbl => [Pcbnz sz r lbl pid; Pincpc pid]                       (**r branch if not zero *)
    | Asm.Pcbz sz r lbl => [Pcbz sz r lbl pid; Pincpc pid]                         (**r branch if zero *)
    | Asm.Ptbnz sz r n lbl => [Ptbnz sz r n lbl pid; Pincpc pid]                   (**r branch if bit n is not zero *)
    | Asm.Ptbz sz r n lbl => [Ptbz sz r n lbl pid; Pincpc pid]                     (**r branch if bit n is zero *)
    | Asm.Pldrw rd a => [Pldrw rd a pid; Pincpc pid]                               (**r load int32 *)
    | Asm.Pldrw_a rd a => [Pldrw_a rd a pid; Pincpc pid]                           (**r load int32 as any32 *)
    | Asm.Pldrx rd a => [Pldrx rd a pid; Pincpc pid]                               (**r load int64 *)
    | Asm.Pldrx_a rd a => [Pldrx_a rd a pid; Pincpc pid]                           (**r load int64 as any64 *)
    | Asm.Pldrb sz rd a => [Pldrb sz rd a pid; Pincpc pid]                         (**r load int8, zero-extend *)
    | Asm.Pldrsb sz rd a => [Pldrsb sz rd a pid; Pincpc pid]                       (**r load int8, sign-extend *)
    | Asm.Pldrh sz rd a => [Pldrh sz rd a pid; Pincpc pid]                         (**r load int16, zero-extend *)
    | Asm.Pldrsh sz rd a => [Pldrsh sz rd a pid; Pincpc pid]                       (**r load int16, sign-extend *)
    | Asm.Pldrzw rd a => [Pldrzw rd a pid; Pincpc pid]                             (**r load int32, zero-extend to int64 *)
    | Asm.Pldrsw rd a => [Pldrsw rd a pid; Pincpc pid]                             (**r load int32, sign-extend to int64 *)
    | Asm.Pldp rd1 rd2 a => [Pldp rd1 rd2 a pid; Pincpc pid]                       (**r load two int64 *)
    | Asm.Pstrw rs a => [Pstrw rs a pid; Pincpc pid]                               (**r store int32 *)
    | Asm.Pstrw_a rs a => [Pstrw_a rs a pid; Pincpc pid]                           (**r store int32 as any32 *)
    | Asm.Pstrx rs a => [Pstrx rs a pid; Pincpc pid]                               (**r store int64 *)
    | Asm.Pstrx_a rs a => [Pstrx_a rs a pid; Pincpc pid]                           (**r store int64 as any64 *)
    | Asm.Pstrb rs a => [Pstrb rs a pid; Pincpc pid]                               (**r store int8 *)
    | Asm.Pstrh rs a => [Pstrh rs a pid; Pincpc pid]                               (**r store int16 *)
    | Asm.Pstp rs1 rs2 a => [Pstp rs1 rs2 a pid; Pincpc pid]                       (**r store two int64 *)
    | Asm.Paddimm sz rd r1 n => [Paddimm sz rd r1 n pid; Pincpc pid]               (**r addition *)
    | Asm.Psubimm sz rd r1 n => [Psubimm sz rd r1 n pid; Pincpc pid]               (**r subtraction *)
    | Asm.Pcmpimm sz r1 n => [Pcmpimm sz r1 n pid; Pincpc pid]                     (**r compare *)
    | Asm.Pcmnimm sz r1 n => [Pcmnimm sz r1 n pid; Pincpc pid]                     (**r compare negative *)
    | Asm.Pmov rd r1 => [Pmov rd r1 pid; Pincpc pid]                               (**r move integer register *)
    | Asm.Pandimm sz rd r1 n => [Pandimm sz rd r1 n pid; Pincpc pid]               (**r and *)
    | Asm.Peorimm sz rd r1 n => [Peorimm sz rd r1 n pid; Pincpc pid]               (**r xor *)
    | Asm.Porrimm sz rd r1 n => [Porrimm sz rd r1 n pid; Pincpc pid]               (**r or *)
    | Asm.Ptstimm sz r1 n => [Ptstimm sz r1 n pid; Pincpc pid]                     (**r and, then set flags *)
    | Asm.Pmovz sz rd n pos => [Pmovz sz rd n pos pid; Pincpc pid]                 (**r move wide immediate *)
    | Asm.Pmovn sz rd n pos => [Pmovn sz rd n pos pid; Pincpc pid]
    | Asm.Pmovk sz rd n pos => [Pmovk sz rd n pos pid; Pincpc pid]
    | Asm.Padrp rd id ofs => [Padrp rd id ofs pid; Pincpc pid]                     (**r PC-relative addressing *)
    | Asm.Paddadr rd r1 id ofs => [Paddadr rd r1 id ofs pid; Pincpc pid]
    | Asm.Psbfiz sz rd r1 r s => [Psbfiz sz rd r1 r s pid; Pincpc pid]              (**r Bit-field operations *)
    | Asm.Psbfx sz rd r1 r s => [Psbfx sz rd r1 r s pid; Pincpc pid]
    | Asm.Pubfiz sz rd r1 r s => [Pubfiz sz rd r1 r s pid; Pincpc pid]
    | Asm.Pubfx sz rd r1 r s => [Pubfx sz rd r1 r s pid; Pincpc pid]
    | Asm.Padd sz rd r1 r2 s => [Padd sz rd r1 r2 s pid; Pincpc pid]                (**r Integer arithmetic, shifted register *)
    | Asm.Psub sz rd r1 r2 s => [Psub sz rd r1 r2 s pid; Pincpc pid]
    | Asm.Pcmp sz r1 r2 s => [Pcmp sz r1 r2 s pid; Pincpc pid]
    | Asm.Pcmn sz r1 r2 s => [Pcmn sz r1 r2 s pid; Pincpc pid]
    | Asm.Paddext rd r1 r2 x => [Paddext rd r1 r2 x pid; Pincpc pid]                (**r Integer arithmetic, extending register *)
    | Asm.Psubext rd r1 r2 x => [Psubext rd r1 r2 x pid; Pincpc pid]
    | Asm.Pcmpext r1 r2 x => [Pcmpext r1 r2 x pid; Pincpc pid]
    | Asm.Pcmnext r1 r2 x => [Pcmnext r1 r2 x pid; Pincpc pid]
    | Asm.Pand sz rd r1 r2 s => [Pand sz rd r1 r2 s pid; Pincpc pid]                (**r Logical, shifted register *)
    | Asm.Pbic sz rd r1 r2 s => [Pbic sz rd r1 r2 s pid; Pincpc pid]
    | Asm.Peon sz rd r1 r2 s => [Peon sz rd r1 r2 s pid; Pincpc pid]
    | Asm.Peor sz rd r1 r2 s => [Peor sz rd r1 r2 s pid; Pincpc pid]
    | Asm.Porr sz rd r1 r2 s => [Porr sz rd r1 r2 s pid; Pincpc pid]
    | Asm.Porn sz rd r1 r2 s => [Porn sz rd r1 r2 s pid; Pincpc pid]
    | Asm.Ptst sz r1 r2 s => [Ptst sz r1 r2 s pid; Pincpc pid]                      (**r and, then set flags *)
    | Asm.Pasrv sz rd r1 r2 => [Pasrv sz rd r1 r2 pid; Pincpc pid]                  (**r Variable shifts *)
    | Asm.Plslv sz rd r1 r2 => [Plslv sz rd r1 r2 pid; Pincpc pid]
    | Asm.Plsrv sz rd r1 r2 => [Plsrv sz rd r1 r2 pid; Pincpc pid]
    | Asm.Prorv sz rd r1 r2 => [Prorv sz rd r1 r2 pid; Pincpc pid]
    | Asm.Pcls sz rd r1 => [Pcls sz rd r1 pid; Pincpc pid]                          (**r Bit operations *)
    | Asm.Pclz sz rd r1 => [Pclz sz rd r1 pid; Pincpc pid]
    | Asm.Prev sz rd r1 => [Prev sz rd r1 pid; Pincpc pid]
    | Asm.Prev16 sz rd r1 => [Prev16 sz rd r1 pid; Pincpc pid]
    | Asm.Prbit sz rd r1 => [Prbit sz rd r1 pid; Pincpc pid]
    | Asm.Pcsel rd r1 r2 c => [Pcsel rd r1 r2 c pid; Pincpc pid]                    (**r Conditional data processing *)
    | Asm.Pcset rd c => [Pcset rd c pid; Pincpc pid]
    | Asm.Pmadd sz rd r1 r2 r3 => [Pmadd sz rd r1 r2 r3 pid; Pincpc pid]            (**r Integer multiply/divide *)
    | Asm.Pmsub sz rd r1 r2 r3 => [Pmsub sz rd r1 r2 r3 pid; Pincpc pid]
    | Asm.Psmulh rd r1 r2 => [Psmulh rd r1 r2 pid; Pincpc pid]
    | Asm.Pumulh rd r1 r2 => [Pumulh rd r1 r2 pid; Pincpc pid]
    | Asm.Psdiv sz rd r1 r2 => [Psdiv sz rd r1 r2 pid; Pincpc pid]
    | Asm.Pudiv sz rd r1 r2 => [Pudiv sz rd r1 r2 pid; Pincpc pid]
    | Asm.Pldrs rd a => [Pldrs rd a pid; Pincpc pid]                                (**r Floating-point loads and stores *)
    | Asm.Pldrd rd a => [Pldrd rd a pid; Pincpc pid]
    | Asm.Pldrd_a rd a => [Pldrd_a rd a pid; Pincpc pid]
    | Asm.Pstrs rs a => [Pstrs rs a pid; Pincpc pid]
    | Asm.Pstrd rs a => [Pstrd rs a pid; Pincpc pid]
    | Asm.Pstrd_a rs a => [Pstrd_a rs a pid; Pincpc pid]
    | Asm.Pfmov rd r1 => [Pfmov rd r1 pid; Pincpc pid]                              (**r Floating-point move *)
    | Asm.Pfmovimms rd f => [Pfmovimms rd f pid; Pincpc pid]
    | Asm.Pfmovimmd rd f => [Pfmovimmd rd f pid; Pincpc pid]
    | Asm.Pfmovi fsz rd r1 => [Pfmovi fsz rd r1 pid; Pincpc pid]
    | Asm.Pfcvtds rd r1 => [Pfcvtds rd r1 pid; Pincpc pid]                          (**r Floating-point conversions *)
    | Asm.Pfcvtsd rd r1 => [Pfcvtsd rd r1 pid; Pincpc pid]
    | Asm.Pfcvtzs isz fsz rd r1 => [Pfcvtzs isz fsz rd r1 pid; Pincpc pid]
    | Asm.Pfcvtzu isz fsz rd r1 => [Pfcvtzu isz fsz rd r1 pid; Pincpc pid]
    | Asm.Pscvtf fsz isz rd r1 => [Pscvtf fsz isz rd r1 pid; Pincpc pid]
    | Asm.Pucvtf fsz isz rd r1 => [Pucvtf fsz isz rd r1 pid; Pincpc pid]
    | Asm.Pfabs sz rd r1 => [Pfabs sz rd r1 pid; Pincpc pid]                        (**r Floating-point arithmetic *)
    | Asm.Pfneg sz rd r1 => [Pfneg sz rd r1 pid; Pincpc pid]
    | Asm.Pfsqrt sz rd r1 => [Pfsqrt sz rd r1 pid; Pincpc pid]
    | Asm.Pfadd sz rd r1 r2 => [Pfadd sz rd r1 r2 pid; Pincpc pid]
    | Asm.Pfdiv sz rd r1 r2 => [Pfdiv sz rd r1 r2 pid; Pincpc pid]
    | Asm.Pfmul sz rd r1 r2 => [Pfmul sz rd r1 r2 pid; Pincpc pid]
    | Asm.Pfnmul sz rd r1 r2 => [Pfnmul sz rd r1 r2 pid; Pincpc pid]
    | Asm.Pfsub sz rd r1 r2 => [Pfsub sz rd r1 r2 pid; Pincpc pid]
    | Asm.Pfmadd sz rd r1 r2 r3 => [Pfmadd sz rd r1 r2 r3 pid; Pincpc pid]
    | Asm.Pfmsub sz rd r1 r2 r3 => [Pfmsub sz rd r1 r2 r3 pid; Pincpc pid]
    | Asm.Pfnmadd sz rd r1 r2 r3 => [Pfnmadd sz rd r1 r2 r3 pid; Pincpc pid]
    | Asm.Pfnmsub sz rd r1 r2 r3 => [Pfnmsub sz rd r1 r2 r3 pid; Pincpc pid]
    | Asm.Pfmax sz rd r1 r2 => [Pfmax sz rd r1 r2 pid; Pincpc pid]
    | Asm.Pfmin sz rd r1 r2 => [Pfmin sz rd r1 r2 pid; Pincpc pid]
    | Asm.Pfcmp sz r1 r2 => [Pfcmp sz r1 r2 pid; Pincpc pid]                        (**r Floating-point comparison *)
    | Asm.Pfcmp0 sz r1 => [Pfcmp0 sz r1 pid; Pincpc pid]
    | Asm.Pfsel rd r1 r2 cond => [Pfsel rd r1 r2 cond pid; Pincpc pid]              (**r Floating-point conditional select *)
    | Asm.Pallocframe sz linkofs => [Pallocframe sz linkofs pid; Pincpc pid]       (**r Pseudo-instructions *)
    | Asm.Pfreeframe sz linkofs => [Pfreeframe sz linkofs pid; Pincpc pid]
    | Asm.Plabel lbl => [Plabel lbl pid; Pincpc pid]
    | Asm.Ploadsymbol rd id => [Ploadsymbol rd id pid; Pincpc pid]
    | Asm.Pcvtsw2x rd r1 => [Pcvtsw2x rd r1 pid; Pincpc pid]
    | Asm.Pcvtuw2x rd r1 => [Pcvtuw2x rd r1 pid; Pincpc pid]
    | Asm.Pcvtx2w rd => [Pcvtx2w rd pid; Pincpc pid]
    | Asm.Pbtbl r1 tbl => [Pbtbl r1 tbl pid; Pincpc pid]
    | Asm.Pbuiltin ef args res => [Pbuiltin ef args res pid; Pincpc pid]
    | Asm.Pnop => [Pnop pid; Pincpc pid]                                              (**r no operation *)
    | Asm.Pcfi_adjust ofs => [Pcfi_adjust ofs pid; Pincpc pid]
    | Asm.Pcfi_rel_offset ofs => [Pcfi_rel_offset ofs pid; Pincpc pid]                                
end.

(** What to do if a goto forces early abort of a list? have the individual eval_memsim_instr return a state for early abort*)
Fixpoint eval_memsim_chain (g: genv)(f: function)(instrs: list instruction)  (ars: allregsets)  (m: mem): outcome := 
    match instrs with
    | nil => MemSimNext ars m
    | instr :: chain' =>
        match eval_memsim_instr g f instr ars m with
        | MemSimNext ars' m' => eval_memsim_chain g f chain' ars' m'
        | MemSimJumpOut ars' m' => MemSimJumpOut ars' m'
        | MemSimStuck => MemSimStuck
        end
    end.

(** Proof boilerplate: move to another file asap*)

(** ** Simplify matches when possible *)

Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
  let repl_match_hyp H d d' :=
      replace d with d' in H;
      lazymatch type of H with
      | context[match d' with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  end.


(** ** Find and destruct matches *)

Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
    destruct_matches_in d
  | _ => destruct e eqn:?; intros
  end.

Ltac destruct_all_matches :=
  repeat (try simpl_match;
          try match goal with
              | [ |- context[match ?d with | _ => _ end] ] =>
                destruct_matches_in d
              | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
              end);
  subst;
  try congruence;
  auto.

Ltac destruct_nongoal_matches :=
  repeat (try simpl_match;
           try match goal with
           | [ H: context[match ?d with | _ => _ end] |- _ ] =>
             destruct_matches_in d
               end);
  subst;
  try congruence;
  auto.

Ltac destruct_goal_matches :=
  repeat (try simpl_match;
           match goal with
           | [ |- context[match ?d with | _ => _ end] ] =>
              destruct_matches_in d
           end);
  try congruence;
  auto.

Ltac destruct_tuple :=
  match goal with
  | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
    let a := fresh a in
    let b := fresh b in
    destruct p as [a b]
  | [ |- context[let '(a, b) := ?p in _] ] =>
    let a := fresh a in
    let b := fresh b in
    destruct p as [a b]
  end.

Tactic Notation "destruct" "matches" "in" "*" := destruct_all_matches.
Tactic Notation "destruct" "matches" "in" "*|-" := destruct_nongoal_matches.
Tactic Notation "destruct" "matches" := destruct_goal_matches.


Definition regs_identical (ars: allregsets) (pid: processor_id) (rs: regset): Prop :=
    forall r, rs r = ars@(pid, r).

Remark vptr_equality: forall b1 b2 o1 o2, b1=b2 /\ o1 = o2 -> Vptr b1 o1 = Vptr b2 o2.
Proof. intros. destruct H. rewrite H. rewrite H0. reflexivity. Qed.

Remark inverse_vptr_equality: forall b1 b2 o1 o2,  Vptr b1 o1 = Vptr b2 o2 -> b1=b2 /\ o1 = o2.
Proof. intros. inversion H. split; reflexivity. Qed.


Remark tup_equal: forall (a c: processor_id) (b d: preg), a = c /\ b = d -> (a, b) = (c, d).
Proof. intros. destruct H. rewrite H. rewrite H0. reflexivity. Qed.

Remark preg_neq: forall (a b: preg), a <> b -> a = b -> False.
Proof.
    intros. rewrite H0 in H. apply H. reflexivity.
Qed.

Remark set_method_semantic_equality: forall rs (pid: processor_id) (r1 r2: preg) (v: val)  ars, 
    regs_identical ars pid rs ->  regs_identical ars@(pid, r1)<-v pid rs#r1<-v.
    Proof. 
    intros. unfold regs_identical in H. unfold regs_identical. intro.
    
    unfold Asm.Pregmap.set. unfold PRmap.set. 
    destruct (PregEq.eq r r1).
    - subst. destruct (PREq.eq (pid, r1)(pid, r1)). reflexivity. contradiction.
    - destruct (PREq.eq (pid, r) (pid, r1)). inversion e. contradiction. apply H.
Qed.

Remark set_method_sem_eq_form2: forall (pid: processor_id)(pr k: preg)(rs: regset)(ars: allregsets)(v: val),
 regs_identical ars pid rs -> rs # k <- v pr = ars @ (pid, k) <- v (pid, pr).
 Proof.
    intros. unfold regs_identical in H. unfold Asm.Pregmap.set. unfold PRmap.set. destruct (PregEq.eq k pr).
    - subst. destruct (PREq.eq (pid, pr) (pid, pr)). destruct (PregEq.eq pr pr). reflexivity. contradiction.
    unfold not in n. contradiction.
    -destruct (PregEq.eq pr k). rewrite <- e in n. contradiction. destruct (PREq.eq (pid, pr) (pid, k)).
    inversion e. contradiction. apply H.
 Qed.

 Remark set_method_sem_eq_form3: forall (pid: processor_id)(pr k: preg)(rs: regset)(ars: allregsets)(v1 v2: val),
 regs_identical ars pid rs -> v1 = v2 -> rs # k <- v1 pr = ars @ (pid, k) <- v2 (pid, pr).
 Proof.
    intros. unfold regs_identical in H. unfold Asm.Pregmap.set. rewrite <- H0. unfold PRmap.set. destruct (PregEq.eq k pr).
    - subst. destruct (PREq.eq (pid, pr) (pid, pr)). destruct (PregEq.eq pr pr). reflexivity. contradiction.
    unfold not in n. contradiction.
    -destruct (PregEq.eq pr k). rewrite <- e in n. contradiction. destruct (PREq.eq (pid, pr) (pid, k)).
    inversion e. contradiction. apply H.
 Qed.



(** Definition of the end state of an asm instruction in terms of the memsim outcome*)

Definition end_state_equals_asm_memsim (r: preg)(asm_o: Asm.outcome) (memsim_o: outcome) (pid: processor_id): Prop :=
    match asm_o, memsim_o with
    | Next rs m1, MemSimNext ars m2 => rs r = (ars @ (pid, r)) /\ m1 = m2
    | Next rs m1, MemSimJumpOut ars m2 => rs r = (ars @ (pid, r)) /\ m1 = m2
    | Stuck, MemSimStuck => True
    | _, _ => False
    end.

(* Ltac sem_eq_solver :=
    match goal with
    | [ H : regs_identical ?ars ?pid ?rs
        |- Pregmap.set ?write_reg _ ?rs ?read_reg = PRmap.set (?pid, ?write_reg) _ ?ars (?pid, ?read_reg)
    ] => apply set_method_sem_eq_form3; [ apply H | unfold regs_identical in H; specialize (H write_reg) as H_store_eq; sem_eq_solver]
    | [H1 : ?rs ?reg = Vptr ?b1 ?i1, H2: ?ars (?pid, ?reg) = Vptr ?b2 ?i2, H_store_eq: ?rs ?reg = ?ars (?pid, ?reg) 
        |- Vptr ?b1 ?z = Vptr ?b2 ?z] => rewrite -> H_store_eq in H1; rewrite -> H2 in H1; inversion H1; reflexivity
    | [H_store_eq: ?rs ?reg = ?ars (?pid, ?reg) 
        |- ?a (?rs ?reg) ?c = ?a (?ars (?pid, ?reg)) ?c] => rewrite -> H_store_eq; reflexivity
    end. *)

Remark cancel_dual_ptr_increments: forall (rs: regset) (ars: allregsets) (pid: processor_id) (v: ptrofs)(r: preg),
   rs # r = ars @ (pid, r) -> Val.offset_ptr (rs r) v = Val.offset_ptr (ars (pid, r)) v.
   Proof.
   intros. rewrite <- H. reflexivity.
   Qed.

Remark eq_implies_set_eq: forall  (rs: regset) (ars: allregsets) (pid: processor_id) (write_reg read_reg: preg) (v1 v2: val),
    rs read_reg = ars (pid, read_reg) -> v1 = v2 -> (rs # write_reg <- v1) read_reg = (ars @ (pid, write_reg) <- v2) (pid, read_reg).
    Proof. intros. rewrite <- H0. unfold Asm.Pregmap.set. unfold PRmap.set. rewrite H. destruct (PregEq.eq read_reg write_reg); destruct (PREq.eq (pid, read_reg)(pid, write_reg)).
      reflexivity. destruct n. rewrite <- e. reflexivity. destruct n. inversion e. reflexivity. reflexivity.
Qed.

Remark invert_shll: forall (rs: regset) (v1 v2: val) (r: preg) (pid: processor_id) (ars: allregsets),
    (rs r) = (ars (pid, r)) -> v1 = v2 -> Val.shll (rs r) v1 = Val.shll (ars (pid, r)) v2.
    Proof. intros. rewrite H. rewrite H0. reflexivity. Qed. 

Remark long_of_int: forall (v1 v2: val),
    v1 = v2 -> Val.longofintu v1 = Val.longofintu v2.
    Proof. intros. rewrite H. reflexivity. Qed. 

(* Ltac sem_eq_solver := 
    match goal with
    | [ |- ?x = ?x ] => reflexivity (*Terminal*)
    | [H: regs_identical ?ars ?pid ?rs |- regs_identical ?ars ?pid ?rs] => apply H (*Terminal*)
    | [Hri: forall r: PregEq.t, ?rs r = ?ars (?pid, r)    |- ?rs ?r = ?ars (?pid, ?r) ] => apply Hri (*Terminal*)
    | [H1 : ?rs ?reg = Vptr ?b1 ?i1, H2: ?ars (?pid, ?reg) = Vptr ?b2 ?i2, Hri: forall r: PregEq.t, ?rs r = ?ars (?pid, r) 
        |- Vptr ?b1 ?z = Vptr ?b2 ?z] => specialize (Hri reg); rewrite -> Hri in H1; rewrite -> H2 in H1; inversion H1; reflexivity  (*Terminal*)
    | [ |- Val.offset_ptr _ ?v = Val.offset_ptr _ ?v] => apply cancel_dual_ptr_increments; sem_eq_solver
    | [ |- regs_identical _ _ _] => unfold regs_identical; intro; sem_eq_solver
    | [ |- Pregmap.set ?r1 _ ?rs ?r2 = PRmap.set (?pid, ?r1) _ ?ars (?pid, ?r2)] => apply eq_implies_set_eq; sem_eq_solver
    | [ H: forall r: PregEq.t, ?rs r = ?ars (?pid, r),
    Ha1: Val.addl (?rs ?r1) _ = Vptr ?b1 ?i1, 
    Ha2: Val.addl (?ars (?pid, ?r1)) _ = Vptr ?b2 ?i2
    |- ?v1 = ?v2] => pose proof H as Hdup; specialize (Hdup r1); rewrite <- Hdup in Ha2; sem_eq_solver
    | [ H: forall r: PregEq.t, ?rs r = ?ars (?pid, r),
    Ha1: Val.addl _ (?rs ?r1) = Vptr ?b1 ?i1, 
    Ha2: Val.addl _ (?ars (?pid, ?r1)) = Vptr ?b2 ?i2
    |- ?v1 = ?v2] => pose proof H as Hdupdup; specialize (Hdupdup r1); rewrite <- Hdupdup in Ha2; sem_eq_solver
    | [ Ha1: ?op ?e1 ?e2 = Vptr ?b1 ?i1, 
        Ha2: ?op ?e1 ?e2 = Vptr ?b2 ?i2,
        Ha3: _ _ ?m ?b1 (Ptrofs.unsigned ?i1) = Some ?v1,
        Ha4:  _ _ ?m ?b2 (Ptrofs.unsigned ?i2) = Some ?v2
    |- ?v1 = ?v2] => rewrite -> Ha1 in Ha2; inversion Ha2; subst; rewrite -> Ha3 in Ha4; inversion Ha4; reflexivity (*Terminal*)
    | [ |- Val.shll _ ?v1 = Val.shll _ ?v2] => apply invert_shll; sem_eq_solver
    | _ => idtac
    end. *)

(* Ltac sem_eq_solver := 
    match goal with
    | [ |- ?x = ?x ] => reflexivity (*Terminal*)
    | [H: regs_identical ?ars ?pid ?rs |- regs_identical ?ars ?pid ?rs] => apply H (*Terminal*)
    | [Hri: forall r: PregEq.t, ?rs r = ?ars (?pid, r)    |- ?rs ?r = ?ars (?pid, ?r) ] => apply Hri (*Terminal*)
    | [H1 : ?rs ?reg = Vptr ?b1 ?i1, H2: ?ars (?pid, ?reg) = Vptr ?b2 ?i2, Hri: forall r: PregEq.t, ?rs r = ?ars (?pid, r) 
        |- Vptr ?b1 ?z = Vptr ?b2 ?z] => specialize (Hri reg); rewrite -> Hri in H1; rewrite -> H2 in H1; inversion H1; reflexivity  (*Terminal*)
    | [ |- Val.offset_ptr _ ?v = Val.offset_ptr _ ?v] => apply cancel_dual_ptr_increments; sem_eq_solver
    | [ |- regs_identical _ _ _] => unfold regs_identical; intro; sem_eq_solver
    | [ |- Pregmap.set ?r1 _ ?rs ?r2 = PRmap.set (?pid, ?r1) _ ?ars (?pid, ?r2)] => apply eq_implies_set_eq; sem_eq_solver
    | [ Ha1: ?op ?e1 ?e2 = Vptr ?b1 ?i1, 
        Ha2: ?op ?e1 ?e2 = Vptr ?b2 ?i2,
        Ha3: _ _ ?m ?b1 (Ptrofs.unsigned ?i1) = Some ?v1,
        Ha4:  _ _ ?m ?b2 (Ptrofs.unsigned ?i2) = Some ?v2
    |- ?v1 = ?v2] => rewrite -> Ha1 in Ha2; inversion Ha2; subst; rewrite -> Ha3 in Ha4; inversion Ha4; reflexivity (*Terminal*)
    | [ Ha1: ?op ?e1 ?e2 = Vptr ?b1 ?i1, 
    Ha2: ?op ?e1 ?e2 = Vptr ?b2 ?i2,
    Ha3: _ _ ?m ?b1 (Ptrofs.unsigned ?i1) = Some ?v1,
    Ha4:  _ _ ?m ?b2 (Ptrofs.unsigned ?i2) = Some ?v2
    |- _ ?v1 = _ ?v2] => rewrite -> Ha1 in Ha2; inversion Ha2; subst; rewrite -> Ha3 in Ha4; inversion Ha4; reflexivity (*Terminal*)
    | [ |- Val.shll _ ?v1 = Val.shll _ ?v2] => apply invert_shll; sem_eq_solver
    | _ => idtac
    end. *)

Remark set_sem_eq : 
    forall (rs: regset) (ars: allregsets) (pid: processor_id) (r read_reg: preg) (v: val),
    regs_identical ars pid rs -> (rs # r <- v) read_reg = (ars @ (pid, r) <- v) (pid, read_reg).
    Proof. intros. unfold regs_identical in H. unfold Asm.Pregmap.set. unfold PRmap.set. destruct PregEq.eq; destruct PREq.eq. reflexivity. 
    destruct n. rewrite e. reflexivity. destruct n. inversion e. reflexivity.
    apply H. 
    Qed.

Ltac sem_eq_solver :=
    match goal with
    (*Identity*)
    [ |- ?x = ?x ] => reflexivity (*Terminal*)
    (*Prereq of a proof we already did upon entry*)
    | [H: regs_identical ?ars ?pid ?rs |- regs_identical ?ars ?pid ?rs] => apply H (*Terminal*)
    (*Gradually replace memsim regs with Asm regs*)
    | [H: forall r: PregEq.t, ?rs r = ?ars (?pid, r), 
          H2: context[?ars (?pid, ?r2)],
          H3: context[?rs ?r2] |- _] => pose proof H as Hdup3;  specialize (Hdup3 r2); rewrite <- Hdup3 in H2; clear Hdup3; sem_eq_solver (*Nonterminal*)
    (*Replace in goal as well*)
    | [H: forall r: PregEq.t, ?rs r = ?ars (?pid, r)
        |- context[?ars (?pid, ?r2)]] => pose proof H as Hdup3;  specialize (Hdup3 r2); rewrite <- Hdup3; clear Hdup3; sem_eq_solver (*Nonterminal*)
    (* Set equivalent*)
    | [ |- Pregmap.set ?r ?v ?rs ?r2 = PRmap.set (?pid, ?r) ?v ?ars (?pid, ?r2)] => apply set_sem_eq; sem_eq_solver (*Nonterminal*)
    (*Replace like hypotheses*)
    | [H1: ?x = ?y, H2: ?x = ?z |- _ ] => rewrite H1 in H2; sem_eq_solver (*Nonterminal*)
    (*Break apart optional*)
    | [H: Some ?v = Some ?v2 |- _] => inversion H; clear H; subst; sem_eq_solver (*Nonterminal*) 
    (*Pointer inversion*)
    | [H1: ?x = Vptr ?b1 ?i1,
       H2: ?x = Vptr ?b2 ?i2
       |- _ ] => rewrite -> H1 in H2; inversion H2; clear H2; subst; sem_eq_solver (*Nonterminal*)
    (*Pointer inversion*)
    | [H1: Vptr ?b1 ?i1 = Vptr ?b2 ?i2 |- _] => inversion H1; clear H1; subst; sem_eq_solver (*Nonterminal*)
    | [ |- Val.offset_ptr ?v1 ?n = Val.offset_ptr ?v2 ?n] => apply cancel_dual_ptr_increments; sem_eq_solver (*Nonterminal*)
    | _ => idtac
    end.

Theorem asm_identical_to_forward_sim: forall (pr: preg) (g: genv)(f: function) (i: Asm.instruction) (rs: regset) (ars: allregsets) (m: mem) (pid: processor_id), 
    regs_identical ars pid rs -> end_state_equals_asm_memsim pr (exec_instr g f i rs  m)  (eval_memsim_chain g f (asm_to_memsim i pid) ars m) pid.
Proof.
intros. pose proof H as ri. unfold regs_identical in H.  unfold end_state_equals_asm_memsim. destruct i; simpl; try unfold Asm.goto_label; try unfold goto_label; try unfold Asm.eval_testcond; try unfold eval_testcond; try unfold Asm.exec_load; try unfold exec_load; try unfold Asm.exec_store; try unfold exec_store; try unfold Mem.loadv; try unfold eval_addressing; try unfold Asm.eval_addressing; unfold Asm.compare_long; unfold compare_long; unfold Asm.compare_int; unfold compare_int; unfold Asm.ir0w; unfold ir0w; unfold Asm.ir0x; unfold ir0x; destruct matches; try split; try unfold nextinstr; try apply set_method_sem_eq_form3; try unfold regs_identical; try intro; sem_eq_solver.
Unset Printing Notations.
Qed.


      

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR X16 => false
  | IR X30 => false
  | IR _ => true
  | FR _ => true
  | CR _ => false
  | SP => true
  | PC => false
  end.


Lemma outcome_equality: forall (rs1 rs2: regset)(m1 m2: mem),  Next rs1 m1 = Next rs2 m2 -> rs1 = rs2 /\ m1 = m2. 
    Proof. intros. inversion H. split; reflexivity. Qed.

Lemma inverse_outcome_equality: forall (rs1 rs2: regset)(m1 m2: mem), rs1 = rs2 /\ m1 = m2 -> Next rs1 m1 = Next rs2 m2.
Proof. intros. destruct H. rewrite H. rewrite H0. reflexivity. Qed.

(* need some way of abstracting 
for a given instruction if an argument is a data source/data sink*)
Inductive data_resource: Type :=
    | SingleReg: preg -> data_resource
    | SingleMemAddr: memory_chunk -> val -> data_resource.
Definition data_res_eq (d1 d2: data_resource): Prop :=
    match d1, d2 with
    | SingleReg r1, SingleReg r2 => r1 = r2
    | SingleMemAddr c1 a1, SingleMemAddr c2 a2 => c1 = c2 /\ a1 = a2
    | _, _ => False
    end.

Definition iregz_same_resource (dr: data_resource) (r: ireg0) : Prop :=
    match r with 
    | RR0 r1 => data_res_eq dr (SingleReg r1) 
    | XZR => False
    end.
    
    
Remark data_res_isomorphism: forall r, data_res_eq r r.
Proof.
    intros. destruct r. unfold data_res_eq. reflexivity. unfold data_res_eq. split; reflexivity. 
Qed.

Lemma symb_data_eq: forall (x y: data_resource), {x=y} + {x<>y}.
Proof. decide equality. apply preg_eq. apply Val.eq. apply AST.chunk_eq.
Qed.

(* TODO Check if data resource d is an input for address a. Requires checking the regs of A*)
Definition data_address_src(a: addressing) (d: data_resource) : Prop := 
   match a with
   | ADimm base n => data_res_eq d (SingleReg (preg_of_iregsp base))
   | ADreg base r => data_res_eq d (SingleReg (preg_of_iregsp base)) \/  data_res_eq d (SingleReg r) 
   | ADlsl base r n => data_res_eq d  ( SingleReg (preg_of_iregsp base)) \/ data_res_eq d (SingleReg r) 
   | ADsxt base r n => data_res_eq d (SingleReg (preg_of_iregsp base)) \/ data_res_eq d (SingleReg r) 
   | ADuxt base r n => data_res_eq d (SingleReg (preg_of_iregsp base)) \/ data_res_eq d (SingleReg r) 
   | ADadr base id ofs => data_res_eq d (SingleReg (preg_of_iregsp base))
   | ADpostincr base n => True (* not modeled in CompCert*) 
   end.



 (* Check if data resource d is overwritten by a. Requires checking the evaluated expr*)
 Definition data_address_sink (a: addressing) (d: data_resource) (g: genv) (r: regset): Prop := 
    match d with
    | SingleMemAddr _ val => eval_addressing g a r = val
    | _ => False
    end.

(* TODO: change all instances of NoResource to false? kinda based*)

(* Get a proposition representing if an instruction has a dependency on dr*)
Definition data_source(i: instruction) (dr: data_resource): Prop := 
    match i with 
   (* Jump to*)
   | Pb lbl => False                                                    (**r branch *)
   | Pbc c lbl  => data_res_eq dr (SingleReg (CR CZ))                                    (**r conditional branch *)
   | Pbl id sg => data_res_eq dr (SingleReg PC)                                  (**r jump to function and link *)
   | Pbs id sg => False                              (**r jump to function *)
   | Pblr r sg  => data_res_eq dr (SingleReg PC)                                   (**r indirect jump and link *)
   | Pbr r sg   => data_res_eq dr (SingleReg PC)                                   (**r indirect jump *)
   | Pret r => False                                              (**r return *)
   | Pcbnz sz r lbl    => data_res_eq dr (SingleReg r)                      (**r branch if not zero *)
   | Pcbz sz r lbl => data_res_eq dr (SingleReg r)                         (**r branch if zero *)
   | Ptbnz sz r n lbl   => data_res_eq dr (SingleReg r)               (**r branch if bit n is not zero *)
   | Ptbz sz r n lbl => data_res_eq dr (SingleReg r)                  (**r branch if bit n is zero *)
   (** Memory loads and stores *)
   | Pldrw rd a => data_address_src a dr                             (**r load int32 *)
   | Pldrw_a rd a => data_address_src a dr                                 (**r load int32 as any32 *)
   | Pldrx rd a => data_address_src a dr                                  (**r load int64 *)
   | Pldrx_a rd a => data_address_src a dr                                 (**r load int64 as any64 *)
   | Pldrb sz rd a => data_address_src a dr                         (**r load int8, zero-extend *)
   | Pldrsb sz rd a => data_address_src a dr                        (**r load int8, sign-extend *)
   | Pldrh sz rd a => data_address_src a dr                        (**r load int16, zero-extend *)
   | Pldrsh sz rd a => data_address_src a dr                        (**r load int16, sign-extend *)
   | Pldrzw rd a  => data_address_src a dr                                  (**r load int32, zero-extend to int64 *)
   | Pldrsw rd a => data_res_eq dr (SingleReg rd)                                 (**r load int32, sign-extend to int64 *)
   | Pldp rd1 rd2 a => data_res_eq dr (SingleReg rd1) \/ data_res_eq dr (SingleReg rd2)                               (**r load two int64 *)
   (** Stores *)
   | Pstrw rs a => data_res_eq dr (SingleReg rs)                               (**r store int32 *)
   | Pstrw_a rs a => data_res_eq dr (SingleReg rs)                                     (**r store int32 as any32 *)
   | Pstrx rs a => data_res_eq dr (SingleReg rs)                                      (**r store int64 *)
   | Pstrx_a rs a => data_res_eq dr (SingleReg rs)                                   (**r store int64 as any64 *)
   | Pstrb rs a => data_res_eq dr (SingleReg rs)                                    (**r store int8 *)
   | Pstrh rs a => data_res_eq dr (SingleReg rs)                                    (**r store int16 *)
   | Pstp rs1 rs2 a => data_res_eq dr (SingleReg rs1)  \/ data_res_eq dr (SingleReg rs2)                               (**r store two int64 *)
   (** Integer arithmetic, immediate *)
   | Paddimm sz rd r1 n  => data_res_eq dr (SingleReg (preg_of_iregsp r1))            (**r addition *)
   | Psubimm sz rd r1 n => data_res_eq dr (SingleReg (preg_of_iregsp r1))               (**r subtraction *)
   | Pcmpimm sz r1 n => data_res_eq dr (SingleReg r1)                             (**r compare *)
   | Pcmnimm sz r1 n => data_res_eq dr (SingleReg r1)                              (**r compare negative *)
   (** Move integer register *)
   | Pmov rd r1 => data_res_eq dr (SingleReg (preg_of_iregsp r1)) 
   (** Logical, immediate *)
   | Pandimm sz rd r1 n => iregz_same_resource dr r1                 (**r and *)
   | Peorimm sz rd r1 n => iregz_same_resource dr r1                  (**r xor *)
   | Porrimm sz rd r1 n => iregz_same_resource dr r1                  (**r or *)
   | Ptstimm sz r1 n => data_res_eq dr (SingleReg r1)                             (**r and, then set flags *)
   (** Move wide immediate *)
   | Pmovz sz rd n pos  => False                (**r move [n << pos] to [rd] *)
   | Pmovn sz rd n pos  => False                (**r move [NOT(n << pos)] to [rd] *)
   | Pmovk sz rd n pos  => False                (**r insert 16 bits of [n] at [pos] in rd *)
   (** PC-relative addressing *)
   | Padrp rd id ofs => False                   (**r set [rd] to high address of [id + ofs] *)
   | Paddadr rd r1 id ofs => data_res_eq dr (SingleReg r1)             (**r add the low address of [id + ofs] *)
   (** Bit-field operations *)
   | Psbfiz sz rd r1 r s => data_res_eq dr (SingleReg r1)           (**r sign extend and shift left *)
   | Psbfx sz rd r1 r s => data_res_eq dr (SingleReg r1)           (**r shift right and sign extend *)
   | Pubfiz sz rd r1 r s => data_res_eq dr (SingleReg r1)           (**r zero extend and shift left *)
   | Pubfx sz rd r1 r s => data_res_eq dr (SingleReg r1)           (**r shift right and zero extend *)
   (** Integer arithmetic, shifted register *)
   | Padd sz rd r1 r2 s => iregz_same_resource dr r1 \/ data_res_eq dr (SingleReg r2)    (**r addition *)
   | Psub sz rd r1 r2 s => iregz_same_resource dr r1 \/ data_res_eq dr (SingleReg r2)   (**r subtraction *)
   | Pcmp sz r1 r2 s => iregz_same_resource dr r1 \/ data_res_eq dr (SingleReg r2)              (**r compare *)
   | Pcmn sz r1 r2 s => iregz_same_resource dr r1 \/ data_res_eq dr (SingleReg r2)              (**r compare negative *)
   (** Integer arithmetic, extending register *)
   | Paddext rd r1 r2 x => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)        (**r int64-int32 add *)
   | Psubext rd r1 r2 x => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)        (**r int64-int32 sub *)
   | Pcmpext r1 r2 x => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                     (**r int64-int32 cmp *)
   | Pcmnext r1 r2 x => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                       (**r int64-int32 cmn *)
   (** Logical, shifted register *)
   | Pand sz rd r1 r2 s => iregz_same_resource dr r1 \/ data_res_eq dr (SingleReg r2)   (**r and *)
   | Pbic sz rd r1 r2 s => iregz_same_resource dr r1 \/ data_res_eq dr (SingleReg r2)   (**r and-not *)
   | Peon sz rd r1 r2 s => iregz_same_resource dr r1 \/ data_res_eq dr (SingleReg r2)   (**r xor-not *)
   | Peor sz rd r1 r2 s => iregz_same_resource dr r1 \/ data_res_eq dr (SingleReg r2)   (**r xor *)
   | Porr sz rd r1 r2 s => iregz_same_resource dr r1 \/ data_res_eq dr (SingleReg r2)   (**r or *)
   | Porn sz rd r1 r2 s => iregz_same_resource dr r1 \/ data_res_eq dr (SingleReg r2)   (**r or-not *)
   | Ptst sz r1 r2 s => iregz_same_resource dr r1 \/ data_res_eq dr (SingleReg r2)                (**r and, then set flags *)
   (** Variable shifts *)
   | Pasrv sz rd r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                         (**r arithmetic right shift *)
   | Plslv sz rd r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                         (**r left shift *)
   | Plsrv sz rd r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                         (**r logical right shift *)
   | Prorv sz rd r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                        (**r rotate right *)
   (** Bit operations *)
   | Pcls sz rd r1 => data_res_eq dr (SingleReg r1)                                    (**r count leading sign bits *)
   | Pclz sz rd r1 => data_res_eq dr (SingleReg r1)                                     (**r count leading zero bits *)
   | Prev sz rd r1 => data_res_eq dr (SingleReg r1)                                    (**r reverse bytes *)
   | Prev16 sz rd r1 => data_res_eq dr (SingleReg r1)                                   (**r reverse bytes in each 16-bit word *)
   | Prbit sz rd r1  => data_res_eq dr (SingleReg r1)                                   (**r reverse bits *)
   (** Conditional data processing *)
   | Pcsel rd r1 r2 c  => data_res_eq dr (SingleReg r1)  \/ data_res_eq dr (SingleReg r2)                      (**r int conditional move *)
    (*TODO: anything more to handle conditions?*)
   | Pcset rd c => False                               (**r set to 1/0 if cond is true/false *)
   (*
   | Pcsetm rd c                                   (**r set to -1/0 if cond is true/false *)
   *)
   (** Integer multiply/divide *)
   | Pmadd sz rd r1 r2 r3 =>  data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2) \/ iregz_same_resource dr r3              (**r multiply-add *)
   | Pmsub sz rd r1 r2 r3 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2) \/ iregz_same_resource dr r3            (**r multiply-sub *)
   | Psmulh rd r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                                   (**r signed multiply high *)
   | Pumulh rd r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                                   (**r unsigned multiply high *)
   | Psdiv sz rd r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                       (**r signed division *)
   | Pudiv sz rd r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                       (**r unsigned division *)
   (** Floating-point loads and stores *)
   | Pldrs rd a => data_address_src a dr                                   (**r load float32 (single precision) *)
   | Pldrd rd a => data_address_src a dr                                  (**r load float64 (double precision) *)
   | Pldrd_a rd a => data_address_src a dr                                (**r load float64 as any64 *)
   | Pstrs rs a => data_res_eq dr (SingleReg rs)                                   (**r store float32 *)
   | Pstrd rs a => data_res_eq dr (SingleReg rs)                                   (**r store float64 *)
   | Pstrd_a rs a => data_res_eq dr (SingleReg rs)                                (**r store float64 as any64 *)
   (** Floating-point move *)
   | Pfmov rd r1 => data_res_eq dr (SingleReg r1) 
   | Pfmovimms rd f  => False                                (**r load float32 constant *)
   | Pfmovimmd rd f  => False                                  (**r load float64 constant *)
   | Pfmovi fsz rd r1 => iregz_same_resource dr r1                         (**r copy int reg to FP reg *)
   (** Floating-point conversions *)
   | Pfcvtds rd r1  => data_res_eq dr (SingleReg r1)                                            (**r convert float32 to float64 *)
   | Pfcvtsd rd r1  => data_res_eq dr (SingleReg r1)                                           (**r convert float64 to float32 *)
   | Pfcvtzs isz fsz rd r1 => data_res_eq dr (SingleReg r1)            (**r convert float to signed int *)
   | Pfcvtzu isz fsz rd r1 => data_res_eq dr (SingleReg r1)           (**r convert float to unsigned int *)
   | Pscvtf fsz isz rd r1 => data_res_eq dr (SingleReg r1)             (**r convert signed int to float *)
   | Pucvtf fsz isz rd r1 => data_res_eq dr (SingleReg r1)            (**r convert unsigned int to float *)
   (** Floating-point arithmetic *)
   | Pfabs sz rd r1 => data_res_eq dr (SingleReg r1)                                    (**r absolute value *)
   | Pfneg sz rd r1 => data_res_eq dr (SingleReg r1)                                    (**r negation *)
   | Pfsqrt sz rd r1 => data_res_eq dr (SingleReg r1)                                   (**r square root *)
   | Pfadd sz rd r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                                 (**r addition *)
   | Pfdiv sz rd r1 r2  => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                               (**r division *)
   | Pfmul sz rd r1 r2  => data_res_eq dr (SingleReg r1)  \/ data_res_eq dr (SingleReg r2)                             (**r multiplication *)
   | Pfnmul sz rd r1 r2 => data_res_eq dr (SingleReg r1)  \/ data_res_eq dr (SingleReg r2)                             (**r multiply-negate *)
   | Pfsub sz rd r1 r2 => data_res_eq dr (SingleReg r1)   \/ data_res_eq dr (SingleReg r2)                              (**r subtraction *)
   | Pfmadd sz rd r1 r2 r3 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2) \/ data_res_eq dr (SingleReg r3)                            (**r [rd = r3 + r1 * r2] *)
   | Pfmsub sz rd r1 r2 r3 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2) \/ data_res_eq dr (SingleReg r3)                            (**r [rd = r3 - r1 * r2] *)
   | Pfnmadd sz rd r1 r2 r3 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2) \/ data_res_eq dr (SingleReg r3)                           (**r [rd = - r3 - r1 * r2] *)
   | Pfnmsub sz rd r1 r2 r3 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2) \/ data_res_eq dr (SingleReg r3)                           (**r [rd = - r3 + r1 * r2] *)
   | Pfmax sz rd r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                                (**r maximum *)
   | Pfmin sz rd r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                               (**r minimum *)
   (** Floating-point comparison *)
   | Pfcmp sz r1 r2 => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)                                   (**r compare [r1] and [r2] *)
   | Pfcmp0 sz r1 => data_res_eq dr (SingleReg r1)                                      (**r compare [r1] and [+0.0] *)
   (** Floating-point conditional select *)
   (*TODO: figure out cond*)
   | Pfsel rd r1 r2 cond => data_res_eq dr (SingleReg r1) \/ data_res_eq dr (SingleReg r2)
   (** Pseudo-instructions *)
   | Pallocframe sz linkofs => False                              (**r allocate new stack frame *)
   | Pfreeframe sz linkofs => False                               (**r deallocate stack frame and restore previous frame *)
   | Plabel lbl => False                                                (**r define a code label *)
   | Ploadsymbol rd id => False                                 (**r load the address of [id] *)
   | Pcvtsw2x rd r1 => data_res_eq dr (SingleReg r1)                                 (**r sign-extend 32-bit int to 64-bit *)
   | Pcvtuw2x rd r1 => data_res_eq dr (SingleReg r1)                                  (**r zero-extend 32-bit int to 64-bit *)
   | Pcvtx2w rd => data_res_eq dr (SingleReg rd)                                                 (**r retype a 64-bit int as a 32-bit int *)
   | Pbtbl r1 tbl  => False                              (**r N-way branch through a jump table *)
   | Pbuiltin ef args res => False   (**r built-in function (pseudo) *)
   | Pnop => False                                                             (**r no operation *)
   | Pcfi_adjust ofs => False                                           (**r .cfi_adjust debug directive *)
   | Pcfi_rel_offset ofs  => False                                       (**r .cfi_rel_offset debug directive *)
   | Pincpc => data_res_eq dr (SingleReg PC) 
    end.

Definition data_sink(i: instruction) (dr: data_resource) (g: genv) (ers: regset): Prop := 
    match i with
    (*actual*)
    (* Jump to*)
    | Pb lbl pid => data_res_eq dr (SingleReg PC)                                                    (**r branch *)
    | Pbc c lbl  pid => data_res_eq dr (SingleReg PC)                                    (**r conditional branch *)
    | Pbl id sg pid => data_res_eq dr (SingleReg PC) \/ data_res_eq dr (SingleReg RA)                                    (**r jump to function and link *)
    | Pbs id sg pid => data_res_eq dr (SingleReg PC)                                   (**r jump to function *)
    | Pblr r sg  pid => data_res_eq dr (SingleReg PC)  \/ data_res_eq dr (SingleReg RA)                                (**r indirect jump and link *)
    | Pbr r sg   pid => data_res_eq dr (SingleReg PC)                                   (**r indirect jump *)
    | Pret r pid => data_res_eq dr (SingleReg PC)                                                     (**r return *)
    | Pcbnz sz r lbl    pid => data_res_eq dr (SingleReg PC)                       (**r branch if not zero *)
    | Pcbz sz r lbl pid => data_res_eq dr (SingleReg PC)                           (**r branch if zero *)
    | Ptbnz sz r n lbl   pid => data_res_eq dr (SingleReg PC)               (**r branch if bit n is not zero *)
    | Ptbz sz r n lbl pid => data_res_eq dr (SingleReg PC)                  (**r branch if bit n is zero *)
    (** Memory loads and stores *)
    | Pldrw rd a pid => data_res_eq dr (SingleReg rd)                                 (**r load int32 *)
    | Pldrw_a rd a pid => data_res_eq dr (SingleReg rd)                                (**r load int32 as any32 *)
    | Pldrx rd a pid => data_res_eq dr (SingleReg rd)                                 (**r load int64 *)
    | Pldrx_a rd a pid => data_res_eq dr (SingleReg rd)                                (**r load int64 as any64 *)
    | Pldrb sz rd a pid => data_res_eq dr (SingleReg (preg_of_iregsp rd))                        (**r load int8, zero-extend *)
    | Pldrsb sz rd a pid => data_res_eq dr (SingleReg (preg_of_iregsp rd))                      (**r load int8, sign-extend *)
    | Pldrh sz rd a pid => data_res_eq dr (SingleReg (preg_of_iregsp rd))                       (**r load int16, zero-extend *)
    | Pldrsh sz rd a pid => data_res_eq dr (SingleReg (preg_of_iregsp rd))                      (**r load int16, sign-extend *)
    | Pldrzw rd a  pid => data_res_eq dr (SingleReg rd)                                 (**r load int32, zero-extend to int64 *)
    | Pldrsw rd a pid => data_res_eq dr (SingleReg rd)                                 (**r load int32, sign-extend to int64 *)
    | Pldp rd1 rd2 a pid => data_res_eq dr (SingleReg rd1) \/ data_res_eq dr (SingleReg rd2)                               (**r load two int64 *)
    (*TODO: check this works *)
    (* explanation: check if r is a memory address and, if so, check if a stores in r. Can check by evaluating both??? *)
    | Pstrw rs a pid => data_address_sink a dr g ers                                 (**r store int32 *)
    | Pstrw_a rs a pid => data_address_sink a dr g ers                                  (**r store int32 as any32 *)
    | Pstrx rs a pid => data_address_sink a dr g ers                                    (**r store int64 *)
    | Pstrx_a rs a pid => data_address_sink a dr g ers                                  (**r store int64 as any64 *)
    | Pstrb rs a pid => data_address_sink a dr g ers                                   (**r store int8 *)
    | Pstrh rs a pid => data_address_sink a dr g ers                                   (**r store int16 *)
    | Pstp rs1 rs2 a pid => data_address_sink a dr g ers                                (**r store two int64 *)
    (** Integer arithmetic, immediate *)
    | Paddimm sz rd r1 n  pid => data_res_eq dr (SingleReg (preg_of_iregsp rd))            (**r addition *)
    | Psubimm sz rd r1 n pid => data_res_eq dr (SingleReg (preg_of_iregsp rd))               (**r subtraction *)
    | Pcmpimm sz r1 n pid => data_res_eq dr (SingleReg (CR CZ))                             (**r compare *)
    | Pcmnimm sz r1 n pid => data_res_eq dr (SingleReg (CR CZ))                              (**r compare negative *)
    (** Move integer register *)
    | Pmov rd r1 pid => data_res_eq dr (SingleReg (preg_of_iregsp rd)) 
    (** Logical, immediate *)
    | Pandimm sz rd r1 n pid => data_res_eq dr (SingleReg rd)                  (**r and *)
    | Peorimm sz rd r1 n pid => data_res_eq dr (SingleReg rd)                  (**r xor *)
    | Porrimm sz rd r1 n pid => data_res_eq dr (SingleReg (preg_of_iregsp rd))                  (**r or *)
    | Ptstimm sz r1 n pid => data_res_eq dr (SingleReg (CR CZ))                             (**r and, then set flags *)
    (** Move wide immediate *)
    | Pmovz sz rd n pos  pid => data_res_eq dr (SingleReg rd)                     (**r move [n << pos] to [rd] *)
    | Pmovn sz rd n pos  pid => data_res_eq dr (SingleReg rd)                     (**r move [NOT(n << pos)] to [rd] *)
    | Pmovk sz rd n pos  pid => data_res_eq dr (SingleReg rd)                     (**r insert 16 bits of [n] at [pos] in rd *)
    (** PC-relative addressing *)
    | Padrp rd id ofs pid => data_res_eq dr (SingleReg rd)                        (**r set [rd] to high address of [id + ofs] *)
    | Paddadr rd r1 id ofs pid => data_res_eq dr (SingleReg rd)             (**r add the low address of [id + ofs] *)
    (** Bit-field operations *)
    | Psbfiz sz rd r1 r s pid => data_res_eq dr (SingleReg rd)           (**r sign extend and shift left *)
    | Psbfx sz rd r1 r s pid => data_res_eq dr (SingleReg rd)           (**r shift right and sign extend *)
    | Pubfiz sz rd r1 r s pid => data_res_eq dr (SingleReg rd)           (**r zero extend and shift left *)
    | Pubfx sz rd r1 r s pid => data_res_eq dr (SingleReg rd)           (**r shift right and zero extend *)
    (** Integer arithmetic, shifted register *)
    | Padd sz rd r1 r2 s pid => data_res_eq dr (SingleReg rd)    (**r addition *)
    | Psub sz rd r1 r2 s pid => data_res_eq dr (SingleReg rd)   (**r subtraction *)
    | Pcmp sz r1 r2 s pid => data_res_eq dr (SingleReg (CR CZ))              (**r compare *)
    | Pcmn sz r1 r2 s pid => data_res_eq dr (SingleReg (CR CZ))              (**r compare negative *)
    (** Integer arithmetic, extending register *)
    | Paddext rd r1 r2 x pid => data_res_eq dr (SingleReg (preg_of_iregsp rd))        (**r int64-int32 add *)
    | Psubext rd r1 r2 x pid => data_res_eq dr (SingleReg (preg_of_iregsp rd))        (**r int64-int32 sub *)
    | Pcmpext r1 r2 x pid => data_res_eq dr (SingleReg (CR CZ))                      (**r int64-int32 cmp *)
    | Pcmnext r1 r2 x pid => data_res_eq dr (SingleReg (CR CZ))                       (**r int64-int32 cmn *)
    (** Logical, shifted register *)
    | Pand sz rd r1 r2 s pid => data_res_eq dr (SingleReg rd)   (**r and *)
    | Pbic sz rd r1 r2 s pid => data_res_eq dr (SingleReg rd)   (**r and-not *)
    | Peon sz rd r1 r2 s pid => data_res_eq dr (SingleReg rd)   (**r xor-not *)
    | Peor sz rd r1 r2 s pid => data_res_eq dr (SingleReg rd)   (**r xor *)
    | Porr sz rd r1 r2 s pid => data_res_eq dr (SingleReg rd)   (**r or *)
    | Porn sz rd r1 r2 s pid => data_res_eq dr (SingleReg rd)   (**r or-not *)
    | Ptst sz r1 r2 s pid => data_res_eq dr (SingleReg (CR CZ))                (**r and, then set flags *)
    (** Variable shifts *)
    | Pasrv sz rd r1 r2 pid => data_res_eq dr (SingleReg rd)                         (**r arithmetic right shift *)
    | Plslv sz rd r1 r2 pid => data_res_eq dr (SingleReg rd)                         (**r left shift *)
    | Plsrv sz rd r1 r2 pid => data_res_eq dr (SingleReg rd)                         (**r logical right shift *)
    | Prorv sz rd r1 r2 pid => data_res_eq dr (SingleReg rd)                        (**r rotate right *)
    (** Bit operations *)
    | Pcls sz rd r1 pid => data_res_eq dr (SingleReg rd)                                     (**r count leading sign bits *)
    | Pclz sz rd r1 pid => data_res_eq dr (SingleReg rd)                                     (**r count leading zero bits *)
    | Prev sz rd r1 pid => data_res_eq dr (SingleReg rd)                                    (**r reverse bytes *)
    | Prev16 sz rd r1 pid => data_res_eq dr (SingleReg rd)                                   (**r reverse bytes in each 16-bit word *)
    | Prbit sz rd r1  pid => data_res_eq dr (SingleReg rd)                                   (**r reverse bits *)
    (** Conditional data processing *)
    | Pcsel rd r1 r2 c  pid => data_res_eq dr (SingleReg rd)                     (**r int conditional move *)
    | Pcset rd c pid => data_res_eq dr (SingleReg rd)                                     (**r set to 1/0 if cond is true/false *)
    (*
    | Pcsetm rd c                                   (**r set to -1/0 if cond is true/false *)
    *)
    (** Integer multiply/divide *)
    | Pmadd sz rd r1 r2 r3 pid => data_res_eq dr (SingleReg rd)             (**r multiply-add *)
    | Pmsub sz rd r1 r2 r3 pid => data_res_eq dr (SingleReg rd)             (**r multiply-sub *)
    | Psmulh rd r1 r2 pid => data_res_eq dr (SingleReg rd)                                   (**r signed multiply high *)
    | Pumulh rd r1 r2 pid => data_res_eq dr (SingleReg rd)                                    (**r unsigned multiply high *)
    | Psdiv sz rd r1 r2 pid => data_res_eq dr (SingleReg rd)                        (**r signed division *)
    | Pudiv sz rd r1 r2 pid => data_res_eq dr (SingleReg rd)                        (**r unsigned division *)
    (** Floating-point loads and stores *)
    | Pldrs rd a pid => data_res_eq dr (SingleReg rd)                                   (**r load float32 (single precision) *)
    | Pldrd rd a pid => data_res_eq dr (SingleReg rd)                                  (**r load float64 (double precision) *)
    | Pldrd_a rd a pid => data_res_eq dr (SingleReg rd)                                (**r load float64 as any64 *)
    | Pstrs rs a pid => data_address_sink a dr g ers                                   (**r store float32 *)
    | Pstrd rs a pid => data_address_sink a dr g ers                                   (**r store float64 *)
    | Pstrd_a rs a pid => data_address_sink a dr g ers                                (**r store float64 as any64 *)
    (** Floating-point move *)
    | Pfmov rd r1 pid => data_res_eq dr (SingleReg rd) 
    | Pfmovimms rd f  pid => data_res_eq dr (SingleReg rd)                                (**r load float32 constant *)
    | Pfmovimmd rd f  pid => data_res_eq dr (SingleReg rd)                                  (**r load float64 constant *)
    | Pfmovi fsz rd r1 pid => data_res_eq dr (SingleReg rd)                         (**r copy int reg to FP reg *)
    (** Floating-point conversions *)
    | Pfcvtds rd r1  pid => data_res_eq dr (SingleReg rd)                                            (**r convert float32 to float64 *)
    | Pfcvtsd rd r1  pid => data_res_eq dr (SingleReg rd)                                           (**r convert float64 to float32 *)
    | Pfcvtzs isz fsz rd r1 pid => data_res_eq dr (SingleReg rd)            (**r convert float to signed int *)
    | Pfcvtzu isz fsz rd r1 pid => data_res_eq dr (SingleReg rd)           (**r convert float to unsigned int *)
    | Pscvtf fsz isz rd r1 pid => data_res_eq dr (SingleReg rd)             (**r convert signed int to float *)
    | Pucvtf fsz isz rd r1 pid => data_res_eq dr (SingleReg rd)            (**r convert unsigned int to float *)
    (** Floating-point arithmetic *)
    | Pfabs sz rd r1 pid => data_res_eq dr (SingleReg rd)                                    (**r absolute value *)
    | Pfneg sz rd r1 pid => data_res_eq dr (SingleReg rd)                                    (**r negation *)
    | Pfsqrt sz rd r1 pid => data_res_eq dr (SingleReg rd)                                   (**r square root *)
    | Pfadd sz rd r1 r2 pid => data_res_eq dr (SingleReg rd)                                (**r addition *)
    | Pfdiv sz rd r1 r2  pid => data_res_eq dr (SingleReg rd)                                (**r division *)
    | Pfmul sz rd r1 r2  pid => data_res_eq dr (SingleReg rd)                               (**r multiplication *)
    | Pfnmul sz rd r1 r2 pid => data_res_eq dr (SingleReg rd)                               (**r multiply-negate *)
    | Pfsub sz rd r1 r2 pid => data_res_eq dr (SingleReg rd)                                 (**r subtraction *)
    | Pfmadd sz rd r1 r2 r3 pid => data_res_eq dr (SingleReg rd)                             (**r [rd = r3 + r1 * r2] *)
    | Pfmsub sz rd r1 r2 r3 pid => data_res_eq dr (SingleReg rd)                             (**r [rd = r3 - r1 * r2] *)
    | Pfnmadd sz rd r1 r2 r3 pid => data_res_eq dr (SingleReg rd)                            (**r [rd = - r3 - r1 * r2] *)
    | Pfnmsub sz rd r1 r2 r3 pid => data_res_eq dr (SingleReg rd)                           (**r [rd = - r3 + r1 * r2] *)
    | Pfmax sz rd r1 r2 pid => data_res_eq dr (SingleReg rd)                                (**r maximum *)
    | Pfmin sz rd r1 r2 pid => data_res_eq dr (SingleReg rd)                                (**r minimum *)
    (** Floating-point comparison *)
    | Pfcmp sz r1 r2 pid => data_res_eq dr (SingleReg (CR CZ))                                   (**r compare [r1] and [r2] *)
    | Pfcmp0 sz r1 pid => data_res_eq dr (SingleReg (CR CZ))                                      (**r compare [r1] and [+0.0] *)
    (** Floating-point conditional select *)
    | Pfsel rd r1 r2 cond pid => data_res_eq dr (SingleReg rd) 
    (** Pseudo-instructions *)
    | Pallocframe sz linkofs pid => False                            (**r allocate new stack frame *)
    | Pfreeframe sz linkofs pid => False                             (**r deallocate stack frame and restore previous frame *)
    | Plabel lbl pid => False                                              (**r define a code label *)
    | Ploadsymbol rd id pid => data_res_eq dr (SingleReg rd)                                (**r load the address of [id] *)
    | Pcvtsw2x rd r1 pid => data_res_eq dr (SingleReg rd)                                    (**r sign-extend 32-bit int to 64-bit *)
    | Pcvtuw2x rd r1 pid => data_res_eq dr (SingleReg rd)                                    (**r zero-extend 32-bit int to 64-bit *)
    | Pcvtx2w rd pid => data_res_eq dr (SingleReg rd)                                                 (**r retype a 64-bit int as a 32-bit int *)
    | Pbtbl r1 tbl  pid => False                            (**r N-way branch through a jump table *)
    | Pbuiltin ef args res pid => False (**r built-in function (pseudo) *)
    | Pnop pid => False                                                           (**r no operation *)
    | Pcfi_adjust ofs pid => False                                         (**r .cfi_adjust debug directive *)
    | Pcfi_rel_offset ofs  pid => False                                     (**r .cfi_rel_offset debug directive *)
    | Pincpc pid => data_res_eq dr (SingleReg PC) 
end.



Definition data_dependence(i1 i2: instruction) g rs: Prop :=
    (exists r, data_sink i1 r g rs /\ data_source i2 r) \/ (exists r, data_sink i2 r g rs /\ data_source i1 r) \/ (exists r, data_sink i2 r g rs /\ data_sink i1 r g rs).


Remark not_or_and : forall A B : Prop, ~(A \/ B) -> ~A /\ ~B.
Proof.
  intros A B H. split.
    - intro. apply H. left. assumption.
    - intro. apply H. right. assumption.
Qed.

Remark not_or_or_and : forall A B C : Prop, ~(A \/ B \/ C) -> ~A /\ ~B /\ ~C.
Proof.
  intros A B C H. split; [|split].
  - intro HA. apply H. left. assumption.
  - intro HB. apply H. right. left. assumption.
  - intro HC. apply H. right. right. assumption.
Qed.

Lemma hazard_elimination_identity: forall r1, ~(exists r2: data_resource, data_res_eq r2 r1 /\ True)  -> False.
Proof. intros. apply H. exists r1. split. apply data_res_isomorphism. reflexivity. Qed.

Lemma hazard_elimination: forall (d: data_resource), ~ (exists r : data_resource, data_res_eq r (d) /\ data_res_eq r (d)) -> False.
Proof. intros. apply H. exists d. split; apply data_res_isomorphism. 
Qed.


 Remark regs_are_different_resources: forall r1 r2, ~
 (exists r : data_resource, data_res_eq r (SingleReg r1) /\ data_res_eq r (SingleReg r2)) -> r1 <> r2.
 Proof.
 unfold not. intros. apply H. exists (SingleReg r1). 
 split. try apply data_res_isomorphism. 
rewrite <- H0; apply data_res_isomorphism.
Qed.

Remark resources_are_different_resources: forall r1 r2,  ~
 (exists r : data_resource, data_res_eq r r1 /\ data_res_eq r r2) ->  r1 <> r2.
 Proof.
 unfold not. intros. apply H. exists r1. 
 split. try apply data_res_isomorphism. auto. 
  try (rewrite <- H0; apply data_res_isomorphism).
Qed.

Remark VInt_eq: forall i1 i2, Vint i1 = Vint i2 -> i1 = i2.
Proof. intros. inv H. reflexivity. Qed.

(* Theorem reorder: forall  g (f: function) (i1 i2: instruction)  (rs_i rs_t1 rs_t2 rs_f: regset)  (m_i m_t1 m_t2 m_f: mem), ~data_dependence i1 i2 g rs_i -> exec_instr g f i1 rs_i m_i = Next rs_t1 m_t1 -> exec_instr g f i2 rs_i m_i = Next rs_t2 m_t2 -> exec_instr g f i2 rs_t1 m_t1 = Next rs_f m_f -> exec_instr g f i1 rs_t2 m_t2 = Next rs_f m_f. *)
(* Theorem reorder: forall g (f: function) (i1 i2: instruction) (rs_i: regset) (m_i: mem), ~data_dependence i1 i2 g rs_i -> i1 = exec_instr g f i2 (exec_instr g f i1 (Next rs_i m_i)) = exec_instr g f i1 (exec_instr g f i2 (Next rs_i m_i)). *)

Ltac Super_Equalities :=
  match goal with
  | [ H_gso: ?a @ ?b <- (?a ?c) ?d = ?e |- _ ] =>
    rewrite -> Pregmap.gso in H_gso; Super_Equalities
  | [ H1: Vint ?a = Vint ?b, H2: Vint ?a = Vint ?c |- _ ] =>
    rewrite H1 in H2; apply VInt_eq; Super_Equalities
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Super_Equalities
  | [ H_destroy: ?a = ?b |- _] => subst a; Super_Equalities
  | _ => idtac
  end.


Theorem reorder: forall g (f: function) arg11 arg12 (i2: instruction) (rs_i: regset) (m_i: mem), ~data_dependence (Pmov arg11 arg12) i2 g rs_i -> exec_instr g f i2  (exec_instr g f (Pmov arg11 arg12)  (Next rs_i m_i)) = exec_instr g f (Pmov arg11 arg12)  (exec_instr g f i2  (Next rs_i m_i)).
Proof. intros. 
(* Definition unwrapping*)
unfold data_dependence in H. unfold data_sink, data_source in H. apply not_or_or_and in H; destruct H; destruct H0. destruct i2.
(* unfold data_dependence in H. unfold data_sink, data_source in H. destruct i1. destruct i2; apply not_or_or_and in H; destruct H; destruct H0; *)
(* Remove data hazards that hit the same singleton register (eg PC, CR)*)
try (apply hazard_elimination in H1;  contradiction +  unfold not;  intros;  discriminate H2);
try (apply hazard_elimination in H;  contradiction +  unfold not;  intros;  discriminate H2);
try (apply hazard_elimination in H0;  contradiction +  unfold not;  intros;  discriminate H2);



(* Remove data hazards that hit True - maybe WIP?*)
try (apply hazard_elimination_identity in H; contradiction + unfold not; intros; discriminate H2);

try (apply hazard_elimination_identity in H0; contradiction + unfold not; intros; discriminate H2);

try (apply hazard_elimination_identity in H1; contradiction + unfold not; intros; discriminate H2); auto;

auto;

(*Prove data vals different*)
(* apply regs_are_different_resources in H1 || clear H1; apply regs_are_different_resources in H0 || clear H0; apply regs_are_different_resources in H || clear H; *)
try apply regs_are_different_resources; try apply regs_are_different_resources in H0; try apply regs_are_different_resources in H;  
unfold exec_instr; unfold nextinstr; unfold goto_label; unfold eval_testcond; destruct matches; auto; 
(* Changing the order will not change the end result (Stuck/Next)*)
Super_Equalities; auto.

(* 
(*breakdown mov*)


(* Expression should be in the form Next ... = Next...*)
-apply inverse_outcome_equality; split. rewrite -> Pregmap.gso. rewrite -> Heqv in Heqv0. inversion Heqv0. apply Pregmap.gscsc. auto. auto. auto.
- rewrite -> Pregmap.gso in Heqv0. rewrite -> Heqv0 in Heqv2. discriminate. assumption.


(* 
try (rewrite -> Pregmap.gso in Heqv; rewrite -> Heqv in Heqv0; try discriminate + assumption). Qed.


(*breakdown goto*)
unfold goto_label. destruct matches; rewrite -> Pregmap.gso in Heqv; try rewrite -> Heqv in Heqv0; try discriminate;
try apply regs_are_different_resources in H1; try apply regs_are_different_resources in H0; try apply regs_are_different_resources in H; auto.

apply inverse_outcome_equality. split. rewrite -> Pregmap.gso. inversion Heqv0. rewrite <- H3. apply Pregmap.gscsc. assumption. auto. reflexivity. 



contradiction.
destruct (label_pos lbl 0 (fn_code f)); try reflexivity.  try rewrite -> Pregmap.gso; try destruct (rs_i PC); try reflexivity; try (apply inverse_outcome_equality; rewrite -> Pregmap.gso; try split; try apply Pregmap.gscsc);


(*breakdown testcond*)
unfold eval_testcond.  destruct c;  try rewrite -> Pregmap.gso.


(*breakdown exec_add*)

(*breakdown exec_load*)


auto.  try apply regs_are_different_resources in H1. apply regs_are_different_resources in H0. auto.
inversion H0. unfold nextinstr. rewrite H2. reflexivity.
unfold nextinstr. split. Unset Printing Notations.  rewrite -> Pregmap.gso.  rewrite -> Pregmap.gso. apply Pregmap.gscsc. assumption. auto. auto. reflexivity. Qed.

apply regs_are_different_resources in H, H0, H1.
(*solves Pmov*)
unfold exec_instr. apply inverse_outcome_equality. unfold nextinstr. split. Unset Printing Notations.  rewrite -> Pregmap.gso.  rewrite -> Pregmap.gso. apply Pregmap.gscsc. assumption. auto. auto. reflexivity. Qed.  *)
(* 
 unfold exec_instr. unfold goto_label. unfold exec_load.
  destruct (rs_i PC). destruct (label_pos lbl 0 (fn_code f)).
 destruct (Mem.loadv Mint32 m (eval_addressing g a rs)).  inversion H2.
 destruct (Mem.loadv Mint32 m_i (eval_addressing g a rs_i)). inversion H1. unfold nextinstr in H6, H8.
 destruct (label_pos lbl 0 (fn_code f)). destruct (rs_i PC); try discriminate. inversion H0. unfold nextinstr. rewrite -> H8. 
 
 destruct (rs_i @ rd <- v0 PC); try discriminate. contradiction. unfold eval_addressing in H1, H2. *)

Qed.