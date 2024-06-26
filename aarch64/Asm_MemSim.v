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
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Classical_Prop.
Import ListNotations.
Require Stacklayout.



Definition processor_id := Z.
Definition processor_reg := (processor_id * preg) % type.

Remark pr_eq:
  forall (r1 r2: processor_reg), {r1 = r2} + {r1 <> r2}.
Proof.
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

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [pair pid preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and condition bits to either [Vzero] or [Vone]. *)


(** Map of processor id + regcode to val for that processor*)
Definition allregsets := PRmap.t val.

(** Memory model*)
Definition mem_transaction_id := Z.

Remark tx_eq:
  forall (r1 r2: mem_transaction_id), {r1 = r2} + {r1 <> r2}.
Proof.
    apply Z.eq_dec.
Qed.

Module TrxEq.
  Definition t := mem_transaction_id.
  Definition eq := tx_eq.
End TrxEq. 

Module Trmap := EMap(TrxEq).

Definition early_write_id: Type := (processor_id * val * memory_chunk) % type.

Remark ew_eq:
  forall (r1 r2: early_write_id), {r1 = r2} + {r1 <> r2}.
Proof.
    intros. decide equality. apply chunk_eq. decide equality. apply Val.eq. apply Z.eq_dec. 
Qed.

Module EWEq.
  Definition t := early_write_id.
  Definition eq := ew_eq.
End EWEq.

Module EWmap := EMap(EWEq).

(* (Unenforced) convention: for writes, the first val is the ptr to the memory address, the second val is the value that is to be written, and the third val is the memory chunk*)
(*second val is initially arbitrary for reads, but later is serialized*)
Definition in_flight_mem_ops := Trmap.t (option (val* val * memory_chunk) % type).

(* map of (process id, val (unenforced convention: Vptr)) to value. Used to determine if that processor has a more recent early acked write than is serialized in mem*)
Definition early_ack_writes := EWmap.t (option (val)).




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
  | Pldrw (pid: processor_id) (txid: mem_transaction_id)                           (**r load int32 *)
  | Pldrw_a (pid: processor_id) (txid: mem_transaction_id)                         (**r load int32 as any32 *)
  | Pldrx (pid: processor_id) (txid: mem_transaction_id)                           (**r load int64 *)
  | Pldrx_a (pid: processor_id)  (txid: mem_transaction_id)                       (**r load int64 as any64 *)
  | Pldrb (sz: isize) (pid: processor_id) (txid: mem_transaction_id)              (**r load int8, zero-extend *)
  | Pldrsb (sz: isize) (pid: processor_id)  (txid: mem_transaction_id)            (**r load int8, sign-extend *)
  | Pldrh (sz: isize) (pid: processor_id)   (txid: mem_transaction_id)            (**r load int16, zero-extend *)
  | Pldrsh (sz: isize) (pid: processor_id) (txid: mem_transaction_id)             (**r load int16, sign-extend *)
  | Pldrzw (pid: processor_id) (txid: mem_transaction_id)                         (**r load int32, zero-extend to int64 *)
  | Pldrsw (pid: processor_id) (txid: mem_transaction_id)                         (**r load int32, sign-extend to int64 *)
  | Pldp (rd1 rd2: ireg) (pid: processor_id) (txid: mem_transaction_id)                        (**r load two int64 *)
  | Pstrw (a: addressing) (pid: processor_id) (txid: mem_transaction_id)                          (**r store int32 *)
  | Pstrw_a (a: addressing) (pid: processor_id) (txid: mem_transaction_id)                        (**r store int32 as any32 *)
  | Pstrx (a: addressing) (pid: processor_id) (txid: mem_transaction_id)                           (**r store int64 *)
  | Pstrx_a (a: addressing) (pid: processor_id) (txid: mem_transaction_id)                         (**r store int64 as any64 *)
  | Pstrb (a: addressing) (pid: processor_id) (txid: mem_transaction_id)                           (**r store int8 *)
  | Pstrh (a: addressing) (pid: processor_id) (txid: mem_transaction_id)                          (**r store int16 *)
  | Pstp (a: addressing) (pid: processor_id) (txid: mem_transaction_id)                       (**r store two int64 *)
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
  | Pldrs  (pid: processor_id) (txid: mem_transaction_id)                           (**r load float32 (single precision) *)
  | Pldrd  (pid: processor_id)  (txid: mem_transaction_id)                         (**r load float64 (double precision) *)
  | Pldrd_a  (pid: processor_id)  (txid: mem_transaction_id)                        (**r load float64 as any64 *)
  | Pstrs (a: addressing) (pid: processor_id)  (txid: mem_transaction_id)                         (**r store float32 *)
  | Pstrd  (a: addressing) (pid: processor_id) (txid: mem_transaction_id)                          (**r store float64 *)
  | Pstrd_a (a: addressing) (pid: processor_id) (txid: mem_transaction_id)                         (**r store float64 as any64 *)
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
  | Memfence (pid: processor_id) (** memory fence *)
  | EarlyAck (txid: mem_transaction_id) (pid: processor_id) (** Early write acknowledgement*)
  | WriteRequest (txid: mem_transaction_id) (pid: processor_id) (a: addressing) (r: preg) (c: memory_chunk) (** Serialize a transaction in memory*)
  | WriteAck (txid: mem_transaction_id) (pid: processor_id) (* Acknowledges memory serialization*)
  | ReadRequest (txid: mem_transaction_id) (pid: processor_id) (a: addressing) (c: memory_chunk)(* Requests value from memory*)
  | ReadAck (r:preg)(txid: mem_transaction_id) (pid: processor_id).


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
    | MemSimNext: allregsets -> mem -> in_flight_mem_ops -> early_ack_writes -> outcome
    | MemSimJumpOut: allregsets -> mem -> in_flight_mem_ops -> early_ack_writes -> outcome
    | MemSimStuck: outcome.


Definition goto_label (f: function) (lbl: label) (ars: allregsets) (pid: processor_id) (m: mem) (ifmo: in_flight_mem_ops) (eaw: early_ack_writes) :=
    match label_pos lbl 0 (fn_code f) with
    | None => MemSimStuck
    | Some pos =>
        match ars (pid, PC) with
        | Vptr b ofs => MemSimJumpOut (ars@(pid, PC ) <- (Vptr b (Ptrofs.repr pos))) m ifmo eaw
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

Definition read_request (a: addressing) (txid: mem_transaction_id)(ars: allregsets)(pid:processor_id)(ifmo: in_flight_mem_ops)(c: memory_chunk): in_flight_mem_ops :=
    Trmap.set txid (Some (eval_addressing a ars pid, Vundef, c)) ifmo.

(*represents the moment the fetched value is determined*)
Definition serialize_read (transf: val -> val) (txid: mem_transaction_id)
  (ars: allregsets) (pid: processor_id) (m: mem) (ifmo: in_flight_mem_ops) (eaw: early_ack_writes): outcome  :=
    (*Check if anything is in early write*)
    match ifmo txid with 
        | Some (address, _, chunk) => match eaw (pid, address, chunk) with 
            | Some v =>  MemSimNext ars m (Trmap.set txid (Some (address, (transf v), chunk)) ifmo) eaw
            (*If not, read from main memory*)
            | None => match Mem.loadv chunk m address with
                | None => MemSimStuck
                | Some v => MemSimNext ars m (Trmap.set txid (Some (address, (transf v), chunk)) ifmo) eaw
                end
        end
        | None => MemSimStuck
    end.

(*Writes fetched value into register*)
Definition read_ack (txid: mem_transaction_id) (ars:allregsets)(m:mem) (pid:processor_id) (eaw: early_ack_writes) (r: preg) (ifmo: in_flight_mem_ops) : outcome :=
    match ifmo txid with
    | Some (address, v, chunk) => MemSimNext (ars@(pid, r) <- v) m (Trmap.set txid None ifmo) eaw
    | None => MemSimStuck
    end.

Definition early_ack_write (txid: mem_transaction_id) (pid:processor_id) (eaw: early_ack_writes)(ifmo: in_flight_mem_ops) : early_ack_writes :=
    match ifmo txid with
    | Some (address, value, chunk) => EWmap.set (pid, address, chunk) (Some value) eaw
    | None => eaw (* Should not happen*)
    end.    

Definition write_request  (a: addressing) (v: val) (txid: mem_transaction_id)
(ars: allregsets) (pid: processor_id) (ifmo: in_flight_mem_ops)(chunk: memory_chunk) : in_flight_mem_ops :=
    Trmap.set txid (Some (eval_addressing a ars pid, v, chunk)) ifmo.     


(*Used for write serialization*)
(*Also removes early write acks*)
Definition serialize_write
    (txid: mem_transaction_id)
    (ars: allregsets) (pid: processor_id) (m: mem) (ifmo: in_flight_mem_ops) (eaw: early_ack_writes) :=
    match ifmo txid with
    | Some (a, v, c) => match Mem.storev c m a v with
        | None => MemSimStuck
        | Some m' => MemSimNext ars m' ifmo (EWmap.set (pid,a, c) None eaw)
        end
    | None => MemSimStuck
end.

Definition write_ack (txid: mem_transaction_id) (pid:processor_id) (ifmo: in_flight_mem_ops) : in_flight_mem_ops :=
    Trmap.set txid None ifmo.

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

Definition eval_memsim_instr_internal (f: function)(i: instruction)(ars: allregsets) (m: mem)  (ifo: in_flight_mem_ops) (eaw: early_ack_writes): outcome:=
    match i with 
    | Pb lbl pid =>
            goto_label f lbl ars pid m ifo eaw
        | Pbc cond lbl pid =>
            match eval_testcond cond ars pid with
            | Some true => goto_label f lbl ars pid m ifo eaw
            | Some false => MemSimNext ars m ifo eaw
            | None => MemSimStuck
            end
        | Pbl id sg pid =>
            MemSimNext (ars@ (pid, RA)  <- (Val.offset_ptr ars@ (pid, PC)  Ptrofs.one) @ (pid, PC) <- (Genv.symbol_address ge id Ptrofs.zero)) m ifo eaw
        | Pbs id sg pid =>
            MemSimNext (ars@ (pid , PC)  <- (Genv.symbol_address ge id Ptrofs.zero)) m ifo eaw
        | Pblr r sg pid =>
        MemSimNext (ars@ (pid , RA)  <- (Val.offset_ptr ars@ (pid , PC)  Ptrofs.one) @ (pid, PC) <- (ars@ (pid , r)) ) m ifo eaw
        | Pbr r sg pid =>
            MemSimNext (ars@ (pid , PC)  <- (ars@ (pid, r)) ) m ifo eaw
        | Pret r pid =>
            MemSimNext (ars@ (pid , PC)  <- (ars@ (pid, r)) ) m ifo eaw
        | Pcbnz sz r lbl pid =>
            match eval_testzero sz ars@ (pid, r) m with
            | Some true => MemSimNext ars m ifo eaw
            | Some false => goto_label f lbl ars pid m ifo eaw
            | None => MemSimStuck
            end
        | Pcbz sz r lbl pid =>
            match eval_testzero sz ars@ (pid, r ) m with
            | Some true => goto_label f lbl ars pid m ifo eaw
            | Some false => MemSimNext ars m ifo eaw
            | None => MemSimStuck
            end
        | Ptbnz sz r n lbl pid =>
            match eval_testbit sz ars@ (pid, r ) n with
            | Some true => goto_label f lbl ars pid m ifo eaw
            | Some false => MemSimNext ars m ifo eaw
            | None => MemSimStuck
            end
        | Ptbz sz r n lbl pid =>
            match eval_testbit sz ars@ (pid, r ) n with
            | Some true => MemSimNext ars m ifo eaw
            | Some false => goto_label f lbl ars pid m ifo eaw
            | None => MemSimStuck
            end
        (** Memory loads and stores *)
        | Pldrw pid txid =>
            serialize_read (fun v => v) txid ars pid m ifo eaw
        | Pldrw_a pid txid =>
            serialize_read (fun v => v) txid ars pid m ifo eaw
        | Pldrx pid txid =>
            serialize_read (fun v => v) txid ars pid m ifo eaw
        | Pldrx_a pid txid =>
            serialize_read (fun v => v) txid ars pid m ifo eaw
        | Pldrb W pid txid =>
            serialize_read (fun v => v) txid ars pid m ifo eaw
        | Pldrb X pid txid =>
            serialize_read Val.longofintu txid ars pid m ifo eaw
        | Pldrsb W pid txid =>
            serialize_read (fun v => v) txid ars pid m ifo eaw
        | Pldrsb X pid txid =>
            serialize_read Val.longofint txid ars pid m ifo eaw
        | Pldrh W pid txid =>
            serialize_read (fun v => v) txid ars pid m ifo eaw
        | Pldrh X pid txid =>
            serialize_read (Val.longofintu) txid ars pid m ifo eaw
        | Pldrsh W pid txid =>
            serialize_read (fun v => v) txid ars pid m ifo eaw
        | Pldrsh X pid txid =>
            serialize_read (Val.longofint) txid ars pid m ifo eaw
        | Pldrzw pid txid =>
            serialize_read (Val.longofintu) txid ars pid m ifo eaw
        | Pldrsw pid txid =>
            serialize_read (Val.longofint) txid ars pid m ifo eaw
        | Pstrw a pid txid =>
            serialize_write txid ars pid m ifo eaw
        | Pstrw_a a pid txid =>
            serialize_write txid ars pid m ifo eaw
        | Pstrx a pid txid =>
            serialize_write txid ars pid m ifo eaw
        | Pstrx_a a pid txid =>
            serialize_write txid ars pid m ifo eaw
        | Pstrb a pid txid =>
            serialize_write txid ars pid m ifo eaw
        | Pstrh a pid txid =>
            serialize_write txid ars pid m ifo eaw
        (** Integer arithmetic, immediate *)
        | Paddimm W rd r1 n pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.add ars@ (pid, r1)  (Vint (Int.repr n))))) m ifo eaw
        | Paddimm X rd r1 n pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.addl ars@ (pid, r1)  (Vlong (Int64.repr n))))) m ifo eaw
        | Psubimm W rd r1 n pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.sub ars@ (pid, r1)  (Vint (Int.repr n))))) m ifo eaw
        | Psubimm X rd r1 n pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.subl ars@ (pid, r1)  (Vlong (Int64.repr n))))) m ifo eaw
        | Pcmpimm W r1 n pid =>
            MemSimNext ((compare_int ars ars@(pid, r1)  (Vint (Int.repr n)) m) pid ) m ifo eaw
        | Pcmpimm X r1 n pid =>
            MemSimNext ((compare_long ars ars@ (pid, r1)  (Vlong (Int64.repr n)) m) pid ) m ifo eaw
        | Pcmnimm W r1 n pid =>
            MemSimNext ((compare_int ars ars@ (pid, r1)  (Vint (Int.neg (Int.repr n))) m) pid) m ifo eaw
        | Pcmnimm X r1 n pid =>
            MemSimNext ((compare_long ars ars@ (pid, r1)  (Vlong (Int64.neg (Int64.repr n))) m) pid) m ifo eaw
        (** Move integer register *)
        | Pmov rd r1 pid =>
            MemSimNext ( (ars@ (pid, rd)  <- (ars@ (pid, r1) ))) m ifo eaw
        (** Logical, immediate *)
        | Pandimm W rd r1 n pid =>
            MemSimNext ((ars@(pid, rd)  <- (Val.and (ars@@ pid @@> r1) (Vint (Int.repr n))))) m ifo eaw
        | Pandimm X rd r1 n pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.andl (ars@@@ pid @@@> r1) (Vlong (Int64.repr n))))) m ifo eaw
        | Peorimm W rd r1 n pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.xor (ars@@ pid @@> r1)  (Vint (Int.repr n))))) m ifo eaw
        | Peorimm X rd r1 n pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.xorl (ars@@@ pid @@@> r1) (Vlong (Int64.repr n))))) m ifo eaw
        | Porrimm W rd r1 n pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.or (ars@@ pid @@> r1) (Vint (Int.repr n))))) m ifo eaw
        | Porrimm X rd r1 n pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.orl (ars@@@ pid @@@> r1) (Vlong (Int64.repr n))))) m ifo eaw
        | Ptstimm W r1 n pid =>
            MemSimNext (compare_int ars (Val.and ars@ (pid, r1)  (Vint (Int.repr n))) (Vint Int.zero) m pid) m ifo eaw
        | Ptstimm X r1 n pid =>
            MemSimNext ((compare_long ars (Val.andl ars@ (pid, r1)  (Vlong (Int64.repr n))) (Vlong Int64.zero) m pid)) m ifo eaw
        (** Move wide immediate *)
        | Pmovz W rd n pos pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Vint (Int.repr (Z.shiftl n pos))))) m ifo eaw
        | Pmovz X rd n pos pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Vlong (Int64.repr (Z.shiftl n pos))))) m ifo eaw
        | Pmovn W rd n pos pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Vint (Int.repr (Z.lnot (Z.shiftl n pos)))))) m ifo eaw
        | Pmovn X rd n pos pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Vlong (Int64.repr (Z.lnot (Z.shiftl n pos)))))) m ifo eaw
        | Pmovk W rd n pos pid =>
            MemSimNext ((ars@ (pid, rd)  <- (insert_in_int ars@ (pid, rd)  n pos 16))) m ifo eaw
        | Pmovk X rd n pos pid =>
            MemSimNext ((ars@ (pid, rd)  <- (insert_in_long ars@ (pid, rd)  n pos 16))) m ifo eaw
        (** PC-relative addressing *)
        | Padrp rd id ofs pid =>
            MemSimNext ((ars@ (pid, rd)  <- (symbol_high ge id ofs))) m ifo eaw
        | Paddadr rd r1 id ofs pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.addl ars@ (pid, r1)  (symbol_low ge id ofs)))) m  ifo eaw
        (** Bit-field operations *)
        | Psbfiz W rd r1 r s pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.shl (Val.sign_ext s ars@ (pid, r1) ) (Vint r)))) m ifo eaw
        | Psbfiz X rd r1 r s pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.shll (Val.sign_ext_l s ars@ (pid, r1) ) (Vint r)))) m ifo eaw
        | Psbfx W rd r1 r s pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.sign_ext s (Val.shr ars@ (pid, r1)  (Vint r))))) m ifo eaw
        | Psbfx X rd r1 r s pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.sign_ext_l s (Val.shrl ars@ (pid, r1)  (Vint r))))) m ifo eaw
        | Pubfiz W rd r1 r s pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.shl (Val.zero_ext s ars@ (pid, r1) ) (Vint r)))) m ifo eaw
        | Pubfiz X rd r1 r s pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.shll (Val.zero_ext_l s ars@ (pid, r1) ) (Vint r)))) m ifo eaw
        | Pubfx W rd r1 r s pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.zero_ext s (Val.shru ars@ (pid, r1)  (Vint r))))) m ifo eaw
        | Pubfx X rd r1 r s pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.zero_ext_l s (Val.shrlu ars@ (pid, r1)  (Vint r))))) m ifo eaw
        (** Integer arithmetic, shifted register *)
        | Padd W rd r1 r2 s pid =>
            MemSimNext (ars@ (pid, rd)  <- (Val.add ars@@ pid @@> r1 (eval_shift_op_int ars@ (pid, r2)  s))) m ifo eaw
        | Padd X rd r1 r2 s pid =>
            MemSimNext (ars@ (pid, rd)  <- (Val.addl ars@@@pid @@@> r1 (eval_shift_op_long ars@ (pid, r2)  s))) m ifo eaw
        | Psub W rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.sub ars@@pid @@> r1 (eval_shift_op_int ars@ (pid, r2)  s)))) m ifo eaw
        | Psub X rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.subl ars@@@ pid@@@> r1 (eval_shift_op_long ars@ (pid, r2)  s)))) m ifo eaw
        | Pcmp W r1 r2 s pid =>
            MemSimNext (compare_int ars (ars@@pid@@>r1) (eval_shift_op_int ars@(pid, r2)  s) m pid) m ifo eaw
        | Pcmp X r1 r2 s pid =>
            MemSimNext ((compare_long ars ars@@@pid@@@>r1) (eval_shift_op_long ars@ (pid, r2)  s) m pid) m ifo eaw
        | Pcmn W r1 r2 s pid =>
            MemSimNext (compare_int ars ars@@pid@@>r1 (Val.neg (eval_shift_op_int ars@ (pid, r2)  s)) m pid) m ifo eaw
        | Pcmn X r1 r2 s pid =>
            MemSimNext ((compare_long ars ars@@@pid@@@>r1 (Val.negl (eval_shift_op_long ars@ (pid, r2)  s)) m pid)) m ifo eaw
        (** Integer arithmetic, extending register *)
        | Paddext rd r1 r2 x pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.addl ars@ (pid, r1)  (eval_extend ars@ (pid, r2)  x)))) m ifo eaw
        | Psubext rd r1 r2 x pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.subl ars@ (pid, r1)  (eval_extend ars@ (pid, r2)  x)))) m ifo eaw
        | Pcmpext r1 r2 x pid =>
            MemSimNext ((compare_long ars ars@ (pid, r1)  (eval_extend ars@ (pid, r2)  x) m pid)) m ifo eaw
        | Pcmnext r1 r2 x pid =>
            MemSimNext ((compare_long ars ars@ (pid, r1)  (Val.negl (eval_extend ars@ (pid, r2)  x)) m pid)) m ifo eaw
        (** Logical, shifted register *)
        | Pand W rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.and ars@@pid@@>r1 (eval_shift_op_int ars@ (pid , r2)  s)))) m ifo eaw
        | Pand X rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.andl ars@@@pid@@@>r1 (eval_shift_op_long ars@ (pid , r2)  s)))) m ifo eaw
        | Pbic W rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.and ars@@pid@@>r1 (Val.notint (eval_shift_op_int ars@ (pid , r2)  s))))) m ifo eaw
        | Pbic X rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.andl ars@@@pid@@@>r1 (Val.notl (eval_shift_op_long ars@ (pid , r2)  s))))) m ifo eaw
        | Peon W rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.xor ars@@pid@@>r1 (Val.notint (eval_shift_op_int ars@ (pid , r2)  s))))) m ifo eaw
        | Peon X rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.xorl ars@@@pid@@@>r1 (Val.notl (eval_shift_op_long ars@ (pid , r2)  s))))) m ifo eaw
        | Peor W rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.xor ars@@pid@@>r1 (eval_shift_op_int ars@ (pid , r2)  s)))) m ifo eaw
        | Peor X rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.xorl ars@@@pid@@@>r1 (eval_shift_op_long ars@ (pid , r2)  s)))) m ifo eaw
        | Porr W rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.or ars@@pid@@>r1 (eval_shift_op_int ars@ (pid , r2)  s)))) m ifo eaw
        | Porr X rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.orl ars@@@pid@@@>r1 (eval_shift_op_long ars@ (pid , r2)  s)))) m ifo eaw
        | Porn W rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.or ars@@pid@@>r1 (Val.notint (eval_shift_op_int ars@ (pid , r2)  s))))) m ifo eaw
        | Porn X rd r1 r2 s pid =>
            MemSimNext ((ars@ (pid , rd)  <- (Val.orl ars@@@pid@@@>r1 (Val.notl (eval_shift_op_long ars@ (pid , r2)  s))))) m ifo eaw
        | Ptst W r1 r2 s pid =>
            MemSimNext ((compare_int ars (Val.and ars@@pid@@>r1 (eval_shift_op_int ars@ (pid , r2)  s)) (Vint Int.zero) m pid)) m ifo eaw
        | Ptst X r1 r2 s pid =>
            MemSimNext ((compare_long ars (Val.andl ars@@@pid@@@>r1 (eval_shift_op_long ars@ (pid , r2)  s)) (Vlong Int64.zero) m pid)) m ifo eaw
        (*** Variable shifts *)
        | Pasrv W rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.shr ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Pasrv X rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.shrl ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Plslv W rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.shl ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Plslv X rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.shll ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Plsrv W rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.shru ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Plsrv X rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.shrlu ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Prorv W rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.ror ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Prorv X rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.rorl ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        (** Conditional data processing *)
        | Pcsel rd r1 r2 cond pid =>
            let v :=
                match eval_testcond cond ars pid with
                | Some true => ars@ (pid, r1) 
                | Some false => ars@ (pid, r2) 
                | None => Vundef
                end in
            MemSimNext ((ars@ (pid, rd)  <- v)) m ifo eaw
        | Pcset rd cond pid =>
            let v :=
                match eval_testcond cond ars pid with
                | Some true => Vint Int.one
                | Some false => Vint Int.zero
                | None => Vundef
                end in
            MemSimNext ((ars@ (pid, rd)  <- v)) m ifo eaw
        (** Integer multiply/divide *)
        | Pmadd W rd r1 r2 r3 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.add ars@@pid@@>r3 (Val.mul ars@ (pid, r1)  ars@ (pid, r2) )))) m ifo eaw
        | Pmadd X rd r1 r2 r3 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.addl ars@@@pid@@@>r3 (Val.mull ars@ (pid, r1)  ars@ (pid, r2) )))) m ifo eaw
        | Pmsub W rd r1 r2 r3 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.sub ars@@pid@@>r3 (Val.mul ars@ (pid, r1)  ars@ (pid, r2) )))) m ifo eaw
        | Pmsub X rd r1 r2 r3 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.subl ars@@@pid@@@>r3 (Val.mull ars@ (pid, r1)  ars@ (pid, r2) )))) m ifo eaw
        | Psmulh rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.mullhs ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Pumulh rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.mullhu ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Psdiv W rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.divs ars@ (pid, r1)  ars@ (pid, r2) )))) m ifo eaw
        | Psdiv X rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.divls ars@ (pid, r1)  ars@ (pid, r2) )))) m ifo eaw
        | Pudiv W rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.divu ars@ (pid, r1)  ars@ (pid, r2) )))) m ifo eaw
        | Pudiv X rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.divlu ars@ (pid, r1)  ars@ (pid, r2) )))) m ifo eaw
        (** Floating-point loads and stores *)
        | Pldrs pid txid =>
            serialize_read (fun v => v) txid ars pid m ifo eaw
        | Pldrd pid txid =>
            serialize_read (fun v => v) txid ars pid m ifo eaw
        | Pldrd_a pid txid =>
            serialize_read (fun v => v) txid ars pid m ifo eaw
        | Pstrs a pid txid =>
            serialize_write txid ars pid m ifo eaw
        | Pstrd a pid txid =>
            serialize_write txid ars pid m ifo eaw
        | Pstrd_a a pid txid =>
            serialize_write txid ars pid m ifo eaw
        (** Floating-point move *)
        | Pfmov rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (ars@ (pid, r1) ))) m  ifo eaw
        | Pfmovimms rd f pid =>
            MemSimNext ((ars@ (pid, X16) <- Vundef @(pid, rd) <- (Vsingle f))) m ifo eaw
        | Pfmovimmd rd f pid =>
            MemSimNext ((ars@ (pid, X16) <- Vundef @(pid, rd) <- (Vfloat f))) m ifo eaw
        | Pfmovi S rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (float32_of_bits ars@@pid@@>r1))) m ifo eaw
        | Pfmovi D rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (float64_of_bits ars@@@pid@@@>r1))) m ifo eaw
        (** Floating-point conversions *)
        | Pfcvtds rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.floatofsingle ars@ (pid, r1) ))) m ifo eaw
        | Pfcvtsd rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.singleoffloat ars@ (pid, r1) ))) m ifo eaw
        | Pfcvtzs W S rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.intofsingle ars@ (pid, r1) )))) m ifo eaw
        | Pfcvtzs W D rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.intoffloat ars@ (pid, r1) )))) m ifo eaw
        | Pfcvtzs X S rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.longofsingle ars@ (pid, r1) )))) m ifo eaw
        | Pfcvtzs X D rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.longoffloat ars@ (pid, r1) )))) m ifo eaw
        | Pfcvtzu W S rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.intuofsingle ars@ (pid, r1) )))) m ifo eaw
        | Pfcvtzu W D rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.intuoffloat ars@ (pid, r1) )))) m ifo eaw
        | Pfcvtzu X S rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.longuofsingle ars@ (pid, r1) )))) m ifo eaw
        | Pfcvtzu X D rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.longuoffloat ars@ (pid, r1) )))) m ifo eaw
        | Pscvtf S W rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.singleofint ars@ (pid, r1) )))) m ifo eaw
        | Pscvtf D W rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.floatofint ars@ (pid, r1) )))) m ifo eaw
        | Pscvtf S X rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.singleoflong ars@ (pid, r1) )))) m ifo eaw
        | Pscvtf D X rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.floatoflong ars@ (pid, r1) )))) m ifo eaw
        | Pucvtf S W rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.singleofintu ars@ (pid, r1) )))) m ifo eaw
        | Pucvtf D W rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.floatofintu ars@ (pid, r1) )))) m ifo eaw
        | Pucvtf S X rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.singleoflongu ars@ (pid, r1) )))) m ifo eaw
        | Pucvtf D X rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.maketotal (Val.floatoflongu ars@ (pid, r1) )))) m ifo eaw
        (** Floating-point arithmetic *)
        | Pfabs S rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.absfs ars@ (pid, r1) ))) m ifo eaw
        | Pfabs D rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.absf ars@ (pid, r1) ))) m ifo eaw
        | Pfneg S rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.negfs ars@ (pid, r1) ))) m ifo eaw
        | Pfneg D rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.negf ars@ (pid, r1) ))) m ifo eaw
        | Pfadd S rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.addfs ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Pfadd D rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.addf ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Pfdiv S rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.divfs ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Pfdiv D rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.divf ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Pfmul S rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.mulfs ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Pfmul D rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.mulf ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Pfnmul S rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.negfs (Val.mulfs ars@ (pid, r1)  ars@ (pid, r2) )))) m ifo eaw
        | Pfnmul D rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.negf (Val.mulf ars@ (pid, r1)  ars@ (pid, r2) )))) m ifo eaw
        | Pfsub S rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.subfs ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        | Pfsub D rd r1 r2 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.subf ars@ (pid, r1)  ars@ (pid, r2) ))) m ifo eaw
        (** Floating-point comparison *)
        | Pfcmp S r1 r2 pid =>
            MemSimNext ((compare_single ars ars@ (pid, r1)  ars@ (pid, r2) pid )) m ifo eaw
        | Pfcmp D r1 r2 pid =>
            MemSimNext ((compare_float ars ars@ (pid, r1)  ars@ (pid, r2) pid )) m ifo eaw
        | Pfcmp0 S r1 pid =>
            MemSimNext ((compare_single ars ars@ (pid, r1)  (Vsingle Float32.zero) pid)) m ifo eaw
        | Pfcmp0 D r1 pid =>
            MemSimNext ((compare_float ars ars@ (pid, r1)  (Vfloat Float.zero) pid)) m ifo eaw
        (** Floating-point conditional select *)
        | Pfsel rd r1 r2 cond pid =>
            let v :=
                match eval_testcond cond ars pid with
                | Some true => ars@ (pid, r1) 
                | Some false => ars@ (pid, r2) 
                | None => Vundef
                end in
            MemSimNext ((ars@ (pid, rd)  <- v)) m ifo eaw
        (** Pseudo-instructions *)
        | Pallocframe sz pos pid =>
            let (m1, stk) := Mem.alloc m 0 sz in
            let sp := (Vptr stk Ptrofs.zero) in
            match Mem.storev Mint64 m1 (Val.offset_ptr sp pos) ars@ (pid, SP)  with
            | None => MemSimStuck
            | Some m2 => MemSimNext ((ars @ (pid, X15) <- (ars@ (pid, SP) ) @(pid, SP) <- sp @(pid, X16) <- Vundef)) m2  ifo eaw
            end
        | Pfreeframe sz pos pid =>
            match Mem.loadv Mint64 m (Val.offset_ptr ars@ (pid, SP)  pos) with
            | None => MemSimStuck
            | Some v =>
                match ars@ (pid, SP)  with
                | Vptr stk ofs =>
                    match Mem.free m stk 0 sz with
                    | None => MemSimStuck
                    | Some m' => MemSimNext ((ars@ (pid, SP)  <- v @(pid, X16) <- Vundef)) m'  ifo eaw
                    end
                | _ => MemSimStuck
                end
            end
        | Plabel lbl pid =>
            MemSimNext ars m  ifo eaw
        | Ploadsymbol rd id pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Genv.symbol_address ge id Ptrofs.zero))) m ifo eaw
        | Pcvtsw2x rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.longofint ars@ (pid, r1) ))) m ifo eaw
        | Pcvtuw2x rd r1 pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.longofintu ars@ (pid, r1) ))) m ifo eaw
        | Pcvtx2w rd pid =>
            MemSimNext ((ars@ (pid, rd)  <- (Val.loword ars@ (pid, rd) ))) m ifo eaw
        | Pbtbl r tbl pid =>
            match (ars@ (pid, X16)  <- Vundef)@(pid, r) with
            | Vint n =>
                match list_nth_z tbl (Int.unsigned n) with
                | None => MemSimStuck
                | Some lbl => goto_label f lbl (ars@ (pid, X16) <- Vundef) pid m ifo eaw
                end
            | _ => MemSimStuck
            end
        | Pcfi_rel_offset _ pid =>
            MemSimNext ars m ifo eaw
        | Pbuiltin ef args res pid => MemSimStuck    (**r treated specially below *)
        (** The following instructions and directives are not generated directly
            by Asmgen, so we do not model them. *)
        | Pldp _ _ _ _ => MemSimStuck
        | Pstp _ _  _ => MemSimStuck
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
        | Pincpc pid => MemSimNext (ars@(pid, PC) <- (Val.offset_ptr ars@(pid,PC) Ptrofs.one)) m ifo eaw
        | Pcfi_adjust _ _ =>
            MemSimStuck
        | Memfence _ => MemSimNext ars m ifo eaw
        | EarlyAck txid pid =>
            MemSimNext ars m ifo (early_ack_write txid pid eaw ifo)
        | WriteRequest txid pid a r c =>
            MemSimNext ars m (Trmap.set txid (Some (eval_addressing a ars pid, ars@ (pid, r), c)) ifo ) eaw
        | WriteAck txid pid =>
            MemSimNext ars m (write_ack txid pid ifo) eaw
        | ReadRequest txid pid a c =>
            MemSimNext ars m (read_request a txid ars pid ifo c) eaw
        | ReadAck r txid pid =>
            read_ack txid ars m pid eaw r ifo
    end.

Definition eval_memsim_instr (f: function) (i: instruction) (o: outcome): outcome :=
match o with 
    | MemSimNext ars m ifo eaw => eval_memsim_instr_internal f i ars m ifo eaw
    | MemSimJumpOut ars m ifo eaw => eval_memsim_instr_internal f i ars m ifo eaw
    | MemSimStuck => MemSimStuck    
end.

End RELSEM.






(** asm to mem sim - turns ISA into a series of memsim semantics*)
(** separates most operations into the actual operation and incrementing the PC - this lets us reorder more easily since we 
dont update the PC in every operation*)
(** Memory accesses are split into multiple stages *)

Definition translate_write(asm_i: Asm.instruction)(pid: processor_id)(txid: mem_transaction_id): list instruction :=
    match asm_i with 
    | Asm.Pstrd_a r a => ([WriteRequest txid pid a r Many64; Pstrd_a a pid txid; WriteAck txid pid; Pincpc pid])                               (**r store float64 *)
    | Asm.Pstrd r a => ([WriteRequest txid pid a r Mfloat64; Pstrd a pid txid; WriteAck txid pid; Pincpc pid])                               (**r store float64 *)
    | Asm.Pstrw r a => ([WriteRequest txid pid a r Mint32; Pstrw a pid txid; WriteAck txid pid; Pincpc pid ])                               (**r store int32 *)
    | Asm.Pstrw_a r a => ([WriteRequest txid pid a r Many32; Pstrw_a a pid txid; WriteAck txid pid; Pincpc pid] )                            (**r store int32 as any32 *)
    | Asm.Pstrx r a => ([WriteRequest txid pid a r Mint64; Pstrx a pid txid;  WriteAck txid pid; Pincpc pid] )                                (**r store int64 *)
    | Asm.Pstrx_a r a => ([WriteRequest txid pid a r Many64; Pstrx_a a pid txid;  WriteAck txid pid; Pincpc pid ])                             (**r store int64 as any64 *)
    | Asm.Pstrb r a => ([WriteRequest txid pid a r Mint8unsigned; Pstrb a pid txid;  WriteAck txid pid; Pincpc pid ])                                  (**r store int8 *)
    | Asm.Pstrh r a => ([WriteRequest txid pid a r Mint16unsigned; Pstrh a pid txid;  WriteAck txid pid; Pincpc pid])                                (**r store int16 *)
    | Asm.Pstrs r a => ([WriteRequest txid pid a r Mfloat32; Pstrs a pid txid;  WriteAck txid pid; Pincpc pid]) 
    | _ => []
    end.

(** translates loads/stores into memory dispatches and acknowledgements*)
(** Takes in a processor id*)
Definition asm_to_memsim (asm_i: Asm.instruction) (pid: processor_id)(txid: mem_transaction_id): list instruction := 
    match asm_i with 
    | Asm.Pb lbl    => ([Pb lbl pid])                                               (**r branch *)
    | Asm.Pbc c lbl  => ([Pbc c lbl pid; Pincpc pid])                             (**r conditional branch *)
    | Asm.Pbl id sg  => ([Pbl id sg pid])                             (**r jump to function and link *)
    | Asm.Pbs id sg => ([Pbs id sg pid])                                  (**r jump to function *)
    | Asm.Pblr r sg => ([Pblr r sg pid])        
    | Asm.Pbr r sg => ([Pbr r sg pid])                                   (**r indirect jump *)
    | Asm.Pret r => ([Pret r pid])                                        (**r return *)
    | Asm.Pcbnz sz r lbl => ([Pcbnz sz r lbl pid; Pincpc pid])                       (**r branch if not zero *)
    | Asm.Pcbz sz r lbl => ([Pcbz sz r lbl pid; Pincpc pid])                         (**r branch if zero *)
    | Asm.Ptbnz sz r n lbl => ([Ptbnz sz r n lbl pid; Pincpc pid])                   (**r branch if bit n is not zero *)
    | Asm.Ptbz sz r n lbl => ([Ptbz sz r n lbl pid; Pincpc pid])                     (**r branch if bit n is zero *)
    | Asm.Pldrw rd a => ([ReadRequest txid pid a Mint32; Pldrw pid txid; ReadAck rd txid pid; Pincpc pid])                               (**r load int32 *)
    | Asm.Pldrw_a rd a => ([ReadRequest txid pid a Many32; Pldrw_a pid txid; ReadAck rd txid pid; Pincpc pid])                           (**r load int32 as any32 *)
    | Asm.Pldrx rd a => ([ReadRequest txid pid a Mint64; Pldrx pid txid; ReadAck rd txid pid; Pincpc pid])                               (**r load int64 *)
    | Asm.Pldrx_a rd a => ([ReadRequest txid pid a Many64; Pldrx_a pid txid; ReadAck rd txid pid; Pincpc pid])                           (**r load int64 as any64 *)
    | Asm.Pldrb sz rd a => ([ReadRequest txid pid a Mint8unsigned; Pldrb sz pid txid; ReadAck rd txid pid; Pincpc pid])                         (**r load int8, zero-extend *)
    | Asm.Pldrsb sz rd a => ([ReadRequest txid pid a Mint8signed; Pldrsb sz pid txid; ReadAck rd txid pid; Pincpc pid])                       (**r load int8, sign-extend *)
    | Asm.Pldrh sz rd a => ([ReadRequest txid pid a Mint16unsigned; Pldrh sz pid txid; ReadAck rd txid pid; Pincpc pid])                         (**r load int16, zero-extend *)
    | Asm.Pldrsh sz rd a => ([ReadRequest txid pid a Mint16signed; Pldrsh sz pid txid; ReadAck rd txid pid; Pincpc pid])                       (**r load int16, sign-extend *)
    | Asm.Pldrzw rd a => ([ReadRequest txid pid a Mint32; Pldrzw pid txid; ReadAck rd txid pid; Pincpc pid])                             (**r load int32, zero-extend to int64 *)
    | Asm.Pldrsw rd a => ([ReadRequest txid pid a Mint32; Pldrsw pid txid; ReadAck rd txid pid; Pincpc pid])                             (**r load int32, sign-extend to int64 *)
    | Asm.Pldp rd1 rd2 a => ([Pldp rd1 rd2 pid txid])                        (**r load two int64 - not generated by compcert*)
    | Asm.Pstrw rs a => translate_write asm_i pid txid                             (**r store int32 *)
    | Asm.Pstrw_a rs a => translate_write asm_i pid txid                         (**r store int32 as any32 *)
    | Asm.Pstrx rs a => translate_write asm_i pid txid                           (**r store int64 *)
    | Asm.Pstrx_a rs a => translate_write asm_i pid  txid                        (**r store int64 as any64 *)
    | Asm.Pstrb rs a => translate_write asm_i pid txid                            (**r store int8 *)
    | Asm.Pstrh rs a => translate_write asm_i pid txid                           (**r store int16 *)
    | Asm.Pstp rs1 rs2 a => [Pstp a pid txid; Pincpc pid]                                                  (**r store two int64 - NOT MODELED BY COMPCERT *)
    | Asm.Paddimm sz rd r1 n => ([Paddimm sz rd r1 n pid; Pincpc pid])               (**r addition *)
    | Asm.Psubimm sz rd r1 n => ([Psubimm sz rd r1 n pid; Pincpc pid])               (**r subtraction *)
    | Asm.Pcmpimm sz r1 n => ([Pcmpimm sz r1 n pid; Pincpc pid])                     (**r compare *)
    | Asm.Pcmnimm sz r1 n => ([Pcmnimm sz r1 n pid; Pincpc pid])                     (**r compare negative *)
    | Asm.Pmov rd r1 => ([Pmov rd r1 pid; Pincpc pid])                               (**r move integer register *)
    | Asm.Pandimm sz rd r1 n => ([Pandimm sz rd r1 n pid; Pincpc pid])               (**r and *)
    | Asm.Peorimm sz rd r1 n => ([Peorimm sz rd r1 n pid; Pincpc pid])               (**r xor *)
    | Asm.Porrimm sz rd r1 n => ([Porrimm sz rd r1 n pid; Pincpc pid])               (**r or *)
    | Asm.Ptstimm sz r1 n => ([Ptstimm sz r1 n pid; Pincpc pid])                     (**r and, then set flags *)
    | Asm.Pmovz sz rd n pos => ([Pmovz sz rd n pos pid; Pincpc pid])                 (**r move wide immediate *)
    | Asm.Pmovn sz rd n pos => ([Pmovn sz rd n pos pid; Pincpc pid])
    | Asm.Pmovk sz rd n pos => ([Pmovk sz rd n pos pid; Pincpc pid])
    | Asm.Padrp rd id ofs => ([Padrp rd id ofs pid; Pincpc pid])                     (**r PC-relative addressing *)
    | Asm.Paddadr rd r1 id ofs => ([Paddadr rd r1 id ofs pid; Pincpc pid])
    | Asm.Psbfiz sz rd r1 r s => ([Psbfiz sz rd r1 r s pid; Pincpc pid])              (**r Bit-field operations *)
    | Asm.Psbfx sz rd r1 r s => ([Psbfx sz rd r1 r s pid; Pincpc pid])
    | Asm.Pubfiz sz rd r1 r s => ([Pubfiz sz rd r1 r s pid; Pincpc pid])
    | Asm.Pubfx sz rd r1 r s => ([Pubfx sz rd r1 r s pid; Pincpc pid])
    | Asm.Padd sz rd r1 r2 s => ([Padd sz rd r1 r2 s pid; Pincpc pid])                (**r Integer arithmetic, shifted register *)
    | Asm.Psub sz rd r1 r2 s => ([Psub sz rd r1 r2 s pid; Pincpc pid])
    | Asm.Pcmp sz r1 r2 s => ([Pcmp sz r1 r2 s pid; Pincpc pid])
    | Asm.Pcmn sz r1 r2 s => ([Pcmn sz r1 r2 s pid; Pincpc pid])
    | Asm.Paddext rd r1 r2 x => ([Paddext rd r1 r2 x pid; Pincpc pid])                (**r Integer arithmetic, extending register *)
    | Asm.Psubext rd r1 r2 x => ([Psubext rd r1 r2 x pid; Pincpc pid])
    | Asm.Pcmpext r1 r2 x => ([Pcmpext r1 r2 x pid; Pincpc pid])
    | Asm.Pcmnext r1 r2 x => ([Pcmnext r1 r2 x pid; Pincpc pid])
    | Asm.Pand sz rd r1 r2 s => ([Pand sz rd r1 r2 s pid; Pincpc pid])                (**r Logical, shifted register *)
    | Asm.Pbic sz rd r1 r2 s => ([Pbic sz rd r1 r2 s pid; Pincpc pid])
    | Asm.Peon sz rd r1 r2 s => ([Peon sz rd r1 r2 s pid; Pincpc pid])
    | Asm.Peor sz rd r1 r2 s => ([Peor sz rd r1 r2 s pid; Pincpc pid])
    | Asm.Porr sz rd r1 r2 s => ([Porr sz rd r1 r2 s pid; Pincpc pid])
    | Asm.Porn sz rd r1 r2 s => ([Porn sz rd r1 r2 s pid; Pincpc pid])
    | Asm.Ptst sz r1 r2 s => ([Ptst sz r1 r2 s pid; Pincpc pid])                      (**r and, then set flags *)
    | Asm.Pasrv sz rd r1 r2 => ([Pasrv sz rd r1 r2 pid; Pincpc pid])                  (**r Variable shifts *)
    | Asm.Plslv sz rd r1 r2 => ([Plslv sz rd r1 r2 pid; Pincpc pid])
    | Asm.Plsrv sz rd r1 r2 => ([Plsrv sz rd r1 r2 pid; Pincpc pid])
    | Asm.Prorv sz rd r1 r2 => ([Prorv sz rd r1 r2 pid; Pincpc pid])
    | Asm.Pcls sz rd r1 => ([Pcls sz rd r1 pid; Pincpc pid])                          (**r Bit operations *)
    | Asm.Pclz sz rd r1 => ([Pclz sz rd r1 pid; Pincpc pid])
    | Asm.Prev sz rd r1 => ([Prev sz rd r1 pid; Pincpc pid])
    | Asm.Prev16 sz rd r1 => ([Prev16 sz rd r1 pid; Pincpc pid])
    | Asm.Prbit sz rd r1 => ([Prbit sz rd r1 pid; Pincpc pid])
    | Asm.Pcsel rd r1 r2 c => ([Pcsel rd r1 r2 c pid; Pincpc pid])                    (**r Conditional data processing *)
    | Asm.Pcset rd c => ([Pcset rd c pid; Pincpc pid])
    | Asm.Pmadd sz rd r1 r2 r3 => ([Pmadd sz rd r1 r2 r3 pid; Pincpc pid])            (**r Integer multiply/divide *)
    | Asm.Pmsub sz rd r1 r2 r3 => ([Pmsub sz rd r1 r2 r3 pid; Pincpc pid])
    | Asm.Psmulh rd r1 r2 => ([Psmulh rd r1 r2 pid; Pincpc pid])
    | Asm.Pumulh rd r1 r2 => ([Pumulh rd r1 r2 pid; Pincpc pid])
    | Asm.Psdiv sz rd r1 r2 => ([Psdiv sz rd r1 r2 pid; Pincpc pid])
    | Asm.Pudiv sz rd r1 r2 => ([Pudiv sz rd r1 r2 pid; Pincpc pid])
    | Asm.Pldrs rd a => ([ReadRequest txid pid a Mfloat32; Pldrs pid txid; ReadAck rd txid pid; Pincpc pid])                           (**r Floating-point loads and stores *)
    | Asm.Pldrd rd a =>  ([ReadRequest txid pid a Mfloat64; Pldrd pid txid; ReadAck rd txid pid; Pincpc pid])
    | Asm.Pldrd_a rd a =>  ([ReadRequest txid pid a Many64; Pldrd_a pid txid; ReadAck rd txid pid; Pincpc pid])
    | Asm.Pstrs rs a => translate_write asm_i pid txid                           (**r store single-precision float *)
    | Asm.Pstrd rs a => translate_write asm_i pid txid 
    | Asm.Pstrd_a rs a => translate_write asm_i pid txid 
    | Asm.Pfmov rd r1 => ([Pfmov rd r1 pid; Pincpc pid])                              (**r Floating-point move *)
    | Asm.Pfmovimms rd f => ([Pfmovimms rd f pid; Pincpc pid])
    | Asm.Pfmovimmd rd f => ([Pfmovimmd rd f pid; Pincpc pid])
    | Asm.Pfmovi fsz rd r1 => ([Pfmovi fsz rd r1 pid; Pincpc pid])
    | Asm.Pfcvtds rd r1 => ([Pfcvtds rd r1 pid; Pincpc pid])                          (**r Floating-point conversions *)
    | Asm.Pfcvtsd rd r1 => ([Pfcvtsd rd r1 pid; Pincpc pid])
    | Asm.Pfcvtzs isz fsz rd r1 => ([Pfcvtzs isz fsz rd r1 pid; Pincpc pid])
    | Asm.Pfcvtzu isz fsz rd r1 => ([Pfcvtzu isz fsz rd r1 pid; Pincpc pid])
    | Asm.Pscvtf fsz isz rd r1 => ([Pscvtf fsz isz rd r1 pid; Pincpc pid])
    | Asm.Pucvtf fsz isz rd r1 => ([Pucvtf fsz isz rd r1 pid; Pincpc pid])
    | Asm.Pfabs sz rd r1 => ([Pfabs sz rd r1 pid; Pincpc pid])                        (**r Floating-point arithmetic *)
    | Asm.Pfneg sz rd r1 => ([Pfneg sz rd r1 pid; Pincpc pid])
    | Asm.Pfsqrt sz rd r1 => ([Pfsqrt sz rd r1 pid; Pincpc pid])
    | Asm.Pfadd sz rd r1 r2 => ([Pfadd sz rd r1 r2 pid; Pincpc pid])
    | Asm.Pfdiv sz rd r1 r2 => ([Pfdiv sz rd r1 r2 pid; Pincpc pid])
    | Asm.Pfmul sz rd r1 r2 => ([Pfmul sz rd r1 r2 pid; Pincpc pid])
    | Asm.Pfnmul sz rd r1 r2 => ([Pfnmul sz rd r1 r2 pid; Pincpc pid])
    | Asm.Pfsub sz rd r1 r2 => ([Pfsub sz rd r1 r2 pid; Pincpc pid])
    | Asm.Pfmadd sz rd r1 r2 r3 => ([Pfmadd sz rd r1 r2 r3 pid; Pincpc pid])
    | Asm.Pfmsub sz rd r1 r2 r3 => ([Pfmsub sz rd r1 r2 r3 pid; Pincpc pid])
    | Asm.Pfnmadd sz rd r1 r2 r3 => ([Pfnmadd sz rd r1 r2 r3 pid; Pincpc pid])
    | Asm.Pfnmsub sz rd r1 r2 r3 => ([Pfnmsub sz rd r1 r2 r3 pid; Pincpc pid])
    | Asm.Pfmax sz rd r1 r2 => ([Pfmax sz rd r1 r2 pid; Pincpc pid])
    | Asm.Pfmin sz rd r1 r2 => ([Pfmin sz rd r1 r2 pid; Pincpc pid])
    | Asm.Pfcmp sz r1 r2 => ([Pfcmp sz r1 r2 pid; Pincpc pid])                        (**r Floating-point comparison *)
    | Asm.Pfcmp0 sz r1 => ([Pfcmp0 sz r1 pid; Pincpc pid])
    | Asm.Pfsel rd r1 r2 cond => ([Pfsel rd r1 r2 cond pid; Pincpc pid])              (**r Floating-point conditional select *)
    | Asm.Pallocframe sz linkofs => ([Pallocframe sz linkofs pid; Pincpc pid])       (**r Pseudo-instructions *)
    | Asm.Pfreeframe sz linkofs => ([Pfreeframe sz linkofs pid; Pincpc pid])
    | Asm.Plabel lbl => ([Plabel lbl pid; Pincpc pid])
    | Asm.Ploadsymbol rd id => ([Ploadsymbol rd id pid; Pincpc pid])
    | Asm.Pcvtsw2x rd r1 => ([Pcvtsw2x rd r1 pid; Pincpc pid])
    | Asm.Pcvtuw2x rd r1 => ([Pcvtuw2x rd r1 pid; Pincpc pid])
    | Asm.Pcvtx2w rd => ([Pcvtx2w rd pid; Pincpc pid])
    | Asm.Pbtbl r1 tbl => ([Pbtbl r1 tbl pid])
    | Asm.Pbuiltin ef args res => ([Pbuiltin ef args res pid; Pincpc pid])
    | Asm.Pnop => ([Pnop pid; Pincpc pid])                                              (**r no operation *)
    | Asm.Pcfi_adjust ofs => ([Pcfi_adjust ofs pid; Pincpc pid])
    | Asm.Pcfi_rel_offset ofs => ([Pcfi_rel_offset ofs pid; Pincpc pid])                                
end.

Fixpoint eval_memsim_chain (g: genv)(f: function)(instrs: list instruction)  (ars: allregsets)  (m: mem) (ifo: in_flight_mem_ops) (eaw: early_ack_writes): outcome := 
    match instrs with
    | nil => MemSimNext ars m ifo eaw
    | instr :: chain' =>
        match eval_memsim_instr g f instr (MemSimNext ars m ifo eaw) with
        | MemSimNext ars' m' ifo eaw  => eval_memsim_chain g f (chain') ars' m' ifo eaw
        | MemSimJumpOut ars' m' ifo eaw => MemSimJumpOut ars' m' ifo eaw
        | MemSimStuck => MemSimStuck
        end
    end.

(** Proof boilerplate: move to another file?*)

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

Remark tup_equal: forall (A B: Type) (a c: A) (b d: B), a = c /\ b = d -> (a, b) = (c, d).
Proof. intros. destruct H. rewrite H. rewrite H0. reflexivity. Qed.

 Remark set_method_sem_eq: forall (pid: processor_id)(pr k: preg)(rs: regset)(ars: allregsets)(v1 v2: val),
 regs_identical ars pid rs -> v1 = v2 -> rs # k <- v1 pr = ars @ (pid, k) <- v2 (pid, pr).
 Proof.
    intros. unfold regs_identical in H. unfold Asm.Pregmap.set. rewrite <- H0. unfold PRmap.set. destruct (PregEq.eq k pr).
    - subst. destruct (PREq.eq (pid, pr) (pid, pr)). destruct (PregEq.eq pr pr). reflexivity. contradiction.
    unfold not in n. contradiction.
    -destruct (PregEq.eq pr k). rewrite <- e in n. contradiction. destruct (PREq.eq (pid, pr) (pid, k)).
    inversion e. contradiction. apply H.
 Qed.



(** Definition of the end state of an asm instruction in terms of the memsim outcome*)

Definition end_state_equals_asm_memsim (asm_o: Asm.outcome) (memsim_o: outcome) (pid: processor_id): Prop :=
    forall (r: preg),
    match asm_o, memsim_o with
    | Next rs m1, MemSimNext ars m2 _ _ => rs r = (ars @ (pid, r)) /\ m1 = m2
    | Next rs m1, MemSimJumpOut ars m2 _ _ => rs r = (ars @ (pid, r)) /\ m1 = m2
    | Stuck, MemSimStuck => True
    | _, _ => False
    end.

Remark cancel_dual_ptr_increments: forall (rs: regset) (ars: allregsets) (pid: processor_id) (v: ptrofs)(r: preg),
   rs # r = ars @ (pid, r) -> Val.offset_ptr (rs r) v = Val.offset_ptr (ars (pid, r)) v.
   Proof.
   intros. rewrite <- H. reflexivity.
   Qed.

Remark id_writes_preserve_id_regs:
    forall (rs: regset) (ars: allregsets) (pid: processor_id) (r1 r2: preg) (v: val),
    regs_identical ars pid rs -> regs_identical (ars @ (pid, r1) <- v) pid (rs # r1 <- v).
    Proof.
    intros. unfold regs_identical. unfold regs_identical in H. intro. unfold Asm.Pregmap.set. unfold PRmap.set.  destruct PREq.eq; destruct PregEq.eq. reflexivity. destruct n. inversion e. reflexivity. destruct n. inversion e. reflexivity. 
    apply H.
Qed.

Remark set_sem_eq : 
    forall (rs: regset) (ars: allregsets) (pid: processor_id) (r read_reg: preg) (v: val),
    regs_identical ars pid rs -> (rs # r <- v) read_reg = (ars @ (pid, r) <- v) (pid, read_reg).
    Proof. intros. unfold regs_identical in H. unfold Asm.Pregmap.set. unfold PRmap.set. destruct PregEq.eq; destruct PREq.eq. reflexivity. 
    destruct n. rewrite e. reflexivity. destruct n. inversion e. reflexivity.
    apply H. 
    Qed.

Remark trx_map_transitive: forall v (txid: mem_transaction_id) (ifm: in_flight_mem_ops),  
    Trmap.set txid (v) ifm txid = v.
Proof.
intros. unfold Trmap.set. destruct TrxEq.eq. reflexivity. contradiction.
Qed.

Remark eaw_map_transitive: forall (v: val) (a: val) (eaw: early_ack_writes) (pid: processor_id) (c: memory_chunk),  
(EWmap.set (pid, a, c) (Some v) eaw)(pid, a, c) = Some v.
Proof.
intros. unfold EWmap.set. destruct EWEq.eq. reflexivity. contradiction.
Qed.

(* Remark trx_map_transitive_form_2: forall v (txid: mem_transaction_id) (ifm: in_flight_mem_ops),  
Trmap.get txid (Trmap.set txid (v) ifm) = v.
Proof.
intros. unfold Trmap.set. unfold Trmap.get. destruct TrxEq.eq. reflexivity. contradiction.
Qed.  *)

Ltac sem_eq_solver :=
    match goal with
    (*Identity*)
    [ |- ?x = ?x ] => reflexivity (*Terminal*)
    (*Prereq of a proof we already did upon entry*)
    | [H: regs_identical ?ars ?pid ?rs |- regs_identical ?ars ?pid ?rs] => apply H (*Terminal*)
    (* Obvious contradiction - is there a better way to do this?*)
    | [H1: Vptr ?b1 ?i1 = Vundef |- _] => inversion H1 (*Terminal*)
    | [H1: Vundef =  Vptr ?b1 ?i1 |- _] => inversion H1 (*Terminal*)
    | [H1: Some ?x = None |- _] => inversion H1 (*Terminal*)
    | [H1: None = Some ?x |- _] => inversion H1 (*Terminal*)
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
    | [H1: ?x = ?y, H2: ?x = ?z |- _ ] => rewrite H1 in H2; try inversion H2; sem_eq_solver (*Nonterminal*)
    (*Break apart constructions*)
    | [H: ?singleton_op ?v = ?singleton_op ?v2 |- _] => inversion H; clear H; subst; sem_eq_solver (*Nonterminal*) 
    (*Used for forwarding values from in-flight memory ops*)
    | [H: context[Trmap.set ?txid ?v ?ifm ?txid] |- _] => rewrite -> trx_map_transitive in H; sem_eq_solver (*Nonterminal*)
    (*Used for forwarding values from early acks*)
    | [H: context[EWmap.set ?k ?v ?m ?k] |- _] => rewrite -> eaw_map_transitive in H; sem_eq_solver (*Nonterminal*)
    (*Pointer inversion*)
    | [H1: ?x = Vptr ?b1 ?i1,
       H2: ?x = Vptr ?b2 ?i2
       |- _ ] => rewrite -> H1 in H2; inversion H2; clear H2; subst; sem_eq_solver (*Nonterminal*)
    (*Pointer inversion*)
    | [H1: Vptr ?b1 ?i1 = Vptr ?b2 ?i2 |- _] => inversion H1; clear H1; subst; sem_eq_solver (*Nonterminal*)
    | [ |- Val.offset_ptr ?v1 ?n = Val.offset_ptr ?v2 ?n] => apply cancel_dual_ptr_increments; sem_eq_solver (*Nonterminal*)
    | (*Break apart subgoal*)
    [ |- regs_identical ?ars ?r ?rs ] => unfold regs_identical; intro; sem_eq_solver (*Nonterminal*)
    | _ => idtac
    end.

Remark tuple_fneq: forall(A B: Type)  (a b: A) (c d: B), a <> b -> pair a c <> pair b d.
Proof.
intros. unfold not. intros. inv H0. contradiction.
Qed.

Remark tuple_bneq:  forall(A B: Type)  (a b: A) (c d: B), c <> d -> pair a c <> pair b d.
Proof.
intros. unfold not. intros. inv H0. contradiction.
Qed.


Ltac temp_solver := 
    match goal with
    | [H1: Pregmap.set ?r1 ?v ?rs ?r2 = ?e1,
        H2: PRmap.set (?pid, ?r1) ?v ?ars (?pid, ?r2) = ?e2,
        ri: regs_identical ?ars ?pid ?rs 
        |- False] => assert (Hri: regs_identical (ars @ (pid, r1) <- v) pid (rs # r1 <- v)); try apply id_writes_preserve_id_regs; auto; try apply ri;
        specialize (Hri r2); rewrite <- Hri in H2; rewrite -> H2 in H1; inversion H1
    end.

 Definition no_early_acks (eaw: early_ack_writes)(pid: processor_id): Prop :=
    forall a c, eaw (pid, a, c) = None.

Theorem asm_identical_to_forward_sim: forall (g: genv)(f: function) (i: Asm.instruction) (rs: regset) (ars: allregsets) (m: mem) (pid: processor_id) (ifm: in_flight_mem_ops) (eaw: early_ack_writes), 
    no_early_acks eaw pid -> regs_identical ars pid rs -> end_state_equals_asm_memsim (exec_instr g f i rs  m)  (eval_memsim_chain g f (asm_to_memsim i pid 0) ars m ifm eaw) pid .
Proof.
intros. pose proof H0 as ri. unfold no_early_acks in H. unfold regs_identical in H0.  unfold end_state_equals_asm_memsim. intro. remember i as orig_i eqn:H_orig_i. rewrite -> H_orig_i. destruct i; simpl; try unfold Asm.goto_label; try unfold goto_label; try unfold Asm.eval_testcond; try unfold eval_testcond; try unfold Asm.exec_load; try unfold serialize_read; unfold read_ack; try unfold read_request; try unfold Asm.exec_store; try unfold write_ack; try unfold write_request; try unfold early_ack_write; unfold serialize_write; try unfold Mem.loadv; try unfold eval_addressing; try unfold Asm.eval_addressing; unfold Asm.compare_long; unfold compare_long; unfold Asm.compare_int; unfold compare_int; unfold Asm.ir0w; unfold ir0w; unfold Asm.ir0x; unfold ir0x; unfold Asm.compare_single; unfold compare_single; unfold Asm.compare_float; unfold compare_float;destruct matches; try split; try unfold nextinstr; try apply set_method_sem_eq; sem_eq_solver. 

(*Solves 21/25 proof by contradiction of Pbtbl*)
all: try temp_solver.

assert (regs_identical (ars @ (pid, X16) <- Vundef) pid (rs # X16 <- Vundef)). apply id_writes_preserve_id_regs. auto. apply ri.
pose proof H1 as Hdup. specialize (H1 r1). rewrite <- H1 in Heqv1. rewrite -> Heqv1 in Heqv. inversion Heqv. subst.
rewrite Heqo1 in Heqo. inversion Heqo. subst. rewrite Heqo2 in Heqo0. inversion Heqo0.  subst.
specialize (Hdup PC). rewrite <- Hdup in Heqv2. rewrite -> Heqv2 in Heqv0. inversion Heqv0. reflexivity.



(*4 annoying remaining edge cases*)
subst. rewrite Heqo1 in Heqo. inversion Heqo. subst. rewrite Heqo2 in Heqo0. discriminate.
subst. rewrite Heqo1 in Heqo. inversion Heqo.
subst. rewrite Heqo1 in Heqo. inversion Heqo. subst. rewrite Heqo2 in Heqo0. discriminate.
subst.  rewrite Heqo0 in Heqo. inversion Heqo. 
Qed.


Lemma outcome_equality: forall (ars1 ars2: allregsets)(m1 m2: mem)(eaw1 eaw2: early_ack_writes) (ifmo1 ifmo2: in_flight_mem_ops), 
     MemSimNext ars1 m1 ifmo1 eaw1 = MemSimNext ars2 m2 ifmo2 eaw2 -> ars1 = ars2 /\ m1 = m2 /\ eaw1 = eaw2 /\ ifmo1 = ifmo2. 
    Proof. intros. inversion H. split. reflexivity. split. reflexivity. split. reflexivity. reflexivity. Qed.

Lemma inverse_outcome_equality: forall (ars1 ars2: allregsets)(m1 m2: mem)(eaw1 eaw2: early_ack_writes) (ifmo1 ifmo2: in_flight_mem_ops), 
ars1 = ars2 /\ m1 = m2 /\ eaw1 = eaw2 /\ ifmo1 = ifmo2 -> MemSimNext ars1 m1 ifmo1 eaw1 = MemSimNext ars2 m2 ifmo2 eaw2. 
Proof. intros. destruct H. destruct H0. destruct H1. subst. reflexivity. Qed.

(* need some way of abstracting 
for a given instruction if an argument is a data source/data sink*)
Inductive data_resource: Type :=
    | SingleReg: processor_id -> preg -> data_resource
    | SingleMemAddr: memory_chunk -> val -> data_resource
    | TransactionId: mem_transaction_id -> data_resource
    .

Definition data_res_eq (d1 d2: data_resource): Prop :=
    match d1, d2 with
    | SingleReg p1 r1, SingleReg p2 r2 => p1 = p2 /\ r1 = r2
    | SingleMemAddr c1 v1, SingleMemAddr c2 v2 => c1 = c2 /\ v1 = v2
    | TransactionId t1, TransactionId t2 => t1 = t2
    | _, _ => False
    end.

Definition iregz_same_resource (r: ireg0) (pid: processor_id)(dr: data_resource) : Prop :=
    match r with 
    | RR0 r1 => data_res_eq (SingleReg pid r1) dr 
    | XZR => False
    end.
    
    
Remark data_res_isomorphism: forall r, data_res_eq r r.
Proof.
    intros. destruct r; unfold data_res_eq; try split; reflexivity.
Qed.

Lemma symb_data_eq: forall (x y: data_resource), {x=y} + {x<>y}.
Proof. decide equality. apply preg_eq. apply Z.eq_dec. apply Val.eq. apply AST.chunk_eq. apply tx_eq.
Qed.

(* TODO Check if data resource d is an input for address a. Requires checking the regs of A*)
Definition data_address_src (pid: processor_id)(a: addressing) (d: data_resource) : Prop := 
   match a with
   | ADimm base n => data_res_eq (SingleReg pid (preg_of_iregsp base)) d
   | ADreg base r => data_res_eq (SingleReg pid (preg_of_iregsp base)) d \/  data_res_eq (SingleReg pid r) d
   | ADlsl base r n => data_res_eq  ( SingleReg pid (preg_of_iregsp base)) d \/ data_res_eq (SingleReg pid r) d
   | ADsxt base r n => data_res_eq (SingleReg pid (preg_of_iregsp base)) d \/ data_res_eq (SingleReg pid r) d
   | ADuxt base r n => data_res_eq (SingleReg pid (preg_of_iregsp base)) d \/ data_res_eq (SingleReg pid r) d
   | ADadr base id ofs => data_res_eq (SingleReg pid (preg_of_iregsp base)) d
   | ADpostincr base n => True (* not modeled in CompCert*) 
   end.



Definition memory_conflict(c1 c2: memory_chunk)(a1 a2: val): Prop :=
    match a1, a2 with
    | Vptr b1 ofs1, Vptr b2 ofs2 => b1 = b2 /\ ~(Ptrofs.unsigned ofs1 + size_chunk c1 <= Ptrofs.unsigned ofs2 \/ Ptrofs.unsigned ofs2 + size_chunk c2 <= Ptrofs.unsigned ofs1)
    | _, _ => True
    end.

 (* Check if data resource d is overwritten by a. Requires checking the evaluated expr*)
 Definition data_address_sink (c: memory_chunk)(a: addressing)(g: genv) (ars: allregsets) (pid: processor_id) (d: data_resource) : Prop := 
    match d with
        | SingleMemAddr c' b => memory_conflict c c' (eval_addressing g a ars pid) b 
    | _ => False
    end.

(* Get a proposition representing if an instruction has a dependency on dr*)
Definition data_source(i: instruction) (dr: data_resource): Prop := 
    match i with 
   (* Jump to*)
   | Pb lbl pid => False                                                    (**r branch *)
   | Pbc c lbl  pid => data_res_eq (SingleReg pid (CR CZ)) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr                                  (**r conditional branch *)
   | Pbl id sg pid => data_res_eq (SingleReg pid PC) dr                                 (**r jump to function and link *)
   | Pbs id sg pid => False                              (**r jump to function *)
   | Pblr r sg  pid => data_res_eq (SingleReg pid PC) dr \/ data_res_eq (SingleReg pid r) dr                             (**r indirect jump and link *)
   | Pbr r sg   pid => data_res_eq (SingleReg pid RA) dr  \/ data_res_eq (SingleReg pid r) dr                        (**r indirect jump *)
   | Pret r pid => data_res_eq (SingleReg pid r) dr                                              (**r return *)
   | Pcbnz sz r lbl    pid => data_res_eq (SingleReg pid r) dr                      (**r branch if not zero *)
   | Pcbz sz r lbl pid => data_res_eq (SingleReg pid r) dr                         (**r branch if zero *)
   | Ptbnz sz r n lbl   pid => data_res_eq (SingleReg pid r) dr               (**r branch if bit n is not zero *)
   | Ptbz sz r n lbl pid => data_res_eq (SingleReg pid r) dr                  (**r branch if bit n is zero *)
   (** Memory loads and stores *)
   | Pldrw pid txid =>  data_res_eq (TransactionId txid) dr                          (**r load int32 *)
   | Pldrw_a pid txid =>  data_res_eq (TransactionId txid) dr                                (**r load int32 as any32 *)
   | Pldrx pid txid =>  data_res_eq (TransactionId txid) dr                                 (**r load int64 *)
   | Pldrx_a pid txid =>  data_res_eq (TransactionId txid) dr                                (**r load int64 as any64 *)
   | Pldrb sz pid txid =>  data_res_eq (TransactionId txid) dr                        (**r load int8, zero-extend *)
   | Pldrsb sz pid txid =>  data_res_eq (TransactionId txid) dr                       (**r load int8, sign-extend *)
   | Pldrh sz pid txid =>  data_res_eq (TransactionId txid) dr                       (**r load int16, zero-extend *)
   | Pldrsh sz pid txid =>  data_res_eq (TransactionId txid) dr                       (**r load int16, sign-extend *)
   | Pldrzw  pid txid =>  data_res_eq (TransactionId txid) dr                                 (**r load int32, zero-extend to int64 *)
   | Pldrsw pid txid => data_res_eq (TransactionId txid) dr                                (**r load int32, sign-extend to int64 *)
   | Pldp rd1 a pid txid => data_res_eq (TransactionId txid) dr                            (**r load two int64 *)
   (** Stores *)
   | Pstrw a pid txid => data_res_eq (TransactionId txid) dr                            (**r store int32 *)
   | Pstrw_a a pid txid => data_res_eq (TransactionId txid) dr                                  (**r store int32 as any32 *)
   | Pstrx a pid txid => data_res_eq (TransactionId txid) dr                                   (**r store int64 *)
   | Pstrx_a a pid txid => data_res_eq (TransactionId txid) dr                                (**r store int64 as any64 *)
   | Pstrb a pid txid => data_res_eq (TransactionId txid) dr                                 (**r store int8 *)
   | Pstrh a pid txid => data_res_eq (TransactionId txid) dr                                 (**r store int16 *)
   | Pstp a pid txid => True                              (**Not generated by compcert *)
   (** Integer arithmetic, immediate *)
   | Paddimm sz rd r1 n  pid => data_res_eq (SingleReg pid (preg_of_iregsp r1)) dr            (**r addition *)
   | Psubimm sz rd r1 n pid => data_res_eq (SingleReg pid (preg_of_iregsp r1)) dr               (**r subtraction *)
   | Pcmpimm sz r1 n pid => data_res_eq (SingleReg pid r1) dr                             (**r compare *)
   | Pcmnimm sz r1 n pid => data_res_eq (SingleReg pid r1) dr                              (**r compare negative *)
   (** Move integer register *)
   | Pmov rd r1 pid => data_res_eq (SingleReg pid (preg_of_iregsp r1)) dr 
   (** Logical, immediate *)
   | Pandimm sz rd r1 n pid => iregz_same_resource r1 pid dr                (**r and *)
   | Peorimm sz rd r1 n pid => iregz_same_resource r1 pid dr                 (**r xor *)
   | Porrimm sz rd r1 n pid => iregz_same_resource r1 pid dr                 (**r or *)
   | Ptstimm sz r1 n pid => data_res_eq (SingleReg pid r1) dr                            (**r and, then set flags *)
   (** Move wide immediate *)
   | Pmovz sz rd n pos  pid => False                (**r move [n << pos] to [rd] *)
   | Pmovn sz rd n pos  pid => False                (**r move [NOT(n << pos)] to [rd] *)
   | Pmovk sz rd n pos  pid => False                (**r insert 16 bits of [n] at [pos] in rd *)
   (** PC-relative addressing *)
   | Padrp rd id ofs pid => False                   (**r set [rd] to high address of [id + ofs] *)
   | Paddadr rd r1 id ofs pid => data_res_eq (SingleReg pid r1) dr             (**r add the low address of [id + ofs] *)
   (** Bit-field operations *)
   | Psbfiz sz rd r1 r s pid => data_res_eq (SingleReg pid r1) dr           (**r sign extend and shift left *)
   | Psbfx sz rd r1 r s pid => data_res_eq (SingleReg pid r1) dr           (**r shift right and sign extend *)
   | Pubfiz sz rd r1 r s pid => data_res_eq (SingleReg pid r1) dr           (**r zero extend and shift left *)
   | Pubfx sz rd r1 r s pid => data_res_eq (SingleReg pid r1) dr           (**r shift right and zero extend *)
   (** Integer arithmetic, shifted register *)
   | Padd sz rd r1 r2 s pid => iregz_same_resource r1 pid dr \/ data_res_eq (SingleReg pid r2) dr   (**r addition *)
   | Psub sz rd r1 r2 s pid => iregz_same_resource r1 pid dr \/ data_res_eq (SingleReg pid r2) dr  (**r subtraction *)
   | Pcmp sz r1 r2 s pid => iregz_same_resource r1 pid dr \/ data_res_eq (SingleReg pid r2) dr             (**r compare *)
   | Pcmn sz r1 r2 s pid => iregz_same_resource r1 pid dr \/ data_res_eq (SingleReg pid r2) dr             (**r compare negative *)
   (** Integer arithmetic, extending register *)
   | Paddext rd r1 r2 x pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr        (**r int64-int32 add *)
   | Psubext rd r1 r2 x pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr        (**r int64-int32 sub *)
   | Pcmpext r1 r2 x pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                     (**r int64-int32 cmp *)
   | Pcmnext r1 r2 x pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                       (**r int64-int32 cmn *)
   (** Logical, shifted register *)
   | Pand sz rd r1 r2 s pid => iregz_same_resource r1 pid dr \/ data_res_eq (SingleReg pid r2) dr   (**r and *)
   | Pbic sz rd r1 r2 s pid => iregz_same_resource r1 pid dr \/ data_res_eq (SingleReg pid r2) dr  (**r and-not *)
   | Peon sz rd r1 r2 s pid => iregz_same_resource r1 pid dr \/ data_res_eq (SingleReg pid r2) dr  (**r xor-not *)
   | Peor sz rd r1 r2 s pid => iregz_same_resource r1 pid dr \/ data_res_eq (SingleReg pid r2) dr  (**r xor *)
   | Porr sz rd r1 r2 s pid => iregz_same_resource r1 pid dr \/ data_res_eq (SingleReg pid r2) dr  (**r or *)
   | Porn sz rd r1 r2 s pid => iregz_same_resource r1 pid dr \/ data_res_eq (SingleReg pid r2) dr   (**r or-not *)
   | Ptst sz r1 r2 s pid => iregz_same_resource r1 pid dr \/ data_res_eq (SingleReg pid r2) dr                (**r and, then set flags *)
   (** Variable shifts *)
   | Pasrv sz rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                         (**r arithmetic right shift *)
   | Plslv sz rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                         (**r left shift *)
   | Plsrv sz rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                         (**r logical right shift *)
   | Prorv sz rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                        (**r rotate right *)
   (** Bit operations *)
   | Pcls sz rd r1 pid => data_res_eq (SingleReg pid r1) dr                                    (**r count leading sign bits *)
   | Pclz sz rd r1 pid => data_res_eq (SingleReg pid r1) dr                                     (**r count leading zero bits *)
   | Prev sz rd r1 pid => data_res_eq (SingleReg pid r1) dr                                    (**r reverse bytes *)
   | Prev16 sz rd r1 pid => data_res_eq (SingleReg pid r1) dr                                   (**r reverse bytes in each 16-bit word *)
   | Prbit sz rd r1  pid => data_res_eq (SingleReg pid r1) dr                                   (**r reverse bits *)
   (** Conditional data processing *)
   | Pcsel rd r1 r2 c  pid => data_res_eq (SingleReg pid r1) dr  \/ data_res_eq (SingleReg pid r2) dr \/ data_res_eq (SingleReg pid CZ) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr                      (**r int conditional move *)
   | Pcset rd c pid => data_res_eq (SingleReg pid CZ) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr                               (**r set to 1/0 if cond is true/false *)
   (*
   | Pcsetm rd c                                   (**r set to -1/0 if cond is true/false *)
   *)
   (** Integer multiply/divide *)
   | Pmadd sz rd r1 r2 r3 pid =>  data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr \/ iregz_same_resource r3 pid dr              (**r multiply-add *)
   | Pmsub sz rd r1 r2 r3 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr \/ iregz_same_resource r3 pid dr          (**r multiply-sub *)
   | Psmulh rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                                   (**r signed multiply high *)
   | Pumulh rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                                   (**r unsigned multiply high *)
   | Psdiv sz rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                       (**r signed division *)
   | Pudiv sz rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                       (**r unsigned division *)
   (** Floating-point loads and stores *)
   | Pldrs pid txid => data_res_eq (TransactionId txid) dr                                   (**r load float32 (single precision) *)
   | Pldrd pid txid => data_res_eq (TransactionId txid) dr                                  (**r load float64 (double precision) *)
   | Pldrd_a pid txid => data_res_eq (TransactionId txid) dr                                (**r load float64 as any64 *)
   | Pstrs a pid txid => data_res_eq (TransactionId txid) dr                                   (**r store float32 *)
   | Pstrd a pid txid => data_res_eq (TransactionId txid) dr                                   (**r store float64 *)
   | Pstrd_a a pid txid=> data_res_eq (TransactionId txid) dr                                (**r store float64 as any64 *)
   (** Floating-point move *)
   | Pfmov rd r1 pid => data_res_eq (SingleReg pid r1) dr
   | Pfmovimms rd f  pid => False                                (**r load float32 constant *)
   | Pfmovimmd rd f  pid => False                                  (**r load float64 constant *)
   | Pfmovi fsz rd r1 pid => iregz_same_resource r1 pid dr                        (**r copy int reg to FP reg *)
   (** Floating-point conversions *)
   | Pfcvtds rd r1  pid => data_res_eq (SingleReg pid r1) dr                                            (**r convert float32 to float64 *)
   | Pfcvtsd rd r1  pid => data_res_eq (SingleReg pid r1) dr                                           (**r convert float64 to float32 *)
   | Pfcvtzs isz fsz rd r1 pid => data_res_eq (SingleReg pid r1) dr            (**r convert float to signed int *)
   | Pfcvtzu isz fsz rd r1 pid => data_res_eq (SingleReg pid r1) dr           (**r convert float to unsigned int *)
   | Pscvtf fsz isz rd r1 pid => data_res_eq (SingleReg pid r1) dr             (**r convert signed int to float *)
   | Pucvtf fsz isz rd r1 pid => data_res_eq (SingleReg pid r1) dr            (**r convert unsigned int to float *)
   (** Floating-point arithmetic *)
   | Pfabs sz rd r1 pid => data_res_eq (SingleReg pid r1) dr                                    (**r absolute value *)
   | Pfneg sz rd r1 pid => data_res_eq (SingleReg pid r1) dr                                    (**r negation *)
   | Pfsqrt sz rd r1 pid => data_res_eq (SingleReg pid r1) dr                                   (**r square root *)
   | Pfadd sz rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                                 (**r addition *)
   | Pfdiv sz rd r1 r2  pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                               (**r division *)
   | Pfmul sz rd r1 r2  pid => data_res_eq (SingleReg pid r1) dr  \/ data_res_eq (SingleReg pid r2) dr                             (**r multiplication *)
   | Pfnmul sz rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr  \/ data_res_eq (SingleReg pid r2) dr                             (**r multiply-negate *)
   | Pfsub sz rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr   \/ data_res_eq (SingleReg pid r2) dr                              (**r subtraction *)
   | Pfmadd sz rd r1 r2 r3 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr \/ data_res_eq (SingleReg pid r3) dr                            (**r [rd = r3 + r1 * r2] *)
   | Pfmsub sz rd r1 r2 r3 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr \/ data_res_eq (SingleReg pid r3) dr                            (**r [rd = r3 - r1 * r2] *)
   | Pfnmadd sz rd r1 r2 r3 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr \/ data_res_eq (SingleReg pid r3) dr                           (**r [rd = - r3 - r1 * r2] *)
   | Pfnmsub sz rd r1 r2 r3 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr \/ data_res_eq (SingleReg pid r3) dr                           (**r [rd = - r3 + r1 * r2] *)
   | Pfmax sz rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                                (**r maximum *)
   | Pfmin sz rd r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                               (**r minimum *)
   (** Floating-point comparison *)
   | Pfcmp sz r1 r2 pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr                                   (**r compare [r1] and [r2] *)
   | Pfcmp0 sz r1 pid => data_res_eq (SingleReg pid r1) dr                                      (**r compare [r1] and [+0.0] *)
   (** Floating-point conditional select *)
   | Pfsel rd r1 r2 cond pid => data_res_eq (SingleReg pid r1) dr \/ data_res_eq (SingleReg pid r2) dr  \/ data_res_eq (SingleReg pid CZ) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr
   (** Pseudo-instructions *)
   | Pallocframe sz linkofs pid => False                              (**r allocate new stack frame *)
   | Pfreeframe sz linkofs pid => False                               (**r deallocate stack frame and restore previous frame *)
   | Plabel lbl pid => False                                                (**r define a code label *)
   | Ploadsymbol rd id pid => False                                 (**r load the address of [id] *)
   | Pcvtsw2x rd r1 pid => data_res_eq (SingleReg pid r1) dr                                 (**r sign-extend 32-bit int to 64-bit *)
   | Pcvtuw2x rd r1 pid => data_res_eq (SingleReg pid r1) dr                                  (**r zero-extend 32-bit int to 64-bit *)
   | Pcvtx2w rd pid => data_res_eq (SingleReg pid rd) dr                                                 (**r retype a 64-bit int as a 32-bit int *)
   | Pbtbl r1 tbl  pid => data_res_eq (SingleReg pid r1) dr                              (**r N-way branch through a jump table *)
   | Pbuiltin ef args res pid => False   (**r built-in function (pseudo) *)
   | Pnop pid => False                                                             (**r no operation *)
   | Pcfi_adjust ofs pid => False                                           (**r .cfi_adjust debug directive *)
   | Pcfi_rel_offset ofs  pid => False                                       (**r .cfi_rel_offset debug directive *)
   | Pincpc pid => data_res_eq (SingleReg pid PC) dr
   (* prevents reordering of memory operations*)
   | Memfence _ => match dr with
                    | TransactionId _ => True 
                    | _ => False
                    end
    | EarlyAck txid pid => data_res_eq (TransactionId txid) dr
    | WriteRequest txid pid a rd c => data_address_src pid a dr \/ data_res_eq (SingleReg pid rd) dr \/ data_res_eq (TransactionId txid) dr
    | ReadRequest txid pid a c => data_address_src  pid a dr \/ data_res_eq (TransactionId txid) dr
    | WriteAck txid pid => data_res_eq (TransactionId txid) dr
    | ReadAck r txid pid => data_res_eq (TransactionId txid) dr
    end.

(* checks if instruction writes to dr*)
Definition data_sink(i: instruction) (dr: data_resource) (g: genv) (ars: allregsets): Prop := 
    match i with
    (*actual*)
    (* Jump to*)
    | Pb lbl pid => data_res_eq (SingleReg pid PC) dr                                                    (**r branch *)
    | Pbc c lbl  pid => data_res_eq (SingleReg pid PC) dr                                    (**r conditional branch *)
    | Pbl id sg pid => data_res_eq (SingleReg pid PC) dr \/ data_res_eq (SingleReg pid RA) dr                                    (**r jump to function and link *)
    | Pbs id sg pid => data_res_eq (SingleReg pid PC) dr                                   (**r jump to function *)
    | Pblr r sg  pid => data_res_eq (SingleReg pid PC) dr  \/ data_res_eq (SingleReg pid RA) dr                                (**r indirect jump and link *)
    | Pbr r sg   pid => data_res_eq (SingleReg pid PC) dr                                   (**r indirect jump *)
    | Pret r pid => data_res_eq (SingleReg pid PC) dr                                             (**r return *)
    | Pcbnz sz r lbl    pid => data_res_eq (SingleReg pid PC) dr                       (**r branch if not zero *)
    | Pcbz sz r lbl pid => data_res_eq (SingleReg pid PC) dr                           (**r branch if zero *)
    | Ptbnz sz r n lbl   pid => data_res_eq (SingleReg pid PC) dr               (**r branch if bit n is not zero *)
    | Ptbz sz r n lbl pid => data_res_eq (SingleReg pid PC) dr                  (**r branch if bit n is zero *)
    (** Memory loads and stores *)
    | Pldrw pid txid => data_res_eq (TransactionId txid) dr                                 (**r load int32 *)
    | Pldrw_a pid txid => data_res_eq (TransactionId txid) dr                                  (**r load int32 as any32 *)
    | Pldrx pid txid => data_res_eq (TransactionId txid) dr                                  (**r load int64 *)
    | Pldrx_a pid txid => data_res_eq (TransactionId txid) dr                                 (**r load int64 as any64 *)
    | Pldrb sz pid txid => data_res_eq (TransactionId txid) dr                        (**r load int8, zero-extend *)
    | Pldrsb sz pid txid => data_res_eq (TransactionId txid) dr                        (**r load int8, sign-extend *)
    | Pldrh sz pid txid => data_res_eq (TransactionId txid) dr                        (**r load int16, zero-extend *)
    | Pldrsh sz pid txid => data_res_eq (TransactionId txid) dr                      (**r load int16, sign-extend *)
    | Pldrzw  pid txid => data_res_eq (TransactionId txid) dr                                 (**r load int32, zero-extend to int64 *)
    | Pldrsw pid txid => data_res_eq (TransactionId txid) dr                                 (**r load int32, sign-extend to int64 *)
    | Pldp rd1 rd2 id txid => True (*not modeled by CompCErt*)                                (**r load two int64 *)
    (* explanation: check if r is a memory address and, if so, check if a stores in r. Can check by evaluating both??? *)
    | Pstrw a pid txid => data_address_sink Mint32 a g ars pid dr  \/ data_res_eq (TransactionId txid) dr                                   (**r store int32 *)
    | Pstrw_a a pid txid => data_address_sink Many32 a g ars pid dr  \/ data_res_eq (TransactionId txid) dr                                    (**r store int32 as any32 *)
    | Pstrx a pid txid => data_address_sink Mint64 a g ars pid dr  \/ data_res_eq (TransactionId txid) dr                                     (**r store int64 *)
    | Pstrx_a a pid txid => data_address_sink Many64 a g ars pid dr  \/ data_res_eq (TransactionId txid) dr                                   (**r store int64 as any64 *)
    | Pstrb a pid txid => data_address_sink Mint8unsigned a g ars pid dr    \/ data_res_eq (TransactionId txid) dr                                  (**r store int8 *)
    | Pstrh a pid txid => data_address_sink Mint16unsigned a g ars pid dr  \/ data_res_eq (TransactionId txid) dr                                     (**r store int16 *)
    | Pstp a pid txid => True (*Not generated by compcert*)                              (**r store two int64 *)
    (** Integer arithmetic, immediate *)
    | Paddimm sz rd r1 n  pid => data_res_eq (SingleReg pid (preg_of_iregsp rd)) dr           (**r addition *)
    | Psubimm sz rd r1 n pid => data_res_eq (SingleReg pid (preg_of_iregsp rd)) dr               (**r subtraction *)
    | Pcmpimm sz r1 n pid => data_res_eq (SingleReg pid (CR CZ)) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr                            (**r compare *)
    | Pcmnimm sz r1 n pid => data_res_eq (SingleReg pid (CR CZ)) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr                             (**r compare negative *)
    (** Move integer register *)
    | Pmov rd r1 pid => data_res_eq (SingleReg pid (preg_of_iregsp rd)) dr
    (** Logical, immediate *)
    | Pandimm sz rd r1 n pid => data_res_eq (SingleReg pid rd) dr                 (**r and *)
    | Peorimm sz rd r1 n pid => data_res_eq (SingleReg pid rd) dr                 (**r xor *)
    | Porrimm sz rd r1 n pid => data_res_eq (SingleReg pid (preg_of_iregsp rd))  dr                (**r or *)
    | Ptstimm sz r1 n pid => data_res_eq (SingleReg pid (CR CZ)) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr                             (**r and, then set flags *)
    (** Move wide immediate *)
    | Pmovz sz rd n pos  pid => data_res_eq  (SingleReg pid rd) dr                   (**r move [n << pos] to [rd] *)
    | Pmovn sz rd n pos  pid => data_res_eq  (SingleReg pid rd) dr                  (**r move [NOT(n << pos)] to [rd] *)
    | Pmovk sz rd n pos  pid => data_res_eq  (SingleReg pid rd) dr                 (**r insert 16 bits of [n] at [pos] in rd *)
    (** PC-relative addressing *)
    | Padrp rd id ofs pid => data_res_eq (SingleReg pid rd)  dr                      (**r set [rd] to high address of [id + ofs] *)
    | Paddadr rd r1 id ofs pid => data_res_eq (SingleReg pid rd) dr             (**r add the low address of [id + ofs] *)
    (** Bit-field operations *)
    | Psbfiz sz rd r1 r s pid => data_res_eq (SingleReg pid rd) dr           (**r sign extend and shift left *)
    | Psbfx sz rd r1 r s pid => data_res_eq (SingleReg pid rd) dr           (**r shift right and sign extend *)
    | Pubfiz sz rd r1 r s pid => data_res_eq (SingleReg pid rd) dr           (**r zero extend and shift left *)
    | Pubfx sz rd r1 r s pid => data_res_eq (SingleReg pid rd) dr           (**r shift right and zero extend *)
    (** Integer arithmetic, shifted register *)
    | Padd sz rd r1 r2 s pid => data_res_eq (SingleReg pid rd) dr   (**r addition *)
    | Psub sz rd r1 r2 s pid => data_res_eq (SingleReg pid rd) dr  (**r subtraction *)
    | Pcmp sz r1 r2 s pid => data_res_eq (SingleReg pid (CR CZ)) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr              (**r compare *)
    | Pcmn sz r1 r2 s pid => data_res_eq (SingleReg pid (CR CZ)) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr               (**r compare negative *)
    (** Integer arithmetic, extending register *)
    | Paddext rd r1 r2 x pid => data_res_eq (SingleReg pid (preg_of_iregsp rd)) dr        (**r int64-int32 add *)
    | Psubext rd r1 r2 x pid => data_res_eq (SingleReg pid (preg_of_iregsp rd)) dr       (**r int64-int32 sub *)
    | Pcmpext r1 r2 x pid => data_res_eq (SingleReg pid (CR CZ)) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr                     (**r int64-int32 cmp *)
    | Pcmnext r1 r2 x pid => data_res_eq (SingleReg pid (CR CZ)) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr                      (**r int64-int32 cmn *)
    (** Logical, shifted register *)
    | Pand sz rd r1 r2 s pid => data_res_eq (SingleReg pid rd) dr   (**r and *)
    | Pbic sz rd r1 r2 s pid => data_res_eq (SingleReg pid rd) dr   (**r and-not *)
    | Peon sz rd r1 r2 s pid => data_res_eq (SingleReg pid rd) dr   (**r xor-not *)
    | Peor sz rd r1 r2 s pid => data_res_eq (SingleReg pid rd) dr   (**r xor *)
    | Porr sz rd r1 r2 s pid => data_res_eq (SingleReg pid rd) dr  (**r or *)
    | Porn sz rd r1 r2 s pid => data_res_eq (SingleReg pid rd) dr  (**r or-not *)
    | Ptst sz r1 r2 s pid => data_res_eq (SingleReg pid (CR CZ)) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr                (**r and, then set flags *)
    (** Variable shifts *)
    | Pasrv sz rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                         (**r arithmetic right shift *)
    | Plslv sz rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                         (**r left shift *)
    | Plsrv sz rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                         (**r logical right shift *)
    | Prorv sz rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                        (**r rotate right *)
    (** Bit operations *)
    | Pcls sz rd r1 pid => data_res_eq (SingleReg pid rd) dr                                     (**r count leading sign bits *)
    | Pclz sz rd r1 pid => data_res_eq (SingleReg pid rd) dr                                     (**r count leading zero bits *)
    | Prev sz rd r1 pid => data_res_eq (SingleReg pid rd) dr                                    (**r reverse bytes *)
    | Prev16 sz rd r1 pid => data_res_eq (SingleReg pid rd) dr                                   (**r reverse bytes in each 16-bit word *)
    | Prbit sz rd r1  pid => data_res_eq (SingleReg pid rd) dr                                   (**r reverse bits *)
    (** Conditional data processing *)
    | Pcsel rd r1 r2 c  pid => data_res_eq (SingleReg pid rd) dr                     (**r int conditional move *)
    | Pcset rd c pid => data_res_eq (SingleReg pid rd) dr                                     (**r set to 1/0 if cond is true/false *)
    (*
    | Pcsetm rd c                                   (**r set to -1/0 if cond is true/false *)
    *)
    (** Integer multiply/divide *)
    | Pmadd sz rd r1 r2 r3 pid => data_res_eq (SingleReg pid rd) dr             (**r multiply-add *)
    | Pmsub sz rd r1 r2 r3 pid => data_res_eq (SingleReg pid rd) dr             (**r multiply-sub *)
    | Psmulh rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                                   (**r signed multiply high *)
    | Pumulh rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                                    (**r unsigned multiply high *)
    | Psdiv sz rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                        (**r signed division *)
    | Pudiv sz rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                        (**r unsigned division *)
    (** Floating-point loads and stores *)
    | Pldrs pid txid =>  data_res_eq (TransactionId txid) dr                                     (**r load float32 (single precision) *)
    | Pldrd pid txid => data_res_eq (TransactionId txid) dr                                  (**r load float64 (double precision) *)
    | Pldrd_a pid txid =>  data_res_eq (TransactionId txid) dr                                 (**r load float64 as any64 *)
    | Pstrs a pid txid => data_address_sink Mfloat32 a g ars pid dr   \/ data_res_eq (TransactionId txid) dr                                  (**r store float32 *)
    | Pstrd a pid txid =>  data_address_sink Mfloat64 a g ars pid dr   \/ data_res_eq (TransactionId txid) dr                                (**r store float64 *)
    | Pstrd_a a pid txid => data_address_sink Many64 a g ars pid dr  \/ data_res_eq (TransactionId txid) dr                              (**r store float64 as any64 *)
    (** Floating-point move *)
    | Pfmov rd r1 pid => data_res_eq (SingleReg pid rd) dr 
    | Pfmovimms rd f  pid => data_res_eq (SingleReg pid rd) dr \/ data_res_eq (SingleReg pid X16) dr                               (**r load float32 constant *)
    | Pfmovimmd rd f  pid => data_res_eq (SingleReg pid rd) dr  \/ data_res_eq (SingleReg pid X16) dr                               (**r load float64 constant *)
    | Pfmovi fsz rd r1 pid => data_res_eq (SingleReg pid rd) dr                         (**r copy int reg to FP reg *)
    (** Floating-point conversions *)
    | Pfcvtds rd r1  pid => data_res_eq (SingleReg pid rd) dr                                            (**r convert float32 to float64 *)
    | Pfcvtsd rd r1  pid => data_res_eq (SingleReg pid rd) dr                                           (**r convert float64 to float32 *)
    | Pfcvtzs isz fsz rd r1 pid => data_res_eq (SingleReg pid rd) dr            (**r convert float to signed int *)
    | Pfcvtzu isz fsz rd r1 pid => data_res_eq (SingleReg pid rd) dr           (**r convert float to unsigned int *)
    | Pscvtf fsz isz rd r1 pid => data_res_eq (SingleReg pid rd) dr             (**r convert signed int to float *)
    | Pucvtf fsz isz rd r1 pid => data_res_eq (SingleReg pid rd) dr            (**r convert unsigned int to float *)
    (** Floating-point arithmetic *)
    | Pfabs sz rd r1 pid => data_res_eq (SingleReg pid rd) dr                                    (**r absolute value *)
    | Pfneg sz rd r1 pid => data_res_eq (SingleReg pid rd) dr                                    (**r negation *)
    | Pfsqrt sz rd r1 pid => data_res_eq (SingleReg pid rd) dr                                   (**r square root *)
    | Pfadd sz rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                                (**r addition *)
    | Pfdiv sz rd r1 r2  pid => data_res_eq (SingleReg pid rd) dr                                (**r division *)
    | Pfmul sz rd r1 r2  pid => data_res_eq (SingleReg pid rd) dr                               (**r multiplication *)
    | Pfnmul sz rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                               (**r multiply-negate *)
    | Pfsub sz rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                                 (**r subtraction *)
    | Pfmadd sz rd r1 r2 r3 pid => data_res_eq (SingleReg pid rd) dr                             (**r [rd = r3 + r1 * r2] *)
    | Pfmsub sz rd r1 r2 r3 pid => data_res_eq (SingleReg pid rd) dr                             (**r [rd = r3 - r1 * r2] *)
    | Pfnmadd sz rd r1 r2 r3 pid => data_res_eq (SingleReg pid rd) dr                            (**r [rd = - r3 - r1 * r2] *)
    | Pfnmsub sz rd r1 r2 r3 pid => data_res_eq (SingleReg pid rd) dr                           (**r [rd = - r3 + r1 * r2] *)
    | Pfmax sz rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                                (**r maximum *)
    | Pfmin sz rd r1 r2 pid => data_res_eq (SingleReg pid rd) dr                                (**r minimum *)
    (** Floating-point comparison *)
    | Pfcmp sz r1 r2 pid => data_res_eq (SingleReg pid (CR CZ)) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr                                   (**r compare [r1] and [r2] *)
    | Pfcmp0 sz r1 pid => data_res_eq (SingleReg pid (CR CZ)) dr \/ data_res_eq (SingleReg pid CC) dr \/ data_res_eq (SingleReg pid CN) dr \/ data_res_eq (SingleReg pid CV) dr                                       (**r compare [r1] and [+0.0] *)
    (** Floating-point conditional select *)
    | Pfsel rd r1 r2 cond pid => data_res_eq (SingleReg pid rd) dr
    (** Pseudo-instructions *)
    | Pallocframe sz linkofs pid => data_res_eq (SingleReg pid X15) dr \/ data_res_eq (SingleReg pid X16) dr                            (**r allocate new stack frame *)
    | Pfreeframe sz linkofs pid => data_res_eq (SingleReg pid X16) dr                              (**r deallocate stack frame and restore previous frame *)
    | Plabel lbl pid => False                                              (**r define a code label *)
    | Ploadsymbol rd id pid => data_res_eq (SingleReg pid rd) dr                                (**r load the address of [id] *)
    | Pcvtsw2x rd r1 pid => data_res_eq (SingleReg pid rd) dr                                    (**r sign-extend 32-bit int to 64-bit *)
    | Pcvtuw2x rd r1 pid => data_res_eq (SingleReg pid rd) dr                                    (**r zero-extend 32-bit int to 64-bit *)
    | Pcvtx2w rd pid => data_res_eq (SingleReg pid rd) dr                                                 (**r retype a 64-bit int as a 32-bit int *)
    | Pbtbl r1 tbl  pid => data_res_eq (SingleReg pid PC) dr \/ (data_res_eq (SingleReg pid X16) dr)                            (**r N-way branch through a jump table *)
    | Pbuiltin ef args res pid => False (**r built-in function (pseudo) *)
    | Pnop pid => False                                                           (**r no operation *)
    | Pcfi_adjust ofs pid => False                                         (**r .cfi_adjust debug directive *)
    | Pcfi_rel_offset ofs  pid => False                                     (**r .cfi_rel_offset debug directive *)
    | Pincpc pid => data_res_eq (SingleReg pid PC) dr 
    | Memfence pid => match dr with
                    | TransactionId _ => True
                    | _ => False
                    end
    | EarlyAck txid pid =>  data_res_eq (TransactionId txid) dr
    | WriteRequest txid pid a rd c =>  data_res_eq (TransactionId txid) dr
    | ReadRequest txid pid a c=>  data_res_eq (TransactionId txid) dr
    | WriteAck txid pid =>  data_res_eq (TransactionId txid) dr
    | ReadAck r txid pid => data_res_eq (SingleReg pid r) dr \/ data_res_eq (TransactionId txid) dr    
    end.


(*Comparisons disabled for runtime reasons*)
(*Compcert pseudo-instructions disabled - will try to implement them soon*)
Definition disabled_instr(i: instruction): Prop :=
    match i with
    | Pbc _ _ _ => True
    | Pcmpimm _ _ _ _ => True
    | Pcmnimm _ _ _ _ => True
    | Ptstimm _ _ _ _ => True
    | Pcmp _ _ _ _ _ => True
    | Pcmn _ _ _ _ _ => True
    | Pcmpext _ _ _ _ => True
    | Pcmnext _ _ _ _ => True
    | Ptst _ _ _ _ _ => True
    | Pfcmp _ _ _ _ => True
    | Pfcmp0 _ _ _ => True
    | Pallocframe _ _ _ => True
    | Pfreeframe _ _ _ => True
    | Plabel _ _ => True
    | Ploadsymbol _ _ _ => True
    | Pbuiltin _ _ _ _ => True
    | _ => False
    end.

Definition disabled_instrs(i1 i2: instruction): Prop :=
    disabled_instr i1 \/ disabled_instr i2.

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

Lemma hazard_elimination_identity: forall r1, ~(exists r2: data_resource, data_res_eq r1 r2 /\ True)  -> False.
Proof. intros. apply H. exists r1. split. apply data_res_isomorphism. reflexivity. Qed.

Lemma hazard_elimination: forall (d: data_resource), ~ (exists r : data_resource, data_res_eq d r /\ data_res_eq d r) -> False.
Proof. intros. apply H. exists d. split; apply data_res_isomorphism. 
Qed.


 Remark regs_are_different_resources: forall r1 r2 (pid: processor_id),
  ~(exists r : data_resource, data_res_eq (SingleReg pid r1) r /\ data_res_eq (SingleReg pid r2) r) -> r1 <> r2.
 Proof.
 unfold not. intros. apply H. exists (SingleReg pid r1). 
 split. try apply data_res_isomorphism. 
rewrite <- H0; apply data_res_isomorphism.
Qed.

Remark different_procs_different_resources: forall r pid1 pid2, 
~ (exists dr : data_resource, data_res_eq (SingleReg pid1 r) dr /\ data_res_eq (SingleReg pid2 r) dr) -> pid1 <> pid2.
Proof. unfold not. intros. apply H. exists (SingleReg pid1 r). subst. split; apply data_res_isomorphism.
Qed.

Remark different_preg_different_resource: forall r1 r2 pid1 pid2,
~ (exists dr : data_resource, data_res_eq (SingleReg pid1 r1) dr /\ data_res_eq (SingleReg pid2 r2) dr) -> pair pid1 r1 <> pair pid2 r2.
Proof.
intros. unfold not. intro. apply H. exists (SingleReg pid1 r1). split. apply data_res_isomorphism. inversion H0. subst. apply data_res_isomorphism.
Qed.

Remark different_transactions_different_resource: forall txid1 txid2,
~(exists dr: data_resource, data_res_eq (TransactionId txid1) dr /\ data_res_eq (TransactionId txid2) dr) -> txid1 <> txid2.
Proof.
unfold not. intros. apply H. exists (TransactionId txid1). split. apply data_res_isomorphism. subst. apply data_res_isomorphism.
Qed.

Remark split_hazards_generic_l: forall (t: Type)(P Q R: t -> Prop),
(~(exists r : t, P r /\ (Q r \/ R r))) <-> (~ (exists r : t, P r/\ Q r) /\ ~ (exists r : t, P r /\ R r)).
Proof.
intros t P Q R.
split; intros H.
- split. intros [r [HP HX]]. apply H. exists r. split. assumption. left. assumption. 
    intros [r [HP HX]]. apply H. exists r. split. assumption. right. assumption.
-intros [r [HP [HQ | HR]]]; destruct H as [HNQ HNR];
  [ apply HNQ; exists r; split
  | apply HNR; exists r; split]; assumption.
Qed.

Remark split_hazards_generic_r: forall (t: Type)(P Q R: t -> Prop),
~(exists r : t, (Q r \/ R r) /\ P r) <-> ~ (exists r : t, Q r /\ P r) /\ ~ (exists r : t, R r /\ P r).
Proof.
intros t P Q R.
split.
- split. intros [r [HX HP]]. apply H. exists r. split. left. assumption. assumption. 
    intros [r [HX HP]]. apply H. exists r. split. right. assumption. assumption.
- intros [HNQ HNR] [r [[HQ | HR] HPR]];
    [ apply HNQ; exists r; split
    | apply HNR; exists r; split]; assumption.
Qed.

Remark resources_are_different_resources: forall r1 r2,  ~
 (exists r : data_resource, data_res_eq r1 r /\ data_res_eq r2 r) ->  r1 <> r2.
 Proof.
 unfold not. intros. apply H. exists r1. 
 split. try apply data_res_isomorphism. auto. 
  try (rewrite <- H0; apply data_res_isomorphism).
Qed.

Remark tuple_inv_fneq: forall (a c : processor_id) (b d: preg), (a, b) <> (c, d) -> a = c -> b <> d.
intros. unfold not in *. intro. subst. auto.
Qed.
 
Remark tuple_inv_bneq: forall (a c : processor_id) (b d: preg), (a, b) <> (c, d) -> b = d -> a <> c.
intros. unfold not in *. intro. subst. auto.
Qed.
  
Remark tuple_rewrite: forall (a: processor_id) (b d: preg), b = d -> (a, b) = (a, d).
Proof. intros. subst. reflexivity. Qed.

Remark neq_comm: forall (A:Type) (a b: A), a <> b -> b <> a.
Proof.
intros. unfold not in *. intro. apply H. symmetry. apply H0.
Qed.

Remark four_and_shortcut: forall A B C D: Prop, A -> B -> C -> D -> A /\ B /\ C /\ D.
Proof.
intros. split. apply H. split. apply H0. split. apply H1. apply H2.
Qed.

Definition output_data_eq (o1 o2: outcome): Prop := 
    match o1, o2 with
    | MemSimStuck, MemSimStuck => True
    | MemSimStuck, _ => False
    | _, MemSimStuck => False
    | MemSimJumpOut ars1 m1 ifmo1 eaw1, MemSimJumpOut ars2 m2 ifmo2 eaw2 => ars1 = ars2 /\ Mem.mem_extensional m1 m2 /\ ifmo1 = ifmo2 /\ eaw1 = eaw2
    | MemSimNext ars1 m1 ifmo1 eaw1, MemSimNext ars2 m2 ifmo2 eaw2 => ars1 = ars2 /\ Mem.mem_extensional m1 m2 /\ ifmo1 = ifmo2 /\ eaw1 = eaw2
    | MemSimNext ars1 m1 ifmo1 eaw1, MemSimJumpOut ars2 m2 ifmo2 eaw2 => ars1 = ars2 /\ Mem.mem_extensional m1 m2 /\ ifmo1 = ifmo2 /\ eaw1 = eaw2
    | MemSimJumpOut ars1 m1 ifmo1 eaw1, MemSimNext ars2 m2 ifmo2 eaw2 => ars1 = ars2 /\ Mem.mem_extensional m1 m2 /\ ifmo1 = ifmo2 /\ eaw1 = eaw2
    end.

Remark reduce_ors_1: ~(True \/ True) -> False.
Proof. intuition. Qed.

(* we introduced this so that we'd know two txids not conflict with serialization*)
(* if we remove the ability for serializes to permute, then we don't need this. *)
(*at a high level, this means that this serialization is happening in program order*)
Definition input_code_race_free (ifmo: in_flight_mem_ops): Prop := forall (txid1 txid2: mem_transaction_id)(v1 v2 v3 v4: val)(c1 c2: memory_chunk),
    txid1 <> txid2 -> ifmo txid1 = (Some (v1, v3, c1))  -> ifmo txid2 = (Some (v2, v4, c2)) ->  ~(memory_conflict c1 c2 v1 v2).

Remark reduce_ors_2: ~(True \/ False) -> False.
Proof. intuition. Qed.

Remark reduce_ors_3: ~(False \/ True) -> False.
Proof. intuition. Qed.

Remark mem_ne: forall m1 v1 m2 v2 (pid1 pid2: processor_id),
(~ memory_conflict m1 m2 v1 v2) -> (pid1, v1, m1) <> (pid2, v2, m2).
Proof.
intros. unfold not. intro. apply H. unfold memory_conflict. inv H0. destruct v2; try auto. split. reflexivity. unfold not. intro. destruct m2; unfold size_chunk in H0; lia.
Qed.

Definition is_vptr (v: val): Prop := match v with
    | Vptr _ _ => True
    | _ => False
    end.

Remark load_ptrs: forall (v1 v2: val) t m,
    Mem.loadv t m v1 = Some v2 -> is_vptr v1.
Proof.
    intros. unfold Mem.loadv in H. destruct v1; try discriminate H. unfold is_vptr. reflexivity.
Qed.

Remark store_ptrs: forall (v1 v2: val) t m1 m2,
    Mem.storev t m1 v1 v2 = Some m2 -> is_vptr v1.
Proof.
    intros. unfold Mem.storev in H. destruct v1; try discriminate H. unfold is_vptr. reflexivity.
Qed.

Remark mem_chunk_length_sync: forall c v, Datatypes.length (encode_val c v) = size_chunk_nat c.
Proof.
    intros. destruct c; simpl; unfold encode_val; unfold size_chunk_nat; unfold size_chunk; destruct v; simpl; intuition.
Qed.

Remark expand_memory_conflict: forall (c1 c2: memory_chunk) (b1 b2: block) o1 o2,
    ~memory_conflict c1 c2 (Vptr b1 o1) (Vptr b2 o2) -> 
    b1 <> b2  \/ Ptrofs.unsigned o1 + size_chunk c1 <= Ptrofs.unsigned o2 \/ Ptrofs.unsigned o2 + size_chunk c2 <= Ptrofs.unsigned o1.
Proof.
intros. unfold memory_conflict in H. apply not_and_or in H.

destruct H as [bNe | dNe]. left. assumption.
right. lia.
Qed.

Remark output_data_eq_refl: forall o, output_data_eq o o.
Proof.
intros. unfold output_data_eq. destruct o; auto. split. reflexivity. split. apply Mem.mem_self_extensional. auto. split. auto. split. apply Mem.mem_self_extensional. auto.
Qed.

Remark output_data_eq_sym: forall o1 o2, output_data_eq o1 o2 -> output_data_eq o2 o1.
Proof.
intros. unfold output_data_eq in *. destruct o1; destruct o2;  destruct H; try destruct H0; try destruct H1; try apply four_and_shortcut; auto;
unfold Mem.mem_extensional in *; intros; symmetry; apply H0. 
Qed.

Remark destruct_some: forall (A: Type) (a b: A), a = b -> Some a = Some b.
intros. subst. reflexivity.
Qed.

Remark cmpu_valid_ptr: forall m_i m_1 c vc1 vc2 o,
   Val.cmpu_bool (Mem.valid_pointer m_i) c vc1  vc2 = o -> Val.cmpu_bool (Mem.valid_pointer m_1) c vc1 vc2 = o.
Proof.
    intros. unfold Val.cmpu_bool in *. destruct o.
    - destruct vc1; destruct vc2; try discriminate. apply H.
    -destruct vc1; destruct vc2; try reflexivity. apply H. 
Qed.

Ltac convert_pointers H :=
    match type of H with
    | Mem.storev _ _ ?va _ = Some _ => pose H as Hptr; apply store_ptrs in Hptr; destruct va; try discriminate; clear Hptr
    | Mem.loadv _ _ ?va = Some _ => pose H as Hptr; apply load_ptrs in Hptr; destruct va; try discriminate; clear Hptr
    | _ => idtac
    end.

Remark cmplu_valid_ptr: forall m_i m_1 c vc1 vc2 o vwa vwv ch,
   Val.cmplu_bool (Mem.valid_pointer m_i) c vc1  vc2 = o -> 
   Mem.storev ch m_i vwa vwv = Some m_1 -> Val.cmplu_bool (Mem.valid_pointer m_1) c vc1 vc2 = o.
Proof.
    intros. convert_pointers H0.
    unfold Mem.storev in H0.
    unfold Val.cmplu_bool in *. destruct o.
    - destruct vc1; destruct vc2; try discriminate. apply H.
        destruct (negb Archi.ptr64) eqn: n; try discriminate;
        rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m := m_i);
        try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i); assumption.
       
        destruct (negb Archi.ptr64) eqn: n; try discriminate;
        rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m := m_i);
        try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i); assumption.

        destruct (negb Archi.ptr64) eqn: n; try discriminate;
        rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m := m_i);
        try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i); 
        try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i);
        try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i);

        assumption.
    - destruct vc1; destruct vc2; try reflexivity; try discriminate.
    destruct (negb Archi.ptr64) eqn: n; try discriminate;
    rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m := m_i);
    try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i); 
    try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i);
    try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i);
    assumption.

    destruct (negb Archi.ptr64) eqn: n; try discriminate;
    rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m := m_i);
    try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i); 
    try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i);
    try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i);
    assumption.

    destruct (negb Archi.ptr64) eqn: n; try discriminate;
    rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m := m_i);
    try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i); 
    try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i);
    try rewrite <- Mem.store_preserves_valid_ptr_tof with (chunk := ch)(b := b)(ofs := Ptrofs.unsigned i)(v := vwv)(m' := m_1)(m := m_i);
    assumption.
Qed. 

(* Remark different_address_different_resource:  
~(exists r : data_resource, data_res_eq ?d1 r /\ data_res_eq (SingleReg ?pid2 (preg_of_iregsp ?rd2)) r) -> rd1 <> rd2.  *)

(*auxilary ltac that breaks down memory accesses*)
(* ultimately introduces no new subgoals, but proves that two memory accesses are equal*)
Ltac breakdown_mem :=
match goal with
| [ H_tx1: ?ifmo_p ?tx1 = Some (Vptr ?bl ?il, ?vtx0, ?t1),
    H_tx2: ?ifmo_p ?tx2 = Some (Vptr ?bs ?is, ?vtx2, ?c2),
    no_race: forall (txid1 txid2 : mem_transaction_id) (v1 v2 v3 v4 : val)
            (ifmo : in_flight_mem_ops) (c1 c2 : memory_chunk),
            txid1 <> txid2 ->
            ifmo txid1 = Some (v1, v3, c1) ->
            ifmo txid2 = Some (v2, v4, c2) -> ~ memory_conflict c1 c2 v1 v2,
    H_st: Mem.storev ?c2 ?m_i (Vptr ?bs ?is) ?vwv = Some ?m1
         |- Mem.loadv ?t ?m1 (Vptr ?bl ?il) = Mem.loadv ?t ?m_i (Vptr ?bl ?il)]
         =>  apply Mem.ld_str_gso with (v2 := vwv)(b3 := bs)(o3 := is)(t2 := c2); [apply expand_memory_conflict; apply no_race with (txid1 := tx1)(txid2 := tx2)(v3 := vtx0)(v4 := vtx2)(ifmo := ifmo_p); assumption | assumption] 
|   [H_l1: Mem.loadv ?t ?m_i ?v = _, 
    H_l2: Mem.loadv ?t ?m1 ?v = _, 
    H_st: Mem.storev ?t2 ?m_i ?vwa ?vwv = Some ?m1 |- _] => assert (Mem.loadv t m1 v = Mem.loadv t m_i v);
                                                (pose H_l1 as ptr1; apply load_ptrs in ptr1) + (pose H_l2 as ptr1; apply load_ptrs in ptr1); destruct v; try contradiction;
                                            pose H_st as ptr2; apply store_ptrs in ptr2; destruct vwa; try contradiction; [breakdown_mem | idtac]
| _ => idtac
end.

Ltac reorder_solver :=
    match goal with
    | [|-?a = ?a] => reflexivity (*Terminal*)
    | [H_a: ?a |- ?a] => assumption (*Terminal*)
    | [H_not_comm: ?a <> ?b |- ?b <> ?a] => apply neq_comm in H_not_comm; assumption (*Terminal*)
    | [|- Mem.mem_extensional ?m ?m] => apply Mem.mem_self_extensional (*Terminal*)
    (* Boring transitivity*)
    | H_l: ?a = ?b, H_r: context[?a] |- _ => rewrite H_l in H_r; try inversion H_r; subst; reorder_solver (* Nonterminal*)
    | H_l: ?a = ?b |- context[?a] => rewrite H_l; try inversion H_l; subst; reorder_solver (* Nonterminal*)
    (*break apart exists dr statements*)
    | H_das: context[data_address_src] |- _ => unfold data_address_src in H_das; reorder_solver (*Nonterminal*)
    | H_e: ~(exists r : data_resource, data_res_eq ?d r /\ data_res_eq ?d r) |- _ => apply hazard_elimination in H_e; contradiction +  unfold not;  intros;  discriminate H_e (*Terminal*)
    | H_e: ~(exists r : data_resource, data_res_eq ?d r /\ True) |- _ => apply hazard_elimination in H_e; contradiction +  unfold not;  intros;  discriminate H_e (*Terminal*)
    | H_e: ~(exists r : data_resource, _ /\ (_ \/ _)) |- _ => apply split_hazards_generic_l in H_e; destruct H_e; reorder_solver (*Nonterminal*)
    | H_e: ~(exists r : data_resource, (_ \/ _) /\ _) |- _ => apply split_hazards_generic_r in H_e; destruct H_e; reorder_solver (*Nonterminal*)
    | H_e: ~(exists r : data_resource, data_res_eq (SingleReg ?pid1 ?dr) r /\ data_res_eq (SingleReg ?pid2 ?dr) r) |- _ => apply different_procs_different_resources in H_e; reorder_solver(*Nonterminal*)
    | H_e: ~(exists r: data_resource, data_res_eq (TransactionId ?tid1) r /\ data_res_eq (TransactionId ?tid2) r) |- _ => apply different_transactions_different_resource in H_e; reorder_solver(*Nonterminal*)
    | H_e: ~(exists r : data_resource, data_res_eq (SingleReg ?pid1 ?r1) r /\ data_res_eq (SingleReg ?pid2 ?r2) r) |- _ => apply different_preg_different_resource in H_e; reorder_solver(*Nonterminal*)
    | H_e: ~(exists r : data_resource, data_res_eq ?d1 r /\ data_res_eq ?d2 r) |- _ => clear H_e; reorder_solver(*Nonterminal*)
    (* break down str/str conflicts - all terminal*)
     (*potential problem: proof of valid stores requires that eauto correctly matches the newly generated offsets*)
     | [ H_i1:  Mem.storev ?m ?m_i ?v ?v0 = Some ?m0,
     H_i2: Mem.storev ?m1 ?m_i ?v1 ?v2 = Some ?m3,
     H_t1:  Mem.storev ?m1 ?m0 ?v1 ?v2 = Some ?m2,
     H_t2:  Mem.storev ?m ?m3 ?v ?v0 = Some ?m4,
     H_tx1:  ?ifmo_i ?txid = Some (?v, ?v0, ?m),
     H_tx2: ?ifmo_i ?txid0 = Some (?v1, ?v2, ?m1),
     H_mc:  forall (txid1 txid2 : mem_transaction_id) (v1 v2 v3 v4 : val) (ifmo : in_flight_mem_ops)
         (c1 c2 : memory_chunk),
         txid1 <> txid2 ->
         ifmo txid1 = Some (v1, v3, c1) -> ifmo txid2 = Some (v2, v4, c2) -> ~ memory_conflict c1 c2 v1 v2
     |- Mem.mem_extensional ?m2 ?m4] => convert_pointers H_i1; convert_pointers H_i2; 
     eapply Mem.str_str_comm with (t1 := m)(t2 := m1)(m_t1 := m0)(m_t2 := m3)(sv1 := v0)(sv2 := v2)(m_i := m_i); eauto;
     apply expand_memory_conflict; eapply H_mc with (ifmo := ifmo_i)(v3 := v0)(v4 := v2)(txid1 := txid)(txid2 := txid0); auto        
    | [H_contra: Mem.storev ?m ?m3 ?v ?v0 = None,
        H_1: Mem.storev ?m1 ?m_i ?v1 ?v2 = Some ?m3, 
        H_2: Mem.storev ?m ?m_i ?v ?v0 = Some ?m0 |- False] => apply Mem.store_validity with (m := m) (m_i := m_i) (v := v) (v0 := v0) (v1 := v1) (v2 := v2) (m1 := m1) (m0 := m0) (m3 := m3); auto
    | [H_contra: Mem.storev ?m1 ?m0 ?v1 ?v2 = None,
        H_1:  Mem.storev ?m ?m_i ?v ?v0 = Some ?m0, 
        H_2:  Mem.storev ?m1 ?m_i ?v1 ?v2 = Some ?m2 |- False] => apply Mem.store_validity with (m := m1) (m3 := m0)(v := v1)(v0 := v2)(m_i := m_i)(m0 := m2)(m1 := m)(v1 := v)(v2 := v0); auto
    | [H_1: Mem.storev ?m ?m_i ?v ?v0 = Some ?m0, 
        H_contra: Mem.storev ?m1 ?m_i ?v1 ?v2 = None,
        H_2: Mem.storev ?m1 ?m0 ?v1 ?v2 = Some ?m2  |- False] => apply Mem.store_validity_1 with (m := m) (m_i := m_i) (v := v) (v0 := v0) (v1 := v1) (v2 := v2) (m1 := m1) (m0 := m0) (m2 := m2); auto
    | [H_contra: Mem.storev ?m ?m_i ?v ?v0 = None,
        H1:  Mem.storev ?m0 ?m_i ?v1 ?v2 = Some ?m1,
        H2: Mem.storev ?m ?m1 ?v ?v0 = Some ?m2 |- False] => apply Mem.store_validity_1 with (m1 := m)(m_i := m_i)(v1 := v)(v2 := v0)(m := m0)(v := v1)(v0 := v2)(m0 := m1)(m2 := m2); assumption
    (*break down memory operations involving reading from in flight mem*)
    (*this needs to be early as 3-tuples are just nested 2-tuples, so any tuple destruction will kill this*)
    | [H_rc:  forall (txid1 txid2 : mem_transaction_id) (v1 v2 v3 v4 : val)
       (c1 c2 : memory_chunk),
    txid1 <> txid2 ->
    ?ifmo txid1 = Some (v1, v3, c1) ->
    ?ifmo txid2 = Some (v2, v4, c2) -> ~ (memory_conflict c1 c2 v1 v2),
    H_ls: ?ifmo_i ?txid = Some (?v1, ?v5, ?m1),
    H_rs: ?ifmo_i ?txid0 = Some (?v2, ?v6, ?m2)
    |- (_, ?v1, ?m1) <> (_, ?v2, ?m2)] => apply mem_ne;  apply H_rc with (txid1 := txid)(txid2 := txid0)(v3 := v5) (v4 := v6)(ifmo:= ifmo_i); reorder_solver
    
    (*deconstruct vptr - might be able to get rid of this somehow*)
    | H_v: Vptr ?a ?b = Vptr ?c ?d |- _ => inversion H_v; clear H_v; subst; reorder_solver (*Semiterminal*)
    | H_sm: Some ?x = Some ?y |- _ => inversion H_sm; clear H_sm; subst; reorder_solver (*Semiterminal*)
 
    (*deconstruct tuple goals*)
    | [H_ne: ?a <> ?b |- pair ?a _ <> pair ?b _] => apply tuple_fneq; assumption (*Terminal*)
    | [H_ne: ?a <> ?b |- pair _ ?a <> pair _ ?b] => apply tuple_bneq; assumption (*Terminal*)
    | [H_ne: pair ?a ?c <> pair ?b ?c |- ?a <> ?b] => apply tuple_inv_fneq in H_ne; assumption (*Terminal*)
    | [H_ne: pair ?c ?a <> pair ?c ?b |- ?a <> ?b] => apply tuple_inv_bneq in H_ne; assumption (*Terminal*)   
   (* Break apart mem*)
    (* | [ H_rf:  forall (txid1 txid2 : mem_transaction_id) (v1 v2 v3 v4 : val) (ifmo : in_flight_mem_ops),
    txid1 <> txid2 -> ifmo txid1 = Some (v1, v3) -> ifmo txid2 = Some (v2, v4) -> v1 <> v2,
    H1: ?ifmo_i ?txid = Some (?v, ?v0),
    H2: ?ifmo_i ?txid0 = Some (?v4, ?v5) |- (?pid, ?v) <> (?pid0, ?v4)] => assert (v <> v4); try apply H_rf with (txid1 := txid) (txid2 := txid0) (v3 := v0) (v4 := v5)(ifmo := ifmo_i); reorder_solver *)
    (* | [ |- (?pid1 ?v1 ?m1 <> ?pid2 ?v2 ?m2)] => pose  *)
   
    (* More tuple manipulation*)
    | [H_ne: ?b <> ?a |- pair ?a _ <> pair ?b _] => apply neq_comm in H_ne; reorder_solver
    | [H_ne: ?b <> ?a |- pair _ ?a <> pair _ ?b] => apply neq_comm in H_ne; reorder_solver
    | [H_ne: pair ?a _ <> pair ?b _ |- ?a <> ?b] => apply neq_comm; reorder_solver
    | [H_ne: pair _ ?a <> pair _ ?b |- ?a <> ?b] => apply neq_comm; reorder_solver
    | [H_ne: pair ?a ?c <> pair ?b ?c |- _] => apply tuple_inv_bneq in H_ne; reorder_solver
    | [H_ne: pair ?c ?a <> pair ?c ?b |- _] => apply tuple_inv_fneq in H_ne; reorder_solver
    | [ |- pair ?a ?c <> pair ?b ?d] => apply tuple_bneq; unfold not; intro; try discriminate; reorder_solver
    (*Break apart memory*)
    (* | [H1: Some _ = Some ?m1, H2: Some _ = Some ?m2 |- ?m1 = ?m2] => unfold Mem.storev in *; unfold Mem.store in *; destruct matches in *; inv H1; inv H2; reorder_solver *)
    (* Break apart ireg0/iregsp*)
    | [|- context[ir0w _ ?r _]] => unfold ir0w; destruct r; reorder_solver (*Nonterminal*)
    | [|- context[ir0x _ ?r _]] => unfold ir0x; destruct r; reorder_solver (*Nonterminal*)
    (*Handle weird case of all matches not being deconstructed - look into more*)
    | [H_match_cond: ?a = ?b |- context[match ?a with _ => _ end]] => rewrite H_match_cond; reorder_solver (* Nonterminal*)
    (*destruct equivalence conjunctions*)
    | [ |- ?A /\ ?B /\ ?C /\ ?D] => apply four_and_shortcut; try reflexivity; reorder_solver 
    
    (*good for instructions that set multiple regs - only used in PRmap*)
    | [ H_ssw: context[PRmap.set (pair ?pid1 _) _ (PRmap.set (pair ?pid2 _) _ ?m) (pair ?pid1 _)] |- _ ] => rewrite PRmap.ssw in H_ssw; reorder_solver

    (*Break down map updates for all map updating types*)
    (*set commutativity*)
    | [ |- PRmap.set ?k1 ?v1 (PRmap.set ?k2 ?v2 ?mi) = PRmap.set ?k2 ?v2 (PRmap.set ?k1 ?v1 ?mi)] => rewrite PRmap.gscsc; try reflexivity; reorder_solver (*Semiterminal*)
    (* Break down gss*)
    | [ H_raw: context [PRmap.set ?k ?v ?m ?k] |- _] => rewrite PRmap.gss in H_raw; try discriminate; reorder_solver
    (*Break down gso. Need to be very careful with this - it can lead to unbounded recursion*)
    | [ H_raw: context[PRmap.set ?k1 ?v ?map ?k2]  |- _] => rewrite PRmap.gso in H_raw; reorder_solver (* Nonterminal *)
    | [|- PRmap.set ?x ?v3 (PRmap.set ?y ?v4 ( PRmap.set ?z ?v5 (PRmap.set ?q ?v1 (PRmap.set ?w ?v2 ?m)))) = PRmap.set ?q ?v1 (PRmap.set ?w ?v2 (PRmap.set ?x ?v3 (PRmap.set ?y ?v4 (PRmap.set ?z ?v5 ?m))))]=> symmetry; rewrite -> PRmap.gscsc_2of5; reorder_solver
    | [|- PRmap.set ?q ?v1 (PRmap.set ?w ?v2 (PRmap.set ?x ?v3 (PRmap.set ?y ?v4 (PRmap.set ?z ?v5 ?m)))) = PRmap.set ?x ?v3 (PRmap.set ?y ?v4 ( PRmap.set ?z ?v5 (PRmap.set ?q ?v1 (PRmap.set ?w ?v2 ?m))))] => rewrite -> PRmap.gscsc_2of5; reorder_solver
    | [|- PRmap.set ?q ?v1 (PRmap.set ?w ?v2 (PRmap.set ?x ?v3 (PRmap.set ?y ?v4 (PRmap.set ?z ?v5 ?m)))) = PRmap.set ?z ?v5 (PRmap.set ?q ?v1 (PRmap.set ?w ?v2 (PRmap.set ?x ?v3 (PRmap.set ?y ?v4 ?m))))] => rewrite -> PRmap.gscsc_1of5; reorder_solver
    | [|- PRmap.set ?w ?v2 (PRmap.set ?x ?v3 (PRmap.set ?y ?v4 (PRmap.set ?z ?v5 ?m))) = PRmap.set ?z ?v5 (PRmap.set ?w ?v2 (PRmap.set ?x ?v3 (PRmap.set ?y ?v4 ?m)))] => rewrite -> PRmap.gscsc_1of4; reorder_solver
    | [|- PRmap.set ?A ?v1 (PRmap.set ?B ?v2 (PRmap.set ?C ?v3 ?mi)) = PRmap.set ?C ?v3 (PRmap.set ?A ?v1 (PRmap.set ?B ?v2 ?mi))] => rewrite <- PRmap.gscsc_ext; try reflexivity; reorder_solver (* Nonterminal*)
    | [|- PRmap.set ?A ?v1 (PRmap.set ?B ?v2 (PRmap.set ?C ?v3 ?mi)) = PRmap.set ?B ?v2 (PRmap.set ?C ?v3 (PRmap.set ?A ?v1 ?mi))] => symmetry; rewrite <- PRmap.gscsc_ext; try reflexivity; reorder_solver (* Nonterminal*)
    | [|- PRmap.set ?w ?v2 (PRmap.set ?x ?v3 (PRmap.set ?y ?v4 (PRmap.set ?z ?v5 ?m))) = PRmap.set ?y ?v4 (PRmap.set ?z ?v5 (PRmap.set ?w ?v2 (PRmap.set ?x ?v3 ?m)))] => rewrite <- PRmap.gscsc_2of4; try reflexivity; reorder_solver (* Nonterminal*)  
    | [|- context[PRmap.set ?k1 _ ?map ?k2]] => rewrite PRmap.gso; reorder_solver (* Nonterminal *)
    (*set commutativity*)
    | [ |- Trmap.set ?k1 ?v1 (Trmap.set ?k2 ?v2 ?mi) = Trmap.set ?k2 ?v2 (Trmap.set ?k1 ?v1 ?mi)] => rewrite Trmap.gscsc; try reflexivity; reorder_solver (*Semiterminal*)
    (* Break down gss*)
    | [ H_raw: context [Trmap.set ?k ?v ?m ?k] |- _] => rewrite Trmap.gss in H_raw; try discriminate; reorder_solver
    (*Break down gso. Need to be very careful with this - it can lead to unbounded recursion*)
    | [ H_raw: context[Trmap.set ?k1 ?v ?map ?k2]  |- _] => rewrite Trmap.gso in H_raw; reorder_solver (* Nonterminal *)
    | [|- Trmap.set ?x ?v3 (Trmap.set ?y ?v4 ( Trmap.set ?z ?v5 (Trmap.set ?q ?v1 (Trmap.set ?w ?v2 ?m)))) = Trmap.set ?q ?v1 (Trmap.set ?w ?v2 (Trmap.set ?x ?v3 (Trmap.set ?y ?v4 (Trmap.set ?z ?v5 ?m))))]=> symmetry; rewrite -> Trmap.gscsc_2of5; reorder_solver
    | [|- Trmap.set ?q ?v1 (Trmap.set ?w ?v2 (Trmap.set ?x ?v3 (Trmap.set ?y ?v4 (Trmap.set ?z ?v5 ?m)))) = Trmap.set ?x ?v3 (Trmap.set ?y ?v4 ( Trmap.set ?z ?v5 (Trmap.set ?q ?v1 (Trmap.set ?w ?v2 ?m))))] => rewrite -> Trmap.gscsc_2of5; reorder_solver
    | [|- Trmap.set ?q ?v1 (Trmap.set ?w ?v2 (Trmap.set ?x ?v3 (Trmap.set ?y ?v4 (Trmap.set ?z ?v5 ?m)))) = Trmap.set ?z ?v5 (Trmap.set ?q ?v1 (Trmap.set ?w ?v2 (Trmap.set ?x ?v3 (Trmap.set ?y ?v4 ?m))))] => rewrite -> Trmap.gscsc_1of5; reorder_solver
    | [|- Trmap.set ?w ?v2 (Trmap.set ?x ?v3 (Trmap.set ?y ?v4 (Trmap.set ?z ?v5 ?m))) = Trmap.set ?z ?v5 (Trmap.set ?w ?v2 (Trmap.set ?x ?v3 (Trmap.set ?y ?v4 ?m)))] => rewrite -> Trmap.gscsc_1of4; reorder_solver
    | [|- Trmap.set ?A ?v1 (Trmap.set ?B ?v2 (Trmap.set ?C ?v3 ?mi)) = Trmap.set ?C ?v3 (Trmap.set ?A ?v1 (Trmap.set ?B ?v2 ?mi))] => rewrite <- Trmap.gscsc_ext; try reflexivity; reorder_solver (* Nonterminal*)
    | [|- Trmap.set ?A ?v1 (Trmap.set ?B ?v2 (Trmap.set ?C ?v3 ?mi)) = Trmap.set ?B ?v2 (Trmap.set ?C ?v3 (Trmap.set ?A ?v1 ?mi))] => symmetry; rewrite <- Trmap.gscsc_ext; try reflexivity; reorder_solver (* Nonterminal*)
    | [|- Trmap.set ?w ?v2 (Trmap.set ?x ?v3 (Trmap.set ?y ?v4 (Trmap.set ?z ?v5 ?m))) = Trmap.set ?y ?v4 (Trmap.set ?z ?v5 (Trmap.set ?w ?v2 (Trmap.set ?x ?v3 ?m)))] => rewrite <- Trmap.gscsc_2of4; try reflexivity; reorder_solver (* Nonterminal*)  
    | [|- context[Trmap.set ?k1 _ ?map ?k2]] => rewrite Trmap.gso; reorder_solver (* Nonterminal *)

    (*set commutativity*)
    | [ |- EWmap.set ?k1 ?v1 (EWmap.set ?k2 ?v2 ?mi) = EWmap.set ?k2 ?v2 (EWmap.set ?k1 ?v1 ?mi)] => rewrite EWmap.gscsc; try reflexivity; reorder_solver (*Semiterminal*)
    (* Break down gss*)
    | [ H_raw: context [EWmap.set ?k ?v ?m ?k] |- _] => rewrite EWmap.gss in H_raw; try discriminate; reorder_solver
    (*Break down gso. Need to be very careful with this - it can lead to unbounded recursion*)
    | [ H_raw: context[EWmap.set ?k1 ?v ?map ?k2]  |- _] => rewrite EWmap.gso in H_raw; reorder_solver (* Nonterminal *)
    | [|- EWmap.set ?x ?v3 (EWmap.set ?y ?v4 ( EWmap.set ?z ?v5 (EWmap.set ?q ?v1 (EWmap.set ?w ?v2 ?m)))) = EWmap.set ?q ?v1 (EWmap.set ?w ?v2 (EWmap.set ?x ?v3 (EWmap.set ?y ?v4 (EWmap.set ?z ?v5 ?m))))]=> symmetry; rewrite -> EWmap.gscsc_2of5; reorder_solver
    | [|- EWmap.set ?q ?v1 (EWmap.set ?w ?v2 (EWmap.set ?x ?v3 (EWmap.set ?y ?v4 (EWmap.set ?z ?v5 ?m)))) = EWmap.set ?x ?v3 (EWmap.set ?y ?v4 ( EWmap.set ?z ?v5 (EWmap.set ?q ?v1 (EWmap.set ?w ?v2 ?m))))] => rewrite -> EWmap.gscsc_2of5; reorder_solver
    | [|- EWmap.set ?q ?v1 (EWmap.set ?w ?v2 (EWmap.set ?x ?v3 (EWmap.set ?y ?v4 (EWmap.set ?z ?v5 ?m)))) = EWmap.set ?z ?v5 (EWmap.set ?q ?v1 (EWmap.set ?w ?v2 (EWmap.set ?x ?v3 (EWmap.set ?y ?v4 ?m))))] => rewrite -> EWmap.gscsc_1of5; reorder_solver
    | [|- EWmap.set ?w ?v2 (EWmap.set ?x ?v3 (EWmap.set ?y ?v4 (EWmap.set ?z ?v5 ?m))) = EWmap.set ?z ?v5 (EWmap.set ?w ?v2 (EWmap.set ?x ?v3 (EWmap.set ?y ?v4 ?m)))] => rewrite -> EWmap.gscsc_1of4; reorder_solver
    | [|- EWmap.set ?A ?v1 (EWmap.set ?B ?v2 (EWmap.set ?C ?v3 ?mi)) = EWmap.set ?C ?v3 (EWmap.set ?A ?v1 (EWmap.set ?B ?v2 ?mi))] => rewrite <- EWmap.gscsc_ext; try reflexivity; reorder_solver (* Nonterminal*)
    | [|- EWmap.set ?A ?v1 (EWmap.set ?B ?v2 (EWmap.set ?C ?v3 ?mi)) = EWmap.set ?B ?v2 (EWmap.set ?C ?v3 (EWmap.set ?A ?v1 ?mi))] => symmetry; rewrite <- EWmap.gscsc_ext; try reflexivity; reorder_solver (* Nonterminal*)
    | [|- EWmap.set ?w ?v2 (EWmap.set ?x ?v3 (EWmap.set ?y ?v4 (EWmap.set ?z ?v5 ?m))) = EWmap.set ?y ?v4 (EWmap.set ?z ?v5 (EWmap.set ?w ?v2 (EWmap.set ?x ?v3 ?m)))] => rewrite <- EWmap.gscsc_2of4; try reflexivity; reorder_solver (* Nonterminal*)  
    | [|- context[EWmap.set ?k1 _ ?map ?k2]] => rewrite EWmap.gso; reorder_solver (* Nonterminal *)
    (*different comparisons*)
    | [H1: Val.cmplu_bool (Mem.valid_pointer ?m1) ?b ?c ?d = ?o1,
       H2: Val.cmplu_bool (Mem.valid_pointer ?m2) ?b ?c ?d = ?o2,
       H_set: Mem.storev ?t ?m1 ?sa ?sv = Some ?m2 |- _] => apply cmplu_valid_ptr with (m_i := m1)(m_1 := m2) (vwa := sa) (vwv := sv)(ch := t)  in H1; reorder_solver
    | [H1: Val.cmpu_bool (Mem.valid_pointer ?m1) ?b ?c ?d = ?o1,
       H2: Val.cmpu_bool (Mem.valid_pointer ?m2) ?b ?c ?d = ?o2 |- _] => apply cmpu_valid_ptr with (m_1 := m2) in H1; reorder_solver
    (*call auxilary mewory ltac*)
    | [H_l1: Mem.loadv ?t ?m_i ?v = _, 
    H_l2: Mem.loadv ?t ?m1 ?v = _, 
    H_st: Mem.storev ?t2 ?m_i ?vwa ?vwv = Some ?m1 |- _] => breakdown_mem; reorder_solver
    | _ => try reflexivity
end.

(* Remark cmpu_valid_ptr: forall m_i m_1 c vc1 vc2 vsa vsv b t,
    Mem.storev t m_i vsa vsv = Some m_1 -> Val.cmpu_bool (Mem.valid_pointer m_i) c vc1  vc2 = Some b -> Val.cmpu_bool (Mem.valid_pointer m_1) c vc1 vc2 = Some b.
Proof.
    intros. destruct vc1; destruct vc2;
    unfold Val.cmpu_bool in *; try discriminate. apply H0.
Qed. *)




Ltac disable_cmps :=
    match goal with
    | [H_test: ~disabled_instrs ?i1 ?i2 |- _] => unfold disabled_instrs in H_test; unfold disabled_instr in H_test; try apply reduce_ors_1 in H_test; try apply reduce_ors_2 in H_test; try apply reduce_ors_3 in H_test; try contradiction
    end.

Theorem reorder: forall g (f: function)(i1 i2: instruction) (ars_i: allregsets) (m_i: mem) (eaw_i: early_ack_writes) (ifmo_i: in_flight_mem_ops),
     ~data_dependence i1 i2 g ars_i -> ~disabled_instrs i1 i2 -> input_code_race_free ifmo_i ->
     output_data_eq ( eval_memsim_instr g f i2  (eval_memsim_instr g f i1 (MemSimNext ars_i m_i ifmo_i eaw_i))) (eval_memsim_instr g f i1  (eval_memsim_instr g f i2  (MemSimNext ars_i m_i ifmo_i eaw_i))).
Proof. intros. 
(* Definition unwrapping*)
unfold data_dependence in H. unfold data_sink, data_source in H. apply not_or_or_and in H. destruct H.  destruct H2. destruct i1.
(* verified: gotos, lds, strs, ews, requests, acks*)
Focus 131.
destruct i2.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
auto.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.

disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.
disable_cmps; unfold output_data_eq; unfold input_code_race_free in *; unfold eval_memsim_instr; unfold eval_memsim_instr_internal; unfold eval_testcond; unfold goto_label; unfold serialize_read; unfold read_ack; unfold serialize_write; unfold write_ack; unfold compare_int; unfold compare_float; unfold compare_long; unfold compare_single; unfold read_request;  unfold early_ack_write; unfold eval_addressing; unfold eval_testzero; unfold iregz_same_resource in *; destruct matches; reorder_solver.







Qed. 