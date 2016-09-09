(* Coq 8.5pl2. *)

Require Import Ascii.
Require Import String.
Require Import List.
Require Import FMapInterface.
Require Import NArith.

Module Lang.

  (* TODO: sort by opcode *)
  Inductive instr := (** partial.  adding those necessary. *)
  (* 0s *)
  | STOP
  | ADD
  | MUL
  | SUB
  | DIV
  | SDIV
  | MOD
  | SMOD
  | ADDMOD
  | MULMOD
  | EXP
  | SIGNEXTEND
  (* 10s *)
  | LT
  | GT
  | SLT
  | SGT
  | EQ
  | ISZERO
  | AND
  | OR
  | XOR
  | NOT
  | BYTE
  (* 20s *)
  | SHA3
  (* 30s *)
  | ADDRESS
  | BALANCE
  | ORIGIN
  | CALLER
  | CALLVALUE
  | CALLDATALOAD
  | CALLDATASIZE
  | CALLDATACOPY
  | CODESIZE
  | CODECOPY
  | GASPRICE
  | EXTCODESIZE
  | EXTCODECOPY
  (* 40s *)
  | BLOCKHASH
  | COINBASE
  | TIMESTAMP
  | NUMBER
  | DIFFICULTY
  | GASLIMIT
  (* 50s *)
  | POP
  | MLOAD
  | MSTORE
  | MSTORE8
  | SLOAD
  | SSTORE
  | JUMP
  | JUMPI
  | PC
  | MSIZE
  | GAS
  | JUMPDEST
  (* 60s, 70s *)
  | PUSH_N : (* pushed value in hex with 0x *) string -> instr
  (* 80s *)
  | DUP1
  | DUP2
  | DUP3
  | DUP4
  | DUP5
  | DUP6
  | DUP7
  | DUP8
  | DUP9
  | DUP10
  | DUP11
  | DUP12
  | DUP13
  | DUP14
  | DUP15
  | DUP16
  (* 90s *)
  | SWAP1
  | SWAP2
  | SWAP3
  | SWAP4
  | SWAP5
  | SWAP6
  | SWAP7
  | SWAP8
  | SWAP9
  | SWAP10
  | SWAP11
  | SWAP12
  | SWAP13
  | SWAP14
  | SWAP15
  | SWAP16
  (* a0s *)
  | LOG0
  | LOG1
  | LOG2
  | LOG3
  | LOG4
  (* f0s *)
  | CREATE
  | CALL
  | CALLCODE
  | RETURN
  (* | DELEGATECALL *)
  | SUICIDE
  | UNKNOWN : string -> instr
  .

  Fixpoint string_half_len str :=
    match str with
    | String _ (String _ tl) => S (string_half_len tl)
    | _ => O
    end.

  Definition instr_length (i : instr) : nat :=
    match i with
    | PUSH_N str => string_half_len str
    | _ => 1
    end.

  Require Import Coq.Program.Wf.

  Fixpoint drop_bytes (prog : list instr) (bytes : nat) {struct bytes} :=
    match prog, bytes with
    | _, O => prog
    | PUSH_N str :: tl, S pre =>
      drop_bytes tl (pre - (string_half_len str - 1))
    | _ :: tl, S pre =>
      drop_bytes tl pre
    | nil, S _ => nil
    end.

  Open Scope N_scope.
  Fixpoint program_bytes (prog : list instr) : N :=
    match prog with
    | nil => 0
    | PUSH_N str :: tl =>
      (N.of_nat (string_half_len str) - 1) +
      program_bytes tl
    | _ :: tl =>
      1 + program_bytes tl
    end.
  Close Scope N_scope.

  Inductive decoding_mode : Set :=
  | first_zero
  | first_x
  | next_instr
  | read_0
  | read_1
  | read_2
  | read_3
  | read_4
  | read_5
  | read_6
  | read_7
  | read_8
  | read_9
  | read_a
  | read_b
  | read_c
  | read_d
  | read_e
  | read_f
  | read_hex : nat (* remaining read, after the next char *)
               -> list ascii (* read so far in reverse *) -> decoding_mode
  .

  Inductive decode_result : Set :=
  | decode_success : list instr -> decode_result
  | decode_failure : string     -> decode_result
  .

  Close Scope string_scope.
  Open Scope char_scope.
  Definition rev0x : list ascii := "x" :: "0" :: nil.
  Fixpoint rev_string_inner (lst : list ascii) (acc : string): string :=
    match lst with
    | nil => acc
    | hd :: tl => rev_string_inner tl (String hd acc)
    end.

  Definition rev_string lst := rev_string_inner lst EmptyString.

  (* sofar accumulates instructions in the reverse order *)

  Open Scope string_scope.

  Fixpoint decode_inner (str : string) (m : decoding_mode)
           (sofar : list instr): decode_result :=
  let after_0 (error_message : string) :=
      match str with
      | String "0" rest => decode_inner rest next_instr (STOP :: sofar)
      | String "1" rest => decode_inner rest next_instr (ADD  :: sofar)
      | String "2" rest => decode_inner rest next_instr (MUL  :: sofar)
      | String "3" rest => decode_inner rest next_instr (SUB  :: sofar)
      | String "4" rest => decode_inner rest next_instr (DIV  :: sofar)
      | String "5" rest => decode_inner rest next_instr (SDIV :: sofar)
      | String "6" rest => decode_inner rest next_instr (MOD  :: sofar)
      | String "7" rest => decode_inner rest next_instr (SMOD :: sofar)
      | String "8" rest => decode_inner rest next_instr (ADDMOD :: sofar)
      | String "9" rest => decode_inner rest next_instr (MULMOD :: sofar)
      | String "a" rest => decode_inner rest next_instr (EXP :: sofar)
      | String "b" rest => decode_inner rest next_instr (SIGNEXTEND :: sofar)
      | String "c" rest => decode_inner rest next_instr (UNKNOWN  "0c" :: sofar)
      | String "d" rest => decode_inner rest next_instr (UNKNOWN  "0d" :: sofar)
      | String "e" rest => decode_inner rest next_instr (UNKNOWN  "0e" :: sofar)
      | String "f" rest => decode_inner rest next_instr (UNKNOWN  "0f" :: sofar)
      | _ => decode_failure error_message
      end in
  match m with
  | first_zero =>
    match str with
    | String "0" rest => decode_inner rest first_x sofar
    | String "1" rest => decode_inner rest read_1 sofar
    | String "2" rest => decode_inner rest read_2 sofar
    | String "3" rest => decode_inner rest read_3 sofar
    | String "4" rest => decode_inner rest read_4 sofar
    | String "5" rest => decode_inner rest read_5 sofar
    | String "6" rest => decode_inner rest read_6 sofar
    | String "7" rest => decode_inner rest read_7 sofar
    | String "8" rest => decode_inner rest read_8 sofar
    | String "9" rest => decode_inner rest read_9 sofar
    | String "a" rest => decode_inner rest read_a sofar
    | String "b" rest => decode_inner rest read_b sofar
    | String "c" rest => decode_inner rest read_c sofar
    | String "d" rest => decode_inner rest read_d sofar
    | String "e" rest => decode_inner rest read_e sofar
    | String "f" rest => decode_inner rest read_f sofar
    | _ => decode_failure "first nonzero"
    end
  | first_x =>
    match str with
    | String "x" rest => decode_inner rest next_instr sofar
    (* since we are not reading x, 0 must have been first byte of the code*)
    | _ => after_0 "second character not x nor hex digit"
    end
  | next_instr =>
    match str with
    | String "0" rest => decode_inner rest read_0 sofar
    | String "1" rest => decode_inner rest read_1 sofar
    | String "2" rest => decode_inner rest read_2 sofar
    | String "3" rest => decode_inner rest read_3 sofar
    | String "4" rest => decode_inner rest read_4 sofar
    | String "5" rest => decode_inner rest read_5 sofar
    | String "6" rest => decode_inner rest read_6 sofar
    | String "7" rest => decode_inner rest read_7 sofar
    | String "8" rest => decode_inner rest read_8 sofar
    | String "9" rest => decode_inner rest read_9 sofar
    | String "a" rest => decode_inner rest read_a sofar
    | String "b" rest => decode_inner rest read_b sofar
    | String "c" rest => decode_inner rest read_c sofar
    | String "d" rest => decode_inner rest read_d sofar
    | String "e" rest => decode_inner rest read_e sofar
    | String "f" rest => decode_inner rest read_f sofar
    | EmptyString => decode_success (List.rev sofar)
    | _ => decode_failure "?"
    end
  | read_0 => after_0 "0?"
  | read_1 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (LT     :: sofar)
    | String "1" rest => decode_inner rest next_instr (GT     :: sofar)
    | String "2" rest => decode_inner rest next_instr (SLT    :: sofar)
    | String "3" rest => decode_inner rest next_instr (SGT    :: sofar)
    | String "4" rest => decode_inner rest next_instr (EQ     :: sofar)
    | String "5" rest => decode_inner rest next_instr (ISZERO :: sofar)
    | String "6" rest => decode_inner rest next_instr (AND    :: sofar)
    | String "7" rest => decode_inner rest next_instr (OR     :: sofar)
    | String "8" rest => decode_inner rest next_instr (XOR    :: sofar)
    | String "9" rest => decode_inner rest next_instr (NOT    :: sofar)
    | String "a" rest => decode_inner rest next_instr (BYTE   :: sofar)
    | String "b" rest => decode_failure "1b"
    | String "c" rest => decode_failure "1c"
    | String "d" rest => decode_failure "1d"
    | String "e" rest => decode_failure "1e"
    | String "f" rest => decode_failure "1f"
    | _ => decode_failure "1?"
    end
  | read_2 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (SHA3  :: sofar)
    | String "7" rest => decode_inner rest next_instr (UNKNOWN "27" :: sofar)
    | String _ rest => decode_inner rest next_instr (UNKNOWN "2?" :: sofar)
    | _ => decode_failure "2$"
    end
  | read_3 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (ADDRESS :: sofar)
    | String "1" rest => decode_inner rest next_instr (BALANCE :: sofar)
    | String "2" rest => decode_inner rest next_instr (ORIGIN :: sofar)
    | String "3" rest => decode_inner rest next_instr (CALLER :: sofar)
    | String "4" rest => decode_inner rest next_instr (CALLVALUE :: sofar)
    | String "5" rest => decode_inner rest next_instr (CALLDATALOAD :: sofar)
    | String "6" rest => decode_inner rest next_instr (CALLDATASIZE :: sofar)
    | String "7" rest => decode_inner rest next_instr (CALLDATACOPY :: sofar)
    | String "8" rest => decode_inner rest next_instr (CODESIZE :: sofar)
    | String "9" rest => decode_inner rest next_instr (CODECOPY :: sofar)
    | String "a" rest => decode_inner rest next_instr (GASPRICE :: sofar)
    | String "b" rest => decode_inner rest next_instr (EXTCODESIZE :: sofar)
    | String "c" rest => decode_inner rest next_instr (EXTCODECOPY :: sofar)
    | String "d" rest => decode_inner rest next_instr (UNKNOWN "3d" :: sofar)
    | String "e" rest => decode_inner rest next_instr (UNKNOWN "3e" :: sofar)
    | String "f" rest => decode_inner rest next_instr (UNKNOWN "3f" :: sofar)
    | _ => decode_failure "3?"
    end
  | read_4 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (BLOCKHASH :: sofar)
    | String "1" rest => decode_inner rest next_instr (COINBASE :: sofar)
    | String "2" rest => decode_inner rest next_instr (TIMESTAMP :: sofar)
    | String "3" rest => decode_inner rest next_instr (NUMBER :: sofar)
    | String "4" rest => decode_inner rest next_instr (DIFFICULTY :: sofar)
    | String "5" rest => decode_inner rest next_instr (GASLIMIT :: sofar)
    | String "6" rest => decode_failure "46"
    | String "7" rest => decode_failure "47"
    | String "8" rest => decode_failure "48"
    | String "9" rest => decode_failure "49"
    | String "a" rest => decode_failure "4a"
    | String "b" rest => decode_failure "4b"
    | String "c" rest => decode_inner rest next_instr (UNKNOWN "4c" :: sofar)
    | String "d" rest => decode_failure "4d"
    | String "e" rest => decode_failure "4e"
    | String "f" rest => decode_failure "4f"
    | _ => decode_failure "4?"
    end
  | read_5 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (POP :: sofar)
    | String "1" rest => decode_inner rest next_instr (MLOAD :: sofar)
    | String "2" rest => decode_inner rest next_instr (MSTORE :: sofar)
    | String "3" rest => decode_inner rest next_instr (MSTORE8 :: sofar)
    | String "4" rest => decode_inner rest next_instr (SLOAD :: sofar)
    | String "5" rest => decode_inner rest next_instr (SSTORE :: sofar)
    | String "6" rest => decode_inner rest next_instr (JUMP :: sofar)
    | String "7" rest => decode_inner rest next_instr (JUMPI :: sofar)
    | String "8" rest => decode_inner rest next_instr (PC :: sofar)
    | String "9" rest => decode_inner rest next_instr (MSIZE :: sofar)
    | String "a" rest => decode_inner rest next_instr (GAS :: sofar)
    | String "b" rest => decode_inner rest next_instr (JUMPDEST :: sofar)
    | String "c" rest => decode_failure "5c"
    | String "d" rest => decode_failure "5d"
    | String "e" rest => decode_failure "5e"
    | String "f" rest => decode_failure "5f"
    | _ => decode_failure "5?"
    end
  | read_6 =>
    match str with
    | String "0" rest => decode_inner rest (read_hex 2 rev0x)  sofar
    | String "1" rest => decode_inner rest (read_hex 4 rev0x)  sofar
    | String "2" rest => decode_inner rest (read_hex 6 rev0x)  sofar
    | String "3" rest => decode_inner rest (read_hex 8 rev0x)  sofar
    | String "4" rest => decode_inner rest (read_hex 10 rev0x) sofar
    | String "5" rest => decode_inner rest (read_hex 12 rev0x) sofar
    | String "6" rest => decode_inner rest (read_hex 14 rev0x) sofar
    | String "7" rest => decode_inner rest (read_hex 16 rev0x) sofar
    | String "8" rest => decode_inner rest (read_hex 18 rev0x) sofar
    | String "9" rest => decode_inner rest (read_hex 20 rev0x) sofar
    | String "a" rest => decode_inner rest (read_hex 22 rev0x) sofar
    | String "b" rest => decode_inner rest (read_hex 24 rev0x) sofar
    | String "c" rest => decode_inner rest (read_hex 26 rev0x) sofar
    | String "d" rest => decode_inner rest (read_hex 28 rev0x) sofar
    | String "e" rest => decode_inner rest (read_hex 30 rev0x) sofar
    | String "f" rest => decode_inner rest (read_hex 32 rev0x) sofar
    | _ => decode_failure "6?"
    end
  | read_7 =>
    match str with
    | String "0" rest => decode_inner rest (read_hex 34 rev0x) sofar
    | String "1" rest => decode_inner rest (read_hex 36 rev0x) sofar
    | String "2" rest => decode_inner rest (read_hex 38 rev0x) sofar
    | String "3" rest => decode_inner rest (read_hex 40 rev0x) sofar
    | String "4" rest => decode_inner rest (read_hex 42 rev0x) sofar
    | String "5" rest => decode_inner rest (read_hex 44 rev0x) sofar
    | String "6" rest => decode_inner rest (read_hex 46 rev0x) sofar
    | String "7" rest => decode_inner rest (read_hex 48 rev0x) sofar
    | String "8" rest => decode_inner rest (read_hex 50 rev0x) sofar
    | String "9" rest => decode_inner rest (read_hex 52 rev0x) sofar
    | String "a" rest => decode_inner rest (read_hex 54 rev0x) sofar
    | String "b" rest => decode_inner rest (read_hex 56 rev0x) sofar
    | String "c" rest => decode_inner rest (read_hex 58 rev0x) sofar
    | String "d" rest => decode_inner rest (read_hex 60 rev0x) sofar
    | String "e" rest => decode_inner rest (read_hex 62 rev0x) sofar
    | String "f" rest => decode_inner rest (read_hex 64 rev0x) sofar
    | _ => decode_failure "7?"
    end
  | read_8 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (DUP1  :: sofar)
    | String "1" rest => decode_inner rest next_instr (DUP2  :: sofar)
    | String "2" rest => decode_inner rest next_instr (DUP3  :: sofar)
    | String "3" rest => decode_inner rest next_instr (DUP4  :: sofar)
    | String "4" rest => decode_inner rest next_instr (DUP5  :: sofar)
    | String "5" rest => decode_inner rest next_instr (DUP6  :: sofar)
    | String "6" rest => decode_inner rest next_instr (DUP7  :: sofar)
    | String "7" rest => decode_inner rest next_instr (DUP8  :: sofar)
    | String "8" rest => decode_inner rest next_instr (DUP9  :: sofar)
    | String "9" rest => decode_inner rest next_instr (DUP10 :: sofar)
    | String "a" rest => decode_inner rest next_instr (DUP11 :: sofar)
    | String "b" rest => decode_inner rest next_instr (DUP12 :: sofar)
    | String "c" rest => decode_inner rest next_instr (DUP13 :: sofar)
    | String "d" rest => decode_inner rest next_instr (DUP14 :: sofar)
    | String "e" rest => decode_inner rest next_instr (DUP15 :: sofar)
    | String "f" rest => decode_inner rest next_instr (DUP16 :: sofar)
    | _ => decode_failure "8?"
    end
  | read_9 =>
    match str with
    | String "0" rest => decode_inner rest next_instr (SWAP1  :: sofar)
    | String "1" rest => decode_inner rest next_instr (SWAP2  :: sofar)
    | String "2" rest => decode_inner rest next_instr (SWAP3  :: sofar)
    | String "3" rest => decode_inner rest next_instr (SWAP4  :: sofar)
    | String "4" rest => decode_inner rest next_instr (SWAP5  :: sofar)
    | String "5" rest => decode_inner rest next_instr (SWAP6  :: sofar)
    | String "6" rest => decode_inner rest next_instr (SWAP7  :: sofar)
    | String "7" rest => decode_inner rest next_instr (SWAP8  :: sofar)
    | String "8" rest => decode_inner rest next_instr (SWAP9  :: sofar)
    | String "9" rest => decode_inner rest next_instr (SWAP10 :: sofar)
    | String "a" rest => decode_inner rest next_instr (SWAP11 :: sofar)
    | String "b" rest => decode_inner rest next_instr (SWAP12 :: sofar)
    | String "c" rest => decode_inner rest next_instr (SWAP13 :: sofar)
    | String "d" rest => decode_inner rest next_instr (SWAP14 :: sofar)
    | String "e" rest => decode_inner rest next_instr (SWAP15 :: sofar)
    | String "f" rest => decode_inner rest next_instr (SWAP16 :: sofar)
    | _ => decode_failure "9?"
    end
  | read_a =>
    match str with
    | String "0" rest => decode_inner rest next_instr (LOG0 :: sofar)
    | String "1" rest => decode_inner rest next_instr (LOG1 :: sofar)
    | String "2" rest => decode_inner rest next_instr (LOG2 :: sofar)
    | String "3" rest => decode_inner rest next_instr (LOG3 :: sofar)
    | String "4" rest => decode_inner rest next_instr (LOG4 :: sofar)
    | String "5" rest => decode_failure "a5"
    | String "6" rest => decode_failure "a6"
    | String "7" rest => decode_failure "a7"
    | String "8" rest => decode_failure "a8"
    | String "9" rest => decode_inner rest next_instr (UNKNOWN "a9" :: sofar)
    | String "a" rest => decode_failure "aa"
    | String "b" rest => decode_failure "ab"
    | String "c" rest => decode_inner rest next_instr (UNKNOWN "ac" :: sofar)
    | String "d" rest => decode_failure "ad"
    | String "e" rest => decode_failure "ae"
    | String "f" rest => decode_failure "af"
    | _ => decode_failure "a?"
    end
  | read_b =>
    match str with
      | String _ rest => decode_inner rest next_instr (UNKNOWN "b?" :: sofar)
      | EmptyString => decode_failure "b$"
    end
  | read_c =>
    match str with
      | String _ rest => decode_inner rest next_instr (UNKNOWN "c?" :: sofar) 
      | EmptyString => decode_failure "c$"
    end
  | read_d =>
    match str with
    | String _ rest => decode_inner rest next_instr (UNKNOWN "e?" :: sofar)
    | EmptyString => decode_failure "d$"
    end
  | read_e =>
    match str with
    | String "0" rest => decode_inner rest next_instr (UNKNOWN "e0" :: sofar)
    | String "9" rest => decode_inner rest next_instr (UNKNOWN "e9" :: sofar)
    | String _ rest   => decode_inner rest next_instr (UNKNOWN "e?" :: sofar)
    | EmptyString => decode_failure "e$"
    end
  | read_f =>
    match str with
    | String "0" rest => decode_inner rest next_instr (CREATE :: sofar)
    | String "1" rest => decode_inner rest next_instr (CALL :: sofar)
    | String "2" rest => decode_inner rest next_instr (CALLCODE :: sofar)
    | String "3" rest => decode_inner rest next_instr (RETURN :: sofar)
    | String "4" rest => decode_inner rest next_instr (UNKNOWN "f4" :: sofar)
    | String "5" rest => decode_inner rest next_instr (UNKNOWN "f5" :: sofar)
    | String "6" rest => decode_inner rest next_instr (UNKNOWN "f6" :: sofar)
    | String "7" rest => decode_inner rest next_instr (UNKNOWN "f7" :: sofar)
    | String "8" rest => decode_inner rest next_instr (UNKNOWN "f8" :: sofar)
    | String "9" rest => decode_inner rest next_instr (UNKNOWN "f9" :: sofar)
    | String "a" rest => decode_inner rest next_instr (UNKNOWN "fa" :: sofar)
    | String "b" rest => decode_inner rest next_instr (UNKNOWN "fb" :: sofar)
    | String "c" rest => decode_inner rest next_instr (UNKNOWN "fc" :: sofar)
    | String "d" rest => decode_inner rest next_instr (UNKNOWN "fd" :: sofar)
    | String "e" rest => decode_inner rest next_instr (UNKNOWN "fe" :: sofar)
    | String "f" rest => decode_inner rest next_instr (SUICIDE :: sofar)
    | _ => decode_failure "f?"
    end
  | read_hex O acc => decode_failure "should not happen"
  | read_hex (S O) acc =>
    match str with
    | EmptyString =>  decode_success (List.rev sofar) (*decode_failure "end_of_string reading hex" *)
    | String c rest =>
      decode_inner rest next_instr (PUSH_N (rev_string (c :: acc)) :: sofar)
    end
  | read_hex (S pre) acc =>
    match str with
    | EmptyString =>  decode_success (List.rev sofar) (* decode_failure "end_of_string reading hex" *)
    | String c rest =>
      decode_inner rest (read_hex pre (c :: acc)) sofar
    end
  end
  .
  (* Question: Is there a need to decode further after a failure *)

  Definition decode (code : string) : decode_result :=
    decode_inner code first_zero nil.



  Open Scope string_scope.


  Open Scope char_scope.
  Close Scope nat_scope.
  Open Scope N_scope.

  Definition read_hex_char (c : ascii) : option N :=
    match c with
    | "0" => Some 0
    | "1" => Some 1
    | "2" => Some 2
    | "3" => Some 3
    | "4" => Some 4
    | "5" => Some 5
    | "6" => Some 6
    | "7" => Some 7
    | "8" => Some 8
    | "9" => Some 9
    | "a" => Some 10
    | "b" => Some 11
    | "c" => Some 12
    | "d" => Some 13
    | "e" => Some 14
    | "f" => Some 15
    | _   => None
    end.

  Fixpoint read_str_hex (carry: N) (str : string) : N :=
    match str with
    | EmptyString => carry
    | String c rest =>
      match read_hex_char c with
      | None => 0
      | Some num => read_str_hex (carry * 16 + num) rest
      end
    end.

  Definition literal_to_nat (str : string) : N :=
    match str with
    | String "0" (String "x" rest) => read_str_hex 0 rest
    | _ => 0
    end.


End Lang.


Module AbstractEVM.

  Definition a_pc := N. (* program counter *)
  Definition a_hex := string.

  (* a_word stands for abstract world *)
  Inductive a_word :=
  | Acaller : a_word
  | Aorigin : a_word
  | Agas_price : a_word
  | Ablock_number : a_word
  | Acoinbase : a_word
  | Ablockhash : a_word
  | Atime : a_word
  | Adatasize : a_word
  | Avalue : a_word
  | Aaddress : a_word
  | Abalance : a_word
  | Adifficulty : a_word
  | Agaslimit : a_word
  | Aextcodesize : a_word -> a_word
  | Aimm_nat : N -> a_word
  | Aunknown : string -> a_word (* whatever that might change during execution *)
  | Ais_zero : a_word -> a_word
  | Azero : a_word
  | Asub : a_word -> a_word -> a_word
  | Aadd : a_word -> a_word -> a_word
  | Aand : a_word -> a_word -> a_word
  | Abyte : a_word -> a_word -> a_word
  | Aor : a_word -> a_word -> a_word
  | Axor : a_word -> a_word -> a_word
  | Aexp : a_word -> a_word -> a_word
  | Adiv : a_word -> a_word -> a_word
  | Amul : a_word -> a_word -> a_word
  | Agt  : a_word -> a_word -> a_word
  | Asdiv : a_word -> a_word -> a_word
  | Amod : a_word -> a_word -> a_word
  | Asmod : a_word -> a_word -> a_word
  | Asignextend : a_word -> a_word -> a_word
  | Anot : a_word -> a_word
  | Asha3 : a_memory -> a_word
  | Alt  : a_word -> a_word -> a_word
  | Aslt : a_word -> a_word -> a_word
  | Aeq  : a_word -> a_word -> a_word
  | Aget32 : a_word -> a_memory -> a_word (* Aget32 addr mem *)
  | Aget_storage : a_word -> a_storage -> a_word
  with a_memory :=
  | Aempty : a_memory
  | Aput32 : a_word -> a_word -> a_memory -> a_memory
  (* Aput32 addr val orig represents the result of a one-word write. *)
  | Aput1 : a_word -> a_word -> a_memory -> a_memory
  (* Aput1 addr val orig represents the result of a one-byte write.
   * Actually (val mod 256) is written.
   *)
  | Amemwrite : a_word -> a_word -> a_memory -> a_memory -> a_memory
  (* Amemwrite start_addr len source mem represents the result of memwrite.  source [0..len - 1] is copied to mem[start_addr.. start_addr + len - 1]. *)
  | Adata : a_memory
  (* Adata represents the input data. *)
  | Adrop : a_word -> a_memory -> a_memory
  (* Adrop n mem is the result of dropping the first n bytes and shifting forward. *)
  | Atake : a_word -> a_word -> a_memory -> a_memory
  (* Atake n size mem takes size bytes from position n *)
  | Acodecopy : a_word -> a_word -> a_word -> a_memory -> a_memory
  (* Acodecopy base_in_memory base_in_code len orig *)
  | Amem_imm : string -> a_memory
  with a_storage :=
  | Ainitial_storage : a_storage
  | Aput_storage : a_word -> a_word -> a_storage -> a_storage
  .

  Fixpoint simplify_above (addr : N) (mem : a_memory) :=
    match mem with
    | Aput32 (Aimm_nat w) val orig =>
      if N.leb addr w then simplify_above addr orig
      else
        Aput32 (Aimm_nat w) val (simplify_above addr orig)
    | _ => mem
    end.

  Fixpoint simplify_below (addr : N) (mem : a_memory) :=
    match mem with
    | Aput32 (Aimm_nat w) val orig =>
      if N.leb (w + 32) addr then simplify_below addr orig
      else
        Aput32 (Aimm_nat w) val (simplify_below addr orig)
    | _ => mem
    end.

  Definition Atake' start size mem :=
    match start, size with
    | Aimm_nat st, Aimm_nat si =>
      Atake start size
            (simplify_below st (simplify_above (st + si) mem))
    | _, _ =>
      Atake start size mem
    end.

  Definition Aadd' (a : a_word) (b : a_word) :=
    match a, b with
    | Aimm_nat m, Aimm_nat n => Aimm_nat (m + n)
    | _, _ => Aadd a b
    end.

  Definition Asub' (a : a_word) (b : a_word) :=
    match a, b with
    | Aimm_nat m, Aimm_nat n => Aimm_nat (m - n)
    | _, _ => Asub a b
    end.

  Definition Aexp' (a : a_word) (b : a_word) :=
    match a, b with
    | Aimm_nat m, Aimm_nat n => Aimm_nat (N.pow m n)
    | _, _ => Aexp a b
    end.

  Close Scope nat_scope.

  Fixpoint Aget32' (addr : a_word) (mem : a_memory) : a_word :=
    match addr, mem with
    | Aimm_nat n, Aput32 (Aimm_nat w) v orig =>
      if orb (N.leb 32 (n - w)) (N.leb 32 (w - n)) then
        Aget32' addr orig
      else if (N.eqb n w) then v else Aget32 addr mem
    | _, _ => Aget32 addr mem
    end.

  Fixpoint forget32 addr orig :=
    match addr, orig with
    | Aimm_nat w, Aput32 (Aimm_nat p) v pre =>
      if (N.eqb w p) then
        forget32 addr pre
      else
        Aput32 (Aimm_nat p) v (forget32 addr pre)
    | _, _ => orig
    end.

  Fixpoint Aput32' (addr : a_word) (val : a_word) (orig : a_memory) : a_memory :=
    Aput32 addr val (forget32 addr orig).

  Definition Aimm (hex : a_hex) : a_word :=
    Aimm_nat (Lang.literal_to_nat hex).

  Definition a_stack := list a_word.

  Inductive a_prop :=
  | is_zero : a_word -> a_prop
  | is_not_zero : a_word -> a_prop
  .

  Definition a_operation := a_stack -> a_memory ->
                            list (list a_prop * option (a_stack * a_memory)).

  (* [ (condition1, None = failure ); (condition2, Some (post_stack, post_memory)) ] *)

  Require Import List.
  Open Scope N_scope.

  Definition simple_result {T} (x : T) := (@nil a_prop, x) :: nil.

  Definition a_push_x (data : a_word) : a_operation :=
    fun s mem => simple_result (Some (data :: s, mem)).

  Definition a_pop : a_operation :=
    fun s mem =>
      match s with
        | nil => simple_result None
        | hd :: tl => simple_result (Some (tl, mem))
      end.

  Definition a_mstore : a_operation :=
    fun s mem =>
      match s with
      | nil => simple_result None
      | _ :: nil => simple_result None
      | a :: b :: l => simple_result (Some (l, Aput32' a b mem))
      end.

  (* TODO: use Aput1' instead of Aput1.  See Aput32'. *)
  Definition a_mstore8 : a_operation :=
    fun s mem =>
      match s with
      | nil => simple_result None
      | _ :: nil => simple_result None
      | a :: b :: l => simple_result (Some (l, Aput1 a b mem))
      end.

  Definition a_mload : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | nil => None
        | addr :: l =>
          Some (Aget32' addr mem :: l, mem)
      end.

  Definition a_gas : a_operation :=
    fun s mem =>
      simple_result (Some (Aunknown "remaining gas" :: s, mem)).

  Definition a_msize : a_operation :=
    fun s mem =>
      simple_result (Some (Aunknown "memory size" :: s, mem)).

  Definition a_calldatasize : a_operation :=
    fun s mem =>
      simple_result (Some (Adatasize :: s, mem)).

  Definition a_callvalue : a_operation :=
    fun s mem =>
      simple_result (Some (Avalue :: s, mem)).
  Definition a_address : a_operation :=
    fun s mem =>
      simple_result (Some (Aaddress :: s, mem)).
  Definition a_balance : a_operation :=
    fun s mem =>
      simple_result (Some (Abalance :: s, mem)).

  Definition a_calldatacopy : a_operation :=
    fun s mem =>
      simple_result
        match s with
        | m0 :: m1 :: m2 :: l =>
          Some (l, Amemwrite m0 m2 (Adrop m1 Adata) mem)
        | _ => None
        end.

  Definition a_codecopy : a_operation :=
    fun s mem =>
      simple_result
        match s with
        | m0 :: m1 :: m2 :: l =>
          Some (l, Acodecopy m0 m1 m2 mem)
        | _ => None
        end.

  Definition a_iszero : a_operation :=
    fun s mem =>
      simple_result
        match s with
        | nil => None
        | h :: tl =>
          Some (Ais_zero h :: tl, mem)
        end.

  Definition a_two_two_op (f : a_word -> a_word -> (a_word * a_word)) : a_operation :=
    fun s mem =>
      simple_result
        match s with
        | a :: b :: l =>
          Some (fst (f a b) :: snd (f a b) :: l, mem)
        | _ => None
      end.

  Definition a_two_one_op (f : a_word -> a_word -> a_word) : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | nil => None
        | _ :: nil => None
        | a :: b :: l => Some ((f a b) :: l, mem)
      end.

  Definition a_three_one_op (f : a_word -> a_word -> a_word -> a_word)
    : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | nil => None
        | _ :: nil => None
        | _ :: _ :: nil => None
        | a :: b :: c :: l => Some ((f a b c) :: l, mem)
      end.

  Definition a_exp_op : a_operation := a_two_one_op Aexp'.

  Definition a_and_op : a_operation := a_two_one_op Aand.
  Definition a_or_op : a_operation := a_two_one_op Aor.
  Definition a_byte_op : a_operation := a_two_one_op Abyte.
  Definition a_xor_op : a_operation := a_two_one_op Axor.

  Definition a_one_one_op (f : a_word -> a_word) : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | nil => None
        | a :: l => Some (f a :: l, mem)
      end.

  Definition a_sload storage : a_operation :=
    a_one_one_op (fun addr => Aget_storage addr storage).

  Definition a_calldataload : a_operation :=
    a_one_one_op (fun n => Aget32' n Adata).

  Definition a_div_op := a_two_one_op Adiv.
  Definition a_mul_op := a_two_one_op Amul.
  Definition a_add_op := a_two_one_op Aadd'.
  Definition a_sdiv_op := a_two_one_op Asdiv.
  Definition a_mod_op := a_two_one_op Amod.
  Definition a_addmod_op := a_three_one_op
                              (fun a b c =>
                                 Amod (Aadd' a b) c).
  Definition a_mulmod_op := a_three_one_op
                              (fun a b c =>
                                 Amod (Amul a b) c).
  Definition a_smod_op := a_two_one_op Asmod.
  Definition a_signextend_op := a_two_one_op Asignextend.

  Definition a_dup1 : a_operation :=
    fun s mem =>
    simple_result
      match s with
        | a :: l => Some (a :: a :: l, mem)
        | _ => None (* really? *)
      end.

  Definition a_dup2 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: l => Some (b :: a :: b :: l, mem)
        | _ => None
      end.

  Definition a_dup3 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: l => Some (c :: a :: b :: c :: l, mem)
        | _ => None
      end.

  Definition a_dup4 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: l => Some (d :: a :: b :: c :: d :: l, mem)
        | _ => None
      end.

  Fixpoint nth_opt {A} (n : nat) (lst : list A) :=
    match n, lst with
    | S O, hd :: _ => Some hd
    | S pre, _ :: tl => nth_opt pre tl
    | _, _ => None
    end.

  Definition stack_dup n (s : a_stack) :=
    match nth_opt n s with
    | Some elm => Some (elm :: s)
    | None => None
    end.


  Definition a_dup_n (n : nat) : a_operation :=
    fun s mem =>
      simple_result
      match stack_dup n s with
      | Some new_s => Some (new_s, mem)
      | None => None
      end.

  Definition a_eq_op : a_operation := a_two_one_op
    (fun a b => Aeq a b).

  Definition a_gt_op : a_operation := a_two_one_op
    (fun a b => Agt a b).

  Definition a_slt_op : a_operation := a_two_one_op Aslt.
  Definition a_sgt_op : a_operation :=
    a_two_one_op (fun a b => Aslt b a).

  Definition a_not_op : a_operation := a_one_one_op Anot.
  Definition a_extcodesize : a_operation := a_one_one_op Aextcodesize.

  Definition a_sha3 : a_operation :=
    fun s mem =>
      simple_result
        match s with
        | st :: size :: rest =>
          Some (Asha3 (Atake' st size mem) :: rest, mem)
        | _ => None
        end.

  Definition a_lt_op : a_operation := a_two_one_op
    (fun a b => Alt a b).

  Definition a_sub_op : a_operation := a_two_one_op Asub'.

  Definition a_swap1 : a_operation := a_two_two_op (fun a b => (b, a)).

  Definition a_swap2 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: l =>
          Some (c :: b :: a :: l, mem)
        | _ => None
      end.

  Definition a_swap3 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: l =>
          Some (d :: b :: c :: a :: l, mem)
        | _ => None
      end.

  Definition a_swap4 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: l =>
          Some (e :: b :: c :: d :: a :: l, mem)
        | _ => None
      end.

  Definition a_swap5 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: l =>
          Some (f :: b :: c :: d :: e :: a :: l, mem)
        | _ => None
      end.

  Definition a_swap6 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: g :: l =>
          Some (g :: b :: c :: d :: e :: f :: a :: l, mem)
        | _ => None
      end.

  Definition a_swap7 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: g :: h :: l =>
          Some (h :: b :: c :: d :: e :: f :: g :: a :: l, mem)
        | _ => None
      end.

  Definition a_swap8 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: g :: h :: i :: l =>
          Some (i :: b :: c :: d :: e :: f :: g :: h :: a :: l, mem)
        | _ => None
      end.

  Definition a_swap9 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: l =>
          Some (j :: b :: c :: d :: e :: f :: g :: h :: i :: a :: l, mem)
        | _ => None
      end.

  Definition a_swap10 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l =>
          Some (k :: b :: c :: d :: e :: f :: g :: h :: i :: j :: a :: l, mem)
        | _ => None
      end.

  Definition a_swap11 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m =>
          Some (l :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: a :: m, mem)
        | _ => None
      end.

  Definition a_swap12 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: X :: rest =>
          Some (X :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: a :: rest, mem)
        | _ => None
      end.

  Definition a_swap13 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: X :: rest =>
          Some (X :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: a :: rest, mem)
        | _ => None
      end.

  Definition a_swap14 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: X :: rest =>
          Some (X :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: a :: rest, mem)
        | _ => None
      end.

  Definition a_swap15 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: X :: rest =>
          Some (X :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: a :: rest, mem)
        | _ => None
      end.

  Definition a_swap16 : a_operation :=
    fun s mem =>
      simple_result
      match s with
        | a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: p :: X :: rest =>
          Some (X :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: m :: n :: o :: p :: a :: rest, mem)
        | _ => None
      end.

  Record a_log_entry :=
    { a_log_address : a_word
    ; a_log_topics : list a_word
    ; a_log_data : a_memory
    }.

  Definition a_logs := list a_log_entry.

  Record a_state :=
    { a_stc : a_stack
    ; a_mem : a_memory
    ; a_str : a_storage
    ; a_log : a_logs
    ; a_prg_sfx : list Lang.instr
    ; a_program : list Lang.instr
    ; a_program_code : string
    }.

  Record a_call :=
    { a_call_gaslimit   : a_word
    ; a_call_code       : a_word
    ; a_call_recipient  : a_word
    ; a_call_value      : a_word
    ; a_call_data_begin : a_word
    ; a_call_data_size  : a_word
    ; a_call_output_dst : a_word
    ; a_call_output_max : a_word
    ; a_call_pre        : a_state
    }.

  Record a_create :=
    { a_create_value : a_word
    ; a_create_mem_start : a_word
    ; a_create_mem_size  : a_word
    }.

  Record a_extcode_copy :=
    { a_extcode_copy_addr : a_word
    ; a_extcode_copy_memory_start : a_word
    ; a_extcode_copy_code_start : a_word
    ; a_extcode_copy_len : a_word
    }.

  Inductive a_single_result :=
  | continue : a_state -> a_single_result
  | suicide  : a_word (* who gets the balance *) -> a_single_result
  | returned : a_memory (* output *) -> a_state -> a_single_result
  | stopped  : a_state -> a_single_result
  | calling  : a_call -> a_single_result
  | creating : a_create -> a_single_result
  | extcode_copying : a_extcode_copy -> a_single_result
  | end_of_program : a_state -> a_single_result (* what actually happens? *)
  | failure :  a_state -> a_single_result (* what actually happens? *)
  | not_implemented : Lang.instr -> a_state -> a_single_result
  | decode_fail : string -> a_single_result
  | back_jmp : a_state -> a_single_result
  .


  Open Scope type_scope.

  Definition a_result := (list (list a_prop * a_single_result) * N).
  (* the second element is the length of the list *)

  Fixpoint for_all_pairs {A : Type} (lst : list A) (rel : A -> A -> bool) :=
    match lst with
    | nil => true
    | hd :: tl =>
      if (forallb (rel hd) tl) then
        (for_all_pairs tl rel)
      else false
    end.

  Definition same_cond_same_val a_word_eq : (a_prop -> a_prop -> bool) :=
    fun a b =>
    match a, b with
    | is_zero _, is_zero _ => true
    | is_not_zero _, is_not_zero _ => true
    | is_zero a, is_not_zero b => negb (a_word_eq a b)
    | is_not_zero a, is_zero b => negb (a_word_eq a b)
    end.

  Definition compat_conds a_word_eq (c : list a_prop * a_single_result) :=
    match c with
    | (lst, _) => for_all_pairs lst (same_cond_same_val a_word_eq)
    end.

  Definition cond_incompat a_word_eq a b:=
    negb (same_cond_same_val a_word_eq a b).

  Close Scope type_scope.



  Open Scope N_scope.

  Fixpoint len {A} (lst : list A) :=
    match lst with
    | nil => 0
    | hd :: tl =>
      1 + (len tl)
    end.

  Definition a_result_from_list lst : a_result :=
    (lst, len lst).

  Definition a_operation_sem (op : a_operation) (pre: a_state) : a_result :=
    match pre.(a_prg_sfx) with
      | nil => ((nil, end_of_program pre) :: nil, 0)
      | _ :: tl =>
        a_result_from_list (
        map
            (fun cond_opt =>
               match cond_opt with
               | (cond, None) => (cond, failure pre)
               | (cond, Some (s,m)) =>
                 (cond,
                  continue {| a_stc := s ;
                              a_mem := m ;
                              a_str := pre.(a_str) ;
                              a_log := pre.(a_log) ;
                              a_program := pre.(a_program);
                              a_prg_sfx := tl;
                              a_program_code := pre.(a_program_code)
                           |})
               end)
            (op pre.(a_stc) pre.(a_mem)))
    end.

  Fixpoint take_n {A} (n : nat) (lst : list A) : option (list A * list A) :=
    match n, lst with
    | O, _ => Some (nil, lst)
    | S n', hd :: tl =>
      match take_n n' tl with
      | Some (heads, tails) => Some (hd :: heads, tails)
      | None => None
      end
    | S n', nil => None
    end.

  Definition a_log_n (n : nat) (pre : a_state) : a_result :=
    match pre.(a_prg_sfx) with
    | nil => ((nil, failure pre) :: nil, 1)
    | _ :: prg_tl =>
      match pre.(a_stc) with
      | start :: size :: tl =>
        match take_n n tl with
        | None => ((nil, failure pre) :: nil, 1)
        | Some (heads, tails) =>
          ((nil,
           continue {| a_stc := tails;
                       a_mem := pre.(a_mem);
                       a_str := pre.(a_str);
                       a_log :=
                         {|
                           a_log_address := Aaddress;
                           a_log_topics := heads;
                           a_log_data := Atake' start size pre.(a_mem)
                         |} :: pre.(a_log); (* XXX: log is cons'ed, not appended at the end!!! *)
                       a_program := pre.(a_program);
                       a_program_code := pre.(a_program_code);
                       a_prg_sfx := prg_tl
                    |}) :: nil, 1)
        end
      | _ => ((nil, failure pre) :: nil, 1)
      end
    end.

  Definition a_noop (pre : a_state) : a_result :=
    match pre.(a_prg_sfx) with
    | nil => ((nil, end_of_program pre) :: nil, 1)
    | _ :: tl =>
      ((nil,
       continue {| a_stc := pre.(a_stc);
                  a_mem := pre.(a_mem);
                  a_str := pre.(a_str);
                  a_log := pre.(a_log);
                  a_program := pre.(a_program);
                  a_program_code := pre.(a_program_code);
                  a_prg_sfx := tl
               |}) :: nil, 1)
    end.

  Definition a_reader (f : a_state -> a_word) (pre : a_state) : a_result :=
    match pre.(a_prg_sfx) with
      | nil => ((nil, end_of_program pre) :: nil, 1)
      | _ :: tl =>
        ((nil, continue {| a_stc := f pre :: pre.(a_stc) ;
                    a_mem := pre.(a_mem) ;
                    a_str := pre.(a_str) ;
                    a_log := pre.(a_log) ;
                    a_program := pre.(a_program);
                    a_program_code := pre.(a_program_code);
                    a_prg_sfx := tl
                 |}) :: nil, 1)
    end.

  Import Lang.

  Definition comp {A B C} (g : B -> C) (f : A -> B) := fun x => (g (f x)).

  Close Scope string_scope.

  Definition simple_result' x := a_result_from_list (simple_result x).

  Definition a_instr_sem (i : instr) : a_state -> a_result :=
    match i with
      | STOP => (fun pre => ((nil, stopped pre) :: nil, 1))
      | ADD => a_operation_sem a_add_op
      | MUL => a_operation_sem a_mul_op
      | SUB => a_operation_sem a_sub_op
      | DIV => a_operation_sem a_div_op
      | SDIV => a_operation_sem a_sdiv_op
      | MOD => a_operation_sem a_mod_op
      | SMOD => a_operation_sem a_smod_op
      | ADDMOD => a_operation_sem a_addmod_op
      | MULMOD => a_operation_sem a_mulmod_op
      | SIGNEXTEND => a_operation_sem a_signextend_op
      | EXP => a_operation_sem a_exp_op
      | GT  => a_operation_sem a_gt_op
      | LT  => a_operation_sem a_lt_op
      | SLT => a_operation_sem a_slt_op
      | SGT => a_operation_sem a_sgt_op
      | EQ => a_operation_sem a_eq_op
      | AND => a_operation_sem a_and_op
      | OR  => a_operation_sem a_or_op
      | XOR => a_operation_sem a_xor_op
      | NOT => a_operation_sem a_not_op
      | BYTE => a_operation_sem a_byte_op
      | ISZERO => a_operation_sem a_iszero
      | GAS    => a_reader (fun _ => Aunknown "remaining_gas")
      | CALLER => a_reader (fun _ => Acaller)
      | CALLVALUE => a_reader (fun _ => Avalue)
      | CALLDATALOAD => a_operation_sem a_calldataload
      | CALLDATASIZE => a_operation_sem a_calldatasize
      | CALLDATACOPY => a_operation_sem a_calldatacopy
      | BALANCE => a_operation_sem a_balance
      | ADDRESS => a_operation_sem a_address
      | TIMESTAMP => a_reader (fun _ => Atime)
      | POP =>    a_operation_sem a_pop
      | MLOAD  => a_operation_sem a_mload
      | MSTORE => a_operation_sem a_mstore
      | MSTORE8 => a_operation_sem a_mstore8
      | SLOAD => (fun pre => a_operation_sem (a_sload pre.(a_str)) pre)
      | SSTORE => (fun pre =>
                     simple_result'
                     match pre.(a_stc) with
                     | nil => failure pre
                     | _ :: nil => failure pre
                     | addr :: val :: stl =>
                       match pre.(a_prg_sfx) with
                       | nil => failure pre
                       | _ :: cont =>
                         continue {|
                             a_stc := stl;
                             a_mem := pre.(a_mem);
                             a_str := Aput_storage addr val pre.(a_str);
                             a_log := pre.(a_log);
                             a_program := pre.(a_program);
                             a_program_code := pre.(a_program_code);
                             a_prg_sfx := cont
                           |}
                       end
                     end)
      | JUMP => (fun pre =>
                   simple_result'
                   match pre.(a_stc) with
                   | nil => failure pre
                   | Aimm_nat jmp :: tl =>
(*                     if NPeano.leb
                          (List.length pre.(a_prg_sfx))
                          (List.length (drop_bytes pre.(a_program) (literal_to_nat jmp)))
                     then
                       back_jmp pre
                     else *)
                     continue {|
                       a_stc := tl;
                       a_mem := pre.(a_mem);
                       a_str := pre.(a_str);
                       a_log := pre.(a_log);
                       a_program := pre.(a_program);
                       a_program_code := pre.(a_program_code);
                       a_prg_sfx := drop_bytes pre.(a_program) (N.to_nat jmp)
                     |}
                   | _ => not_implemented i pre
                   end
                )
      | JUMPI => (fun pre =>
                    match pre.(a_stc) with
                    | nil => simple_result' (failure pre)
                    | hd::nil => simple_result' (failure pre)
                    | Aimm_nat dst :: cond :: tl_stc =>
                      a_result_from_list
                        ((is_zero cond :: nil,
                        match pre.(a_prg_sfx) with
                        | nil => failure pre
                        | _ :: tl =>
                          continue {|
                              a_stc := tl_stc;
                              a_mem := pre.(a_mem);
                              a_str := pre.(a_str);
                              a_log := pre.(a_log);
                              a_program := pre.(a_program);
                              a_program_code := pre.(a_program_code);
                              a_prg_sfx := tl
                            |}
                        end)
                        ::
                        (is_not_zero cond :: nil,
(*                         if NPeano.leb
                              (List.length pre.(a_prg_sfx))
                              (List.length (drop_bytes pre.(a_program) (literal_to_nat dst)))
                         then
                           back_jmp pre
                         else *)
                        continue {|
                            a_stc := tl_stc;
                            a_mem := pre.(a_mem);
                            a_str := pre.(a_str);
                            a_log := pre.(a_log);
                            a_program := pre.(a_program);
                            a_program_code := pre.(a_program_code);
                            a_prg_sfx := drop_bytes pre.(a_program) (N.to_nat dst)
                          |})
                        :: nil)
                    | _ => simple_result' (not_implemented i pre)
                    end)
      | JUMPDEST =>
        (fun pre => match pre.(a_prg_sfx) with
                      | nil => simple_result' (failure pre)
                      | _ :: tl =>
                        simple_result' (
                        continue {|
                            a_stc := pre.(a_stc);
                            a_mem := pre.(a_mem);
                            a_str := pre.(a_str);
                            a_log := pre.(a_log);
                            a_program := pre.(a_program);
                            a_program_code := pre.(a_program_code);
                            a_prg_sfx := tl
                            |} )
                    end)
      | PUSH_N str => a_operation_sem (a_push_x (Aimm str))
      | DUP1 => a_operation_sem a_dup1
      | DUP2 => a_operation_sem a_dup2
      | DUP3 => a_operation_sem a_dup3
      | DUP4 => a_operation_sem a_dup4
      | DUP5 => a_operation_sem (a_dup_n 5)
      | DUP6 => a_operation_sem (a_dup_n 6)
      | DUP7 => a_operation_sem (a_dup_n 7)
      | DUP8 => a_operation_sem (a_dup_n 8)
      | DUP9 => a_operation_sem (a_dup_n 9)
      | DUP10 => a_operation_sem (a_dup_n 10)
      | DUP11 => a_operation_sem (a_dup_n 11)
      | DUP12 => a_operation_sem (a_dup_n 12)
      | DUP13 => a_operation_sem (a_dup_n 13)
      | DUP14 => a_operation_sem (a_dup_n 14)
      | DUP15 => a_operation_sem (a_dup_n 15)
      | DUP16 => a_operation_sem (a_dup_n 16)
      | SWAP1 => a_operation_sem a_swap1
      | SWAP2 => a_operation_sem a_swap2
      | SWAP3 => a_operation_sem a_swap3
      | SWAP4 => a_operation_sem a_swap4
      | SWAP5 => a_operation_sem a_swap5
      | SWAP6 => a_operation_sem a_swap6
      | SWAP7 => a_operation_sem a_swap7
      | SWAP8 => a_operation_sem a_swap8
      | SWAP9 => a_operation_sem a_swap9
      | SWAP10 => a_operation_sem a_swap10
      | SWAP11 => a_operation_sem a_swap11
      | SWAP12 => a_operation_sem a_swap12
      | SWAP13 => a_operation_sem a_swap13
      | SWAP14 => a_operation_sem a_swap14
      | SWAP15 => a_operation_sem a_swap15
      | SWAP16 => a_operation_sem a_swap16
      | LOG0 => a_log_n 0
      | LOG1 => a_log_n 1
      | LOG2 => a_log_n 2
      | LOG3 => a_log_n 3
      | LOG4 => a_log_n 4
      | CALL =>
        (fun pre =>
           simple_result'
        match pre.(a_stc) with
        | e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: rest =>
         calling {| a_call_gaslimit := e0
           ; a_call_code   := e1
           ; a_call_recipient := e1
           ; a_call_value    := e2
           ; a_call_data_begin :=  e3
           ; a_call_data_size  :=  e4
           ; a_call_output_dst :=  e5
           ; a_call_output_max :=  e6
           ; a_call_pre := pre (* TODO: maybe remove the seven stack elements already *)
          |}
        | _ => failure pre
        end)
      | CREATE =>
        (fun pre =>
           simple_result'
             match pre.(a_stc) with
             | value :: mem_start :: mem_size :: rest =>
               creating {|
                     a_create_value := value
                   ; a_create_mem_start := mem_start
                   ; a_create_mem_size := mem_size
                 |}
             | _ => failure pre
             end
        )
      | CALLCODE =>
        (fun pre =>
           simple_result'
        match pre.(a_stc) with
        | e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: rest =>
         calling {| a_call_gaslimit := e0
           ; a_call_code   := e1
           ; a_call_recipient := Aaddress
           ; a_call_value    := e2
           ; a_call_data_begin :=  e3
           ; a_call_data_size  :=  e4
           ; a_call_output_dst :=  e5
           ; a_call_output_max :=  e6
           ; a_call_pre := pre (* TODO: maybe remove the seven stack elements already *)
          |}
        | _ => failure pre
        end)
      | RETURN =>
        (fun pre =>
           simple_result'
             match pre.(a_stc) with
               | start :: size :: rest =>
                 returned (Atake' start size pre.(a_mem)) pre
               | _ =>
                 failure pre
             end)
      | SUICIDE => (fun pre =>
                      simple_result'
                      match pre.(a_stc) with
                        | nil => failure pre
                        | hd :: _ => suicide hd
                      end
                   )
      | CODECOPY => a_operation_sem a_codecopy
      | SHA3 => a_operation_sem a_sha3
      | ORIGIN => a_reader (fun _ => Aorigin)
      | CODESIZE => a_reader (fun state => Aimm_nat (program_bytes state.(a_program)))
      | GASPRICE => a_reader (fun _ => Agas_price)
      | NUMBER => a_reader (fun _ => Ablock_number)
      | COINBASE => a_reader (fun _ => Acoinbase)
      | BLOCKHASH => a_reader (fun _ => Ablockhash)
      | DIFFICULTY => a_reader (fun _ => Adifficulty)
      | GASLIMIT => a_reader (fun _ => Agaslimit)
      | MSIZE => a_operation_sem a_msize
      | PC => a_reader (fun state =>
                          Aimm_nat
                            (  program_bytes state.(a_program)
                             - program_bytes state.(a_prg_sfx))
                       )
      | EXTCODESIZE => a_operation_sem a_extcodesize
      | EXTCODECOPY =>
        (fun pre =>
           simple_result'
             match pre.(a_stc) with
             | addr :: memory_start :: code_start :: len :: rest =>
               extcode_copying
               {|
                 a_extcode_copy_addr := addr ;
                 a_extcode_copy_memory_start := memory_start ;
                 a_extcode_copy_code_start := code_start ;
                 a_extcode_copy_len := len |}
             | _ => failure pre
             end
        )
      | UNKNOWN _ => comp simple_result' (not_implemented i)
    end.

  Fixpoint optmap {A B : Type} (f : A -> option B) lst :=
    match lst with
    | nil => nil
    | hd :: tl =>
      match f hd with
      | None => optmap f tl
      | Some hh => hh :: optmap f tl
      end
    end.

  Definition conflict a_word_eq (conds0 conds1 : list a_prop) : bool :=
    if forallb (fun orig =>
                  forallb (fun new =>
                             (same_cond_same_val a_word_eq orig new)
                          ) conds0
               ) conds1 then
      false else true.


  Definition append_cond (a_word_eq : a_word -> a_word -> bool) (cond : list a_prop) (r : a_result) : a_result :=
    match r with (lst, len) =>
      let left := (optmap (fun sr =>
                         match sr with
                         | (c', x) =>
(*                           if forallb (fun orig =>
                                      forallb (fun new =>
                                          negb (a_word_eq orig new)
                                        ) cond
                                   ) c' then *)
                             Some (cond ++ c', x)
(*                           else
                             None *)
                         end) lst) in
      (left, len)
    end.

  Fixpoint flat_map' {A B : Type} (number_checker : N -> N)
           (f : A -> prod (list B) N) (a_lst : list A) : prod (list B) N :=
    match a_lst with
    | (nil) => (nil, 0)
    | (a :: tl_a) =>
        match flat_map' number_checker f tl_a with
        | (tl_b, tl_num) =>
          match f a with
            (hd_bs, hd_num) =>
            (app hd_bs tl_b, number_checker (hd_num + tl_num))
          end
        end
    end.

  Fixpoint a_exec conds number_checker a_word_eq (n : nat) (st : a_single_result) : a_result :=
    match st with
    | continue pre =>
      match n, pre.(a_prg_sfx) with
      | O, _ => ((nil, continue pre) :: nil, 1)
      | S n', hd::_ =>
        flat_map' number_checker
          (fun s_result =>
             match s_result with
               | (cond, x) =>
                 if conflict a_word_eq cond conds then (nil, 0) else
                   append_cond a_word_eq cond (a_exec (cond ++ conds) number_checker a_word_eq n' x)
             end)
          (fst (a_instr_sem hd pre))
      | S n', nil => simple_result' (end_of_program pre)
      end
    | _ => simple_result' st
    end
    .

  Definition a_ex (r : decode_result) (code : string) : a_single_result :=
    match r with
    | decode_success prog =>
      continue {|
        a_stc := nil;
        a_mem := Aempty;
        a_str := Ainitial_storage;
        a_log := nil;
        a_program := prog;
        a_program_code := match code with
                          | String "0" (String "x" y) => y
                          | _ => code
                          end ;
        a_prg_sfx := prog
      |}
    | decode_failure reason => decode_fail reason
    end.

Definition a_run a_word_eq number_checker n code :=
  (a_exec nil number_checker a_word_eq n (a_ex (decode code) code)).

End AbstractEVM.
