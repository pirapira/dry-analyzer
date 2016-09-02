(* Coq 8.5pl5 with ssreflect 1.5. *)
(* On ProofGeneral 4.3pre150930.  *)


Require Import Ascii.
Require Import String.
Require Import List.
Require Import FMapInterface.
Require Import NArith.

Module Lang.

  (* TODO: sort by opcode *)
  Inductive instr := (** partial.  adding those necessary. *)
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
  | SIGNEXTEND
  | EXP
  | GT
  | SGT
  | EQ
  | LT
  | SLT
  | AND
  | OR
  | XOR
  | NOT
  | BYTE
  | ISZERO
  | SHA3
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
  | BLOCKHASH
  | COINBASE
  | TIMESTAMP
  | NUMBER
  | DIFFICULTY
  | GASLIMIT
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
  | PUSH_N : string -> instr
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
  | LOG0
  | LOG1
  | LOG2
  | LOG3
  | LOG4
  | CREATE
  | CALL
  | CALLCODE
  | RETURN
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

  (* sofar accumulates instrucitons in the reverse order *)

  Fixpoint decode_inner (str : string) (m : decoding_mode)
           (sofar : list instr): decode_result :=
  match m with
  | first_zero =>
    match str with
    | String "0" rest => decode_inner rest first_x sofar
    | _ => decode_failure "first nonzero"
    end
  | first_x =>
    match str with
    | String "x" rest => decode_inner rest next_instr sofar
    | _ => decode_failure "second not x"
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
  | read_0 =>
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
    | _ => decode_failure "0?"
    end
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

(*
  Eval compute in decode "0x606060405236156100b95760e060020a6000350463173825d9811461010b5780632f54bf6e1461015b5780634123cb6b146101835780635c52c2f51461018c5780637065cb48146101b2578063746c9171146101db578063797af627146101e4578063b20d30a9146101f7578063b61d27f614610220578063b75c7dc614610241578063ba51a6df14610270578063c2cf732614610299578063cbf0b0c0146102d7578063f00d4b5d14610300578063f1736d861461032e575b61033860003411156101095760408051600160a060020a033316815234602082015281517fe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c929181900390910190a15b565b6103386004356000600036604051808383808284375050509081018190039020905061063d815b600160a060020a03331660009081526101026020526040812054818082811415610bb357610d0b565b61033a6004355b600160a060020a03811660009081526101026020526040812054115b919050565b61033a60015481565b610338600036604051808383808284375050509081018190039020905061078e81610132565b61033860043560003660405180838380828437505050908101819003902090506105b581610132565b61033a60005481565b61033a6004355b6000816109f181610132565b610338600435600036604051808383808284375050509081018190039020905061078281610132565b61033a6004803590602480359160443591820191013560006107ad33610162565b610338600435600160a060020a0333166000908152610102602052604081205490808281141561034c576103cb565b61033860043560003660405180838380828437505050908101819003902090506106fc81610132565b61033a600435602435600082815261010360209081526040808320600160a060020a0385168452610102909252822054828181141561075557610779565b610338600435600036604051808383808284375050509081018190039020905061079c81610132565b6103386004356024356000600036604051808383808284375050509081018190039020905061045681610132565b61033a6101055481565b005b60408051918252519081900360200190f35b50506000828152610103602052604081206001810154600284900a9290831611156103cb5780546001828101805492909101835590839003905560408051600160a060020a03331681526020810186905281517fc7fb647e59b18047309aa15aad418e5d7ca96d173ad704f1031a2c3d7591734b929181900390910190a15b50505050565b600160a060020a03831660028361010081101561000257508301819055600160a060020a03851660008181526101026020908152604080832083905584835291829020869055815192835282019290925281517fb532073b38c83145e3e5135377a08bf9aab55bc0fd7c1179cd4fb995d2a5159c929181900390910190a1505b505050565b156103cb5761046483610162565b1561046f5750610451565b600160a060020a0384166000908152610102602052604081205492508214156104985750610451565b6103d15b6101045460005b81811015610e5857610104805461010891600091849081101561000257600080516020610f1383398151915201548252506020918252604081208054600160a060020a0319168155600181018290556002810180548382559083528383209193610edd92601f92909201048101906109d9565b60018054810190819055600160a060020a038316906002906101008110156100025790900160005081905550600160005054610102600050600084600160a060020a03168152602001908152602001600020600050819055507f994a936646fe87ffe4f1e469d3d6aa417d6b855598397f323de5b449f765f0c3826040518082600160a060020a0316815260200191505060405180910390a15b505b50565b156105b0576105c382610162565b156105ce57506105b2565b6105d661049c565b60015460fa90106105eb576105e9610600565b505b60015460fa901061051657506105b2565b6106ba5b600060015b6001548110156109ed575b600154811080156106305750600281610100811015610002570154600014155b15610d1357600101610610565b1561045157600160a060020a03831660009081526101026020526040812054925082141561066b57506105b0565b600160016000505403600060005054111561068657506105b0565b600060028361010081101561000257508301819055600160a060020a038416815261010260205260408120556105fc61049c565b5060408051600160a060020a038516815290517f58619076adf5bb0943d100ef88d52d7c3fd691b19d3a9071b555b651fbf418da9181900360200190a1505050565b156105b05760015482111561071157506105b2565b600082905561071e61049c565b6040805183815290517facbdb084c721332ac59f9b8e392196c9eb0e4932862da8eb9beaf0dad4f550da9181900360200190a15050565b506001820154600282900a908116600014156107745760009350610779565b600193505b50505092915050565b156105b0575061010555565b156105b25760006101065550565b156105b05781600160a060020a0316ff5b156109c9576107c1846000610ded33610162565b1561087d577f92ca3a80853e6663fa31fa10b99225f18d4902939b4c53a9caae9043f6efd00433858786866040518086600160a060020a0316815260200185815260200184600160a060020a031681526020018060200182810382528484828181526020019250808284378201915050965050505050505060405180910390a184600160a060020a03168484846040518083838082843750505090810191506000908083038185876185025a03f150600093506109c992505050565b600036436040518084848082843750505090910190815260405190819003602001902091506108ad9050816101eb565b1580156108d0575060008181526101086020526040812054600160a060020a0316145b156109c95760008181526101086020908152604082208054600160a060020a03191688178155600181018790556002018054858255818452928290209092601f019190910481019084908682156109d1579182015b828111156109d1578235826000505591602001919060010190610925565b50507f1733cbb53659d713b79580f79f3f9ff215f78a7c7aa45890f3b89fc5cddfbf328133868887876040518087815260200186600160a060020a0316815260200185815260200184600160a060020a03168152602001806020018281038252848482818152602001925080828437820191505097505050505050505060405180910390a15b949350505050565b506109439291505b808211156109ed57600081556001016109d9565b5090565b15610ba05760008381526101086020526040812054600160a060020a031614610ba05760408051600091909120805460018201546002929092018054600160a060020a0392909216939091819083908015610a7157820191906000526020600020905b815481529060010190602001808311610a5457829003601f168201915b505091505060006040518083038185876185025a03f150505060008481526101086020908152604080519281902080546001820154600160a060020a033381811688529587018b905293860181905292166060850181905260a06080860181815260029390930180549187018290527fe7c957c06e9a662c1a6c77366179f5b702b97651dc28eee7d5bf1dff6e40bb4a975094958a959293909160c083019084908015610b4357820191906000526020600020905b815481529060010190602001808311610b2657829003601f168201915b5050965050505050505060405180910390a160008381526101086020908152604082208054600160a060020a031916815560018101839055600281018054848255908452828420919392610ba692601f92909201048101906109d9565b50919050565b505050600191505061017e565b60008581526101036020526040812080549093501415610c3b576000805483556001838101919091556101048054918201808255828015829011610c0a57818360005260206000209182019101610c0a91906109d9565b50505060028301819055610104805487929081101561000257600091909152600080516020610f1383398151915201555b506001810154600283900a90811660001415610d0b5760408051600160a060020a03331681526020810187905281517fe1c52dc63b719ade82e8bea94cc41a0d5d28e4aaf536adb5e9cccc9ff8c1aeda929181900390910190a1815460019011610cf8576000858152610103602052604090206002015461010480549091908110156100025760406000908120600080516020610f138339815191529290920181905580825560018281018290556002909201559450610d0b9050565b8154600019018255600182018054821790555b505050919050565b5b60018054118015610d3657506001546002906101008110156100025701546000145b15610d4a5760018054600019019055610d14565b60015481108015610d6d5750600154600290610100811015610002570154600014155b8015610d8757506002816101008110156100025701546000145b15610de857600154600290610100811015610002578101549082610100811015610002578101919091558190610102906000908361010081101561000257810154825260209290925260408120929092556001546101008110156100025701555b610605565b1561017e5761010754610e035b62015180420490565b1115610e1c57600061010655610e17610dfa565b610107555b6101065480830110801590610e3a5750610106546101055490830111155b15610e505750610106805482019055600161017e565b50600061017e565b6105b06101045460005b81811015610ee85761010480548290811015610002576000918252600080516020610f13833981519152015414610ed557610104805461010391600091849081101561000257600080516020610f1383398151915201548252506020919091526040812081815560018101829055600201555b600101610e62565b5050506001016104a3565b610104805460008083559190915261045190600080516020610f13833981519152908101906109d956004c0be60200faa20559308cb7b5a1bb3255c16cb1cab91f525b5ae7a03d02fabe". *)


  Open Scope string_scope.


(*
  Definition example2 :=
  (* taken from
     https://etherchain.org/account/0xad8d3a5d2d92eb14bb56ca9f380be35b8efe0c04#codeDisasm *)
    PUSH_N "0x60" ::
    PUSH_N "0x40" ::
    MSTORE ::
    CALLDATASIZE ::
    ISZERO ::
    PUSH_N "0x0053" ::
    JUMPI ::
    PUSH_N "0x00" ::
    CALLDATALOAD ::
    PUSH_N "0x0100000000000000000000000000000000000000000000000000000000" ::
    SWAP1 ::
    DIV ::
    DUP1 ::
    PUSH_N "0x3feb1bd8" ::
    EQ ::
    PUSH_N "0x00aa" ::
    JUMPI ::
    DUP1 ::
    PUSH_N "0x6042a760" ::
    EQ ::
    PUSH_N "0x00c9" ::
    JUMPI ::
    DUP1 ::
    PUSH_N "0xb214faa5" ::
    EQ ::
    PUSH_N "0x00ee" ::
    JUMPI ::
    PUSH_N "0x0053" ::
    JUMP ::
    JUMPDEST ::
    PUSH_N "0x00a8" ::
    JUMPDEST ::
    CALLER ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0xceaafb6781e240ba6b317a906047690d1c227df2d967ff3f53b44f14a62c2cab" ::
    CALLVALUE ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP3 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    SWAP2 ::
    POP ::
    POP ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    SWAP2 ::
    SUB ::
    SWAP1 ::
    LOG2 ::
    JUMPDEST ::
    JUMP ::
    JUMPDEST ::
    STOP ::
    JUMPDEST ::
    PUSH_N "0x00c7" ::
    PUSH_N "0x04" ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    POP ::
    PUSH_N "0x0154" ::
    JUMP ::
    JUMPDEST ::
    STOP ::
    JUMPDEST ::
    PUSH_N "0x00ec" ::
    PUSH_N "0x04" ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    POP ::
    PUSH_N "0x0233" ::
    JUMP ::
    JUMPDEST ::
    STOP ::
    JUMPDEST ::
    PUSH_N "0x00ff" ::
    PUSH_N "0x04" ::
    DUP1 ::
    CALLDATALOAD ::
    SWAP1 ::
    PUSH_N "0x20" ::
    ADD ::
    POP ::
    PUSH_N "0x0101" ::
    JUMP ::
    JUMPDEST ::
    STOP ::
    JUMPDEST ::
    DUP1 ::
    CALLER ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0x19dacbf83c5de6658e14cbf7bcae5c15eca2eedecf1c66fbca928e4d351bea0f" ::
    CALLVALUE ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP3 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    SWAP2 ::
    POP ::
    POP ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    SWAP2 ::
    SUB ::
    SWAP1 ::
    LOG3 ::
    JUMPDEST ::
    POP ::
    JUMP ::
    JUMPDEST ::
    PUSH_N "0x00" ::
    PUSH_N "0x00" ::
    SWAP1 ::
    SLOAD ::
    SWAP1 ::
    PUSH_N "0x0100" ::
    EXP ::
    SWAP1 ::
    DIV ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    CALLER ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    EQ ::
    ISZERO ::
    PUSH_N "0x022d" ::
    JUMPI ::
    DUP2 ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0x00" ::
    DUP3 ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    SWAP1 ::
    POP ::
    PUSH_N "0x00" ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP4 ::
    SUB ::
    DUP2 ::
    DUP6 ::
    DUP9 ::
    DUP9 ::
    CALL ::
    SWAP4 ::
    POP ::
    POP ::
    POP ::
    POP ::
    POP ::
    DUP2 ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    DUP4 ::
    PUSH_N "0x4c13017ee95afc4bbd8a701dd9fbc9733f1f09f5a1b5438b5b9abd48e4c92d78" ::
    DUP4 ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP3 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    SWAP2 ::
    POP ::
    POP ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    SWAP2 ::
    SUB ::
    SWAP1 ::
    LOG3 ::
    JUMPDEST ::
    JUMPDEST ::
    POP ::
    POP ::
    POP ::
    JUMP ::
    JUMPDEST ::
    PUSH_N "0x00" ::
    PUSH_N "0x00" ::
    SWAP1 ::
    SLOAD ::
    SWAP1 ::
    PUSH_N "0x0100" ::
    EXP ::
    SWAP1 ::
    DIV ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    CALLER ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    EQ ::
    ISZERO ::
    PUSH_N "0x034b" ::
    JUMPI ::
    DUP3 ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    PUSH_N "0xb214faa5" ::
    DUP3 ::
    DUP5 ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP4 ::
    PUSH_N "0x0100000000000000000000000000000000000000000000000000000000" ::
    MUL ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x04" ::
    ADD ::
    DUP1 ::
    DUP3 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    SWAP2 ::
    POP ::
    POP ::
    PUSH_N "0x00" ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP4 ::
    SUB ::
    DUP2 ::
    DUP6 ::
    DUP9 ::
    PUSH_N "0x8502" ::
    GAS ::
    SUB ::
    CALL ::
    ISZERO ::
    PUSH_N "0x0002" ::
    JUMPI ::
    POP ::
    POP ::
    POP ::
    POP ::
    DUP3 ::
    PUSH_N "0xffffffffffffffffffffffffffffffffffffffff" ::
    AND ::
    DUP5 ::
    PUSH_N "0x260c3af1b30cb645202dd6dbf41affda680b1ffebd32d401b7f121c2b9262680" ::
    DUP5 ::
    DUP5 ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    DUP4 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    DUP3 ::
    DUP2 ::
    MSTORE ::
    PUSH_N "0x20" ::
    ADD ::
    SWAP3 ::
    POP ::
    POP ::
    POP ::
    PUSH_N "0x40" ::
    MLOAD ::
    DUP1 ::
    SWAP2 ::
    SUB ::
    SWAP1 ::
    LOG3 ::
    JUMPDEST ::
    JUMPDEST ::
    POP ::
    POP ::
    POP ::
    POP ::
    JUMP :: nil. *)

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
  | Atime : a_word
  | Adatasize : a_word
  | Avalue : a_word
  | Aaddress : a_word
  | Abalance : a_word
  | Aimm_nat : N -> a_word
  | Aunknown_remaining_gas : a_word
  | Ais_zero : a_word -> a_word
  | Azero : a_word
  | Asub : a_word -> a_word -> a_word
  | Aadd : a_word -> a_word -> a_word
  | Aand : a_word -> a_word -> a_word
  | Aor : a_word -> a_word -> a_word
  | Axor : a_word -> a_word -> a_word
  | Aexp : a_word -> a_word -> a_word
  | Adiv : a_word -> a_word -> a_word
  | Amul : a_word -> a_word -> a_word
  | Agt  : a_word -> a_word -> a_word
  | Anot : a_word -> a_word
  | Asha3 : a_memory -> a_word
  | Alt  : a_word -> a_word -> a_word
  | Aeq  : a_word -> a_word -> a_word
  | Aget32 : a_word -> a_memory -> a_word (* Aget32 addr mem *)
  | Aget_storage : a_word -> a_storage -> a_word
  with a_memory :=
  | Aempty : a_memory
  | Aput : a_word -> a_word -> a_memory -> a_memory
  (* Aput addr val orig represents the result of store. *)
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
    | Aput (Aimm_nat w) val orig =>
      if N.leb addr w then simplify_above addr orig
      else
        Aput (Aimm_nat w) val (simplify_above addr orig)
    | _ => mem
    end.

  Fixpoint simplify_below (addr : N) (mem : a_memory) :=
    match mem with
    | Aput (Aimm_nat w) val orig =>
      if N.leb (w + 32) addr then simplify_below addr orig
      else
        Aput (Aimm_nat w) val (simplify_below addr orig)
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
    | Aimm_nat n, Aput (Aimm_nat w) v orig =>
      if orb (N.leb 32 (n - w)) (N.leb 32 (w - n)) then
        Aget32' addr orig
      else if (N.eqb n w) then v else Aget32 addr mem
    | _, _ => Aget32 addr mem
    end.

  Fixpoint forget addr orig :=
    match addr, orig with
    | Aimm_nat w, Aput (Aimm_nat p) v pre =>
      if (N.eqb w p) then
        forget addr pre
      else
        Aput (Aimm_nat p) v (forget addr pre)
    | _, _ => orig
    end.

  Fixpoint Aput' (addr : a_word) (val : a_word) (orig : a_memory) : a_memory :=
    Aput addr val (forget addr orig).

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
      | a :: b :: l => simple_result (Some (l, Aput' a b mem))
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
      simple_result (Some (Aunknown_remaining_gas :: s, mem)).

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

  Definition a_exp_op : a_operation := a_two_one_op Aexp'.

  Definition a_and_op : a_operation := a_two_one_op Aand.
  Definition a_or_op : a_operation := a_two_one_op Aor.
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

  Definition a_gt : a_operation := a_two_one_op
    (fun a b => Agt a b).

  Definition a_not : a_operation := a_one_one_op Anot.

  Definition a_sha3 : a_operation :=
    fun s mem =>
      simple_result
        match s with
        | st :: size :: rest =>
          Some (Asha3 (Atake' st size mem) :: rest, mem)
        | _ => None
        end.

  Definition a_lt : a_operation := a_two_one_op
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


  Inductive a_single_result :=
  | continue : a_state -> a_single_result
  | suicide  : a_word (* who gets the balance *) -> a_single_result
  | returned : a_memory (* output *) -> a_state -> a_single_result
  | stopped  : a_state -> a_single_result
  | calling  : a_call -> a_single_result
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
      | SDIV => (fun pre =>(simple_result' (not_implemented SDIV pre)))
      | MOD => (fun pre => simple_result' (not_implemented MOD pre))
      | SMOD => (fun pre => simple_result' (not_implemented SMOD pre))
      | ADDMOD => (fun pre => simple_result' (not_implemented ADDMOD pre))
      | MULMOD => (fun pre => simple_result' (not_implemented MULMOD pre))
      | SIGNEXTEND => comp simple_result' (not_implemented i)
      | EXP => a_operation_sem a_exp_op
      | GT  => a_operation_sem a_gt
      | LT  => a_operation_sem a_lt
      | SLT => comp simple_result' (not_implemented i)
      | SGT => comp simple_result' (not_implemented i)
      | EQ => a_operation_sem a_eq_op
      | AND => a_operation_sem a_and_op
      | OR  => a_operation_sem a_or_op
      | XOR => a_operation_sem a_xor_op
      | NOT => a_operation_sem a_not
      | BYTE => comp simple_result' (not_implemented i)
      | ISZERO => a_operation_sem a_iszero
      | GAS    => a_reader (fun pre => Aunknown_remaining_gas)
      | CALLER => a_reader (fun _ => Acaller)
      | CALLVALUE => a_reader (fun _ => Avalue)
      | CALLDATALOAD => a_operation_sem a_calldataload
      | CALLDATASIZE => a_operation_sem a_calldatasize
      | CALLDATACOPY => a_operation_sem a_calldatacopy
      | ADDRESS => a_operation_sem a_address
      | TIMESTAMP => a_reader (fun _ => Atime)
      | POP =>    a_operation_sem a_pop
      | MLOAD  => a_operation_sem a_mload
      | MSTORE => a_operation_sem a_mstore
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
      | LOG1 => a_log_n 1
      | LOG2 => a_log_n 2
      | LOG3 => a_log_n 3
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
      | _ => comp simple_result' (not_implemented i)
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

(*    Definition example4 : string :=
    "0x606060405236156100985760e060020a60003504631ff6c705811461009a578063303a36e2146100a35780635ea8cd12146101f757806369d640fd1461021b5780637ce3489b146102735780637fd6f15c1461029b5780638da5cb5b146102a4578063c943e51a146102b6578063d229b54b1461034d578063e45be8eb14610371578063f2a75fe41461037a578063f46a85a9146103bf575b005b6103f560015481565b610407600435617d00604051908101604052806103e8905b60008152602001906001900390816100bb57505060408051617d0081019091526103e8815b60008152602001906001900390816100e057505060408051617d0081019091526103e8815b60008152602001906001900390816101055750600090505b6103e8811015610846576004816103e881101561000257610fa00201600050856103e88110156100025790906004020160005054600160a060020a031684826103e8811015610002575050602082028501526004816103e881101561000257610fa00201600050856103e8811015610002579090600402016000506002015483826103e88110156100025760200201526004816103e881101561000257610fa00201600050856103e8811015610002579090600402016000506003015482826103e88110156100025750506020820283015260010161011d565b610098600435600054600160a060020a039081163391909116141561029857600355565b6104566004356024356004826103e88110156100025750610fa0830201816103e88110156100025790906004020160005060038101546002820154825460019390930154600160a060020a0393909316945091925084565b610098600435600054600160a060020a03908116339190911614156102985760028190555b50565b6103f560025481565b610487600054600160a060020a031681565b6103f56004356024356044355b60006000600060008610806102da57506103e88610155b156105b15760408051600160a060020a03331681528082018890526060602082018190526019908201527f58206d757374206265203e203020616e64203c20313030302e000000000000006080820152905160008051602061084e8339815191529181900360a00190a1600092506105a8565b610098600435600054600160a060020a039081163391909116141561029857600155565b6103f560035481565b610098600054600160a060020a03908116339190911614156103bd5760405160008054600160a060020a039081169230909116319082818181858883f150505050505b565b6103f560043560243560443560643560843560a43560006104a487878587610100028962010000028762100000020101016102c3565b60408051918252519081900360200190f35b6040518084617d008083818460006004610bc7f150918201918591508083818460006004610bc7f15061fa00840192508491508083818460006004610bc7f15062017700965092945050505050f35b60408051600160a060020a039590951685526020850193909352838301919091526060830152519081900360800190f35b60408051600160a060020a03929092168252519081900360200190f35b979650505050505050565b6001546004876103e881101561000257610fa00201866103e8811015610002576004020160030154023460640210156106d25760015460008051602061084e83398151915290339060649060048a6103e881101561000257610fa00201896103e881101561000257600402016000506003015460408051600160a060020a03959095168552910291909104828201526060602083018190526032908301527f56616c7565206d7573742062652031302520686967686572207468616e20637560808301527f7272656e7420706978656c2070726963652e000000000000000000000000000060a0830152519081900360c00190a1600092505b50509392505050565b60008510806105c257506103e88510155b156106355760408051600160a060020a03331681528082018790526060602082018190526019908201527f59206d757374206265203e203020616e64203c20313030302e000000000000006080820152905160008051602061084e8339815191529181900360a00190a1600092506105a8565b6003543410156104af5760408051600160a060020a033316815234818301526060602082018190526021908201527f4d696e696d756d20706978656c2070726963652069732035302066696e6e657960808201527f2e0000000000000000000000000000000000000000000000000000000000000060a0820152905160008051602061084e8339815191529181900360c00190a1600092506105a8565b6004866103e881101561000257610fa00201856103e8811015610002576004020180549092506000600160a060020a03919091161115610740575060405160025482546064349283020492600160a060020a039190911691600091908490039082818181858883f150505050505b604080516080810182523381524360208201529081018590523460608201526004876103e881101561000257610fa00201866103e881101561000257600402018054825173ffffffffffffffffffffffffffffffffffffffff199190911617815560208281015160018301556040838101516002848101919091556060948501516003948501558654908701549387015482518c81529384018b9052600160a060020a03918216848401529483019390935260808201939093523390911660a082015260c081018690523460e082015290517f26f34cb6b7870852e345e9eac424ccb8198e669c65b63734ccffd3f591abfd67918190036101000190a1600192506105a8565b50919390925056fd33e90d0eac940755277aa91045b95664988beeeafc4ed7d1281a6d83afbc00".



Definition ethdev :=
"0x606060405236156100b95760e060020a6000350463173825d9811461010b5780632f54bf6e1461015b5780634123cb6b146101835780635c52c2f51461018c5780637065cb48146101b2578063746c9171146101db578063797af627146101e4578063b20d30a9146101f7578063b61d27f614610220578063b75c7dc614610241578063ba51a6df14610270578063c2cf732614610299578063cbf0b0c0146102d7578063f00d4b5d14610300578063f1736d861461032e575b61033860003411156101095760408051600160a060020a033316815234602082015281517fe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c929181900390910190a15b565b6103386004356000600036604051808383808284375050509081018190039020905061063d815b600160a060020a03331660009081526101026020526040812054818082811415610bb357610d0b565b61033a6004355b600160a060020a03811660009081526101026020526040812054115b919050565b61033a60015481565b610338600036604051808383808284375050509081018190039020905061078e81610132565b61033860043560003660405180838380828437505050908101819003902090506105b581610132565b61033a60005481565b61033a6004355b6000816109f181610132565b610338600435600036604051808383808284375050509081018190039020905061078281610132565b61033a6004803590602480359160443591820191013560006107ad33610162565b610338600435600160a060020a0333166000908152610102602052604081205490808281141561034c576103cb565b61033860043560003660405180838380828437505050908101819003902090506106fc81610132565b61033a600435602435600082815261010360209081526040808320600160a060020a0385168452610102909252822054828181141561075557610779565b610338600435600036604051808383808284375050509081018190039020905061079c81610132565b6103386004356024356000600036604051808383808284375050509081018190039020905061045681610132565b61033a6101055481565b005b60408051918252519081900360200190f35b50506000828152610103602052604081206001810154600284900a9290831611156103cb5780546001828101805492909101835590839003905560408051600160a060020a03331681526020810186905281517fc7fb647e59b18047309aa15aad418e5d7ca96d173ad704f1031a2c3d7591734b929181900390910190a15b50505050565b600160a060020a03831660028361010081101561000257508301819055600160a060020a03851660008181526101026020908152604080832083905584835291829020869055815192835282019290925281517fb532073b38c83145e3e5135377a08bf9aab55bc0fd7c1179cd4fb995d2a5159c929181900390910190a1505b505050565b156103cb5761046483610162565b1561046f5750610451565b600160a060020a0384166000908152610102602052604081205492508214156104985750610451565b6103d15b6101045460005b81811015610e5857610104805461010891600091849081101561000257600080516020610f1383398151915201548252506020918252604081208054600160a060020a0319168155600181018290556002810180548382559083528383209193610edd92601f92909201048101906109d9565b60018054810190819055600160a060020a038316906002906101008110156100025790900160005081905550600160005054610102600050600084600160a060020a03168152602001908152602001600020600050819055507f994a936646fe87ffe4f1e469d3d6aa417d6b855598397f323de5b449f765f0c3826040518082600160a060020a0316815260200191505060405180910390a15b505b50565b156105b0576105c382610162565b156105ce57506105b2565b6105d661049c565b60015460fa90106105eb576105e9610600565b505b60015460fa901061051657506105b2565b6106ba5b600060015b6001548110156109ed575b600154811080156106305750600281610100811015610002570154600014155b15610d1357600101610610565b1561045157600160a060020a03831660009081526101026020526040812054925082141561066b57506105b0565b600160016000505403600060005054111561068657506105b0565b600060028361010081101561000257508301819055600160a060020a038416815261010260205260408120556105fc61049c565b5060408051600160a060020a038516815290517f58619076adf5bb0943d100ef88d52d7c3fd691b19d3a9071b555b651fbf418da9181900360200190a1505050565b156105b05760015482111561071157506105b2565b600082905561071e61049c565b6040805183815290517facbdb084c721332ac59f9b8e392196c9eb0e4932862da8eb9beaf0dad4f550da9181900360200190a15050565b506001820154600282900a908116600014156107745760009350610779565b600193505b50505092915050565b156105b0575061010555565b156105b25760006101065550565b156105b05781600160a060020a0316ff5b156109c9576107c1846000610ded33610162565b1561087d577f92ca3a80853e6663fa31fa10b99225f18d4902939b4c53a9caae9043f6efd00433858786866040518086600160a060020a0316815260200185815260200184600160a060020a031681526020018060200182810382528484828181526020019250808284378201915050965050505050505060405180910390a184600160a060020a03168484846040518083838082843750505090810191506000908083038185876185025a03f150600093506109c992505050565b600036436040518084848082843750505090910190815260405190819003602001902091506108ad9050816101eb565b1580156108d0575060008181526101086020526040812054600160a060020a0316145b156109c95760008181526101086020908152604082208054600160a060020a03191688178155600181018790556002018054858255818452928290209092601f019190910481019084908682156109d1579182015b828111156109d1578235826000505591602001919060010190610925565b50507f1733cbb53659d713b79580f79f3f9ff215f78a7c7aa45890f3b89fc5cddfbf328133868887876040518087815260200186600160a060020a0316815260200185815260200184600160a060020a03168152602001806020018281038252848482818152602001925080828437820191505097505050505050505060405180910390a15b949350505050565b506109439291505b808211156109ed57600081556001016109d9565b5090565b15610ba05760008381526101086020526040812054600160a060020a031614610ba05760408051600091909120805460018201546002929092018054600160a060020a0392909216939091819083908015610a7157820191906000526020600020905b815481529060010190602001808311610a5457829003601f168201915b505091505060006040518083038185876185025a03f150505060008481526101086020908152604080519281902080546001820154600160a060020a033381811688529587018b905293860181905292166060850181905260a06080860181815260029390930180549187018290527fe7c957c06e9a662c1a6c77366179f5b702b97651dc28eee7d5bf1dff6e40bb4a975094958a959293909160c083019084908015610b4357820191906000526020600020905b815481529060010190602001808311610b2657829003601f168201915b5050965050505050505060405180910390a160008381526101086020908152604082208054600160a060020a031916815560018101839055600281018054848255908452828420919392610ba692601f92909201048101906109d9565b50919050565b505050600191505061017e565b60008581526101036020526040812080549093501415610c3b576000805483556001838101919091556101048054918201808255828015829011610c0a57818360005260206000209182019101610c0a91906109d9565b50505060028301819055610104805487929081101561000257600091909152600080516020610f1383398151915201555b506001810154600283900a90811660001415610d0b5760408051600160a060020a03331681526020810187905281517fe1c52dc63b719ade82e8bea94cc41a0d5d28e4aaf536adb5e9cccc9ff8c1aeda929181900390910190a1815460019011610cf8576000858152610103602052604090206002015461010480549091908110156100025760406000908120600080516020610f138339815191529290920181905580825560018281018290556002909201559450610d0b9050565b8154600019018255600182018054821790555b505050919050565b5b60018054118015610d3657506001546002906101008110156100025701546000145b15610d4a5760018054600019019055610d14565b60015481108015610d6d5750600154600290610100811015610002570154600014155b8015610d8757506002816101008110156100025701546000145b15610de857600154600290610100811015610002578101549082610100811015610002578101919091558190610102906000908361010081101561000257810154825260209290925260408120929092556001546101008110156100025701555b610605565b1561017e5761010754610e035b62015180420490565b1115610e1c57600061010655610e17610dfa565b610107555b6101065480830110801590610e3a5750610106546101055490830111155b15610e505750610106805482019055600161017e565b50600061017e565b6105b06101045460005b81811015610ee85761010480548290811015610002576000918252600080516020610f13833981519152015414610ed557610104805461010391600091849081101561000257600080516020610f1383398151915201548252506020919091526040812081815560018101829055600201555b600101610e62565b5050506001016104a3565b610104805460008083559190915261045190600080516020610f13833981519152908101906109d956004c0be60200faa20559308cb7b5a1bb3255c16cb1cab91f525b5ae7a03d02fabe". *)

(* http://etherscan.io/address/0xf75e354c5edc8efed9b59ee9f67a80845ade7d0c *)
(*Definition something := "0x3660008037602060003660003473273930d21e01ee25e4c219b63259d214872220a261235a5a03f21560015760206000f3".*)
(*
Definition hoge := "0x3660008037602060003660003473273930d21e01ee25e4c219b63259d214872220a261235a5a03f21560015760206000f3".

Definition fuga := "0x60006000526001543314610100527f6265740000000000000000000000000000000000000000000000000000000000600035141561009057346040526000608035111561005b57600f5460405103604052600f54600c5401600c555b60055460405110156100cd577f6265743a206e6f7420656e6f75676820626574000000000000000000000000006012556101a0565b600061010051156100c0577f7365745f737461747573000000000000000000000000000000000000000000009035145b156101c657602035600255005b6000600160025414156100e35750602035600354145b610110577f6265743a2077726f6e6720737461747573206f7220726e6420230000000000006012556101a0565b60045460075410610144577f6265743a20616c6c20626574732061726520646f6e65000000000000000000006012556101a0565b600560075402602052602051610100016020523360006020510155604051600160205101556040356002602051015560603560036020510155608035600460205101556040516008540160085560016007540160075560016000525b600060003411156101af578051145b156101c45760006000600060003433610303f1505b005b600061010051156101ff577f73746172745f726f756e64000000000000000000000000000000000000000000813514156101ff57600254145b156102405760016003540160203514156101c45760016002556020356003554360065560006007556000600855604035600955606035600a55608035600b55005b6000610100511561027c577f636f6d706c6574655f726f756e640000000000000000000000000000000000008135141561027c57506001600254145b156102c557600060035460203514156102985750600454600754145b610368577f77726f6e6720726f756e64206f72206e5f6265747320746f20737461727400006012556101c4565b600061010051156102f5577f63616e63656c5f726f756e6400000000000000000000000000000000000000009035145b156105cb5760006060525b60075460605110156106085760605160050261010081016020526101018101546080526101040154600090111561033c57600f54608051016080525b60805160085403600855600060006000600060805160205154610401f150600160605101606052610300565b600060805261010060205260006060525b60075460605110156103cd5760808051606080516020805180546001828101546002840154600385015460048601549988189094189091181890911890951890955260059490940190935291019052610379565b60403560805114610407576080516011557f77726f6e672063730000000000000000000000000000000000000000000000006012556101c4565b600060a05260085460c052600060e0526000606035111561043757600e54600c54606035606491909202040460a0525b60006060525b60075460605110156105845760ff6060516061013516608052600560605102610100016020526000608051141561046f575b600160805114156104a15760006000600060006001602051015460205154610201f1506001602051015460c0510360c0525b600260805114156104d35760006000600060006001602051015460205154610202f1506001602051015460c0510360c0525b6003608051141561050b5760006000600060006002600160205101540260205154610203f1506002600160205101540260c0510360c0525b600460805114156105765760006000600060006002600160205101540260205154610204f1506002600160205101540260c0510360c05260603560e051101561057657600060006000600060a05160205154610301f150600160e0510160e05260a051600c5403600c555b60016060510160605261043d565b600060c05111156105c4576064600d5460c0510204608052608051600c5401600c5560805160c0510360c052600060006000600060c051600154610302f1505b6000600255005b600061010051156105fb577f7365745f726f756e6400000000000000000000000000000000000000000000009035145b1561061d57602035600355005b60016003540360035560026002556000600755005b6000610100511561064d577f6162616e646f6e5f726f756e64000000000000000000000000000000000000009035145b1561065f576020356003556000600255005b6000610100511561068f577f6164645f6a7000000000000000000000000000000000000000000000000000009035145b1561069e5734600c5401600c55005b600061010051156106ce577f7365745f6a705f626574000000000000000000000000000000000000000000009035145b156106db57602035600f55005b6000610100511561070b577f7365745f6a705f6e65656465645f6269747300000000000000000000000000009035145b1561071857602035601055005b60006101005115610748577f7365745f6a705f70657263656e746167650000000000000000000000000000009035145b1561075557602035600d55005b60006101005115610785577f7365745f6a705f7061796d656e745f70657263656e74616765000000000000009035145b1561079257602035600e55005b600061010051156107c2577f7365745f6e65656465645f6265747300000000000000000000000000000000009035145b156107cf57602035600455005b600061010051156107ff577f7365745f6d696e5f6265740000000000000000000000000000000000000000009035145b1561080c57602035600555005b6000610100511561083c577f72657365745f6572726f720000000000000000000000000000000000000000009035145b1561084d5760006012556000601155005b60006101005115610889577f6b696c6c000000000000000000000000000000000000000000000000000000008135141561088957506002600254145b1561089357600154ff5b7f57726f6e6720636f6d6d616e640000000000000000000000000000000000000060125560003560115560003411156108d65760006000600060003433610303f1505b".

Definition something_else := "0x60606040526101cd806100126000396000f36060604052361561000f5761000f565b6101cb5b60006002600050541180156100315750620151806002600050544203115b156100e5573373ffffffffffffffffffffffffffffffffffffffff16600034604051809050600060405180830381858888f1935050505050600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1660003073ffffffffffffffffffffffffffffffffffffffff1631604051809050600060405180830381858888f193505050505060006002600050819055506101c8565b670de0b6b3a7640000341015156101c757600060026000505414156101345733600060006101000a81548173ffffffffffffffffffffffffffffffffffffffff02191690830217905550610191565b600060009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff166000662386f26fc10000604051809050600060405180830381858888f19350505050505b33600160006101000a81548173ffffffffffffffffffffffffffffffffffffffff02191690830217905550426002600050819055505b5b5b565b00".
*)

(* taken from above, just chosen something 60606040... *)
  Open Scope string_scope.

Definition cheated := "0x6060604052361561000f5761000f565b6101cb5b60006002600050541180156100315750620151806002600050544203115b156100e5573373ffffffffffffffffffffffffffffffffffffffff16600034604051809050600060405180830381858888f1935050505050600160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1660003073ffffffffffffffffffffffffffffffffffffffff1631604051809050600060405180830381858888f193505050505060006002600050819055506101c8565b670de0b6b3a7640000341015156101c757600060026000505414156101345733600060006101000a81548173ffffffffffffffffffffffffffffffffffffffff02191690830217905550610191565b600060009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff166000662386f26fc10000604051809050600060405180830381858888f19350505050505b33600160006101000a81548173ffffffffffffffffffffffffffffffffffffffff02191690830217905550426002600050819055505b5b5b565b00".

Definition are :=
"0x3660008037602060003660003473273930d21e01ee25e4c219b63259d214872220a261235a5a03f21560015760206000f3".

Definition a_run a_word_eq number_checker n code :=
  (a_exec nil number_checker a_word_eq n (a_ex (decode code) code)).

(* Eval compute in (a_run 200 are).*)


End AbstractEVM.
