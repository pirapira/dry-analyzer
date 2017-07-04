open Getopt
open Lwt
open Cohttp
open Cohttp_lwt_unix

open Evm;;

Lwt_log.default :=
  Lwt_log.channel ~close_mode:`Keep ~channel:Lwt_io.stderr ()
  ;;

let rec hex_of_big_int_ (n : Big_int.big_int) =
  let le = Big_int.le_big_int in
  let bofi = Big_int.big_int_of_int in
  if le n (bofi 9) then Big_int.string_of_big_int n
  else if le n (bofi 15) then
    (match Big_int.int_of_big_int n with
      | 10 -> "a"
      | 11 -> "b"
      | 12 -> "c"
      | 13 -> "d"
      | 14 -> "e"
      | 15 -> "f"
      | _ -> failwith "hex_of_big_int_ broken"
    )
  else
    let (q, r) = Big_int.quomod_big_int n (bofi 16) in
    (hex_of_big_int_ q) ^ (hex_of_big_int_ r)
;;

let hex_of_big_int n = "0x"^(hex_of_big_int_ n);;

open AbstractEVM;;

exception TooManyCases;;

let number_checker (n : Big_int.big_int) =
  if Big_int.le_big_int (Big_int.big_int_of_int 30000) n then raise TooManyCases;
  n;;

let rec len lst =
  match lst with
    | [] -> 0
    | _ :: tl -> 1 + (len tl);;

let parens str = "("^str^")";;

let binary f op v0 v1 =
  parens (f v0^op^f v1);;

let rec simplify_val v =
  (match v with
    | Aadd (x,y) -> Aadd (simplify_val x, simplify_val y)
    | Asub (x,y) -> Asub (simplify_val x, simplify_val y)
    | Aget32 (addr, mem) ->
      (match  (simplify_val addr, simplify_mem_focus addr mem) with
	| (a, m) -> Aget32 (a, m))
    | _ -> v)
and simplify_mem_focus addr (m : a_memory) = m
and simplify_mem m =
  match m with
    | Atake (st, size, orig) ->
      Atake ((simplify_val st), (simplify_val size), (simplify_mem orig))
    | Aput32 (addr, v, orig) ->
      Aput32 ((simplify_val addr), (simplify_val v), (simplify_mem orig))
    | _ -> m;;


let rec a_val_to_str v =
  let bin = binary a_val_to_str in
  match v with
    | Abyte (idx, w) -> (a_val_to_str w)^"["^(a_val_to_str idx)^"]"
    | Acaller -> "(address of caller)"
    | Atime   -> "(timestamp)"
    | Agas_price -> "(gasprice)"
    | Ablock_number -> "(block number)"
	| Ablockhash -> "(blockhash)"
    | Adifficulty -> "(difficulty)"
	| Agaslimit -> "(gaslimit)"
    | Acoinbase -> "(coinbase)"
    | Aorigin -> "(address of original external account)"
    | Adatasize -> "(size of input)"
    | Avalue  -> "(value of this call)"
    | Aaddress -> "(address of this contract)"
    | Abalance addr -> "(balance of "^a_val_to_str addr^")"
    | Aunknown explanation -> "(unknown ("^BatString.implode explanation^"))"
    | Ais_zero v' -> "(is_zero "^a_val_to_str v'^")"
    | Azero -> "0"
    | Aextcodesize a -> "(code size of address "^a_val_to_str a^")"
    | Asub (v0, v1) -> bin " - " v0 v1
    | Aadd (v0, v1) -> bin " + " v0 v1
    | Aand (v0, v1) -> bin " and " v0 v1
    | Aor  (v0, v1) -> bin " or " v0 v1
    | Axor (v0, v1) -> bin " xor " v0 v1
    | Aexp (v0, v1) -> bin " ** " v0 v1
    | Adiv (v0, v1) -> bin " / " v0 v1
    | Amod (v0, v1) -> bin " mod " v0 v1
    | Asmod (v0, v1) -> bin " smod " v0 v1
    | Asdiv (v0, v1) -> bin " sdiv " v0 v1
    | Amul (v0, v1) -> bin " * " v0 v1
    | Agt (v0, v1) -> bin " > " v0 v1
    | Anot v -> "(not "^(a_val_to_str v)^")"
    | Alt (v0, v1) -> bin " < " v0 v1
    | Aslt (v0, v1) -> bin " slt " v0 v1
    | Aeq (v0, v1) -> bin " == " v0 v1
    | Asignextend (v0, v1) -> "(signextend "^(a_val_to_str v1)^" from "^(a_val_to_str v0)^"bytes)"
    | Aget32 (addr, mem) -> "(get32 "^(a_val_to_str addr)^" "^(a_memory_to_str mem false)^")"
    | Aget_storage (addr, str) -> "(get_storage "^(a_val_to_str addr)^" "^(a_storage_to_str str false)^")"
    | Asha3 mem -> "(sha3 "^(a_memory_to_str mem false)^")"
    | Aimm_nat imm -> Printf.sprintf "(%s)" (hex_of_big_int imm)
and a_memory_to_str m block  =
  (if block then
    "<div class=\"memory\">"
  else
    "<span class=\"memory\">"
  )^
    begin match m with
    | Aempty -> "(empty)"
    | Aput32 (addr,v,orig) ->
      Printf.sprintf "(mem_write32 addr: %s val: %s in %s)" (a_val_to_str addr) (a_val_to_str v) (a_memory_to_str orig block)
    | Aput1 (addr,v,orig) ->
      Printf.sprintf "(mem_write_byte addr: %s val: (%s mod 256) in %s)" (a_val_to_str addr) (a_val_to_str v) (a_memory_to_str orig block)
    | Amemwrite (start_addr, len, source, mem) ->
      Printf.sprintf "%s; copy from %s [0, %s) at offset %s" (a_memory_to_str mem block) (a_memory_to_str source false) (a_val_to_str len) (a_val_to_str start_addr)
    | Adata -> "(input data)"
    | Adrop (num, orig) -> Printf.sprintf "(drop first %s bytes from %s)"
      (a_val_to_str num) (a_memory_to_str orig block)
    | Atake (start, size, orig) -> Printf.sprintf "(take %s bytes at %s from %s)"
      (a_val_to_str size) (a_val_to_str start) (a_memory_to_str orig block)
    | Amem_imm _ -> "a_mem_to_str imm not implemented"
    | Acodecopy (memstart, codestart, size, orig) ->
       Printf.sprintf "(codecopy mem: %s, code: %s, size: %s, on %s)"
                      (a_val_to_str memstart)
                      (a_val_to_str codestart)
                      (a_val_to_str size)
                      (a_memory_to_str orig block)
    | Aconcat (w0, w1) ->
       Printf.sprintf "(concat %s %s)" (a_val_to_str w0) (a_val_to_str w1)
    end^(if block then "</div>" else "</span>")
and a_storage_to_str m block =
  (if block then
    "<div class=\"memory\">"
  else
    "<span class=\"memory\">"
  )^
    begin match m with
    | Ainitial_storage -> "(initial storage)"
    | Aput_storage  (addr,v,orig) ->
      Printf.sprintf "(storage_write at: %s, val: %s %s)" (a_val_to_str addr) (a_val_to_str v) (a_storage_to_str orig block)
    end^(if block then "</div>" else "</span>")
;;

open Lang;;

let istr_to_str istr =
  match istr with
    | STOP -> "STOP"
    | ADD -> "ADD"
    | MUL -> "MUL"
    | SUB -> "SUB"
    | DIV -> "DIV"
    | SDIV -> "SDIV"
    | MOD -> "MOD"
    | SMOD -> "SMOD"
    | ADDMOD -> "ADDMOD"
    | MULMOD -> "MULMOD"
    | SIGNEXTEND -> "SIGNEXTEND"
    | EXP -> "EXP"
    | GT -> "GT"
    | SGT -> "SGT"
    | EQ -> "EQ"
    | LT -> "LT"
    | SLT -> "SLT"
    | AND -> "AND"
    | OR -> "OR"
    | XOR -> "XOR"
    | NOT -> "NOT"
    | BYTE -> "BYTE"
    | ISZERO -> "ISZERO"
    | SHA3 -> "SHA3"
    | ADDRESS -> "ADDRESS"
    | BALANCE -> "BALANCE"
    | ORIGIN -> "ORIGIN"
    | CALLER -> "CALLER"
    | CALLVALUE -> "CALLVALUE"
    | CALLDATALOAD -> "CALLDATALOAD"
    | CALLDATASIZE -> "CALLDATASIZE"
    | CALLDATACOPY -> "CALLDATACOPY"
    | CODESIZE -> "CODESIZE"
    | CODECOPY -> "CODECOPY"
    | GASPRICE -> "GASPRICE"
    | EXTCODESIZE -> "EXTCODESIZE"
    | EXTCODECOPY -> "EXTCODECOPY"
    | BLOCKHASH -> "BLOCKHASH"
    | COINBASE -> "COINBASE"
    | TIMESTAMP -> "TIMESTAMP"
    | NUMBER -> "NUMBER"
    | DIFFICULTY -> "DIFFICULTY"
    | GASLIMIT -> "GASLIMIT"
    | POP -> "POP"
    | MLOAD -> "MLOAD"
    | MSTORE -> "MSTORE"
    | MSTORE8 -> "MSTORE8"
    | SLOAD -> "SLOAD"
    | SSTORE -> "SSTORE"
    | JUMP -> "JUMP"
    | JUMPI -> "JUMPI"
    | PC -> "PC"
    | MSIZE -> "MSIZE"
    | GAS -> "GAS"
    | JUMPDEST -> "JUMPDEST"
    | PUSH_N data -> "PUSH_N"^(BatString.implode data)
    | DUP1 -> "DUP1"
    | DUP2 -> "DUP2"
    | DUP3 -> "DUP3"
    | DUP4 -> "DUP4"
    | DUP5 -> "DUP5"
    | DUP6 -> "DUP6"
    | DUP7 -> "DUP7"
    | DUP8 -> "DUP8"
    | DUP9 -> "DUP9"
    | DUP10 -> "DUP10"
    | DUP11 -> "DUP11"
    | DUP12 -> "DUP12"
    | DUP13 -> "DUP13"
    | DUP14 -> "DUP14"
    | DUP15 -> "DUP15"
    | DUP16 -> "DUP16"
    | SWAP1 -> "SWAP1"
    | SWAP2 -> "SWAP2"
    | SWAP3 -> "SWAP3"
    | SWAP4 -> "SWAP4"
    | SWAP5 -> "SWAP5"
    | SWAP6 -> "SWAP6"
    | SWAP7 -> "SWAP7"
    | SWAP8 -> "SWAP8"
    | SWAP9 -> "SWAP9"
    | SWAP10 -> "SWAP10"
    | SWAP11 -> "SWAP11"
    | SWAP12 -> "SWAP12"
    | SWAP13 -> "SWAP13"
    | SWAP14 -> "SWAP14"
    | SWAP15 -> "SWAP15"
    | SWAP16 -> "SWAP16"
    | LOG0 -> "LOG0"
    | LOG1 -> "LOG1"
    | LOG2 -> "LOG2"
    | LOG3 -> "LOG3"
    | LOG4 -> "LOG4"
    | CREATE -> "CREATE"
    | CALL -> "CALL"
    | DELEGATECALL -> "DELEGATECALL"
    | CALLCODE -> "CALLCODE"
    | RETURN -> "RETURN"
    | SUICIDE -> "SUICIDE"
    | UNKNOWN str -> "UNKNOWN "^(BatString.implode str);;

let cond_to_str cond =
  begin
    match cond with
      | Coq_is_zero v
      | Coq_is_not_zero v ->
	a_val_to_str v
  end^
  begin
    match cond with
      | Coq_is_zero _ -> " is zero."
      | Coq_is_not_zero _ -> " is not zero."
  end;;

let rec simplify_cond c =
  match c with
    | Coq_is_zero (Ais_zero v) ->
      simplify_cond (Coq_is_not_zero v)
    | Coq_is_not_zero (Ais_zero v) ->
      simplify_cond (Coq_is_zero v)
    | _ -> c;;

let show_condition cond : string =
  Printf.sprintf "<li>%s</li>\n" (cond_to_str (simplify_cond cond));;

let stack_to_str stc =
  "["^
    (StringLabels.concat ", " (CoqList.map a_val_to_str stc))
  ^"]"^(Printf.sprintf "(size %d)" (len stc))

let state_to_str s =
  Printf.sprintf
  ("{<div style='margin-left:1em;'>  stack: %s<br>  memory: %s<br>  storage: %s<br>  log: XXX<br>  remaining_program: XXX</div>}")
    (stack_to_str s.a_stc)
    (a_memory_to_str s.a_mem true)
    (a_storage_to_str s.a_str true)
;;

let print_call c =
  Printf.sprintf "code at address: %s <br>" (a_val_to_str c.a_call_code)^
  Printf.sprintf "recipient address: %s <br>" (a_val_to_str c.a_call_recipient)^
  Printf.sprintf "value: %s <br>" (a_val_to_str c.a_call_value)^
  Printf.sprintf "caller: %s <br>" (a_val_to_str c.a_caller)
;;

let print_create c =
  Printf.sprintf "with value: %s <br>" (a_val_to_str c.a_create_value)^
  Printf.sprintf "with code from memory idx %s and size %s<br>"
    (a_val_to_str c.a_create_mem_start)
    (a_val_to_str c.a_create_mem_size)
;;

let print_extcode_copy e =
  Printf.sprintf "with addr: %s <br>" (a_val_to_str e.a_extcode_copy_addr)^
  Printf.sprintf "with memory start: %s <br>" (a_val_to_str e.a_extcode_copy_memory_start)^
  Printf.sprintf "with code start: %s <br>" (a_val_to_str e.a_extcode_copy_code_start)^
  Printf.sprintf "with length: %s <br>" (a_val_to_str e.a_extcode_copy_len)
;;

let show_single_result r =
  match r with
    | Coq_continue s -> Printf.sprintf "still <strong>running</strong> with state %s." (state_to_str s)
    | Coq_suicide addr -> Printf.sprintf "<strong>suicide</strong>s with inheritance to %s." (a_val_to_str addr)
    | Coq_returned (output, state) -> Printf.sprintf "<strong>return</strong>s with output %s and state %s." (a_memory_to_str (simplify_mem output) true) (state_to_str state)
    | Coq_stopped s -> Printf.sprintf "<strong>stop</strong>s with state %s." (state_to_str s)
    | Coq_calling c -> (Printf.sprintf "<strong>call</strong>s something:<br>")^
             (print_call c)^
      Printf.sprintf "<br>It's unknown what happens during/after the call."
    | Coq_creating c -> (Printf.sprintf "tries to <strong>create</strong> something:<br>")^
             (print_create c)^
      Printf.sprintf "<br>It's unknown what happens during/after the create."
    | Coq_extcode_copying e ->
        (Printf.sprintf "tries to <strong>copy code of</strong> an account:<br>")^
             (print_extcode_copy e)^
      Printf.sprintf "<br>It's unknown what happens during/after the code copying."
    | Coq_end_of_program s -> Printf.sprintf "reaches the <strong>end of the program</strong> with state %s." (state_to_str s)
    | Coq_failure s -> Printf.sprintf "causes runtime error with state %s." (state_to_str s)
    | Coq_not_implemented (istr, st) -> Printf.sprintf "hits an unimplemented instruction %s in this analyzer." (istr_to_str istr)
    | Coq_decode_fail str -> Printf.sprintf "causing parsing failure in this analyzer: %s." (BatString.implode str)
    | Coq_back_jmp s -> Printf.sprintf "causes a backward jump (and so the automatic analysis gives up).  The final state is %s." (state_to_str s)
;;

let show_result num ((conds : a_prop list), r) =
  (Printf.sprintf "<h3>Behavior %d</h3>" num)^
  (Printf.sprintf "<p>under conditions:</p>")^
  (Printf.sprintf "<ol>\n")^
  (if conds = [] then "<li>unconditionally!</li>" else
    BatString.join "\n" (List.map show_condition conds))^
  (Printf.sprintf "</ol>\n")^
  (show_single_result r)
;;

let port = ref 8000

let specs = [
  ('p', "port", None, Some (fun str -> port := int_of_string str))
]

let filter_hex =
  BatString.filter
    (fun c ->
     match c with
     | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' | 'a' | 'b'| 'c' | 'd' |'e' |'f' | 'x' -> true
     | _ -> false)

(* returns true when two abstract values are known to be equal *)
let rec aval_eq a b =
  (match a, b with
  | Acaller, Acaller -> true
  | Atime, Atime -> true
  | Adatasize, Adatasize -> true
  | Avalue, Avalue -> true
  | Aaddress, Aaddress -> true
  | Abalance v, Abalance w -> aval_eq v w
  | Adifficulty, Adifficulty -> true
  | Agaslimit, Agaslimit -> true
  | Ablockhash, Ablockhash -> true
  | Ablock_number, Ablock_number -> true
  | Aimm_nat abig, Aimm_nat bbig -> Big_int.eq_big_int abig bbig
  | Aunknown _, _ -> false
  | _, Aunknown _ -> false
  | Ais_zero av, Ais_zero bv -> aval_eq av bv
  | Azero, Azero -> true
  | Asub (a0, a1), Asub (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aadd (a0, a1), Aadd (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aand (a0, a1), Aand (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aor (a0, a1), Aor (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Axor (a0, a1), Axor (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aexp (a0, a1), Aexp (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Adiv (a0, a1), Adiv (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Asdiv (a0, a1), Asdiv (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Amod (a0, a1), Amod (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Asmod (a0, a1), Asmod (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Amul (a0, a1), Amul (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Agt (a0, a1), Agt (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aextcodesize a, Aextcodesize b -> aval_eq a b
  | Asignextend (a0, a1), Asignextend (b0, b1) ->
     aval_eq a0 b0 && aval_eq a1 b1
  | Anot a_, Anot b_ -> aval_eq a_ b_
  | Asha3 am, Asha3 bm -> false
  | Alt (a0, a1), Alt (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aslt (a0, a1), Aslt (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Abyte (a0, a1), Abyte (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aeq (a0, a1), Aeq (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aget32 (ai, am), Aget32 (bi, bm) -> aval_eq ai bi && am_eq am bm
  | (Aget_storage (ai, a_s), Aget_storage (bi, b_s)) ->
     aval_eq ai bi && ast_eq a_s b_s
  | _, _ -> false)
and ast_eq a b =
  match a, b with
  | Ainitial_storage, Ainitial_storage -> true
  | _, _ -> false
and am_eq a b =
  match a, b with
  | Adata, Adata -> true
  | _, _ -> false

let rec parse_storage_inner (strs : string list) (current : Evm.AbstractEVM.a_storage) : Evm.AbstractEVM.a_storage =
  match strs with
  | [] -> current
  | [a] ->
     Printf.eprintf "single %s\n%!" a;
     failwith "odd number of strings"
  | k :: v :: rest ->
     Printf.eprintf "pair %s %s\n%!" k v;
     let k = Big_int.big_int_of_string k in
     let v = Big_int.big_int_of_string v in
     parse_storage_inner rest Evm.AbstractEVM.(Aput_storage (Aimm_nat k, Aimm_nat v, current))

let parse_storage (input : string option) : Evm.AbstractEVM.a_storage =
  match input with
  | None -> Evm.AbstractEVM.Ainitial_storage
  | Some str -> parse_storage_inner (Str.split (Str.regexp "[ \t\n\012\r]+") str) Evm.AbstractEVM.Ainitial_storage
  ;;


let generate_link code steps =
  Printf.sprintf "./?nsteps=%s&contract=%s" (string_of_int steps) code

let body_creator uri meth headers =
  (fun body ->
   ((Printf.sprintf "<html>
<head>
<title>Dr. Y's Ethereum Contract Analyzer</title>
<style>
.memory {padding: 2px; padding-left: 5px; }
body { background-color: #cfc; color: #000; padding: 3em; }
</style>
</head>
<body>
<h1><a href=\".\">Dr. Y's Ethereum Contract Analyzer</a></h1>
<form action=\".\" method=\"get\">
Maximal number of steps to analyze:
<input type=\"text\" value=\"%s\" name=\"nsteps\"><br>
Contract:<br>
<textarea rows='8' cols='48' name='contract'>%s</textarea><br>
<input type=\"submit\" value=\"Analyze\" style=\"font-size: 200%%; background-color: green; color: white; border: none;\"> <br>
Storage (optional):<br>
<textarea rows='2' cols='48' name='storage'>%s</textarea><br>
</form>"
(match Uri.get_query_param uri "nsteps" with
 | None -> "400"
 | Some str -> string_of_int (int_of_string str)
)
(match Uri.get_query_param uri "contract" with
 | None -> "0x3660008037602060003660003473273930d21e01ee25e4c219b63259d214872220a261235a5a03f21560015760206000f3"
 | Some str ->
    let filtered = filter_hex str in
    filtered
)
(match Uri.get_query_param uri "storage" with
 | None -> ""
 | Some str -> str)
)
    ^
(match Uri.get_query_param uri "contract", Uri.get_query_param uri "nsteps" with
 | None, _ ->  ""
 | _, None -> ""
 | Some code, Some steps ->
    try
      let filtered = filter_hex code in
      let steps = (if filtered = "0x0x0x" then 400 else int_of_string steps) in
      let steps = if steps < 0 then 0 else steps in
      let code_coq : char list = BatString.explode filtered in
      let storage_coq : Evm.AbstractEVM.a_storage = parse_storage (Uri.get_query_param uri "storage") in
      let (result, result_len)  =
	a_run aval_eq number_checker steps code_coq storage_coq
    in
    (Printf.sprintf
      "<h2>Code</h2>
<pre style=\"word-break: break-all; white-space: pre-wrap;\">%s</pre>
<h2>Behaviors</h2>
<p>%d behaviors cover the possibilities (assuming enough gas).</p>
<p><a href=\"%s\">back</a> <a href=\"%s\">fwd</a></p>
"
(filter_hex code)
(Big_int.int_of_big_int result_len)
(generate_link filtered (steps - 1))
(generate_link filtered (steps + 1))
)^
(BatString.concat "\n" (List.mapi show_result result))
      with TooManyCases ->
	Printf.sprintf "<h2>Results</h2><p>Too many behaviors found.  Maybe there is a loop.</p>"
     | e -> 
	Printf.printf "an exception %s %s \n%!" (Printexc.to_string e) (Printexc.get_backtrace ());
        raise e
)
    ^
("
<hr>
<h2>TODO</h2>
<ul>
<li>Consider the stack depsth limitation.</li>
<li>Consider uint256 overflow/underflow (currently the concrete values are taken as natural numbers).</li>
<li>Test the symbolic execution against other implementations.</li>
<li>Translate the Yellow Paper faithfully to a theorem prover and then prove that the symbolic execution matches the Yellow Paper.</li>
</ul>
<hr>
<address>
Yoichi Hirai
<br>Contact: i@yoichihirai.com</address>
<address><a href=\"https://github.com/pirapira/dry-analyzer\">GitHub: view source and file issues</a></address>
</body>
</html>")
		   ))

let callback _conn req body =
  let uri = req |> Request.uri in
  let meth = req |> Request.meth |> Code.string_of_method in
  let headers = req |> Request.headers |> Header.to_string in
  body |> Cohttp_lwt_body.to_string >|=
    body_creator uri meth headers
  >>= (fun body -> Server.respond_string ~status:`OK ~body ())
  >>= (fun k ->
       Lwt_log.notice_f "%f %s %s %s" (Unix.time ()) (uri |> Uri.to_string) meth headers >>=
	 (fun _ -> return k)
      )

let () =
  Printexc.record_backtrace true;
  Getopt.parse_cmdline specs print_endline;
  let server =
    Server.create ~mode:(`TCP (`Port !port)) (Server.make ~callback ()) in
  let () = Printf.printf "Starting a web server at port %d\n%!" !port in
  ignore (Lwt_main.run server)
