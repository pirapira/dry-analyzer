open Getopt
open Lwt
open Cohttp
open Cohttp_lwt_unix

open Evm2;;

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
    | Aput (addr, v, orig) ->
      Aput ((simplify_val addr), (simplify_val v), (simplify_mem orig))
    | _ -> m;;


let rec a_val_to_str v =
  let bin = binary a_val_to_str in
  match v with
    | Acaller -> "(address of caller)"
    | Atime   -> "(timestamp)"
    | Adatasize -> "(size of input)"
    | Avalue  -> "(value of this call)"
    | Aaddress -> "(address of this contract)"
    | Abalance -> "(balance of this contract)"
    | Aunknown_remaining_gas -> "(remaining gas (XXX make this more precise))"
    | Ais_zero v' -> "(is_zero "^a_val_to_str v'^")"
    | Azero -> "0"
    | Asub (v0, v1) -> bin " - " v0 v1
    | Aadd (v0, v1) -> bin " + " v0 v1
    | Aand (v0, v1) -> bin " and " v0 v1
    | Aor  (v0, v1) -> bin " or " v0 v1
    | Axor (v0, v1) -> bin " xor " v0 v1
    | Aexp (v0, v1) -> bin " ** " v0 v1
    | Adiv (v0, v1) -> bin " / " v0 v1
    | Amul (v0, v1) -> bin " * " v0 v1
    | Agt (v0, v1) -> bin " > " v0 v1
    | Anot v -> "(not "^(a_val_to_str v)^")"
    | Alt (v0, v1) -> bin " < " v0 v1
    | Aeq (v0, v1) -> bin " == " v0 v1
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
    | Aput (addr,v,orig) ->
      Printf.sprintf "(mem_write addr: %s val: %s in %s)" (a_val_to_str addr) (a_val_to_str v) (a_memory_to_str orig block)
    | Amemwrite (start_addr, len, source, mem) ->
      Printf.sprintf "%s; copy from %s [0, %s) at offset %s" (a_memory_to_str mem block) (a_memory_to_str source false) (a_val_to_str len) (a_val_to_str start_addr)
    | Adata -> "(input data)"
    | Adrop (num, orig) -> Printf.sprintf "(drop first %s bytes from %s)"
      (a_val_to_str num) (a_memory_to_str orig block)
    | Atake (start, size, orig) -> Printf.sprintf "(take %s bytes at %s from %s)"
      (a_val_to_str size) (a_val_to_str start) (a_memory_to_str orig block)
    | Amem_imm _ -> "a_mem_to_str imm not implemented"
    | Acodecopy _ -> "a_mem_to_str: codecopy not implemented"
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
  Printf.sprintf "value: %s <br>" (a_val_to_str c.a_call_value)
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

let token = "0x6060604052361561008a576000357c010000000000000000000000000000000000000000000000000000000090048063181670e61461008c5780631fa03a2b146100c157806370a08231146100f65780638c915b9214610122578063930b7a2314610160578063b7760c8f14610195578063daea85c5146101ca578063fbf1f78a146101f65761008a565b005b6100ab60048080359060200190919080359060200190919050506109ee565b6040518082815260200191505060405180910390f35b6100e060048080359060200190919080359060200190919050506108a7565b6040518082815260200191505060405180910390f35b61010c60048080359060200190919050506105e6565b6040518082815260200191505060405180910390f35b61014a6004808035906020019091908035906020019091908035906020019091905050610356565b6040518082815260200191505060405180910390f35b61017f600480803590602001909190803590602001909190505061091a565b6040518082815260200191505060405180910390f35b6101b46004808035906020019091908035906020019091905050610222565b6040518082815260200191505060405180910390f35b6101e06004808035906020019091905050610624565b6040518082815260200191505060405180910390f35b61020c6004808035906020019091905050610707565b6040518082815260200191505060405180910390f35b600082600060005060003373ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600050541015156103465782600060005060003373ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008282825054039250508190555082600060005060008473ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828282505401925050819055508173ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef856040518082815260200191505060405180910390a3600190506103505661034f565b60009050610350565b5b92915050565b6000600083600060005060008773ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600050541015156105d45760009050600160005060008673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060005060003373ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060009054906101000a900460ff161561040a576001905080506104d3565b600260005060008673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060005060003373ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060005054841115156104d2576001905080506000600260005060008773ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060005060003373ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600050819055505b5b60018114156105c65783600060005060008773ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008282825054039250508190555083600060005060008573ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828282505401925050819055508273ffffffffffffffffffffffffffffffffffffffff168573ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef866040518082815260200191505060405180910390a3600191506105de566105cf565b600091506105de565b6105dd565b600091506105de565b5b509392505050565b6000600060005060008373ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060005054905061061f565b919050565b60006001600160005060003373ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060005060008473ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060006101000a81548160ff021916908302179055508173ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f0e40f4b0b06b7d270eb92aed48caf256e6bbe4f83c5492e7433958cf5566192060016040518082815260200191505060405180910390a360019050610702565b919050565b60006000600160005060003373ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060005060008473ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060006101000a81548160ff021916908302179055506000600260005060003373ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060005060008473ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600050819055508173ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f0e40f4b0b06b7d270eb92aed48caf256e6bbe4f83c5492e7433958cf5566192060006040518082815260200191505060405180910390a38173ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fcc92c05edef6bc5dcdfab43862409620fd81888eec1be99935f19375c4ef704e60006040518082815260200191505060405180910390a35b919050565b6000600160005060008473ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060005060008373ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060009054906101000a900460ff169050610914565b92915050565b600081600260005060003373ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060005060008573ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600050819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fcc92c05edef6bc5dcdfab43862409620fd81888eec1be99935f19375c4ef704e846040518082815260200191505060405180910390a3600190506109e8565b92915050565b6000600260005060008473ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060005060008373ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600050549050610a51565b9291505056";;

let rec aval_eq a b =
  (match a, b with
  | Acaller, Acaller -> true
  | Atime, Atime -> true
  | Adatasize, Adatasize -> true
  | Avalue, Avalue -> true
  | Aaddress, Aaddress -> true
  | Abalance, Abalance -> true
  | Aimm_nat abig, Aimm_nat bbig -> Big_int.eq_big_int abig bbig
  | Aunknown_remaining_gas, Aunknown_remaining_gas -> false
  | Ais_zero av, Ais_zero bv -> aval_eq av bv
  | Azero, Azero -> true
  | Asub (a0, a1), Asub (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aadd (a0, a1), Aadd (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aand (a0, a1), Aand (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aor (a0, a1), Aor (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Axor (a0, a1), Axor (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Aexp (a0, a1), Aexp (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Adiv (a0, a1), Adiv (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Amul (a0, a1), Amul (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Agt (a0, a1), Agt (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
  | Anot a_, Anot b_ -> aval_eq a_ b_
  | Asha3 am, Asha3 bm -> false
  | Alt (a0, a1), Alt (b0, b1) -> aval_eq a0 b0 && aval_eq a1 b1
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
<input type=\"submit\" value=\"Analyze\" style=\"font-size: 200%%; background-color: green; color: white; border: none;\">
</form>"
(match Uri.get_query_param uri "nsteps" with
 | None -> "400"
 | Some str -> string_of_int (int_of_string str)
)
(match Uri.get_query_param uri "contract" with
 | None -> "0x3660008037602060003660003473273930d21e01ee25e4c219b63259d214872220a261235a5a03f21560015760206000f3"
 | Some str ->
    let filtered = filter_hex str in
    if filtered = "0x0x0x" then token
    else filtered
)
)
    ^
(match Uri.get_query_param uri "contract", Uri.get_query_param uri "nsteps" with
 | None, _ ->  ""
 | _, None -> ""
 | Some code, Some steps ->
    try
      let filtered = filter_hex code in
      let steps = (if filtered = "0x0x0x" then 400 else int_of_string steps) in
      let code_coq : char list = BatString.explode (
				     if filtered = "0x0x0x" then token
				     else filtered) in
      let (result, result_len)  =
	a_run aval_eq number_checker steps code_coq
    in
    (Printf.sprintf
      "<h2>Code</h2>
<pre style=\"word-break: break-all; white-space: pre-wrap;\">%s</pre>
<h2>Behaviors</h2>
<p>%d behaviors cover the possibilities (assuming enough gas).</p>
"
(let filtered = filter_hex code in
    if filtered = "0x0x0x" then token
    else filtered)
(Big_int.int_of_big_int result_len))^
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
<li>Translate the Yellow Ppaer faithfully to a theorem prover and then prove that the symbolic execution matches the Yellow Paper.</li>
</ul>
<hr>
<address>
Dr. Y is a hobby-time entity, whose identity will be revealed when the hobby is no longer a hobby.
<br>Contact: dr-y@hushmail.com</address>
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
  ignore (Lwt_main.run server)
