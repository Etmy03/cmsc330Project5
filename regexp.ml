open List
open Nfa

(*********)
(* Types *)
(*********)

type regexp_t =
  | Empty_String
  | Char of char
  | Union of regexp_t * regexp_t
  | Concat of regexp_t * regexp_t
  | Star of regexp_t

(***********)
(* Utility *)
(***********)

let fresh =
  let cntr = ref 0 in
  fun () ->
    cntr := !cntr + 1 ;
    !cntr

(*******************************)
(* Part 3: Regular Expressions *)
(*******************************)

let create_nfa () =
  let start = fresh () in
  let accepting = fresh () in
  let transition = [(start, None, accepting)] in
  { sigma = []; qs = [start; accepting]; q0 = start; fs = [accepting]; delta = transition }
;;

let merge_nfas nfa1 nfa2 =
  let fresh_states nfa =
    let new_states = List.map (fun q -> fresh ()) nfa.qs in
    let state_map = List.combine nfa.qs new_states in
    (new_states, state_map)
  in

  let (new_states1, state_map1) = fresh_states nfa1 in
  let (new_states2, state_map2) = fresh_states nfa2 in

  let translate_state state state_map =
    List.assoc state state_map
  in

  let translate_transition (q, sym, q') state_map =
    (translate_state q state_map, sym, translate_state q' state_map)
  in

  let new_transitions1 = List.map (fun trans -> translate_transition trans state_map1) nfa1.delta in
  let new_transitions2 = List.map (fun trans -> translate_transition trans state_map2) nfa2.delta in

  let start = fresh () in
  let accepting = fresh () in

  let new_transitions =
    [(start, None, translate_state nfa1.q0 state_map1);
     (start, None, translate_state nfa2.q0 state_map2);
     (translate_state (List.hd nfa1.fs) state_map1, None, accepting);
     (translate_state (List.hd nfa2.fs) state_map2, None, accepting)]
    @ new_transitions1 @ new_transitions2
  in
  let rec merge_sigma sigma1 sigma2 =
  match sigma1 with
  | [] -> sigma2
  | x :: xs -> if List.mem x sigma2 then merge_sigma xs sigma2 else merge_sigma xs (x :: sigma2)
  in

  let new_states = start :: accepting :: new_states1 @ new_states2 in
  let new_sigma = merge_sigma nfa1.sigma nfa2.sigma in

  { sigma = new_sigma; qs = new_states; q0 = start; fs = [accepting]; delta = new_transitions }
;;


let rec regexp_to_nfa (regexp: regexp_t) : (int, char) nfa_t =
match regexp with
  | Empty_String ->
    create_nfa ()
  | Char c ->
    let nfa = create_nfa () in
    let start, accepting = nfa.q0, List.hd nfa.fs in
    { nfa with sigma = [c]; delta = [(start, Some c, accepting)] }
  | Union (r1, r2) ->
    let nfa1 = regexp_to_nfa r1 in
    let nfa2 = regexp_to_nfa r2 in
    merge_nfas nfa1 nfa2
  | Concat (r1, r2) ->
    let nfa1 = regexp_to_nfa r1 in
    let nfa2 = regexp_to_nfa r2 in
    let start = nfa1.q0 in
    let accepting = List.hd nfa2.fs in
    let new_transitions = [(List.hd nfa1.fs, None, nfa2.q0)] @ nfa1.delta @ nfa2.delta @ [(List.hd nfa2.fs, None, accepting)] in
    let new_states = nfa1.qs @ nfa2.qs in
    let rec merge_sigma sigma1 sigma2 =
    match sigma1 with
      | [] -> sigma2
      | x :: xs -> if List.mem x sigma2 then merge_sigma xs sigma2 else merge_sigma xs (x :: sigma2)
    in
    let new_sigma = merge_sigma nfa1.sigma nfa2.sigma
    in
    { sigma = new_sigma; qs = new_states; q0 = start; fs = [accepting]; delta = new_transitions }
  | Star r ->
    let nfa1 = regexp_to_nfa r in
    let start = fresh () in
    let accepting = fresh () in
    let new_transitions = [(start, None, accepting); (accepting, None, start)] in
    let merged_transitions = new_transitions @ nfa1.delta @ [(start, None, nfa1.q0); (List.hd nfa1.fs, None, accepting)] in
    { sigma = nfa1.sigma; qs = [start; accepting] @ nfa1.qs; q0 = start; fs = [accepting]; delta = merged_transitions }
  


;;

(*****************************************************************)
(* Below this point is parser code that YOU DO NOT NEED TO TOUCH *)
(*****************************************************************)

exception IllegalExpression of string

(* Scanner *)
type token =
  | Tok_Char of char
  | Tok_Epsilon
  | Tok_Union
  | Tok_Star
  | Tok_LParen
  | Tok_RParen
  | Tok_END

let tokenize str =
  let re_var = Str.regexp "[a-z]" in
  let re_epsilon = Str.regexp "E" in
  let re_union = Str.regexp "|" in
  let re_star = Str.regexp "*" in
  let re_lparen = Str.regexp "(" in
  let re_rparen = Str.regexp ")" in
  let rec tok pos s =
    if pos >= String.length s then [Tok_END]
    else if Str.string_match re_var s pos then
      let token = Str.matched_string s in
      Tok_Char token.[0] :: tok (pos + 1) s
    else if Str.string_match re_epsilon s pos then
      Tok_Epsilon :: tok (pos + 1) s
    else if Str.string_match re_union s pos then Tok_Union :: tok (pos + 1) s
    else if Str.string_match re_star s pos then Tok_Star :: tok (pos + 1) s
    else if Str.string_match re_lparen s pos then Tok_LParen :: tok (pos + 1) s
    else if Str.string_match re_rparen s pos then Tok_RParen :: tok (pos + 1) s
    else raise (IllegalExpression ("tokenize: " ^ s))
  in
  tok 0 str

let tok_to_str t =
  match t with
  | Tok_Char v -> Char.escaped v
  | Tok_Epsilon -> "E"
  | Tok_Union -> "|"
  | Tok_Star -> "*"
  | Tok_LParen -> "("
  | Tok_RParen -> ")"
  | Tok_END -> "END"

(*
   S -> A Tok_Union S | A
   A -> B A | B
   B -> C Tok_Star | C
   C -> Tok_Char | Tok_Epsilon | Tok_LParen S Tok_RParen

   FIRST(S) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(A) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(B) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(C) = Tok_Char | Tok_Epsilon | Tok_LParen
 *)

let parse_regexp (l : token list) =
  let lookahead tok_list =
    match tok_list with
    | [] -> raise (IllegalExpression "lookahead")
    | h :: t -> (h, t)
  in
  let rec parse_S l =
    let a1, l1 = parse_A l in
    let t, n = lookahead l1 in
    match t with
    | Tok_Union ->
        let a2, l2 = parse_S n in
        (Union (a1, a2), l2)
    | _ -> (a1, l1)
  and parse_A l =
    let a1, l1 = parse_B l in
    let t, n = lookahead l1 in
    match t with
    | Tok_Char c ->
        let a2, l2 = parse_A l1 in
        (Concat (a1, a2), l2)
    | Tok_Epsilon ->
        let a2, l2 = parse_A l1 in
        (Concat (a1, a2), l2)
    | Tok_LParen ->
        let a2, l2 = parse_A l1 in
        (Concat (a1, a2), l2)
    | _ -> (a1, l1)
  and parse_B l =
    let a1, l1 = parse_C l in
    let t, n = lookahead l1 in
    match t with Tok_Star -> (Star a1, n) | _ -> (a1, l1)
  and parse_C l =
    let t, n = lookahead l in
    match t with
    | Tok_Char c -> (Char c, n)
    | Tok_Epsilon -> (Empty_String, n)
    | Tok_LParen ->
        let a1, l1 = parse_S n in
        let t2, n2 = lookahead l1 in
        if t2 = Tok_RParen then (a1, n2)
        else raise (IllegalExpression "parse_C 1")
    | _ -> raise (IllegalExpression "parse_C 2")
  in
  let rxp, toks = parse_S l in
  match toks with
  | [Tok_END] -> rxp
  | _ -> raise (IllegalExpression "parse didn't consume all tokens")


let string_to_regexp str = parse_regexp @@ tokenize str

let string_to_nfa str = regexp_to_nfa @@ string_to_regexp str
