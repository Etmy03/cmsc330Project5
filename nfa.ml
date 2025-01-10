open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

  let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  let transitions = List.filter (fun (q1, myS, q2) -> List.mem q1 qs && (myS = s)) nfa.delta
  in
  List.fold_left (fun acc (_, _, q) -> if List.mem q acc then acc else q::acc) [] transitions;;


let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  let rec e_closure_helper cStates visitedStates =
    let new_states = move nfa cStates None in
    let unvisitedStates = List.filter (fun q -> not (List.mem q visitedStates)) new_states in
    match unvisitedStates with
    | [] -> visitedStates
    | _ ->
      let updated_visitedStates = visitedStates @ unvisitedStates in
      e_closure_helper unvisitedStates updated_visitedStates
  in
  e_closure_helper qs qs
  ;;


let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  let s0 = e_closure nfa [nfa.q0] in
  let char_list = explode s in

  let rec accept_helper cStates lst : bool =
    match lst with
    | [] -> List.exists (fun state -> List.mem state nfa.fs) cStates
    | char :: rest ->
      let nextS = e_closure nfa (move nfa cStates (Some char)) in
      accept_helper nextS rest
  in
  accept_helper s0 char_list;;


(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  List.map (fun s -> e_closure nfa (move nfa qs (Some s))) nfa.sigma;;


let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  List.map (fun s -> let dest = List.flatten (List.map (fun state -> e_closure nfa (move nfa [state] (Some s))) qs) in (qs, Some s, dest)) nfa.sigma;;


let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  if List.exists (fun q -> List.mem q nfa.fs) qs then [qs] else [];;


let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t) (work: 'q list list) : ('q list, 's) nfa_t =
match work with
| [] -> dfa  
| qs :: remaining ->
  if not (List.mem qs dfa.qs) then (
    let dfa_states = qs :: dfa.qs in
    let dfa_transitions = new_trans nfa qs @ dfa.delta in
    let dfa_finals = new_finals nfa qs @ dfa.fs in
    let new_worklist = (new_states nfa qs) @ remaining in
    let updated_dfa = { qs = dfa_states; q0 = dfa.q0; sigma = nfa.sigma; delta = dfa_transitions; fs = dfa_finals } in
    nfa_to_dfa_step nfa updated_dfa new_worklist
  ) else
    nfa_to_dfa_step nfa dfa remaining
;;

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
let start_state = e_closure nfa [nfa.q0] in
  let initial_dfa = { 
  sigma = nfa.sigma; 
  q0 = start_state;
  qs = []; 
  fs = [];
  delta = [] 
  
  } in
  let dfa = nfa_to_dfa_step nfa initial_dfa [start_state] in
  dfa
  ;;
