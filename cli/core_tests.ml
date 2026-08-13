open Ccont_core

let rec deriv a = function
  | Zero | Eps -> Zero
  | Atom b -> if a = b then Eps else Zero
  | Plus (r,s) -> Plus (deriv a r, deriv a s)
  | Concat (r,s) ->
      if nullable r then Plus (Concat (deriv a r, s), deriv a s)
      else Concat (deriv a r, s)
  | Star r -> Concat (deriv a r, Star r)

let regex_accept r w = nullable (List.fold_left (fun r a -> deriv a r) r w)

let words alphabet max_len =
  let rec exact n =
    if n = 0 then [[]]
    else List.concat_map (fun a -> List.map (fun w -> a :: w) (exact (n - 1))) alphabet
  in
  let rec upto n = if n < 0 then [] else exact n @ upto (n - 1) in
  upto max_len

let () =
  let a = Atom (Char.code 'a') and b = Atom (Char.code 'b') in
  let expressions = [
    Zero; Eps; a; b; Plus (a,b); Concat (a,b); Star a;
    Concat (Eps,a); Plus (Zero,a); Star (Star a);
    Concat (Star a, Star (Plus (Concat (a,a), b)));
    Plus (Concat (a, Star b), Concat (b, Star a))
  ] in
  let ws = words [Char.code 'a'; Char.code 'b'] 4 in
  let random = Random.State.make [|20260813|] in
  let rec gen depth =
    if depth = 0 then match Random.State.int random 4 with
      | 0 -> Zero | 1 -> Eps | 2 -> a | _ -> b
    else match Random.State.int random 6 with
      | 0 -> Zero | 1 -> Eps | 2 -> a | 3 -> Star (gen (depth - 1))
      | 4 -> Plus (gen (depth - 1), gen (depth - 1))
      | _ -> Concat (gen (depth - 1), gen (depth - 1))
  in
  let expressions = expressions @ List.init 300 (fun _ -> gen 4) in
  List.iteri (fun i r ->
    let ce = (build_ce_char r).machine in
    let quotient = (build_quotient_char r).machine in
    List.iter (fun w ->
      let expected = regex_accept r w in
      if acceptb ce w <> expected then
        failwith (Printf.sprintf "CE mismatch for expression %d" i);
      if acceptb quotient w <> expected then
        failwith (Printf.sprintf "quotient mismatch for expression %d" i)) ws) expressions;
  let paper = Concat (Star a, Star (Plus (Concat (a,a), b))) in
  assert ((build_ce_char paper).machine.state_count = 5);
  assert ((build_quotient_char paper).machine.state_count = 3);
  Printf.printf "checked %d expressions and %d words: OK\n"
    (List.length expressions) (List.length ws)
