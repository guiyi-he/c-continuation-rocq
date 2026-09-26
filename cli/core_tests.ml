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
  let debug_states = Mod15Example.requested_derivative_debug_states in
  assert (List.length debug_states = 182);
  assert (Mod15Example.residue_state_count = 182);
  assert Mod15Example.all_debug_states_replayb;
  List.iteri (fun i q ->
    assert (q.Mod15Example.debug_id = i);
    assert (List.length q.Mod15Example.debug_representative = 15);
    assert (rewpla_nullable_char
      (requested_debug_representative_char
        q.Mod15Example.debug_witness q.Mod15Example.debug_representative)
      = q.Mod15Example.debug_accepting);
    assert (List.length q.Mod15Example.debug_transitions = 2);
    List.iter (fun tr ->
      assert (tr.Mod15Example.debug_target >= 0);
      assert (tr.Mod15Example.debug_target < 182))
      q.Mod15Example.debug_transitions) debug_states;
  assert (List.fold_left (fun n q ->
    n + List.length q.Mod15Example.debug_transitions) 0 debug_states = 364);
  let representatives =
    List.map (fun q -> q.Mod15Example.debug_representative) debug_states in
  assert (List.length (List.sort_uniq compare representatives) = 182);
  let wa = WAtom (Char.code 'a') and wb = WAtom (Char.code 'b') in
  let aci = rewpla_aci_normalize_char in
  assert (rewpla_eqb_char (aci (WPlus (wa, wb)))
    (aci (WPlus (wb, wa))));
  assert (rewpla_eqb_char
    (aci (WPlus (WPlus (wa, wb), wa)))
    (aci (WPlus (wa, wb))));
  assert (rewpla_eqb_char
    (aci (rewpla_simplify_char (WPlus (WConcat (WEps, wa),
      WConcat (wa, WEps))))) (aci wa));
  let positive = rewpla_positive_normalize_char in
  let same_positive r s = rewpla_eqb_char (positive r) (positive s) in
  let la = WLookahead wa and lb = WLookahead wb in
  (* P1--P9: idempotent union, units, associativity and both
     distributivity laws are reflected in the extracted key. *)
  assert (same_positive (WPlus (wa, WPlus (wb, wa)))
    (WPlus (wb, wa)));
  assert (same_positive (WConcat (WPlus (wa, wb), WPlus (wa, wb)))
    (WPlus (WPlus (WConcat (wa, wa), WConcat (wa, wb)),
      WPlus (WConcat (wb, wa), WConcat (wb, wb)))));
  assert (same_positive (WConcat (WConcat (WEps, wa), wb))
    (WConcat (wa, WConcat (wb, WEps))));
  assert (same_positive (WConcat (WPlus (wa, WZero), WZero)) WZero);
  (* P10--P11 apply to adjacent positive logical factors only. *)
  assert (same_positive (WConcat (WConcat (la, lb), la))
    (WConcat (lb, la)));
  assert (same_positive (WConcat (WPlus (la, lb), la))
    (WPlus (la, WConcat (la, lb))));
  assert (same_positive
    (WConcat (WPlus (la, lb), WPlus (la, lb))) (WPlus (la, lb)));
  assert (not (same_positive (WConcat (wa, wb)) (WConcat (wb, wa))));
  assert (not (same_positive (WConcat (wa, wa)) wa));
  let alpha = [Char.code 'a'; Char.code 'b'; Char.code 'c'] in
  let one_a = WPlus (WLookahead wa, wa) in
  let guarded_ab = WPlus
    (WConcat (WConcat (WLookahead (WConcat (wa, wb)), wa),
      WPlus (wb, WAtom (Char.code 'c'))), WAtom (Char.code 'c')) in
  let accepts_rw r w = rewpla_nullable_char
    (rewpla_normalized_word_step_char w r) in
  let accepts_paper r w = rewpla_nullable_char
    (rewpla_paper_word_step_char w r) in
  List.iter (fun w ->
    assert (accepts_rw one_a w = (w = [Char.code 'a']));
    assert (accepts_rw guarded_ab w =
      (w = [Char.code 'a'; Char.code 'b'] || w = [Char.code 'c']));
    assert (accepts_paper one_a w = (w = [Char.code 'a']));
    assert (accepts_paper guarded_ab w =
      (w = [Char.code 'a'; Char.code 'b'] || w = [Char.code 'c'])))
    (words alpha 3);
  assert (rewpla_states_closedb_char alpha [WZero]);
  assert (rewpla_states_closedb_char alpha [WEps; WZero]);
  assert (not (rewpla_states_closedb_char alpha [wa]));
  assert (rewpla_paper_states_closedb_char alpha [WZero]);
  assert (rewpla_paper_states_closedb_char alpha [WEps; WZero]);
  assert (not (rewpla_paper_states_closedb_char alpha [wa]));
  let sigma = WPlus (wa, wb) in
  let even_suffix = WStar (WConcat (sigma, sigma)) in
  let periodic2 = WConcat
    (WConcat (WStar sigma, wa), WLookahead even_suffix) in
  let rec direct_periodic2 = function
    | [] -> false
    | x :: suffix ->
        (x = Char.code 'a' && List.length suffix mod 2 = 0) ||
        ((x = Char.code 'a' || x = Char.code 'b') &&
         direct_periodic2 suffix) in
  List.iter (fun w ->
    assert (accepts_paper periodic2 w = direct_periodic2 w))
    (words [Char.code 'a'; Char.code 'b'] 6);
  (* Independently evaluate the suffix-length condition for every prefix
     ending at a trigger. This checks both empty-main context residuals and
     projected acceptance for the extracted parameterized transition. *)
  let periodic_cases = [
    (15, [3;5], [97;98], 97);
    (6, [2;3], [97;98], 98);
    (4, [2;4], [120;121;122], 122);
    (7, [1;7], [97;98], 98);
    (3, [3], [97;98], 97);
    (12, [2;3;4], [97;98], 97)
  ] in
  List.iter (fun (modulus, periods, alphabet, trigger) ->
    let base = periodic_base_char modulus periods in
    let zero = periodic_zeros_char modulus in
    let step s a = periodic_step_char trigger base s a in
    assert (List.length base = modulus);
    let suffix_ok n = List.exists (fun p -> n mod p = 0) periods in
    let rec direct_context context_length = function
      | [] -> false
      | a :: suffix ->
          (a = trigger && suffix_ok (List.length suffix + context_length)) ||
          direct_context context_length suffix in
    List.iter (fun w ->
      let bits = List.fold_left step zero w in
      assert (List.length bits = modulus);
      for context_length = 0 to 2 * modulus do
        assert (List.nth bits (context_length mod modulus) =
          direct_context context_length w)
      done) (words alphabet 6)) periodic_cases;
  (* The old certified example is an oracle here; the CLI never reads it. *)
  let dynamic_base = periodic_base_char 15 [3;5] in
  assert (dynamic_base = Mod15Example.base15);
  let sigma_re = Plus (Atom 97, Atom 98) in
  let rec power n = if n = 0 then WEps
    else WConcat (sigma, power (n - 1)) in
  let c3 = WLookahead (WStar (power 3))
  and c5 = WLookahead (WStar (power 5)) in
  let initial35 = WConcat (WConcat (WConcat (WStar sigma, wa), c3), c5) in
  let compact w = periodic_history_representative_char sigma_re 97
    initial35 [3;5] w in
  let proposed_aa = WPlus (initial35,
    WPlus (WConcat (c3, c5), WConcat
      (WLookahead (WConcat (power 2, WStar (power 3))),
       WLookahead (WConcat (power 4, WStar (power 5)))))) in
  let d3 = WLookahead (WConcat (power 2, WStar (power 3)))
  and d5 = WLookahead (WConcat (power 4, WStar (power 5))) in
  let expanded_aa = WPlus (initial35, WPlus (WConcat (c3, c5),
    WPlus (WConcat (d3, d5), WPlus (d3, d5)))) in
  let administrative_normalize r = aci (rewpla_paper_normalize_char r) in
  assert (rewpla_eqb_char (administrative_normalize (compact [97;97]))
    (administrative_normalize expanded_aa));
  (* The shifted product alone drops Eq. (20)'s epsilon-factor terms. *)
  assert (accepts_paper (compact [97;97]) [98;98]);
  assert (not (accepts_paper proposed_aa [98;98]));
  let suffixes = words [97;98] 4 in
  let rec direct35 = function
    | [] -> false
    | a :: suffix ->
        (a = 97 && (List.length suffix mod 3 = 0 ||
                     List.length suffix mod 5 = 0)) || direct35 suffix in
  List.iter (fun q ->
    let witness = List.map (fun a -> if a then 97 else 98)
      q.Mod15Example.debug_witness in
    let replay = List.fold_left (periodic_step_char 97 dynamic_base)
      (periodic_zeros_char 15) witness in
    assert (replay = q.Mod15Example.debug_representative);
    let display = compact witness in
    assert (rewpla_nullable_char display = q.Mod15Example.debug_accepting);
    List.iter (fun suffix ->
      assert (accepts_paper display suffix = direct35 (witness @ suffix))) suffixes;
    List.iter (fun a ->
      assert (periodic_step_char 97 dynamic_base replay a =
        Mod15Example.residue_step replay (a = 97))) [97;98]) debug_states;
  let tight_accepts k w = tight_finalb_char
    (List.fold_left (tight_step_char k) tight_initial_char w) in
  assert (tight_accepts 2 [TLa; TLd; TLhash]);
  assert (tight_accepts 2 [TLa; TLb; TLd; TLhash]);
  assert (tight_accepts 2 [TLa; TLc; TLd; TLe; TLx; TLhash]);
  assert (not (tight_accepts 2 [TLa; TLc; TLd; TLx; TLhash]));
  assert (not (tight_accepts 2 [TLa; TLd]));
  Printf.printf "checked %d expressions and %d words: OK\n"
    (List.length expressions) (List.length ws)
