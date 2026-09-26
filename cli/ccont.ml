open Ccont_core

exception Parse_error of int * string

type parser = { text : string; mutable pos : int; len : int }

let is_space = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false
let is_letter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

let rec skip p =
  if p.pos < p.len && is_space p.text.[p.pos] then (p.pos <- p.pos + 1; skip p)

let peek p = skip p; if p.pos < p.len then Some p.text.[p.pos] else None
let take p = match peek p with Some c -> p.pos <- p.pos + 1; c | None -> raise (Parse_error (p.pos, "unexpected end of input"))
let fail p msg = raise (Parse_error (p.pos, msg))

let rec parse_union p =
  let left = parse_concat p in
  let rec loop acc = match peek p with
    | Some '+' -> ignore (take p); loop (Plus (acc, parse_concat p))
    | _ -> acc
  in loop left

and parse_concat p =
  let left = parse_repeat p in
  let rec loop acc = match peek p with
    | Some '.' ->
        ignore (take p);
        (match peek p with
         | Some c when is_letter c || c = '0' || c = '1' || c = '(' ->
             loop (Concat (acc, parse_repeat p))
         | _ -> fail p "expected an expression after '.'")
    | Some c when is_letter c || c = '0' || c = '1' || c = '(' ->
        loop (Concat (acc, parse_repeat p))
    | _ -> acc
  in loop left

and parse_repeat p =
  let atom = parse_atom p in
  let rec loop acc = match peek p with
    | Some '*' -> ignore (take p); loop (Star acc)
    | _ -> acc
  in loop atom

and parse_atom p = match peek p with
  | Some c when is_letter c -> ignore (take p); Atom (Char.code c)
  | Some '0' -> ignore (take p); Zero
  | Some '1' -> ignore (take p); Eps
  | Some '(' ->
      ignore (take p);
      let r = parse_union p in
      (match peek p with
       | Some ')' -> ignore (take p); r
       | _ -> fail p "expected ')'")
  | Some c -> fail p (Printf.sprintf "unexpected character '%c'" c)
  | None -> fail p "expected an expression"

let parse s =
  let p = { text = s; pos = 0; len = String.length s } in
  let r = parse_union p in
  match peek p with None -> r | Some c -> fail p (Printf.sprintf "unexpected character '%c'" c)

(* REwPLA parser.  LA(...) is reserved and therefore cannot be interpreted as
   two adjacent literal letters in this mode. *)
let starts_with p token =
  skip p;
  let n = String.length token in
  p.pos + n <= p.len && String.sub p.text p.pos n = token

let rec parse_wunion p =
  let left = parse_wconcat p in
  let rec loop acc = match peek p with
    | Some '+' -> ignore (take p); loop (WPlus (acc, parse_wconcat p))
    | _ -> acc
  in loop left

and parse_wconcat p =
  let left = parse_wrepeat p in
  let rec loop acc = match peek p with
    | Some '.' ->
        ignore (take p);
        (match peek p with
         | Some c when is_letter c || c = '0' || c = '1' || c = '(' ->
             loop (WConcat (acc, parse_wrepeat p))
         | _ -> fail p "expected an expression after '.'")
    | Some c when is_letter c || c = '0' || c = '1' || c = '(' ->
        loop (WConcat (acc, parse_wrepeat p))
    | _ -> acc
  in loop left

and parse_wrepeat p =
  let atom = parse_watom p in
  let rec loop acc = match peek p with
    | Some '*' -> ignore (take p); loop (WStar acc)
    | _ -> acc
  in loop atom

and parse_watom p =
  if starts_with p "LA" then begin
    p.pos <- p.pos + 2;
    match peek p with
    | Some '(' ->
        ignore (take p);
        let r = parse_wunion p in
        (match peek p with
         | Some ')' -> ignore (take p); WLookahead r
         | _ -> fail p "expected ')' after LA expression")
    | _ -> fail p "expected '(' after LA"
  end else
    match peek p with
    | Some c when is_letter c -> ignore (take p); WAtom (Char.code c)
    | Some '0' -> ignore (take p); WZero
    | Some '1' -> ignore (take p); WEps
    | Some '(' ->
        ignore (take p);
        let r = parse_wunion p in
        (match peek p with
         | Some ')' -> ignore (take p); r
         | _ -> fail p "expected ')'")
    | Some c -> fail p (Printf.sprintf "unexpected character '%c'" c)
    | None -> fail p "expected an expression"

let parse_rewpla s =
  let p = { text = s; pos = 0; len = String.length s } in
  let r = parse_wunion p in
  match peek p with None -> r | Some c -> fail p (Printf.sprintf "unexpected character '%c'" c)

let char_of_code n = if 0 <= n && n <= 255 then Char.chr n else '?'

let rec regex_string ?(prec=0) atom = function
  | Zero -> "0"
  | Eps -> "1"
  | Atom a -> atom a
  | Plus (r, s) ->
      let x = regex_string ~prec:1 atom r ^ "+" ^ regex_string ~prec:1 atom s in
      if prec > 1 then "(" ^ x ^ ")" else x
  | Concat (r, s) ->
      let x = regex_string ~prec:2 atom r ^ "." ^ regex_string ~prec:2 atom s in
      if prec > 2 then "(" ^ x ^ ")" else x
  | Star r -> regex_string ~prec:3 atom r ^ "*"

let source_regex r = regex_string (fun n -> String.make 1 (char_of_code n)) r
let continuation r =
  regex_string (fun (n, a) -> Printf.sprintf "%c_%d" (char_of_code a) n) r

let rec rewpla_string ?(prec=0) atom = function
  | WZero -> "0"
  | WEps -> "1"
  | WAtom a -> atom a
  | WPlus (r, s) ->
      let x = rewpla_string ~prec:1 atom r ^ "+" ^ rewpla_string ~prec:1 atom s in
      if prec > 1 then "(" ^ x ^ ")" else x
  | WConcat (WEps, r) | WConcat (r, WEps) ->
      rewpla_string ~prec atom r
  | WConcat (r, s) ->
      let x = rewpla_string ~prec:2 atom r ^ "." ^ rewpla_string ~prec:2 atom s in
      if prec > 2 then "(" ^ x ^ ")" else x
  | WStar r -> rewpla_string ~prec:3 atom r ^ "*"
  | WLookahead r -> "LA(" ^ rewpla_string atom r ^ ")"

let source_rewpla r =
  rewpla_string (fun n -> String.make 1 (char_of_code n)) r

let alphabet r =
  let rec collect acc = function
    | Zero | Eps -> acc
    | Atom a -> if List.mem a acc then acc else a :: acc
    | Plus (x,y) | Concat (x,y) -> collect (collect acc x) y
    | Star x -> collect acc x
  in List.sort compare (collect [] r)

let rewpla_alphabet r =
  let rec collect acc = function
    | WZero | WEps -> acc
    | WAtom a -> if List.mem a acc then acc else a :: acc
    | WPlus (x,y) | WConcat (x,y) -> collect (collect acc x) y
    | WStar x | WLookahead x -> collect acc x
  in List.sort compare (collect [] r)

let transitions alpha b =
  let rec states q acc =
    if q >= b.machine.state_count then List.rev acc else
    let acc = List.fold_left (fun acc a ->
      List.fold_left (fun acc t -> (q,a,t) :: acc) acc (b.machine.trans q a)) acc alpha
    in states (q + 1) acc
  in states 0 []

let info_by_id b id = List.find (fun x -> x.info_id = id) b.infos

let render_text name alpha b =
  let out = Buffer.create 512 in
  Printf.bprintf out "%s\nStates: %d\nInitial: %d\n" name b.machine.state_count b.machine.initial;
  Buffer.add_string out "State details:\n";
  List.iter (fun s ->
    let pos = match s.info_position with
      | None -> "initial"
      | Some (n,a) -> Printf.sprintf "%c_%d" (char_of_code a) n
    in
    Printf.bprintf out "  %d: position=%s members={%s} continuation=%s final=%b\n"
      s.info_id pos (String.concat "," (List.map string_of_int s.info_members))
      (continuation s.info_continuation) s.info_final) b.infos;
  Buffer.add_string out "Transitions:\n";
  List.iter (fun (q,a,t) -> Printf.bprintf out "  %d -%c-> %d\n" q (char_of_code a) t)
    (transitions alpha b);
  Buffer.contents out

let json_escape s =
  let b = Buffer.create (String.length s + 8) in
  String.iter (function
    | '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | '\n' -> Buffer.add_string b "\\n"
    | '\r' -> Buffer.add_string b "\\r"
    | '\t' -> Buffer.add_string b "\\t"
    | c -> Buffer.add_char b c) s;
  Buffer.contents b

let json_string s = "\"" ^ json_escape s ^ "\""
let json_ints xs = "[" ^ String.concat "," (List.map string_of_int xs) ^ "]"

let render_machine_json alpha b =
  let states = List.map (fun s ->
    let position = match s.info_position with
      | None -> "null"
      | Some (n,a) -> Printf.sprintf "{\"index\":%d,\"symbol\":%s}" n (json_string (String.make 1 (char_of_code a)))
    in
    Printf.sprintf
      "{\"id\":%d,\"position\":%s,\"members\":%s,\"continuation\":%s,\"final\":%b}"
      s.info_id position (json_ints s.info_members)
      (json_string (continuation s.info_continuation)) s.info_final) b.infos in
  let edges = List.map (fun (q,a,t) ->
    Printf.sprintf "{\"from\":%d,\"symbol\":%s,\"to\":%d}"
      q (json_string (String.make 1 (char_of_code a))) t) (transitions alpha b) in
  Printf.sprintf "{\"state_count\":%d,\"initial\":%d,\"states\":[%s],\"transitions\":[%s]}"
    b.machine.state_count b.machine.initial (String.concat "," states) (String.concat "," edges)

let dot_escape s = json_escape s

let render_dot_graph name prefix alpha b =
  let out = Buffer.create 512 in
  Printf.bprintf out "  subgraph cluster_%s {\n    label=%s;\n" prefix (json_string name);
  Printf.bprintf out "    %s_start [shape=point,label=\"\"];\n" prefix;
  Printf.bprintf out "    %s_start -> %s_%d;\n" prefix prefix b.machine.initial;
  List.iter (fun s ->
    Printf.bprintf out "    %s_%d [shape=%s,label=\"%d: %s\"];\n" prefix s.info_id
      (if s.info_final then "doublecircle" else "circle") s.info_id
      (dot_escape (continuation s.info_continuation))) b.infos;
  List.iter (fun (q,a,t) ->
    Printf.bprintf out "    %s_%d -> %s_%d [label=\"%c\"];\n" prefix q prefix t (char_of_code a))
    (transitions alpha b);
  Buffer.add_string out "  }\n"; Buffer.contents out

let bool_word_string w =
  String.init (List.length w) (fun i -> if List.nth w i then 'a' else 'b')

let bit_string bits =
  String.concat "" (List.map (fun b -> if b then "1" else "0") bits)

let json_bools bits =
  "[" ^ String.concat "," (List.map string_of_bool bits) ^ "]"

let rw_word_string w =
  String.concat "" (List.map (fun a -> String.make 1 (char_of_code a)) w)

let rw_finals id accepting states =
  List.filter_map (fun q -> if accepting q then Some (id q) else None) states

type progress_reporter = {
  progress_enabled : bool;
  progress_interval : float;
  progress_started : float;
  mutable progress_last : float;
}

let make_progress_reporter enabled interval =
  let now = Sys.time () in
  { progress_enabled = enabled; progress_interval = interval;
    progress_started = now; progress_last = now }

let progress_emit reporter message =
  if reporter.progress_enabled then begin
    let now = Sys.time () in
    reporter.progress_last <- now;
    Printf.eprintf "[ccont +%.1fs] %s\n%!"
      (now -. reporter.progress_started) message
  end

let progressf reporter fmt =
  Printf.ksprintf (progress_emit reporter) fmt

let progress_maybe reporter make_message =
  if reporter.progress_enabled then begin
    let now = Sys.time () in
    if now -. reporter.progress_last >= reporter.progress_interval then
      progress_emit reporter (make_message ())
  end

let render_rw_five_tuple out alphabet count finals =
  Printf.bprintf out "States: %d\nQ = {%s}\nSigma = {%s}\ndelta: Q x Sigma -> Q\nq0 = 0\nF = {%s}\nInitial: 0\nState details:\n"
    count
    (String.concat "," (List.init count string_of_int))
    (String.concat "," (List.map (fun a -> String.make 1 (char_of_code a)) alphabet))
    (String.concat "," (List.map string_of_int finals))

let rec concat_factors = function
  | WConcat (r,s) -> concat_factors r @ concat_factors s
  | r -> [r]

let rec union_atoms = function
  | WAtom a -> Some [a]
  | WPlus (r,s) ->
      (match union_atoms r, union_atoms s with
       | Some xs, Some ys -> Some (xs @ ys)
       | _ -> None)
  | _ -> None

let is_full_alphabet alpha r =
  match union_atoms r with
  | None -> false
  | Some atoms ->
      List.sort_uniq compare atoms = List.sort_uniq compare alpha &&
      List.length atoms = List.length alpha

let periodic_block_size alpha r =
  let factors = concat_factors r in
  if factors <> [] && List.for_all (is_full_alphabet alpha) factors
  then Some (List.length factors) else None

let rec gcd a b = if b = 0 then a else gcd b (a mod b)

let lcm a b =
  let g = gcd a b in
  if g = 0 then 0
  else if a / g > max_int / b then failwith "periodic modulus overflow"
  else (a / g) * b

type periodic_family = {
  pf_modulus : int;
  pf_periods : int list;
  pf_trigger : int;
}

let detect_periodic_family alpha r =
  match concat_factors r with
  | WStar sigma :: WAtom trigger :: assertions
      when assertions <> [] && List.mem trigger alpha &&
           is_full_alphabet alpha sigma ->
      let periods = List.map (function
        | WLookahead (WStar block) -> periodic_block_size alpha block
        | _ -> None) assertions in
      if List.for_all Option.is_some periods then
        let periods = List.map Option.get periods in
        let modulus = List.fold_left lcm 1 periods in
        Some { pf_modulus = modulus; pf_periods = periods;
               pf_trigger = trigger }
      else None
  | _ -> None

type tight_family = {
  tf_k : int;
  tf_a : int;
  tf_b : int;
  tf_c : int;
  tf_d : int;
  tf_e : int;
  tf_x : int;
  tf_hash : int;
}

let same_atom_set expected r =
  match union_atoms r with
  | Some atoms ->
      List.length atoms = List.length expected &&
      List.sort_uniq compare atoms = List.sort_uniq compare expected
  | None -> false

let tight_period_size core = function
  | WStar block ->
      let factors = concat_factors block in
      if factors <> [] && List.for_all (same_atom_set core) factors
      then Some (List.length factors) else None
  | _ -> None

let detect_tight_family alpha r =
  match concat_factors r with
  | [WStar outer_left; WAtom a; WStar (WAtom e); WStar factor;
     WAtom d; WStar outer_right; WAtom hash] ->
      let assertion = match factor with
        | WPlus (WAtom b, WConcat (WAtom c,
            WLookahead (WConcat (period, WAtom x)))) ->
              Some (b, c, period, x)
        | WPlus (WConcat (WAtom c,
            WLookahead (WConcat (period, WAtom x))), WAtom b) ->
              Some (b, c, period, x)
        | _ -> None
      in
      (match assertion with
       | None -> None
       | Some (b, c, period, x) ->
           let core = [a; b; c; d; e; x] in
           let roles = core @ [hash] in
           if List.length (List.sort_uniq compare roles) <> 7 ||
              List.sort_uniq compare alpha <> List.sort_uniq compare roles ||
              not (same_atom_set core outer_left) ||
              not (same_atom_set core outer_right)
           then None
           else
             match tight_period_size core period with
             | Some k when k >= 2 ->
                 Some { tf_k = k; tf_a = a; tf_b = b; tf_c = c;
                        tf_d = d; tf_e = e; tf_x = x; tf_hash = hash }
             | _ -> None)
  | _ -> None

let tight_symbol family a =
  if a = family.tf_a then TLa
  else if a = family.tf_b then TLb
  else if a = family.tf_c then TLc
  else if a = family.tf_d then TLd
  else if a = family.tf_e then TLe
  else if a = family.tf_x then TLx
  else if a = family.tf_hash then TLhash
  else failwith "internal error: symbol outside tight-family alphabet"

type tight_rw_state = {
  tr_id : int;
  tr_witness : int list;
  tr_state : TightAutomaton.state;
}

module TightStateTable = Hashtbl.Make(struct
  type t = TightAutomaton.state
  let equal = tight_state_eqb_char
  let hash = Hashtbl.hash
end)

let build_tight_states progress alpha family =
  let step state a =
    tight_step_char family.tf_k state (tight_symbol family a) in
  let by_state = TightStateTable.create 4096 in
  let by_id = Hashtbl.create 4096 in
  let pending = Queue.create () in
  let initial = { tr_id = 0; tr_witness = []; tr_state = tight_initial_char } in
  TightStateTable.add by_state initial.tr_state initial;
  Hashtbl.add by_id 0 initial;
  Queue.add initial pending;
  let discovered = ref 1 and processed = ref 0 in
  progressf progress
    "tight-family exploration started (k=%d, alphabet=%d)"
    family.tf_k (List.length alpha);
  while not (Queue.is_empty pending) do
    let q = Queue.take pending in
    List.iter (fun a ->
      let state = step q.tr_state a in
      if not (TightStateTable.mem by_state state) then begin
        let next = { tr_id = !discovered;
                     tr_witness = q.tr_witness @ [a]; tr_state = state } in
        incr discovered;
        TightStateTable.add by_state state next;
        Hashtbl.add by_id next.tr_id next;
        Queue.add next pending
      end) alpha;
    incr processed;
    progress_maybe progress (fun () -> Printf.sprintf
      "tight exploration: processed=%d discovered=%d pending=%d"
      !processed !discovered (Queue.length pending))
  done;
  let states = List.init !discovered (fun id -> Hashtbl.find by_id id) in
  progressf progress "tight exploration complete: states=%d transitions=%d"
    !discovered (!discovered * List.length alpha);
  progressf progress "checking tight transition closure";
  let symbols = List.map (tight_symbol family) alpha in
  let values = List.map (fun q -> q.tr_state) states in
  if not (tight_states_closedb_char family.tf_k symbols values) then
    failwith "internal error: tight-family derivative table is not closed";
  progressf progress "replaying tight state witnesses";
  List.iteri (fun i q ->
    let replay = List.fold_left step tight_initial_char q.tr_witness in
    if not (tight_state_eqb_char replay q.tr_state) then
      failwith "internal error: tight-family witness does not replay";
    progress_maybe progress (fun () -> Printf.sprintf
      "replaying tight witnesses: %d/%d" (i + 1) (List.length states)))
    states;
  progressf progress "tight table verified";
  step, states

let tight_target states state =
  match List.find_opt (fun q -> tight_state_eqb_char q.tr_state state) states with
  | Some q -> q.tr_id
  | None -> failwith "internal error: tight-family target was not explored"

let tight_bit_string bits =
  String.concat "" (List.map (fun b -> if b then "1" else "0") bits)

let tight_partial_string = function
  | TightAutomaton.PartialNone -> "none"
  | TightAutomaton.PartialPadding -> "padding"
  | TightAutomaton.PartialBits bits -> "bits:" ^ tight_bit_string bits

let tight_state_string = function
  | TightAutomaton.Running (partial, family) ->
      Printf.sprintf "running(partial=%s,family={%s})"
        (tight_partial_string partial)
        (String.concat ";" (List.map tight_bit_string family))
  | TightAutomaton.Accepting -> "accepting"
  | TightAutomaton.Dead -> "dead"

type periodic_rw_state = {
  pr_id : int;
  pr_witness : int list;
  pr_bits : bool list;
}

let build_periodic_states progress alpha family =
  if not (periodic_parameters_validb_char family.pf_modulus family.pf_periods) then
    failwith "periodic parameters failed the verified common-modulus check";
  if family.pf_modulus > 4096 then
    failwith "periodic modulus exceeds the 4096-bit implementation limit";
  let base = periodic_base_char family.pf_modulus family.pf_periods in
  let zero = periodic_zeros_char family.pf_modulus in
  let step bits a = periodic_step_char family.pf_trigger base bits a in
  let states = ref [{ pr_id = 0; pr_witness = []; pr_bits = zero }] in
  let pending = Queue.create () in
  Queue.add 0 pending;
  let processed = ref 0 in
  let find bits = List.find_opt (fun q -> q.pr_bits = bits) !states in
  progressf progress
    "periodic exploration started (modulus=%d, alphabet=%d)"
    family.pf_modulus (List.length alpha);
  while not (Queue.is_empty pending) do
    let id = Queue.take pending in
    let q = List.nth !states id in
    List.iter (fun a ->
      let bits = step q.pr_bits a in
      match find bits with
      | Some _ -> ()
      | None ->
          if List.length !states >= 10000 then
            failwith "periodic derivative exploration exceeded 10000 states";
          let next = { pr_id = List.length !states;
                       pr_witness = q.pr_witness @ [a]; pr_bits = bits } in
          states := !states @ [next];
          Queue.add next.pr_id pending) alpha
    ;
    incr processed;
    progress_maybe progress (fun () -> Printf.sprintf
      "periodic exploration: processed=%d discovered=%d pending=%d"
      !processed (List.length !states) (Queue.length pending))
  done;
  progressf progress "periodic exploration complete: states=%d transitions=%d"
    (List.length !states) (List.length !states * List.length alpha);
  progressf progress "checking periodic transition closure";
  let values = List.map (fun q -> q.pr_bits) !states in
  let closed = ref true in
  List.iteri (fun i q ->
    List.iter (fun a ->
      if not (List.exists (fun t -> t = step q.pr_bits a) values) then
        closed := false) alpha;
    progress_maybe progress (fun () -> Printf.sprintf
      "checking periodic closure: %d/%d states"
      (i + 1) (List.length !states))) !states;
  if not !closed then
    failwith "internal error: periodic derivative table is not closed";
  progressf progress "replaying periodic state witnesses";
  List.iteri (fun i q ->
    let replay = List.fold_left step zero q.pr_witness in
    if replay <> q.pr_bits then
      failwith "internal error: periodic derivative witness does not replay";
    progress_maybe progress (fun () -> Printf.sprintf
      "replaying periodic witnesses: %d/%d states"
      (i + 1) (List.length !states)))
    !states;
  progressf progress "periodic table verified";
  base, step, !states

let periodic_state_expression alpha initial family q =
  let rec sigma = function
    | [] -> Zero
    | [a] -> Atom a
    | a :: rest -> Plus (Atom a, sigma rest)
  in
  source_rewpla (periodic_history_representative_char (sigma alpha)
    family.pf_trigger initial family.pf_periods q.pr_witness)

type generic_rw_state = {
  rw_id : int;
  rw_witness : int list;
  rw_expr : int rewpla;
}

let normalize_rw r = rewpla_positive_normalize_char
  (rewpla_paper_normalize_char r)
let generic_step a r = rewpla_positive_symbol_step_char a r

let build_generic_rewpla_states progress alpha initial =
  let states = ref [{ rw_id = 0; rw_witness = []; rw_expr = normalize_rw initial }] in
  let pending = Queue.create () in
  Queue.add 0 pending;
  let processed = ref 0 in
  let find r =
    List.find_opt (fun q -> rewpla_eqb_char q.rw_expr r) !states
  in
  progressf progress
    "generic REwPLA exploration started (alphabet=%d)" (List.length alpha);
  while not (Queue.is_empty pending) do
    let id = Queue.take pending in
    let q = List.nth !states id in
    List.iter (fun a ->
      let r = generic_step a q.rw_expr in
      match find r with
      | Some _ -> ()
      | None ->
          if List.length !states >= 10000 then
            failwith "REwPLA syntactic exploration exceeded 10000 states";
          let next = { rw_id = List.length !states;
                       rw_witness = q.rw_witness @ [a]; rw_expr = r } in
          states := !states @ [next];
          Queue.add next.rw_id pending) alpha
    ;
    incr processed;
    progress_maybe progress (fun () -> Printf.sprintf
      "generic exploration: processed=%d discovered=%d pending=%d"
      !processed (List.length !states) (Queue.length pending))
  done;
  progressf progress "generic exploration complete: states=%d transitions=%d"
    (List.length !states) (List.length !states * List.length alpha);
  let values = List.map (fun q -> q.rw_expr) !states in
  progressf progress "checking generic transition closure";
  let closed = ref true in
  List.iteri (fun i q ->
    List.iter (fun a ->
      let target = generic_step a q.rw_expr in
      if not (List.exists (fun t -> rewpla_eqb_char target t) values) then
        closed := false) alpha;
    progress_maybe progress (fun () -> Printf.sprintf
      "checking generic closure: %d/%d states"
      (i + 1) (List.length !states))) !states;
  if not !closed then
    failwith "internal error: generic derivative table is not closed";
  progressf progress "replaying generic state witnesses";
  List.iteri (fun i q ->
    if not (rewpla_eqb_char
      (rewpla_positive_word_step_char q.rw_witness
        (normalize_rw initial)) q.rw_expr) then
      failwith "internal error: derivative witness does not replay";
    progress_maybe progress (fun () -> Printf.sprintf
      "replaying generic witnesses: %d/%d states"
      (i + 1) (List.length !states))) !states;
  progressf progress "generic table verified";
  !states

let generic_target states r =
  match List.find_opt (fun q -> rewpla_eqb_char q.rw_expr r) states with
  | Some q -> q.rw_id
  | None -> failwith "internal error: derivative target was not explored"

let render_tight_rewpla_json progress input alpha family =
  let step, states = build_tight_states progress alpha family in
  let finals = rw_finals (fun q -> q.tr_id)
    (fun q -> tight_finalb_char q.tr_state) states in
  progressf progress "rendering tight JSON state records";
  let state_json = List.mapi (fun i q ->
    progress_maybe progress (fun () -> Printf.sprintf
      "rendering tight JSON states: %d/%d" (i + 1) (List.length states));
    let representative = tight_state_string q.tr_state in
    Printf.sprintf
      "{\"id\":%d,\"witness\":%s,\"accepting\":%b,\"representative\":%s,\"derivative_regex\":%s,\"normal_form_term_ids\":[]}"
      q.tr_id (json_string (rw_word_string q.tr_witness))
      (tight_finalb_char q.tr_state) (json_string representative)
      (json_string representative)) states in
  progressf progress "rendering tight JSON transitions";
  let edges = List.concat_map (fun q ->
    List.map (fun a -> Printf.sprintf
      "{\"from\":%d,\"symbol\":%s,\"to\":%d}"
      q.tr_id (json_string (String.make 1 (char_of_code a)))
      (tight_target states (step q.tr_state a))) alpha) states in
  Printf.sprintf
    "{\"input\":%s,\"automaton\":\"rewpla\",\"method\":\"verified-tight-phase-obligations\",\"k\":%d,\"state_count\":%d,\"alphabet\":%s,\"initial\":0,\"final_states\":%s,\"states\":[%s],\"transitions\":[%s]}\n"
    (json_string input) family.tf_k (List.length states)
    ("[" ^ String.concat "," (List.map (fun a ->
      json_string (String.make 1 (char_of_code a))) alpha) ^ "]")
    (json_ints finals) (String.concat "," state_json) (String.concat "," edges)

let render_tight_rewpla_text progress input alpha family =
  progressf progress "selected verified tight-family construction";
  let step, states = build_tight_states progress alpha family in
  let out = Buffer.create 8192 in
  Printf.bprintf out
    "REwPLA semantic DFA (verified tight phase/obligation construction, k=%d)\nInput: %s\n"
    family.tf_k input;
  render_rw_five_tuple out alpha (List.length states)
    (rw_finals (fun q -> q.tr_id)
       (fun q -> tight_finalb_char q.tr_state) states);
  progressf progress "rendering tight text state records";
  List.iter (fun q ->
    Printf.bprintf out "  %d: witness=%s state=%s final=%b\n"
      q.tr_id (rw_word_string q.tr_witness) (tight_state_string q.tr_state)
      (tight_finalb_char q.tr_state)) states;
  Buffer.add_string out "Transitions:\n";
  progressf progress "rendering tight text transitions";
  List.iter (fun q -> List.iter (fun a ->
    Printf.bprintf out "  %d -%c-> %d\n" q.tr_id (char_of_code a)
      (tight_target states (step q.tr_state a))) alpha) states;
  Buffer.contents out

let render_generic_rewpla_json progress input alpha r =
  let states = build_generic_rewpla_states progress alpha r in
  let finals = rw_finals (fun q -> q.rw_id)
    (fun q -> rewpla_nullable_char q.rw_expr) states in
  progressf progress "rendering JSON state records";
  let state_json = List.mapi (fun i q ->
    progress_maybe progress (fun () -> Printf.sprintf
      "rendering JSON states: %d/%d" (i + 1) (List.length states));
    Printf.sprintf
      "{\"id\":%d,\"witness\":%s,\"accepting\":%b,\"representative\":%s,\"derivative_regex\":%s,\"normal_form_term_ids\":[]}"
      q.rw_id
      (json_string (rw_word_string q.rw_witness))
      (rewpla_nullable_char q.rw_expr) (json_string (source_rewpla q.rw_expr))
      (json_string (source_rewpla q.rw_expr))) states in
  progressf progress "rendering JSON transitions";
  let transitions = List.concat_map (fun q ->
    progress_maybe progress (fun () -> Printf.sprintf
      "rendering JSON transitions: state %d/%d"
      (q.rw_id + 1) (List.length states));
    List.map (fun a ->
    let dm, dc = rewpla_derivation_symbol_components_char a q.rw_expr in
    let dm = rewpla_derivation_display_normalize_char dm
    and dc = rewpla_derivation_display_normalize_char dc in
    let merged = generic_step a q.rw_expr in
    Printf.sprintf
      "{\"from\":%d,\"symbol\":%s,\"to\":%d,\"main_derivative\":%s,\"context_derivative\":%s}"
      q.rw_id (json_string (String.make 1 (char_of_code a)))
      (generic_target states merged) (json_string (source_rewpla dm))
      (json_string (source_rewpla dc))) alpha) states in
  Printf.sprintf
    "{\"input\":%s,\"automaton\":\"rewpla\",\"method\":\"proved-positive-congruence-normal-form\",\"state_count\":%d,\"alphabet\":%s,\"initial\":0,\"final_states\":%s,\"states\":[%s],\"transitions\":[%s]}\n"
    (json_string input) (List.length states)
    ("[" ^ String.concat "," (List.map (fun a -> json_string (String.make 1 (char_of_code a))) alpha) ^ "]")
    (json_ints finals) (String.concat "," state_json)
    (String.concat "," transitions)

let true_indices bits =
  List.filter_map (fun (i,b) -> if b then Some i else None)
    (List.mapi (fun i b -> i,b) bits)

let rotate_bits = function [] -> [] | x :: xs -> xs @ [x]

let periodic_target states bits =
  match List.find_opt (fun q -> q.pr_bits = bits) states with
  | Some q -> q.pr_id
  | None -> failwith "internal error: periodic target was not explored"

let render_periodic_rewpla_json progress input alpha initial family =
  let base, step, states = build_periodic_states progress alpha family in
  let finals = rw_finals (fun q -> q.pr_id)
    (fun q -> List.hd q.pr_bits) states in
  progressf progress "rendering periodic JSON state records";
  let state_json = List.map (fun q ->
    progress_maybe progress (fun () -> Printf.sprintf
      "rendering periodic JSON states: %d/%d"
      (q.pr_id + 1) (List.length states));
    let residues = true_indices q.pr_bits in
    let expression = periodic_state_expression alpha initial family q in
    Printf.sprintf
      "{\"id\":%d,\"witness\":%s,\"accepting\":%b,\"representative\":%s,\"derivative_regex\":%s,\"normal_form_term_ids\":%s,\"residue_bits\":%s,\"residues\":%s}"
      q.pr_id (json_string (rw_word_string q.pr_witness))
      (List.hd q.pr_bits)
      (json_string expression) (json_string expression)
      (json_ints residues) (json_string (bit_string q.pr_bits))
      (json_ints residues)) states in
  progressf progress "rendering periodic JSON transitions";
  let edges = List.concat_map (fun q ->
    progress_maybe progress (fun () -> Printf.sprintf
      "rendering periodic JSON transitions: state %d/%d"
      (q.pr_id + 1) (List.length states));
    List.map (fun a ->
      let target_bits = step q.pr_bits a in
      let main_bits = if a = family.pf_trigger then base
        else periodic_zeros_char family.pf_modulus in
      Printf.sprintf
        "{\"from\":%d,\"symbol\":%s,\"to\":%d,\"main_derivative\":{\"keeps_main_suffix_language\":true,\"residue_bits\":%s},\"context_derivative\":{\"residue_bits\":%s}}"
        q.pr_id (json_string (String.make 1 (char_of_code a)))
        (periodic_target states target_bits)
        (json_string (bit_string main_bits))
        (json_string (bit_string (rotate_bits q.pr_bits)))) alpha) states in
  Printf.sprintf
    "{\"input\":%s,\"automaton\":\"rewpla\",\"method\":\"verified-periodic-family\",\"modulus\":%d,\"periods\":%s,\"state_count\":%d,\"alphabet\":%s,\"initial\":0,\"final_states\":%s,\"states\":[%s],\"transitions\":[%s]}\n"
    (json_string input) family.pf_modulus (json_ints family.pf_periods)
    (List.length states)
    ("[" ^ String.concat "," (List.map (fun a ->
      json_string (String.make 1 (char_of_code a))) alpha) ^ "]")
    (json_ints finals) (String.concat "," state_json) (String.concat "," edges)

let render_rewpla_text progress input alpha r =
  match detect_tight_family alpha r with
  | Some family -> render_tight_rewpla_text progress input alpha family
  | None -> match detect_periodic_family alpha r with
  | Some family ->
    progressf progress "selected verified periodic-family construction";
    let _, step, states = build_periodic_states progress alpha family in
    let out = Buffer.create 8192 in
    Printf.bprintf out "REwPLA semantic derivative DFA (verified mod %d)\nInput: %s\n"
      family.pf_modulus input;
    render_rw_five_tuple out alpha (List.length states)
      (rw_finals (fun q -> q.pr_id) (fun q -> List.hd q.pr_bits) states);
    progressf progress "rendering periodic text state records";
    List.iter (fun q ->
      progress_maybe progress (fun () -> Printf.sprintf
        "rendering periodic text states: %d/%d"
        (q.pr_id + 1) (List.length states));
      Printf.bprintf out "  %d: witness=%s continuation=%s final=%b bits=%s residues={%s}\n"
        q.pr_id (rw_word_string q.pr_witness)
        (periodic_state_expression alpha r family q)
        (List.hd q.pr_bits) (bit_string q.pr_bits)
        (String.concat "," (List.map string_of_int (true_indices q.pr_bits)))) states;
    Buffer.add_string out "Transitions:\n";
    progressf progress "rendering periodic text transitions";
    List.iter (fun q -> List.iter (fun a ->
      progress_maybe progress (fun () -> Printf.sprintf
        "rendering periodic text transitions: state %d/%d"
        (q.pr_id + 1) (List.length states));
      Printf.bprintf out "  %d -%c-> %d\n" q.pr_id (char_of_code a)
        (periodic_target states (step q.pr_bits a))) alpha) states;
    Buffer.contents out
  | None ->
    progressf progress "selected generic positive-congruence construction";
    let states = build_generic_rewpla_states progress alpha r in
    let out = Buffer.create 2048 in
    Printf.bprintf out "REwPLA derivative DFA (positive-congruence classes)\nInput: %s\n" input;
    render_rw_five_tuple out alpha (List.length states)
      (rw_finals (fun q -> q.rw_id)
         (fun q -> rewpla_nullable_char q.rw_expr) states);
    progressf progress "rendering generic text state records";
    List.iter (fun q ->
      progress_maybe progress (fun () -> Printf.sprintf
        "rendering generic text states: %d/%d"
        (q.rw_id + 1) (List.length states));
      Printf.bprintf out "  %d: witness=%s continuation=%s final=%b\n"
        q.rw_id (rw_word_string q.rw_witness)
        (source_rewpla q.rw_expr)
        (rewpla_nullable_char q.rw_expr)) states;
    Buffer.add_string out "Transitions:\n";
    progressf progress "rendering generic text transitions";
    List.iter (fun q -> List.iter (fun a ->
      progress_maybe progress (fun () -> Printf.sprintf
        "rendering generic text transitions: state %d/%d"
        (q.rw_id + 1) (List.length states));
      Printf.bprintf out "  %d -%c-> %d\n" q.rw_id (char_of_code a)
        (generic_target states (generic_step a q.rw_expr))) alpha) states;
    Buffer.contents out

type automaton_choice = Ce | Quotient | Both | Rewpla
type format_choice = Text | Dot | Json

let () =
  let automaton = ref Both and format = ref Text and output = ref None
      and expression = ref None and alphabet_option = ref None
      and show_progress = ref true and progress_interval = ref 5.0 in
  let set_automaton = function
    | "ce" -> automaton := Ce | "quotient" -> automaton := Quotient
    | "both" -> automaton := Both | "rewpla" -> automaton := Rewpla
    | s -> raise (Arg.Bad ("unknown automaton: " ^ s)) in
  let set_format = function
    | "text" -> format := Text | "dot" -> format := Dot | "json" -> format := Json
    | s -> raise (Arg.Bad ("unknown format: " ^ s)) in
  let specs = [
    "--automaton", Arg.Symbol (["ce";"quotient";"both";"rewpla"], set_automaton), " select automaton";
    "--alphabet", Arg.String (fun s -> alphabet_option := Some s),
      "SYMBOLS finite alphabet (required for --automaton rewpla)";
    "--format", Arg.Symbol (["text";"dot";"json"], set_format), " select output format";
    "--progress", Arg.Set show_progress, " show REwPLA construction progress on stderr (default)";
    "--no-progress", Arg.Clear show_progress, " disable REwPLA construction progress";
    "--progress-interval", Arg.Set_float progress_interval,
      "SECONDS minimum interval between progress updates (default: 5)";
    "-o", Arg.String (fun s -> output := Some s), "FILE write output to FILE"
  ] in
  let usage = "ccont [--automaton ce|quotient|both|rewpla] [--alphabet SYMBOLS] [--format text|dot|json] [--no-progress] [--progress-interval SECONDS] [-o FILE] REGEX" in
  try
    Arg.parse specs (fun s -> match !expression with None -> expression := Some s | Some _ -> raise (Arg.Bad "exactly one REGEX is required")) usage;
    if !progress_interval <= 0.0 then
      raise (Arg.Bad "--progress-interval must be greater than zero");
    let input = match !expression with Some s -> s | None -> raise (Arg.Bad "REGEX is required") in
    let progress = make_progress_reporter
      (!show_progress && !automaton = Rewpla) !progress_interval in
    let body = match !automaton with
      | Rewpla ->
          progressf progress "parsing REwPLA input";
          let alphabet_text = match !alphabet_option with
            | Some s when String.length s > 0 -> s
            | _ -> raise (Arg.Bad "--alphabet is required for --automaton rewpla") in
          let alpha = List.init (String.length alphabet_text)
            (fun i -> Char.code alphabet_text.[i]) in
          if List.length (List.sort_uniq compare alpha) <> List.length alpha then
            raise (Arg.Bad "--alphabet must not contain duplicate symbols");
          let r = parse_rewpla input in
          if not (List.for_all (fun a -> List.mem a alpha) (rewpla_alphabet r)) then
            raise (Arg.Bad "the supplied alphabet does not contain every expression symbol");
          progressf progress "input parsed; constructing DFA";
          (match !format with
           | Json ->
               (match detect_tight_family alpha r with
                | Some family ->
                    progressf progress "selected verified tight-family construction";
                    render_tight_rewpla_json progress input alpha family
                | None ->
                    match detect_periodic_family alpha r with
                    | Some family ->
                        progressf progress "selected verified periodic-family construction";
                        render_periodic_rewpla_json progress input alpha r family
                    | None ->
                        progressf progress "selected generic positive-congruence construction";
                        render_generic_rewpla_json progress input alpha r)
           | Text -> render_rewpla_text progress input alpha r
           | Dot -> raise (Arg.Bad "dot output is not yet available for --automaton rewpla"))
      | (Ce | Quotient | Both) as ordinary ->
          let r = parse input in
          let alpha = alphabet r in
          let ce = build_ce_char r and quotient = build_quotient_char r in
          match !format with
          | Text -> (match ordinary with
              | Ce -> render_text "c-continuation automaton CE" alpha ce
              | Quotient -> render_text "quotient automaton CE/~" alpha quotient
              | Both -> render_text "c-continuation automaton CE" alpha ce ^ "\n" ^ render_text "quotient automaton CE/~" alpha quotient
              | Rewpla -> assert false)
          | Json ->
              let cej = match ordinary with Quotient -> "null" | _ -> render_machine_json alpha ce in
              let qj = match ordinary with Ce -> "null" | _ -> render_machine_json alpha quotient in
              Printf.sprintf "{\"input\":%s,\"ce\":%s,\"quotient\":%s}\n" (json_string input) cej qj
          | Dot ->
              let graphs = match ordinary with
                | Ce -> render_dot_graph "c-continuation automaton CE" "ce" alpha ce
                | Quotient -> render_dot_graph "quotient automaton CE/~" "quotient" alpha quotient
                | Both -> render_dot_graph "c-continuation automaton CE" "ce" alpha ce ^ render_dot_graph "quotient automaton CE/~" "quotient" alpha quotient
                | Rewpla -> assert false
              in "digraph ccont {\n  rankdir=LR;\n" ^ graphs ^ "}\n"
    in
    progressf progress "writing output (%d bytes)" (String.length body);
    (match !output with None -> print_string body | Some path -> let ch = open_out path in output_string ch body; close_out ch);
    progressf progress "done"
  with
  | Parse_error (pos,msg) -> Printf.eprintf "parse error at character %d: %s\n" pos msg; exit 2
  | Arg.Bad msg -> Printf.eprintf "%s\nUsage: %s\n" msg usage; exit 2
  | Failure msg -> Printf.eprintf "error: %s\n" msg; exit 1
  | Sys_error msg -> Printf.eprintf "I/O error: %s\n" msg; exit 1
