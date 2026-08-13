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

let alphabet r =
  let rec collect acc = function
    | Zero | Eps -> acc
    | Atom a -> if List.mem a acc then acc else a :: acc
    | Plus (x,y) | Concat (x,y) -> collect (collect acc x) y
    | Star x -> collect acc x
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

type automaton_choice = Ce | Quotient | Both
type format_choice = Text | Dot | Json

let () =
  let automaton = ref Both and format = ref Text and output = ref None and expression = ref None in
  let set_automaton = function
    | "ce" -> automaton := Ce | "quotient" -> automaton := Quotient | "both" -> automaton := Both
    | s -> raise (Arg.Bad ("unknown automaton: " ^ s)) in
  let set_format = function
    | "text" -> format := Text | "dot" -> format := Dot | "json" -> format := Json
    | s -> raise (Arg.Bad ("unknown format: " ^ s)) in
  let specs = [
    "--automaton", Arg.Symbol (["ce";"quotient";"both"], set_automaton), " select automaton";
    "--format", Arg.Symbol (["text";"dot";"json"], set_format), " select output format";
    "-o", Arg.String (fun s -> output := Some s), "FILE write output to FILE"
  ] in
  let usage = "ccont [--automaton ce|quotient|both] [--format text|dot|json] [-o FILE] REGEX" in
  try
    Arg.parse specs (fun s -> match !expression with None -> expression := Some s | Some _ -> raise (Arg.Bad "exactly one REGEX is required")) usage;
    let input = match !expression with Some s -> s | None -> raise (Arg.Bad "REGEX is required") in
    let r = parse input in
    let alpha = alphabet r in
    let ce = build_ce_char r and quotient = build_quotient_char r in
    let body = match !format with
      | Text -> (match !automaton with
          | Ce -> render_text "c-continuation automaton CE" alpha ce
          | Quotient -> render_text "quotient automaton CE/~" alpha quotient
          | Both -> render_text "c-continuation automaton CE" alpha ce ^ "\n" ^ render_text "quotient automaton CE/~" alpha quotient)
      | Json ->
          let cej = match !automaton with Quotient -> "null" | _ -> render_machine_json alpha ce in
          let qj = match !automaton with Ce -> "null" | _ -> render_machine_json alpha quotient in
          Printf.sprintf "{\"input\":%s,\"ce\":%s,\"quotient\":%s}\n" (json_string input) cej qj
      | Dot ->
          let graphs = match !automaton with
            | Ce -> render_dot_graph "c-continuation automaton CE" "ce" alpha ce
            | Quotient -> render_dot_graph "quotient automaton CE/~" "quotient" alpha quotient
            | Both -> render_dot_graph "c-continuation automaton CE" "ce" alpha ce ^ render_dot_graph "quotient automaton CE/~" "quotient" alpha quotient
          in "digraph ccont {\n  rankdir=LR;\n" ^ graphs ^ "}\n"
    in
    (match !output with None -> print_string body | Some path -> let ch = open_out path in output_string ch body; close_out ch)
  with
  | Parse_error (pos,msg) -> Printf.eprintf "parse error at character %d: %s\n" pos msg; exit 2
  | Arg.Bad msg -> Printf.eprintf "%s\nUsage: %s\n" msg usage; exit 2
  | Sys_error msg -> Printf.eprintf "I/O error: %s\n" msg; exit 1

