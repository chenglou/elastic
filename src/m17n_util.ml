let gen_of_lexbuf oldlexbuf () =
  let open Lexing in
  if oldlexbuf.lex_eof_reached &&
     oldlexbuf.lex_curr_pos = oldlexbuf.lex_buffer_len then
    None
  else begin
    if oldlexbuf.lex_curr_pos = oldlexbuf.lex_buffer_len then
      oldlexbuf.refill_buff oldlexbuf;
    let curr_pos = oldlexbuf.lex_curr_pos in
    oldlexbuf.lex_curr_pos <- oldlexbuf.lex_buffer_len;
    Some (oldlexbuf.lex_buffer, curr_pos,
          oldlexbuf.lex_buffer_len - curr_pos)
  end

let rec skip_phrase lexbuf =
  try
    match Mylexer.token lexbuf with
    | Myparser.SEMISEMI | Myparser.EOF -> ()
    | _ -> skip_phrase lexbuf
  with
  | Mylexer.Error (Mylexer.Unterminated_comment _, _)
  | Mylexer.Error (Mylexer.Unterminated_string, _)
  | Mylexer.Error (Mylexer.Unterminated_string_in_comment _, _)
  | Mylexer.Error (Mylexer.Illegal_character _, _) ->
    skip_phrase lexbuf

let maybe_skip_phrase lexbuf =
  if Parsing.is_current_lookahead Myparser.SEMISEMI
  || Parsing.is_current_lookahead Myparser.EOF
  then ()
  else skip_phrase lexbuf

let extract_exn src name =
  try
    ignore (!Toploop.parse_toplevel_phrase (Lexing.from_string src));
    assert false
  with exn ->
    assert (Printexc.exn_slot_name exn = name);
    exn

let transmogrify_exn exn template =
  assert (Obj.tag (Obj.repr exn) = 0);
  Obj.set_field (Obj.repr exn) 0 (Obj.field (Obj.repr template) 0);
  exn

let exn_Lexer_Error = extract_exn "\128" "Mylexer.Error"
let exn_Syntaxerr_Error = extract_exn "fun" "Syntaxerr.Error"

let internationalize ?load_path fn oldlexbuf =
  let kind = if !Toploop.input_name = "//toplevel//" then `Toplevel else `Batch in
  let co = open_in !Toploop.input_name in
  let lexbuf = Lexing.from_channel co in
  try
    try
      let ast = fn Mylexer.token lexbuf in
      Parsing.clear_parser ();
      ast
    with
    | Mylexer.Error(Mylexer.Illegal_character _, _) as err when kind = `Toplevel ->
      raise err
    | Syntaxerr.Error _ as err when kind = `Toplevel ->
      raise err
    | Parsing.Parse_error | Syntaxerr.Escape_error ->
      let loc = Location.curr lexbuf in
      if kind = `Toplevel then maybe_skip_phrase lexbuf;
      raise (Syntaxerr.Error (Syntaxerr.Other loc))
  with exn when kind = `Toplevel ->
    (* In expunged toplevel, we have a split-brain situation where toplevel
       and m17n have different internal IDs for the "same" exceptions.
       Fixup. *)
    raise (match exn with
          | Mylexer.Error _ -> transmogrify_exn exn exn_Lexer_Error
          | Syntaxerr.Error _ -> transmogrify_exn exn exn_Syntaxerr_Error
          | _ -> exn)

let utf8_parenthesized_ident name =
  (List.mem name ["or"; "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"]) ||
  (match name.[0] with
   | 'a'..'z' | 'A'..'Z' | '_' | '\128'..'\255' -> false
   | _ -> true)

let utf8_print_string fmt s =
  try
    try
      let uutf = Uutf.decoder ~encoding:`UTF_8 (`String s) in
      let buf  = Buffer.create (String.length s) in
      let rec loop () =
        match Uutf.decode uutf with
        | `Malformed _ -> raise Exit
        | `End -> ()
        | `Uchar u ->
          begin match Uucp.Gc.general_category u with
          | (`Cc | `Cf | `Cn | `Co | `Cs) -> raise Exit
          | _ -> Uutf.Buffer.add_utf_8 buf u
          end;
          loop ()
        | `Await -> assert false
      in
      Buffer.add_char buf '"';
      loop ();
      Buffer.add_char buf '"';
      Format.pp_print_string fmt (Buffer.contents buf)
    with Exit ->
      Format.fprintf fmt "%S" s
  with Invalid_argument "String.create" ->
    Format.fprintf fmt "<huge string>"

let utf8_value_ident ppf name =
  if utf8_parenthesized_ident name then
    Format.fprintf ppf "( %s )" name
  else
    Format.pp_print_string ppf name

let utf8_print_out_sig_item next ppf =
  function
  | Outcometree.Osig_value (name, ty, prims) ->
    let kwd = if prims = [] then "val" else "external" in
    let pr_prims ppf =
      function
        [] -> ()
      | s :: sl ->
          Format.fprintf ppf "@ = \"%s\"" s;
          List.iter (fun s -> Format.fprintf ppf "@ \"%s\"" s) sl
    in
    Format.fprintf ppf "@[<2>%s %a :@ %a%a@]" kwd utf8_value_ident name !Toploop.print_out_type
      ty pr_prims prims
  | x -> next ppf x
