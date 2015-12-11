let wrap_parser ?load_path parser lexer lexbuf =
  let ast = parser lexer lexbuf in
  Parsing.clear_parser ();
  ast

type language = Ocaml | Elastic | Binary
let print_ast size filename towards ast =
  match towards with
  | Elastic ->
    output_string  stdout (match size with
      | None -> Mypprintast.string_of_structure ast
      | Some s -> Mypprintast.string_of_structure ~size:s ast)
  | Ocaml ->
    output_string  stdout (match size with
      | None -> Ocamlpprintast.string_of_structure ast
      | Some s -> Ocamlpprintast.string_of_structure ~size:s ast)
  | Binary ->
    output_string stdout Config.ast_impl_magic_number;
    output_value  stdout filename;
    output_value  stdout ast

let () =
  let filename, load_path, towards, from, size, from_stdin =
    let filename = ref "" in
    let load_path = ref [] in
    let towards = ref Binary in
    let from = ref Ocaml in
    let size = ref None in
    let from_stdin = ref false in
    Arg.parse [
        "-to", Arg.String (fun x -> (match x with
          | "elastic" -> towards := Elastic
          | "ocaml" -> towards := Ocaml
          | "binary" -> towards := Binary
          | _ -> assert false
        )), "Destination language (choice between elastic, ocaml or binary)";
        "-from", Arg.String (fun x -> (match x with
          | "elastic" -> from := Elastic
          | "ocaml" -> from := Ocaml
          | _ -> assert false
        )), "Origin language (choice between elastic orocaml)";
        "-max_width", Arg.Int (fun x -> size := Some x), "Max width in number of characters used by the formatter.";
        "-from_stdin", Arg.Unit (fun _ -> from_stdin := true), "Read from stdin instead of from a file";
        "-I", Arg.String (fun x -> load_path := x :: !load_path), "<path> add <path> to load path";
        "-ignore", Arg.Unit ignore, "ignored";
      ]
      (fun arg -> filename := arg)
      "OCaml Multilingualization preprocessor";
    !filename, load_path, !towards, !from, !size, !from_stdin
  in
  let co = if from_stdin then stdin else open_in filename in
  let lexbuf = Lexing.from_channel co in
  try
    (* if Filename.check_suffix filename ".ml" then *)
      print_ast size filename towards (match from with
      | Elastic -> wrap_parser ~load_path Myparser.implementation Mylexer.token lexbuf
      | Ocaml -> wrap_parser ~load_path Parser.implementation Lexer.token lexbuf
      | _ -> assert false)
    (* else
      (prerr_string ("Don't know what to do with " ^ filename ^ ".");
       exit 1) *)
  with
  | Parsing.Parse_error | Syntaxerr.Escape_error ->
    let exn = Syntaxerr.Error (Syntaxerr.Other (Location.curr lexbuf)) in
    Location.report_exception Format.err_formatter exn;
  | exn ->
    Location.report_exception Format.err_formatter exn;
    exit 1
