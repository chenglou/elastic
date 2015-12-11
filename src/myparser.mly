/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the Q Public License version 1.0.               */
/*                                                                     */
/***********************************************************************/

/* The parser definition */

%{
open Location
open Asttypes
open Longident
open Parsetree
open Ast_helper

let mktyp d = Typ.mk ~loc:(symbol_rloc()) d
let mkpat d = Pat.mk ~loc:(symbol_rloc()) d
let mkexp d = Exp.mk ~loc:(symbol_rloc()) d
let mkmty d = Mty.mk ~loc:(symbol_rloc()) d
let mksig d = Sig.mk ~loc:(symbol_rloc()) d
let mkmod d = Mod.mk ~loc:(symbol_rloc()) d
let mkstr d = Str.mk ~loc:(symbol_rloc()) d
let mkclass d = Cl.mk ~loc:(symbol_rloc()) d
let mkcty d = Cty.mk ~loc:(symbol_rloc()) d
let mkctf d = Ctf.mk ~loc:(symbol_rloc()) d
let mkcf d = Cf.mk ~loc:(symbol_rloc()) d

let mkrhs rhs pos = mkloc rhs (rhs_loc pos)
let mkoption d =
  let loc = {d.ptyp_loc with loc_ghost = true} in
  Typ.mk ~loc (Ptyp_constr(mkloc (Ldot (Lident "*predef*", "option")) loc,[d]))

let reloc_pat x = { x with ppat_loc = symbol_rloc () };;
let reloc_exp x = { x with pexp_loc = symbol_rloc () };;

let mkoperator name pos =
  let loc = rhs_loc pos in
  Exp.mk ~loc (Pexp_ident(mkloc (Lident name) loc))

let mkpatvar name pos =
  Pat.mk ~loc:(rhs_loc pos) (Ppat_var (mkrhs name pos))

(*
  Ghost expressions and patterns:
  expressions and patterns that do not appear explicitly in the
  source file they have the loc_ghost flag set to true.
  Then the profiler will not try to instrument them and the
  -annot option will not try to display their type.

  Every grammar rule that generates an element with a location must
  make at most one non-ghost element, the topmost one.

  How to tell whether your location must be ghost:
  A location corresponds to a range of characters in the source file.
  If the location contains a piece of code that is syntactically
  valid (according to the documentation), and corresponds to the
  AST node, then the location must be real; in all other cases,
  it must be ghost.
*)
let ghexp d = Exp.mk ~loc:(symbol_gloc ()) d
let ghpat d = Pat.mk ~loc:(symbol_gloc ()) d
let ghtyp d = Typ.mk ~loc:(symbol_gloc ()) d
let ghloc d = { txt = d; loc = symbol_gloc () }
let ghstr d = Str.mk ~loc:(symbol_gloc()) d

let ghunit () =
  ghexp (Pexp_construct (mknoloc (Lident "()"), None))

let mkinfix arg1 name arg2 =
  mkexp(Pexp_apply(mkoperator name 2, ["", arg1; "", arg2]))

let mkpartial name arg =
  mkexp (Pexp_apply (mkoperator name 1, [("", arg)]))

let rec mkinfix_list l name =
  match l with
  | [] -> assert false
  | hd :: [] -> hd
  | hd :: tl -> mkinfix hd name (mkinfix_list tl name)

let neg_float_string f =
  if String.length f > 0 && f.[0] = '-'
  then String.sub f 1 (String.length f - 1)
  else "-" ^ f

let mkuminus name arg =
  match name, arg.pexp_desc with
  | "-", Pexp_constant(Const_int n) ->
      mkexp(Pexp_constant(Const_int(-n)))
  | "-", Pexp_constant(Const_int32 n) ->
      mkexp(Pexp_constant(Const_int32(Int32.neg n)))
  | "-", Pexp_constant(Const_int64 n) ->
      mkexp(Pexp_constant(Const_int64(Int64.neg n)))
  | "-", Pexp_constant(Const_nativeint n) ->
      mkexp(Pexp_constant(Const_nativeint(Nativeint.neg n)))
  | ("-" | "-."), Pexp_constant(Const_float f) ->
      mkexp(Pexp_constant(Const_float(neg_float_string f)))
  | _ ->
      mkexp(Pexp_apply(mkoperator ("~" ^ name) 1, ["", arg]))

let mkuplus name arg =
  let desc = arg.pexp_desc in
  match name, desc with
  | "+", Pexp_constant(Const_int _)
  | "+", Pexp_constant(Const_int32 _)
  | "+", Pexp_constant(Const_int64 _)
  | "+", Pexp_constant(Const_nativeint _)
  | ("+" | "+."), Pexp_constant(Const_float _) -> mkexp desc
  | _ ->
      mkexp(Pexp_apply(mkoperator ("~" ^ name) 1, ["", arg]))

let mkexp_cons consloc args loc =
  Exp.mk ~loc (Pexp_construct(mkloc (Lident "::") consloc, Some args))

let mkpat_cons consloc args loc =
  Pat.mk ~loc (Ppat_construct(mkloc (Lident "::") consloc, Some args))

let rec mktailexp nilloc = function
    [] ->
      let loc = { nilloc with loc_ghost = true } in
      let nil = { txt = Lident "[]"; loc = loc } in
      Exp.mk ~loc (Pexp_construct (nil, None))
  | e1 :: el ->
      let exp_el = mktailexp nilloc el in
      let loc = {loc_start = e1.pexp_loc.loc_start;
               loc_end = exp_el.pexp_loc.loc_end;
               loc_ghost = true}
      in
      let arg = Exp.mk ~loc (Pexp_tuple [e1; exp_el]) in
      mkexp_cons {loc with loc_ghost = true} arg loc

let rec mktailpat nilloc = function
    [] ->
      let loc = { nilloc with loc_ghost = true } in
      let nil = { txt = Lident "[]"; loc = loc } in
      Pat.mk ~loc (Ppat_construct (nil, None))
  | p1 :: pl ->
      let pat_pl = mktailpat nilloc pl in
      let loc = {loc_start = p1.ppat_loc.loc_start;
               loc_end = pat_pl.ppat_loc.loc_end;
               loc_ghost = true}
      in
      let arg = Pat.mk ~loc (Ppat_tuple [p1; pat_pl]) in
      mkpat_cons {loc with loc_ghost = true} arg loc

let mkstrexp e attrs =
  { pstr_desc = Pstr_eval (e, attrs); pstr_loc = e.pexp_loc }

let mkexp_constraint e (t1, t2) =
  match t1, t2 with
  | Some t, None -> ghexp(Pexp_constraint(e, t))
  | _, Some t -> ghexp(Pexp_coerce(e, t1, t))
  | None, None -> assert false

let array_function str name =
  ghloc (Ldot(Lident str, (if !Clflags.fast then "unsafe_" ^ name else name)))

let syntax_error () =
  raise Syntaxerr.Escape_error

let unclosed opening_name opening_num closing_name closing_num =
  raise(Syntaxerr.Error(Syntaxerr.Unclosed(rhs_loc opening_num, opening_name,
                                           rhs_loc closing_num, closing_name)))

let expecting pos nonterm =
    raise Syntaxerr.(Error(Expecting(rhs_loc pos, nonterm)))

let not_expecting pos nonterm =
    raise Syntaxerr.(Error(Not_expecting(rhs_loc pos, nonterm)))

let bigarray_function str name =
  ghloc (Ldot(Ldot(Lident "Bigarray", str), name))

let bigarray_untuplify = function
    { pexp_desc = Pexp_tuple explist; pexp_loc = _ } -> explist
  | exp -> [exp]

let bigarray_get arr arg =
  let get = if !Clflags.fast then "unsafe_get" else "get" in
  match bigarray_untuplify arg with
    [c1] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array1" get)),
                       ["", arr; "", c1]))
  | [c1;c2] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array2" get)),
                       ["", arr; "", c1; "", c2]))
  | [c1;c2;c3] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array3" get)),
                       ["", arr; "", c1; "", c2; "", c3]))
  | coords ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Genarray" "get")),
                       ["", arr; "", ghexp(Pexp_array coords)]))

let bigarray_set arr arg newval =
  let set = if !Clflags.fast then "unsafe_set" else "set" in
  match bigarray_untuplify arg with
    [c1] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array1" set)),
                       ["", arr; "", c1; "", newval]))
  | [c1;c2] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array2" set)),
                       ["", arr; "", c1; "", c2; "", newval]))
  | [c1;c2;c3] ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Array3" set)),
                       ["", arr; "", c1; "", c2; "", c3; "", newval]))
  | coords ->
      mkexp(Pexp_apply(ghexp(Pexp_ident(bigarray_function "Genarray" "set")),
                       ["", arr;
                        "", ghexp(Pexp_array coords);
                        "", newval]))

let lapply p1 p2 =
  if !Clflags.applicative_functors
  then Lapply(p1, p2)
  else raise (Syntaxerr.Error(Syntaxerr.Applicative_path (symbol_rloc())))

let exp_of_label lbl pos =
  mkexp (Pexp_ident(mkrhs (Lident(Longident.last lbl)) pos))

let pat_of_label lbl pos =
  mkpat (Ppat_var (mkrhs (Longident.last lbl) pos))

let check_variable vl loc v =
  if List.mem v vl then
    raise Syntaxerr.(Error(Variable_in_scope(loc,v)))

let varify_constructors var_names t =
  let rec loop t =
    let desc =
      match t.ptyp_desc with
      | Ptyp_any -> Ptyp_any
      | Ptyp_var x ->
          check_variable var_names t.ptyp_loc x;
          Ptyp_var x
      | Ptyp_arrow (label,core_type,core_type') ->
          Ptyp_arrow(label, loop core_type, loop core_type')
      | Ptyp_tuple lst -> Ptyp_tuple (List.map loop lst)
      | Ptyp_constr( { txt = Lident s }, []) when List.mem s var_names ->
          Ptyp_var s
      | Ptyp_constr(longident, lst) ->
          Ptyp_constr(longident, List.map loop lst)
      | Ptyp_object (lst, o) ->
          Ptyp_object
            (List.map (fun (s, attrs, t) -> (s, attrs, loop t)) lst, o)
      | Ptyp_class (longident, lst) ->
          Ptyp_class (longident, List.map loop lst)
      | Ptyp_alias(core_type, string) ->
          check_variable var_names t.ptyp_loc string;
          Ptyp_alias(loop core_type, string)
      | Ptyp_variant(row_field_list, flag, lbl_lst_option) ->
          Ptyp_variant(List.map loop_row_field row_field_list,
                       flag, lbl_lst_option)
      | Ptyp_poly(string_lst, core_type) ->
          List.iter (check_variable var_names t.ptyp_loc) string_lst;
          Ptyp_poly(string_lst, loop core_type)
      | Ptyp_package(longident,lst) ->
          Ptyp_package(longident,List.map (fun (n,typ) -> (n,loop typ) ) lst)
      | Ptyp_extension (s, arg) ->
          Ptyp_extension (s, arg)
    in
    {t with ptyp_desc = desc}
  and loop_row_field  =
    function
      | Rtag(label,attrs,flag,lst) ->
          Rtag(label,attrs,flag,List.map loop lst)
      | Rinherit t ->
          Rinherit (loop t)
  in
  loop t

let wrap_type_annotation newtypes core_type body =
  let exp = mkexp(Pexp_constraint(body,core_type)) in
  let exp =
    List.fold_right (fun newtype exp -> mkexp (Pexp_newtype (newtype, exp)))
      newtypes exp
  in
  (exp, ghtyp(Ptyp_poly(newtypes,varify_constructors newtypes core_type)))

let wrap_exp_attrs body (ext, attrs) =
  (* todo: keep exact location for the entire attribute *)
  let body = {body with pexp_attributes = attrs @ body.pexp_attributes} in
  match ext with
  | None -> body
  | Some id -> ghexp(Pexp_extension (id, PStr [mkstrexp body []]))

let mkexp_attrs d attrs =
  wrap_exp_attrs (mkexp d) attrs

let mkcf_attrs d attrs =
  Cf.mk ~loc:(symbol_rloc()) ~attrs d

let mkctf_attrs d attrs =
  Ctf.mk ~loc:(symbol_rloc()) ~attrs d

let rec mklistpat l last =
  match l with
  | [] -> last
  | hd :: tl -> mkpat_cons (rhs_loc 2) (ghpat(Ppat_tuple[hd; mklistpat tl last])) (symbol_rloc())

%}

/* Tokens */

%token AMPERAMPER
%token AMPERSAND
%token AND
%token AS
%token ASSERT
%token BACKQUOTE
%token BANG
%token BAR
%token BARBAR
%token BARRBRACKET
%token BEGIN
%token <char> CHAR
%token CLASS
%token COLON
%token COLONCOLON
%token COLONEQUAL
%token COLONGREATER
%token COMMA
%token COND
%token CONSTRAINT
%token DO
%token DONE
%token DOT
%token DOTDOT
%token DOWNTO
%token ELSE
%token END
%token EOF
%token EQUAL
%token EXCEPTION
%token EXTERNAL
%token FALSE
%token <string> FLOAT
%token FOR
%token FUN
%token FUNCTION
%token FUNCTOR
%token GREATER
%token GREATERRBRACE
%token GREATERRBRACKET
%token IF
%token IN
%token INCLUDE
%token <string> INFIXOP0
%token <string> INFIXOP1
%token <string> INFIXOP2
%token <string> INFIXOP3
%token <string> INFIXOP4
%token INHERIT
%token INITIALIZER
%token <int> INT
%token <int32> INT32
%token <int64> INT64
%token <string> LABEL
%token LAZY
%token LBRACE
%token LBRACELESS
%token LBRACKET
%token LBRACKETBAR
%token LBRACKETLESS
%token LBRACKETGREATER
%token LBRACKETPERCENT
%token LBRACKETPERCENTPERCENT
%token LESS
%token LESSMINUS
%token LET
%token LETREC
%token <string> LIDENT
%token LPAREN
%token LBRACKETAT
%token LBRACKETATAT
%token LBRACKETATATAT
%token MATCH
%token METHOD
%token MINUS
%token MINUSDOT
%token MINUSGREATER
%token MODULE
%token MUTABLE
%token <nativeint> NATIVEINT
%token NEW
%token OBJECT
%token OF
%token OPEN
%token <string> OPTLABEL
%token OR
/* %token PARSER */
%token PERCENT
%token PLUS
%token PLUSDOT
%token PLUSEQ
%token <string> PREFIXOP
%token PRIVATE
%token QUESTION
%token QUOTE
%token RBRACE
%token RBRACKET
%token REC
%token RPAREN
%token SEMI
%token SEMISEMI
%token SHARP
%token SIG
%token SPACE
%token STAR
%token <string * string option> STRING
%token STRUCT
%token THEN
%token TILDE
%token TO
%token TRUE
%token TRY
%token TYPE
%token <string> UIDENT
%token UNDERSCORE
%token UPDATE
%token VAL
%token VIRTUAL
%token WHEN
%token WHILE
%token WITH
%token <string * Location.t> COMMENT

%token EOL

/* Precedences and associativities.

Tokens and rules have precedences.  A reduce/reduce conflict is resolved
in favor of the first rule (in source file order).  A shift/reduce conflict
is resolved by comparing the precedence and associativity of the token to
be shifted with those of the rule to be reduced.

By default, a rule has the precedence of its rightmost terminal (if any).

When there is a shift/reduce conflict between a rule and a token that
have the same precedence, it is resolved using the associativity:
if the token is left-associative, the parser will reduce; if
right-associative, the parser will shift; if non-associative,
the parser will declare a syntax error.

We will only use associativities with operators of the kind  x * x -> x
for example, in the rules of the form    expr: expr BINOP expr
in all other cases, we define two precedences if needed to resolve
conflicts.

The precedences must be listed from low to high.
*/

%nonassoc IN
%nonassoc below_SPACE
%nonassoc SEMI                          /* below EQUAL ({lbl=...; lbl=...}) */
%nonassoc LET                           /* above SEMI ( ...; let ... in ...) */
%nonassoc below_WITH
%nonassoc FUNCTION WITH                 /* below BAR  (match ... with ...) */
%nonassoc AND             /* above WITH (module rec A: SIG with ... and ...) */
%nonassoc THEN                          /* below ELSE (if ... then ...) */
%nonassoc ELSE                          /* (if ... then ... else ...) */
%nonassoc LESSMINUS                     /* below COLONEQUAL (lbl <- x := e) */
%right    COLONEQUAL                    /* expr (e := e := e) */
%nonassoc AS
%left     BAR                           /* pattern (p|p|p) */
%nonassoc below_COMMA
%left     COMMA                         /* expr/expr_comma_list (e,e,e) */
%right    MINUSGREATER                  /* core_type2 (t -> t -> t) */
%right    OR BARBAR                     /* expr (e || e || e) */
%right    AMPERSAND AMPERAMPER          /* expr (e && e && e) */
%nonassoc below_EQUAL
%left     INFIXOP0 EQUAL LESS GREATER   /* expr (e OP e OP e) */
%right    INFIXOP1                      /* expr (e OP e OP e) */
%nonassoc below_LBRACKETAT
%nonassoc LBRACKETAT
%nonassoc LBRACKETATAT
%right    COLONCOLON                    /* expr (e :: e :: e) */
%left     INFIXOP2 PLUS PLUSDOT MINUS MINUSDOT PLUSEQ /* expr (e OP e OP e) */
%left     PERCENT INFIXOP3 STAR                 /* expr (e OP e OP e) */
%right    INFIXOP4                      /* expr (e OP e OP e) */
%nonassoc prec_unary_minus prec_unary_plus /* unary - */
%nonassoc prec_constant_constructor     /* cf. simple_expr (C versus C x) */
%nonassoc prec_constr_appl              /* above AS BAR COLONCOLON COMMA */
%nonassoc below_SHARP
%nonassoc SHARP                         /* simple_expr/toplevel_directive */
%nonassoc below_DOT
%nonassoc DOT
/* Finally, the first tokens of simple_expr are above everything else. */
%nonassoc BACKQUOTE BANG BEGIN CHAR FALSE FLOAT INT INT32 INT64
          LBRACE LBRACELESS LBRACKET LBRACKETBAR LIDENT LPAREN
          NEW NATIVEINT PREFIXOP STRING TRUE UIDENT
          LBRACKETPERCENT LBRACKETPERCENTPERCENT


/* Entry points */
%start implementation                   /* for implementation files */
%type <Parsetree.structure> implementation
%start toplevel_phrase                  /* for interactive use */
%type <Parsetree.toplevel_phrase> toplevel_phrase
%start use_file                         /* for the #use directive */
%type <Parsetree.toplevel_phrase list> use_file
%start parse_expression
%type <Parsetree.expression> parse_expression
%%

/* Entry points */
implementation:
  | stmt_list EOF                        { $1 }
;
toplevel_phrase:
  | top_structure                        { Ptop_def $1 }
  | EOF                                  { raise End_of_file }
;
top_structure:
  | s_expr                               { [mkstrexp $1 []] }
  |    /* empty */                       { [] }
;
use_file:
  | EOF                                  { [] }
  | s_expr EOF                         { Ptop_def[mkstrexp $1 []] :: [] }
;
parse_expression:
  | s_expr EOF { $1 }
;

stmt_list:
  | stmt stmt_list                      { $1 :: $2 }
  | /* empty */                         { [] }
;

stmt:
  | s_expr
      { mkstrexp $1 [] }
  | LPAREN LET let_binding RPAREN
      { mkstr (Pstr_value (Nonrecursive, $3)) }
  | LPAREN LETREC let_binding RPAREN
      { mkstr (Pstr_value (Recursive, $3)) }
  | LPAREN TYPE type_declaration RPAREN
      { mkstr (Pstr_type [$3] ) }
;

s_expr:
    expr                                 { $1 }
  | paren_expr                                 { $1 }
;

paren_expr:
  | LPAREN RPAREN
      { ghunit () }
  | LPAREN LET LBRACKET let_bindings RBRACKET s_expr RPAREN
      { List.fold_right
          (fun let_binding body -> mkexp_attrs (Pexp_let (Nonrecursive, let_binding, body)) (None, []))
          $4
          $6 }
  | LPAREN FUN LBRACKET ident_pattern ident_pattern_list RBRACKET s_expr RPAREN
      { let (l,o,p) = $4 in
        mkexp_attrs
          (Pexp_fun (l, o, p,
            (List.fold_right
              (fun cur prev -> let (l,o,p) = cur in ghexp (Pexp_fun (l, o, p, prev)))
              (List.rev $5)
              $7)))
          (None, [])
        }
  | LPAREN IF s_expr s_expr RPAREN
      { mkexp_attrs (Pexp_ifthenelse($3, $4, None)) (None, []) }
  | LPAREN IF s_expr s_expr s_expr RPAREN
      { mkexp_attrs (Pexp_ifthenelse($3, $4, Some $5)) (None, []) }
  /*| LPAREN COND expr_pairs s_expr s_expr RPAREN
      { if (List.length $3) mod 2 = 0 then
          List.fold_left
            (fun prev cur ->
              let (cond, branch) = cur in
              mkexp_attrs (Pexp_ifthenelse(cond, branch, Some prev)) (None, []))
            (mkexp_attrs (Pexp_ifthenelse($4, $5, None)) (None, []))
            $3
        else
          match (List.rev $3) with
          | (c, b) :: hd_list ->
            List.fold_right
              (fun cur prev ->
                let (cond, branch) = cur in
                mkexp_attrs (Pexp_ifthenelse(cond, branch, Some prev)) (None, []))
              hd_list
              (mkexp_attrs (Pexp_ifthenelse(c, b, Some (mkexp_attrs (Pexp_ifthenelse($4, $5, None)) (None, [])))) (None, []))
          | _ -> assert false;
      }*/
  | LPAREN DO expr_list s_expr RPAREN
      { (List.fold_right
          (fun prev cur -> mkexp (Pexp_sequence (prev, cur)))
          (List.rev $3)
          $4
        ) }
  | LPAREN DO expr_list s_expr error
      { unclosed "(" 1 ")" 5 }
  | LPAREN MATCH s_expr match_cases RPAREN
      { mkexp_attrs (Pexp_match($3, (List.rev $4))) (None, []) }
  | LPAREN MATCH s_expr match_cases error
      { unclosed "(" 1 ")" 5 }
  | LPAREN built_in_funcs RPAREN
      { $2 }
  | LPAREN constructor_or_func_call RPAREN
      { $2 }
;

constructor_or_func_call:
  | ASSERT s_expr %prec below_SHARP
      { mkexp_attrs (Pexp_assert $2) (None, []) }
  | s_expr labeled_s_expr_list
      { mkexp (Pexp_apply($1, (List.rev $2))) }
  | name_tag s_expr %prec below_SHARP
      { mkexp(Pexp_variant($1, Some $2)) }
  | mod_longident s_expr %prec below_SHARP
      { mkexp(Pexp_construct(mkrhs $1 1, Some $2)) }
;


expr:
  | simple_expr
    { $1 }
  | QUOTE LPAREN expr_list RPAREN
      { reloc_exp (mktailexp (rhs_loc 3) (List.rev $3)) }
  | s_expr DOT label_longident
      { mkexp (Pexp_field($1, mkrhs $3 3)) }
  | LBRACKET expr_list RBRACKET
      { mkexp (Pexp_array(List.rev $2)) }
  | LESS expr_list GREATER
      { mkexp(Pexp_tuple(List.rev $2)) }
  | LESS expr_list error
      { unclosed "<" 1 ">" 3 }
  | subtractive simple_expr %prec prec_unary_minus
      { mkuminus $1 $2 }
  | additive simple_expr %prec prec_unary_plus
      { mkuplus $1 $2 }

;

simple_expr:
  | constant
      { mkexp (Pexp_constant $1) }
  | constr_longident
      { mkexp(Pexp_construct(mkrhs $1 1, None)) }
  | record_expr
      { let (exten, fields) = $1 in mkexp (Pexp_record(fields, exten)) }
  | val_longident
      { mkexp (Pexp_ident (mkrhs $1 1)) }
  | PREFIXOP s_expr
      { mkexp(Pexp_apply(mkoperator $1 1, ["",$2])) }
  | BANG expr
      { mkexp(Pexp_apply(mkoperator "!" 1, ["",$2])) }
  | LPAREN mod_longident RPAREN %prec prec_constant_constructor
      { mkexp(Pexp_construct(mkrhs $2 1, None)) }
  | LPAREN name_tag RPAREN %prec prec_constant_constructor
      { mkexp(Pexp_variant($2, None)) }
  | LPAREN s_expr type_constraint RPAREN
      { mkexp_constraint $2 $3 }
;

/*expr_pairs:
  | s_expr s_expr
    { [($1, $2)] }
  | expr_pairs s_expr s_expr
    { ($2, $3) :: $1 }
;*/

record_expr:
  | LPAREN UPDATE simple_expr LBRACE lbl_expr_list RBRACE RPAREN
      { (Some $3, $5) }
  | LPAREN UPDATE simple_expr LBRACE lbl_expr_list RBRACE error
      { unclosed "(" 1 ")" 7 }
  | LBRACE lbl_expr_list RBRACE
      { (None, $2) }
  | LBRACE record_expr error
      { unclosed "{" 1 "}" 3 }
;
lbl_expr_list:
  |  lbl_expr lbl_expr_list { $1 :: $2 }
  |  lbl_expr { [$1] }
;
lbl_expr:
    label_longident expr
      { (mkrhs $1 1,$2) }
  | label_longident
      { (mkrhs $1 1, exp_of_label $1 1) }
;

labeled_s_expr_list:
    labeled_s_expr
      { [$1] }
  | labeled_s_expr_list labeled_s_expr
      { $2 :: $1 }
;

labeled_s_expr:
    s_expr %prec below_SHARP
      { ("", $1) }
  | label_expr
      { $1 }
;

label_expr:
  | LPAREN TILDE LIDENT s_expr RPAREN
      { ($3, $4) }
  | LPAREN QUESTION LIDENT s_expr RPAREN
      { ("?" ^ $3, $4) }
;

match_cases:
  | match_case { [$1] }
  | match_cases match_case { $2 :: $1 }
;

match_case:
  | pattern s_expr { Exp.case $1 $2 }
;

built_in_funcs:
  | PREFIXOP s_expr s_expr
      { mkinfix $2 $1 $3 }
  | PLUS s_expr s_expr
      { mkinfix $2 "+" $3 }
  | PLUSDOT s_expr s_expr
      { mkinfix $2 "+." $3 }
  | MINUS s_expr s_expr
      { mkinfix $2 "-" $3 }
  | MINUSDOT s_expr s_expr
      { mkinfix $2 "-." $3 }
  | STAR s_expr s_expr
      { mkinfix $2 "*" $3 }
  | EQUAL s_expr s_expr
      { mkinfix $2 "=" $3 }
  | LESS s_expr s_expr
      { mkinfix $2 "<" $3 }
  | GREATER s_expr s_expr
      { mkinfix $2 ">" $3 }
  | OR s_expr s_expr
      { mkinfix $2 "or" $3 }
  | BARBAR s_expr s_expr
      { mkinfix $2 "||" $3 }
  | AMPERAMPER s_expr s_expr
      { mkinfix $2 "&&" $3 }
  | PERCENT s_expr s_expr
      { mkinfix $2 "%" $3 }
  | COLONEQUAL s_expr s_expr
      { mkinfix $2 ":=" $3 }

  /* Auto currying */
  | PREFIXOP s_expr
      { mkpartial $1 $2 }
  | PLUS s_expr
      { mkpartial "+" $2 }
  | PLUSDOT s_expr
      { mkpartial "+." $2 }
  | MINUS s_expr
      { mkpartial "-" $2 }
  | MINUSDOT s_expr
      { mkpartial "-." $2 }
  | STAR s_expr
      { mkpartial "*" $2 }
  | EQUAL s_expr
      { mkpartial "=" $2 }
  | LESS s_expr
      { mkpartial "<" $2 }
  | GREATER s_expr
      { mkpartial ">" $2 }
  | OR s_expr
      { mkpartial "or" $2 }
  | BARBAR s_expr
      { mkpartial "||" $2 }
  | AMPERAMPER s_expr
      { mkpartial "&&" $2 }
  | PERCENT s_expr
      { mkpartial "%" $2 }
;

expr_list:
  | /* empty */                                  { [] }
  | expr_list s_expr                            { $2 :: $1 }
;

let_bindings:
  | /* empty */                                  { [] }
  | let_binding let_bindings
      { $1 :: $2 }
;

let_binding:
  | let_binding_ s_expr
      { [Vb.mk ~loc:(symbol_rloc()) ~attrs:[] $1 $2] }
;

let_binding_:
  | pattern
      { $1 }
  | val_ident
      { mkpatvar $1 1 }
  | LPAREN simple_pattern COLON core_type RPAREN
      { mkpat(Ppat_constraint($2, $4)) }
;

ident_pattern:
  | simple_pattern
      { ("", None, $1) }
  | LPAREN simple_pattern COLON core_type RPAREN
      { ("", None, mkpat(Ppat_constraint($2, $4))) }
  | LPAREN QUESTION label_let_pattern opt_default RPAREN
      { ("?" ^ fst $3, $4, snd $3) }
  /*| LPAREN QUESTION LIDENT pattern_var RPAREN
      { ("?" ^ $3, None, $4) }*/
  | LPAREN TILDE label_let_pattern RPAREN
      { (fst $3, None, snd $3) }
  | LPAREN TILDE LIDENT simple_pattern RPAREN
      { ($3, None, $4) }
;

let_pattern:
    pattern
      { $1 }
  | pattern COLON core_type
      { mkpat(Ppat_constraint($1, $3)) }
;

label_var:
    LIDENT    { ($1, mkpat(Ppat_var (mkrhs $1 1))) }
;

pattern_var:
    LIDENT            { mkpat(Ppat_var (mkrhs $1 1)) }
  | UNDERSCORE        { mkpat Ppat_any }
;

label_let_pattern:
    label_var
      { $1 }
  | LPAREN label_var COLON core_type RPAREN
      { let (lab, pat) = $2 in (lab, mkpat(Ppat_constraint(pat, $4))) }
;

opt_default:
    /* empty */                         { None }
  | s_expr                      { Some $1 }
;

pattern:
  | simple_pattern
      { $1 }
  | pattern AS LIDENT
      { mkpat (Ppat_alias ($1, mkrhs $3 3)) }
  | pattern AS error
      { expecting 3 "identifier" }
  | LPAREN name_tag pattern RPAREN %prec prec_constr_appl
      { mkpat(Ppat_variant($2, Some $3)) }
  | LPAREN mod_longident pattern RPAREN %prec prec_constr_appl
      { mkpat(Ppat_construct(mkrhs $2 1, Some $3)) }
;

simple_pattern:
  | LIDENT %prec below_EQUAL
      { mkpat (Ppat_var (mkrhs $1 1)) }
  | simple_pattern_not_ident { $1 }
;

simple_pattern_not_ident:
  | UNDERSCORE
      { mkpat (Ppat_any) }
  | signed_constant
      { mkpat (Ppat_constant $1) }
  | LPAREN name_tag RPAREN
      { mkpat(Ppat_variant($2, None)) }
  | constr_longident
      { mkpat(Ppat_construct(mkrhs $1 1, None)) }
  | LPAREN mod_longident RPAREN
      { mkpat(Ppat_construct(mkrhs $2 1, None)) }
  | LPAREN UIDENT RPAREN
      { mkpat(Ppat_construct(mkrhs (Lident $2) 1, None)) }
  | signed_constant DOTDOT signed_constant
      { mkpat (Ppat_interval ($1, $3)) }
  | LBRACE lbl_pattern_list RBRACE
      { let (fields, closed) = $2 in mkpat(Ppat_record(fields, closed)) }
  | LBRACE lbl_pattern_list error
      { unclosed "{" 1 "}" 3 }
  | LESS pattern_list GREATER
      { mkpat(Ppat_tuple(List.rev $2)) }
  | LESS pattern_list error
      { unclosed "<" 1 ">" 3 }
  | QUOTE LPAREN pattern_list RPAREN
      { reloc_pat (mktailpat (rhs_loc 4) (List.rev $3)) }
  | QUOTE LPAREN pattern_list error
      { unclosed "'(" 2 ")" 4 }
  | QUOTE LPAREN pattern_list AMPERSAND pattern RPAREN
      { mklistpat (List.rev $3) $5 }
  | QUOTE LPAREN pattern_list AMPERSAND pattern error
      { unclosed "'(" 2 ")" 6 }
  | LBRACKET pattern_list RBRACKET
      { mkpat (Ppat_array (List.rev $2)) }
  | LBRACKET pattern_list error
      { unclosed "[" 1 "]" 4 }
  /* If you change simple_pattern_not_ident to just simple_pattern (allowing for
    identifiers), the grammar becomes ambiguous and we can't both parse
    (let [a (func 10)] a) and
    (let [a (func : int -> int)] a)*/
  /*| LPAREN pattern COLON core_type RPAREN
      { mkpat(Ppat_constraint($2, $4)) }
  | LPAREN pattern COLON core_type error
      { unclosed "(" 1 ")" 5 }*/
;

lbl_pattern_list:
    lbl_pattern { [$1], Closed }
  | lbl_pattern { [$1], Closed }
  | lbl_pattern UNDERSCORE { [$1], Open }
  | lbl_pattern lbl_pattern_list
      { let (fields, closed) = $2 in $1 :: fields, closed }
;

lbl_pattern:
  | label_longident EQUAL pattern
      { (mkrhs $1 1,$3) }
  | label_longident
      { (mkrhs $1 1, pat_of_label $1 1) }
;

ident_pattern_list:
  | /* empty */
      { [] }
  | ident_pattern_list ident_pattern
      { $2 :: $1 }
;

pattern_list:
  | pattern
      { [$1] }
  | pattern_list pattern
      { $2 :: $1 }
;

label_longident:
    LIDENT                                      { Lident $1 }
  | mod_longident DOT LIDENT                    { Ldot($1, $3) }
;

mod_longident:
    UIDENT                                      { Lident $1 }
  | mod_longident DOT UIDENT                    { Ldot($1, $3) }
;

/**
 * ----------------------
 *    Type Annotations
 * ----------------------
 */

type_constraint:
    COLON core_type                             { (Some $2, None) }
  | COLON core_type COLONGREATER core_type      { (Some $2, Some $4) }
  | COLONGREATER core_type                      { (None, Some $2) }
  | COLON error                                 { syntax_error() }
  | COLONGREATER error                          { syntax_error() }
;

core_type:
    core_type2
      { $1 }
  | core_type2 AS QUOTE LIDENT
      { mktyp(Ptyp_alias($1, $4)) }
  | LPAREN MINUSGREATER core_type2 core_type2_list RPAREN
      {
        List.fold_right
          (fun acc x -> mktyp(Ptyp_arrow("", acc, x)))
          (List.rev $4)
          $3
      }
;


core_type2:
  | simple_core_type %prec below_LBRACKETAT
      { $1 }
  | LPAREN core_type RPAREN
      { $2 }
  | QUESTION LIDENT COLON core_type2 MINUSGREATER core_type2
      { mktyp(Ptyp_arrow("?" ^ $2 , mkoption $4, $6)) }
  | OPTLABEL core_type2 MINUSGREATER core_type2
      { mktyp(Ptyp_arrow("?" ^ $1 , mkoption $2, $4)) }
  /*| LIDENT COLON core_type2 MINUSGREATER core_type2
      { mktyp(Ptyp_arrow($1, $3, $5)) }*/
;

simple_core_type:
  | simple_core_type2  %prec below_SHARP
      { $1 }
  | LESS simple_core_type simple_core_type_list GREATER
      { mktyp(Ptyp_tuple($2 :: (List.rev $3))) }
  /*| LPAREN core_type_comma_list RPAREN %prec below_SHARP
      { match $2 with [sty] -> sty | _ -> raise Parse_error }*/
;

simple_core_type2:
    QUOTE LIDENT
      { mktyp(Ptyp_var $2) }
  | UNDERSCORE
      { mktyp(Ptyp_any) }
  | type_longident
      { mktyp(Ptyp_constr(mkrhs $1 1, [])) }
  | LPAREN type_longident simple_core_type_list RPAREN
      { mktyp(Ptyp_constr(mkrhs $2 2, $3)) }
  /*| LPAREN core_type_comma_list RPAREN type_longident
      { mktyp(Ptyp_constr(mkrhs $4 4, List.rev $2)) }
  | LESS meth_list GREATER
      { let (f, c) = $2 in mktyp(Ptyp_object (f, c)) }
  | LESS GREATER
      { mktyp(Ptyp_object ([], Closed)) }*/
/* PR#3835: this is not LR(1), would need lookahead=2
  | LBRACKET simple_core_type RBRACKET
      { mktyp(Ptyp_variant([$2], Closed, None)) }
*/
  | LBRACKET BAR row_field_list RBRACKET
      { mktyp(Ptyp_variant(List.rev $3, Closed, None)) }
  | LBRACKET row_field BAR row_field_list RBRACKET
      { mktyp(Ptyp_variant($2 :: List.rev $4, Closed, None)) }
  | LBRACKETGREATER row_field_list RBRACKET
      { mktyp(Ptyp_variant(List.rev $2, Open, None)) }
  | LBRACKETGREATER RBRACKET
      { mktyp(Ptyp_variant([], Open, None)) }
  | LBRACKETLESS row_field_list RBRACKET
      { mktyp(Ptyp_variant(List.rev $2, Closed, Some [])) }
  /*| LBRACKETLESS row_field_list GREATER name_tag_list RBRACKET
      { mktyp(Ptyp_variant(List.rev $2, Closed, Some (List.rev $4))) }*/
  | LPAREN MODULE package_type RPAREN
      { mktyp(Ptyp_package $3) }
;

core_type_comma_list:
    core_type                                   { [$1] }
  | core_type_comma_list COMMA core_type        { $3 :: $1 }
;

simple_core_type_list:
  | simple_core_type
      { [$1] }
  | simple_core_type_list simple_core_type
      { $2 :: $1 }
;

core_type2_list:
  | core_type2
      { [$1] }
  | core_type2_list core_type2
      { $2 :: $1 }
;

type_longident:
    LIDENT                                      { Lident $1 }
  | mod_ext_longident DOT LIDENT                { Ldot($1, $3) }
;

mod_ext_longident:
    UIDENT                                      { Lident $1 }
  | mod_ext_longident DOT UIDENT                { Ldot($1, $3) }
  | mod_ext_longident LPAREN mod_ext_longident RPAREN { lapply $1 $3 }
;

meth_list:
    field meth_list                     { let (f, c) = $2 in ($1 :: f, c) }
  | field                              { [$1], Closed }
  | DOTDOT                                      { [], Open }
;

field:
    label COLON poly_type            { ($1, [], $3) }
;

label:
    LIDENT                                      { $1 }
;

row_field_list:
    row_field                                   { [$1] }
  | row_field_list BAR row_field                { $3 :: $1 }
;

row_field:
  | simple_core_type                            { Rinherit $1 }
;

package_type:
    mty_longident { (mkrhs $1 1, []) }
  | mty_longident WITH package_type_cstrs { (mkrhs $1 1, $3) }
;

package_type_cstr:
    TYPE label_longident EQUAL core_type { (mkrhs $2 2, $4) }
;

package_type_cstrs:
    package_type_cstr { [$1] }
  | package_type_cstr AND package_type_cstrs { $1::$3 }
;

mty_longident:
    LIDENT                                       { Lident $1 }
  | mod_ext_longident DOT LIDENT                 { Ldot($1, $3) }

typevar_list:
    QUOTE LIDENT                             { [$2] }
  | typevar_list QUOTE LIDENT                { $3 :: $1 }
;

poly_type:
    core_type
      { $1 }
  | typevar_list DOT core_type
      { mktyp(Ptyp_poly(List.rev $1, $3)) }
;

/**
 * ----------------------
 *    Type Declaration
 * ----------------------
 */

type_declaration:
  | LIDENT type_kind constraints
      { let (kind, priv, manifest) = $2 in
        Type.mk (mkrhs $1 2)
          ~cstrs:(List.rev $3)
          ~kind ~priv ?manifest ~loc:(symbol_rloc())
       }
  | LPAREN LIDENT type_parameters RPAREN type_kind constraints
      { let (kind, priv, manifest) = $5 in
        Type.mk (mkrhs $2 2)
          ~params:$3 ~cstrs:(List.rev $6)
          ~kind ~priv ?manifest ~loc:(symbol_rloc())
       }
;

constraints:
  | constraints CONSTRAINT constrain        { $3 :: $1 }
  | /* empty */                             { [] }
;

constrain:
  | core_type EQUAL core_type          { $1, $3, symbol_rloc() }
;

type_kind:
    /*empty*/
      { (Ptype_abstract, Public, None) }
  | core_type
      { (Ptype_abstract, Public, Some $1) }
  | PRIVATE core_type
      { (Ptype_abstract, Private, Some $2) }
  | LPAREN BAR constructor_declarations RPAREN
      { (Ptype_variant(List.rev $3), Public, None) }
  | LPAREN BAR constructor_declarations error
      { unclosed "(" 1 ")" 4 }
  | PRIVATE constructor_declarations
      { (Ptype_variant(List.rev $2), Private, None) }
  | private_flag BAR constructor_declarations
      { (Ptype_variant(List.rev $3), $1, None) }
  | DOTDOT
      { (Ptype_open, Public, None) }
  | private_flag LBRACE label_declarations RBRACE
      { (Ptype_record(List.rev $3), $1, None) }
  | core_type private_flag constructor_declarations
      { (Ptype_variant(List.rev $3), $2, Some $1) }
  | core_type DOTDOT
      { (Ptype_open, Public, Some $1) }
  | core_type private_flag LBRACE label_declarations RBRACE
      { (Ptype_record(List.rev $4), $2, Some $1) }
;

type_parameters:
  | optional_type_parameter_list
      { $1 }
;

optional_type_parameter:
  | type_variance optional_type_variable        { $2, $1 }
;

optional_type_parameter_list:
  | optional_type_parameter                              { [$1] }
  | optional_type_parameter optional_type_parameter_list    { $1 :: $2 }
;

optional_type_variable:
  | QUOTE LIDENT                                 { mktyp(Ptyp_var $2) }
  | UNDERSCORE                                  { mktyp(Ptyp_any) }
;

type_variance:
  | /* empty */                                 { Invariant }
  | PLUS                                        { Covariant }
  | MINUS                                       { Contravariant }
;

type_variable:
  | QUOTE LIDENT                                 { mktyp(Ptyp_var $2) }
;

constructor_declarations:
  | constructor_declaration
      { [$1] }
  | constructor_declarations constructor_declaration
      { $2 :: $1 }
;
constructor_declaration:
  | LPAREN constr_ident generalized_constructor_arguments RPAREN
      {let args,res = $3 in
       Type.constructor (mkrhs $2 1) ~args ?res ~loc:(symbol_rloc())}
;

generalized_constructor_arguments:
  | /*empty*/
      { ([],None) }
  | simple_core_type_list
      { (List.rev $1, None) }
  | COLON simple_core_type_list MINUSGREATER simple_core_type
      { (List.rev $2, Some $4) }
  | COLON simple_core_type
      { ([],Some $2) }
;

label_declarations:
  | label_declaration
      { [$1] }
  | label_declarations label_declaration
      { $2 :: $1 }
;
label_declaration:
  | mutable_flag label poly_type
      { Type.field (mkrhs $2 2) $3 ~mut:$1 ~loc:(symbol_rloc()) }
;


/**
 * ----------------------
 *       Miscellaneous
 * ----------------------
 */

private_flag:
  | /* empty */                                 { Public }
  | PRIVATE                                     { Private }
;

mutable_flag:
  | /* empty */                                 { Immutable }
  | MUTABLE                                     { Mutable }
;

name_tag:
  BACKQUOTE ident                             { $2 }
;


/**
 * ----------------------
 *       Constants
 * ----------------------
 */
ident:
    UIDENT                                      { $1 }
  | LIDENT                                      { $1 }
;

val_ident:
    LIDENT                                      { $1 }
;

val_longident:
    val_ident                                   { Lident $1 }
  | mod_longident DOT val_ident                 { Ldot($1, $3) }
;

constr_ident:
    UIDENT                                      { $1 }
  | LPAREN RPAREN                               { "()" }
  | COLONCOLON                                  { "::" }
  | FALSE                                       { "false" }
  | TRUE                                        { "true" }
;

signed_constant:
    constant                               { $1 }
  | MINUS INT                              { Const_int(- $2) }
  | MINUS FLOAT                            { Const_float("-" ^ $2) }
  | MINUS INT32                            { Const_int32(Int32.neg $2) }
  | MINUS INT64                            { Const_int64(Int64.neg $2) }
  | MINUS NATIVEINT                        { Const_nativeint(Nativeint.neg $2) }
  | PLUS INT                               { Const_int $2 }
  | PLUS FLOAT                             { Const_float $2 }
  | PLUS INT32                             { Const_int32 $2 }
  | PLUS INT64                             { Const_int64 $2 }
  | PLUS NATIVEINT                         { Const_nativeint $2 }
;

constr_longident:
  | LBRACKET RBRACKET                      { Lident "[]" }
  | LPAREN RPAREN                          { Lident "()" }
  | FALSE                                  { Lident "false" }
  | TRUE                                   { Lident "true" }
;

constant:
  | INT                                   { Const_int $1 }
  | CHAR                                  { Const_char $1 }
  | STRING                                { let (s, d) = $1 in Const_string (s, d) }
  | FLOAT                                 { Const_float $1 }
  | INT32                                 { Const_int32 $1 }
  | INT64                                 { Const_int64 $1 }
  | NATIVEINT                             { Const_nativeint $1 }
;

subtractive:
  | MINUS                                       { "-" }
  | MINUSDOT                                    { "-." }
;
additive:
  | PLUS                                        { "+" }
  | PLUSDOT                                     { "+." }
;
%%
