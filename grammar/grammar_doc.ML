(* Author: Basil Fürer *)

(* the grammar as a reader sees it: every grammar command keeps its surface as written
   (templates, operators, groups, the token clause, the precedence declarations, no
   actions and no carriers), and the document antiquotations print it:
   \<open>@{grammar G}\<close> as EBNF text, \<open>@{grammar_rail G}\<close> as a railroad diagram.  A
   grammar built in ML has no surface; it is printed from its elaborated productions *)

signature GRAMMAR_DOC =
sig
  val register: Grammar_Common.surface -> local_theory -> local_theory
  val pretty_grammar: Proof.context -> xstring * Position.T -> Pretty.T
  val rail_grammar: Proof.context -> xstring * Position.T ->
    (string Antiquote.antiquote * Rail.rail) list
end;

structure Grammar_Doc: GRAMMAR_DOC =
struct

open Grammar_Common;

(** the surfaces, by the grammar's name (also for a grammar of templates only) **)

structure Data = Generic_Data
(
  type T = surface Name_Space.table;
  val empty: T = Name_Space.empty_table "grammar";
  fun merge data: T = Name_Space.merge_tables data;
);

fun register (surf: surface) =
  Local_Theory.declaration
    {syntax = false, pervasive = false, pos = Binding.pos_of (#name surf)}
    (fn phi => fn context =>
      Data.map (#2 o Name_Space.define context true (Morphism.binding phi (#name surf), surf))
        context);

datatype source = Surface of surface | Record of grammar;

fun lookup ctxt (xname, pos) =
  (case try (Name_Space.check (Context.Proof ctxt) (Data.get (Context.Proof ctxt))) (xname, pos) of
    SOME (_, surf) => Surface surf
  | NONE => Record (#2 (check_grammar ctxt (xname, pos))));


(** EBNF text **)

(* a cartouche or a type as written: the parser keeps the text without delimiters *)
fun written src =
  if Input.is_delimited src then cartouche (Input.string_of src) else Input.string_of src;

(* an item of a precedence level: a name, else a terminal's spelling *)
fun prec_text n = if Symbol_Pos.is_identifier n then n else quote n;

fun string_of_gsym (Lit (s, _)) = quote s
  | string_of_gsym (Ref (n, _)) = n
  | string_of_gsym (Tok src) = written src
  | string_of_gsym (Span _) = "";

fun annotated s ann = s ^ (case ann of NONE => "" | SOME a => string_of_ann a);

(* an item as text; \<open>@span\<close> is a value of the alternative, not a symbol *)
fun string_of_item (Sym g) = string_of_gsym g
  | string_of_item (App ((n, _), args)) = n ^ "(" ^ commas (map string_of_item args) ^ ")"
  | string_of_item (Group (its, _)) = "(" ^ string_of_items its ^ ")"
  | string_of_item (Rep (opr, it, _)) = string_of_item it ^ opr
and string_of_items its =
  space_implode " "
    (map_filter (fn (Sym (Span _), _) => NONE | (it, ann) => SOME (annotated (string_of_item it) ann))
      its);

val epsilon = "\<epsilon>";

fun pretty_alt ((its, _), mark) =
  let
    val body = string_of_items its;
    val syms = if body = "" then [Pretty.str epsilon] else [Pretty.str body];
    val prec =
      (case mark of
        NONE => []
      | SOME (n, _) => [Pretty.brk 1, Pretty.str "(", Pretty.keyword1 "prec", Pretty.brk 1,
          Pretty.str (n ^ ")")]);
  in Pretty.block (syms @ prec) end;

(* \<open>A ::= a | b\<close> on one line where it fits, else one alternative per line, each
   \<open>|\<close> under the \<open>::=\<close> *)
fun pretty_rule lhs alts =
  Pretty.markup_block
    {markup = Markup.empty, open_block = false, consistent = true,
     indent = length (Symbol.explode lhs) + 1}
    (Pretty.str (lhs ^ " ::= ") ::
      flat (separate [Pretty.brk 1, Pretty.str "| "] (map single alts)));

fun group_lhs ((b, params), _) =
  Binding.name_of b ^ (if null params then "" else "(" ^ commas (map #1 params) ^ ")");

fun pretty_level ((assoc, _), items) =
  Pretty.block (Pretty.keyword2 assoc :: maps (fn ((n, _), strict) =>
    [Pretty.brk 1, Pretty.str (prec_text n ^ (if strict then "!" else ""))]) items);

fun pretty_chain levels =
  Pretty.block (Pretty.keyword1 "precedence" :: Pretty.brk 1 ::
    flat (separate [Pretty.brk 1, Pretty.str ">", Pretty.brk 1] (map (single o pretty_level) levels)));

fun pretty_forbid ((p, _), k, (kind, _), cs) =
  Pretty.block ([Pretty.keyword1 "forbid", Pretty.brk 1,
    Pretty.str (prec_text p ^ " @ " ^ string_of_int k), Pretty.brk 1, Pretty.keyword2 kind] @
    maps (fn (c, _) => [Pretty.brk 1, Pretty.str (prec_text c)]) cs);

fun pretty_header (surf: surface) =
  (if null (#opens surf) then []
   else [Pretty.block (Pretty.keyword1 "open" ::
     maps (fn (n, _) => [Pretty.brk 1, Pretty.str n]) (#opens surf))]) @
  (case (#lexer surf, #tok_typ surf) of
    (SOME (l, _), _) => [Pretty.block [Pretty.keyword1 "tokens", Pretty.brk 1,
      Pretty.keyword1 "of", Pretty.brk 1, Pretty.str l]]
  | (NONE, SOME T) => [Pretty.block [Pretty.keyword1 "tokens", Pretty.brk 1, Pretty.str (written T)]]
  | (NONE, NONE) => []) @
  map pretty_chain (#chains surf) @
  map pretty_forbid (#forbids surf);

fun pretty_surface (surf: surface) =
  Pretty.chunks
    (pretty_header surf @
     map (fn (g as (_, alts)) => pretty_rule (group_lhs (#1 g)) (map pretty_alt alts))
       (#groups surf));

(* a grammar built in ML: its productions, a terminal class by its constructor, a fixed
   terminal by its spelling, the nonterminals by their display names *)
fun pretty_record ctxt (gr: grammar) =
  let
    val shown = display_names ctxt (Symtab.keys (#nonterms gr));
    fun disp n = the_default n (AList.lookup (op =) shown n);
    fun term_text t =
      (case AList.lookup (op aconv) (#lit_names gr) t of
        SOME s => quote s
      | NONE => XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt t)));
    fun sym (RN n) = disp n
      | sym (RC k) = term_text (Vector.sub (#terminals gr, k))
      | sym (RT k) = term_text (Vector.sub (#terminals gr, k));
    val prods = fold (fn p => Inttab.update (#no p, p)) (#prods gr) Inttab.empty;
    fun alt i =
      (case #rhs (the (Inttab.lookup prods i)) of
        [] => Pretty.str epsilon
      | rhs => Pretty.str (space_implode " " (map (fn (s, a) => sym s ^ string_of_ann a) rhs)));
  in
    Pretty.chunks (map (fn (n, {prods = ps, ...}) => pretty_rule (disp n) (map alt ps))
      (nonterms_list gr))
  end;

fun pretty_grammar ctxt name =
  (case lookup ctxt name of
    Surface surf => pretty_surface surf
  | Record gr => pretty_record ctxt gr);


(** railroad diagrams **)

fun cat rails = Rail.Cat (0, rails);
val empty = cat [];
fun maybe rail = Rail.Bar [empty, cat [rail]];

(* an annotation on a group or an operator applies to the nonterminal it generates,
   which a diagram has no box for: such an item is one box with its text *)
fun rail_item (Sym (Lit (s, _))) = Rail.Terminal (false, s)
  | rail_item (Sym g) = Rail.Nonterminal (string_of_gsym g)
  | rail_item (it as App _) = Rail.Nonterminal (string_of_item it)
  | rail_item (Group (its, _)) = Rail.Bar [rail_items its]
  | rail_item (Rep ("*", it, _)) = maybe (Rail.Plus (cat [rail_item it], empty))
  | rail_item (Rep ("+", it, _)) = Rail.Plus (cat [rail_item it], empty)
  | rail_item (Rep (_, it, _)) = maybe (rail_item it)
and rail_annotated (Sym (Lit (s, _)), SOME a) = Rail.Terminal (false, s ^ string_of_ann a)
  | rail_annotated (it, SOME a) = Rail.Nonterminal (annotated (string_of_item it) (SOME a))
  | rail_annotated (it, NONE) = rail_item it
and rail_items its =
  cat (map rail_annotated (filter_out (fn (Sym (Span _), _) => true | _ => false) its));

fun rail_surface (surf: surface) =
  map (fn (g, alts) =>
    (Antiquote.Text (group_lhs g), Rail.Bar (map (rail_items o #1 o #1) alts))) (#groups surf);

fun rail_record ctxt (gr: grammar) =
  let
    val shown = display_names ctxt (Symtab.keys (#nonterms gr));
    fun disp n = the_default n (AList.lookup (op =) shown n);
    fun term_rail t =
      (case AList.lookup (op aconv) (#lit_names gr) t of
        SOME s => Rail.Terminal (false, s)
      | NONE => Rail.Nonterminal (XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt t))));
    fun sym (RN n, a) = Rail.Nonterminal (disp n ^ string_of_ann a)
      | sym (RC k, _) = term_rail (Vector.sub (#terminals gr, k))
      | sym (RT k, _) = term_rail (Vector.sub (#terminals gr, k));
    val prods = fold (fn p => Inttab.update (#no p, p)) (#prods gr) Inttab.empty;
    fun alt i = cat (map sym (#rhs (the (Inttab.lookup prods i))));
  in
    map (fn (n, {prods = ps, ...}) => (Antiquote.Text (disp n), Rail.Bar (map alt ps)))
      (nonterms_list gr)
  end;

fun rail_grammar ctxt name =
  (case lookup ctxt name of
    Surface surf => rail_surface surf
  | Record gr => rail_record ctxt gr);


(** antiquotations **)

val _ = Theory.setup
  (Document_Output.antiquotation_pretty_embedded \<^binding>\<open>grammar\<close>
    (Scan.lift (Parse.position Parse.embedded)) pretty_grammar #>
   Document_Output.antiquotation_raw_embedded \<^binding>\<open>grammar_rail\<close>
    (Scan.lift (Parse.position Parse.embedded))
    (fn ctxt => fn name => Rail.output_rules ctxt (rail_grammar ctxt name)));

end;
