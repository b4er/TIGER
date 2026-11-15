(* Author: Basil Fürer *)

theory Doc_Tests
  imports TIGER_Grammar.Grammar_Command
begin

section \<open>The grammar as a reader sees it: \<open>@{grammar}\<close>\<close>

datatype d_tok = DNum | DId | DPlus | DStar | DWhile | DColon

text \<open>Layout-free, with precedence, an operator, a group and a template of the prelude.\<close>

grammar d_arith =
  tokens \<open>d_tok\<close>
  terminals "+" = \<open>DPlus\<close> and "*" = \<open>DStar\<close>
  precedence left "*" > left "+"
  productions
    L :: \<open>nat list\<close> = Sep1(E, "+") DId? \<Rightarrow> \<open>\<lambda>xs _. xs\<close> | (DId "*")+ \<Rightarrow> \<open>\<lambda>_. []\<close> | \<Rightarrow> \<open>[]\<close>
  and
    E :: \<open>nat\<close>
      = E "+" E \<Rightarrow> \<open>(+)\<close>
      | E "*" E \<Rightarrow> \<open>(*)\<close>
      | DNum \<Rightarrow> \<open>\<lambda>_. 1\<close>

text \<open>With layout annotations.\<close>

grammar d_py =
  tokens \<open>d_tok\<close>
  terminals "while" = \<open>DWhile\<close> and ":" = \<open>DColon\<close>
  productions
      Block :: \<open>nat\<close> = Stmt\<^sup>= | Block\<^sup>= Stmt\<^sup>= \<Rightarrow> \<open>(+)\<close>
    and
      Stmt :: \<open>nat\<close>
        = DId\<^sup>= \<Rightarrow> \<open>\<lambda>_. 1\<close>
        | "while"\<^sup>= DId\<^sup>> ":"\<^sup>> Block\<^sup>> \<Rightarrow> \<open>\<lambda>_ n. n + 1\<close>

text \<open>Templates only, and a copy of another grammar's nonterminal.\<close>

grammar d_tmpl =
  productions
    Pair(X, Y) :: \<open>'x \<times> 'y\<close> = X Y \<Rightarrow> \<open>Pair\<close>

grammar d_copy =
  tokens \<open>d_tok\<close>
  terminals ":" = \<open>DColon\<close>
  productions
    S :: \<open>nat \<times> nat\<close> = d_tmpl.Pair(d_arith.E, d_arith.E) ":" @span \<Rightarrow> \<open>\<lambda>p _. p\<close>

text \<open>A rule too long for a line has one alternative per line.\<close>

grammar d_long =
  tokens \<open>d_tok\<close>
  terminals "while" = \<open>DWhile\<close> and ":" = \<open>DColon\<close>
  productions
    S :: \<open>unit\<close>
      = "while" DId ":" S S \<Rightarrow> \<open>\<lambda>_ _ _. ()\<close>
      | DId DId DId DId DId DId DId DId DId DId \<Rightarrow> \<open>\<lambda>_ _ _ _ _ _ _ _ _ _. ()\<close>
      | DNum ":" DNum ":" DNum \<Rightarrow> \<open>\<lambda>_ _ _. ()\<close>

text \<open>
  @{grammar [display] d_long}
  @{grammar [display] d_arith}
  @{grammar [display] d_py}
  @{grammar [display] Grammar_Prelude}
  @{grammar [display] d_copy}
  @{grammar_rail d_arith}
  @{grammar_rail d_py}
  @{grammar_rail Grammar_Prelude}
\<close>

ML \<open>
fun shown ctxt name =
  Pretty.pure_string_of (Grammar_Doc.pretty_grammar ctxt (name, Position.none))
  |> YXML.parse_body |> XML.content_of |> trim_line;
fun expect ctxt name lines =
  let val s = shown ctxt name in
    if s = cat_lines lines then ()
    else error ("@{grammar " ^ name ^ "}:\n" ^ ML_Syntax.print_string s ^ "\n" ^ ML_Syntax.print_string (cat_lines lines))
  end;

val _ = expect \<^context> "d_long"
  ["tokens \<open>d_tok\<close>",
   "S ::= \"while\" DId \":\" S S",
   "  | DId DId DId DId DId DId DId DId DId DId",
   "  | DNum \":\" DNum \":\" DNum"];
val _ = expect \<^context> "d_arith"
  ["tokens \<open>d_tok\<close>",
   "precedence left \"*\" > left \"+\"",
   "L ::= Sep1(E, \"+\") DId? | (DId \"*\")+ | \<epsilon>",
   "E ::= E \"+\" E | E \"*\" E | DNum"];
val _ = expect \<^context> "d_py"
  ["tokens \<open>d_tok\<close>",
   "Block ::= Stmt\<^sup>= | Block\<^sup>= Stmt\<^sup>=",
   "Stmt ::= DId\<^sup>= | \"while\"\<^sup>= DId\<^sup>> \":\"\<^sup>> Block\<^sup>>"];
val _ = expect \<^context> "Grammar_Prelude"
  ["List(X) ::= \<epsilon> | List(X) X",
   "List1(X) ::= X | List1(X) X",
   "Opt(X) ::= \<epsilon> | X",
   "Sep1(X, S) ::= X | Sep1(X, S) S X",
   "Sep(X, S) ::= \<epsilon> | Sep1(X, S)"];
val _ = expect \<^context> "d_copy"
  ["tokens \<open>d_tok\<close>",
   "S ::= d_tmpl.Pair(d_arith.E, d_arith.E) \":\""];
\<close>

text \<open>A grammar built in ML has no surface: it is printed from its productions.\<close>

local_setup \<open>
  let
    fun alt syms : Grammar_Common.alternative =
      (map (fn s => (Grammar_Common.Ref (s, Position.none), NONE)) syms,
       SOME (Input.string "\<lambda>_. ()"));
  in
    Grammar_Command.grammar_cmd []
      {name = \<^binding>\<open>d_ml\<close>, tok_typ = SOME (Input.string "d_tok"), lexer = NONE,
       terminals = [], prec = NONE,
       productions = [((Binding.name "S", SOME (Input.string "unit")), [alt ["DId"], alt ["DNum"]])]}
  end
\<close>

ML \<open>expect \<^context> "d_ml" ["S ::= DId | DNum"]\<close>

text \<open>@{grammar [display] d_ml} @{grammar_rail d_ml}\<close>

end
