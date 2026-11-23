(* Author: Basil Fürer *)

theory Utf8_Tests
  imports Lexer_Command_Tests Stress_Lexer_Tests
begin

section \<open>UTF-8\<close>

subsection \<open>Codepoint intervals as byte intervals\<close>

text \<open>The byte intervals of a codepoint interval, as numbers:\<close>

definition byte_seqs :: \<open>nat \<times> nat \<Rightarrow> (nat \<times> nat) list list\<close> where
  \<open>byte_seqs ab = map (map (\<lambda>(l, h). (of_char l, of_char h))) (utf8_ranges ab)\<close>

text \<open>An interval splits where the length of the encoding changes and around the
  surrogates, which have no encoding:\<close>

lemma \<open>byte_seqs (0x7F, 0x80) = [[(0x7F, 0x7F)], [(0xC2, 0xC2), (0x80, 0x80)]]\<close>
  by eval

lemma \<open>byte_seqs (0x7FF, 0x800) =
  [[(0xDF, 0xDF), (0xBF, 0xBF)], [(0xE0, 0xE0), (0xA0, 0xA0), (0x80, 0x80)]]\<close>
  by eval

lemma \<open>byte_seqs (0xD7FF, 0xE000) =
  [[(0xED, 0xED), (0x9F, 0x9F), (0xBF, 0xBF)], [(0xEE, 0xEE), (0x80, 0x80), (0x80, 0x80)]]\<close>
  by eval

lemma \<open>byte_seqs (0xD800, 0xDFFF) = []\<close>
  by eval

lemma \<open>byte_seqs (0xFFFF, 0x10000) =
  [[(0xEF, 0xEF), (0xBF, 0xBF), (0xBF, 0xBF)],
   [(0xF0, 0xF0), (0x90, 0x90), (0x80, 0x80), (0x80, 0x80)]]\<close>
  by eval

text \<open>All codepoints give the table of well-formed byte sequences
  \<^cite>\<open>\<open>Sect.~4\<close> in "rfc3629-utf8"\<close>:\<close>

lemma \<open>byte_seqs (0, 0x10FFFF) =
  [[(0x00, 0x7F)],
   [(0xC2, 0xDF), (0x80, 0xBF)],
   [(0xE0, 0xE0), (0xA0, 0xBF), (0x80, 0xBF)],
   [(0xE1, 0xEC), (0x80, 0xBF), (0x80, 0xBF)],
   [(0xED, 0xED), (0x80, 0x9F), (0x80, 0xBF)],
   [(0xEE, 0xEF), (0x80, 0xBF), (0x80, 0xBF)],
   [(0xF0, 0xF0), (0x90, 0xBF), (0x80, 0xBF), (0x80, 0xBF)],
   [(0xF1, 0xF3), (0x80, 0xBF), (0x80, 0xBF), (0x80, 0xBF)],
   [(0xF4, 0xF4), (0x80, 0x8F), (0x80, 0xBF), (0x80, 0xBF)]]\<close>
  by eval

subsection \<open>A lexer on the bytes of UTF-8\<close>

datatype utok = Greek | Arrow | Word

text \<open>The rules are written on codepoints; the comment rule's complement means every
  codepoint but the newline:\<close>

lexer (utf8) u8 :: \<open>utok\<close>
  rules
    \<open>[\<alpha>-\<omega>]+\<close> \<Rightarrow> Greek
  | \<open>[\<rightarrow>\<Rightarrow>]+\<close> \<Rightarrow> Arrow
  | \<open>[a-z]+\<close> \<Rightarrow> Word
  | \<open>[ \n]+ | "#" [^\n]*\<close> \<Rightarrow> skip

text \<open>The kind, line, column, offset and length of each token, the length of the
  consumed input and of the residue, on input given as byte values:\<close>

definition u8_run :: \<open>nat list \<Rightarrow> (utok \<times> nat \<times> nat \<times> nat \<times> nat) list \<times> nat \<times> nat\<close> where
  \<open>u8_run s = (case u8_lex (map char_of s) of (l, r, _) \<Rightarrow>
    (map (\<lambda>t. (tok t, s_line (span t), s_col (span t), s_off (span t), s_len (span t)))
      (toks l), length (source l), length r))\<close>

text \<open>\<open>\<alpha>\<beta> \<rightarrow>\<Rightarrow>\<close>, a newline and \<open>x\<close>: columns count codepoints, offsets and lengths
  count bytes:\<close>

lexer_check
  \<open>u8_run [0xCE, 0xB1, 0xCE, 0xB2, 0x20, 0xE2, 0x86, 0x92, 0xE2, 0x87, 0x92, 0x0A, 0x78] =
    ([(Greek, 0, 0, 0, 4), (Arrow, 0, 3, 5, 6), (Word, 1, 0, 12, 1)], 13, 0)\<close>

text \<open>The text of a token is its bytes, and a comment holding \<open>\<alpha>\<close> is trivia:\<close>

lexer_check
  \<open>map (s_txt \<circ> span) (toks (fst (u8_lex (map char_of [0xCE, 0xB1, 0x20, 0x61 :: nat])))) =
    [map char_of [0xCE, 0xB1 :: nat], [CHR 0x61]]\<close>
  \<open>u8_run [0x61, 0x20, 0x23, 0xCE, 0xB1, 0x0A, 0x62] =
    ([(Word, 0, 0, 0, 1), (Word, 1, 0, 6, 1)], 7, 0)\<close>

text \<open>Malformed input stops the lexer in front of the bad sequence: the overlong
  \<open>C0 80\<close>, a lone continuation byte and \<open>ED A0 80\<close>, the encoding of the surrogate
  \<open>0xD800\<close>:\<close>

lexer_check
  \<open>u8_run [0x61, 0x20, 0xC0, 0x80] = ([(Word, 0, 0, 0, 1)], 2, 2)\<close>
  \<open>u8_run [0x61, 0x80, 0x62] = ([(Word, 0, 0, 0, 1)], 1, 2)\<close>
  \<open>u8_run [0xCE, 0xB1, 0xED, 0xA0, 0x80] = ([(Greek, 0, 0, 0, 2)], 2, 3)\<close>
  \<open>\<not> u8_lex.ok (map char_of [0x61, 0x80 :: nat])\<close>

text \<open>A truncated sequence stops the comment rule too, which then matches up to it:\<close>

lexer_check
  \<open>u8_run [0x61, 0x23, 0xCE] = ([(Word, 0, 0, 0, 1)], 2, 1)\<close>

subsection \<open>The stress lexer on UTF-8\<close>

text \<open>The lexer of \<^theory>\<open>TIGER_Lexer_Tests.Stress_Lexer_Tests\<close> on the bytes of UTF-8:\<close>

lexer (utf8) stress8 :: \<open>stok\<close>
  modes \<open>smode\<close>
  start \<open>Tok Outer AfterOp\<close>
  exclusive Cmt
  final \<open>Tok Outer AfterOp\<close> \<open>Tok Outer AfterVal\<close>
  after stress_after
  where
    letter = \<open>[a-zA-Z_]\<close> | digit = \<open>[0-9]\<close> | idchar = \<open>letter | digit | [']\<close>
  | strchar = \<open>[^"$\\\n] | "\\" [^\n]\<close>
  rules
    "let" \<Rightarrow> KwLet | "in" \<Rightarrow> KwIn | "fun" \<Rightarrow> KwFun
  | \<open>letter idchar*\<close> \<Rightarrow> Ident
  | \<open>digit+\<close> \<Rightarrow> Num
  | \<open>digit+ letter+\<close> \<Rightarrow> error
  | <Tok _ AfterOp> (
      \<open>"-" digit+\<close> \<Rightarrow> NegNum
    | \<open>"-" digit+ letter+\<close> \<Rightarrow> error
  )
  | \<open>[-+*/<>=]+\<close> \<Rightarrow> Op
  | "(" \<Rightarrow> LParen | ")" \<Rightarrow> RParen
  | "{" \<Rightarrow> LBrace, push \<open>Tok Outer AfterOp\<close>
  | <Tok Outer _> "}" \<Rightarrow> RBrace, pop
  | \<open>"\"" strchar* "\""\<close> \<Rightarrow> Str
  | \<open>"\"" strchar* "${"\<close> \<Rightarrow> StrStart, push \<open>Tok Hole AfterOp\<close>
  | <Tok Hole _> (
      \<open>"}" strchar* "${"\<close> \<Rightarrow> StrMid, begin \<open>Tok Hole AfterOp\<close>
    | \<open>"}" strchar* "\""\<close> \<Rightarrow> StrEnd, pop
  )
  | \<open>[ \n]+\<close> \<Rightarrow> skip
  | "(*" \<Rightarrow> skip, push Cmt
  | <Cmt> (
      "(*" \<Rightarrow> skip, push Cmt
    | "*)" \<Rightarrow> skip, pop
    | \<open>[^*(]+ | [*(]\<close> \<Rightarrow> skip
  )

text \<open>Size and cost (PIDE, 2026-11-14, beside another proof job): five tables, as on
  codepoints. A token table has 58 byte intervals, 43 minterms and 33 to 48 states, the
  comment table 14 states, against 45 intervals, 22 or 23 minterms and 26 to 34 states
  on codepoints: the encodings of the non-ASCII complements in \<open>strchar\<close> and the
  comment rule add the states of the multi-byte sequences. The command takes about 23 s,
  3 to 6 s per table, about five times the codepoint lexer.\<close>

text \<open>Strings and comments take any codepoint, and columns count codepoints:\<close>

lexer_check
  \<open>map tok (toks (fst (stress8_lex (map char_of
    [0x78, 0x20, 0x28, 0x2A, 0xCE, 0xB1, 0x2A, 0x29, 0x20, 0x22, 0xE2, 0x86, 0x92, 0x22 :: nat]))))
    = [Ident, Str]\<close>
  \<open>map (s_col \<circ> span) (toks (fst (stress8_lex (map char_of
    [0x22, 0xCE, 0xB1, 0xCE, 0xB2, 0x22, 0x20, 0x79 :: nat])))) = [0, 5]\<close>
  \<open>stress8_lex.ok (map char_of [0x22, 0xF0, 0x9F, 0x98, 0x80, 0x24, 0x7B, 0x78, 0x7D, 0x22 :: nat])\<close>

subsection \<open>Errors\<close>

text \<open>A newline class that leaves ASCII is an error:\<close>

ML_command \<open>
  lexer_fails \<^context>
    "(utf8) ls :: \<open>utok\<close> newline nl where nl = \<open>[\\n\\u{2028}]\<close> rules \"x\" \<Rightarrow> Word"
    "leaves ASCII"
\<close>

end
