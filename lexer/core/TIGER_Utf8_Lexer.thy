(* Author: Basil Fürer *)

theory TIGER_Utf8_Lexer
  imports TIGER_Codepoints TIGER_UTF8.TIGER_UTF8
begin

section \<open>UTF-8 in one pass\<close>

text \<open>A spec on codepoints is read on the bytes of their UTF-8 encoding by \<open>utf8_spec\<close>,
  which replaces each class of a rule by the byte sequences of its valid codepoints
  (\<^const>\<open>utf8_ranges\<close>) and applies the action to the decoded lexeme. The DFA of the byte
  spec then decodes and lexes in one pass.

  The language of the transformed regex is the encoding of the valid words of the
  original one. Since the encoding is prefix-free, the prefixes of an encoded input that
  a byte rule matches are the encodings of the prefixes that the codepoint rule matches,
  in the same order of length, so longest match and rule priority carry over. On a valid
  input, lexing the bytes is lexing the codepoints followed by the encoding of the
  lexed source (\<open>encode_lexed\<close>), provided a newline is an ASCII character (a byte can only
  end a line if it is one codepoint). Columns count the bytes that start a codepoint, and
  offsets count bytes.

  On any input, the bytes the lexer consumes are valid UTF-8 (each lexeme is in the
  language of a transformed regex), and they lex as they do on their own.\<close>

subsection \<open>The regex transform\<close>

text \<open>A sequence of byte intervals as a regex, and a list of regexes as their sum:\<close>

fun seq_rexp :: \<open>(char \<times> char) list \<Rightarrow> char cls rexp\<close> where
  \<open>seq_rexp [] = One\<close>
| \<open>seq_rexp [r] = Atom [r]\<close>
| \<open>seq_rexp (r # rs) = Times (Atom [r]) (seq_rexp rs)\<close>

fun plus_list :: \<open>'a rexp list \<Rightarrow> 'a rexp\<close> where
  \<open>plus_list [] = Zero\<close>
| \<open>plus_list [r] = r\<close>
| \<open>plus_list (r # rs) = Plus r (plus_list rs)\<close>

definition utf8_atom :: \<open>nat cls \<Rightarrow> char cls rexp\<close> where
  \<open>utf8_atom p = plus_list (map seq_rexp (concat (map utf8_ranges p)))\<close>

text \<open>The transform replaces each atom, a class of codepoints, by the byte sequences of its
  valid codepoints:\<close>

primrec utf8_rexp :: \<open>nat cls rexp \<Rightarrow> char cls rexp\<close> where
  \<open>utf8_rexp Zero = Zero\<close>
| \<open>utf8_rexp One = One\<close>
| \<open>utf8_rexp (Atom p) = utf8_atom p\<close>
| \<open>utf8_rexp (Plus r s) = Plus (utf8_rexp r) (utf8_rexp s)\<close>
| \<open>utf8_rexp (Times r s) = Times (utf8_rexp r) (utf8_rexp s)\<close>
| \<open>utf8_rexp (Star r) = Star (utf8_rexp r)\<close>

abbreviation valid_cps :: \<open>nat list set\<close> where
  \<open>valid_cps \<equiv> lists {c. is_valid_cp c}\<close>

lemma lang_seq_rexp: \<open>symbolic.lang in_cls (seq_rexp rs) = {bs. in_ranges bs rs}\<close>
  by (induct rs rule: seq_rexp.induct)
    (auto simp: symbolic.lang.simps in_ranges_def conc_def list_all2_Cons2,
      metis append_Cons append_Nil)

lemma lang_plus_list: \<open>symbolic.lang sem (plus_list rs) = (\<Union>r \<in> set rs. symbolic.lang sem r)\<close>
  by (induct rs rule: plus_list.induct) (auto simp: symbolic.lang.simps)

lemma lang_utf8_atom:
  \<open>symbolic.lang in_cls (utf8_atom p) = utf8_encode ` ({[c] | c. in_cls p c} \<inter> valid_cps)\<close>
proof -
  have \<open>symbolic.lang in_cls (utf8_atom p) = (\<Union>(a, b) \<in> set p. seqs (utf8_ranges (a, b)))\<close>
    by (auto simp: utf8_atom_def lang_plus_list lang_seq_rexp seqs_def)
  also have \<open>\<dots> = {utf8_encode_cp c | c. in_cls p c \<and> is_valid_cp c}\<close>
    by (auto simp: seqs_utf8_ranges in_cls_iff) (force simp: seqs_utf8_ranges)+
  also have \<open>\<dots> = utf8_encode ` ({[c] | c. in_cls p c} \<inter> valid_cps)\<close>
  proof (intro set_eqI iffI)
    fix x
    assume \<open>x \<in> {utf8_encode_cp c | c. in_cls p c \<and> is_valid_cp c}\<close>
    then obtain c where \<open>x = utf8_encode [c]\<close> \<open>[c] \<in> {[c] | c. in_cls p c} \<inter> valid_cps\<close>
      by auto
    then show \<open>x \<in> utf8_encode ` ({[c] | c. in_cls p c} \<inter> valid_cps)\<close>
      by blast
  next
    fix x
    assume \<open>x \<in> utf8_encode ` ({[c] | c. in_cls p c} \<inter> valid_cps)\<close>
    then show \<open>x \<in> {utf8_encode_cp c | c. in_cls p c \<and> is_valid_cp c}\<close>
      by auto
  qed
  finally show ?thesis .
qed

lemma conc_Int_lists: \<open>(A @@ B) \<inter> lists V = (A \<inter> lists V) @@ (B \<inter> lists V)\<close>
  unfolding conc_def by (auto simp: in_lists_conv_set) blast

lemma star_Int_lists: \<open>star A \<inter> lists V = star (A \<inter> lists V)\<close>
proof
  show \<open>star A \<inter> lists V \<subseteq> star (A \<inter> lists V)\<close>
  proof
    fix w
    assume \<open>w \<in> star A \<inter> lists V\<close>
    then have \<open>w \<in> star A\<close> \<open>w \<in> lists V\<close>
      by simp_all
    then show \<open>w \<in> star (A \<inter> lists V)\<close>
      by (induct w rule: star_induct) (auto intro: star_if_lang)
  qed
next
  show \<open>star (A \<inter> lists V) \<subseteq> star A \<inter> lists V\<close>
  proof
    fix w
    assume \<open>w \<in> star (A \<inter> lists V)\<close>
    then show \<open>w \<in> star A \<inter> lists V\<close>
      by (induct w rule: star_induct) auto
  qed
qed

lemma image_utf8_encode_conc: \<open>utf8_encode ` (A @@ B) = utf8_encode ` A @@ utf8_encode ` B\<close>
proof
  show \<open>utf8_encode ` (A @@ B) \<subseteq> utf8_encode ` A @@ utf8_encode ` B\<close>
    by (auto simp: conc_def) (blast intro: imageI)
next
  show \<open>utf8_encode ` A @@ utf8_encode ` B \<subseteq> utf8_encode ` (A @@ B)\<close>
  proof
    fix w
    assume \<open>w \<in> utf8_encode ` A @@ utf8_encode ` B\<close>
    then obtain u v where \<open>u \<in> A\<close> \<open>v \<in> B\<close> \<open>w = utf8_encode (u @ v)\<close>
      by (auto simp: conc_def)
    then show \<open>w \<in> utf8_encode ` (A @@ B)\<close>
      by (auto intro!: image_eqI[where x = \<open>u @ v\<close>])
  qed
qed

lemma image_utf8_encode_star: \<open>utf8_encode ` star A = star (utf8_encode ` A)\<close>
proof
  show \<open>utf8_encode ` star A \<subseteq> star (utf8_encode ` A)\<close>
  proof
    fix w
    assume \<open>w \<in> utf8_encode ` star A\<close>
    then obtain u where \<open>u \<in> star A\<close> \<open>w = utf8_encode u\<close>
      by blast
    then show \<open>w \<in> star (utf8_encode ` A)\<close>
      by (induct u arbitrary: w rule: star_induct) auto
  qed
next
  show \<open>star (utf8_encode ` A) \<subseteq> utf8_encode ` star A\<close>
  proof
    fix w
    assume \<open>w \<in> star (utf8_encode ` A)\<close>
    then show \<open>w \<in> utf8_encode ` star A\<close>
    proof (induct w rule: star_induct)
      case Nil
      have \<open>[] = utf8_encode []\<close>
        by simp
      then show ?case
        by blast
    next
      case (append u v)
      then obtain u0 v0 where \<open>u0 \<in> A\<close> \<open>v0 \<in> star A\<close> \<open>u = utf8_encode u0\<close>
        \<open>v = utf8_encode v0\<close>
        by blast
      moreover from \<open>u0 \<in> A\<close> \<open>v0 \<in> star A\<close> have \<open>u0 @ v0 \<in> star A\<close>
        by (blast intro: append_in_starI star_if_lang)
      ultimately show ?case
        by (auto intro!: image_eqI[where x = \<open>u0 @ v0\<close>])
    qed
  qed
qed

text \<open>The language of the transform is the encoding of the valid words of the language:\<close>

theorem lang_utf8_rexp:
  \<open>symbolic.lang in_cls (utf8_rexp r) = utf8_encode ` (symbolic.lang in_cls r \<inter> valid_cps)\<close>
  by (induct r) (simp_all add: symbolic.lang.simps lang_utf8_atom image_Un Int_Un_distrib2
      conc_Int_lists star_Int_lists image_utf8_encode_conc image_utf8_encode_star)

subsection \<open>The spec on bytes\<close>

definition utf8_rule :: \<open>('k, nat cls, nat, 'm) rule \<Rightarrow> ('k, char cls, char, 'm) rule\<close> where
  \<open>utf8_rule \<rho> = \<lparr>match = utf8_rexp (match \<rho>), act = \<lambda>u. act \<rho> (utf8_decode u)\<rparr>\<close>

definition utf8_spec :: \<open>('k, nat cls, nat, 'm) lexer_spec \<Rightarrow> ('k, char cls, char, 'm) lexer_spec\<close>
where
  \<open>utf8_spec sp m = map utf8_rule (sp m)\<close>

text \<open>The lexed source on codepoints, encoded: the text and trivia are encoded, and each
  offset grows by the bytes the encoding adds before it. \<open>d\<close> is the number of bytes added
  before the source:\<close>

definition extra_bytes :: \<open>nat list \<Rightarrow> nat\<close> where
  \<open>extra_bytes w = length (utf8_encode w) - length w\<close>

definition encode_span :: \<open>nat \<Rightarrow> nat span \<Rightarrow> char span\<close> where
  \<open>encode_span d sp = \<lparr>s_line = s_line sp, s_col = s_col sp, s_off = s_off sp + d,
    s_len = length (utf8_encode (s_txt sp)), s_txt = utf8_encode (s_txt sp)\<rparr>\<close>

fun encode_toks :: \<open>nat \<Rightarrow> ('k, nat) lex_token list \<Rightarrow> ('k, char) lex_token list\<close> where
  \<open>encode_toks d [] = []\<close>
| \<open>encode_toks d (t # ts) =
    \<lparr>tok = tok t, span = encode_span d (span t), trivia = utf8_encode (trivia t)\<rparr> #
    encode_toks (d + extra_bytes (s_txt (span t)) + extra_bytes (trivia t)) ts\<close>

fun encode_lexed_from :: \<open>nat \<Rightarrow> ('k, nat) lexed \<Rightarrow> ('k, char) lexed\<close> where
  \<open>encode_lexed_from d (Lexed h ts) = Lexed (utf8_encode h) (encode_toks (d + extra_bytes h) ts)\<close>

abbreviation encode_lexed :: \<open>('k, nat) lexed \<Rightarrow> ('k, char) lexed\<close> where
  \<open>encode_lexed \<equiv> encode_lexed_from 0\<close>

subsection \<open>Simulation\<close>

text \<open>A byte position and a codepoint position agree up to \<open>d\<close> added bytes:\<close>

definition pos_shift :: \<open>nat \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> bool\<close> where
  \<open>pos_shift d q\<^sub>b q \<longleftrightarrow> line q\<^sub>b = line q \<and> col q\<^sub>b = col q \<and> off q\<^sub>b = off q + d\<close>

text \<open>One-byte encodings of ASCII codepoints:\<close>

lemma utf8_encode_cp_ascii: \<open>c < 0x80 \<Longrightarrow> utf8_encode_cp c = [char_of c]\<close>
  by (simp add: utf8_encode_cp_def cp_len_def bytes_of_def lead_def)

text \<open>Every byte of the encoding of a non-ASCII codepoint is at least \<open>0x80\<close>:\<close>

lemma utf8_encode_cp_high:
  assumes \<open>is_valid_cp c\<close> \<open>0x80 \<le> c\<close> \<open>b \<in> set (utf8_encode_cp c)\<close>
  shows \<open>0x80 \<le> (of_char b :: nat)\<close>
proof -
  from assms(1) have \<open>c \<le> 0x10FFFF\<close>
    by (simp add: is_valid_cp_def)
  then obtain h bs where enc: \<open>utf8_encode_cp c = h # bs\<close> \<open>lead_len h = cp_len c\<close>
    \<open>\<forall>x \<in> set bs. is_cont x\<close>
    by (rule utf8_encode_cp_Cons)
  from assms(2) have \<open>2 \<le> cp_len c\<close>
    by (simp add: cp_len_def)
  with enc(2) have \<open>0xC0 \<le> (of_char h :: nat)\<close>
    by (auto simp: lead_len_def split: if_splits)
  with assms(3) enc show ?thesis
    by (auto simp: is_cont_def)
qed

text \<open>A run of continuation bytes, none of them a newline, moves only the offset:\<close>

lemma advance_list_cont:
  assumes \<open>\<And>b. b \<in> set bs \<Longrightarrow> is_cont b \<and> \<not> is_newline (of_char b)\<close>
  shows \<open>advance_list (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) bs q =
    q\<lparr>off := off q + length bs\<rparr>\<close>
  using assms by (induction bs arbitrary: q) (auto simp: advance_def)

text \<open>The encoding of one valid codepoint advances the columns by one and the offset by
  its length:\<close>

lemma advance_list_utf8_cp:
  assumes \<open>\<forall>c. is_newline c \<longrightarrow> c < 0x80\<close> \<open>is_valid_cp c\<close> \<open>pos_shift d q\<^sub>b q\<close>
  shows \<open>pos_shift (d + (length (utf8_encode_cp c) - 1))
    (advance_list (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) (utf8_encode_cp c) q\<^sub>b)
    (advance is_newline (\<lambda>_. True) c q)\<close>
proof (cases \<open>c < 0x80\<close>)
  case True
  moreover have \<open>(of_char (char_of c) :: nat) = c\<close> if \<open>c < 0x80\<close> for c
    using that by simp
  ultimately show ?thesis
    using assms(3) by (auto simp: utf8_encode_cp_ascii advance_def pos_shift_def is_cont_def)
next
  case False
  from assms(2) have \<open>c \<le> 0x10FFFF\<close>
    by (simp add: is_valid_cp_def)
  then obtain h bs where enc: \<open>utf8_encode_cp c = h # bs\<close> \<open>\<not> is_cont h\<close>
    \<open>\<forall>x \<in> set bs. is_cont x\<close>
    by (rule utf8_encode_cp_Cons)
  have high: \<open>0x80 \<le> (of_char b :: nat)\<close> if \<open>b \<in> set (utf8_encode_cp c)\<close> for b
    using utf8_encode_cp_high[OF assms(2) _ that] False by simp
  have nl: \<open>\<not> is_newline (of_char b)\<close> if \<open>b \<in> set (utf8_encode_cp c)\<close> for b
    using assms(1) high[OF that] by force
  have \<open>\<not> is_newline c\<close>
    using assms(1) False by force
  moreover have \<open>\<not> is_newline (of_char h)\<close>
    using nl enc(1) by simp
  moreover have \<open>\<forall>b \<in> set bs. is_cont b \<and> \<not> is_newline (of_char b)\<close>
    using nl enc by simp
  ultimately show ?thesis
    using assms(3) enc(3) unfolding enc(1)
    by (simp add: advance_list_cont advance_def pos_shift_def enc(2))
qed

text \<open>The byte string is at least as long as the codepoint list:\<close>

lemma length_utf8_encode_ge: \<open>w \<in> valid_cps \<Longrightarrow> length w \<le> length (utf8_encode w)\<close>
proof (induction w)
  case (Cons c w)
  then have \<open>c \<le> 0x10FFFF\<close>
    by (simp add: is_valid_cp_def)
  then have \<open>0 < length (utf8_encode_cp c)\<close>
    by simp
  moreover have \<open>length w \<le> length (utf8_encode w)\<close>
    using Cons by simp
  ultimately show ?case
    by (simp only: utf8_encode_simps length_Cons length_append)
qed simp

lemma extra_bytes_Cons:
  assumes \<open>is_valid_cp c\<close> \<open>w \<in> valid_cps\<close>
  shows \<open>extra_bytes (c # w) = (length (utf8_encode_cp c) - 1) + extra_bytes w\<close>
proof -
  from assms(1) have \<open>c \<le> 0x10FFFF\<close>
    by (simp add: is_valid_cp_def)
  then have \<open>utf8_encode_cp c \<noteq> []\<close>
    by simp
  then show ?thesis
    using length_utf8_encode_ge[OF assms(2)]
    by (simp add: extra_bytes_def length_greater_0_conv Suc_le_eq)
qed

text \<open>Hence the byte and codepoint positions of a valid text stay in step:\<close>

lemma advance_list_utf8:
  assumes \<open>\<forall>c. is_newline c \<longrightarrow> c < 0x80\<close> \<open>w \<in> valid_cps\<close> \<open>pos_shift d q\<^sub>b q\<close>
  shows \<open>pos_shift (d + extra_bytes w)
    (advance_list (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) (utf8_encode w) q\<^sub>b)
    (advance_list is_newline (\<lambda>_. True) w q)\<close>
proof -
  have \<open>w \<in> valid_cps \<Longrightarrow> pos_shift d q\<^sub>b q \<Longrightarrow> pos_shift (d + extra_bytes w)
    (advance_list (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) (utf8_encode w) q\<^sub>b)
    (advance_list is_newline (\<lambda>_. True) w q)\<close> for w d q\<^sub>b q
  proof (induction w arbitrary: d q\<^sub>b q)
    case Nil
    then show ?case
      by (simp add: extra_bytes_def)
  next
    case (Cons c w)
    then have c: \<open>is_valid_cp c\<close> and w: \<open>w \<in> valid_cps\<close>
      by simp_all
    from advance_list_utf8_cp[OF assms(1) c \<open>pos_shift d q\<^sub>b q\<close>]
    have \<open>pos_shift (d + (length (utf8_encode_cp c) - 1))
      (advance_list (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) (utf8_encode_cp c) q\<^sub>b)
      (advance is_newline (\<lambda>_. True) c q)\<close> .
    from Cons.IH[OF w this] show ?case
      by (simp add: extra_bytes_Cons[OF c w] add.assoc)
  qed
  from this[OF assms(2,3)] show ?thesis .
qed

text \<open>A valid word is empty iff its encoding is:\<close>

lemma utf8_encode_eq_Nil_valid:
  \<open>\<forall>c \<in> set w. is_valid_cp c \<Longrightarrow> utf8_encode w = [] \<longleftrightarrow> w = []\<close>
  by (cases w) (auto simp: utf8_encode_simps is_valid_cp_le)

lemma match_rule_utf8_rule:
  \<open>symbolic.match_rule in_cls (utf8_rule \<rho>) p \<longleftrightarrow>
    (\<exists>p'. p' \<in> valid_cps \<and> symbolic.match_rule in_cls \<rho> p' \<and> p = utf8_encode p')\<close>
  by (auto simp: symbolic.match_rule.simps utf8_rule_def lang_utf8_rexp
      dest: utf8_encode_eq_Nil_valid utf8_encode_eq_Nil_valid[symmetric])

text \<open>A match of a byte rule on a prefix of valid bytes is the encoding of a match on a
  prefix of the codepoints:\<close>

lemma match_rule_prefix_utf8:
  assumes \<open>cs \<in> valid_cps\<close> \<open>utf8_encode cs = P @ U\<close>
    \<open>symbolic.match_rule in_cls (utf8_rule \<rho>) P\<close>
  obtains q v where \<open>cs = q @ v\<close> \<open>P = utf8_encode q\<close> \<open>q \<in> valid_cps\<close>
    \<open>symbolic.match_rule in_cls \<rho> q\<close>
proof -
  from assms(3) obtain q where q: \<open>q \<in> valid_cps\<close> \<open>symbolic.match_rule in_cls \<rho> q\<close>
    \<open>P = utf8_encode q\<close>
    unfolding match_rule_utf8_rule by blast
  from assms(1,2) q have \<open>\<forall>c \<in> set (q @ cs). c \<le> 0x10FFFF\<close> \<open>utf8_encode q @ U = utf8_encode cs\<close>
    by (auto simp: is_valid_cp_le)
  then obtain v where \<open>cs = q @ v\<close>
    by (rule utf8_encode_prefix)
  with q that show thesis
    by blast
qed

text \<open>Of two prefixes of valid codepoints, the one with fewer codepoints has fewer bytes:\<close>

lemma length_utf8_encode_prefix_less:
  assumes \<open>cs \<in> valid_cps\<close> \<open>cs = p @ u\<close> \<open>cs = q @ v\<close>
  shows \<open>length p < length q \<longleftrightarrow> length (utf8_encode p) < length (utf8_encode q)\<close>
proof -
  from assms(2,3) obtain zs where cmp: \<open>q = p @ zs \<or> p = q @ zs\<close>
    using append_eq_append_conv2[of p u q v] by auto
  then show ?thesis
  proof
    assume q: \<open>q = p @ zs\<close>
    with assms(1,3) have \<open>\<forall>c \<in> set zs. is_valid_cp c\<close>
      by auto
    then show ?thesis
      by (auto simp: q utf8_encode_simps utf8_encode_eq_Nil_valid)
  next
    assume \<open>p = q @ zs\<close>
    then show ?thesis
      by (simp add: utf8_encode_simps)
  qed
qed

lemma first_token_utf8:
  assumes \<open>cs \<in> valid_cps\<close>
  shows \<open>symbolic.first_token in_cls (map utf8_rule rs) i p (utf8_encode cs) \<longleftrightarrow>
    (\<exists>p'. symbolic.first_token in_cls rs i p' cs \<and> p = utf8_encode p')\<close>
proof
  assume \<open>symbolic.first_token in_cls (map utf8_rule rs) i p (utf8_encode cs)\<close>
  then obtain mp: \<open>symbolic.max_pref in_cls (map utf8_rule rs) p (utf8_encode cs)\<close>
    and i: \<open>i < length rs\<close> and m: \<open>symbolic.match_rule in_cls (utf8_rule (rs ! i)) p\<close>
    and first: \<open>\<And>j. j < i \<Longrightarrow> \<not> symbolic.match_rule in_cls (utf8_rule (rs ! j)) p\<close>
    by (auto simp: symbolic.first_token.simps)
  from mp obtain u where enc: \<open>utf8_encode cs = p @ u\<close>
    by (auto simp: symbolic.max_pref.simps)
  have long: \<open>\<And>P U \<rho>'. \<lbrakk> utf8_encode cs = P @ U; length p < length P;
      \<rho>' \<in> set (map utf8_rule rs) \<rbrakk> \<Longrightarrow> \<not> symbolic.match_rule in_cls \<rho>' P\<close>
    by (rule symbolic.max_pref_longest[OF mp])
  from assms enc m obtain p' v where p': \<open>cs = p' @ v\<close> \<open>p = utf8_encode p'\<close>
    \<open>p' \<in> valid_cps\<close> \<open>symbolic.match_rule in_cls (rs ! i) p'\<close>
    by (rule match_rule_prefix_utf8)
  have \<open>symbolic.max_pref in_cls rs p' cs\<close>
  proof (rule symbolic.max_pref.intros[OF \<open>cs = p' @ v\<close> _ \<open>symbolic.match_rule in_cls (rs ! i) p'\<close>])
    show \<open>rs ! i \<in> set rs\<close>
      using i by simp
    fix q w \<rho>'
    assume qw: \<open>cs = q @ w\<close> \<open>length p' < length q\<close> and \<rho>': \<open>\<rho>' \<in> set rs\<close>
    from qw assms have \<open>q \<in> valid_cps\<close>
      by auto
    with qw \<rho>' p' show \<open>\<not> symbolic.match_rule in_cls \<rho>' q\<close>
      using long[of \<open>utf8_encode q\<close> \<open>utf8_encode w\<close> \<open>utf8_rule \<rho>'\<close>]
        length_utf8_encode_prefix_less[OF assms \<open>cs = p' @ v\<close> \<open>cs = q @ w\<close>]
      by (auto simp: match_rule_utf8_rule utf8_encode_simps)
  qed
  moreover have \<open>\<And>j. j < i \<Longrightarrow> \<not> symbolic.match_rule in_cls (rs ! j) p'\<close>
    using first i p' by (auto simp: match_rule_utf8_rule intro!: bexI[of _ p'])
  ultimately show \<open>\<exists>p'. symbolic.first_token in_cls rs i p' cs \<and> p = utf8_encode p'\<close>
    using i p' by (auto simp: symbolic.first_token.simps)
next
  assume \<open>\<exists>p'. symbolic.first_token in_cls rs i p' cs \<and> p = utf8_encode p'\<close>
  then obtain p' where ft: \<open>symbolic.first_token in_cls rs i p' cs\<close> and p: \<open>p = utf8_encode p'\<close>
    by blast
  from ft obtain u \<rho> where mp: \<open>symbolic.max_pref in_cls rs p' cs\<close> \<open>cs = p' @ u\<close>
    \<open>i < length rs\<close> \<open>symbolic.match_rule in_cls (rs ! i) p'\<close>
    and first: \<open>\<And>j. j < i \<Longrightarrow> \<not> symbolic.match_rule in_cls (rs ! j) p'\<close>
    by (auto simp: symbolic.first_token.simps symbolic.max_pref.simps)
  from \<open>cs = p' @ u\<close> assms have valid: \<open>p' \<in> valid_cps\<close> \<open>u \<in> valid_cps\<close>
    by auto
  have \<open>symbolic.max_pref in_cls (map utf8_rule rs) (utf8_encode p') (utf8_encode cs)\<close>
  proof (rule symbolic.max_pref.intros[where u = \<open>utf8_encode u\<close> and \<rho> = \<open>utf8_rule (rs ! i)\<close>])
    show \<open>utf8_encode cs = utf8_encode p' @ utf8_encode u\<close>
      using \<open>cs = p' @ u\<close> by (simp add: utf8_encode_simps)
    show \<open>utf8_rule (rs ! i) \<in> set (map utf8_rule rs)\<close>
      using mp by simp
    show \<open>symbolic.match_rule in_cls (utf8_rule (rs ! i)) (utf8_encode p')\<close>
      using mp valid by (auto simp: match_rule_utf8_rule)
    fix P U \<rho>'
    assume PU: \<open>utf8_encode cs = P @ U\<close> \<open>length (utf8_encode p') < length P\<close>
      \<open>\<rho>' \<in> set (map utf8_rule rs)\<close>
    then obtain \<rho>0 where \<rho>0: \<open>\<rho>0 \<in> set rs\<close> \<open>\<rho>' = utf8_rule \<rho>0\<close>
      by auto
    show \<open>\<not> symbolic.match_rule in_cls \<rho>' P\<close>
    proof
      assume \<open>symbolic.match_rule in_cls \<rho>' P\<close>
      then have \<open>symbolic.match_rule in_cls (utf8_rule \<rho>0) P\<close>
        using \<rho>0(2) by simp
      from match_rule_prefix_utf8[OF assms PU(1) this] obtain q v where qv: \<open>cs = q @ v\<close>
        \<open>P = utf8_encode q\<close> \<open>symbolic.match_rule in_cls \<rho>0 q\<close>
        by blast
      with PU(2) have \<open>length p' < length q\<close>
        using length_utf8_encode_prefix_less[OF assms \<open>cs = p' @ u\<close> \<open>cs = q @ v\<close>] by simp
      with qv(1,3) \<rho>0(1) mp show False
        by (auto simp: symbolic.max_pref.simps)
    qed
  qed
  then show \<open>symbolic.first_token in_cls (map utf8_rule rs) i p (utf8_encode cs)\<close>
    unfolding p
  proof (rule symbolic.first_token.intros)
    show \<open>i < length (map utf8_rule rs)\<close>
      using mp by simp
    show \<open>symbolic.match_rule in_cls (map utf8_rule rs ! i) (utf8_encode p')\<close>
      using mp valid by (auto simp: match_rule_utf8_rule)
    fix j
    assume j: \<open>j < i\<close>
    show \<open>\<not> symbolic.match_rule in_cls (map utf8_rule rs ! j) (utf8_encode p')\<close>
    proof
      assume \<open>symbolic.match_rule in_cls (map utf8_rule rs ! j) (utf8_encode p')\<close>
      with j mp obtain p'' where p'': \<open>p'' \<in> valid_cps\<close> \<open>symbolic.match_rule in_cls (rs ! j) p''\<close>
        \<open>utf8_encode p' = utf8_encode p''\<close>
        by (auto simp: match_rule_utf8_rule)
      from p''(1,3) valid(1) have \<open>p' = p''\<close>
        by (intro utf8_encode_inj) (auto simp: is_valid_cp_le)
      with first[OF j] p''(2) show False
        by simp
    qed
  qed
qed

lemma step_utf8:
  assumes \<open>cs \<in> valid_cps\<close>
  shows \<open>symbolic.step in_cls (utf8_spec sp) st (utf8_encode cs) x \<longleftrightarrow>
    (\<exists>k p st' cs'. symbolic.step in_cls sp st cs (k, p, st', cs') \<and>
      x = (k, utf8_encode p, st', utf8_encode cs'))\<close>
proof (cases x)
  case (fields k P st' s')
  show ?thesis
  proof
    assume \<open>symbolic.step in_cls (utf8_spec sp) st (utf8_encode cs) x\<close>
    with fields obtain m st\<^sub>0 i where st: \<open>st = m # st\<^sub>0\<close>
      and ft: \<open>symbolic.first_token in_cls (map utf8_rule (sp m)) i P (utf8_encode cs)\<close>
      and act: \<open>act (utf8_spec sp m ! i) P (m # st\<^sub>0) = (k, st')\<close> and ne: \<open>st' \<noteq> []\<close>
      and enc: \<open>utf8_encode cs = P @ s'\<close>
      by (auto elim: symbolic.step.cases simp: utf8_spec_def)
    from ft assms obtain p' where ft': \<open>symbolic.first_token in_cls (sp m) i p' cs\<close>
      and P: \<open>P = utf8_encode p'\<close>
      unfolding first_token_utf8[OF assms] by blast
    from symbolic.first_token_prefix[OF ft'] obtain cs' where cs: \<open>cs = p' @ cs'\<close>
      by blast
    with assms enc P have s': \<open>s' = utf8_encode cs'\<close>
      by (simp add: utf8_encode_simps)
    from ft' have \<open>i < length (sp m)\<close>
      by (auto elim: symbolic.first_token.cases)
    from assms cs have \<open>utf8_decode (utf8_encode p') = p'\<close>
      by (intro utf8_decode_encode) (auto simp: is_valid_cp_le)
    with \<open>i < length (sp m)\<close> act P have \<open>act (sp m ! i) p' (m # st\<^sub>0) = (k, st')\<close>
      by (simp add: utf8_spec_def utf8_rule_def)
    with ft' ne cs st have \<open>symbolic.step in_cls sp st cs (k, p', st', cs')\<close>
      by (auto intro: symbolic.step.intros)
    with fields P s' show \<open>\<exists>k p st' cs'. symbolic.step in_cls sp st cs (k, p, st', cs') \<and>
        x = (k, utf8_encode p, st', utf8_encode cs')\<close>
      by blast
  next
    assume \<open>\<exists>k p st' cs'. symbolic.step in_cls sp st cs (k, p, st', cs') \<and>
        x = (k, utf8_encode p, st', utf8_encode cs')\<close>
    with fields obtain p' cs' where \<open>symbolic.step in_cls sp st cs (k, p', st', cs')\<close>
      and \<open>P = utf8_encode p'\<close> \<open>s' = utf8_encode cs'\<close>
      by auto
    then obtain m st\<^sub>0 i where st: \<open>st = m # st\<^sub>0\<close>
      and ft: \<open>symbolic.first_token in_cls (sp m) i p' cs\<close>
      and act: \<open>act (sp m ! i) p' (m # st\<^sub>0) = (k, st')\<close> and ne: \<open>st' \<noteq> []\<close>
      and cs: \<open>cs = p' @ cs'\<close>
      by (auto elim: symbolic.step.cases)
    from ft have i: \<open>i < length (sp m)\<close>
      by (auto elim: symbolic.first_token.cases)
    from ft have \<open>symbolic.first_token in_cls (utf8_spec sp m) i (utf8_encode p') (utf8_encode cs)\<close>
      unfolding utf8_spec_def first_token_utf8[OF assms] by blast
    moreover from assms cs have \<open>utf8_decode (utf8_encode p') = p'\<close>
      by (intro utf8_decode_encode) (auto simp: is_valid_cp_le)
    with act i have
        \<open>act (utf8_spec sp m ! i) (utf8_encode p') (m # st\<^sub>0) = (k, st')\<close>
      by (simp add: utf8_spec_def utf8_rule_def)
    ultimately show \<open>symbolic.step in_cls (utf8_spec sp) st (utf8_encode cs) x\<close>
      using ne st cs \<open>P = utf8_encode p'\<close> \<open>s' = utf8_encode cs'\<close> fields
      by (auto intro: symbolic.step.intros simp: utf8_encode_simps)
  qed
qed

text \<open>A step splits its input, the encoding adds bytes word by word, and a span moves with
  the position:\<close>

lemma step_split: \<open>symbolic.step in_cls sp st cs (k, p, st', cs') \<Longrightarrow> cs = p @ cs'\<close>
  by (auto elim: symbolic.step.cases)

lemma extra_bytes_append:
  assumes \<open>u \<in> valid_cps\<close> \<open>v \<in> valid_cps\<close>
  shows \<open>extra_bytes (u @ v) = extra_bytes u + extra_bytes v\<close>
  using length_utf8_encode_ge[OF \<open>u \<in> valid_cps\<close>] length_utf8_encode_ge[OF \<open>v \<in> valid_cps\<close>]
  by (simp add: extra_bytes_def)

text \<open>From a run on the bytes of valid UTF-8 to the run on its codepoints:\<close>

lemma lexes_utf8_decode:
  assumes nl: \<open>\<forall>c. is_newline c \<longrightarrow> c < 0x80\<close>
    and lx: \<open>symbolic.lexes in_cls (utf8_spec sp) (\<lambda>b. is_newline (of_char b))
      (\<lambda>b. \<not> is_cont b) st q\<^sub>b s l r st\<^sub>f\<close>
  shows \<open>s = utf8_encode cs \<Longrightarrow> cs \<in> valid_cps \<Longrightarrow> pos_shift d q\<^sub>b q \<Longrightarrow>
    \<exists>l' r'. symbolic.lexes in_cls sp is_newline (\<lambda>_. True) st q cs l' r' st\<^sub>f \<and>
      l = encode_lexed_from d l' \<and> r = utf8_encode r'\<close>
  using lx
proof (induction arbitrary: cs d q rule: symbolic.lexes.induct[of in_cls, consumes 1,
    case_names lexes_stop lexes_token lexes_trivia])
  case (lexes_stop st s q\<^sub>b)
  have \<open>\<not> symbolic.step in_cls sp st cs x\<close> for x
  proof
    assume \<open>symbolic.step in_cls sp st cs x\<close>
    moreover obtain k p st' cs' where \<open>x = (k, p, st', cs')\<close>
      by (cases x) auto
    ultimately have
      \<open>symbolic.step in_cls (utf8_spec sp) st s (k, utf8_encode p, st', utf8_encode cs')\<close>
      using step_utf8[OF \<open>cs \<in> valid_cps\<close>] \<open>s = utf8_encode cs\<close> by blast
    with lexes_stop.hyps show False
      by blast
  qed
  then have \<open>symbolic.lexes in_cls sp is_newline (\<lambda>_. True) st q cs (Lexed [] []) cs st\<close>
    by (rule symbolic.lexes_stop)
  then show ?case
    using \<open>s = utf8_encode cs\<close> by (auto simp: extra_bytes_def intro!: exI[of _ \<open>Lexed [] []\<close>])
next
  case (lexes_token st s k p st' s' q\<^sub>b h ts r st\<^sub>f)
  from \<open>symbolic.step in_cls (utf8_spec sp) st s (Some k, p, st', s')\<close>
  obtain p0 cs' where st0: \<open>symbolic.step in_cls sp st cs (Some k, p0, st', cs')\<close>
    and p: \<open>p = utf8_encode p0\<close> and s': \<open>s' = utf8_encode cs'\<close>
    using step_utf8[OF \<open>cs \<in> valid_cps\<close>] \<open>s = utf8_encode cs\<close> by blast
  from st0 have \<open>cs = p0 @ cs'\<close>
    by (rule step_split)
  with \<open>cs \<in> valid_cps\<close> have v0: \<open>p0 \<in> valid_cps\<close> and v': \<open>cs' \<in> valid_cps\<close>
    by simp_all
  have adv: \<open>pos_shift (d + extra_bytes p0)
    (advance_list (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) p q\<^sub>b)
    (advance_list is_newline (\<lambda>_. True) p0 q)\<close>
    unfolding p by (rule advance_list_utf8[OF nl v0 \<open>pos_shift d q\<^sub>b q\<close>])
  from lexes_token.IH[OF s' v' adv] obtain l'' r' where
    lx: \<open>symbolic.lexes in_cls sp is_newline (\<lambda>_. True) st'
      (advance_list is_newline (\<lambda>_. True) p0 q) cs' l'' r' st\<^sub>f\<close>
    and l'': \<open>Lexed h ts = encode_lexed_from (d + extra_bytes p0) l''\<close> and r: \<open>r = utf8_encode r'\<close>
    by blast
  obtain h0 ts0 where l0: \<open>l'' = Lexed h0 ts0\<close>
    by (cases l'')
  from l'' have h: \<open>h = utf8_encode h0\<close>
    and ts: \<open>ts = encode_toks (d + extra_bytes p0 + extra_bytes h0) ts0\<close>
    by (simp_all add: l0)
  from st0 lx have \<open>symbolic.lexes in_cls sp is_newline (\<lambda>_. True) st q cs
    (Lexed [] (\<lparr>tok = k, span = span_at q p0, trivia = h0\<rparr> # ts0)) r' st\<^sub>f\<close>
    unfolding l0 by (rule symbolic.lexes_token)
  moreover have \<open>Lexed [] (\<lparr>tok = k, span = span_at q\<^sub>b p, trivia = h\<rparr> # ts) =
      encode_lexed_from d (Lexed [] (\<lparr>tok = k, span = span_at q p0, trivia = h0\<rparr> # ts0))\<close>
    using \<open>pos_shift d q\<^sub>b q\<close>
    by (simp add: p h ts span_at_def encode_span_def pos_shift_def extra_bytes_def)
  ultimately show ?case
    using r by blast
next
  case (lexes_trivia st s p st' s' q\<^sub>b h ts r st\<^sub>f)
  from \<open>symbolic.step in_cls (utf8_spec sp) st s (None, p, st', s')\<close>
  obtain p0 cs' where st0: \<open>symbolic.step in_cls sp st cs (None, p0, st', cs')\<close>
    and p: \<open>p = utf8_encode p0\<close> and s': \<open>s' = utf8_encode cs'\<close>
    using step_utf8[OF \<open>cs \<in> valid_cps\<close>] \<open>s = utf8_encode cs\<close> by blast
  from st0 have \<open>cs = p0 @ cs'\<close>
    by (rule step_split)
  with \<open>cs \<in> valid_cps\<close> have v0: \<open>p0 \<in> valid_cps\<close> and v': \<open>cs' \<in> valid_cps\<close>
    by simp_all
  have adv: \<open>pos_shift (d + extra_bytes p0)
    (advance_list (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) p q\<^sub>b)
    (advance_list is_newline (\<lambda>_. True) p0 q)\<close>
    unfolding p by (rule advance_list_utf8[OF nl v0 \<open>pos_shift d q\<^sub>b q\<close>])
  from lexes_trivia.IH[OF s' v' adv] obtain l'' r' where
    lx: \<open>symbolic.lexes in_cls sp is_newline (\<lambda>_. True) st'
      (advance_list is_newline (\<lambda>_. True) p0 q) cs' l'' r' st\<^sub>f\<close>
    and l'': \<open>Lexed h ts = encode_lexed_from (d + extra_bytes p0) l''\<close> and r: \<open>r = utf8_encode r'\<close>
    by blast
  obtain h0 ts0 where l0: \<open>l'' = Lexed h0 ts0\<close>
    by (cases l'')
  from l'' have h: \<open>h = utf8_encode h0\<close>
    and ts: \<open>ts = encode_toks (d + extra_bytes p0 + extra_bytes h0) ts0\<close>
    by (simp_all add: l0)
  from symbolic.lexes_source[OF lx] v' have vh: \<open>h0 \<in> valid_cps\<close>
    by (auto simp: l0 source_def)
  from st0 lx have \<open>symbolic.lexes in_cls sp is_newline (\<lambda>_. True) st q cs
    (Lexed (p0 @ h0) ts0) r' st\<^sub>f\<close>
    unfolding l0 by (rule symbolic.lexes_trivia)
  moreover have \<open>Lexed (p @ h) ts = encode_lexed_from d (Lexed (p0 @ h0) ts0)\<close>
    by (simp add: p h ts extra_bytes_append[OF v0 vh] add.assoc)
  ultimately show ?case
    using r by blast
qed

text \<open>From a run on codepoints to the run on their bytes:\<close>

lemma lexes_utf8_encode:
  assumes nl: \<open>\<forall>c. is_newline c \<longrightarrow> c < 0x80\<close>
    and lx: \<open>symbolic.lexes in_cls sp is_newline (\<lambda>_. True) st q cs l r st\<^sub>f\<close>
  shows \<open>cs \<in> valid_cps \<Longrightarrow> pos_shift d q\<^sub>b q \<Longrightarrow>
    symbolic.lexes in_cls (utf8_spec sp) (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b)
      st q\<^sub>b (utf8_encode cs) (encode_lexed_from d l) (utf8_encode r) st\<^sub>f\<close>
  using lx
proof (induction arbitrary: d q\<^sub>b rule: symbolic.lexes.induct[of in_cls, consumes 1,
    case_names lexes_stop lexes_token lexes_trivia])
  case (lexes_stop st cs q)
  have \<open>\<not> symbolic.step in_cls (utf8_spec sp) st (utf8_encode cs) x\<close> for x
    using lexes_stop.hyps step_utf8[OF \<open>cs \<in> valid_cps\<close>] by blast
  then have \<open>symbolic.lexes in_cls (utf8_spec sp) (\<lambda>b. is_newline (of_char b))
    (\<lambda>b. \<not> is_cont b) st q\<^sub>b (utf8_encode cs) (Lexed [] []) (utf8_encode cs) st\<close>
    by (rule symbolic.lexes_stop)
  then show ?case
    by (simp add: extra_bytes_def)
next
  case (lexes_token st cs k p st' cs' q h ts r st\<^sub>f)
  from \<open>symbolic.step in_cls sp st cs (Some k, p, st', cs')\<close> have \<open>cs = p @ cs'\<close>
    by (rule step_split)
  with \<open>cs \<in> valid_cps\<close> have v0: \<open>p \<in> valid_cps\<close> and v': \<open>cs' \<in> valid_cps\<close>
    by simp_all
  have st0: \<open>symbolic.step in_cls (utf8_spec sp) st (utf8_encode cs)
    (Some k, utf8_encode p, st', utf8_encode cs')\<close>
    using step_utf8[OF \<open>cs \<in> valid_cps\<close>] \<open>symbolic.step in_cls sp st cs (Some k, p, st', cs')\<close>
    by blast
  have adv: \<open>pos_shift (d + extra_bytes p)
    (advance_list (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) (utf8_encode p) q\<^sub>b)
    (advance_list is_newline (\<lambda>_. True) p q)\<close>
    by (rule advance_list_utf8[OF nl v0 \<open>pos_shift d q\<^sub>b q\<close>])
  from lexes_token.IH[OF v' adv] have \<open>symbolic.lexes in_cls (utf8_spec sp)
    (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) st'
    (advance_list (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) (utf8_encode p) q\<^sub>b)
    (utf8_encode cs') (Lexed (utf8_encode h) (encode_toks (d + extra_bytes p + extra_bytes h) ts))
    (utf8_encode r) st\<^sub>f\<close>
    by simp
  with st0 have \<open>symbolic.lexes in_cls (utf8_spec sp) (\<lambda>b. is_newline (of_char b))
    (\<lambda>b. \<not> is_cont b) st q\<^sub>b (utf8_encode cs)
    (Lexed [] (\<lparr>tok = k, span = span_at q\<^sub>b (utf8_encode p), trivia = utf8_encode h\<rparr> #
      encode_toks (d + extra_bytes p + extra_bytes h) ts)) (utf8_encode r) st\<^sub>f\<close>
    by (rule symbolic.lexes_token)
  then show ?case
    using \<open>pos_shift d q\<^sub>b q\<close>
    by (simp add: span_at_def encode_span_def pos_shift_def extra_bytes_def)
next
  case (lexes_trivia st cs p st' cs' q h ts r st\<^sub>f)
  from \<open>symbolic.step in_cls sp st cs (None, p, st', cs')\<close> have \<open>cs = p @ cs'\<close>
    by (rule step_split)
  with \<open>cs \<in> valid_cps\<close> have v0: \<open>p \<in> valid_cps\<close> and v': \<open>cs' \<in> valid_cps\<close>
    by simp_all
  from symbolic.lexes_source[OF \<open>symbolic.lexes in_cls sp is_newline (\<lambda>_. True) st'
    (advance_list is_newline (\<lambda>_. True) p q) cs' (Lexed h ts) r st\<^sub>f\<close>] v'
  have vh: \<open>h \<in> valid_cps\<close>
    by (auto simp: source_def)
  have st0: \<open>symbolic.step in_cls (utf8_spec sp) st (utf8_encode cs)
    (None, utf8_encode p, st', utf8_encode cs')\<close>
    using step_utf8[OF \<open>cs \<in> valid_cps\<close>] \<open>symbolic.step in_cls sp st cs (None, p, st', cs')\<close>
    by blast
  have adv: \<open>pos_shift (d + extra_bytes p)
    (advance_list (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) (utf8_encode p) q\<^sub>b)
    (advance_list is_newline (\<lambda>_. True) p q)\<close>
    by (rule advance_list_utf8[OF nl v0 \<open>pos_shift d q\<^sub>b q\<close>])
  from lexes_trivia.IH[OF v' adv] have \<open>symbolic.lexes in_cls (utf8_spec sp)
    (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) st'
    (advance_list (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b) (utf8_encode p) q\<^sub>b)
    (utf8_encode cs') (Lexed (utf8_encode h) (encode_toks (d + extra_bytes p + extra_bytes h) ts))
    (utf8_encode r) st\<^sub>f\<close>
    by simp
  with st0 have \<open>symbolic.lexes in_cls (utf8_spec sp) (\<lambda>b. is_newline (of_char b))
    (\<lambda>b. \<not> is_cont b) st q\<^sub>b (utf8_encode cs)
    (Lexed (utf8_encode p @ utf8_encode h) (encode_toks (d + extra_bytes p + extra_bytes h) ts))
    (utf8_encode r) st\<^sub>f\<close>
    by (rule symbolic.lexes_trivia)
  then show ?case
    by (simp add: extra_bytes_append[OF v0 vh] add.assoc)
qed

theorem lexes_utf8:
  assumes nl: \<open>\<forall>c. is_newline c \<longrightarrow> c < 0x80\<close> and cs: \<open>cs \<in> valid_cps\<close>
    and pq: \<open>pos_shift d q\<^sub>b q\<close>
  shows \<open>symbolic.lexes in_cls (utf8_spec sp) (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b)
      st q\<^sub>b (utf8_encode cs) l r st\<^sub>f \<longleftrightarrow>
    (\<exists>l' r'. symbolic.lexes in_cls sp is_newline (\<lambda>_. True) st q cs l' r' st\<^sub>f \<and>
      l = encode_lexed_from d l' \<and> r = utf8_encode r')\<close>
  using lexes_utf8_decode[OF nl _ refl cs pq] lexes_utf8_encode[OF nl _ cs pq] by blast

text \<open>What a step on bytes reads is the encoding of codepoints, so what the lexer on
  bytes consumes is valid:\<close>

lemma step_utf8_lexeme:
  assumes \<open>symbolic.step in_cls (utf8_spec sp) st s (k, p, st', s')\<close>
  obtains p' where \<open>p' \<in> valid_cps\<close> \<open>p = utf8_encode p'\<close>
proof -
  from assms obtain m i where \<open>symbolic.first_token in_cls (map utf8_rule (sp m)) i p s\<close>
    by (auto simp: symbolic.step.simps utf8_spec_def)
  then have \<open>i < length (sp m)\<close> \<open>symbolic.match_rule in_cls (utf8_rule (sp m ! i)) p\<close>
    by (auto simp: symbolic.first_token.simps)
  then show thesis
    using that by (auto simp: match_rule_utf8_rule)
qed

lemma lexes_utf8_source:
  \<open>symbolic.lexes in_cls (utf8_spec sp) is_newline is_col st q s l r st\<^sub>f \<Longrightarrow>
    \<exists>cs. utf8 (source l) cs\<close>
proof (induction rule: symbolic.lexes.induct[of in_cls, consumes 1,
    case_names lexes_stop lexes_token lexes_trivia])
  case (lexes_stop st s q)
  show ?case
    by (auto simp: source_def utf8_def intro!: exI[of _ \<open>[]\<close>])
next
  case (lexes_token st s k p st' s' q h ts r st\<^sub>f)
  from \<open>symbolic.step in_cls (utf8_spec sp) st s (Some k, p, st', s')\<close>
  obtain p' where \<open>p' \<in> valid_cps\<close> \<open>p = utf8_encode p'\<close>
    by (rule step_utf8_lexeme)
  moreover from lexes_token.IH obtain cs where \<open>utf8 (source (Lexed h ts)) cs\<close>
    by blast
  ultimately show ?case
    by (auto simp: source_def span_at_def utf8_def intro!: exI[of _ \<open>p' @ cs\<close>])
next
  case (lexes_trivia st s p st' s' q h ts r st\<^sub>f)
  from \<open>symbolic.step in_cls (utf8_spec sp) st s (None, p, st', s')\<close>
  obtain p' where \<open>p' \<in> valid_cps\<close> \<open>p = utf8_encode p'\<close>
    by (rule step_utf8_lexeme)
  moreover from lexes_trivia.IH obtain cs where \<open>utf8 (source (Lexed h ts)) cs\<close>
    by blast
  ultimately show ?case
    by (auto simp: source_def utf8_def intro!: exI[of _ \<open>p' @ cs\<close>])
qed

section \<open>Surface theorems\<close>

text \<open>If the index of each mode holds the tables of its rules on bytes and newlines are
  ASCII, the lexer on the bytes of valid UTF-8 is the encoding of the judgment on the
  codepoints:\<close>

theorem utf8_lexer_iff_lexes:
  assumes ix: \<open>\<forall>m. ix m < IArray.length TT \<and> TT !! ix m = char_tables (utf8_spec sp m)\<close>
    and nl: \<open>\<forall>c. is_newline c \<longrightarrow> c < 0x80\<close> and u: \<open>utf8 s cs\<close>
  shows \<open>char_lexer TT ix (utf8_spec sp) (\<lambda>b. is_newline (of_char b)) (\<lambda>b. \<not> is_cont b)
      st q s = (l, r, st\<^sub>f) \<longleftrightarrow>
    (\<exists>l' r'. symbolic.lexes in_cls sp is_newline (\<lambda>_. True) st q cs l' r' st\<^sub>f \<and>
      l = encode_lexed l' \<and> r = utf8_encode r')\<close>
proof -
  from u have s: \<open>s = utf8_encode cs\<close> and cs: \<open>cs \<in> valid_cps\<close>
    by (auto simp: utf8_def)
  have \<open>pos_shift 0 q q\<close>
    by (simp add: pos_shift_def)
  then show ?thesis
    unfolding char_lexer_iff_lexes[OF ix] s by (rule lexes_utf8[OF nl cs])
qed

text \<open>On any input, the lexer consumes valid UTF-8, and lexes it as it does on its own:\<close>

theorem utf8_lexer_consumed:
  assumes ix: \<open>\<forall>m. ix m < IArray.length TT \<and> TT !! ix m = char_tables (utf8_spec sp m)\<close>
    and run: \<open>char_lexer TT ix (utf8_spec sp) is_newline is_col st q s = (l, r, st\<^sub>f)\<close>
  shows \<open>s = source l @ r \<and> (\<exists>cs. utf8 (source l) cs) \<and>
    char_lexer TT ix (utf8_spec sp) is_newline is_col st q (source l) = (l, [], st\<^sub>f)\<close>
proof -
  from run have lx: \<open>symbolic.lexes in_cls (utf8_spec sp) is_newline is_col st q s l r st\<^sub>f\<close>
    by (simp add: char_lexer_iff_lexes[OF ix])
  from lx have \<open>s = source l @ r\<close>
    by (simp add: symbolic.lexes_source)
  moreover from lx have \<open>\<exists>cs. utf8 (source l) cs\<close>
    by (rule lexes_utf8_source)
  moreover from symbolic.lexes_consumed[OF lx]
  have \<open>char_lexer TT ix (utf8_spec sp) is_newline is_col st q (source l) = (l, [], st\<^sub>f)\<close>
    by (simp add: char_lexer_iff_lexes[OF ix])
  ultimately show ?thesis
    by blast
qed

end
