(* Author: Basil Fürer *)

theory TIGER_UTF8
  imports "HOL-Library.Char_ord"
begin

section \<open>UTF-8\<close>

text \<open>Codepoints are natural numbers and bytes are characters. A valid codepoint is one
  up to \<open>0x10FFFF\<close> that is no surrogate. UTF-8 encodes a codepoint in one to four bytes
  \<^cite>\<open>\<open>Sect.~3\<close> in "rfc3629-utf8"\<close>. The encoding writes the codepoint in base 64 with as
  many digits as it has bytes, puts a length marker before the first digit and \<open>0x80\<close>
  before the others. The judgment \<open>utf8 s cs\<close> says that the bytes \<open>s\<close> encode the valid
  codepoints \<open>cs\<close>.

  Decoding needs no validity check: the decoder reads the length from the first byte and
  inverts the encoding of valid codepoints. Whether a byte string is valid is decided
  elsewhere (\<open>utf8_valid\<close> here, a DFA in the lexer).

  This theory proves that the encoding is prefix-free, so a valid byte string splits
  uniquely at codepoint boundaries, and splits a codepoint interval into sequences of byte
  intervals (\<open>utf8_ranges\<close>), whose words are exactly the encodings of the valid
  codepoints of the interval. For the interval of all codepoints these are the rows of the
  table of well-formed byte sequences \<^cite>\<open>\<open>Sect.~4\<close> in "rfc3629-utf8"\<close>. The split is
  that of RE2 and of the \<open>Utf8Sequences\<close> iterator of the Rust crate \<open>regex-syntax\<close>,
  restated over digit strings: an interval of digit strings of one length is a sum of
  products of digit intervals, and those of the encodings of one length map to byte
  intervals digit by digit.\<close>

subsection \<open>Codepoints and their digits\<close>

definition is_valid_cp :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>is_valid_cp c \<longleftrightarrow> c \<le> 0x10FFFF \<and> (c < 0xD800 \<or> 0xDFFF < c)\<close>

definition cp_len :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>cp_len c = (if c < 0x80 then 1 else if c < 0x800 then 2 else if c < 0x10000 then 3 else 4)\<close>

text \<open>\<open>digits n c\<close> writes \<open>c\<close> with \<open>n\<close> digits in base 64, the first of which takes the
  rest of \<open>c\<close>. \<open>digits_val\<close> reads a digit string back:\<close>

fun digits :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>digits 0 c = []\<close>
| \<open>digits (Suc 0) c = [c]\<close>
| \<open>digits (Suc (Suc n)) c = digits (Suc n) (c div 64) @ [c mod 64]\<close>

primrec digits_val :: \<open>nat list \<Rightarrow> nat\<close> where
  \<open>digits_val [] = 0\<close>
| \<open>digits_val (d # ds) = d * 64 ^ length ds + digits_val ds\<close>

lemma length_digits[simp]: \<open>length (digits n c) = n\<close>
  by (induct n c rule: digits.induct) simp_all

lemma digits_val_append_digit[simp]: \<open>digits_val (ds @ [d]) = 64 * digits_val ds + d\<close>
  by (induct ds) (simp_all add: algebra_simps)

lemma digits_val_digits[simp]: \<open>0 < n \<Longrightarrow> digits_val (digits n c) = c\<close>
  by (induct n c rule: digits.induct) simp_all

lemma digits_tl_less: \<open>d \<in> set (tl (digits n c)) \<Longrightarrow> d < 64\<close>
  by (induct n c rule: digits.induct) (auto simp: tl_append split: list.splits)

lemma digits_val_less: \<open>\<forall>d \<in> set ds. d < 64 \<Longrightarrow> digits_val ds < 64 ^ length ds\<close>
proof (induct ds)
  case (Cons d ds)
  then have \<open>d * 64 ^ length ds + digits_val ds < (d + 1) * 64 ^ length ds\<close>
    by simp
  also have \<open>\<dots> \<le> 64 * 64 ^ length ds\<close>
    using Cons.prems by (intro mult_right_mono) auto
  finally show ?case
    by simp
qed simp

lemma digits_digits_val:
  \<open>\<lbrakk> length ds = n; 0 < n; \<forall>d \<in> set (tl ds). d < 64 \<rbrakk> \<Longrightarrow> digits n (digits_val ds) = ds\<close>
proof (induct ds arbitrary: n rule: rev_induct)
  case (snoc d ds)
  show ?case
  proof (cases ds)
    case Nil
    with snoc.prems show ?thesis
      by auto
  next
    case (Cons e es)
    with snoc.prems have \<open>n = Suc (length ds)\<close> \<open>d < 64\<close>
      and \<open>digits (length ds) (digits_val ds) = ds\<close>
      using snoc.hyps[of \<open>length ds\<close>] by (auto simp del: digits_val.simps)
    moreover from Cons have \<open>length ds = Suc (length es)\<close>
      by simp
    ultimately show ?thesis
      by (simp del: digits_val.simps)
  qed
qed simp

subsection \<open>Encoding\<close>

text \<open>The length marker of an encoding of \<open>n\<close> bytes:\<close>

definition lead :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>lead n = (if n = 1 then 0 else if n = 2 then 0xC0 else if n = 3 then 0xE0 else 0xF0)\<close>

definition bytes_of :: \<open>nat \<Rightarrow> nat list \<Rightarrow> char list\<close> where
  \<open>bytes_of n ds = (case ds of [] \<Rightarrow> []
     | d # ds' \<Rightarrow> char_of (lead n + d) # map (\<lambda>d. char_of (0x80 + d)) ds')\<close>

definition utf8_encode_cp :: \<open>nat \<Rightarrow> char list\<close> where
  \<open>utf8_encode_cp c = bytes_of (cp_len c) (digits (cp_len c) c)\<close>

definition utf8_encode :: \<open>nat list \<Rightarrow> char list\<close> where
  \<open>utf8_encode cs = concat (map utf8_encode_cp cs)\<close>

lemma utf8_encode_simps[simp]:
  \<open>utf8_encode [] = []\<close>
  \<open>utf8_encode (c # cs) = utf8_encode_cp c @ utf8_encode cs\<close>
  \<open>utf8_encode (cs @ cs') = utf8_encode cs @ utf8_encode cs'\<close>
  by (simp_all add: utf8_encode_def)

definition utf8 :: \<open>char list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>utf8 s cs \<longleftrightarrow> (\<forall>c \<in> set cs. is_valid_cp c) \<and> s = utf8_encode cs\<close>

text \<open>A continuation byte (\<open>0x80\<close> to \<open>0xBF\<close>) starts no codepoint:\<close>

definition is_cont :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_cont b \<longleftrightarrow> 0x80 \<le> (of_char b :: nat) \<and> (of_char b :: nat) < 0xC0\<close>

subsection \<open>Decoding\<close>

text \<open>The length of an encoding from its first byte, and the codepoint of an encoding
  from its first byte and the others:\<close>

definition lead_len :: \<open>char \<Rightarrow> nat\<close> where
  \<open>lead_len b = (if (of_char b :: nat) < 0xC0 then 1 else if (of_char b :: nat) < 0xE0 then 2
     else if (of_char b :: nat) < 0xF0 then 3 else 4)\<close>

definition decode_cp :: \<open>char \<Rightarrow> char list \<Rightarrow> nat\<close> where
  \<open>decode_cp b bs = digits_val ((of_char b - lead (lead_len b)) # map (\<lambda>x. of_char x - 0x80) bs)\<close>

fun utf8_decode :: \<open>char list \<Rightarrow> nat list\<close> where
  \<open>utf8_decode [] = []\<close>
| \<open>utf8_decode (b # bs) =
    decode_cp b (take (lead_len b - 1) bs) # utf8_decode (drop (lead_len b - 1) bs)\<close>

text \<open>The encoding of a codepoint up to \<open>0x10FFFF\<close> starts with a byte that gives its
  length and decodes back to it:\<close>

lemma digits_numeral:
  \<open>digits 2 c = [c div 64, c mod 64]\<close>
  \<open>digits 3 c = [c div 64 div 64, c div 64 mod 64, c mod 64]\<close>
  \<open>digits 4 c = [c div 64 div 64 div 64, c div 64 div 64 mod 64, c div 64 mod 64, c mod 64]\<close>
proof -
  have n: \<open>(2::nat) = Suc (Suc 0)\<close> \<open>(3::nat) = Suc (Suc (Suc 0))\<close>
    \<open>(4::nat) = Suc (Suc (Suc (Suc 0)))\<close>
    by simp_all
  show \<open>digits 2 c = [c div 64, c mod 64]\<close>
    \<open>digits 3 c = [c div 64 div 64, c div 64 mod 64, c mod 64]\<close>
    \<open>digits 4 c = [c div 64 div 64 div 64, c div 64 div 64 mod 64, c div 64 mod 64, c mod 64]\<close>
    by (simp_all only: n digits.simps append.simps)
qed

lemma utf8_encode_cp_Cons:
  assumes \<open>c \<le> 0x10FFFF\<close>
  obtains b bs where \<open>utf8_encode_cp c = b # bs\<close> \<open>lead_len b = cp_len c\<close>
    \<open>length bs = cp_len c - 1\<close> \<open>decode_cp b bs = c\<close> \<open>\<not> is_cont b\<close> \<open>\<forall>x \<in> set bs. is_cont x\<close>
proof -
  have e: \<open>64 * (x div 64) + x mod 64 = x\<close> for x :: nat
    by simp
  consider (c1) \<open>c < 0x80\<close> | (c2) \<open>0x80 \<le> c\<close> \<open>c < 0x800\<close> | (c3) \<open>0x800 \<le> c\<close> \<open>c < 0x10000\<close>
    | (c4) \<open>0x10000 \<le> c\<close> by linarith
  then show thesis
  proof cases
    case c1
    show thesis
      by (rule that[of \<open>char_of c\<close> \<open>[]\<close>])
        (use c1 in \<open>simp_all add: utf8_encode_cp_def bytes_of_def lead_def lead_len_def
          decode_cp_def is_cont_def cp_len_def\<close>)
  next
    case c2
    show thesis
      by (rule that[of \<open>char_of (0xC0 + c div 64)\<close> \<open>[char_of (0x80 + c mod 64)]\<close>])
        (use c2 assms in \<open>simp_all add: utf8_encode_cp_def bytes_of_def lead_def lead_len_def
          decode_cp_def is_cont_def cp_len_def digits_numeral\<close>)
  next
    case c3
    obtain a b d where dg: \<open>digits 3 c = [a, b, d]\<close>
      and \<open>a < 16\<close> \<open>b < 64\<close> \<open>d < 64\<close> \<open>a * 4096 + b * 64 + d = c\<close>
    proof (intro that[of \<open>c div 64 div 64\<close> \<open>c div 64 mod 64\<close> \<open>c mod 64\<close>])
      have \<open>c div 64 < 1024\<close>
        by (rule less_mult_imp_div_less) (use c3 in simp)
      then show \<open>c div 64 div 64 < 16\<close>
        by (intro less_mult_imp_div_less) simp
      show \<open>c div 64 div 64 * 4096 + c div 64 mod 64 * 64 + c mod 64 = c\<close>
        using e[of c] e[of \<open>c div 64\<close>] by linarith
    qed (simp_all add: digits_numeral)
    show thesis
      by (rule that[of \<open>char_of (0xE0 + a)\<close> \<open>[char_of (0x80 + b), char_of (0x80 + d)]\<close>])
        (use c3 dg \<open>a < 16\<close> \<open>b < 64\<close> \<open>d < 64\<close> \<open>a * 4096 + b * 64 + d = c\<close> in
          \<open>simp_all add: utf8_encode_cp_def bytes_of_def lead_def lead_len_def decode_cp_def
            is_cont_def cp_len_def\<close>)
  next
    case c4
    obtain a b d f where dg: \<open>digits 4 c = [a, b, d, f]\<close>
      and \<open>a < 5\<close> \<open>b < 64\<close> \<open>d < 64\<close> \<open>f < 64\<close> \<open>a * 262144 + b * 4096 + d * 64 + f = c\<close>
    proof (intro that[of \<open>c div 64 div 64 div 64\<close> \<open>c div 64 div 64 mod 64\<close> \<open>c div 64 mod 64\<close>
          \<open>c mod 64\<close>])
      have \<open>c div 64 < 20480\<close>
        by (rule less_mult_imp_div_less) (use assms in simp)
      then have \<open>c div 64 div 64 < 320\<close>
        by (intro less_mult_imp_div_less) simp
      then show \<open>c div 64 div 64 div 64 < 5\<close>
        by (intro less_mult_imp_div_less) simp
      show \<open>c div 64 div 64 div 64 * 262144 + c div 64 div 64 mod 64 * 4096
          + c div 64 mod 64 * 64 + c mod 64 = c\<close>
        using e[of c] e[of \<open>c div 64\<close>] e[of \<open>c div 64 div 64\<close>] by linarith
    qed (simp_all add: digits_numeral)
    show thesis
      by (rule that[of \<open>char_of (0xF0 + a)\<close>
            \<open>[char_of (0x80 + b), char_of (0x80 + d), char_of (0x80 + f)]\<close>])
        (use c4 dg \<open>a < 5\<close> \<open>b < 64\<close> \<open>d < 64\<close> \<open>f < 64\<close> \<open>a * 262144 + b * 4096 + d * 64 + f = c\<close> in
          \<open>simp_all add: utf8_encode_cp_def bytes_of_def lead_def lead_len_def decode_cp_def
            is_cont_def cp_len_def\<close>)
  qed
qed

lemma utf8_encode_cp_ne[simp]: \<open>c \<le> 0x10FFFF \<Longrightarrow> utf8_encode_cp c \<noteq> []\<close>
  by (erule utf8_encode_cp_Cons) simp

lemma utf8_decode_encode_cp_append:
  \<open>c \<le> 0x10FFFF \<Longrightarrow> utf8_decode (utf8_encode_cp c @ s) = c # utf8_decode s\<close>
  by (erule utf8_encode_cp_Cons) simp

theorem utf8_decode_encode: \<open>\<forall>c \<in> set cs. c \<le> 0x10FFFF \<Longrightarrow> utf8_decode (utf8_encode cs) = cs\<close>
  using utf8_decode_encode_cp_append[where s = \<open>utf8_encode _\<close>] by (induct cs) simp_all

lemma is_valid_cp_le: \<open>is_valid_cp c \<Longrightarrow> c \<le> 0x10FFFF\<close>
  by (simp add: is_valid_cp_def)

lemma utf8_imp_decode: \<open>utf8 s cs \<Longrightarrow> utf8_decode s = cs\<close>
  by (auto simp: utf8_def utf8_decode_encode is_valid_cp_le)

text \<open>Validity is decidable by decoding and encoding again:\<close>

definition utf8_valid :: \<open>char list \<Rightarrow> bool\<close> where
  \<open>utf8_valid s \<longleftrightarrow> list_all is_valid_cp (utf8_decode s) \<and> utf8_encode (utf8_decode s) = s\<close>

lemma utf8_valid_iff: \<open>utf8_valid s \<longleftrightarrow> (\<exists>cs. utf8 s cs)\<close>
  by (auto simp: utf8_valid_def utf8_def list_all_iff utf8_decode_encode is_valid_cp_le)

subsection \<open>Prefix-freeness\<close>

theorem utf8_encode_cp_prefix_free:
  assumes \<open>c \<le> 0x10FFFF\<close> \<open>c' \<le> 0x10FFFF\<close> \<open>utf8_encode_cp c @ s = utf8_encode_cp c' @ s'\<close>
  shows \<open>c = c' \<and> s = s'\<close>
proof -
  from assms(1) obtain b bs where \<open>utf8_encode_cp c = b # bs\<close> \<open>lead_len b = cp_len c\<close>
    \<open>length bs = cp_len c - 1\<close> \<open>decode_cp b bs = c\<close>
    by (rule utf8_encode_cp_Cons)
  moreover from assms(2) obtain b' bs' where \<open>utf8_encode_cp c' = b' # bs'\<close>
    \<open>lead_len b' = cp_len c'\<close> \<open>length bs' = cp_len c' - 1\<close> \<open>decode_cp b' bs' = c'\<close>
    by (rule utf8_encode_cp_Cons)
  ultimately show ?thesis
    using assms(3) by (auto simp: append_eq_append_conv)
qed

text \<open>A valid byte string splits uniquely at codepoint boundaries: an encoding that
  starts a valid byte string is the encoding of a prefix of its codepoints:\<close>

lemma utf8_encode_prefix_ex:
  \<open>\<lbrakk> \<forall>c \<in> set (p @ cs). c \<le> 0x10FFFF; utf8_encode p @ u = utf8_encode cs \<rbrakk> \<Longrightarrow>
    \<exists>u'. cs = p @ u' \<and> u = utf8_encode u'\<close>
proof (induct p arbitrary: cs)
  case (Cons c p)
  then obtain c' cs' where \<open>cs = c' # cs'\<close>
    by (cases cs) auto
  with Cons.prems have \<open>c = c' \<and> utf8_encode p @ u = utf8_encode cs'\<close>
    by (intro utf8_encode_cp_prefix_free) auto
  with Cons.hyps[of cs'] Cons.prems \<open>cs = c' # cs'\<close> show ?case
    by auto
qed simp

theorem utf8_encode_prefix:
  assumes \<open>\<forall>c \<in> set (p @ cs). c \<le> 0x10FFFF\<close> \<open>utf8_encode p @ u = utf8_encode cs\<close>
  obtains u' where \<open>cs = p @ u'\<close> \<open>u = utf8_encode u'\<close>
  using utf8_encode_prefix_ex[OF assms] by blast

theorem utf8_encode_inj:
  \<open>\<lbrakk> \<forall>c \<in> set (cs @ cs'). c \<le> 0x10FFFF; utf8_encode cs = utf8_encode cs' \<rbrakk> \<Longrightarrow> cs = cs'\<close>
  by (metis utf8_decode_encode Un_iff set_append)

text \<open>Each codepoint starts with one byte that is no continuation byte:\<close>

lemma length_filter_utf8_encode:
  \<open>\<forall>c \<in> set cs. c \<le> 0x10FFFF \<Longrightarrow> length (filter (\<lambda>b. \<not> is_cont b) (utf8_encode cs)) = length cs\<close>
proof (induct cs)
  case (Cons c cs)
  then show ?case
    by (auto elim!: utf8_encode_cp_Cons[of c] simp: filter_empty_conv)
qed simp

subsection \<open>Intervals of digit strings\<close>

text \<open>The digit strings between \<open>lo\<close> and \<open>hi\<close>, given as the list of their pairs of
  digits, as a sum of products of digit intervals. Where \<open>lo\<close> and \<open>hi\<close> differ first, the
  strings split into those that agree with \<open>lo\<close> there, those strictly between and those
  that agree with \<open>hi\<close>. A part whose bound is all zeros (all \<open>63\<close>) merges into the
  middle:\<close>

function digit_ranges :: \<open>(nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list list\<close> where
  \<open>digit_ranges [] = [[]]\<close>
| \<open>digit_ranges ((x, y) # ds) =
    (if y < x then []
     else if x = y then map ((#) (x, x)) (digit_ranges ds)
     else
      (let lo = (\<forall>d \<in> set ds. fst d = 0); hi = (\<forall>d \<in> set ds. snd d = 63);
         x' = (if lo then x else Suc x); y' = (if hi then y else y - 1) in
       (if lo then [] else map ((#) (x, x)) (digit_ranges (map (\<lambda>(a, _). (a, 63)) ds))) @
       (if x' \<le> y' then [(x', y') # map (\<lambda>_. (0, 63)) ds] else []) @
       (if hi then [] else map ((#) (y, y)) (digit_ranges (map (\<lambda>(_, b). (0, b)) ds)))))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure length\<close>) auto

definition in_ranges :: \<open>('a::ord) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool\<close> where
  \<open>in_ranges ds r \<longleftrightarrow> list_all2 (\<lambda>d (l, h). l \<le> d \<and> d \<le> h) ds r\<close>

definition seqs :: \<open>('a::ord \<times> 'a) list list \<Rightarrow> 'a list set\<close> where
  \<open>seqs R = (\<Union>r \<in> set R. {ds. in_ranges ds r})\<close>

lemma digits_val_Cons_le_iff:
  assumes \<open>length xs = length es\<close> \<open>\<forall>a \<in> set xs. a < 64\<close> \<open>\<forall>a \<in> set es. a < 64\<close>
  shows \<open>digits_val (x # xs) \<le> digits_val (d # es) \<longleftrightarrow>
    x < d \<or> (x = d \<and> digits_val xs \<le> digits_val es)\<close>
proof -
  let ?P = \<open>64 ^ length es\<close>
  have \<open>digits_val xs < ?P\<close> \<open>digits_val es < ?P\<close>
    using digits_val_less[OF assms(2)] digits_val_less[OF assms(3)] assms(1) by simp_all
  moreover have \<open>(Suc d) * ?P \<le> x * ?P\<close> if \<open>d < x\<close>
    using that by (intro mult_le_mono1) simp
  moreover have \<open>(Suc x) * ?P \<le> d * ?P\<close> if \<open>x < d\<close>
    using that by (intro mult_le_mono1) simp
  ultimately show ?thesis
    using assms(1) by (cases \<open>x < d\<close>; cases \<open>x = d\<close>) auto
qed

lemma digits_val_all0: \<open>\<forall>a \<in> set ds. a = 0 \<Longrightarrow> digits_val ds = 0\<close>
  by (induct ds) auto

lemma digits_val_all63: \<open>\<forall>a \<in> set ds. a = 63 \<Longrightarrow> digits_val ds + 1 = 64 ^ length ds\<close>
  by (induct ds) auto

lemma digits_val_hd_less: \<open>digits_val (e # es) < 64 ^ Suc (length es) \<Longrightarrow> e < 64\<close>
proof (rule ccontr)
  assume \<open>digits_val (e # es) < 64 ^ Suc (length es)\<close> \<open>\<not> e < 64\<close>
  then have \<open>64 * 64 ^ length es \<le> e * 64 ^ length es\<close>
    by (intro mult_le_mono1) simp
  with \<open>digits_val (e # es) < _\<close> show False
    by simp
qed

lemma in_ranges_Cons:
  \<open>in_ranges ds ((l, h) # rs) \<longleftrightarrow> (\<exists>d es. ds = d # es \<and> l \<le> d \<and> d \<le> h \<and> in_ranges es rs)\<close>
  by (cases ds) (auto simp: in_ranges_def)

lemma in_ranges_const:
  \<open>in_ranges (es :: nat list) (map (\<lambda>_. (0, 63)) zs) \<longleftrightarrow>
    length es = length zs \<and> (\<forall>e \<in> set es. e \<le> 63)\<close>
proof (induct zs arbitrary: es)
  case Nil
  then show ?case
    by (cases es) (simp_all add: in_ranges_def)
next
  case (Cons z zs)
  then show ?case
    by (cases es) (auto simp: in_ranges_Cons[of _ 0 63, unfolded])
qed

lemma seqs_append: \<open>seqs (R @ S) = seqs R \<union> seqs S\<close>
  by (auto simp: seqs_def)

lemma seqs_map_Cons:
  \<open>ds \<in> seqs (map ((#) (l, h)) R) \<longleftrightarrow> (\<exists>d es. ds = d # es \<and> l \<le> d \<and> d \<le> h \<and> es \<in> seqs R)\<close>
  by (auto simp: seqs_def in_ranges_Cons)

text \<open>The words of \<^const>\<open>digit_ranges\<close> are the digit strings between the bounds, whose
  digits after the first are below \<open>64\<close>:\<close>

lemma digit_ranges_all_of_tl:
  assumes \<open>\<And>ds. ds \<in> S \<longleftrightarrow> length ds = length ws \<and> (\<forall>d \<in> set (tl ds). d < 64) \<and>
    digits_val (map fst ws) \<le> digits_val ds \<and> digits_val ds \<le> digits_val (map snd ws)\<close>
    \<open>\<forall>(a, b) \<in> set ws. a < 64 \<and> b < 64\<close>
  shows \<open>ds \<in> S \<longleftrightarrow> length ds = length ws \<and> (\<forall>d \<in> set ds. d < 64) \<and>
    digits_val (map fst ws) \<le> digits_val ds \<and> digits_val ds \<le> digits_val (map snd ws)\<close>
proof -
  have \<open>digits_val (map snd ws) < 64 ^ length ws\<close>
    using assms(2) by (intro digits_val_less[of \<open>map snd ws\<close>, simplified]) auto
  have hd: \<open>a < 64\<close> if \<open>ds = a # as\<close> \<open>Suc (length as) = length ws\<close>
    \<open>a * 64 ^ length as + digits_val as \<le> digits_val (map snd ws)\<close> for a as
  proof (rule ccontr)
    assume \<open>\<not> a < 64\<close>
    then have \<open>64 ^ Suc (length as) \<le> a * 64 ^ length as\<close>
      by simp
    with that \<open>digits_val (map snd ws) < 64 ^ length ws\<close> show False
      by (metis add_leD1 le_trans not_le)
  qed
  show ?thesis
    using assms(1)[of ds] by (cases ds) (auto dest: hd)
qed

lemma seqs_Nil [simp]: \<open>seqs [] = {}\<close>
  by (simp add: seqs_def)

lemma seqs_if_single:
  \<open>ds \<in> seqs (if c then [(l, h) # rs] else []) \<longleftrightarrow>
    c \<and> (\<exists>d es. ds = d # es \<and> l \<le> d \<and> d \<le> h \<and> in_ranges es rs)\<close>
  by (auto simp: seqs_def in_ranges_Cons)

lemma seqs_digit_ranges_aux:
  \<open>length xys = n \<Longrightarrow> \<forall>(a, b) \<in> set (tl xys). a < 64 \<and> b < 64 \<Longrightarrow>
    ds \<in> seqs (digit_ranges xys) \<longleftrightarrow> length ds = length xys \<and> (\<forall>d \<in> set (tl ds). d < 64) \<and>
    digits_val (map fst xys) \<le> digits_val ds \<and> digits_val ds \<le> digits_val (map snd xys)\<close>
proof (induction n arbitrary: xys ds)
  case 0
  then show ?case
    by (auto simp: seqs_def in_ranges_def)
next
  case (Suc n)
  then obtain x y zs where xys: \<open>xys = (x, y) # zs\<close> \<open>length zs = n\<close>
    and zs: \<open>\<forall>(a, b) \<in> set zs. a < 64 \<and> b < 64\<close>
    by (cases xys) auto
  have A: \<open>ds \<in> seqs (digit_ranges ws) \<longleftrightarrow> length ds = n \<and> (\<forall>d \<in> set ds. d < 64) \<and>
    digits_val (map fst ws) \<le> digits_val ds \<and> digits_val ds \<le> digits_val (map snd ws)\<close>
    if \<open>length ws = n\<close> \<open>\<forall>(a, b) \<in> set ws. a < 64 \<and> b < 64\<close> for ws ds
  proof -
    have \<open>\<forall>(a, b) \<in> set (tl ws). a < 64 \<and> b < 64\<close>
      using that(2) by (cases ws) auto
    from digit_ranges_all_of_tl[OF _ that(2), of \<open>seqs (digit_ranges ws)\<close> ds]
      Suc.IH[OF that(1) this] that(1) show ?thesis
      by simp
  qed
  have e1: \<open>map fst (map (\<lambda>(a, _). (a, 63)) zs) = map fst zs\<close>
    and e2: \<open>map snd (map (\<lambda>(a, _). (a, 63)) zs) = map (\<lambda>_. 63) zs\<close>
    and e3: \<open>map fst (map (\<lambda>(_, b). (0, b)) zs) = map (\<lambda>_. 0) zs\<close>
    and e4: \<open>map snd (map (\<lambda>(_, b). (0, b)) zs) = map snd zs\<close>
    by (induct zs) auto
  have z0: \<open>digits_val (map (\<lambda>_. 0) zs) = 0\<close>
    by (intro digits_val_all0) auto
  have z63: \<open>digits_val (map (\<lambda>_. 63) zs) + 1 = 64 ^ n\<close>
    using digits_val_all63[of \<open>map (\<lambda>_. 63) zs\<close>] \<open>length zs = n\<close> by simp
  have A1: \<open>(es \<in> seqs (digit_ranges (map (\<lambda>(a, _). (a, 63)) zs))) \<longleftrightarrow>
    length es = n \<and> (\<forall>e \<in> set es. e < 64) \<and> digits_val (map fst zs) \<le> digits_val es\<close>
    for es
  proof -
    have l: \<open>length (map (\<lambda>(a, _). (a, 63)) zs) = n\<close>
      using xys by simp
    have b: \<open>\<forall>(a, b) \<in> set (map (\<lambda>(a, _). (a, 63 :: nat)) zs). a < 64 \<and> b < 64\<close>
      using zs by auto
    have le: \<open>length es = n \<Longrightarrow> \<forall>e \<in> set es. e < 64 \<Longrightarrow>
        digits_val es \<le> digits_val (map (\<lambda>_. 63) zs)\<close>
      using digits_val_less[of es] z63 by auto
    show ?thesis
      unfolding A[OF l b] e1 e2 using le by blast
  qed
  have A2: \<open>(es \<in> seqs (digit_ranges (map (\<lambda>(_, b). (0, b)) zs))) \<longleftrightarrow>
    length es = n \<and> (\<forall>e \<in> set es. e < 64) \<and> digits_val es \<le> digits_val (map snd zs)\<close> for es
  proof -
    have l: \<open>length (map (\<lambda>(_, b). (0 :: nat, b)) zs) = n\<close>
      using xys by simp
    have b: \<open>\<forall>(a, b) \<in> set (map (\<lambda>(_, b). (0 :: nat, b)) zs). a < 64 \<and> b < 64\<close>
      using zs by auto
    show ?thesis
      unfolding A[OF l b] e3 e4 z0 by simp
  qed
  have A3: \<open>(es \<in> seqs (digit_ranges zs)) \<longleftrightarrow> length es = n \<and> (\<forall>e \<in> set es. e < 64) \<and>
    digits_val (map fst zs) \<le> digits_val es \<and> digits_val es \<le> digits_val (map snd zs)\<close> for es
    using A[of zs es] zs xys by auto
  have lo0: \<open>\<forall>d \<in> set zs. fst d = 0 \<Longrightarrow> digits_val (map fst zs) = 0\<close>
    by (intro digits_val_all0) auto
  have hi63: \<open>\<forall>d \<in> set zs. snd d = 63 \<Longrightarrow> digits_val (map snd zs) + 1 = 64 ^ n\<close>
    using digits_val_all63[of \<open>map snd zs\<close>] xys by simp
  have vE: \<open>length es = n \<Longrightarrow> \<forall>e \<in> set es. e < 64 \<Longrightarrow> digits_val es < 64 ^ n\<close> for es
    using digits_val_less by auto
  have hv: \<open>\<forall>d \<in> set zs. snd d = 63 \<Longrightarrow> length es = n \<Longrightarrow> \<forall>e \<in> set es. e < 64 \<Longrightarrow>
      digits_val es \<le> digits_val (map snd zs)\<close> for es
    using hi63 vE by fastforce
  show ?case
  proof (cases ds)
    case Nil
    then show ?thesis
      by (cases \<open>y < x\<close>; cases \<open>x = y\<close>)
        (auto simp: xys seqs_map_Cons seqs_append seqs_if_single Let_def)
  next
    case (Cons d es)
    have R: \<open>(length (d # es) = length ((x, y) # zs) \<and> (\<forall>a \<in> set (tl (d # es)). a < 64) \<and>
      digits_val (map fst ((x, y) # zs)) \<le> digits_val (d # es) \<and>
      digits_val (d # es) \<le> digits_val (map snd ((x, y) # zs))) \<longleftrightarrow>
      (length es = n \<and> (\<forall>e \<in> set es. e < 64) \<and>
        (x < d \<or> x = d \<and> digits_val (map fst zs) \<le> digits_val es) \<and>
        (d < y \<or> d = y \<and> digits_val es \<le> digits_val (map snd zs)))\<close>
    proof (cases \<open>length es = n \<and> (\<forall>e \<in> set es. e < 64)\<close>)
      case True
      have lo: \<open>digits_val (x # map fst zs) \<le> digits_val (d # es) \<longleftrightarrow>
          x < d \<or> x = d \<and> digits_val (map fst zs) \<le> digits_val es\<close>
        using True zs xys by (intro digits_val_Cons_le_iff) auto
      have hi: \<open>digits_val (d # es) \<le> digits_val (y # map snd zs) \<longleftrightarrow>
          d < y \<or> d = y \<and> digits_val es \<le> digits_val (map snd zs)\<close>
        using True zs xys by (intro digits_val_Cons_le_iff) auto
      from True xys show ?thesis
        by (simp del: digits_val.simps add: lo hi)
    next
      case False
      with xys show ?thesis
        by auto
    qed
    show ?thesis
      unfolding xys(1) Cons R
      apply (cases \<open>y < x\<close>; cases \<open>x = y\<close>)
      apply (simp_all add: seqs_map_Cons seqs_append seqs_if_single Let_def A1 A2 A3
          in_ranges_const)
      subgoal by auto
      subgoal by auto
      subgoal
        apply (cases \<open>\<forall>d \<in> set zs. fst d = 0\<close>; cases \<open>\<forall>d \<in> set zs. snd d = 63\<close>)
        subgoal premises p
        proof -
          have e1: \<open>(\<exists>d \<in> set zs. 0 < fst d) = False\<close> \<open>(\<exists>d \<in> set zs. snd d \<noteq> 63) = False\<close>
            using p(3, 4) by auto
          have n64: \<open>e < 64 \<longleftrightarrow> e \<le> (63 :: nat)\<close> for e
            by presburger
          have hv': \<open>length es = n \<Longrightarrow> \<forall>e \<in> set es. e < 64 \<Longrightarrow>
              digits_val es \<le> digits_val (map snd zs)\<close>
            using hv[OF p(4)] by blast
          show ?thesis
            using p(3, 4) lo0 xys(2) hv' by (simp add: e1 n64) (auto simp: n64 less_le)
        qed
        subgoal premises p
        proof -
          have e1: \<open>(\<exists>d \<in> set zs. 0 < fst d) = False\<close> \<open>(\<exists>d \<in> set zs. snd d \<noteq> 63) = True\<close>
            \<open>(\<forall>d \<in> set zs. fst d = 0) = True\<close> \<open>(\<forall>d \<in> set zs. snd d = 63) = False\<close>
            using p(3, 4) by auto
          have n64: \<open>e < 64 \<longleftrightarrow> e \<le> (63 :: nat)\<close> for e
            by presburger
          have xy: \<open>x < y\<close>
            using p(1, 2) by simp
          have ym: \<open>x \<le> y - Suc 0\<close> \<open>(d \<le> y - Suc 0) = (d < y)\<close>
            using xy by arith+
          show ?thesis
            using p(3, 4) lo0 xys(2) xy
            apply (simp add: e1 n64 ym order_le_less)
            apply (cases \<open>d < y\<close>; cases \<open>d = y\<close>)
               apply auto
            done
        qed
        subgoal premises p
        proof -
          have e1: \<open>(\<exists>d \<in> set zs. 0 < fst d) = True\<close> \<open>(\<exists>d \<in> set zs. snd d \<noteq> 63) = False\<close>
            \<open>(\<forall>d \<in> set zs. fst d = 0) = False\<close> \<open>(\<forall>d \<in> set zs. snd d = 63) = True\<close>
            using p(3, 4) by auto
          have n64: \<open>e < 64 \<longleftrightarrow> e \<le> (63 :: nat)\<close> for e
            by presburger
          have hv': \<open>length es = n \<Longrightarrow> \<forall>e \<in> set es. e < 64 \<Longrightarrow>
              digits_val es \<le> digits_val (map snd zs)\<close>
            using hv[OF p(4)] by blast
          show ?thesis
            using p(1, 2, 3, 4) xys(2) hv' by (simp add: e1 n64) (auto simp: n64 less_le)
        qed
        subgoal premises p
        proof -
          have e1: \<open>(\<exists>d \<in> set zs. 0 < fst d) = True\<close> \<open>(\<exists>d \<in> set zs. snd d \<noteq> 63) = True\<close>
            \<open>(\<forall>d \<in> set zs. fst d = 0) = False\<close> \<open>(\<forall>d \<in> set zs. snd d = 63) = False\<close>
            using p(3, 4) by auto
          have n64: \<open>e < 64 \<longleftrightarrow> e \<le> (63 :: nat)\<close> for e
            by presburger
          show ?thesis
            using p(1, 2, 3, 4) xys(2) by (simp add: e1 n64) (auto simp: n64 less_le)
        qed
        done
      done
  qed
qed

theorem seqs_digit_ranges:
  assumes \<open>\<forall>(a, b) \<in> set (tl xys). a < 64 \<and> b < 64\<close>
  shows \<open>ds \<in> seqs (digit_ranges xys) \<longleftrightarrow> length ds = length xys \<and> (\<forall>d \<in> set (tl ds). d < 64) \<and>
    digits_val (map fst xys) \<le> digits_val ds \<and> digits_val ds \<le> digits_val (map snd xys)\<close>
  using seqs_digit_ranges_aux[OF refl assms] .

text \<open>The first interval of each product lies between the first digits of the bounds, and
  the others below \<open>64\<close>:\<close>

lemma digit_ranges_bounds:
  assumes \<open>r \<in> set (digit_ranges xys)\<close> \<open>\<forall>(a, b) \<in> set (tl xys). a < 64 \<and> b < 64\<close>
  shows \<open>length r = length xys \<and> (\<forall>(l, h) \<in> set (tl r). h < 64) \<and>
    (\<forall>x y l h. hd xys = (x, y) \<longrightarrow> hd r = (l, h) \<longrightarrow> x \<le> l \<and> h \<le> y)\<close>
  using assms
proof (induction xys arbitrary: r rule: digit_ranges.induct[case_names Nil Cons])
  case Nil
  then show ?case
    by simp
next
  case (Cons x y ds)
  note IH_same = Cons.IH(1) and IH_lo = Cons.IH(2) and IH_hi = Cons.IH(3)
  note pr = Cons.prems
  have all64: \<open>\<forall>(l, h) \<in> set r'. h < 64\<close>
    if \<open>length r' = length ds'\<close> \<open>\<forall>(l, h) \<in> set (tl r'). h < 64\<close>
      \<open>\<forall>x y l h. hd ds' = (x, y) \<longrightarrow> hd r' = (l, h) \<longrightarrow> x \<le> l \<and> h \<le> y\<close>
      \<open>\<forall>(a, b) \<in> set ds'. b < 64\<close> for r' ds' :: \<open>(nat \<times> nat) list\<close>
    using that
    by (cases ds'; cases r') force+
  have ds64: \<open>\<forall>(a, b) \<in> set ds. a < 64 \<and> b < 64\<close>
    using pr(2) by simp
  have n63: \<open>(63::nat) < 64\<close>
    by arith
  have tl64: \<open>\<forall>(a, b) \<in> set (tl ds). a < 64 \<and> b < 64\<close>
    using ds64 by (cases ds) auto
  show ?case
  proof (cases \<open>y < x\<close>)
    case True
    then show ?thesis
      using pr(1) by simp
  next
    case F1: False
    show ?thesis
    proof (cases \<open>x = y\<close>)
      case True
      obtain r' where r: \<open>r = (x, x) # r'\<close> and r': \<open>r' \<in> set (digit_ranges ds)\<close>
        using pr(1) F1 True by auto
      have ih: \<open>length r' = length ds \<and> (\<forall>(l, h) \<in> set (tl r'). h < 64) \<and>
          (\<forall>x y l h. hd ds = (x, y) \<longrightarrow> hd r' = (l, h) \<longrightarrow> x \<le> l \<and> h \<le> y)\<close>
        using IH_same[OF F1 True r' tl64] .
      have \<open>\<forall>(l, h) \<in> set r'. h < 64\<close>
        using all64[of r' ds] ih ds64 by auto
      then show ?thesis
        using ih r F1 by simp
    next
      case F2: False
      obtain lo where lo: \<open>lo = (\<forall>d \<in> set ds. fst d = 0)\<close> by simp
      obtain hi where hi: \<open>hi = (\<forall>d \<in> set ds. snd d = 63)\<close> by simp
      have mem: \<open>r \<in> set ((if lo then [] else map ((#) (x, x))
            (digit_ranges (map (\<lambda>(a, _). (a, 63)) ds))) @
          (if (if lo then x else Suc x) \<le> (if hi then y else y - 1)
           then [((if lo then x else Suc x), (if hi then y else y - 1)) # map (\<lambda>_. (0, 63)) ds]
           else []) @
          (if hi then [] else map ((#) (y, y)) (digit_ranges (map (\<lambda>(_, b). (0, b)) ds))))\<close>
        using pr(1) F1 F2 unfolding lo hi by (simp add: Let_def)
      consider (a) r' where \<open>\<not> lo\<close> \<open>r = (x, x) # r'\<close>
          \<open>r' \<in> set (digit_ranges (map (\<lambda>(a, _). (a, 63)) ds))\<close>
        | (b) \<open>(if lo then x else Suc x) \<le> (if hi then y else y - 1)\<close>
          \<open>r = ((if lo then x else Suc x), (if hi then y else y - 1)) # map (\<lambda>_. (0, 63)) ds\<close>
        | (c) r' where \<open>\<not> hi\<close> \<open>r = (y, y) # r'\<close>
          \<open>r' \<in> set (digit_ranges (map (\<lambda>(_, b). (0, b)) ds))\<close>
        using mem by (auto split: if_splits)
      then show ?thesis
      proof cases
        case a
        have tlm: \<open>\<forall>(a, b) \<in> set (tl (map (\<lambda>(a, _). (a, 63::nat)) ds)). a < 64 \<and> b < 64\<close>
          using tl64 by (cases ds) (auto intro: n63)
        note ih = IH_lo[OF F1 F2 lo hi refl refl a(1) a(3) tlm]
        have \<open>\<forall>(l, h) \<in> set r'. h < 64\<close>
          by (rule all64[of r' \<open>map (\<lambda>(a, _). (a, 63::nat)) ds\<close>]) (use ih n63 in auto)
        then show ?thesis
          using ih a(2) F1 by simp
      next
        case b
        then show ?thesis
          using F1 by (auto split: if_splits)
      next
        case c
        have tlm: \<open>\<forall>(a, b) \<in> set (tl (map (\<lambda>(_, b). (0::nat, b)) ds)). a < 64 \<and> b < 64\<close>
          using tl64 by (cases ds) auto
        note ih = IH_hi[OF F1 F2 lo hi refl refl c(1) c(3) tlm]
        have \<open>\<forall>(l, h) \<in> set r'. h < 64\<close>
          by (rule all64[of r' \<open>map (\<lambda>(_, b). (0::nat, b)) ds\<close>]) (use ih ds64 in auto)
        then show ?thesis
          using ih c(2) F1 by simp
      qed
    qed
  qed
qed

subsection \<open>Intervals of codepoints\<close>

text \<open>The valid codepoints fall into five intervals, on each of which the encoding has
  one length:\<close>

definition utf8_pieces :: \<open>(nat \<times> nat \<times> nat) list\<close> where
  \<open>utf8_pieces = [(1, 0, 0x7F), (2, 0x80, 0x7FF), (3, 0x800, 0xD7FF), (3, 0xE000, 0xFFFF),
    (4, 0x10000, 0x10FFFF)]\<close>

definition byte_range :: \<open>nat \<Rightarrow> nat \<times> nat \<Rightarrow> char \<times> char\<close> where
  \<open>byte_range k r = (case r of (l, h) \<Rightarrow> (char_of (k + l), char_of (k + h)))\<close>

definition byte_ranges :: \<open>nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (char \<times> char) list\<close> where
  \<open>byte_ranges n rs = (case rs of [] \<Rightarrow> []
     | r # rs' \<Rightarrow> byte_range (lead n) r # map (byte_range 0x80) rs')\<close>

text \<open>A codepoint interval as sequences of byte intervals:\<close>

definition utf8_ranges :: \<open>nat \<times> nat \<Rightarrow> (char \<times> char) list list\<close> where
  \<open>utf8_ranges ab = (case ab of (a, b) \<Rightarrow>
     concat [map (byte_ranges n) (digit_ranges (zip (digits n (max a lo)) (digits n (min b hi)))).
       (n, lo, hi) \<leftarrow> utf8_pieces, max a lo \<le> min b hi])\<close>

text \<open>A byte interval below \<open>256\<close> is the interval of the numbers it stands for:\<close>

lemma byte_in:
  fixes k l h :: nat
  assumes \<open>k + h < 256\<close> \<open>l \<le> h\<close>
  shows \<open>char_of (k + l) \<le> b \<and> b \<le> char_of (k + h) \<longleftrightarrow>
    (\<exists>d. l \<le> d \<and> d \<le> h \<and> b = char_of (k + d))\<close>
proof -
  have ofc: \<open>of_char (char_of (x::nat)) = (x::nat)\<close> if \<open>x < 256\<close> for x
    using that by simp
  have kl: \<open>k + l < 256\<close>
    using assms by arith
  note ofcs = ofc[OF kl] ofc[OF assms(1)]
  show ?thesis
  proof
    assume *: \<open>char_of (k + l) \<le> b \<and> b \<le> char_of (k + h)\<close>
    then have \<open>k + l \<le> of_char b\<close> \<open>of_char b \<le> k + h\<close>
      using ofcs by (simp_all add: less_eq_char_def)
    moreover have \<open>b = char_of (of_char b)\<close>
      by simp
    ultimately show \<open>\<exists>d. l \<le> d \<and> d \<le> h \<and> b = char_of (k + d)\<close>
      by (intro exI[of _ \<open>of_char b - k\<close>]) auto
  next
    assume \<open>\<exists>d. l \<le> d \<and> d \<le> h \<and> b = char_of (k + d)\<close>
    then obtain d where d: \<open>l \<le> d\<close> \<open>d \<le> h\<close> \<open>b = char_of (k + d)\<close>
      by blast
    then show \<open>char_of (k + l) \<le> b \<and> b \<le> char_of (k + h)\<close>
      using ofc assms by (simp add: less_eq_char_def)
  qed
qed

text \<open>The tail of byte intervals:\<close>

lemma in_ranges_map_byte_range:
  assumes \<open>\<forall>(l, h) \<in> set rs. l \<le> h \<and> h < 64\<close>
  shows \<open>in_ranges bs (map (byte_range 0x80) rs) \<longleftrightarrow>
    (\<exists>ds. in_ranges ds rs \<and> bs = map (\<lambda>d. char_of (0x80 + d)) ds)\<close>
  using assms
proof (induct rs arbitrary: bs)
  case Nil
  then show ?case
    by (cases bs) (auto simp: in_ranges_def)
next
  case (Cons r rs)
  obtain l h where r: \<open>r = (l, h)\<close>
    by force
  with Cons.prems have lh: \<open>l \<le> h\<close> \<open>h < 64\<close> and rs: \<open>\<forall>(l, h) \<in> set rs. l \<le> h \<and> h < 64\<close>
    by auto
  have bi: \<open>char_of (0x80 + l) \<le> b \<and> b \<le> char_of (0x80 + h) \<longleftrightarrow>
      (\<exists>d. l \<le> d \<and> d \<le> h \<and> b = char_of (0x80 + d))\<close> for b
    using byte_in[of \<open>0x80\<close> h l b] lh by simp
  have \<open>in_ranges bs (map (byte_range 0x80) (r # rs)) \<longleftrightarrow>
      (\<exists>b es. bs = b # es \<and> (char_of (0x80 + l) \<le> b \<and> b \<le> char_of (0x80 + h)) \<and>
        in_ranges es (map (byte_range 0x80) rs))\<close>
    by (simp add: r byte_range_def in_ranges_Cons[of _ \<open>char_of (0x80 + l)\<close>])
  also have \<open>\<dots> \<longleftrightarrow> (\<exists>d ds. l \<le> d \<and> d \<le> h \<and> in_ranges ds rs \<and>
        bs = char_of (0x80 + d) # map (\<lambda>d. char_of (0x80 + d)) ds)\<close>
    unfolding bi Cons.hyps[OF rs] by (auto simp: eq_commute)
  also have \<open>\<dots> \<longleftrightarrow> (\<exists>ds. in_ranges ds (r # rs) \<and> bs = map (\<lambda>d. char_of (0x80 + d)) ds)\<close>
    by (simp add: r in_ranges_Cons) fastforce
  finally show ?case .
qed

text \<open>Each interval of a product is non-empty:\<close>

lemma digit_ranges_le:
  assumes \<open>r \<in> set (digit_ranges xys)\<close>
  shows \<open>\<forall>(l, h) \<in> set r. l \<le> h\<close>
  using assms
proof (induction xys arbitrary: r rule: digit_ranges.induct[case_names Nil Cons])
  case Nil
  then show ?case
    by simp
next
  case (Cons x y ds)
  note IH_same = Cons.IH(1) and IH_lo = Cons.IH(2) and IH_hi = Cons.IH(3)
  note pr = Cons.prems
  show ?case
  proof (cases \<open>y < x\<close>)
    case True
    then show ?thesis
      using pr by simp
  next
    case F1: False
    show ?thesis
    proof (cases \<open>x = y\<close>)
      case True
      obtain r' where r: \<open>r = (x, x) # r'\<close> and r': \<open>r' \<in> set (digit_ranges ds)\<close>
        using pr F1 True by auto
      have \<open>\<forall>(l, h) \<in> set r'. l \<le> h\<close>
        using IH_same F1 True r' by blast
      then show ?thesis
        using r by simp
    next
      case F2: False
      obtain lo where lo: \<open>lo = (\<forall>d \<in> set ds. fst d = 0)\<close> by simp
      obtain hi where hi: \<open>hi = (\<forall>d \<in> set ds. snd d = 63)\<close> by simp
      have mem: \<open>r \<in> set ((if lo then [] else map ((#) (x, x))
            (digit_ranges (map (\<lambda>(a, _). (a, 63)) ds))) @
          (if (if lo then x else Suc x) \<le> (if hi then y else y - 1)
           then [((if lo then x else Suc x), (if hi then y else y - 1)) # map (\<lambda>_. (0, 63)) ds]
           else []) @
          (if hi then [] else map ((#) (y, y)) (digit_ranges (map (\<lambda>(_, b). (0, b)) ds))))\<close>
        using pr F1 F2 unfolding lo hi by (simp add: Let_def)
      consider (a) r' where \<open>\<not> lo\<close> \<open>r = (x, x) # r'\<close>
          \<open>r' \<in> set (digit_ranges (map (\<lambda>(a, _). (a, 63)) ds))\<close>
        | (b) \<open>(if lo then x else Suc x) \<le> (if hi then y else y - 1)\<close>
          \<open>r = ((if lo then x else Suc x), (if hi then y else y - 1)) # map (\<lambda>_. (0, 63)) ds\<close>
        | (c) r' where \<open>\<not> hi\<close> \<open>r = (y, y) # r'\<close>
          \<open>r' \<in> set (digit_ranges (map (\<lambda>(_, b). (0, b)) ds))\<close>
        using mem by (auto split: if_splits)
      then show ?thesis
      proof cases
        case a
        have \<open>\<forall>(l, h) \<in> set r'. l \<le> h\<close>
          using IH_lo[OF F1 F2 lo hi refl refl a(1) a(3)] .
        then show ?thesis
          using a(2) by simp
      next
        case b
        then show ?thesis
          by (auto split: if_splits)
      next
        case c
        have \<open>\<forall>(l, h) \<in> set r'. l \<le> h\<close>
          using IH_hi[OF F1 F2 lo hi refl refl c(1) c(3)] .
        then show ?thesis
          using c(2) by simp
      qed
    qed
  qed
qed

text \<open>A product of byte intervals matches the bytes of the digit strings of the product:\<close>

lemma in_ranges_byte_ranges:
  assumes \<open>lead n + h < 256\<close> \<open>l \<le> h\<close> \<open>\<forall>(l, h) \<in> set rs. l \<le> h \<and> h < 64\<close>
  shows \<open>in_ranges bs (byte_ranges n ((l, h) # rs)) \<longleftrightarrow>
    (\<exists>ds. in_ranges ds ((l, h) # rs) \<and> bs = bytes_of n ds)\<close>
proof -
  have bi: \<open>char_of (lead n + l) \<le> b \<and> b \<le> char_of (lead n + h) \<longleftrightarrow>
      (\<exists>d. l \<le> d \<and> d \<le> h \<and> b = char_of (lead n + d))\<close> for b
    using byte_in[OF assms(1, 2)] .
  have \<open>in_ranges bs (byte_ranges n ((l, h) # rs)) \<longleftrightarrow>
      (\<exists>b es. bs = b # es \<and> (char_of (lead n + l) \<le> b \<and> b \<le> char_of (lead n + h)) \<and>
        in_ranges es (map (byte_range 0x80) rs))\<close>
    by (simp add: byte_ranges_def byte_range_def in_ranges_Cons[of _ \<open>char_of (lead n + l)\<close>])
  also have \<open>\<dots> \<longleftrightarrow> (\<exists>d ds. l \<le> d \<and> d \<le> h \<and> in_ranges ds rs \<and>
        bs = char_of (lead n + d) # map (\<lambda>d. char_of (0x80 + d)) ds)\<close>
    unfolding bi in_ranges_map_byte_range[OF assms(3)] by (auto simp: eq_commute)
  also have \<open>\<dots> \<longleftrightarrow> (\<exists>ds. in_ranges ds ((l, h) # rs) \<and> bs = bytes_of n ds)\<close>
    by (simp add: in_ranges_Cons bytes_of_def) fastforce
  finally show ?thesis .
qed

text \<open>One piece of the codepoint intervals:\<close>

lemma seqs_piece:
  assumes \<open>0 < n\<close> \<open>a' \<le> b'\<close> \<open>lead n + hd (digits n b') < 256\<close>
  shows \<open>bs \<in> seqs (map (byte_ranges n) (digit_ranges (zip (digits n a') (digits n b')))) \<longleftrightarrow>
    (\<exists>c. a' \<le> c \<and> c \<le> b' \<and> bs = bytes_of n (digits n c))\<close>
proof -
  obtain x xs where xs: \<open>digits n a' = x # xs\<close>
    using assms(1) length_digits[of n a'] by (cases \<open>digits n a'\<close>) auto
  obtain y ys where ys: \<open>digits n b' = y # ys\<close>
    using assms(1) length_digits[of n b'] by (cases \<open>digits n b'\<close>) auto
  have lens: \<open>length xs = length ys\<close>
    using length_digits[of n a'] length_digits[of n b'] xs ys by simp
  define xys where \<open>xys = zip (digits n a') (digits n b')\<close>
  have xys: \<open>xys = (x, y) # zip xs ys\<close>
    by (simp add: xys_def xs ys)
  have tl64: \<open>\<forall>(a, b) \<in> set (tl xys). a < 64 \<and> b < 64\<close>
  proof -
    have \<open>\<forall>a \<in> set xs. a < 64\<close> \<open>\<forall>b \<in> set ys. b < 64\<close>
      using digits_tl_less[of _ n a'] digits_tl_less[of _ n b'] xs ys by auto
    then show ?thesis
      using xys by (auto dest: set_zip_leftD set_zip_rightD)
  qed
  have hdy: \<open>y = hd (digits n b')\<close>
    by (simp add: ys)
  have step: \<open>bs \<in> seqs (map (byte_ranges n) (digit_ranges xys)) \<longleftrightarrow>
      (\<exists>ds. ds \<in> seqs (digit_ranges xys) \<and> bs = bytes_of n ds)\<close>
  proof -
    have \<open>in_ranges bs (byte_ranges n r) \<longleftrightarrow> (\<exists>ds. in_ranges ds r \<and> bs = bytes_of n ds)\<close>
      if r: \<open>r \<in> set (digit_ranges xys)\<close> for r
    proof -
      note b = digit_ranges_bounds[OF r tl64] digit_ranges_le[OF r]
      obtain l h rs where lh: \<open>r = (l, h) # rs\<close>
        using b(1) xys by (cases r) auto
      have \<open>h \<le> y\<close>
        using b(1) lh xys by auto
      moreover have \<open>l \<le> h\<close> \<open>\<forall>(l, h) \<in> set rs. l \<le> h \<and> h < 64\<close>
        using b lh by auto
      ultimately show ?thesis
        using in_ranges_byte_ranges[of n h l rs bs] assms(3) hdy lh by simp
    qed
    then show ?thesis
      by (auto simp: seqs_def)
  qed
  have \<open>(\<exists>ds. ds \<in> seqs (digit_ranges xys) \<and> bs = bytes_of n ds) \<longleftrightarrow>
      (\<exists>c. a' \<le> c \<and> c \<le> b' \<and> bs = bytes_of n (digits n c))\<close>
  proof -
    have mf: \<open>map fst xys = digits n a'\<close> \<open>map snd xys = digits n b'\<close>
      using length_digits[of n a'] length_digits[of n b'] by (simp_all add: xys_def)
    have lx: \<open>length xys = n\<close>
      by (simp add: xys_def)
    have va: \<open>digits_val (digits n a') = a'\<close> and vb: \<open>digits_val (digits n b') = b'\<close>
      using assms(1) by simp_all
    show ?thesis
      unfolding seqs_digit_ranges[OF tl64] mf lx va vb
    proof (intro iffI)
      assume \<open>\<exists>ds. (length ds = n \<and> (\<forall>d \<in> set (tl ds). d < 64) \<and> a' \<le> digits_val ds \<and>
          digits_val ds \<le> b') \<and> bs = bytes_of n ds\<close>
      then obtain ds where ds: \<open>length ds = n\<close> \<open>\<forall>d \<in> set (tl ds). d < 64\<close> \<open>a' \<le> digits_val ds\<close>
        \<open>digits_val ds \<le> b'\<close> \<open>bs = bytes_of n ds\<close>
        by blast
      then show \<open>\<exists>c. a' \<le> c \<and> c \<le> b' \<and> bs = bytes_of n (digits n c)\<close>
        using digits_digits_val[OF ds(1) assms(1) ds(2)] by (intro exI[of _ \<open>digits_val ds\<close>]) simp
    next
      assume \<open>\<exists>c. a' \<le> c \<and> c \<le> b' \<and> bs = bytes_of n (digits n c)\<close>
      then obtain c where c: \<open>a' \<le> c\<close> \<open>c \<le> b'\<close> \<open>bs = bytes_of n (digits n c)\<close>
        by blast
      then show \<open>\<exists>ds. (length ds = n \<and> (\<forall>d \<in> set (tl ds). d < 64) \<and> a' \<le> digits_val ds \<and>
          digits_val ds \<le> b') \<and> bs = bytes_of n ds\<close>
        using assms(1) digits_tl_less by (intro exI[of _ \<open>digits n c\<close>]) auto
    qed
  qed
  with step show ?thesis
    by (simp add: xys_def)
qed

text \<open>On each piece the encoding has the piece's length, the first byte stays below \<open>256\<close>, and
  every valid codepoint lies in some piece:\<close>

lemma utf8_pieces_props:
  assumes \<open>(n, lo, hi) \<in> set utf8_pieces\<close>
  shows \<open>0 < n\<close> \<open>c \<le> hi \<Longrightarrow> lead n + hd (digits n c) < 256\<close>
    \<open>lo \<le> c \<Longrightarrow> c \<le> hi \<Longrightarrow> cp_len c = n \<and> is_valid_cp c\<close>
proof -
  have cs: \<open>n = 1 \<and> lo = 0 \<and> hi = 0x7F \<or> n = 2 \<and> lo = 0x80 \<and> hi = 0x7FF \<or>
      n = 3 \<and> lo = 0x800 \<and> hi = 0xD7FF \<or> n = 3 \<and> lo = 0xE000 \<and> hi = 0xFFFF \<or>
      n = 4 \<and> lo = 0x10000 \<and> hi = 0x10FFFF\<close>
    using assms by (simp add: utf8_pieces_def)
  have d1: \<open>digits 1 c = [c]\<close> for c
    by (simp add: numeral_1_eq_Suc_0)
  have d2: \<open>digits 2 c = [c div 64, c mod 64]\<close> for c
    by (simp add: numeral_2_eq_2 numeral_1_eq_Suc_0)
  have d3: \<open>digits 3 c = [c div 64 div 64, c div 64 mod 64, c mod 64]\<close> for c
    by (simp add: numeral_3_eq_3 numeral_2_eq_2 numeral_1_eq_Suc_0)
  have d4: \<open>digits 4 c =
      [c div 64 div 64 div 64, c div 64 div 64 mod 64, c div 64 mod 64, c mod 64]\<close> for c
  proof -
    have e: \<open>(4::nat) = Suc (Suc 2)\<close> by simp
    have ds: \<open>digits (Suc (Suc n)) c = digits (Suc n) (c div 64) @ [c mod 64]\<close> for n c
      by simp
    show ?thesis
      by (subst e, subst ds, simp add: d3)
  qed
  show \<open>0 < n\<close>
    using cs by auto
  show \<open>lead n + hd (digits n c) < 256\<close> if \<open>c \<le> hi\<close>
    using cs
  proof (elim disjE conjE)
    assume n: \<open>n = 1\<close> and \<open>lo = 0\<close> and h: \<open>hi = 0x7F\<close>
    show ?thesis by (insert that h, simp add: n d1 lead_def)
  next
    assume n: \<open>n = 2\<close> and \<open>lo = 0x80\<close> and h: \<open>hi = 0x7FF\<close>
    show ?thesis by (insert that h, simp add: n d2 lead_def; arith)
  next
    assume n: \<open>n = 3\<close> and \<open>lo = 0x800\<close> and h: \<open>hi = 0xD7FF\<close>
    show ?thesis by (insert that h, simp add: n d3 lead_def; arith)
  next
    assume n: \<open>n = 3\<close> and \<open>lo = 0xE000\<close> and h: \<open>hi = 0xFFFF\<close>
    show ?thesis by (insert that h, simp add: n d3 lead_def; arith)
  next
    assume n: \<open>n = 4\<close> and \<open>lo = 0x10000\<close> and h: \<open>hi = 0x10FFFF\<close>
    show ?thesis by (insert that h, simp add: n d4 lead_def; arith)
  qed
  show \<open>cp_len c = n \<and> is_valid_cp c\<close> if \<open>lo \<le> c\<close> \<open>c \<le> hi\<close>
    using cs
  proof (elim disjE conjE)
    assume n: \<open>n = 1\<close> and l: \<open>lo = 0\<close> and h: \<open>hi = 0x7F\<close>
    show ?thesis by (insert that l h, simp add: n cp_len_def is_valid_cp_def; arith)
  next
    assume n: \<open>n = 2\<close> and l: \<open>lo = 0x80\<close> and h: \<open>hi = 0x7FF\<close>
    show ?thesis by (insert that l h, simp add: n cp_len_def is_valid_cp_def; arith)
  next
    assume n: \<open>n = 3\<close> and l: \<open>lo = 0x800\<close> and h: \<open>hi = 0xD7FF\<close>
    show ?thesis by (insert that l h, simp add: n cp_len_def is_valid_cp_def; arith)
  next
    assume n: \<open>n = 3\<close> and l: \<open>lo = 0xE000\<close> and h: \<open>hi = 0xFFFF\<close>
    show ?thesis by (insert that l h, simp add: n cp_len_def is_valid_cp_def; arith)
  next
    assume n: \<open>n = 4\<close> and l: \<open>lo = 0x10000\<close> and h: \<open>hi = 0x10FFFF\<close>
    show ?thesis by (insert that l h, simp add: n cp_len_def is_valid_cp_def; arith)
  qed
qed

lemma is_valid_cp_piece:
  assumes \<open>is_valid_cp c\<close>
  obtains n lo hi where \<open>(n, lo, hi) \<in> set utf8_pieces\<close> \<open>lo \<le> c\<close> \<open>c \<le> hi\<close>
proof -
  have d: \<open>c \<le> 0x7F \<or> (0x80 \<le> c \<and> c \<le> 0x7FF) \<or> (0x800 \<le> c \<and> c \<le> 0xD7FF) \<or>
      (0xE000 \<le> c \<and> c \<le> 0xFFFF) \<or> (0x10000 \<le> c \<and> c \<le> 0x10FFFF)\<close>
    using assms unfolding is_valid_cp_def by arith
  from d show thesis
  proof (elim disjE conjE)
    assume h: \<open>c \<le> 0x7F\<close>
    show thesis by (rule that[of 1 0 \<open>0x7F\<close>]) (simp_all add: utf8_pieces_def h)
  next
    assume h1: \<open>0x80 \<le> c\<close> and h2: \<open>c \<le> 0x7FF\<close>
    show thesis by (rule that[of 2 \<open>0x80\<close> \<open>0x7FF\<close>]) (simp_all add: utf8_pieces_def h1 h2)
  next
    assume h1: \<open>0x800 \<le> c\<close> and h2: \<open>c \<le> 0xD7FF\<close>
    show thesis by (rule that[of 3 \<open>0x800\<close> \<open>0xD7FF\<close>]) (simp_all add: utf8_pieces_def h1 h2)
  next
    assume h1: \<open>0xE000 \<le> c\<close> and h2: \<open>c \<le> 0xFFFF\<close>
    show thesis by (rule that[of 3 \<open>0xE000\<close> \<open>0xFFFF\<close>]) (simp_all add: utf8_pieces_def h1 h2)
  next
    assume h1: \<open>0x10000 \<le> c\<close> and h2: \<open>c \<le> 0x10FFFF\<close>
    show thesis by (rule that[of 4 \<open>0x10000\<close> \<open>0x10FFFF\<close>]) (simp_all add: utf8_pieces_def h1 h2)
  qed
qed

theorem seqs_utf8_ranges:
  \<open>bs \<in> seqs (utf8_ranges (a, b)) \<longleftrightarrow>
    (\<exists>c. a \<le> c \<and> c \<le> b \<and> is_valid_cp c \<and> bs = utf8_encode_cp c)\<close>
proof -
  have \<open>bs \<in> seqs (utf8_ranges (a, b)) \<longleftrightarrow>
      (\<exists>n lo hi. (n, lo, hi) \<in> set utf8_pieces \<and> max a lo \<le> min b hi \<and>
        bs \<in> seqs (map (byte_ranges n)
          (digit_ranges (zip (digits n (max a lo)) (digits n (min b hi))))))\<close>
    by (simp add: utf8_ranges_def seqs_def set_concat split_def
        Bex_def split_paired_Ex del: max.bounded_iff min.bounded_iff)
  also have \<open>\<dots> \<longleftrightarrow> (\<exists>n lo hi. (n, lo, hi) \<in> set utf8_pieces \<and> max a lo \<le> min b hi \<and>
      (\<exists>c. max a lo \<le> c \<and> c \<le> min b hi \<and> bs = bytes_of n (digits n c)))\<close>
  proof -
    have \<open>bs \<in> seqs (map (byte_ranges n)
          (digit_ranges (zip (digits n (max a lo)) (digits n (min b hi))))) \<longleftrightarrow>
        (\<exists>c. max a lo \<le> c \<and> c \<le> min b hi \<and> bs = bytes_of n (digits n c))\<close>
      if \<open>(n, lo, hi) \<in> set utf8_pieces\<close> \<open>max a lo \<le> min b hi\<close> for n lo hi
      using seqs_piece[OF utf8_pieces_props(1)[OF that(1)] that(2)
          utf8_pieces_props(2)[OF that(1) min.cobounded2]] .
    then show ?thesis
      by blast
  qed
  also have \<open>\<dots> \<longleftrightarrow> (\<exists>c. a \<le> c \<and> c \<le> b \<and> is_valid_cp c \<and> bs = utf8_encode_cp c)\<close>
  proof
    assume \<open>\<exists>n lo hi. (n, lo, hi) \<in> set utf8_pieces \<and> max a lo \<le> min b hi \<and>
      (\<exists>c. max a lo \<le> c \<and> c \<le> min b hi \<and> bs = bytes_of n (digits n c))\<close>
    then obtain n lo hi c where p: \<open>(n, lo, hi) \<in> set utf8_pieces\<close> \<open>max a lo \<le> c\<close>
      \<open>c \<le> min b hi\<close> \<open>bs = bytes_of n (digits n c)\<close>
      by blast
    then have \<open>cp_len c = n\<close> \<open>is_valid_cp c\<close>
      using utf8_pieces_props(3)[OF p(1)] by auto
    with p show \<open>\<exists>c. a \<le> c \<and> c \<le> b \<and> is_valid_cp c \<and> bs = utf8_encode_cp c\<close>
      by (intro exI[of _ c]) (auto simp: utf8_encode_cp_def)
  next
    assume \<open>\<exists>c. a \<le> c \<and> c \<le> b \<and> is_valid_cp c \<and> bs = utf8_encode_cp c\<close>
    then obtain c where c: \<open>a \<le> c\<close> \<open>c \<le> b\<close> \<open>is_valid_cp c\<close> \<open>bs = utf8_encode_cp c\<close>
      by blast
    from is_valid_cp_piece[OF c(3)] obtain n lo hi where p: \<open>(n, lo, hi) \<in> set utf8_pieces\<close>
      \<open>lo \<le> c\<close> \<open>c \<le> hi\<close> .
    have \<open>cp_len c = n\<close>
      using utf8_pieces_props(3)[OF p] by simp
    with p c show \<open>\<exists>n lo hi. (n, lo, hi) \<in> set utf8_pieces \<and> max a lo \<le> min b hi \<and>
        (\<exists>c. max a lo \<le> c \<and> c \<le> min b hi \<and> bs = bytes_of n (digits n c))\<close>
      by (intro exI[of _ n] exI[of _ lo] exI[of _ hi])
        (auto simp: utf8_encode_cp_def intro!: exI[of _ c])
  qed
  finally show ?thesis .
qed

end
