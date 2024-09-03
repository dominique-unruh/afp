theory DBM
  imports 
    Floyd_Warshall.Floyd_Warshall 
    HOL.Real
begin

type_synonym ('c, 't) cval = "'c \<Rightarrow> 't"

chapter \<open>Difference Bound Matrices\<close>

section \<open>Definitions\<close>

subsection \<open>Definition and Semantics of DBMs\<close>
text \<open>
  Difference Bound Matrices (DBMs) constrain differences of clocks
  (or more precisely, the difference of values assigned to individual clocks by a valuation).
  The possible constraints are given by the following datatype:
\<close>
datatype 't DBMEntry = Le 't | Lt 't | INF ("\<infinity>")

text \<open>\noindent This yields a simple definition of DBMs:\<close>

type_synonym 't DBM = "nat \<Rightarrow> nat \<Rightarrow> 't DBMEntry"

text \<open>\noindent
  To relate clocks with rows and columns of
  a DBM, we use a clock numbering \<open>v\<close> of type @{typ "'c \<Rightarrow> nat"} to map clocks to indices.
  DBMs will regularly be  accompanied by a natural number $n$,
  which designates the number of clocks constrained by the matrix.
  To be able to represent the full set of clock constraints with DBMs, we add an imaginary
  clock \<open>\<zero>\<close>, which shall be assigned to 0 in every valuation.
  In the following predicate we explicitly keep track of \<open>\<zero>\<close>.
\<close>

class time = linordered_ab_group_add +
  assumes dense: "x < y \<Longrightarrow> \<exists>z. x < z \<and> z < y"
  assumes non_trivial: "\<exists> x. x \<noteq> 0"

begin

lemma non_trivial_neg: "\<exists> x. x < 0"
proof -
  from non_trivial obtain x where x: "x \<noteq> 0" by auto
  show ?thesis
  proof (cases "x < 0")
    case False
    with x have "x > 0" by auto
    then have "(-x) < 0" by auto
    then show ?thesis ..
  qed auto
qed

end

instantiation real :: time
begin
  instance proof
    fix x y :: real
    assume "x < y"
    then show "\<exists>z>x. z < y" using dense_order_class.dense by blast
  next
    have "(1 :: real) \<noteq> 0" by auto
    then show "\<exists>x. (x::real) \<noteq> 0" ..
  qed
end


inductive dbm_entry_val :: "('c, 't) cval \<Rightarrow> 'c option \<Rightarrow> 'c option \<Rightarrow> ('t::time) DBMEntry \<Rightarrow> bool"
where
  "u r \<le> d \<Longrightarrow> dbm_entry_val u (Some r) None (Le d)" |
  "-u c \<le> d \<Longrightarrow> dbm_entry_val u None (Some c) (Le d)" |
  "u r < d \<Longrightarrow> dbm_entry_val u (Some r) None (Lt d)" |
  "-u c < d \<Longrightarrow> dbm_entry_val u None (Some c) (Lt d)" |
  "u r - u c \<le> d \<Longrightarrow> dbm_entry_val u (Some r) (Some c) (Le d)" |
  "u r - u c < d \<Longrightarrow> dbm_entry_val u (Some r) (Some c) (Lt d)" |
  "dbm_entry_val _ _ _ \<infinity>"

declare dbm_entry_val.intros[intro]
inductive_cases[elim!]: "dbm_entry_val u None (Some c) (Le d)"
inductive_cases[elim!]: "dbm_entry_val u (Some c) None (Le d)"
inductive_cases[elim!]: "dbm_entry_val u None (Some c) (Lt d)"
inductive_cases[elim!]: "dbm_entry_val u (Some c) None (Lt d)"
inductive_cases[elim!]: "dbm_entry_val u (Some r) (Some c) (Le d)"
inductive_cases[elim!]: "dbm_entry_val u (Some r) (Some c) (Lt d)"

fun dbm_entry_bound :: "('t::time) DBMEntry \<Rightarrow> 't"
where
  "dbm_entry_bound (Le t) = t" |
  "dbm_entry_bound (Lt t) = t" |
  "dbm_entry_bound \<infinity> = 0"

inductive dbm_lt :: "('t::linorder) DBMEntry \<Rightarrow> 't DBMEntry \<Rightarrow> bool"
("_ \<prec> _" [51, 51] 50)
where
  "dbm_lt (Lt _) \<infinity>" |
  "dbm_lt (Le _) \<infinity>" |
  "a < b  \<Longrightarrow> dbm_lt (Le a) (Le b)" |
  "a < b  \<Longrightarrow> dbm_lt (Le a) (Lt b)" |
  "a \<le> b  \<Longrightarrow> dbm_lt (Lt a) (Le b)" |
  "a < b  \<Longrightarrow> dbm_lt (Lt a) (Lt b)"

declare dbm_lt.intros[intro]

definition dbm_le :: "('t::linorder) DBMEntry \<Rightarrow> 't DBMEntry \<Rightarrow> bool"
("_ \<preceq> _" [51, 51] 50)
where
  "dbm_le a b \<equiv> (a \<prec> b) \<or> a = b"

text \<open>
  Now a valuation is contained in the zone represented by a DBM if it fulfills all individual
  constraints:
\<close>
definition DBM_val_bounded :: "('c \<Rightarrow> nat) \<Rightarrow> ('c, 't) cval \<Rightarrow> ('t::time) DBM \<Rightarrow> nat \<Rightarrow> bool"
where
  "DBM_val_bounded v u m n \<equiv> Le 0 \<preceq> m 0 0 \<and>
    (\<forall> c. v c \<le> n \<longrightarrow> (dbm_entry_val u None (Some c) (m 0 (v c))
                      \<and> dbm_entry_val u (Some c) None (m (v c) 0)))
    \<and> (\<forall> c1 c2. v c1 \<le> n \<and> v c2 \<le> n \<longrightarrow> dbm_entry_val u (Some c1) (Some c2) (m (v c1) (v c2)))"

abbreviation DBM_val_bounded_abbrev ::
  "('c, 't) cval \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('t::time) DBM \<Rightarrow> bool"
("_ \<turnstile>\<^bsub>_,_\<^esub> _" [48, 48, 48, 48] 48)
where
  "u \<turnstile>\<^bsub>v,n\<^esub> M \<equiv> DBM_val_bounded v u M n"

subsection \<open>Ordering DBM Entries\<close>
abbreviation
  "dmin a b \<equiv> if a \<prec> b then a else b"

lemma dbm_le_dbm_min:
  "a \<preceq> b \<Longrightarrow> a = dmin a b" unfolding dbm_le_def
by auto

lemma dbm_lt_asym:
  assumes "e \<prec> f"
  shows "~ f \<prec> e"
using assms
proof (safe, cases e f rule: dbm_lt.cases, goal_cases)
  case 1 from this(2) show ?case using 1(3-) by (cases f e rule: dbm_lt.cases) auto
next
  case 2 from this(2) show ?case using 2(3-) by (cases f e rule: dbm_lt.cases) auto
next
  case 3 from this(2) show ?case using 3(3-) by (cases f e rule: dbm_lt.cases) auto
next
  case 4 from this(2) show ?case using 4(3-) by (cases f e rule: dbm_lt.cases) auto
next
  case 5 from this(2) show ?case using 5(3-) by (cases f e rule: dbm_lt.cases) auto
next
  case 6 from this(2) show ?case using 6(3-) by (cases f e rule: dbm_lt.cases) auto
qed

lemma dbm_le_dbm_min2:
  "a \<preceq> b \<Longrightarrow> a = dmin b a"
using dbm_lt_asym by (auto simp: dbm_le_def)

lemma dmb_le_dbm_entry_bound_inf:
  "a \<preceq> b \<Longrightarrow> a = \<infinity> \<Longrightarrow> b = \<infinity>"
  by (auto simp: dbm_le_def elim: dbm_lt.cases)

lemma dbm_not_lt_eq: "\<not> a \<prec> b \<Longrightarrow> \<not> b \<prec> a \<Longrightarrow> a = b"
  by (cases a; cases b; fastforce)

lemma dbm_not_lt_impl: "\<not> a \<prec> b \<Longrightarrow> b \<prec> a \<or> a = b" using dbm_not_lt_eq by auto

lemma "dmin a b = dmin b a"
proof (cases "a \<prec> b")
  case True thus ?thesis by (simp add: dbm_lt_asym)
next
  case False thus ?thesis by (simp add: dbm_not_lt_eq)
qed

lemma dbm_lt_trans: "a \<prec> b \<Longrightarrow> b \<prec> c \<Longrightarrow> a \<prec> c"
proof (cases a b rule: dbm_lt.cases, goal_cases)
  case 1 thus ?case by simp
next
  case 2 from this(2-) show ?case by (cases rule: dbm_lt.cases) simp+
next
  case 3 from this(2-) show ?case by (cases rule: dbm_lt.cases) simp+
next
  case 4 from this(2-) show ?case by (cases rule: dbm_lt.cases) auto
next
  case 5 from this(2-) show ?case by (cases rule: dbm_lt.cases) auto
next
  case 6 from this(2-) show ?case by (cases rule: dbm_lt.cases) auto
next
  case 7 from this(2-) show ?case by (cases rule: dbm_lt.cases) auto
qed

lemma aux_3: "\<not> a \<prec> b \<Longrightarrow> \<not> b \<prec> c \<Longrightarrow> a \<prec> c \<Longrightarrow> c = a"
proof goal_cases
  case 1 thus ?case
  proof (cases "c \<prec> b")
    case True
    with \<open>a \<prec> c\<close> have "a \<prec> b" by (rule dbm_lt_trans)
    thus ?thesis using 1 by auto
  next
    case False thus ?thesis using dbm_not_lt_eq 1 by auto
  qed
qed

inductive_cases[elim!]: "\<infinity> \<prec> x"

lemma dbm_lt_asymmetric[simp]: "x \<prec> y \<Longrightarrow> y \<prec> x \<Longrightarrow> False"
by (cases x y rule: dbm_lt.cases) (auto elim: dbm_lt.cases)

lemma le_dbm_le: "Le a \<preceq> Le b \<Longrightarrow> a \<le> b" unfolding dbm_le_def by (auto elim: dbm_lt.cases)

lemma le_dbm_lt: "Le a \<preceq> Lt b \<Longrightarrow> a < b" unfolding dbm_le_def by (auto elim: dbm_lt.cases)

lemma lt_dbm_le: "Lt a \<preceq> Le b \<Longrightarrow> a \<le> b" unfolding dbm_le_def by (auto elim: dbm_lt.cases)

lemma lt_dbm_lt: "Lt a \<preceq> Lt b \<Longrightarrow> a \<le> b" unfolding dbm_le_def by (auto elim: dbm_lt.cases)

lemma not_dbm_le_le_impl: "\<not> Le a \<prec> Le b \<Longrightarrow> a \<ge> b" by (metis dbm_lt.intros(3) not_less)

lemma not_dbm_lt_le_impl: "\<not> Lt a \<prec> Le b \<Longrightarrow> a > b" by (metis dbm_lt.intros(5) not_less)

lemma not_dbm_lt_lt_impl: "\<not> Lt a \<prec> Lt b \<Longrightarrow> a \<ge> b" by (metis dbm_lt.intros(6) not_less)

lemma not_dbm_le_lt_impl: "\<not> Le a \<prec> Lt b \<Longrightarrow> a \<ge> b" by (metis dbm_lt.intros(4) not_less)


subsection \<open>Addition on DBM Entries\<close>

fun dbm_add :: "('t::linordered_cancel_ab_semigroup_add) DBMEntry \<Rightarrow> 't DBMEntry \<Rightarrow> 't DBMEntry" (infixl "\<otimes>" 70)
where
  "dbm_add \<infinity>     _      = \<infinity>" |
  "dbm_add _      \<infinity>     = \<infinity>" |
  "dbm_add (Le a) (Le b) = (Le (a+b))" |
  "dbm_add (Le a) (Lt b) = (Lt (a+b))" |
  "dbm_add (Lt a) (Le b) = (Lt (a+b))" |
  "dbm_add (Lt a) (Lt b) = (Lt (a+b))"

lemma aux_4: "x \<prec> y \<Longrightarrow> \<not> dbm_add x z \<prec> dbm_add y z \<Longrightarrow> dbm_add x z = dbm_add y z"
by (cases x y rule: dbm_lt.cases; cases z; auto)

lemma aux_5: "\<not> x \<prec> y \<Longrightarrow> dbm_add x z \<prec> dbm_add y z \<Longrightarrow> dbm_add y z = dbm_add x z"
proof -
  assume lt: "dbm_add x z \<prec> dbm_add y z" "\<not> x \<prec> y"
  hence "x = y \<or> y \<prec> x" by (auto simp: dbm_not_lt_eq)
  thus ?thesis
  proof
    assume "x = y" thus ?thesis by simp
  next
    assume "y \<prec> x"
    thus ?thesis
    proof (cases y x rule: dbm_lt.cases, goal_cases)
      case 1 thus ?case using lt by auto
    next
      case 2 thus ?case using lt by auto
    next
      case 3 thus ?case using dbm_lt_asymmetric lt(1) by (cases z) fastforce+
    next
      case 4 thus ?case using dbm_lt_asymmetric lt(1) by (cases z) fastforce+
    next
      case 5 thus ?case using dbm_lt_asymmetric lt(1) by (cases z) fastforce+
    next
      case 6 thus ?case using dbm_lt_asymmetric lt(1) by (cases z) fastforce+
    qed
  qed
qed

lemma aux_42: "x \<prec> y \<Longrightarrow> \<not> dbm_add z x \<prec> dbm_add z y \<Longrightarrow> dbm_add z x = dbm_add z y"
by (cases x y rule: dbm_lt.cases) ((cases z), auto)+

lemma aux_52: "\<not> x \<prec> y \<Longrightarrow> dbm_add z x \<prec> dbm_add z y \<Longrightarrow> dbm_add z y = dbm_add z x"
proof -
  assume lt: "dbm_add z x \<prec> dbm_add z y" "\<not> x \<prec> y"
  hence "x = y \<or> y \<prec> x" by (auto simp: dbm_not_lt_eq)
  thus ?thesis
  proof
    assume "x = y" thus ?thesis by simp
  next
    assume "y \<prec> x"
    thus ?thesis
    proof (cases y x rule: dbm_lt.cases, goal_cases)
      case 1 thus ?case using lt by (cases z) fastforce+
    next
      case 2 thus ?case using lt by (cases z) fastforce+
    next
      case 3 thus ?case using dbm_lt_asymmetric lt(1) by (cases z) fastforce+
    next
      case 4 thus ?case using dbm_lt_asymmetric lt(1) by (cases z) fastforce+
    next
      case 5 thus ?case using dbm_lt_asymmetric lt(1) by (cases z) fastforce+
    next
      case 6 thus ?case using dbm_lt_asymmetric lt(1) by (cases z) fastforce+
    qed
  qed
qed

lemma dbm_add_not_inf:
  "a \<noteq> \<infinity> \<Longrightarrow> b \<noteq> \<infinity> \<Longrightarrow> dbm_add a b \<noteq> \<infinity>"
  by (cases a; cases b; auto)

lemma dbm_le_not_inf:
  "a \<preceq> b \<Longrightarrow> b \<noteq> \<infinity> \<Longrightarrow> a \<noteq> \<infinity>"
  by (cases "a = b") (auto simp: dbm_le_def)


subsection \<open>Negation of DBM Entries\<close>

fun neg_dbm_entry where
  "neg_dbm_entry (Le a) = Lt (-a)" |
  "neg_dbm_entry (Lt a) = Le (-a)" |
  "neg_dbm_entry \<infinity> = \<infinity>"
  \<comment> \<open>This case does not make sense but we make this definition for technical convenience.\<close>

lemma neg_entry:
  "{u. \<not> dbm_entry_val u a b e} = {u. dbm_entry_val u b a (neg_dbm_entry e)}"
  if "e \<noteq> (\<infinity> :: _ DBMEntry)" "a \<noteq> None \<or> b \<noteq> None"
  using that by (cases e; cases a; cases b; auto 4 3 simp: le_minus_iff less_minus_iff)

instantiation DBMEntry :: (uminus) uminus
begin
  definition uminus: "uminus = neg_dbm_entry"
  instance ..
end

text \<open>
Note that it is not clear that this is the only sensible definition for negation of DBM entries.
The following would also have been quite viable:
@{text 
  \<open>fun neg_dbm_entry where
  "neg_dbm_entry (Le a) = Le (-a)" |
  "neg_dbm_entry (Lt a) = Lt (-a)" |
  "neg_dbm_entry \<infinity> = \<infinity>"\<close>
}

For most practical proofs using arithmetic on DBM entries we have found that this
does not make much of a difference. Lemma @{thm neg_entry} would not hold any longer, however.
\<close>




section \<open>DBM Entries Form a Linearly Ordered Abelian Monoid\<close>

instantiation DBMEntry :: (linorder) linorder
begin
  definition less_eq: "(\<le>) \<equiv> dbm_le"
  definition less: "(<) = dbm_lt"
  instance
  proof ((standard; unfold less less_eq), goal_cases)
    case 1 thus ?case unfolding dbm_le_def using dbm_lt_asymmetric by auto
  next
    case 2 thus ?case by (simp add: dbm_le_def)
  next
    case 3 thus ?case unfolding dbm_le_def using dbm_lt_trans by auto
  next
    case 4 thus ?case unfolding dbm_le_def using dbm_lt_asymmetric by auto
  next
    case 5 thus ?case unfolding dbm_le_def using dbm_not_lt_eq by auto
  qed
end

class linordered_cancel_ab_monoid_add =
  linordered_cancel_ab_semigroup_add + zero +
    assumes neutl[simp]: "0 + x = x"
    assumes neutr[simp]: "x + 0 = x"
begin

  subclass linordered_ab_monoid_add
    by standard (rule neutl)

end

instantiation DBMEntry :: (zero) zero
begin
  definition neutral: "0 = Le 0"
  instance ..
end

instantiation DBMEntry :: (linordered_cancel_ab_monoid_add) linordered_ab_monoid_add
begin

  definition add: "(+) = dbm_add"

  instance proof ((standard; unfold add neutral less less_eq), goal_cases)
    case (1 a b c) thus ?case by (cases a; cases b; cases c; auto simp: add.assoc)
  next
    case (2 a b) thus ?case by (cases a; cases b; auto simp: add.commute)
  next
    case (3 a) thus ?case by (cases a) auto
  next
    case (4 a b c)
    thus ?case unfolding dbm_le_def
    apply safe
     apply (rule dbm_lt.cases)
          apply assumption
      by (cases c; fastforce)+
  qed

end

interpretation linordered_monoid:
  linordered_ab_monoid_add dbm_add "Le (0::'t::linordered_cancel_ab_monoid_add)" dbm_le dbm_lt
  apply (standard, fold neutral add less_eq less)
  using add.commute by (auto intro: add_left_mono simp: add.assoc)

instance time \<subseteq> linordered_cancel_ab_monoid_add by (standard; simp)

lemma dbm_add_strict_right_mono_neutral: "a < Le (d :: 't :: time) \<Longrightarrow> a + Le (-d) < Le 0"
unfolding less add by (cases a) (auto elim!: dbm_lt.cases)

lemma dbm_lt_not_inf_less[intro]: "A \<noteq> \<infinity> \<Longrightarrow> A \<prec> \<infinity>" by (cases A) auto

lemma add_inf[simp]:
  "a + \<infinity> = \<infinity>" "\<infinity> + a = \<infinity>"
unfolding add by (cases a) auto

lemma inf_lt[simp,dest!]:
  "\<infinity> < x \<Longrightarrow> False"
  by (cases x) (auto simp: less)

lemma inf_lt_impl_False[simp]:
  "\<infinity> < x = False"
  by auto

lemma Le_Le_dbm_lt_D[dest]: "Le a \<prec> Lt b \<Longrightarrow> a < b" by (cases rule: dbm_lt.cases) auto
lemma Le_Lt_dbm_lt_D[dest]: "Le a \<prec> Le b \<Longrightarrow> a < b" by (cases rule: dbm_lt.cases) auto
lemma Lt_Le_dbm_lt_D[dest]: "Lt a \<prec> Le b \<Longrightarrow> a \<le> b" by (cases rule: dbm_lt.cases) auto
lemma Lt_Lt_dbm_lt_D[dest]: "Lt a \<prec> Lt b \<Longrightarrow> a < b" by (cases rule: dbm_lt.cases) auto

lemma Le_le_LeI[intro]: "a \<le> b \<Longrightarrow> Le a \<le> Le b" unfolding less_eq dbm_le_def by auto
lemma Lt_le_LeI[intro]: "a \<le> b \<Longrightarrow> Lt a \<le> Le b" unfolding less_eq dbm_le_def by auto
lemma Lt_le_LtI[intro]: "a \<le> b \<Longrightarrow> Lt a \<le> Lt b" unfolding less_eq dbm_le_def by auto
lemma Le_le_LtI[intro]: "a < b \<Longrightarrow> Le a \<le> Lt b" unfolding less_eq dbm_le_def by auto
lemma Lt_lt_LeI: "x \<le> y \<Longrightarrow> Lt x < Le y" unfolding less by auto

lemma Le_le_LeD[dest]: "Le a \<le> Le b \<Longrightarrow> a \<le> b" unfolding dbm_le_def less_eq by auto
lemma Le_le_LtD[dest]: "Le a \<le> Lt b \<Longrightarrow> a < b" unfolding dbm_le_def less_eq by auto
lemma Lt_le_LeD[dest]: "Lt a \<le> Le b \<Longrightarrow> a \<le> b" unfolding less_eq dbm_le_def by auto
lemma Lt_le_LtD[dest]: "Lt a \<le> Lt b \<Longrightarrow> a \<le> b" unfolding less_eq dbm_le_def by auto

lemma inf_not_le_Le[simp]: "\<infinity> \<le> Le x = False" unfolding less_eq dbm_le_def by auto
lemma inf_not_le_Lt[simp]: "\<infinity> \<le> Lt x = False" unfolding less_eq dbm_le_def by auto
lemma inf_not_lt[simp]: "\<infinity> \<prec> x = False" by auto

lemma any_le_inf: "x \<le> (\<infinity> :: _ DBMEntry)" by (metis less_eq dmb_le_dbm_entry_bound_inf le_cases)

lemma dbm_lt_code_simps[code]:
  "dbm_lt (Lt a) \<infinity> = True"
  "dbm_lt (Le a) \<infinity> = True"
  "dbm_lt (Le a) (Le b) = (a < b)"
  "dbm_lt (Le a) (Lt b) = (a < b)"
  "dbm_lt (Lt a) (Le b) = (a \<le> b)"
  "dbm_lt (Lt a) (Lt b) = (a < b)"
  "dbm_lt \<infinity> x = False"
  by auto

section \<open>Basic Properties of DBMs\<close>

subsection \<open>DBMs and Length of Paths\<close>

lemma dbm_entry_val_add_1: "dbm_entry_val u (Some c) (Some d) a \<Longrightarrow>  dbm_entry_val u (Some d) None b
       \<Longrightarrow> dbm_entry_val u (Some c) None (dbm_add a b)"
proof (cases a, goal_cases)
  case 1 thus ?thesis
    apply (cases b)
    using add_mono_thms_linordered_semiring(1) add_le_less_mono by auto fastforce+
next
  case 2 thus ?thesis
  apply (cases b)
      apply (clarsimp simp: dbm_entry_val.intros(3) diff_less_eq less_le_trans)
     apply (clarsimp, metis add_le_less_mono dbm_entry_val.intros(3) diff_add_cancel less_imp_le)
    apply auto
    done
next
  case 3 thus ?thesis by (cases b) auto
qed

lemma dbm_entry_val_add_2: "dbm_entry_val u None (Some c) a \<Longrightarrow> dbm_entry_val u (Some c) (Some d) b
       \<Longrightarrow> dbm_entry_val u None (Some d) (dbm_add a b)"
proof (cases a, goal_cases)
  case 1 thus ?thesis
    apply (cases b)
    using add_mono_thms_linordered_semiring(1) add_le_less_mono by fastforce+
next
  case 2 thus ?thesis
    apply (cases b)
    using add_mono_thms_linordered_field(3) apply fastforce
    using add_strict_mono by fastforce+
next
  case 3 thus ?thesis by (cases b) auto
qed

lemma dbm_entry_val_add_3:
  "dbm_entry_val u (Some c) (Some d) a \<Longrightarrow>  dbm_entry_val u (Some d) (Some e) b
   \<Longrightarrow> dbm_entry_val u (Some c) (Some e) (dbm_add a b)"
proof (cases a, goal_cases)
  case 1 thus ?thesis
    apply (cases b)
    using add_mono_thms_linordered_semiring(1) apply fastforce
    using add_le_less_mono by fastforce+
next
  case 2 thus ?thesis
    apply (cases b)
    using add_mono_thms_linordered_field(3) apply fastforce
    using add_strict_mono by fastforce+
next
  case 3 thus ?thesis by (cases b) auto
qed

lemma dbm_entry_val_add_4:
  "dbm_entry_val u (Some c) None a \<Longrightarrow> dbm_entry_val u None (Some d) b
   \<Longrightarrow> dbm_entry_val u (Some c) (Some d) (dbm_add a b)"
proof (cases a, goal_cases)
  case 1 thus ?thesis
    apply (cases b)
    using add_mono_thms_linordered_semiring(1) apply fastforce
    using add_le_less_mono by fastforce+
next
  case 2 thus ?thesis
    apply (cases b)
    using add_mono_thms_linordered_field(3) apply fastforce
    using add_strict_mono by fastforce+
next
  case 3 thus ?thesis by (cases b) auto
qed

no_notation dbm_add (infixl "\<otimes>" 70)

lemma DBM_val_bounded_len_1'_aux:
  assumes "DBM_val_bounded v u m n" "v c \<le> n" "\<forall> k \<in> set vs. k > 0 \<and> k \<le> n \<and> (\<exists> c. v c = k)"
  shows "dbm_entry_val u (Some c) None (len m (v c) 0 vs)" using assms
proof (induction vs arbitrary: c)
  case Nil then show ?case unfolding DBM_val_bounded_def by auto
next
  case (Cons k vs)
  then obtain c' where c': "k > 0" "k \<le> n" "v c' = k" by auto
  with Cons have "dbm_entry_val u (Some c') None (len m (v c') 0 vs)" by auto
  moreover have "dbm_entry_val u (Some c) (Some c') (m (v c) (v c'))" using Cons.prems c'
  by (auto simp add: DBM_val_bounded_def)
  ultimately have "dbm_entry_val u (Some c) None (m (v c) (v c') + len m (v c') 0 vs)"
  using dbm_entry_val_add_1 unfolding add by fastforce
  with c' show ?case unfolding DBM_val_bounded_def by simp
qed

lemma DBM_val_bounded_len_3'_aux:
  "DBM_val_bounded v u m n \<Longrightarrow> v c \<le> n \<Longrightarrow> v d \<le> n \<Longrightarrow> \<forall> k \<in> set vs. k > 0 \<and> k \<le> n \<and> (\<exists> c. v c = k)
   \<Longrightarrow> dbm_entry_val u (Some c) (Some d) (len m (v c) (v d) vs)"
proof (induction vs arbitrary: c)
  case Nil thus ?case unfolding DBM_val_bounded_def by auto
next
  case (Cons k vs)
  then obtain c' where c': "k > 0" "k \<le> n" "v c' = k" by auto
  with Cons have "dbm_entry_val u (Some c') (Some d) (len m (v c') (v d) vs)" by auto
  moreover have "dbm_entry_val u (Some c) (Some c') (m (v c) (v c'))" using Cons.prems c'
  by (auto simp add: DBM_val_bounded_def)
  ultimately have "dbm_entry_val u (Some c) (Some d) (m (v c) (v c') + len m (v c') (v d) vs)"
  using dbm_entry_val_add_3 unfolding add by fastforce
  with c' show ?case unfolding DBM_val_bounded_def by simp
qed

lemma DBM_val_bounded_len_2'_aux:
  "DBM_val_bounded v u m n \<Longrightarrow> v c \<le> n \<Longrightarrow> \<forall> k \<in> set vs. k > 0 \<and> k \<le> n \<and> (\<exists> c. v c = k)
  \<Longrightarrow> dbm_entry_val u None (Some c) (len m 0 (v c) vs)"
proof (cases vs, goal_cases)
  case 1 then show ?thesis unfolding DBM_val_bounded_def by auto
next
  case (2 k vs)
  then obtain c' where c': "k > 0" "k \<le> n" "v c' = k" by auto
  with 2 have "dbm_entry_val u (Some c') (Some c) (len m (v c') (v c) vs)"
  using DBM_val_bounded_len_3'_aux by auto
  moreover have "dbm_entry_val u None (Some c') (m 0 (v c'))"
  using 2 c' by (auto simp add: DBM_val_bounded_def)
  ultimately have "dbm_entry_val u None (Some c) (m 0 (v c') + len m (v c') (v c) vs)"
  using dbm_entry_val_add_2 unfolding add by fastforce
  with 2(4) c' show ?case unfolding DBM_val_bounded_def by simp
qed

lemma cnt_0_D:
  "cnt x xs = 0 \<Longrightarrow> x \<notin> set xs"
  apply (induction xs)
   apply simp
  subgoal for a xs
    by (cases "x = a"; simp)
  done

lemma cnt_at_most_1_D:
  "cnt x (xs @ x # ys) \<le> 1 \<Longrightarrow> x \<notin> set xs \<and> x \<notin> set ys"
  apply (induction xs)
  apply auto[]
  using cnt_0_D apply force
  subgoal for a xs
    by (cases "x = a"; simp)
  done

lemma nat_list_0 [intro]:
  "x \<in> set xs \<Longrightarrow> 0 \<notin> set (xs :: nat list) \<Longrightarrow> x > 0"
  by (induction xs) auto

lemma DBM_val_bounded_len'1:
  fixes v
  assumes "DBM_val_bounded v u m n" "0 \<notin> set vs" "v c \<le> n"
          "\<forall> k \<in> set vs. k > 0 \<longrightarrow> k \<le> n \<and> (\<exists> c. v c = k)"
  shows "dbm_entry_val u (Some c) None (len m (v c) 0 vs)"
using DBM_val_bounded_len_1'_aux[OF assms(1,3)] assms(2,4) by fastforce

lemma DBM_val_bounded_len'2:
  fixes v
  assumes "DBM_val_bounded v u m n" "0 \<notin> set vs" "v c \<le> n"
          "\<forall> k \<in> set vs. k > 0 \<longrightarrow> k \<le> n \<and> (\<exists> c. v c = k)"
  shows "dbm_entry_val u None (Some c) (len m 0 (v c) vs)"
using DBM_val_bounded_len_2'_aux[OF assms(1,3)] assms(2,4) by fastforce

lemma DBM_val_bounded_len'3:
  fixes v
  assumes "DBM_val_bounded v u m n" "cnt 0 vs \<le> 1" "v c1 \<le> n" "v c2 \<le> n"
          "\<forall> k \<in> set vs. k > 0 \<longrightarrow> k \<le> n \<and> (\<exists> c. v c = k)"
  shows "dbm_entry_val u (Some c1) (Some c2) (len m (v c1) (v c2) vs)"
proof -
  show ?thesis
  proof (cases "\<forall> k \<in> set vs. k > 0")
    case True
    with assms have "\<forall> k \<in> set vs. k > 0 \<and> k \<le> n \<and> (\<exists> c. v c = k)" by auto
    with DBM_val_bounded_len_3'_aux[OF assms(1,3,4)] show ?thesis by auto
  next
    case False
    then have "\<exists> k \<in> set vs. k = 0" by auto
    then obtain us ws where vs: "vs = us @ 0 # ws" by (meson split_list_last)
    with cnt_at_most_1_D[of 0 "us"] assms(2) have
      "0 \<notin> set us" "0 \<notin> set ws"
    by auto
    with vs have vs: "vs = us @ 0 # ws" "\<forall> k \<in> set us. k > 0" "\<forall> k \<in> set ws. k > 0" by auto
    with assms(5) have v:
      "\<forall>k\<in>set us. 0 < k \<and> k \<le> n \<and> (\<exists>c. v c = k)" "\<forall>k\<in>set ws. 0 < k \<and> k \<le> n \<and> (\<exists>c. v c = k)"
    by auto
    with
      dbm_entry_val_add_4[OF
        DBM_val_bounded_len_1'_aux[OF assms(1,3) v(1)]
        DBM_val_bounded_len_2'_aux[OF assms(1,4) v(2)]
      ]
    have "dbm_entry_val u (Some c1) (Some c2) (dbm_add (len m (v c1) 0 us) (len m 0 (v c2) ws))"
      by auto
    moreover from vs have "len m (v c1) (v c2) vs = dbm_add (len m (v c1) 0 us) (len m 0 (v c2) ws)"
      by (simp add: len_comp add)
    ultimately show ?thesis by auto
  qed
qed


paragraph \<open>Now unused\<close>

lemma DBM_val_bounded_len':
  fixes v
  defines "vo \<equiv> \<lambda> k. if k = 0 then None else Some (SOME c. v c = k)"
  assumes "DBM_val_bounded v u m n" "cnt 0 (i # j # vs) \<le> 1"
          "\<forall> k \<in> set (i # j # vs). k > 0 \<longrightarrow> k \<le> n \<and> (\<exists> c. v c = k)"
  shows "dbm_entry_val u (vo i) (vo j) (len m i j vs)"
proof -
  show ?thesis
  proof (cases "\<forall> k \<in> set vs. k > 0")
    case True
    with assms have *: "\<forall> k \<in> set vs. k > 0 \<and> k \<le> n \<and> (\<exists> c. v c = k)" by auto
    show ?thesis
    proof (cases "i = 0")
      case True
      then have i: "vo i = None" by (simp add: vo_def)
      show ?thesis
      proof (cases "j = 0")
        case True with assms \<open>i = 0\<close> show ?thesis by auto
      next
        case False
        with assms obtain c2 where c2: "j \<le> n" "v c2 = j" "vo j = Some c2"
        unfolding vo_def by (fastforce intro: someI)
        with \<open>i = 0\<close> i DBM_val_bounded_len_2'_aux[OF assms(2) _ *] show ?thesis by auto
      qed
    next
      case False
      with assms(4) obtain c1 where c1: "i \<le> n" "v c1 = i" "vo i = Some c1"
      unfolding vo_def by (fastforce intro: someI)
      show ?thesis
      proof (cases "j = 0")
        case True
        with DBM_val_bounded_len_1'_aux[OF assms(2) _ *] c1 show ?thesis by (auto simp: vo_def)
      next
        case False
        with assms obtain c2 where c2: "j \<le> n" "v c2 = j" "vo j = Some c2"
        unfolding vo_def by (fastforce intro: someI)
        with c1 DBM_val_bounded_len_3'_aux[OF assms(2) _ _ *] show ?thesis by auto
      qed
    qed
  next
    case False
    then have "\<exists> k \<in> set vs. k = 0" by auto
    then obtain us ws where vs: "vs = us @ 0 # ws" by (meson split_list_last)
    with cnt_at_most_1_D[of 0 "i # j # us" ws] assms(3) have
      "0 \<notin> set us" "0 \<notin> set ws" "i \<noteq> 0" "j \<noteq> 0"
    by auto
    with vs have vs: "vs = us @ 0 # ws" "\<forall> k \<in> set us. k > 0" "\<forall> k \<in> set ws. k > 0" by auto
    with assms(4) have v:
      "\<forall>k\<in>set us. 0 < k \<and> k \<le> n \<and> (\<exists>c. v c = k)" "\<forall>k\<in>set ws. 0 < k \<and> k \<le> n \<and> (\<exists>c. v c = k)"
    by auto
    from \<open>i \<noteq> 0\<close> \<open>j \<noteq> 0\<close> assms obtain c1 c2 where
      c1: "i \<le> n" "v c1 = i" "vo i = Some c1" and c2: "j \<le> n" "v c2 = j" "vo j = Some c2"
    unfolding vo_def by (fastforce intro: someI)
    with dbm_entry_val_add_4 [OF DBM_val_bounded_len_1'_aux[OF assms(2) _ v(1)] DBM_val_bounded_len_2'_aux[OF assms(2) _ v(2)]]
    have "dbm_entry_val u (Some c1) (Some c2) (dbm_add (len m (v c1) 0 us) (len m 0 (v c2) ws))" by auto
    moreover from vs have "len m (v c1) (v c2) vs = dbm_add (len m (v c1) 0 us) (len m 0 (v c2) ws)"
      by (simp add: len_comp add)
    ultimately show ?thesis using c1 c2 by auto
  qed
qed

lemma DBM_val_bounded_len_1: "DBM_val_bounded v u m n \<Longrightarrow> v c \<le> n \<Longrightarrow> \<forall> c \<in> set cs. v c \<le> n
      \<Longrightarrow> dbm_entry_val u (Some c) None (len m (v c) 0 (map v cs))"
proof (induction cs arbitrary: c)
  case Nil thus ?case unfolding DBM_val_bounded_def by auto
next
  case (Cons c' cs)
  hence "dbm_entry_val u (Some c') None (len m (v c') 0 (map v cs))" by auto
  moreover have "dbm_entry_val u (Some c) (Some c') (m (v c) (v c'))" using Cons.prems
    by (simp add: DBM_val_bounded_def)
  ultimately have "dbm_entry_val u (Some c) None (m (v c) (v c') + len m (v c') 0 (map v cs))"
    using dbm_entry_val_add_1 unfolding add by fastforce
  thus ?case unfolding DBM_val_bounded_def by simp
qed

lemma DBM_val_bounded_len_3: "DBM_val_bounded v u m n \<Longrightarrow> v c \<le> n \<Longrightarrow> v d \<le> n \<Longrightarrow> \<forall> c \<in> set cs. v c \<le> n
      \<Longrightarrow> dbm_entry_val u (Some c) (Some d) (len m (v c) (v d) (map v cs))"
proof (induction cs arbitrary: c)
  case Nil thus ?case unfolding DBM_val_bounded_def by auto
next
  case (Cons c' cs)
  hence "dbm_entry_val u (Some c') (Some d) (len m (v c') (v d) (map v cs))" by auto
  moreover have "dbm_entry_val u (Some c) (Some c') (m (v c) (v c'))" using Cons.prems
    by (simp add: DBM_val_bounded_def)
  ultimately have "dbm_entry_val u (Some c) (Some d) (m (v c) (v c') + len m (v c') (v d) (map v cs))"
    using dbm_entry_val_add_3 unfolding add by fastforce
  thus ?case unfolding DBM_val_bounded_def by simp
qed

lemma DBM_val_bounded_len_2: "DBM_val_bounded v u m n \<Longrightarrow> v c \<le> n \<Longrightarrow> \<forall> c \<in> set cs. v c \<le> n
      \<Longrightarrow> dbm_entry_val u None (Some c) (len m 0 (v c) (map v cs))"
proof (cases cs, goal_cases)
  case 1 thus ?thesis unfolding DBM_val_bounded_def by auto
next
  case (2 c' cs)
  hence "dbm_entry_val u (Some c') (Some c) (len m (v c') (v c) (map v cs))"
    using DBM_val_bounded_len_3 by auto
  moreover have "dbm_entry_val u None (Some c') (m 0 (v c'))"
    using 2 by (simp add: DBM_val_bounded_def)
  ultimately have "dbm_entry_val u None (Some c) (m 0 (v c') + len m (v c') (v c) (map v cs))"
    using dbm_entry_val_add_2 unfolding add by fastforce
  thus ?case using 2(4) unfolding DBM_val_bounded_def by simp
qed


lemmas DBM_arith_defs = add neutral uminus

end (* Theory *)
