theory Auxiliary
  imports Main "HOL-Library.Extended_Nonnegative_Real"
begin

section \<open>Auxiliary Material\<close>

syntax
  "_MAX" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3MAX_\<in>_./ _)" [0, 0, 10] 10)

translations
  "MAX x\<in>A. B"  \<rightleftharpoons> "CONST Max ((\<lambda>x. B) ` A)"

context
  fixes S :: "'s set"
  assumes "finite S"
begin

lemma Max_image_commute:
  "(MAX x \<in> S. MAX y \<in> S. f x y) = (MAX y \<in> S. MAX x \<in> S. f x y)"
proof (rule Max_eq_if, goal_cases)
  case 3
  { fix a assume "a \<in> S"
    with Max_in[OF finite_imageI[OF \<open>finite S\<close>], of "f a"] have "Max (f a ` S) \<in> f a ` S"
      by auto
    then obtain b where "f a b = Max (f a ` S)" "b \<in> S"
      by auto
    from \<open>a \<in> S\<close> have "f a b \<le> (MAX a \<in> S. f a b)"
      by (auto intro: Max_ge finite_imageI[OF \<open>finite S\<close>])
    with \<open>f a b = _\<close> \<open>b \<in> S\<close> have "\<exists>b\<in>S. Max (f a ` S) \<le> (MAX a \<in> S. f a b)"
      by auto
  }
  then show ?case
    by auto
next
  case 4
  { fix b assume "b \<in> S"
    with Max_in[OF finite_imageI[OF \<open>finite S\<close>], of "\<lambda> a. f a b"] have
      "(MAX a \<in> S. f a b) \<in> (\<lambda>a. f a b) ` S"
      by auto
    then obtain a where "f a b = (MAX a \<in> S. f a b)" "a \<in> S"
      by auto
    from \<open>b \<in> S\<close> have "f a b \<le> Max (f a ` S)"
      by (auto intro: Max_ge finite_imageI[OF \<open>finite S\<close>])
    with \<open>f a b = _\<close> \<open>a \<in> S\<close> have "\<exists>a\<in>S. (MAX a \<in> S. f a b) \<le> Max (f a ` S)"
      by auto
  }
    then show ?case
      by auto
  qed (use \<open>finite S\<close> in auto)

lemma Max_image_left_mult:
  "(MAX x \<in> S. c * f x) = (c :: ennreal) * (MAX x \<in> S. f x)" if "S \<noteq> {}"
  apply (rule Max_eqI)
  subgoal
    using \<open>finite S\<close> by auto
  subgoal for y
    using \<open>finite S\<close> by (auto intro: mult_left_mono)
  subgoal
    using Max_in[OF finite_imageI[OF \<open>finite S\<close>], of f] \<open>S \<noteq> {}\<close> by auto
  done

lemma Max_to_image:
  "Max {f t | t. t \<in> TT} = Max (f ` TT)"
  by (rule arg_cong[where f = Max]) auto

lemma Max_image_cong:
  "Max (f ` TT) = Max (g ` RR)" if "TT = RR" "\<And>x. x \<in> RR \<Longrightarrow> f x = g x"
  by (intro arg_cong[where f = Max] image_cong[OF that])

end (* Finite set *)

end (* Theory *)