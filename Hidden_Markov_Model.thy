theory Hidden_Markov_Model
  imports Markov_Models.Discrete_Time_Markov_Chain Auxiliary
begin

section \<open>Hidden Markov Models\<close>

subsection \<open>Definitions\<close>

locale HMM =
  fixes \<K> :: "'s \<Rightarrow> 's pmf" and \<O> :: "'s \<Rightarrow> 't pmf" and \<O>\<^sub>s :: "'t set"
  assumes observations_finite: "finite \<O>\<^sub>s"
      and observations_wellformed: "\<O>\<^sub>s \<noteq> {}"
      and observations_closed: "\<forall> s. \<O> s \<subseteq> \<O>\<^sub>s"
begin

no_notation (ASCII) comp  (infixl "o" 55) 

definition
  "obs \<equiv> SOME x. x \<in> \<O>\<^sub>s"

lemma obs:
  "obs \<in> \<O>\<^sub>s"
  unfolding obs_def using observations_wellformed by (auto intro: someI_ex)

definition "K \<equiv> \<lambda> (s\<^sub>1, o\<^sub>1 :: 't). bind_pmf (\<K> s\<^sub>1) (\<lambda> s\<^sub>2. map_pmf (\<lambda> o\<^sub>2. (s\<^sub>2, o\<^sub>2)) (\<O> s\<^sub>2))"

sublocale MC_syntax K .

definition "I (s :: 's) = map_pmf (\<lambda> x. (s, x)) (pmf_of_set \<O>\<^sub>s)"

definition
  "likelihood s os = T' (I s) {\<omega> \<in> space S. \<exists> o\<^sub>0 xs \<omega>'. \<omega> = (s, o\<^sub>0) ## xs @- \<omega>' \<and> map snd xs = os}"

abbreviation (input) "L os \<omega> \<equiv> \<exists> xs \<omega>'. \<omega> = xs @- \<omega>' \<and> map snd xs = os"

lemma likelihood_alt_def: "likelihood s os = T' (I s) {(s, o) ## xs @- \<omega>' |o xs \<omega>'. map snd xs = os}"
  unfolding likelihood_def by (simp add: in_S)


subsection \<open>Iteration Rule For Likelihood\<close>

lemma L_Nil:
  "L [] \<omega> = True"
  by simp

lemma emeasure_T_observation_Nil:
  "T (s, o\<^sub>0) {\<omega> \<in> space S. L [] \<omega>} = 1"
  by simp

lemma L_measurable[measurable]:
  "Measurable.pred S (L os)"
  sorry

lemma init_measurable[measurable]:
  "Measurable.pred S (\<lambda>x. \<exists>o\<^sub>0 xs \<omega>'. x = (s, o\<^sub>0) ## xs @- \<omega>' \<and> map snd xs = os)"
  sorry

lemma T_init_observation_eq:
  "T (s, o) {\<omega> \<in> space S. L os \<omega>} = T (s, o') {\<omega> \<in> space S. L os \<omega>}"
  apply (subst emeasure_Collect_T[unfolded space_T], (measurable; fail))
  apply (subst (2) emeasure_Collect_T[unfolded space_T], (measurable; fail))
  apply (simp add: K_def)
  done

lemma likelihood_init:
  "likelihood s os = T (s, obs) {\<omega> \<in> space S. L os \<omega>}"
proof -
  have *: "(\<Sum>o\<in>\<O>\<^sub>s. emeasure (T (s, o)) {\<omega> \<in> space S. L os \<omega>}) =
    of_nat (card \<O>\<^sub>s) * emeasure (T (s, obs)) {\<omega> \<in> space S. L os \<omega>}"
    by (subst sum_constant[symmetric]) (fastforce intro: sum.cong T_init_observation_eq[simplified])
  show ?thesis
    unfolding likelihood_def
    apply (subst emeasure_T')
    subgoal
      by measurable
    using *
    apply (simp add: I_def in_S observations_finite observations_wellformed nn_integral_pmf_of_set)
    apply (subst mult.commute)
    apply (simp add: observations_finite observations_wellformed mult_divide_eq_ennreal)
    done
qed

lemma emeasure_T_observation_Cons:
  "T (s, o\<^sub>0) {\<omega> \<in> space S. L (o\<^sub>1 # os) \<omega>} =
   (\<integral>\<^sup>+ t. ennreal (pmf (\<O> t) o\<^sub>1) * T (t, o\<^sub>1) {\<omega> \<in> space S. L os \<omega>} \<partial>(\<K> s))" (is "?l = ?r")
proof -
  have *:
    "\<integral>\<^sup>+ y. T (s', y) {x \<in> space S. \<exists>xs. (\<exists>\<omega>'. (s', y) ## x = xs @- \<omega>') \<and> map snd xs = o\<^sub>1 # os}
       \<partial>measure_pmf (\<O> s') =
    ennreal (pmf (\<O> s') o\<^sub>1) * T (s', o\<^sub>1) {\<omega> \<in> space S. \<exists>xs. (\<exists>\<omega>'. \<omega> = xs @- \<omega>') \<and> map snd xs = os}"
    (is "?L = ?R") for s'
  proof -
    have "?L = \<integral>\<^sup>+ x. ennreal (pmf (\<O> s') x) *
            T (s', x) {\<omega> \<in> space S. \<exists>xs. (\<exists>\<omega>'. (s', x) ## \<omega> = xs @- \<omega>') \<and> map snd xs = o\<^sub>1 # os}
          \<partial>count_space UNIV"
      by (rule nn_integral_measure_pmf)
    also have "\<dots> =
      \<integral>\<^sup>+ o\<^sub>2. (if o\<^sub>2 = o\<^sub>1
              then ennreal (pmf (\<O> s') o\<^sub>1) *
                   T (s', o\<^sub>1) {\<omega> \<in> space S. \<exists>xs \<omega>'. \<omega> = xs @- \<omega>' \<and> map snd xs = os}
              else 0)
       \<partial>count_space UNIV"
      apply (rule nn_integral_cong_AE
          [where v = "\<lambda> o\<^sub>2. if o\<^sub>2 = o\<^sub>1 then ennreal (pmf (\<O> s') o\<^sub>1) * T (s', o\<^sub>1) {\<omega> \<in> space S. \<exists> xs \<omega>'. \<omega> = xs @- \<omega>' \<and> map snd xs = os} else 0"]
          )
       apply (rule AE_I2)
       apply (split if_split, safe)
      subgoal
        by (auto intro!: arg_cong2[where f = times, OF HOL.refl] arg_cong2[where f = emeasure];
            metis list.simps(9) shift.simps(2) snd_conv
           )
      subgoal
        by (subst arg_cong2[where f = emeasure and d = "{}", OF HOL.refl]) auto
      done
    also have "\<dots> = \<integral>\<^sup>+o\<^sub>2\<in>{o\<^sub>1}.
       (ennreal (pmf (\<O> s') o\<^sub>1) * T (s', o\<^sub>1) {\<omega> \<in> space S. \<exists>xs \<omega>'. \<omega> = xs @- \<omega>' \<and> map snd xs = os})
      \<partial>count_space UNIV"
      by (rule nn_integral_cong_AE) auto
    also have "\<dots> = ?R"
      by simp
    finally show ?thesis .
  qed
  have "?l = \<integral>\<^sup>+ t. T t {x \<in> space S. \<exists>xs \<omega>'. t ## x = xs @- \<omega>' \<and> map snd xs = o\<^sub>1 # os} \<partial> (K (s, o\<^sub>0))"
    by (subst emeasure_Collect_T[unfolded space_T], measurable)
  also have "\<dots> = ?r"
    using * by (simp add: K_def)
  finally show ?thesis .
qed


subsection \<open>Computation of Likelihood\<close>

fun backward where
  "backward s [] = 1" |
  "backward s (o # os) = (\<integral>\<^sup>+ t. ennreal (pmf (\<O> t) o) * backward t os \<partial>measure_pmf (\<K> s))"

lemma emeasure_T_observation_backward:
  "emeasure (T (s, o)) {\<omega> \<in> space S. L os \<omega>} = backward s os"
  using emeasure_T_observation_Cons by (induction os arbitrary: s o; simp)

lemma likelihood_backward:
  "likelihood s os = backward s os"
  unfolding likelihood_init emeasure_T_observation_backward ..


context
  fixes \<S> :: "'s set"
  assumes states_finite: "finite \<S>"
      and states_wellformed: "\<S> \<noteq> {}"
      and states_closed: "\<forall> s. \<K> s \<subseteq> \<S>"
begin

fun forward where
  "forward s t_end [] = indicator {t_end} s" |
  "forward s t_end (o # os) =
    (\<Sum>t \<in> \<S>. ennreal (pmf (\<O> t) o) * ennreal (pmf (\<K> s) t) * forward t t_end os)"

lemma forward_split:
  "forward s t (os1 @ os2) = (\<Sum>t' \<in> \<S>. forward s t' os1 * forward t' t os2)"
  if "s \<in> \<S>"
  using that
  apply (induction os1 arbitrary: s)
  subgoal for s
    apply (simp add: sum_indicator_mult[OF \<open>finite \<S>\<close>])
    apply (subst sum.cong[where B = "{s}"])
    by auto
  subgoal for a os1 s
    apply simp
    apply (subst sum_distrib_right)
    apply (subst sum.commute)
    apply (simp add: sum_distrib_left algebra_simps)
    done
  done

lemma forward_backward:
  "(\<Sum>t \<in> \<S>. forward s t os) = backward s os" if "s \<in> \<S>"
  using \<open>s \<in> \<S>\<close>
  apply (induction os arbitrary: s)
  subgoal for s
    by (auto intro: sum_single[where k = s, OF \<open>finite \<S>\<close>])
  subgoal for a os s
    apply (simp add: sum.commute sum_distrib_left[symmetric])
    apply (subst nn_integral_measure_pmf_support[where A = \<S>])
    using states_finite states_closed by (auto simp: algebra_simps)
  done

theorem likelihood_forward:
  "likelihood s os = (\<Sum>t \<in> \<S>. forward s t os)" if \<open>s \<in> \<S>\<close>
  unfolding likelihood_backward forward_backward[symmetric, OF \<open>s \<in> \<S>\<close>] ..


subsection \<open>Definition of Maximum Probability\<close>

abbreviation (input) "V os as \<omega> \<equiv> (\<exists> \<omega>'. \<omega> = zip as os @- \<omega>')"

definition
  "max_prob s os =
  Max {T' (I s) {\<omega> \<in> space S. \<exists>o \<omega>'. \<omega> = (s, o) ## zip as os @- \<omega>'}
       | as. length as = length os \<and> set as \<subseteq> \<S>}"

fun viterbi_prob where
  "viterbi_prob s t_end [] = indicator {t_end} s" |
  "viterbi_prob s t_end (o # os) =
    (MAX t \<in> \<S>. ennreal (pmf (\<O> t) o * pmf (\<K> s) t) * viterbi_prob t t_end os)"

definition
  "is_decoding s os as \<equiv>
    T' (I s) {\<omega> \<in> space S. \<exists>o \<omega>'. \<omega> = (s, o) ## zip as os @- \<omega>'} = max_prob s os \<and>
    length as = length os \<and> set as \<subseteq> \<S>"


subsection \<open>Iteration Rule For Maximum Probability\<close>

lemma emeasure_T_state_Nil:
  "T (s, o\<^sub>0) {\<omega> \<in> space S. V [] as \<omega>} = 1"
  by simp

lemma max_prob_T_state_Nil:
  "Max {T (s, o) {\<omega> \<in> space S. V [] as \<omega>} | as. length as = length [] \<and> set as \<subseteq> \<S>} = 1"
  by (simp add: emeasure_T_state_Nil)

lemma measurable_V[measurable]:
  "Measurable.pred S (\<lambda>\<omega>. V os as \<omega>)"
  sorry

lemma init_V_measurable[measurable]:
  "Measurable.pred S (\<lambda>x. \<exists>o \<omega>'. x = (s, o) ## zip as os @- \<omega>')"
  sorry

lemma max_prob_Cons':
  "Max {T (s, o\<^sub>1) {\<omega> \<in> space S. V (o # os) as \<omega>} | as. length as = length (o # os) \<and> set as \<subseteq> \<S>} =
  (
    MAX t \<in> \<S>. ennreal (pmf (\<O> t) o * pmf (\<K> s) t) *
      (MAX as \<in> {as. length as = length os \<and> set as \<subseteq> \<S>}. T (t, o) {\<omega> \<in> space S. V os as \<omega>})
  )" (is "?l = ?r")
  and T_V_Cons:
  "T (s, o\<^sub>1) {\<omega> \<in> space S. V (o # os) (t # as) \<omega>}
  = ennreal (pmf (\<O> t) o * pmf (\<K> s) t) * T (t, o) {\<omega> \<in> space S. V os as \<omega>}"
  (is "?l' = ?r'")
  if "length as = length os"
proof -
  let ?S = "\<lambda> os. {as. length as = length os \<and> set as \<subseteq> \<S>}"
  have S_finite: "finite (?S os)" for os :: "'t list"
    using finite_lists_length_eq[OF \<open>finite \<S>\<close>] by (rule finite_subset[rotated]) auto
  have S_nonempty: "?S os \<noteq> {}" for os :: "'t list"
  proof -
    let ?a = "SOME a. a \<in> \<S>" let ?as = "replicate (length os) ?a"
    from \<open>\<S> \<noteq> {}\<close> have "?a \<in> \<S>"
      by (auto intro: someI_ex)
    then have "?as \<in> ?S os"
      by auto
    then show ?thesis
      by force
  qed
  let ?f = "\<lambda>t as os. T t {\<omega> \<in> space S. V os as (t ## \<omega>)}"
  let ?g = "\<lambda>t as os. T t {\<omega> \<in> space S. V os as \<omega>}"
  have *: "?f t as (o # os) = ?g t (tl as) os * indicator {(hd as, o)} t"
    if "length as = Suc n" for t as n
    unfolding indicator_def using that by (cases as) auto
  have **: "K (s, o\<^sub>1) {(t, o)} = pmf (\<O> t) o * pmf (\<K> s) t" for t
    unfolding K_def
    apply (simp add: vimage_def)
    apply (subst arg_cong2[where
          f = nn_integral and d = "\<lambda> x. \<O> x {xa. xa = o \<and> x = t} * indicator {t} x",
          OF HOL.refl])
    subgoal
      by (auto simp: indicator_def)
    by (simp add: emeasure_pmf_single ennreal_mult')
  have "?l = (MAX as \<in> ?S (o # os). \<integral>\<^sup>+ t. ?f t as (o # os) \<partial>K (s, o\<^sub>1))"
    by (subst Max_to_image2; subst emeasure_Collect_T[unfolded space_T]; rule measurable_V HOL.refl)
  also have "\<dots> = (MAX as \<in> ?S (o # os). \<integral>\<^sup>+ t. ?g t (tl as) os * indicator {(hd as,o)} t \<partial>K (s,o\<^sub>1))"
    by (simp cong: Max_image_cong_simp add: *)
  also have "\<dots> = (MAX(t, as)\<in> \<S> \<times> ?S os. ennreal (pmf (\<O> t) o * pmf (\<K> s) t) * ?g (t, o) as os)"
  proof ((rule Max_eq_image_if; clarsimp?), goal_cases)
    case 1
    from S_finite[of "o # os"] show ?case
      by simp
  next
    case 2
    from \<open>finite \<S>\<close> show ?case
      by (blast intro: S_finite)
  next
    case (3 as)
    then show ?case
      by - (rule bexI[where x = "hd as"]; cases as; auto simp: algebra_simps **)
  next
    case (4 x as)
    then show ?case
      by - (rule exI[where x = "x # as"], simp add: algebra_simps **)
  qed
  also have "\<dots> = ?r"
    by (subst Max_image_left_mult[symmetric], fact+) (rule sym, rule Max_image_pair, fact+)
  finally show "?l = ?r" .
  have "?l' = \<integral>\<^sup>+ t'. ?f t' (t # as) (o # os) \<partial>K (s, o\<^sub>1)"
    by (rule emeasure_Collect_T[unfolded space_T]; rule measurable_V)
  also from that have "\<dots> = \<integral>\<^sup>+ t'. ?g t' as os * indicator {(t,o)} t' \<partial>K (s,o\<^sub>1)"
    by (subst *[of _ "length as"]; simp)
  also have "\<dots> = ?r'"
    by (simp add: **, simp only: algebra_simps)
  finally show "?l' = ?r'" .
qed

lemmas max_prob_Cons = max_prob_Cons'[OF length_replicate]



subsection \<open>Computation of Maximum Probability\<close>

lemma T_init_V_eq:
  "T (s, o) {\<omega> \<in> space S. V os as \<omega>} = T (s, o') {\<omega> \<in> space S. V os as \<omega>}"
  apply (subst emeasure_Collect_T[unfolded space_T], (measurable; fail))
  apply (subst (2) emeasure_Collect_T[unfolded space_T], (measurable; fail))
  apply (simp add: K_def)
  done

(* TODO: Duplication with likelihood_init *)
lemma T'_I_T:
  "T' (I s) {\<omega> \<in> space S. \<exists>o \<omega>'. \<omega> = (s, o) ## zip as os @- \<omega>'} = T (s,o) {\<omega> \<in> space S. V os as \<omega>}"
proof -
  have "(\<Sum>o\<in>\<O>\<^sub>s. T (s, o) {\<omega> \<in> space S. V os as \<omega>}) =
    of_nat (card \<O>\<^sub>s) * T (s, o) {\<omega> \<in> space S. V os as \<omega>}" for as
    by (subst sum_constant[symmetric]) (fastforce intro: sum.cong T_init_V_eq[simplified])
  then show ?thesis
    unfolding max_prob_def
    apply (subst emeasure_T')
    subgoal
      by measurable
    apply (simp add: I_def in_S observations_finite observations_wellformed nn_integral_pmf_of_set)
    apply (subst mult.commute)
    apply (simp add: observations_finite observations_wellformed mult_divide_eq_ennreal)
    done
qed

lemma max_prob_init:
  "max_prob s os = Max {T (s,o) {\<omega> \<in> space S. V os as \<omega>} | as. length as = length os \<and> set as \<subseteq> \<S>}"
  unfolding max_prob_def by (simp add: T'_I_T[symmetric])

lemma max_prob_Nil[simp]:
  "max_prob s [] = 1"
  unfolding max_prob_init[where o = obs] by auto

lemma Max_start:
  "(MAX t\<in>\<S>. (indicator {t} s :: ennreal)) = 1" if "s \<in> \<S>"
  using \<open>finite \<S>\<close> that by (auto simp: indicator_def intro: Max_eqI)

lemma Max_V_viterbi:
  "(MAX t \<in> \<S>. viterbi_prob s t os) =
   Max {T (s, o) {\<omega> \<in> space S. V os as \<omega>} | as. length as = length os \<and> set as \<subseteq> \<S>}" if "s \<in> \<S>"
  using that \<open>finite \<S>\<close> \<open>\<S> \<noteq> {}\<close>
  by (induction os arbitrary: s o; simp
        add: Max_start max_prob_Cons[simplified] Max_image_commute Max_image_left_mult Max_to_image2
        cong: Max_image_cong
      )

lemma max_prob_viterbi:
  "(MAX t \<in> \<S>. viterbi_prob s t os) = max_prob s os" if "s \<in> \<S>"
  using max_prob_init[of s os] Max_V_viterbi[OF \<open>s \<in> \<S>\<close>, symmetric] by simp


subsection \<open>Decoding the Most Probable Hidden State Sequence\<close>

context
  fixes state_list assumes "set state_list = \<S>"
begin

fun viterbi where
  "viterbi s t_end [] = ([], indicator {t_end} s)" |
  "viterbi s t_end (o # os) = fst (
    argmax snd (map
      (\<lambda>t. let (xs, v) = viterbi t t_end os in (t # xs, ennreal (pmf (\<O> t) o * pmf (\<K> s) t) * v))
    state_list))"

lemma state_list_nonempty:
  "state_list \<noteq> []"
  using \<open>set state_list = \<S>\<close> \<open>\<S> \<noteq> {}\<close> by auto

lemma viterbi_viterbi_prob:
  "snd (viterbi s t_end os) = viterbi_prob s t_end os"
proof (induction os arbitrary: s)
  case Nil
  then show ?case
    by simp
next
  case (Cons o os)
  let ?f =
    "\<lambda>t. let (xs, v) = viterbi t t_end os in (t # xs, ennreal (pmf (\<O> t) o * pmf (\<K> s) t) * v)"
  let ?xs = "map ?f state_list"
  from state_list_nonempty have "map ?f state_list \<noteq> []"
    by simp
  from argmax(2,3)[OF this, of snd] have *:
    "snd (fst (argmax snd ?xs)) = snd (argmax snd ?xs)"
    "snd (argmax snd ?xs) = (MAX x \<in> set ?xs. snd x)" .
  then show ?case
    apply (simp add: \<open>set _ = \<S>\<close>)
    apply (rule Max_eq_image_if)
       apply (intro finite_imageI \<open>finite \<S>\<close>)
      apply (intro finite_imageI \<open>finite \<S>\<close>)
    subgoal
      apply clarsimp
      subgoal for x
        using Cons.IH[of x] by (auto split: prod.splits)
      done
    apply clarsimp
    subgoal for x
      using Cons.IH[of x] by (force split: prod.splits)
    done
qed

private fun val_of where
  "val_of s [] [] = 1" |
  "val_of s (t # xs) (o # os) = ennreal (pmf (\<O> t) o * pmf (\<K> s) t) * val_of t xs os"

lemma val_of_T:
  "val_of s as os = T (s, o\<^sub>1) {\<omega> \<in> space S. V os as \<omega>}" if "length as = length os"
  using that by (induction arbitrary: o\<^sub>1 rule: val_of.induct; (subst T_V_Cons)?; simp)

lemma viterbi_sequence:
  "snd (viterbi s t_end os) = val_of s (fst (viterbi s t_end os)) os"
  if "snd (viterbi s t_end os) > 0"
  using that
proof (induction os arbitrary: s)
  case Nil
  then show ?case
    by (simp add: indicator_def split: if_split_asm)
next
  case (Cons o os s)
  let ?xs = "map
    (\<lambda>t. let (xs, v) = viterbi t t_end os in (t # xs, ennreal (pmf (\<O> t) o * pmf (\<K> s) t) * v))
    state_list"
  from state_list_nonempty have "?xs \<noteq> []"
    by simp
  from argmax(1)[OF this, of snd] obtain t where
    "t \<in> set state_list"
    "fst (argmax snd ?xs) =
    (t # fst (viterbi t t_end os), ennreal (pmf (\<O> t) o * pmf (\<K> s) t) * snd (viterbi t t_end os))"
    by (auto split: prod.splits)
  with Cons show ?case
    by (auto simp: ennreal_zero_less_mult_iff)
qed

lemma viterbi_valid_path:
  "length as = length os \<and> set as \<subseteq> \<S>" if "viterbi s t_end os = (as, v)"
using that proof (induction os arbitrary: s as v)
  case Nil
  then show ?case
    by simp
next
  case (Cons o os s as v)
  let ?xs = "map
    (\<lambda>t. let (xs, v) = viterbi t t_end os in (t # xs, ennreal (pmf (\<O> t) o * pmf (\<K> s) t) * v))
    state_list"
  from state_list_nonempty have "?xs \<noteq> []"
    by simp
  from argmax(1)[OF this, of snd] obtain t where "t \<in> \<S>"
    "fst (argmax snd ?xs) =
    (t # fst (viterbi t t_end os), ennreal (pmf (\<O> t) o * pmf (\<K> s) t) * snd (viterbi t t_end os))"
    by (auto simp: \<open>set _ = \<S>\<close> split: prod.splits)
  with Cons.prems show ?case
    by (cases "viterbi t t_end os"; simp add: Cons.IH)
qed

definition
  "viterbi_final s os = fst (argmax snd (map (\<lambda> t. viterbi s t os) state_list))"

lemma viterbi_finalE:
  obtains t where
    "t \<in> \<S>" "viterbi_final s os = viterbi s t os"
    "snd (viterbi s t os) = Max ((\<lambda>t. snd (viterbi s t os)) ` \<S>)"
proof -
  from state_list_nonempty have "map (\<lambda> t. viterbi s t os) state_list \<noteq> []"
    by simp
  from argmax[OF this, of snd] show ?thesis
    by (auto simp: \<open>set _ = \<S>\<close> image_comp comp_def viterbi_final_def intro: that)
qed

theorem viterbi_final_max_prob:
  assumes "viterbi_final s os = (as, v)" "s \<in> \<S>"
  shows "v = max_prob s os"
proof -
  obtain t where "t \<in> \<S>" "viterbi_final s os = viterbi s t os"
    "snd (viterbi s t os) = Max ((\<lambda>t. snd (viterbi s t os)) ` \<S>)"
    by (rule viterbi_finalE)
  with assms show ?thesis
    by (simp add: viterbi_viterbi_prob max_prob_viterbi)
qed

theorem viterbi_final_is_decoding:
  assumes "viterbi_final s os = (as, v)" "v > 0" "s \<in> \<S>"
  shows "is_decoding s os as"
proof -
  from viterbi_valid_path[of s _ os as v] assms have as: "length as = length os" "set as \<subseteq> \<S>"
    by - (rule viterbi_finalE[of s os]; simp)+
  obtain t where "t \<in> \<S>" "viterbi_final s os = viterbi s t os"
    by (rule viterbi_finalE)
  with assms viterbi_sequence[of s t os] have "val_of s as os = v"
    by (cases "viterbi s t os") (auto simp: snd_def split!: prod.splits)
  with val_of_T as have "max_prob s os = T (s, obs) {\<omega> \<in> space S. V os as \<omega>}"
    by (simp add: viterbi_final_max_prob[OF assms(1,3)])
  with as show ?thesis
    unfolding is_decoding_def by (simp only: T'_I_T)
qed

end (* State set as list *)

end (* Finite state set *)

end (* Hidden Markov Model *)

end (* Theory *)