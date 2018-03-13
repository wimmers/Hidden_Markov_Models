theory Hidden_Markov_Model
  imports Markov_Models.Discrete_Time_Markov_Chain
begin

syntax
  "_MAX"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3MAX_\<in>_./ _)" [0, 0, 10] 10)

translations
  "MAX x\<in>A. B"   \<rightleftharpoons> "CONST Max ((\<lambda>x. B) ` A)"


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

definition
  "decoding s os \<equiv> ARG_MAX
    (\<lambda>as. T' (I s) {\<omega> \<in> space S. \<exists>xs \<omega>'. \<omega> = xs @- \<omega>' \<and> map fst xs = as \<and> map snd xs = os}) _.
    True"

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

lemma
  "T (s, o\<^sub>0) {\<omega> \<in> space S. L (o\<^sub>1 # os) \<omega>} =
   (\<integral>\<^sup>+ t.
     ennreal (pmf (\<O> t) o\<^sub>1) * T (t, o\<^sub>1) {\<omega> \<in> space S. \<exists> xs \<omega>'. \<omega> = xs @- \<omega>' \<and> map snd xs = os}
   \<partial>measure_pmf (\<K> s))"
  apply (subst emeasure_Collect_T[unfolded space_T])
  apply (measurable; fail)
   apply (simp add: K_def)
   apply (rule nn_integral_cong_AE)
   apply (rule AE_I2)
  subgoal for s'
    apply (subst nn_integral_measure_pmf)
    apply (subst nn_integral_cong_AE
        [where v = "\<lambda> o\<^sub>2. if o\<^sub>2 = o\<^sub>1 then ennreal (pmf (\<O> s') o\<^sub>1) * T (s', o\<^sub>1) {\<omega> \<in> space S. \<exists> xs \<omega>'. \<omega> = xs @- \<omega>' \<and> map snd xs = os} else 0"]
          )
     apply (rule AE_I2)
     apply (auto split: if_split)
      apply (simp add: K_def)
      apply (rule arg_cong2[where f = times, OF HOL.refl])
      apply (rule arg_cong2[where f = emeasure, OF HOL.refl])
    subgoal
      apply auto
       apply force
      by (metis list.simps(9) shift.simps(2) snd_conv)
     apply (subst (asm) arg_cong2[where f = emeasure and d = "{}", OF HOL.refl])
      apply (auto; fail)
     apply (simp; fail)
apply (subst nn_integral_cong_AE
        [where v = "\<lambda> o\<^sub>2. ennreal (pmf (\<O> s') o\<^sub>1) * T (s', o\<^sub>1) {\<omega> \<in> space S. \<exists> xs \<omega>'. \<omega> = xs @- \<omega>' \<and> map snd xs = os} * indicator {o\<^sub>1} o\<^sub>2"]
          )
     apply (rule AE_I2)
     apply (auto; fail)
    apply (simp add: K_def)
    done
  done

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
    apply (simp add: K_def)
    apply (rule nn_integral_cong_AE[OF AE_I2])
    apply (rule *[simplified K_def])
    done
  finally show ?thesis .
qed

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

abbreviation (input) "V os as \<omega> \<equiv> (\<exists> \<omega>'. \<omega> = zip as os @- \<omega>')"

lemma emeasure_T_state_Nil:
  "T (s, o\<^sub>0) {\<omega> \<in> space S. V [] as \<omega>} = 1"
  by simp

lemma max_prob_T_state_Nil:
  "Max {T (s, o) {\<omega> \<in> space S. V [] as \<omega>} | as. length as = length [] \<and> set as \<subseteq> \<S>} = 1"
  by (simp add: emeasure_T_state_Nil)

lemma measurable_V[measurable]:
  "Measurable.pred S (\<lambda>\<omega>. V os as \<omega>)"
  sorry

lemma max_prob_Cons:
  "Max {T (s, o\<^sub>1) {\<omega> \<in> space S. V (o # os) as \<omega>} | as. length as = length (o # os) \<and> set as \<subseteq> \<S>} =
  (
    Max {ennreal (pmf (\<O> t) o * pmf (\<K> s) t) *
      Max {T (t, o) {\<omega> \<in> space S. V os as \<omega>} | as. length as = length os \<and> set as \<subseteq> \<S>} | t. t \<in> \<S>}
  )" (is "?l = ?r")
proof -
  let ?P = "\<lambda>as os. length as = length os \<and> set as \<subseteq> \<S>"
  have P_finite: "finite {as. ?P as os}" for os :: "'t list"
    using finite_lists_length_eq[OF \<open>finite \<S>\<close>] by (rule finite_subset[rotated]) auto
  have P_nonempty: "{as. ?P as os} \<noteq> {}" for os :: "'t list"
  proof -
    let ?a = "SOME a. a \<in> \<S>" let ?as = "replicate (length os) ?a"
    from \<open>\<S> \<noteq> {}\<close> have "?a \<in> \<S>"
      by (auto intro: someI_ex)
    then have "?as \<in> {as. ?P as os}"
      by auto
    then show ?thesis
      by force
  qed
  let ?f = "\<lambda>t as os. T t {\<omega> \<in> space S. V os as (t ## \<omega>)}"
  let ?g = "\<lambda>t as os. T t {\<omega> \<in> space S. V os as \<omega>}"
  have *: "?f t as (o # os) = ?g t (tl as) os * indicator {(hd as, o)} t" if "as \<noteq> []" for t as
    unfolding indicator_def using that by (cases as) auto
  have "{\<integral>\<^sup>+ t. ?f t as (o # os) \<partial>K (s, o\<^sub>1) |as. ?P as (o # os)}
      = {\<integral>\<^sup>+ t. ?g t (tl as) os * indicator {(hd as, o)} t \<partial>K (s, o\<^sub>1) |as. ?P as (o # os)}"
    (* TODO: better congruence rules than Collect_cong? *)
    apply safe
     apply (subst *; auto; fail)
    subgoal for _ as
      by (rule exI[where x = as]) (subst *; auto)
    done
  then have *: "{\<integral>\<^sup>+ t. ?f t as (o # os) \<partial>K (s, o\<^sub>1) |as. ?P as (o # os)} =
      (\<lambda>as. \<integral>\<^sup>+ t. ?g t (tl as) os * indicator {(hd as, o)} t \<partial>K (s, o\<^sub>1)) ` {as. ?P as (o # os)}"
    by auto
  have **: "K (s, o\<^sub>1) {(t, o)} = pmf (\<O> t) o * pmf (\<K> s) t"
    for t
    unfolding K_def
    apply (simp add: vimage_def)
    apply (subst arg_cong2[where
          f = nn_integral and d = "\<lambda> x. \<O> x {xa. xa = o \<and> x = t} * indicator {t} x",
          OF HOL.refl])
    subgoal
      by (auto simp: indicator_def)
    by (simp add: emeasure_pmf_single ennreal_mult')
  have "?l = Max {\<integral>\<^sup>+ t. ?f t as (o # os) \<partial>K (s, o\<^sub>1) | as. ?P as (o # os)}"
    by (subst emeasure_Collect_T[unfolded space_T]; rule measurable_V HOL.refl)
  also have "\<dots> =
    Max ((\<lambda>as. \<integral>\<^sup>+ t. ?g t (tl as) os * indicator {(hd as, o)} t \<partial>K (s, o\<^sub>1)) ` {as. ?P as (o # os)})"
    by (subst *) (simp add: **)
  also have "\<dots> = ?r"
  proof ((rule Max_eq_if; clarsimp?), goal_cases)
    case 1
    then show ?case
      using P_finite[of "o # os"] by auto
  next
    case 2
    then show ?case
      using \<open>finite \<S>\<close> by auto
  next
    case prems: (3 as)
    let ?p = "ennreal (pmf (\<O> (hd as)) o * pmf (\<K> s) (hd as))"
    let ?w = "Max {T (hd as, o) {\<omega> \<in> space S. \<exists>\<omega>'. \<omega> = zip bs os @- \<omega>'} |bs. ?P bs os}"
    have "?w * ?p = ?p * ?w"
      by (simp add: algebra_simps)
    moreover have "?g (hd as, o) (tl as) os * ?p \<le> ?w * ?p"
      apply (rule mult_right_mono)
       apply (rule Max_ge)
      subgoal
        using [[simproc add: finite_Collect]] by (auto intro: finite_subset[OF _ P_finite])
      using prems by (cases as; auto)+
    moreover from prems have "hd as \<in> \<S>"
      by (metis list.set_sel(1) list.size(3) nat.distinct(1) subset_eq)
    ultimately show ?case
      by (auto simp add: **)
  next
    case prems: (4 t)
    have "{?g (t, o) as os |as. ?P as os} = (\<lambda>as. ?g (t, o) as os) ` {as. ?P as os}"
      by auto
    with Max_in[OF finite_imageI, OF P_finite, of "\<lambda> as. ?g (t, o) as os" os] obtain as where
      "Max {?g (t, o) as os |as. ?P as os} = ?g (t, o) as os" "?P as os"
      using P_nonempty by atomize_elim auto
    with prems show ?case
      by simp (rule exI[where x= "t # as"], auto simp: algebra_simps **)
  qed
  finally show ?thesis .
qed

fun viterbi_prob where
  "viterbi_prob s t_end [] = indicator {t_end} s" |
  "viterbi_prob s t_end (o # os) =
    (MAX t \<in> \<S>. ennreal (pmf (\<O> t) o * pmf (\<K> s) t) * viterbi_prob t t_end os)"

lemma init_V_measurable[measurable]:
  "Measurable.pred S (\<lambda>x. \<exists>o \<omega>'. x = (s, o) ## zip as os @- \<omega>')"
  sorry

lemma T_init_V_eq:
  "T (s, o) {\<omega> \<in> space S. V os as \<omega>} = T (s, o') {\<omega> \<in> space S. V os as \<omega>}"
  apply (subst emeasure_Collect_T[unfolded space_T], (measurable; fail))
  apply (subst (2) emeasure_Collect_T[unfolded space_T], (measurable; fail))
  apply (simp add: K_def)
  done

definition
  "max_prob s os =
  Max {T' (I s) {\<omega> \<in> space S. \<exists>o \<omega>'. \<omega> = (s, o) ## zip as os @- \<omega>'}
       | as. length as = length os \<and> set as \<subseteq> \<S>}"

(* TODO: Duplication with likelihood_init *)
lemma max_prob_init:
  "max_prob s os = Max {T (s,o) {\<omega> \<in> space S. V os as \<omega>} | as. length as = length os \<and> set as \<subseteq> \<S>}"
proof -
  have *: "(\<Sum>o\<in>\<O>\<^sub>s. emeasure (T (s, o)) {\<omega> \<in> space S. V os as \<omega>}) =
    of_nat (card \<O>\<^sub>s) * emeasure (T (s, o)) {\<omega> \<in> space S. V os as \<omega>}" for as
    by (subst sum_constant[symmetric]) (fastforce intro: sum.cong T_init_V_eq[simplified])
  show ?thesis
    unfolding max_prob_def
    apply (subst emeasure_T')
    subgoal for as
      by measurable
    using *
    apply (simp add: I_def in_S observations_finite observations_wellformed nn_integral_pmf_of_set)
    apply (subst mult.commute)
    apply (simp add: observations_finite observations_wellformed mult_divide_eq_ennreal)
    done
qed

lemma max_prob_Nil[simp]:
  "max_prob s [] = 1"
  unfolding max_prob_init[where o = obs] by auto

lemma Max_start:
  "(MAX t\<in>\<S>. (indicator {t} s :: ennreal)) = 1" if "s \<in> \<S>"
  using \<open>finite \<S>\<close> that by (auto simp: indicator_def intro: Max_eqI)

lemma Max_image_commute:
  "(MAX x \<in> \<S>. MAX y \<in> \<S>. f x y) = (MAX y \<in> \<S>. MAX x \<in> \<S>. f x y)"
proof (rule Max_eq_if, goal_cases)
  case 3
  { fix a assume "a \<in> \<S>"
    with Max_in[OF finite_imageI[OF \<open>finite \<S>\<close>], of "f a"] have "Max (f a ` \<S>) \<in> f a ` \<S>"
      by auto
    then obtain b where "f a b = Max (f a ` \<S>)" "b \<in> \<S>"
      by auto
    from \<open>a \<in> \<S>\<close> have "f a b \<le> (MAX a\<in>\<S>. f a b)"
      by (auto intro: Max_ge finite_imageI[OF \<open>finite \<S>\<close>])
    with \<open>f a b = _\<close> \<open>b \<in> \<S>\<close> have "\<exists>b\<in>\<S>. Max (f a ` \<S>) \<le> (MAX a\<in>\<S>. f a b)"
      by auto
  }
  then show ?case
    by auto
next
  case 4
  { fix b assume "b \<in> \<S>"
    with Max_in[OF finite_imageI[OF \<open>finite \<S>\<close>], of "\<lambda> a. f a b"] have
      "(MAX a \<in> \<S>. f a b) \<in> (\<lambda>a. f a b) ` \<S>"
      by auto
    then obtain a where "f a b = (MAX a \<in> \<S>. f a b)" "a \<in> \<S>"
      by auto
    from \<open>b \<in> \<S>\<close> have "f a b \<le> Max (f a ` \<S>)"
      by (auto intro: Max_ge finite_imageI[OF \<open>finite \<S>\<close>])
    with \<open>f a b = _\<close> \<open>a \<in> \<S>\<close> have "\<exists>a\<in>\<S>. (MAX a\<in>\<S>. f a b) \<le> Max (f a ` \<S>)"
      by auto
  }
    then show ?case
      by auto
  qed (use \<open>finite \<S>\<close> in auto)

lemma Max_image_left_mult:
  "(MAX x \<in> \<S>. c * f x) = (c :: ennreal) * (MAX x \<in> \<S>. f x)"
  apply (rule Max_eqI)
  subgoal
    using \<open>finite \<S>\<close> by auto
  subgoal for y
    using \<open>finite \<S>\<close> by (auto intro: mult_left_mono)
  subgoal
    using Max_in[OF finite_imageI[OF \<open>finite \<S>\<close>], of f] \<open>\<S> \<noteq> {}\<close> by auto
  done

lemma Max_to_image:
  "Max {f t | t. t \<in> TT} = Max (f ` TT)"
  by (rule arg_cong[where f = Max]) auto

lemma Max_image_cong:
  "Max (f ` TT) = Max (g ` RR)" if "TT = RR" "\<And>x. x \<in> RR \<Longrightarrow> f x = g x"
  by (intro arg_cong[where f = Max] image_cong[OF that])

lemma Max_V_viterbi:
  "(MAX t \<in> \<S>. viterbi_prob s t os) =
   Max {T (s, o) {\<omega> \<in> space S. V os as \<omega>} | as. length as = length os \<and> set as \<subseteq> \<S>}" if "s \<in> \<S>"
  using that
  by (induction os arbitrary: s o; simp
        add: Max_start max_prob_Cons[simplified] Max_image_commute Max_image_left_mult Max_to_image
        cong: Max_image_cong
      )

lemma max_prob_viterbi:
  "(MAX t \<in> \<S>. viterbi_prob s t os) = max_prob s os" if "s \<in> \<S>"
  using max_prob_init[of s os] Max_V_viterbi[OF \<open>s \<in> \<S>\<close>, symmetric] by simp

end (* Finite state set *)

end (* Hidden Markov Model *)

end (* Theory *)