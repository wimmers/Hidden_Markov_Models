theory Hidden_Markov_Model
  imports Markov_Models.Discrete_Time_Markov_Chain
begin

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

lemma
  "space (T s) = space S"
  by (rule space_T)

thm emeasure_Collect_T[unfolded space_T]

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
  thm K_def
   apply (simp add: K_def)
   apply (rule nn_integral_cong_AE)
   apply (rule AE_I2)
  subgoal for s'
    apply (subst nn_integral_measure_pmf)
    term indicator
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
   (\<integral>\<^sup>+ t.
     ennreal (pmf (\<O> t) o\<^sub>1) * T (t, o\<^sub>1) {\<omega> \<in> space S. L os \<omega>}
   \<partial>measure_pmf (\<K> s))" (is "?l = ?r")
proof -
  have *: "\<integral>\<^sup>+ y. emeasure (T (s', y))
            {x \<in> space S. \<exists>xs. (\<exists>\<omega>'. (s', y) ## x = xs @- \<omega>') \<and> map snd xs = o\<^sub>1 # os}
       \<partial>measure_pmf (\<O> s') = ennreal (pmf (\<O> s') o\<^sub>1) *
    emeasure (T (s', o\<^sub>1)) {\<omega> \<in> space S. \<exists>xs. (\<exists>\<omega>'. \<omega> = xs @- \<omega>') \<and> map snd xs = os}"
    (is "?L = ?R") for s'
  proof -
    have "?L = \<integral>\<^sup>+ x. ennreal (pmf (\<O> s') x) *
           emeasure (T (s', x))
            {\<omega> \<in> space S.
             \<exists>xs. (\<exists>\<omega>'. (s', x) ## \<omega> = xs @- \<omega>') \<and> map snd xs = o\<^sub>1 # os}
       \<partial>count_space UNIV"
      by (rule nn_integral_measure_pmf)
    also have "\<dots> =
      \<integral>\<^sup>+ o\<^sub>2. (if o\<^sub>2 = o\<^sub>1
              then ennreal (pmf (\<O> s') o\<^sub>1) *
                   emeasure (T (s', o\<^sub>1)) {\<omega> \<in> space S. \<exists>xs \<omega>'. \<omega> = xs @- \<omega>' \<and> map snd xs = os}
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
       (ennreal (pmf (\<O> s') o\<^sub>1) *
        emeasure (T (s', o\<^sub>1)) {\<omega> \<in> space S. \<exists>xs \<omega>'. \<omega> = xs @- \<omega>' \<and> map snd xs = os})
      \<partial>count_space UNIV"
      by (rule nn_integral_cong_AE) auto
    also have "\<dots> = ?R"
      by simp
    finally show ?thesis .
  qed
  have "?l =
    \<integral>\<^sup>+ t. emeasure (T t) {x \<in> space S. \<exists>xs \<omega>'. t ## x = xs @- \<omega>' \<and> map snd xs = o\<^sub>1 # os}
       \<partial>measure_pmf (K (s, o\<^sub>0))"
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

end (* Hidden Markov Model *)

end (* Theory *)