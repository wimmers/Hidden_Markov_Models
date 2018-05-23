theory HMM_Example
  imports HMM_Implementation
begin

section \<open>Example\<close>

text \<open>The ice cream example from Jurafsky and Martin \cite{Jurafsky}.\<close>

definition
  "states = [''start'', ''hot'', ''cold'', ''end'']"

definition observations :: "int list" where
  "observations = [0, 1, 2, 3]"

definition
  "kernel =
    [
      (''start'', [(''hot'',0.8 :: real), (''cold'',0.2)]),
      (''hot'',   [(''hot'',0.6 :: real), (''cold'',0.3), (''end'', 0.1)]),
      (''cold'',  [(''hot'',0.4 :: real), (''cold'',0.5), (''end'', 0.1)]),
      (''end'',   [(''end'', 1)])
    ]"

definition
  "emissions =
    [
      (''hot'',   [(1, 0.2), (2, 0.4), (3, 0.4)]),
      (''cold'',  [(1, 0.5), (2, 0.4), (3, 0.1)])
    ]
  "

global_interpretation Concrete_HMM kernel emissions observations states
  defines viterbi_inner = HMM_interp.viterbi_ix\<^sub>m'
  and viterbi = HMM_interp.viterbi
  and viterbi_final = HMM_interp.viterbi_final
  by (standard; eval)

lemmas [code] = HMM_interp.viterbi_ix\<^sub>m'.simps[unfolded O_code K_code]

code_thms viterbi_final

value "viterbi ''start'' ''end'' [1, 3, 1, 3, 1]"

value "viterbi ''start'' ''end'' [1, 2, 3, 1]"

value "viterbi ''start'' ''end'' [1, 1, 1, 1]"

value "viterbi ''start'' ''end'' [1, 1, 1]"

value "viterbi_final ''start'' [1, 1, 1, 1, 1, 1, 1]"

value "viterbi_final ''start'' [1, 1, 1, 1, 1, 1, 1, 3, 3, 3]"

value "viterbi_final ''start'' [1, 1, 1, 1]"

value "viterbi_final ''start'' [1, 1, 1]"

value "viterbi_final ''start'' [3, 1, 3]"

value "viterbi_final ''start'' [3, 1, 1]"

value "viterbi_final ''start'' [3, 1, 1, 3]"

value "viterbi_final ''start'' [1, 1]"

value "viterbi_final ''start'' [1]"

end