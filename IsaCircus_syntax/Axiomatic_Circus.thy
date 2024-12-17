
section \<open> Axiomatic Circus \<close>

theory Axiomatic_Circus
  imports 
    "Shallow-Expressions-Z.Shallow_Expressions_Z" 
    "Z_Toolkit.Channels_Events"
    "Z_Toolkit.Action_Command"
    "Abstract_Prog_Syntax.Abstract_Prog_Syntax"
begin

no_notation funcset (infixr "\<rightarrow>" 60)

subsection \<open> Types and Constants \<close>


text \<open> We declare an abstract type for Circus actions, which is parametrised by
  type @{typ "'e"} for the events, and @{typ "'s"} for the state. In the long
  term, this should be replaced with a type definition, but for now we are
  constructing an axiomatic theory. \<close>

typedecl ('e, 's) "action"

text \<open> We then declare a type synonym for processes, which is simply an action
  where the state type is unitary (or empty). This is because a process has no visible state. \<close>
type_synonym 'e process = "('e, unit) action"


type_synonym ('a, 'e) chan = "'a \<Longrightarrow>\<^sub>\<triangle> 'e"
\<comment> \<open> a channel is a prism (from a part to a whole), "int \<Longrightarrow>\<triangle> mychan", so , 'a is the value of the event type,
 'e is the channel type(the source).\<close> 

(*why is event not used?*)
typ "('a, 'e) chan"


text \<open> Having defined our types, we proceed to axiomatise the individual operators
  of Circus actions and processes. \<close>

term map


axiomatization
  
  \<comment> \<open> An assignment is represented using a state update function.
       This allows us to express both single and multi-variable assignments. \<close>
  cassigns :: "('s \<Rightarrow> 's) \<Rightarrow> ('e, 's) action" and 
  (*all three 's are state  ? it is the state type .'s can be any type and will be inferred when instantiated? *)

  \<comment> \<open> Sequential composition executes one action after another \<close>
  cseq :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" and
  
  \<comment> \<open> Interrupt allows the first action to be interrupted by the second \<close>
  cinterrupt :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" (infixl "\<triangle>" 55) and
  \<comment> \<open>The operator syntax defined here because all the parameters are logic. Logic can be 
      directly parsed by Isabelle parser. SO we can omit the syntax definition and 
    translation procedure for interrupt\<close>

(*  \<comment> \<open> An event input takes a channel in event type @{typ "'e"} (i.e. a prism) and
       an action indexed by the data type of the channel @{typ "'a"}.
       The effect is to instantiate the action with the value input on the channel. \<close>

 cinput :: "('a, 'e) chan \<Rightarrow> ('a \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" and

\<comment> \<open>we can not remove parathesis  ('a \<Rightarrow> ('e, 's) action), this is a function type.
     "action is indexed" by the event, because the event may decide the behaivour of 
    action.\<close>
*)

(*
  coutput :: "('a, 'e) chan \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" and
*)

  \<comment> \<open> A guard is modelled with a bool expresssion (i.e. a predicate) and the action
       that should be enabled when the guard is true. \<close>
  cguard :: "(bool, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" and
  (*in (bool, 's) expr, 's is the state, and bool value is the current value of 's ? *)
  \<comment> \<open>the syntax of cguard can not be defined here although all paramters are logic.
    Because the first logic is actully a expression, it therefore involves lifting parser and this 
    can not be directly parsed by Isabelle.\<close>
  
  \<comment> \<open> We represent an internal choice as a set of possible choices in @{typ "'i"}
      followed by an action indexed by @{typ "'i"}. \<close>
  cIChoice :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" and

  \<comment> \<open> We represent an external choice as a set of possible choices in @{typ "'i"}
      followed by an action indexed by @{typ "'i"}. \<close>
  cEChoice :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" and 

  \<comment> \<open> Renaming is implemented using a renaming function, which maps every event
       of the input action to another event in the output action. \<close>
  crenaming :: "('e \<leftrightarrow> 'f) \<Rightarrow> ('e, 's) action \<Rightarrow> ('f, 's) action" and
  (*channel renaming?*)

  \<comment> \<open>crenaming :: "('e, 's) action \<Rightarrow> ('a, 'e) chan  \<Rightarrow> ('a, 'e) chan  \<Rightarrow> ('e, 's) action"
    this is generalized by function chan_rename \<close>

   \<comment> \<open>hiding is to make a set of events internal (invisible from the environment.)\<close>
   chide :: "('e, 's) action \<Rightarrow> 'e set \<Rightarrow> ('e, 's) action" and
   \<comment> \<open>   chide :: "('e, 's) action \<Rightarrow> ('a, 'e) chan \<Rightarrow> ('e, 's) action" this can only hide one channel. 
   This is generalized by the funciton chan_events which turn the channel 
    into a set of events\<close>
(*hide a set of events not a set of channels*)

   chidecs :: "('e, 's) action \<Rightarrow> 'i \<Rightarrow> ('e, 's) action" and


  \<comment> \<open>cprefix replaces coutput, cinput, csync. \<close>
  cprefix :: "('a, 'e) chan \<Rightarrow> ('a \<Rightarrow> (('s \<Rightarrow> bool) \<times> ('e, 's) action)) \<Rightarrow> ('e, 's) action" and
  \<comment> \<open>cprefix takes two parameters: a channel ('a, 'e) chan, and  a
  lambda expr ('a \<Rightarrow> (('s \<Rightarrow> bool) \<times> ('e, 's) action)) that returns a pair  (('s \<Rightarrow> bool) \<times> ('e, 's) action)), 
  the first elem of pair is the condition ('s \<Rightarrow> bool) 
  the second of pair is the action ('e, 's) action).
 \<close>

 \<comment> \<open> parallel allows two actions synchronizing on the event set \<close>
  cparallel :: "('e, 's) action \<Rightarrow> 'e set \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" and

  cInterleave :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" and

  cParallelIte :: "'e set \<Rightarrow> 'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" and 

  cParam :: " 'i set \<Rightarrow>  ('e, 's) action \<Rightarrow> ('e, 's) action" and  

  cProcess :: "('e, 's) action \<Rightarrow> 'e process" 


\<comment> \<open>cinput, coutput, csync, dotin and coutinp are defined by cprefix\<close>
definition cinput :: "('a, 'e) chan \<Rightarrow> ('a \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where
"cinput c A = cprefix c (\<lambda> v. ((\<lambda> s. True), A v))"
\<comment> \<open>cprefix takes two parameters: c is the channel, (\<lambda> v. ((\<lambda> s. True), A v)) is a
lambda expr returns a pair, the fist elem of pair is the condition (\<lambda> s. True)
the second of pair is the action A.
v is the value to be output, i.e., the value of the channel c\<close>
\<comment> \<open>the input communication input the value to a variable\<close>


definition csync :: "(unit, 'e) chan \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" where
"csync c A = cprefix c (\<lambda> v. (\<lambda> s. True, A))"


definition coutput :: "('a, 'e) chan \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" where
"coutput c e A = cprefix c (\<lambda> v::'a. ((\<lambda> s::'s. v = e(s)), A))"
\<comment> \<open>the output communication output an expression, so the second parameter is an expr\<close>
\<comment> \<open>"coutput c e A = cprefix c (\<lambda> v. ((\<lambda> s. v = e(s)), A))" also works, because Isabelle can infer the types of v and s\<close>



definition coutinp :: "('a \<times> 'b, 'e) chan \<Rightarrow> ('s \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"coutinp c v A = cprefix c (\<lambda> (x, y). (\<lambda> s. x = v s, A y))"

definition coutinp' :: "('a \<times> 'b, 'e) chan \<Rightarrow> ('a, 's) expr  \<Rightarrow> ('b \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"coutinp' c e A = cprefix c (\<lambda> (x, y). (\<lambda> s. x = e(s), A y))"



definition cdotinp :: "('a \<times> 'b, 'e) chan \<Rightarrow> ('a, 's) expr  \<Rightarrow> ('b \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"cdotinp c e A = cprefix c (\<lambda> (x, y). (\<lambda> s. x = e(s), A y))"

definition cdotdot :: "('a \<times> 'b, 'e) chan \<Rightarrow> ('a, 's) expr \<Rightarrow> ('b, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" where 
"cdotdot c e1 e2 A = cprefix c (\<lambda> (x, y). (\<lambda> s. x = e1(s) \<and> y = e2(s), A))"




definition cdotdotinp :: "('a \<times> 'b \<times> 'c, 'e) chan \<Rightarrow>('a, 's) expr \<Rightarrow> ('b, 's) expr  \<Rightarrow> ('c \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"cdotdotinp c e1 e2 A = cprefix c (\<lambda> (x, y, z). (\<lambda> s. x = e1(s) \<and> y = e2(s), A z))"


definition cdotdotout :: "('a \<times> 'b \<times> 'c, 'e) chan \<Rightarrow>('a, 's) expr \<Rightarrow> ('b, 's) expr \<Rightarrow>('c, 's) expr  \<Rightarrow>  ('e, 's) action \<Rightarrow> ('e, 's) action" where 
"cdotdotout c e1 e2 e3 A = cprefix c (\<lambda> (x, y, z). (\<lambda> s. x = e1(s) \<and> y = e2(s)  \<and> z = e3(s), A))"



definition cdotdotdotinp :: "('a \<times> 'b \<times> 'c \<times> 'd, 'e) chan \<Rightarrow>('a, 's) expr \<Rightarrow> ('b, 's) expr   \<Rightarrow> ('c, 's) expr \<Rightarrow> ('d \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"cdotdotdotinp c e1 e2 e3 A = cprefix c (\<lambda> (x, y, z, w). (\<lambda> s. x = e1(s) \<and> y = e2(s) \<and> z = e3(s), A w))"



(* c!v?y \<rightarrow> P *)

chantype chan1 = evt1:: int evt2:: string
term "prism_build  chan1 evt1"
term "prism_match chan1 evt1"

adhoc_overloading useq cseq

text \<open> We can now define several Circus operators in terms of those axiomatised
  above. \<close>

\<comment> \<open>These operators are defined by definition (as functions using axioms?)  instead of axiomatization, 
  because these are simple. The axiomatization should be as minimum core.\<close>

definition Skip :: "('e, 's) action" where
"Skip = cassigns id"

definition Chaos :: "('e, 's) action" where
"Chaos = cIChoice (UNIV::int set) (\<lambda> i. Skip)"

definition Miracle :: "('e, 's) action" where
"Miracle = cIChoice ({}::bool set) (\<lambda> i. Skip)"

definition Stop :: "('e, 's) action" where
"Stop = cEChoice ({}::bool set) (\<lambda> i. Skip)"

definition cichoice :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow>
 ('e, 's) action" (infixl "\<sqinter>" 59) where
  "cichoice P Q = cIChoice {True, False} (\<lambda> b. if b then P else Q)"

definition cechoice :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow>
 ('e, 's) action" (infixl "\<box>" 59) where
  "cechoice P Q = cEChoice {True, False} (\<lambda> b. if b then P else Q)"

\<comment> \<open>These definitions give the operators both syntax and semantics.\<close>


subsection \<open> Syntax \<close>

bundle Circus_Syntax
begin

unbundle Expression_Syntax

no_notation disj (infixr "|" 30)
no_notation conj (infixr "&" 35)
no_notation funcset (infixr "\<rightarrow>" 60)

no_syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /\<mapsto>/ _")
  ""         :: "maplet \<Rightarrow> updbind"              ("_")
  ""         :: "maplet \<Rightarrow> maplets"             ("_")
  "_Maplets" :: "[maplet, maplets] \<Rightarrow> maplets" ("_,/ _")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"           ("(1[_])")


end

text \<open> The types of the syntax translations represent categories in the Isabelle
  parser. 
  \<^item> @{typ id} is an identifier (i.e. a name)
  \<^item> @{typ pttrn} is a pattern, which is typically use to pattern 
    match on a parameter (e.g. @{term "\<lambda> (x, y). f x y"}.
  \<^item> @{typ logic} corresponds to any term constructable in HOL \<close>

syntax 
 \<comment> \<open> "_cseq" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ ; _" [50, 51] 50) 
    no need to define cseq syntax, cseq is overloading useq
  "_cinterrupt" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<triangle> _" [50, 51] 50)
  (*Can interrupt be defined using definition, just like cechoice??*)\<close>

  "_cinput" :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?_ \<rightarrow> _" [61, 0, 62] 62)

  "_coutput" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>!_ \<rightarrow> _" [61, 0, 62] 62)

  "_cdot" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>._ \<rightarrow> _" [61, 0, 62] 62)
  \<comment> \<open>_._ is parsed as a whole, so bolded here to avoid conflict\<close>

  "_coutinp" :: "id \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>!_\<^bold>?_ \<rightarrow> _" [61, 0, 0, 62] 62)

  "_cdotinp" :: "id \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>?_ \<rightarrow> _" [61, 0, 0, 62] 62)


  "_cdotdot" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._ \<rightarrow> _" [61, 0, 0, 62] 62)


  "_cdotdotinp" :: "id \<Rightarrow> logic   \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._\<^bold>?_ \<rightarrow> _" [61, 0,0, 0, 62] 62)


  "_cdotdotout" :: "id \<Rightarrow> logic   \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._\<^bold>!_ \<rightarrow> _" [61, 0,0, 0, 62] 62)

  "_cdotdotdotinp" :: "id \<Rightarrow> logic \<Rightarrow> logic  \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._\<^bold>._\<^bold>?_ \<rightarrow> _" [61, 0,0,0, 0, 62] 62)


  "_csync" :: "id \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow> _" [61, 62] 61)
  "_cguard" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>& _" [60, 61] 60)

  \<comment> \<open>the order of the parameters does not need to match the definition.\<close>
  "_crenaming" :: "logic \<Rightarrow> rnenum \<Rightarrow> logic" ("_ [_]" [60, 0] 60)  

  "_chide" :: "logic \<Rightarrow> chans \<Rightarrow> logic" ("_ \<Zhide> \<lbrace>_\<rbrace>" [50, 51] 50)
  "_chidecs" :: "logic \<Rightarrow> id \<Rightarrow> logic" ("_ \<Zhide> _" [50, 51] 50)(*TBC to hide a channelset cs?*)

  "_cparallel" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk> | _ | \<rbrakk> _" [50, 0,  51] 50)
 
  "_cEChoice" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<box> _ \<in> _ \<bullet> _")

  "_cInterleave" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<interleave> _ \<in> _ \<bullet> _" [0, 0, 10] 10) 
  \<comment> \<open>\<interleave> i\<in>{1..inpSize} \<bullet> NodeIn(l,n,i)\<close>

  "_cParallelIte" :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrakk> _ \<rbrakk> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  
  "_cParam" :: "pttrn \<Rightarrow>  logic \<Rightarrow> logic" ("_ \<bullet> _" [10, 0] 10)(*TBC*) 

term "P \<box> Q"
term "P \<sqinter> Q"

(* \<lbrace> c \<mapsto> d \<rbrace> *)

translations
 \<comment> \<open> "_cseq P Q" == "CONST cseq P Q "   
  "_cinterrupt P Q" == "CONST cinterrupt P Q " \<close>

\<comment> \<open>A is a set, P is process\<close>
 
  "_cinput c x  P" == "CONST cinput c (\<lambda> x. P)"
  "_coutput c e P" == "CONST coutput c (e)\<^sub>e P"
  "_coutinp c e x P" == "CONST coutinp c (e)\<^sub>e (\<lambda> x. P)"
  "_cdotinp c e x P" == "CONST cdotinp c (e)\<^sub>e (\<lambda> x. P)"

  "_cdotdot c e1 e2 P" == "CONST cdotdot c (e1)\<^sub>e (e2)\<^sub>e P" 
  "_cdotdotinp c e1 e2 x P" == "CONST cdotdotinp c  (e1)\<^sub>e (e2)\<^sub>e (\<lambda> x. P)"

  "_cdotdotout c  e1 e2 e3 P" == "CONST cdotdotout c  (e1)\<^sub>e (e2)\<^sub>e (e3)\<^sub>e P" 
  "_cdotdotdotinp c  e1 e2 e3 x P" == "CONST cdotdotdotinp c  (e1)\<^sub>e (e2)\<^sub>e (e3)\<^sub>e (\<lambda> x. P)"  

  "_cguard b P" == "CONST cguard (b)\<^sub>e P"
  "_cdot c e P" == "CONST coutput c (e)\<^sub>e P"
  "_csync c P" == "CONST csync c P"
  "_crenaming P rn" == "CONST crenaming (_rnenum rn) P" 
  "_chide P es" == "CONST chide P (_ch_enum es)"
  "_chidecs P c" == "CONST chidecs P c" 
  "_cparallel P A Q" == "CONST cparallel P A Q " 
  "_cEChoice i A P" == "CONST cEChoice A (\<lambda> i. P)"
  "_cInterleave i A P" == "CONST cInterleave A (\<lambda> i. P)"

  "_cParallelIte B i A P" == "CONST cParallelIte B A (\<lambda> i. P)"
  "_cParam x P" => "\<lambda> x. P"

term "a\<^bold>.v"


term "a\<^bold>.v\<^bold>?x \<rightarrow> P"

term "a\<^bold>?x \<rightarrow> P"

term "c\<^bold>!e\<^bold>?x \<rightarrow> A x"

term "\<interleave> i\<in>{1..s} \<bullet> P(i)"

term "\<box> i\<in>{1..s} \<bullet> P(i)"

subsection \<open> Axioms \<close>

\<comment> \<open>we need to add more algebiac laws as axioms, refer to Marcel's thesis and CSP book.\<close>
axiomatization where
  action_complete_lattice: "OFCLASS(('e, 's) action, complete_lattice_class)" and
  cseq_left_id: "Skip ;; P = P" and
  cseq_right_id: "P ;; Skip = P" and
  cseq_assoc: "(P::('e, 's) action) ;; (Q ;; R) = (P ;; Q) ;; R" and
  crenaming_id: "crenaming Id P = P" and
  cparallel_commute: "cparallel P A Q = cparallel Q A P"

instance "action" :: (type, type) complete_lattice
  sorry

term lfp

lemma "P ;; Q ;; R = P ;; (Q ;; R)"
  by (simp add: cseq_assoc)


end