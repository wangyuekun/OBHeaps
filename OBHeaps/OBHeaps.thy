theory OBHeaps
imports
  "HOL-Library.Pattern_Aliases"
  Complex_Main
  "HOL-Library.Multiset"
  Priority_Queue_Specs
begin
(*** Definition of a tree  ***)
datatype 'a tree = Node (rank: nat) (root: 'a) (children: "'a tree list")
(*** Definition of a obheap  ***)
datatype 'a OBHeaps = Obheaps (minval: "'a option") (roots:"'a tree list") 

type_synonym 'a heap = "'a tree list"

thm tree.induct
thm OBHeaps.induct 
thm OBHeaps.case

(***truly minval ***)
definition "min_value fh = 
          (case fh of (Obheaps None _ ) \<Rightarrow> None |
                      (Obheaps (Some a) []) \<Rightarrow> None |
                      (Obheaps (Some a) xs) \<Rightarrow> minval fh)"
(***truly roots ***)
definition "root_trees fh =
          (case fh of (Obheaps None _ ) \<Rightarrow> [] |
          (Obheaps (Some a) []) \<Rightarrow> [] |
          (Obheaps (Some a) xs) \<Rightarrow> roots fh)"

fun root_trees_roots::"'a::linorder tree list \<Rightarrow> 'a list " where
 "root_trees_roots [] = []"|
 "root_trees_roots  (x#xs) = (root x)# root_trees_roots xs "

thm root_trees_roots.simps
(***A truly empty heap  ***) (**** but OBHeaps None _ & OBHeaps (Some a) [] as empty heap****)
definition empty_obheap::"'a OBHeaps" where  "empty_obheap = (Obheaps None []) "

(*** Example of a small root tree ***)
definition "B1 = Node 1 (6::nat) [Node 0 10 [] ]"
definition "B2 = Node 2 (8::nat) [Node 1 (10::nat) [Node 0 20 [] ] ,Node 0 15 [] ]"
definition "B3 = Node 3 (7::nat) [Node 2 (10::nat) [Node 1 (20::nat) [Node 0 25 [] ] ,Node 0 15 [] ] , Node 1 (15::nat) [Node 0 22 [] ] ,Node 0 (20::nat) [] ]"
definition "B4 = Node 3 (7::nat) [Node 2 (10::nat) [Node 1 (20::nat) [Node 0 25 []],Node 0 15 []], Node 1 (12::nat) [Node 0 22 []],Node 0 (23::nat) []]"
definition "B5 = [Node (1::nat) (7::nat) [Node 0 (30::nat) []],Node 2 24 [Node 1 26 [Node 0 35 []],Node 0 46 []],(Node (0::nat) (23::nat) []),Node 0 17 [],Node 1 18 [Node 0 39 []],Node 0 52 [],Node 1 41 [Node 0 44 []]]"
definition "B6 = Node 2 (3::nat) [(Node 0 4 []),(Node 0 5 [])]"
definition "B7 = Node 2 (1::nat) [(Node 0 2 []),(Node 0 3 [])]"

(*** Example of a small root obheap ***)
definition "fh0 = Obheaps None []"
definition "fh1 = Obheaps (Some 6) [B1,B2,B3,B4]"

fun is_empty_obheap:: "'a OBHeaps \<Rightarrow> bool" where
  "is_empty_obheap (Obheaps m ts) = ((m=None)\<or>(ts = []))"

subsubsection \<open> tree Invariants\<close>

fun invar_otree :: "'a::linorder tree \<Rightarrow> bool" where
"invar_otree (Node _ x  ts) \<longleftrightarrow> (\<forall>t\<in>set ts. invar_otree t \<and> x \<le> root t)"

fun invar_btree :: "'a::linorder tree \<Rightarrow> bool" where
"invar_btree (Node r x ts) \<longleftrightarrow>
   (\<forall>t\<in>set ts. invar_btree t) \<and> map rank ts = rev [0..<r]"

definition "invar_tree t \<longleftrightarrow> invar_otree t \<and> invar_btree t"

definition "invar ts \<longleftrightarrow> (\<forall>t\<in>set ts. invar_btree t) \<and> (sorted_wrt (<) (map rank ts))"

text \<open> OBHeaps invariant\<close>

definition "invar_trees ts \<longleftrightarrow>(if ts = [] then True else (\<forall>t\<in>set ts. invar_tree t)) "

fun invar_min::"'a::linorder OBHeaps \<Rightarrow> bool " where
"invar_min (Obheaps m ts) \<longleftrightarrow> (if (m=None)\<or>(ts=[]) then True else (the m) = Min (set(root_trees_roots ts))) "

fun invar_obheap ::"'a::linorder OBHeaps \<Rightarrow> bool " where
"invar_obheap heap \<longleftrightarrow> invar_min heap \<and> invar_trees (root_trees heap)"

lemma no_empty_obheap_min :"\<not> is_empty_obheap fh \<Longrightarrow> invar_obheap fh \<Longrightarrow>the (minval fh) = Min (set(root_trees_roots (roots fh))) "
  using is_empty_obheap.elims(3) by fastforce

(*** proof of empty_obheap  ***)
lemma invar_empty_obheap:"invar_obheap empty_obheap" 
  by (auto simp: invar_trees_def empty_obheap_def root_trees_def) 

lemma "invar_obheap (Obheaps (Some a) [])" 
  by (auto simp: invar_trees_def root_trees_def) 

lemma empty_obheap_eq:"is_empty_obheap (Obheaps m ts) \<longleftrightarrow> (m = None)\<or>(ts=[]) "
  by auto

(*** proof of no_empty_obheap  ***)

lemma no_empty_obheap_eq:"\<not> is_empty_obheap (Obheaps (Some a) (x#xs) ) "
  by auto

thm OBHeaps.simps
thm OBHeaps.collapse

lemma no_empty_obheap_invar_min:" \<not> is_empty_obheap fh \<Longrightarrow> the (minval fh) = Min (set(root_trees_roots (roots fh))) 
                                 \<Longrightarrow> invar_min fh"
  by (metis (no_types) OBHeaps.collapse invar_min.simps)

lemma no_empty_obheap_invar_trees:"\<not> is_empty_obheap fh \<Longrightarrow>(\<forall>t\<in>set (root_trees fh).invar_tree t) \<Longrightarrow> invar_trees (root_trees fh)"
  by (meson invar_trees_def)

lemma no_empty_obheap_invar :"\<not> is_empty_obheap fh \<Longrightarrow>(\<forall>t\<in>set (root_trees fh). invar_tree t) \<Longrightarrow>
                              the (minval fh) = Min (set(root_trees_roots (roots fh)))\<Longrightarrow>invar_obheap fh "
  by (meson invar_obheap.elims(3) no_empty_obheap_invar_min no_empty_obheap_invar_trees)
 
lemma invar_children:
  "invar_tree (Node r a ts) \<Longrightarrow> invar_trees ts" 
  by (simp add: invar_trees_def invar_tree_def)

thm OBHeaps.case_eq_if
thm OBHeaps.split
lemma noempty_roots: "\<not> is_empty_obheap fh \<Longrightarrow> root_trees fh \<noteq> []"
  apply(simp add:root_trees_def split:OBHeaps.split list.split option.split)
  using is_empty_obheap.simps by blast 
 
 
lemma noempty_eq_roots: "\<not> is_empty_obheap fh \<Longrightarrow>  roots fh = root_trees fh" 
  by(auto simp:root_trees_def split:OBHeaps.split list.split option.split)

(*** tree to multiset ***)
fun mset_tree :: "'a::linorder tree \<Rightarrow> 'a multiset" where
  "mset_tree (Node _ a ts) = {#a#} + (\<Sum>t\<in>#mset ts. mset_tree t)"

(*** trees to multiset ***)
definition mset_heap :: "'a::linorder heap  \<Rightarrow> 'a multiset" where
  "mset_heap ts = (\<Sum>t\<in>#mset ts. mset_tree t)"

(*** obheap to multiset ***)
fun mset_obheap :: "'a::linorder OBHeaps \<Rightarrow> 'a multiset" where
  "mset_obheap (Obheaps None _) = {#}"|
  "mset_obheap (Obheaps (Some a) []) = {#}"|
  "mset_obheap (Obheaps (Some a) xs) = mset_heap xs"

(***proof of mset_tree  ***)
lemma mset_tree_nonempty[simp]: "mset_tree t \<noteq> {#}"
by (cases t) auto

lemma root_in_mset[simp]: "root t \<in># mset_tree t"
by (cases t) auto

lemma mset_tree_simp_alt[simp]:
  "mset_tree (Node r a ts) = {#a#} + mset_heap ts"
  unfolding mset_heap_def by auto
declare mset_tree.simps[simp del]

(***proof of meset_trees ***)
lemma mset_trees_Nil[simp]:
  "mset_heap [] = {#}"
by (auto simp: mset_heap_def)

lemma mset_trees_Cons[simp]: "mset_heap (t#ts) = mset_tree t + mset_heap ts"
  by (auto simp: mset_heap_def)
lemma mset_trees_Cons':" mset_tree t + mset_heap ts =mset_heap (t#ts) "
  by (auto simp: mset_heap_def)
lemma mset_trees_empty_iff[simp]: "mset_heap ts = {#} \<longleftrightarrow> ts=[]"
  by (auto simp: mset_heap_def)

lemma mset_trees_rev_eq[simp]: "mset_heap (rev ts) = mset_heap ts"
by (auto simp: mset_heap_def)

(***proof of meset_obheap ***)
lemma mset_obheap_empty[simp]:
  "mset_obheap empty_obheap = {#}"
  by (auto simp: empty_obheap_def)

lemma mset_obheap_no_empty[simp]:
  assumes "\<not> is_empty_obheap fh"
  shows "mset_obheap fh = mset_heap (root_trees fh)"
  using assms
  apply(induct fh rule:mset_obheap.induct)
  by (auto simp: root_trees_def )

lemma mset_obheap_empty_iff[simp]: "mset_obheap fh = {#} \<longleftrightarrow> is_empty_obheap fh"
  by (metis mset_obheap.elims mset_obheap_no_empty mset_trees_empty_iff no_empty_obheap_eq noempty_roots)

subsection \<open>Operations and Their Functional Correctness\<close>

subsubsection \<open>\<open>link\<close>\<close>

context
includes pattern_aliases
begin

fun link :: "'a::linorder tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "link (Node r x\<^sub>1  ts\<^sub>1 =: t\<^sub>1 ) (Node r' x\<^sub>2  ts\<^sub>2=: t\<^sub>2) =
    (if x\<^sub>1\<le>x\<^sub>2 then Node (r+1) x\<^sub>1 (t\<^sub>2#ts\<^sub>1)  else Node (r+1) x\<^sub>2 (t\<^sub>1#ts\<^sub>2) )"

lemma invar_otree_link:
  assumes "invar_otree t\<^sub>1"
  assumes "invar_otree t\<^sub>2"
  shows "invar_otree (link t\<^sub>1 t\<^sub>2)"
  using assms 
  by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) auto

lemma invar_btree_link:
  assumes "invar_btree t\<^sub>1"
  assumes "invar_btree t\<^sub>2"
  assumes "rank t\<^sub>1 = rank t\<^sub>2"
  shows "invar_btree (link t\<^sub>1 t\<^sub>2)"
  using assms 
  by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) auto

lemma invar_tree_link:
  assumes "invar_tree t\<^sub>1"
  assumes "invar_tree t\<^sub>2"
  assumes "rank t\<^sub>1 = rank t\<^sub>2"
  shows "invar_tree (link t\<^sub>1 t\<^sub>2)"
  using assms
  by (simp add: invar_otree_link invar_btree_link invar_tree_def) 
 
lemma invar_btrees_link:
  assumes "invar_tree t\<^sub>1"
  assumes "invar_tree t\<^sub>2"
  assumes "rank t\<^sub>1 = rank t\<^sub>2"
  shows "invar_tree (link t\<^sub>1 t\<^sub>2)"
using assms unfolding invar_tree_def
  by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) auto

lemma rank_link[simp]: "rank (link t\<^sub>1 t\<^sub>2) = rank t\<^sub>1 + 1"
  by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) simp

lemma mset_link[simp]: "mset_tree (link t\<^sub>1 t\<^sub>2) = mset_tree t\<^sub>1 + mset_tree t\<^sub>2"
  by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) simp
end

subsubsection \<open>\<open>ins_tree\<close>\<close>

fun ins_tree :: "'a::linorder tree \<Rightarrow> 'a OBHeaps \<Rightarrow> 'a OBHeaps" where
  "ins_tree t (Obheaps None _)= (Obheaps  (Some(root t)) [t])"|
  "ins_tree t (Obheaps (Some a) []) = (Obheaps  (Some(root t)) [t])"|
  "ins_tree t (Obheaps (Some a) xs) = (if root t \<le> a 
                                    then (Obheaps  (Some(root t)) (t#xs)) 
                                    else (Obheaps  (Some a) (t#xs)))"

value "ins_tree (Node 3 (2::nat) []) fh0 "

lemma fheap0[simp]: "invar_tree (Node 0 x [])"
   by (simp add:invar_tree_def)

lemma invar_Cons[simp]:
  "invar_trees (t#ts)
  \<longleftrightarrow> invar_tree t  \<and> invar_trees ts "
by (auto simp: invar_trees_def)

lemma invar_ins_None:
  assumes "invar_tree t"
  shows "invar_obheap (ins_tree t empty_obheap)"
using assms 
  apply (induction t) 
  apply (simp add: invar_trees_def) 
  by(auto simp:empty_obheap_def root_trees_def )

lemma invar_ins_tree:
  assumes "invar_tree t"
  assumes "invar_obheap fh"
  shows "invar_obheap (ins_tree t fh)"
using assms
  apply (induction t fh rule: ins_tree.induct)
  apply (auto simp:invar_ins_None) 
  apply (auto simp: invar_trees_def root_trees_def)
  apply (metis List.finite_set Min.boundedE empty_not_insert finite_insert insertI1 min_def )
  by (metis List.finite_set Min.boundedE ball_empty finite_insert insertCI min_def order_less_le)


lemma mset_trees_ins_tree[simp]:
  "mset_obheap (ins_tree t fh) = mset_tree t + mset_obheap  fh"
  apply(induction t fh rule: ins_tree.induct) 
  apply simp
  apply simp 
  by (metis ins_tree.simps(3) mset_obheap.simps(3) mset_trees_Cons')

subsubsection \<open>\<open>insert\<close>\<close>

definition insert :: "'a::linorder \<Rightarrow> 'a OBHeaps \<Rightarrow> 'a OBHeaps" where
"insert x ts = ins_tree (Node 0 x [] ) ts"

value "insert (2::nat) fh0"
lemma invar_insert[simp]: "invar_obheap fh \<Longrightarrow> invar_obheap (insert x fh)"
  apply (simp add:invar_tree_def)
  by (metis fheap0 invar_obheap.simps invar_ins_tree insert_def)

lemma mset_trees_insert[simp]: "mset_obheap (insert x fh) = {#x#} + mset_obheap fh"
  by(auto simp: insert_def)


fun get_min ::"'a::linorder heap \<Rightarrow> 'a" where
"get_min [t] = root t"
|"get_min (t#ts) = min (root t) (get_min ts)"

definition "get_min_val fh = get_min (root_trees fh)"

value "get_min_val fh1"

lemma get_min_eq_Min:"ts\<noteq>[] \<Longrightarrow> get_min ts = Min (set(root_trees_roots ts))"
  apply(induct ts rule: get_min.induct)
  by auto

lemma obheap_root_min:
  assumes "invar_tree t"
  assumes "x \<in># mset_tree t"
  shows "root t \<le> x"
using assms
by (induction t arbitrary: x rule: mset_tree.induct) (fastforce simp: mset_heap_def invar_tree_def)

lemma get_min_mset:
  assumes "ts\<noteq>[]"
  assumes "invar_trees ts"
  assumes "x \<in># mset_heap ts"
  shows "get_min ts \<le> x"
  using assms
  apply (induction ts arbitrary: x rule: get_min.induct) 
  apply (simp add: obheap_root_min) 
   apply (auto
      simp: obheap_root_min min_def intro: order_trans;
      meson linear order_trans obheap_root_min
      )+
  done

lemma get_min_member:
  "ts\<noteq>[] \<Longrightarrow> get_min ts \<in># mset_heap ts"
by (induction ts rule: get_min.induct) (auto simp: min_def)

lemma get_min:
  assumes "mset_heap ts \<noteq> {#}"
  assumes "invar_trees ts"
  shows "get_min ts = Min_mset (mset_heap ts)"
using assms get_min_member get_min_mset
  by (auto simp: eq_Min_iff)  

subsubsection \<open>\<open>merge\<close>\<close>

fun merge::"'a::linorder OBHeaps \<Rightarrow> 'a OBHeaps \<Rightarrow> 'a OBHeaps"where
  "merge t1 (Obheaps None _) =t1"|
  "merge (Obheaps None _) t2 =t2"|
  "merge (Obheaps (Some a) []) t2 = t2"|
  "merge t1 (Obheaps (Some a') []) = t1"|
  "merge (Obheaps (Some a) ts1) (Obheaps (Some a') ts2) = (if a \<le> a' 
                  then (Obheaps (Some a)  (ts1@ts2)) 
                  else (Obheaps (Some a') (ts1@ts2)) )"

value "invar_obheap (merge fh1 fh1)"
lemma app_invar_trees:"invar_trees ts1 \<Longrightarrow> invar_trees ts2 \<Longrightarrow> invar_trees (ts1@ts2)"
  apply(induct ts1) 
  by auto

lemma app_invar_trees':"invar_trees (ts1@ts2) \<Longrightarrow> invar_trees ts1 \<Longrightarrow> invar_trees ts2 "
  apply(induct ts1) 
  by auto

lemma app_mest_trees:"mset_heap(ts1 @ ts2) = mset_heap ts1 + mset_heap ts2"
  apply(induct ts1) 
  by auto


lemma Min_set:
  assumes "ts1 \<noteq> [] & ts2 \<noteq> []"
  assumes "a = Min (set ts1)"
  assumes "a' = Min (set  ts2)"
  assumes "a \<le> a'"
  shows "a = Min (set (ts1 @ ts2))" 
  using assms 
  by (simp add: Min.union)

lemma Min_mset_roots:
  assumes "ts1 \<noteq> [] & ts2 \<noteq> []"
  assumes "invar_trees ts1 \<and> invar_trees ts2"
  assumes "a = Min_mset (mset_heap ts1)"
  assumes "a' = Min_mset (mset_heap ts2)"
  assumes "a \<le> a'"
  shows "a =  Min_mset (mset_heap (ts1 @ ts2))" 
  using assms 
  apply (simp add: invar_trees_def)
  by (metis (mono_tags, lifting) Min.coboundedI Min_in app_mest_trees append_is_Nil_conv finite_set_mset mset_trees_empty_iff order_antisym set_mset_eq_empty_iff union_iff)
  
lemma Min_set_roots:
  assumes "ts1 \<noteq> [] & ts2 \<noteq> []"
  assumes "invar_trees ts1 \<and> invar_trees ts2"
  assumes "a = get_min ts1"
  assumes "a' = get_min ts2"
  assumes "a \<le> a'"
  shows "a =  get_min (ts1 @ ts2)" 
  using assms 
  apply (simp add: invar_trees_def)
  by (simp add: Min_mset_roots app_invar_trees assms(2) get_min)

lemma Min_set_roots':
  assumes "ts1 \<noteq> [] & ts2 \<noteq> []"
  assumes "invar_trees ts1 \<and> invar_trees ts2"
  assumes "a = get_min ts1"
  assumes "a' = get_min ts2"
  assumes "a > a'"
  shows "a' =  get_min (ts1 @ ts2)" 
  using assms 
  apply (simp add: invar_trees_def)
  by (metis app_invar_trees app_mest_trees append_is_Nil_conv assms(2) get_min_member get_min_mset nle_le order_less_imp_le union_iff)



lemma set2:"a\<in>set ts1 \<Longrightarrow> a'\<in>set ts2 \<Longrightarrow> a' \<in> set (ts1@ts2) "
  apply(induct ts1) 
  by auto

lemma invar_obheap_merge:
  assumes "invar_obheap ts\<^sub>1"
  assumes "invar_obheap ts\<^sub>2"
  shows "invar_trees (root_trees (merge ts\<^sub>1 ts\<^sub>2))"
  using assms
proof (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
  case (1 t1 uu)
  then show ?case by simp
next
  case (2 uv vb va)
  then show ?case by auto
next
  case (3 a vb va)
  then show ?case by auto
next
  case (4 vb v vc a')
  then show ?case by auto
next
  case (5 a v va a' vb vc)
  then show ?case
    by (metis Nil_is_append_conv app_invar_trees OBHeaps.sel(2) invar_obheap.elims(2) is_empty_obheap.simps list.distinct(1) merge.simps(5) noempty_eq_roots option.distinct(1)) 
qed


lemma invar_min_merge:
  assumes "invar_obheap ts\<^sub>1"
  assumes "invar_obheap ts\<^sub>2"
  shows "invar_min (merge ts\<^sub>1 ts\<^sub>2)"
  using assms
proof (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
  case (1 t1 uu)
  then show ?case by simp
next
  case (2 uv vb va)
  then show ?case by auto
next
  case (3 a vb va)
  then show ?case by auto
next
  case (4 vb v vc a')
  then show ?case by auto
next
  case (5 a v va a' vb vc)
  then show ?case 
  proof(cases "a\<le> a'")
    case True
    have 01:"a = get_min (v # va)" 
      by (metis "5.prems"(1) get_min_eq_Min invar_min.simps invar_obheap.elims(1) list.discI option.discI option.sel)
    have 02:"a' = get_min (vb # vc)" 
      by (metis "5.prems"(2) get_min_eq_Min invar_min.simps invar_obheap.elims(1) list.discI option.discI option.sel)
    have 03:"invar_trees (v # va) \<and> invar_trees (vb # vc)" 
      by (metis "5.prems"(1) "5.prems"(2) OBHeaps.sel(2) invar_obheap.elims(2) no_empty_obheap_eq noempty_eq_roots)
    have 04:"a = get_min ((v # va) @ vb # vc)" 
      using "01" "02" "03" Min_set_roots True by blast
    have 05:"a = Min (set (root_trees_roots ((v # va) @ vb # vc)))"
      by (simp add: "04" get_min_eq_Min)
    then show ?thesis using 5   merge.simps(5)[of a  v va a' vb vc] invar_min.simps
      by (metis True option.sel)
  next
    case False
    have 06:"a = get_min (v # va)" 
      by (metis "5.prems"(1) get_min_eq_Min invar_min.simps invar_obheap.elims(1) list.discI option.discI option.sel)
    have 07:"a' = get_min (vb # vc)" 
      by (metis "5.prems"(2) get_min_eq_Min invar_min.simps invar_obheap.elims(1) list.discI option.discI option.sel)
    have 08:"invar_trees (v # va) \<and> invar_trees (vb # vc)" 
      by (metis "5.prems"(1) "5.prems"(2) OBHeaps.sel(2) invar_obheap.elims(2) no_empty_obheap_eq noempty_eq_roots)
    have 09:"a' = get_min ((v # va) @ vb # vc)" 
      using "06" "07" "08"  False 
      by (metis Min_set_roots' linorder_le_less_linear list.distinct(1))
    have 10:"a' = Min (set (root_trees_roots ((v # va) @ vb # vc)))"
      by (simp add: "09" get_min_eq_Min)
    then show ?thesis using 5 
      by (metis False invar_min.simps merge.simps(5) option.sel)      
  qed
   
qed
    
lemma invar_merge[simp]:
  assumes "invar_obheap ts\<^sub>1"
  assumes "invar_obheap ts\<^sub>2"
  shows "invar_obheap (merge ts\<^sub>1 ts\<^sub>2)"
  using assms
  by (simp add:invar_obheap_merge invar_min_merge)


lemma mset_obheap_merge[simp]:
  "mset_obheap (merge ts\<^sub>1 ts\<^sub>2) = mset_obheap ts\<^sub>1 + mset_obheap ts\<^sub>2"
  apply (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
  apply auto
   apply (metis app_mest_trees append_Cons is_empty_obheap.simps list.distinct(1) 
mset_obheap.simps(3) mset_obheap_no_empty mset_trees_Cons' option.simps(3))
  by (metis app_mest_trees append_Cons list.distinct(1) mset_obheap.simps(3) 
mset_obheap_empty_iff mset_obheap_no_empty mset_trees_Cons' mset_trees_empty_iff)




lemma invar_btrees0: "invar_tree (Node 0 x [])"
unfolding invar_tree_def by auto

lemma invar_btrees_Cons:
  "invar (t#ts)
  \<longleftrightarrow> invar_btree t \<and> invar ts \<and> (\<forall>t'\<in>set ts. rank t < rank t')" 
  by (auto simp: invar_def)

lemma invar_tree_add:
  assumes "(\<forall>t\<in>set ts. invar_tree t)"
  assumes "invar_tree t\<^sub>1"
  shows "(\<forall>t\<in>set (t\<^sub>1#ts). invar_tree t)"
  using assms
  by auto



subsubsection \<open>get_min\<close>

fun get_minval :: "'a::linorder OBHeaps \<Rightarrow> 'a option" where
  "get_minval (Obheaps None _) = None"|
  "get_minval (Obheaps (Some a) []) = None"|
  "get_minval (Obheaps (Some a) xs) = (Some a)"

definition "get_min_value fh = the (get_minval fh)"

lemma get_minval_min:"get_minval ts = min_value ts"
  apply (simp add:min_value_def)
  apply (induction ts rule:get_minval.induct)
  apply auto
  done

lemma get_min_val_mset:
  assumes "\<not> is_empty_obheap fh"
  assumes "invar_obheap fh"
  assumes "x \<in># mset_obheap fh"
  shows "get_min_val fh \<le> x"
  using assms
  by (auto simp: get_min_val_def noempty_roots get_min_mset )  

lemma get_min_val_member:
  "\<not> is_empty_obheap fh \<Longrightarrow> get_min_val fh \<in># mset_obheap fh"
  by (auto simp: get_min_val_def  noempty_roots get_min_member ) 

lemma get_min_val:
  assumes "mset_obheap fh \<noteq> {#}"
  assumes "invar_obheap fh"
  shows "get_min_val fh = Min_mset (mset_obheap fh)"
using assms
  by (metis get_min get_min_val_def invar_obheap.elims(2) mset_obheap_empty_iff mset_obheap_no_empty) 


lemma get_min_value:
  assumes "mset_obheap fh \<noteq> {#}"
  assumes "invar_obheap fh"
  shows "get_min_value fh = Min_mset (mset_obheap fh)"
  using assms 
  apply(induct fh rule:mset_obheap.induct)
    apply (auto simp:get_min_value_def) 
  by (metis OBHeaps.sel(2) get_min get_min_eq_Min list.distinct(1) list.simps(15) mset_obheap.simps(3) mset_obheap_empty_iff mset_trees_Cons' no_empty_obheap_eq noempty_eq_roots root_trees_roots.simps(2) set_mset_union)


lemma get_min_eq:"\<not> is_empty_obheap fh \<Longrightarrow>invar_obheap fh \<Longrightarrow> get_min_val fh = get_min_value fh"
proof -
  assume a1: "\<not> is_empty_obheap fh"
  assume a2: "invar_obheap fh"
  have "({#} = mset_obheap fh) = is_empty_obheap fh"
    by simp
  then have "{#} \<noteq> mset_obheap fh"
    using a1 by meson
  then have "{#} \<noteq> mset_obheap fh \<and> invar_obheap fh"
    using a2 by satx
  then show ?thesis
    by (metis (full_types) get_min_val get_min_value)
qed


subsubsection \<open>delete_min\<close>


fun trees_obheap:: "'a::linorder tree list \<Rightarrow>'a OBHeaps " where
"trees_obheap [] = Obheaps None []"|
"trees_obheap ts = Obheaps (Some (get_min ts))  ts"

fun del_min :: "'a::linorder tree list \<Rightarrow>'a \<Rightarrow>  'a tree list" where
  "del_min [] a = []"
| "del_min (t#ts) a = (if a =(root t) then ((children t)@ ts) else (t#(del_min ts a)))"


fun delete_min ::"'a::linorder OBHeaps \<Rightarrow>  'a OBHeaps" where
  "delete_min (Obheaps None _) = empty_obheap"|
  "delete_min (Obheaps (Some a) []) = empty_obheap"|
  "delete_min (Obheaps (Some a) xs) = trees_obheap (del_min xs a)"


lemma app_mset_heap:"mset_heap (x @ y) = mset_heap x + mset_heap y" 
using mset_heap_def 
  by (metis image_mset_union mset_append sum_mset.union)

lemma add_mset_tree:"mset_tree t = {#root t#} + (mset_heap (children t))"
  by (metis mset_tree_simp_alt tree.exhaust_sel)

lemma add_mset_trees:"mset_heap (t#ts) = {#root t#} + mset_heap ((children t) @ ts)"
  apply (auto split: tree.split)
  apply(induct ts)
   apply (auto simp:add_mset_tree app_mset_heap)
  done

lemma eq_get_min:"get_min (t#ts) \<noteq> root t \<Longrightarrow>{#get_min (t#ts)#} = {#get_min ts#}" 
  apply(cases ts) 
  apply(auto)
  by (meson min_def)

lemma mset_trees_del_min:
  assumes "ts \<noteq> []"
  assumes "get_min ts = a"
  shows "mset_heap ts = mset_heap (del_min ts a) + {# get_min ts #}"
  using assms
proof(induct ts a rule:del_min.induct)
  case 1
  then show ?case by simp
next
  case (2 t ts)
  then show ?case 
  proof(cases "get_min(t#ts)=(root t)")
    case True
    then show ?thesis using 2 
      using add_mset_trees by auto
  next
    case Fcondition:False
    then show ?thesis 
    proof(cases "ts = []")
      case True
      then show ?thesis 
        using Fcondition by auto
    next
      case False
      then show ?thesis using del_min.simps(2)[of t ts] 2 eq_get_min[of t ts] Fcondition mset_trees_Cons[of t ts]
        by simp
    qed
  qed
qed

lemma invar_trees_del_min[simp]:
  assumes "ts \<noteq> []"
  assumes "invar_trees ts"
  assumes "get_min ts = a"
  shows "invar_trees (del_min ts a)"
  using assms
  apply(induct ts a rule:del_min.induct)
   apply auto
  apply (metis app_invar_trees invar_children tree.collapse)
  by (metis get_min.simps(1) get_min.simps(2) min_def trees_obheap.cases)
  

lemma invar_trees_roots: "invar_trees ts \<Longrightarrow>invar_trees( roots (trees_obheap ts))" 
  apply(induct ts rule:trees_obheap.induct)
  by auto

lemma invar_trees_get_min: "ts \<noteq> [] \<Longrightarrow> invar_trees ts \<Longrightarrow>\<forall>t\<in>set ts. get_min ts \<le> root t"
  apply(induct ts rule:get_min.induct)
  apply simp 
  by (auto simp: min.coboundedI2)

 
lemma trees_obheap_invar: " invar_trees ts \<Longrightarrow> invar_obheap (trees_obheap ts)" 
  apply(induct ts rule:trees_obheap.induct)
  by (auto simp:root_trees_def get_min_eq_Min)


theorem invar_delete_min[simp]:
  assumes "\<not>is_empty_obheap fh"
  assumes "invar_obheap fh"
  shows "invar_obheap (delete_min fh)"
  using assms
  apply (induction fh rule:delete_min.induct)
  apply simp
  apply simp
  by (metis delete_min.simps(3) OBHeaps.sel(2) invar_min.simps invar_trees_del_min 
      invar_obheap.elims(2) list.distinct(1) noempty_eq_roots option.sel option.simps(3) 
      trees_obheap.simps(2) trees_obheap_invar)

theorem mset_trees_delete_min:
  assumes "\<not>is_empty_obheap fh"
  assumes "invar_obheap fh"
  shows "mset_obheap fh = mset_obheap (delete_min fh) + {# get_min_value fh #}"
  using assms
  apply (induction fh rule:delete_min.induct)
    apply simp
   apply simp
  by (smt (verit, del_insts) delete_min.simps(3) empty_obheap_def OBHeaps.sel(2) 
      get_min get_min_value get_min_value_def get_minval.simps(3) invar_obheap.elims(2) 
      mset_obheap.simps(3) mset_obheap_empty mset_obheap_empty_iff mset_trees_Nil 
      mset_trees_del_min noempty_eq_roots option.sel trees_obheap.elims)

value " (delete_min (merges (Obheaps (Some 2) [B4,B6]) (Obheaps (Some 1) [B7,B3])))"

subsubsection \<open>mergead\<close>

fun del_one::"'a::linorder tree list\<Rightarrow>'a tree\<Rightarrow>'a tree list" where
  "del_one [] _ = []"|
  "del_one (t'#ts)  t =(if t'=t then ts else case ts of
                                              []\<Rightarrow>[t']
                                              |( t''#ts')\<Rightarrow>t'#(del_one (t''#ts')  t))"

fun change_one::"'a::linorder tree list\<Rightarrow>'a tree\<Rightarrow>'a tree\<Rightarrow>'a::linorder tree list" where
  "change_one [] _ _=[]"|
  "change_one (t#ts) x y=(if t=x then (y#ts) else t#(change_one ts x y))"

fun mergenum::"'a::linorder tree list \<Rightarrow>'a tree\<Rightarrow>nat\<Rightarrow>'a tree list"where
  "mergenum [] _ 0=[]"|
  "mergenum (t#ts) t'(Suc n)=(case (find (\<lambda>x. (rank x= rank t')) (t#ts)) of 
    None \<Rightarrow>(t#ts)@[t']|
    Some x\<Rightarrow>(if ((find (\<lambda>y. (rank y= rank (link x t'))) (t#ts)) = None )then (change_one (t#ts) x (link x t')) 
            else (mergenum (del_one (t#ts) x) (link x t')) n))"    
  
fun mergead::"'a::linorder tree list \<Rightarrow>'a tree list\<Rightarrow>'a tree list" where
  "mergead [] x =x"|
  "mergead [t] x =mergenum x t 1"|
  "mergead (t#t'#ts)  x= (mergead ts (mergenum (t#x) t' (length (t#x))))"

fun adjust::"'a::linorder OBHeaps \<Rightarrow>'a OBHeaps" where
  "adjust (Obheaps None _) = (Obheaps None [])"|
  "adjust (Obheaps (Some a) []) = (Obheaps None [])"|
  "adjust (Obheaps (Some a) x) = (Obheaps (Some a) (mergead x []))"


value "adjust fh1"

interpretation obheaps: Priority_Queue_Merge
  where empty = empty_obheap and is_empty = is_empty_obheap and insert = insert
  and get_min = get_min_value and del_min = delete_min and merge = merge
  and invar = invar_obheap and mset = mset_obheap
proof (unfold_locales, goal_cases)
  case 1 then show ?case by simp
next
  case (2 q) then show ?case by simp
next
  case (3 q x)  then show ?case by simp
next
  case (4 q) then show ?case using mset_trees_delete_min by force 
next
  case (5 q) then show ?case  using get_min_value by blast 
next
  case 6 then show ?case by (simp add: empty_obheap_def invar_trees_def root_trees_def)
next
  case (7 q x) then show ?case using invar_insert by blast 
next
  case (8 q) then show ?case using invar_delete_min mset_obheap_empty_iff by blast
next
  case (9 q1 q2) then show ?case by simp
next
  case (10 q1 q2) then show ?case using invar_merge by blast 
qed


subsubsection \<open>Timing Functions\<close>

text \<open>
  We define timing functions for each operation, and provide
  estimations of their complexity.
\<close>
definition T_link :: "'a::linorder tree \<Rightarrow> 'a tree \<Rightarrow> nat" where
[simp]: "T_link _ _ = 1"

fun T_ins_tree :: "'a::linorder tree \<Rightarrow> 'a OBHeaps \<Rightarrow> nat" where
  "T_ins_tree t (Obheaps None _)=  1"|
  "T_ins_tree t (Obheaps (Some a) []) =  1"|
  "T_ins_tree t (Obheaps (Some a) xs) = (if root t < a 
                                    then 1  
                                    else 1)"
definition T_insert :: "'a::linorder \<Rightarrow> 'a OBHeaps \<Rightarrow> nat" where
"T_insert x ts = T_ins_tree (Node 0 x []) ts + 1"

lemma T_ins_tree_simple_bound: "T_ins_tree t ts \<le>  1"
  by (induction t ts rule: T_ins_tree.induct) auto

lemma T_insert_tree_bound: "T_insert x ts \<le> 2"
  using T_insert_def 
  by (metis T_ins_tree_simple_bound add_mono_thms_linordered_semiring(3)  one_add_one)


fun T_merge::"'a::linorder OBHeaps \<Rightarrow> 'a OBHeaps \<Rightarrow> nat"where
  "T_merge t1 (Obheaps None _) =1"|
  "T_merge (Obheaps None _) t2 =1"|
  "T_merge (Obheaps (Some a) []) t2 = 1"|
  "T_merge t1 (Obheaps (Some a') []) = 1"|
  "T_merge (Obheaps (Some a) ts1) (Obheaps (Some a') ts2) = (if a < a' 
                  then 1 
                  else 1 )"

lemma T_merge_simple_bound: "T_merge t1 t2 \<le> 1"
  by (induction t1 t2 rule: T_merge.induct) auto

fun T_get_minval :: "'a::linorder OBHeaps \<Rightarrow> nat" where
  "T_get_minval (Obheaps None _) = 1"|
  "T_get_minval (Obheaps (Some a) []) = 1"|
  "T_get_minval (Obheaps (Some a) xs) = 1"

lemma T_get_minval_bound: "T_get_minval fh \<le>  1"
  by (induction fh rule: T_get_minval.induct) auto

fun T_get_min :: "'a::linorder tree list\<Rightarrow> nat" where
  "T_get_min [t] = 1"
| "T_get_min (t#ts) = 1 + T_get_min ts"

lemma T_get_min_rest_estimate: "ts\<noteq>[] \<Longrightarrow> T_get_min ts = length ts"
  by (induction ts rule: T_get_min.induct) auto

definition T_root_trees::"'a::linorder OBHeaps \<Rightarrow> nat"where 
        "T_root_trees fh =
          (case fh of (Obheaps None _ ) \<Rightarrow> 1 |
          (Obheaps (Some a) []) \<Rightarrow> 1 |
          (Obheaps (Some a) xs) \<Rightarrow> 1)"

lemma T_root_trees_bound: "T_root_trees fh \<le>  1"
  by (simp add: T_root_trees_def OBHeaps.case_eq_if list.case_eq_if option.case_eq_if)
 
definition T_get_min_val::"'a::linorder OBHeaps \<Rightarrow> nat"where 
  "T_get_min_val fh = T_get_min (root_trees fh) + (T_root_trees fh)"

lemma T_get_min_val_bound: "\<not>is_empty_obheap fh \<Longrightarrow> T_get_min_val fh \<le>length (root_trees fh)+ 1"
  by (metis T_get_min_rest_estimate T_get_min_val_def T_root_trees_bound add_left_mono noempty_roots)

fun T_del_min' :: "'a::linorder tree list \<Rightarrow>'a \<Rightarrow> nat" where
  "T_del_min' [] a  = 1"
| "T_del_min' (t#ts) a = 1+(if a =(root t) then 1 else (1 + T_del_min' ts a ))"


lemma T_del_min_bound: "T_del_min' ts a  \<le>2* length ts +1  "
  apply (induction ts a  rule: T_del_min'.induct)
   apply simp
  by auto
  
fun T_trees_obheap:: "'a::linorder tree list \<Rightarrow> nat " where
  "T_trees_obheap [] = 1"|
  "T_trees_obheap ts = T_get_min ts +1"

lemma T_trees_obheap_bound: "T_trees_obheap ts \<le> length ts + 1"
  apply (induction ts rule: T_trees_obheap.induct)
  apply simp
  by (simp add: T_get_min_rest_estimate)

fun T_delete_min' ::"'a::linorder OBHeaps\<Rightarrow>nat \<Rightarrow>  nat" where
  "T_delete_min' (Obheaps None _) x= 1"|
  "T_delete_min' (Obheaps (Some a) []) x= 1"|
  "T_delete_min' (Obheaps (Some a) xs) x = x+ T_del_min' xs a"


lemma T_delete_min_bound: "\<not>is_empty_obheap fh  \<Longrightarrow> T_delete_min' fh k \<le> 2*length(root_trees fh) + k+1"
  apply(induction fh k rule:T_delete_min'.induct )
  apply simp
   apply fastforce
  by (metis (full_types) T_del_min_bound T_delete_min'.simps(3) OBHeaps.sel(2) group_cancel.add1 group_cancel.add2 nat_add_left_cancel_le noempty_eq_roots)

export_code empty_obheap insert get_min merge del_min in Haskell

end