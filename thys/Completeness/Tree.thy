theory Tree = (*Arith +*) Hilbert_Choice + List + Set + Finite_Set + Wellfounded_Relations:

ML {* simp_depth_limit := 5; *}

subsection "Tree"

consts
    tree :: "['a => 'a set,'a] => (nat * 'a) set"

inductive "tree subs gamma"
  (******
   * This set represents the nodes in a tree which may represent a proof of gamma.
   * Only storing the annotation and it's level.
   * NOTE: could parameterize on subs
   ******)
  intros
    tree0: "(0,gamma) : tree subs gamma"

    tree1: "[| (n,delta) : tree subs gamma; sigma : subs(delta) |]
	   ==> (Suc n,sigma) : tree subs gamma"

lemmas [elim] = tree.elims
lemmas [intro] = tree.intros

lemma tree0Eq: "(0,y) : tree subs gamma = (y = gamma)"
  apply(rule iffI)
  apply(erule tree.elims)
  apply(auto) 
  done

lemma tree1Eq [rule_format]:"!Y. (Suc n,Y) : tree subs gamma = (? sigma : subs gamma . (n,Y) : tree subs sigma)"
  apply(induct n)
  apply(blast)
  apply(force)
  done
    --"moving down a tree"

constdefs  
  incLevel :: "nat * 'a => nat * 'a"
  "incLevel == % (n,a). (Suc n,a)"

lemma injIncLevel: "inj incLevel"
  apply(simp add: incLevel_def)
  apply(rule inj_onI) 
  by auto
  
lemma treeEquation: "tree subs gamma = insert (0,gamma) (UN delta:subs gamma . incLevel ` tree subs delta)"
  apply(rule set_ext)
  apply(simp add: split_paired_all)
  apply(case_tac a)
   apply(force simp add: tree0Eq incLevel_def)
  apply(force simp add: tree1Eq incLevel_def)
  done

constdefs
  fans :: "['a => 'a set] => bool"
  "fans subs == !x. finite (subs x)"

lemma fansD: "fans subs ==> finite (subs A)"
  by(simp add: fans_def)

lemma fansI:  "(!A. finite (subs A)) ==> fans subs" 
  by (simp add: fans_def) 


subsection "Terminal"

constdefs
  terminal    :: "['a => 'a set,'a] => bool"
  "terminal subs delta == subs(delta) = {}"

lemma terminalD: "terminal subs Gamma ==> x ~: subs Gamma" 
  apply(simp add: terminal_def) done
  -- "not a good dest rule"

lemma terminalI: "x : subs Gamma ==> ~ terminal subs Gamma" 
  apply(simp add: terminal_def) 
  by blast
  -- "not a good intro rule"


subsection "Inherited"

constdefs
  inherited   :: "['a => 'a set,(nat * 'a) set => bool] => bool"
  "inherited subs P == (!A B. (P A & P B) = P (A Un B))
                       & (!A. P A = P (incLevel ` A))
		       & (!n Gamma A. ~(terminal subs Gamma) --> P A = P (insert (n,Gamma) A))
		       & (P {})"
		       
    (******
     inherited properties:
	- preserved under: dividing into 2, join 2 parts
			   moving up/down levels
			   inserting non terminal nodes
	- hold on empty node set 
     ******)		       

  -- "FIXME tjr why does it have to be invariant under inserting nonterminal nodes?"

lemma inheritedUn[rule_format]:"inherited subs P --> P A --> P B --> P (A Un B)" 
  by (auto simp add: inherited_def)

lemma inheritedIncLevel[rule_format]: "inherited subs P --> P A --> P (incLevel ` A)"
  by (auto simp add: inherited_def)

lemma inheritedEmpty[rule_format]: "inherited subs P --> P {}"
  by (auto simp add: inherited_def)

lemma inheritedInsert[rule_format]: 
  "inherited subs P --> ~(terminal subs Gamma) --> P A --> P (insert (n,Gamma) A)"
  by (auto simp add: inherited_def)

lemma inheritedI[rule_format]: "[| ! A B . (P A & P B) = P (A Un B);
  ! A . P A = P (incLevel ` A); 
  ! n Gamma A . ~(terminal subs Gamma) --> P A = P (insert (n,Gamma) A);
  P {} |] ==> inherited subs P"
  by (simp add: inherited_def)

(* These only for inherited join, and a few more places... *)
lemma inheritedUnEq[rule_format, symmetric]: "inherited subs P --> (P A & P B) = P (A Un B)"
  by (auto simp add: inherited_def)

lemma inheritedIncLevelEq[rule_format, symmetric]: "inherited subs P --> P A = P (incLevel ` A)"
  by (auto simp add: inherited_def)

lemma inheritedInsertEq[rule_format, symmetric]: "inherited subs P --> ~(terminal subs Gamma) --> P A = P (insert (n,Gamma) A)"
  by (auto simp add: inherited_def)

lemmas inheritedUnD = iffD1[OF inheritedUnEq];

lemmas inheritedInsertD = inheritedInsertEq[THEN iffD1];

lemmas inheritedIncLevelD = inheritedIncLevelEq[THEN iffD1]

lemma inheritedUNEq[rule_format]: 
  "finite A --> inherited subs P --> (!x:A. P (B x)) = P (UN a:A. B a)"
  apply(intro impI)
  apply(rule finite_induct) back
  apply(simp) 
  apply(simp add: inheritedEmpty)
  apply(force dest: inheritedUnEq)
  done

lemmas inheritedUN  = inheritedUNEq[THEN iffD1]

lemmas inheritedUND[rule_format] = inheritedUNEq[THEN iffD2]

lemma inheritedPropagateEq[rule_format]: assumes a: "inherited subs P"
  and b: "fans subs"
  and c: "~(terminal subs delta)"
  shows "P(tree subs delta) = (!sigma:subs delta. P(tree subs sigma))"
  apply(insert fansD[OF b])
  apply(subst treeEquation)
  apply(simp! add: inheritedInsertEq inheritedUNEq[symmetric] inheritedIncLevelEq)
  done

lemma inheritedPropagate: "[| ~P(tree subs delta); inherited subs P; fans subs; ~(terminal subs delta)|]
  ==> ? sigma : subs delta . ~P(tree subs sigma)"
  apply(simp add: inheritedPropagateEq)
  done

lemma inheritedViaSub: "[| inherited subs P; fans subs; P(tree subs delta); sigma : subs delta |]
  ==> P(tree subs sigma)"
  apply(frule_tac terminalI)
  apply(simp add: inheritedPropagateEq)
  done

lemma inheritedJoin[rule_format]: "(inherited subs P & inherited subs Q) --> inherited subs (%x. P x & Q x)";
  apply(blast intro!: inheritedI dest: inheritedUnEq inheritedIncLevelEq inheritedInsertEq inheritedEmpty) done

lemma inheritedJoinI[rule_format]: "[| inherited subs P; inherited subs Q; R = ( % x . P x & Q x) |] ==> inherited subs R"
  by(blast intro!:inheritedI dest: inheritedUnEq inheritedIncLevelEq inheritedInsertEq inheritedEmpty)


subsection "bounded, boundedBy"

constdefs
  boundedBy   :: "nat => (nat * 'a) set => bool"
  "boundedBy N A == (! (n,delta) : A. n < N)"

  bounded     :: "(nat * 'a) set => bool"
  "bounded A == ? N . boundedBy N A"

lemma boundedByEmpty[simp]: "boundedBy N {}"
  apply(simp add: boundedBy_def) done

lemma boundedByInsert: "boundedBy N (insert (n,delta) B)     = (n < N & boundedBy N B)"
  apply(simp add: boundedBy_def) done

lemma boundedByUn: "boundedBy N (A Un B) = (boundedBy N A & boundedBy N B)"
  apply(auto simp add: boundedBy_def) done

lemma boundedByIncLevel': "boundedBy (Suc N) (incLevel ` A) = boundedBy N A";    
  apply(simp add: incLevel_def boundedBy_def)
  apply(auto)
  done

lemma boundedByAdd1[rule_format]: "boundedBy N B --> boundedBy (N+M) B"
  apply(auto simp add: boundedBy_def) done

lemma boundedByAdd2[rule_format]: "boundedBy M B --> boundedBy (N+M) B"
  apply(auto simp add: boundedBy_def) done

lemma boundedByMono[rule_format]: "boundedBy m B --> m < M --> boundedBy M B"
  apply(auto simp: boundedBy_def) done

lemmas boundedByMonoD  = boundedByMono
    
lemma boundedBy0: "boundedBy 0 A = (A = {})"
  apply(simp add: boundedBy_def)
  apply(auto simp add: boundedBy_def) done

lemma boundedBySuc': "boundedBy N A \<Longrightarrow> boundedBy (Suc N) A"
  apply(auto simp add: boundedBy_def) done

lemma boundedByIncLevel: "boundedBy n (incLevel ` (tree subs gamma)) = ( ? m . n = Suc m & boundedBy m (tree subs gamma))";
  apply(cases n)
   apply(force simp add: boundedBy0 tree0) 
  apply(subst treeEquation) 
  apply(force simp add: incLevel_def boundedBy_def)
  done

lemma boundedByUN: "boundedBy N (UN x:A. B x) = (!x:A. boundedBy N (B x))"
  apply(simp add: boundedBy_def)
  done

lemma boundedBySuc[rule_format]: "sigma \<in> subs Gamma \<Longrightarrow> boundedBy (Suc n) (tree subs Gamma) \<longrightarrow> boundedBy n (tree subs sigma)"
  apply(subst treeEquation)  back
  apply(rule)
  apply(simp add: boundedByInsert)
  apply(simp add: boundedByUN)
  apply(drule_tac x=sigma in bspec) apply(assumption)
  apply(simp add: boundedByIncLevel)
  done


subsection "Inherited Properties- bounded"

lemma boundedEmpty: "bounded {}" 
  by(simp add: bounded_def)

lemma boundedUn: "bounded (A Un B) = (bounded A & bounded B)"
  apply(auto simp add: bounded_def boundedByUn)
  apply(rule_tac x="N+Na" in exI)
  apply(blast intro: boundedByAdd1 boundedByAdd2)
  done

lemma boundedIncLevel: "bounded (incLevel` A) = (bounded A)"
  apply(simp add: bounded_def)
  apply(rule)
   apply(erule exE)
   apply(rule_tac x=N in exI)
   apply(simp add: boundedBy_def incLevel_def)
   apply(force)
  apply(erule exE)
  apply(rule_tac x="Suc N" in exI)
  apply(simp add: boundedBy_def incLevel_def)
  apply(force)
  done

lemma boundedInsert: "bounded (insert a B) = (bounded B)"
  apply(case_tac a)
  apply(simp add: bounded_def boundedByInsert)
  apply(rule) apply(blast)
  apply(erule exE)
  apply(rule_tac x="Suc(aa+N)" in exI)
  apply(force intro:boundedByMono)
  done

lemma inheritedBounded: "inherited subs bounded"
  apply(blast intro!: inheritedI boundedUn[symmetric] boundedIncLevel[symmetric]
    boundedInsert[symmetric] boundedEmpty)
  done


subsection "founded"

constdefs  
  founded     :: "['a => 'a set,'a => bool,(nat * 'a) set] => bool"
  "founded subs Pred == %A. !(n,delta):A. terminal subs delta --> Pred delta"

lemma foundedD[rule_format]: "founded subs P (tree subs delta) --> terminal subs delta --> P delta"
  apply(subst treeEquation)
  apply(simp add: founded_def) 
  done

lemma foundedMono: "[| founded subs P A; ! x. P x --> Q x |] ==> founded subs Q A";
  apply(auto simp: founded_def) done

lemma foundedSubs: "founded subs P (tree subs Gamma) \<Longrightarrow> sigma \<in> subs Gamma \<Longrightarrow> founded subs P (tree subs sigma)"
  apply(simp add: founded_def)
  apply(intro ballI impI)
  apply(case_tac x)
  apply(simp)
  apply(rule)
  apply(drule_tac x="(Suc a, b)" in bspec)
   apply(subst treeEquation)
   apply(force simp: incLevel_def)
  apply(simp)
  done


subsection "Inherited Properties- founded"

lemma foundedInsert[rule_format]: "~ terminal subs delta --> founded subs P (insert (n,delta) B) = (founded subs P B)"
  apply(simp add: terminal_def founded_def) done

lemma foundedUn: "(founded subs P (A Un B)) = (founded subs P A & founded subs P B)";
  apply(simp add: founded_def) by force
   
lemma foundedIncLevel: "founded subs P (incLevel ` A) = (founded subs P A)";
  apply(simp add: founded_def incLevel_def)
  apply(auto) done

lemma foundedEmpty: "founded subs P {}"
  apply(auto simp add: founded_def) done
    
lemma inheritedFounded: "inherited subs (founded subs P)"
  apply(blast intro!: inheritedI foundedUn[symmetric] foundedIncLevel[symmetric]
    foundedInsert[symmetric] foundedEmpty)
  done


subsection "Inherited Properties- finite"

lemmas finiteInsert = finite_insert

lemma finiteUn: "finite (A Un B) = (finite A & finite B)";
  apply(simp) done

lemma finiteIncLevel: "finite (incLevel ` A) = finite A";
  apply(insert injIncLevel)
  apply(rule)
   apply(frule finite_imageD) 
    apply(blast intro: subset_inj_on)
   apply(assumption)
  apply(rule finite_imageI)
  by assumption
  -- "FIXME often have injOn f A, finite f ` A, to show A finite"
   
lemma finiteEmpty: "finite {}" by auto
    
lemma inheritedFinite: "inherited subs (%A. finite A)"
  apply(blast intro!: inheritedI finiteUn[symmetric] finiteIncLevel[symmetric] finiteInsert[symmetric] finiteEmpty)
  done


subsection "path: follows a failing inherited property through tree"

constdefs
  failingSub :: "['a => 'a set,(nat * 'a) set => bool,'a] => 'a"
  "failingSub subs P gamma == (SOME sigma. (sigma:subs gamma & ~P(tree subs sigma)))"

lemma failingSubProps: "[| inherited subs P; ~P (tree subs gamma); ~(terminal subs gamma); fans subs |] 
  ==> failingSub subs P gamma : subs gamma & ~(P (tree subs (failingSub subs P gamma)))"
  apply(simp add: failingSub_def)
  apply(drule inheritedPropagate) apply(assumption+)
  apply(erule bexE)
  apply(rule someI2)
  apply(auto)
  done

lemma failingSubFailsI: "[| inherited subs P; ~P (tree subs gamma); ~(terminal subs gamma); fans subs |] 
  ==> ~(P (tree subs (failingSub subs P gamma)))"
  apply(rule conjunct2[OF failingSubProps]) .

lemmas failingSubFailsE = failingSubFailsI[THEN notE]

lemma failingSubSubs: "[| inherited subs P; ~P (tree subs gamma); ~(terminal subs gamma); fans subs |] 
  ==> failingSub subs P gamma : subs gamma"
  apply(rule conjunct1[OF failingSubProps]) .

consts
  "path"     :: "['a => 'a set,'a,(nat * 'a) set => bool,nat] => 'a"
primrec 
  path0:   "path subs gamma P 0       = gamma"
  pathSuc: "path subs gamma P (Suc n) = (if terminal subs (path subs gamma P n)
			    	          then path subs gamma P n
					  else failingSub subs P (path subs gamma P n))"

lemma pathFailsP: "[| inherited subs P; fans subs; ~P(tree subs gamma) |]
  ==> ~(P (tree subs (path subs gamma P n)))"
  apply(induct_tac n)
   apply(simp)
  apply(simp) 
  apply(rule)
  apply(rule failingSubFailsI) apply(assumption+)
  done

lemmas PpathE = pathFailsP[THEN notE]

lemma pathTerminal[rule_format]: "[| inherited subs P; fans subs; terminal subs gamma |] 
  ==> terminal subs (path subs gamma P n)"
  apply(induct_tac n)
  apply(simp_all) done

lemma pathStarts:  "path subs gamma P 0 = gamma"
  by(simp)
    
lemma pathSubs: "[| inherited subs P; fans subs; ~P(tree subs gamma); ~ (terminal subs (path subs gamma P n)) |]
  ==> path subs gamma P (Suc n) : subs (path subs gamma P n)"
  apply(simp)
  apply(rule failingSubSubs) 
     apply(assumption)
    apply(rule pathFailsP) 
      apply(assumption+) 
  done
  
lemma pathStops: "terminal subs (path subs gamma P n) ==> path subs gamma P (Suc n) = path subs gamma P n"
  by simp


subsection "Branch"

constdefs
  branch      :: "['a => 'a set,'a,nat => 'a] => bool"
  "branch subs Gamma f == (f 0 = Gamma)
                                          & ( !n . terminal subs (f n) --> f (Suc n) = f n)
                                          & ( !n . ~ terminal subs (f n) --> f (Suc n) : subs (f n))"

lemma branch0: "branch subs Gamma f ==> f 0 = Gamma" 
  by (simp add: branch_def)

lemma branchStops: "branch subs Gamma f ==> terminal subs (f n) ==> f (Suc n) = f n" 
  by (simp add: branch_def)

lemma branchSubs: "branch subs Gamma f ==> ~ terminal subs (f n) ==> f (Suc n) : subs (f n)" 
  by (simp add: branch_def)

lemma branchI: "[| (f 0 = Gamma); 
  !n . terminal subs (f n) --> f (Suc n) = f n;
  !n . ~ terminal subs (f n) --> f (Suc n) : subs (f n) |] ==> branch subs Gamma f"
  by (simp add: branch_def)

lemma branchTerminalPropagates: "branch subs Gamma f ==> terminal subs (f m) ==> terminal subs (f (m + n))"
  apply(induct_tac n)
  apply(simp)
  by(simp add: branchStops)

lemma branchTerminalMono: "branch subs Gamma f ==> m < n ==> terminal subs (f m) ==> terminal subs (f n)"
  apply(subgoal_tac "terminal subs (f (m+(n-m)))") apply(force)
  apply(rule branchTerminalPropagates) 
  .

lemma branchPath : "!!subs.
  [| inherited subs P; fans subs; ~P(tree subs gamma) |] 
  ==> branch subs gamma (path subs gamma P)"
  apply(auto intro!: branchI pathStarts pathSubs pathStops)
  done


subsection "failing branch property: abstracts path defn"

lemma failingBranchExistence:  "!!subs.
  [| inherited subs P; fans subs; ~P(tree subs gamma) |] 
  ==> ? f . branch subs gamma f & (! n . ~P(tree subs (f n)))"
  apply(rule_tac x="path subs gamma P" in exI)
  apply(rule conjI)
  apply(force intro!: branchPath)
  apply(intro allI)
  apply(rule pathFailsP) 
  by auto

constdefs    
  infBranch   :: "['a => 'a set,'a,nat => 'a] => bool"
  "infBranch subs Gamma f == (f 0 = Gamma) & (! n . f (Suc n) : subs (f n))"

lemma infBranchI: "[| (f 0 = Gamma); !n . f (Suc n) : subs (f n) |] ==> infBranch subs Gamma f"
  by (simp add: infBranch_def)


subsection "Tree induction principles"

  -- "we work hard to use nothing fancier that induction over naturals"

lemma boundedTreeInduction': "\<lbrakk> fans subs; 
  !delta. ~ terminal subs delta --> (! sigma:subs delta. P sigma) --> P delta \<rbrakk>
  \<Longrightarrow> ! Gamma. boundedBy m (tree subs Gamma) \<longrightarrow>  founded subs P (tree subs Gamma) \<longrightarrow> P Gamma"
  apply(induct_tac m)
   apply(intro impI allI)
   apply(simp add: boundedBy0)
   apply(subgoal_tac "(0,Gamma) : tree subs Gamma") apply(blast) apply(rule tree0)
  apply(intro impI allI)
  apply(drule_tac x=Gamma in spec)
  apply(case_tac "terminal subs Gamma")
   apply(simp)
   apply(drule_tac foundedD) apply(assumption) apply(assumption)
  apply(erule impE)
   apply(assumption)
  apply(erule impE)
   apply(rule)
   apply(drule_tac x=sigma in spec)
   apply(erule impE)
    apply(rule boundedBySuc) apply(assumption) apply(assumption)
   apply(erule impE)
    apply(rule foundedSubs) apply(assumption) apply(assumption)
   apply(assumption)
  apply(assumption)
  done
  -- "tjr tidied and introduced new lemmas"

lemma boundedTreeInduction: "\<lbrakk> fans subs; 
  bounded (tree subs Gamma); founded subs P (tree subs Gamma);
  !delta. ~ terminal subs delta --> (! sigma:subs delta. P sigma) --> P delta
  \<rbrakk>
  \<Longrightarrow> P Gamma"
  apply(unfold bounded_def)
  apply(erule exE)
  apply(frule_tac boundedTreeInduction') apply(assumption)
  apply(force)
  done

lemma boundedTreeInduction2': "[| fans subs; 
  !delta. (! sigma:subs delta. P sigma) --> P delta |] 
  ==> ! Gamma. boundedBy m (tree subs Gamma) \<longrightarrow> P Gamma"
  apply(induct_tac m)
   apply(intro impI allI)
   apply(simp add: boundedBy0)
   apply(subgoal_tac "(0,Gamma) : tree subs Gamma") apply(blast) apply(rule tree0)
  apply(intro impI allI)
  apply(drule_tac x=Gamma in spec)
  apply(erule impE)
   apply(rule)
   apply(drule_tac x=sigma in spec)
   apply(erule impE)
    apply(rule boundedBySuc) apply(assumption) apply(assumption) 
   apply(assumption)
  apply(assumption)
  done

lemma boundedTreeInduction2: "[| fans subs; 
  boundedBy m (tree subs Gamma);
  !delta. (! sigma:subs delta. P sigma) --> P delta
  |] 
  ==> P Gamma"
  apply(frule_tac boundedTreeInduction2')
  apply(assumption)
  apply(force)
  done

end
