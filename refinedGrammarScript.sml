open HolKernel boolLib bossLib Parse
open stringTheory relationTheory;
open pred_setTheory regexpTheory;
open grammarDefTheory listTheory;

 
val _ = new_theory "refinedGrammar";    
(* ----------------------------- *)
(* Basic definitions and tactics *)
(* ----------------------------- *)

val THROW_AWAY_TAC = fn MATCH => (REPEAT (PAT_ASSUM MATCH (fn th => IMP_RES_TAC th)));
val THROW_ONE_AWAY_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => IMP_RES_TAC th));
val TAKE_DOWN_TAC = fn pat => PAT_ASSUM  pat (fn thm => let val c = concl thm  in  ASSUME_TAC thm  end);


val donotContain_def = Define `
  donotContain t x = ~(?w1 w2. t = w1 ++ x ++ (w2:symbol list))`;

val containAtLeastOne_def = Define `
  containAtLeastOne t x = (?w1 w2. t = w1 ++ x ++ (w2:symbol list))`;

val containOnlyone_def = Define`
  containOnlyone t x = ! u v. donotContain u x /\ donotContain v x /\ (t = u ++ x ++ (v:symbol list))`;

val containMoreThanOne_def = Define `
  containMoreThanOne t x = (?w1 w2 w3. t = w1 ++ x ++ (w2:symbol list) ++ x ++ w3)`;

(* ----------------------------- *)
(* Axioms                        *)
(* ----------------------------- *)

val generating_nts_startSym_reachable = new_axiom("generating_nts_startSym_reachable",
``!s p u w. 
   let g = (G p s)      in
   (w IN (language g))  ==>
   ((derives g)^* u w)  ==>
   ((derives g)^* [NTS s] u)``
);


val null_grammar = new_axiom("null_grammar",
 ``!g s1 s2 s3. (is_null g s1) \/ (is_null g s2) \/ (is_null g s3) ==> is_null g (s1++s2++s3)``
);

val null_rule = new_axiom("null_rule",
``!s p s1 P Q. 
   (!w x:symbol list. 
	(
	  (RTC (derives (G p s)) s1 w) ==> 
          (EVERY isTmnlSym w)  ==> 
          ((P w x) /\ (Q w x))
	) ==>
	 (P w x <=> ~Q w x) ==>
	 (is_null (G p s) s1)
   )
``);

(* ----------------------------- *)
(* Helper Lemmas                 *)
(* ----------------------------- *)

val run_1_step = Q.prove(
`! s p u. ((rule s u) IN p) ==> (derives (G p s) [NTS s]  u)`,
     rw [derives_def]
  \\ MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`, `u`, `s`]
  \\full_simp_tac (srw_ss())[rules_def]);

val run_1_step_ns = Q.prove(
`! s p u ns. ((rule ns u) IN p) ==> (derives (G p s) [NTS ns]  u)`,  
  SRW_TAC [] [derives_def]
  \\ MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`, `u`, `ns`]
  \\full_simp_tac (srw_ss())[rules_def]);

val lemma2gen = store_thm("lemma2gen",
``!g s1 s2 s1' s2' s.derives g (s1++s2) s ==> 
     (?s1'. RTC (derives g) s1 s1' /\ (s=s1'++s2)) \/ (?s2'. RTC (derives g) s2 s2' /\ (s=s1++s2'))``,
   SRW_TAC [] [] 
   \\ RULE_ASSUM_TAC (REWRITE_RULE [derives_def])  
   \\ FULL_SIMP_TAC (srw_ss()) [] 
   \\ `?l1 l2.((s1=s1'++[NTS lhs]++l1) /\ (s2=l2) /\ (s2'=l1++l2)) \/
              ((s2=l2++[NTS lhs]++s2') /\ (s1=l1) /\ (s1'=l1++l2))` by METIS_TAC [list_r6] 
   THENL[DISJ1_TAC
        \\ SRW_TAC [] [derives_def]
	\\ full_simp_tac (srw_ss())[Once RTC_CASES1]
	\\ disj2_tac
	\\ exists_tac ``((((s1' ⧺ (rhs :symbol list)) :symbol list) ⧺ l1) :symbol list)``
	\\ full_simp_tac (srw_ss()) [derives_def, run_1_step]
	\\ MAP_EVERY Q.EXISTS_TAC [`s1':symbol list`,`l1:symbol list`,`rhs`,`lhs`]
	\\ full_simp_tac (srw_ss()) [],
 
         disj2_tac
        \\ schneiderUtils.UNDISCH_ALL_TAC
	\\ rw[]
	\\ full_simp_tac (srw_ss())[Once RTC_CASES1]
	\\ disj2_tac
	\\ exists_tac ``((((l2 ⧺ (rhs :symbol list)) :symbol list) ⧺ s2') :symbol list)``
	\\ full_simp_tac (srw_ss()) [derives_def, run_1_step]
	\\ MAP_EVERY Q.EXISTS_TAC [`l2:symbol list`,`s2':symbol list`,`rhs`,`lhs`]
	\\ full_simp_tac (srw_ss()) []
]);

val derives_same_append_right_rtc = store_thm ("derives_same_append_right_rtc",
``!g u v.RTC (derives g) u v ==> !x. RTC (derives g) (u++x) (v++x)``,
  GEN_TAC 
  \\ HO_MATCH_MP_TAC relationTheory.RTC_INDUCT  
  \\ METIS_TAC [relationTheory.RTC_RULES,derives_same_append_right]
);

val derives_same_append_left_rtc = store_thm ("derives_same_append_left_rtc",
``!g u v.RTC (derives g) u v ==> !x. RTC (derives g) (x++u) (x++v)``,
  GEN_TAC 
  \\ HO_MATCH_MP_TAC relationTheory.RTC_INDUCT  
  \\ METIS_TAC [relationTheory.RTC_RULES,derives_same_append_left]
);

val trans_derive_thm = Q.prove(
`!s p s1 s2 s3 x . 
   (RTC(derives (G p s)) [NTS s] (s1++s2++s3))  ==> 
   (RTC(derives (G p s)) s2 x) ==>
   (RTC(derives (G p s)) [NTS s] (s1++x++s3)) `,

     rw[]
  \\ assume_tac(SPECL [``(G (p :rule -> bool) (s :string) :grammar)``, 
		  ``(s2 :symbol list)``, ``(x :symbol list)``] derives_same_append_right_rtc)
  \\ rev_full_simp_tac (arith_ss) []
  \\ qpat_assum `!c. P` (qspecl_then [`(s3 :symbol list)`] ASSUME_TAC)
  \\ assume_tac( SPECL [``(G (p :rule -> bool) (s :string) :grammar)``, 
       ``(s2 :symbol list) ++ (s3 :symbol list)``,
       ``(x :symbol list) ++ (s3 :symbol list)``] derives_same_append_left_rtc
       )
   \\ rev_full_simp_tac (arith_ss) []
   \\ qpat_assum `!c. P` (qspecl_then [`(s1 :symbol list)`] ASSUME_TAC)
   \\ metis_tac[APPEND,APPEND_ASSOC,RTC_CASES_RTC_TWICE]
);

val left_move_rtc = Q.prove(
`! g s1 x p s w.
 let l = rule s (s1 ++ x) in
     (g = (G p s)) ==>      
     (l IN rules (G p s)) ==> 
     ((RTC (derives (G p s)) s1 w) ==> (RTC (derives (G p s)) [NTS s] (w ++ x)))`,

  srw_tac [][rules_def, derives_def,startSym_def]
  \\ rw []
  \\ UNABBREV_ALL_TAC
  \\ simp_tac (srw_ss())[Once RTC_CASES1]
  \\ disj2_tac
  \\ exists_tac ``(((s1 :symbol list) ⧺ (x :symbol list)) :symbol list)``
  \\ full_simp_tac (srw_ss()) [run_1_step]
  \\ assume_tac(SPECL [``(G (p :rule -> bool) (s :string) :grammar)``,
		       ``(s1 :symbol list)``,
		       ``(w :symbol list)``] derives_same_append_right_rtc)
  \\ rev_full_simp_tac (srw_ss()) []
);

val right_move_rtc = Q.prove(
`! g s1 x p s w.
 let l = rule s (x ++ s1) in
     (g = (G p s)) ==>      
     (l IN rules (G p s)) ==> 
     ( (RTC (derives (G p s)) s1 w) ==> (RTC (derives (G p s)) [NTS s] (x ++ w)))`,

  srw_tac [][rules_def, derives_def,startSym_def]
  \\ rw []
  \\ UNABBREV_ALL_TAC
  \\ simp_tac (srw_ss())[Once RTC_CASES1]
  \\ disj2_tac
  \\ exists_tac ``(((x :symbol list) ++ (s1 :symbol list)) :symbol list)``
  \\ full_simp_tac (srw_ss()) [run_1_step]
  \\ assume_tac(SPECL [``(G (p :rule -> bool) (s :string) :grammar)``,
		       ``(s1 :symbol list)``,
		       ``(w :symbol list)``] derives_same_append_left_rtc)
  \\ rev_full_simp_tac (srw_ss()) []
);

val derives_append_gen = Q.prove(
`!g M N P Q. RTC (derives g) M N /\ RTC (derives g) P Q ==> RTC (derives g) (M ++ P) (N ++ Q)`,
  GEN_TAC 
  \\ Q_TAC SUFF_TAC `!x y. RTC (derives g) x y ==> 
                        !u v. RTC (derives g) u v ==>  
                              RTC (derives g) (x ++ u) (y ++ v)` THEN1 METIS_TAC []  
  \\ HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] 
     THENL [METIS_TAC [rtc_derives_same_append_left], METIS_TAC [derives_same_append_right,RTC_RULES]]);
  
val id_rtc = Q.prove(
`!x g. (RTC(derives g) x x)`,  SRW_TAC[] [derives_def, RTC_REFL]
);

val append_same_mid_rtc = Q.prove(
`! g x s1 s2 p s w1 w2.
 let l = rule s (s1 ++  x ++ s2) in
     (g = (G p s)) ==>      
     (l IN rules (G p s)) ==> 
     ((RTC (derives (G p s)) s1 w1) ==> 
      (RTC (derives (G p s)) s2 w2) ==> 
     (RTC (derives (G p s)) [NTS s] (w1 ++ x ++ w2)))`,

  srw_tac [][rules_def, derives_def, startSym_def]
  \\ rw []
  \\ UNABBREV_ALL_TAC
  \\ simp_tac (srw_ss())[Once RTC_CASES1]
  \\ disj2_tac
  \\ exists_tac ``(((s1 :symbol list) ⧺ (x :symbol list)  ⧺ (s2 :symbol list)) :symbol list)``
  \\ full_simp_tac (srw_ss()) [run_1_step]
  \\ assume_tac ( SPECL [``x:symbol list``, ``(G (p :rule -> bool) (s :string) :grammar)``] id_rtc )
  
  \\ assume_tac(
      SPECL[``(G (p :rule -> bool) (s :string) :grammar)``, 
	    ``(s1 :symbol list)``, ``(w1 :symbol list)``,
	    ``(x :symbol list)``, ``(x :symbol list)``]derives_append_gen
  )
  \\ rev_full_simp_tac (arith_ss) []
  \\ assume_tac(
      SPECL[``(G (p :rule -> bool) (s :string) :grammar)``, 
	    ``(s1 :symbol list) ++ x``, ``(w1 :symbol list) ++ x``,
	    ``(s2 :symbol list)``, ``(w2 :symbol list)``]derives_append_gen
  )
  \\ rev_full_simp_tac (arith_ss) []
);

val append_same_mid_rtc2 = Q.prove(
`! g x s1 s2 p s w1 w2 ns.
 let l = rule ns (s1 ++  x ++ s2) in
     (g = (G p s)) ==>      
     (l IN rules (G p s)) ==> 
     ((RTC (derives (G p s)) s1 w1) ==> 
      (RTC (derives (G p s)) s2 w2) ==> 
     (RTC (derives (G p s)) [NTS ns] (w1 ++ x ++ w2)))`,

  srw_tac [][rules_def, derives_def, startSym_def]
  \\ rw []
  \\ UNABBREV_ALL_TAC
  \\ simp_tac (srw_ss())[Once RTC_CASES1]
  \\ disj2_tac
  \\ exists_tac ``(((s1 :symbol list) ⧺ (x :symbol list)  ⧺ (s2 :symbol list)) :symbol list)``
  \\ full_simp_tac (srw_ss()) [run_1_step]
  \\ assume_tac ( SPECL [``x:symbol list``, ``(G (p :rule -> bool) (s :string) :grammar)``] id_rtc )
  
  \\ assume_tac(
      SPECL[``(G (p :rule -> bool) (s :string) :grammar)``, 
	    ``(s1 :symbol list)``, ``(w1 :symbol list)``,
	    ``(x :symbol list)``, ``(x :symbol list)``]derives_append_gen
  )
  \\ rev_full_simp_tac (arith_ss) []
  \\ assume_tac(
      SPECL[``(G (p :rule -> bool) (s :string) :grammar)``, 
	    ``(s1 :symbol list) ++ x``, ``(w1 :symbol list) ++ x``,
	    ``(s2 :symbol list)``, ``(w2 :symbol list)``]derives_append_gen
  )
  \\ rev_full_simp_tac (arith_ss) []
  \\ simp_tac(srw_ss()) [derives_def]
  \\  MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`, `(((((s1 :symbol list) ⧺ (x :symbol list)) :symbol list) ⧺
          (s2 :symbol list))
           :symbol list)`, `ns:string`]
 \\ full_simp_tac (srw_ss()) [rules_def]
);

val neg_rtc_neg_single_step = Q.prove (
  `!g u v . ~(RTC(derives g) u v) ==> ~(derives g u v)`, 
  rw []
  \\ CCONTR_TAC
  \\ full_simp_tac (srw_ss()) []
);

val split_derive_rel = Q.prove(
`!x y z g u v.
   RTC (derives g) u v ==>
   (u=x++y++z) ==> 
   (?x' y' z'. ((v=x'++y'++z') /\
          RTC (derives g) x x' /\ 
	  RTC (derives g) y y' /\
          RTC (derives g) z z')
   )`,

  ntac 4 GEN_TAC 
  \\ HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 
  \\ SRW_TAC [] [] 
  \\ `derives g (x' ++ (y' ++ z')) v' ==> 
       (?x''. derives g x' x''    /\
              (v'=x''++(y'++z'))) \/ 
              (?y''.derives g (y'++z') y'' /\ 
	      (v'=x'++y''))` by SRW_TAC [][lemma2,APPEND,APPEND_ASSOC] 
  \\ `derives g (x' ++ y' ++ z') v' =  derives g (x' ++ (y' ++ z')) v'` by SRW_TAC [] [] 
  \\ RES_TAC THENL[ METIS_TAC [APPEND,APPEND_ASSOC,RTC_RULES_RIGHT1],
         RES_TAC 
      \\ `derives g (y' ++ z') y'' ==>
           (?s1'.derives g y' s1' /\ 
           (y''=s1'++z'))         \/
           (?s2'.derives g z' s2' /\ (y''=y'++s2'))` by METIS_TAC [lemma2] 
      \\ RES_TAC 
      \\ METIS_TAC [RTC_RULES_RIGHT1,APPEND_ASSOC,APPEND]]
);

val onlyOne_impl_atLeastOne_thm = Q.prove(
 `! t x. containOnlyone t x ==> containAtLeastOne t x`,
   rw[containAtLeastOne_def, containOnlyone_def]
);

val donotContain_fromNotDerivable_thm = Q.prove(
 `! s x y g.
   ((derives g)^* s y) /\ (¬(derives g)^* s [TS x]) /\ (EVERY isTmnlSym [TS (x:string)]) ==>
	    			(¬(derives g)^* y [TS x])`,

  rw[]
  \\ CCONTR_TAC
  \\ full_simp_tac (srw_ss()) []
  \\ metis_tac [RTC_CASES_RTC_TWICE]
);

val neg_donotContain_impl_onlyOneOrAtLeastOne = Q.prove(
`! x s'.
  (! w. (derives (G p s))^* s' w ==> ~donotContain w x) ==> 
   (!w'. (derives (G p s))^* s' w' ==> (containOnlyone w' x \/ containAtLeastOne w' x))`,
   rw[donotContain_def, containAtLeastOne_def, containOnlyone_def]
   \\ metis_tac []
);

val neg_donotContain_impl_AtLeastOne = Q.prove(
`! x s'.
  (! w. (derives (G p s))^* s' w ==> ~donotContain w x) ==> 
   (!w'. (derives (G p s))^* s' w' ==> ( containAtLeastOne w' x))`,
   rw[donotContain_def, containAtLeastOne_def, containOnlyone_def]
   \\ metis_tac []
);

val containAtLeastOne_disj_containOnlyone = Q.prove(
`(!s3 w3 g x. (derives g)^* s3 w3 ==>
      (containOnlyone w3 [TS x] \/ containAtLeastOne w3 [TS x]) ==>
      (containAtLeastOne w3 [TS x])
)`,
      rw[]
   \\ full_simp_tac (srw_ss())[containAtLeastOne_def, containOnlyone_def]
);

val neg_donotContain = Q.prove(
`(!s3 w3 g x. (derives g)^* s3 w3 ==>
      ~(donotContain w3 [TS x]) ==>
      (containAtLeastOne w3 [TS x])
)`,
      rw[]
   \\ metis_tac[containAtLeastOne_def, donotContain_def]
);


val containAtLeastOne_impl_neg_donotContain = Q.prove(
`(!s3 w3 g x. (derives g)^* s3 w3 ==>
      (containAtLeastOne w3 [TS x]) ==>
      ~(donotContain w3 [TS x])
      
)`,
      rw[]
   \\ metis_tac[containAtLeastOne_def, donotContain_def]
);

(* ---------------------------------------------------------- *)
(* Basic case                                                 *)
(* ---------------------------------------------------------- *)

(* ---------------------------------------------------------- *)
(* Grammar contaning at-least-one fault                       *)
(* ---------------------------------------------------------- *)

val lang_includes_atLeatOne_x_def = Define`
  lang_includes_atLeatOne_x s p s1 s2 s3 x = 
  let g = (G p s)  in
 
     (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2)) ==>  
     (!w. (w IN language g) ==> (RTC (derives g) (s1 ++ s3 ++ s2) w) ==> 
	  (? w1 w2 w3. 
	     (RTC (derives g) s1 w1) ==> 
	     (RTC (derives g) s2 w2) ==>	
	     (RTC (derives g) s3 w3 /\ (containAtLeastOne w3 [TS x])) ==>     
	     (EVERY isTmnlSym w1) ==>
	     (EVERY isTmnlSym w2) ==>
	     (EVERY isTmnlSym w3) ==>
	     (w = w1 ++ w3  ++ w2) 
	  )
     )
`;

val lang_includes_atLeatOne_x_lem = Q.prove(
`!s p s1 s2 s3 x. 
     lang_includes_atLeatOne_x s p s1 s2 s3 x`,
 
     srw_tac [][lang_includes_atLeatOne_x_def, rules_def, language_def, derives_def]
     \\ assume_tac(
           SPECL [``(s1 :symbol list) ``, ``(s3 :symbol list)``, ``(s2 :symbol list)``,
		  ``(g :grammar)``,
		  ``(((((s1 :symbol list) ⧺ (s3 :symbol list)) :symbol list) ⧺ (s2 :symbol list)) :symbol list)``, ``w:symbol list``] split_derive_rel
)
     \\ full_simp_tac (srw_ss()) []
     \\ rev_full_simp_tac (srw_ss()) []
     \\ exists_tac ``(x' :symbol list)``
     \\ exists_tac ``(z' :symbol list)``
     \\ exists_tac ``(y' :symbol list)``
     \\ rw [isTmnlSym_def]
     \\ UNABBREV_ALL_TAC
     \\ full_simp_tac (srw_ss()) [startSym_def]
);

val lang_includes_atLeatOne_x'_def = Define`
  lang_includes_atLeatOne_x' s p s1 s2 s3 x = 
  let g = (G p s)  in
 
     (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2)) ==>  
     (!w3. (RTC (derives g) (s3) w3) ==> (containAtLeastOne w3 [TS x])) ==>
     (!w. (w IN language g) ==> (RTC (derives g) (s1 ++ s3 ++ s2) w)    ==> 
	 containAtLeastOne w [TS x]
     )
`;

val lang_includes_atLeatOne_x'_lem = Q.prove(
`!s p s1 s2 s3 x. 
     lang_includes_atLeatOne_x' s p s1 s2 s3 x`,
 
     srw_tac [][lang_includes_atLeatOne_x'_def, rules_def, language_def, derives_def]
     \\ assume_tac(
           SPECL [``(s1 :symbol list) ``, ``(s3 :symbol list)``, ``(s2 :symbol list)``,
		  ``(g :grammar)``,
		  ``(((((s1 :symbol list) ⧺ (s3 :symbol list)) :symbol list) ⧺ (s2 :symbol list)) :symbol list)``, ``w:symbol list``] split_derive_rel
)
     \\ full_simp_tac (srw_ss()) []
     \\ rev_full_simp_tac (srw_ss()) []
     \\ qpat_assum `!c. P` (qspecl_then [`y':symbol list`] ASSUME_TAC)
     \\ WEAKEN_TAC is_forall
     \\ rev_full_simp_tac (srw_ss()) [containAtLeastOne_def]

     \\ exists_tac ``(x' :symbol list) ++ (w1)``
     \\ exists_tac ``w2 ++ (z' :symbol list)``
     \\ full_simp_tac (srw_ss()) []
);

(* ----------------------------- *)
(*         None at all           *)
(* ----------------------------- *)

val lang_doesnot_include_x'_def = Define`
  lang_doesnot_include_x' s p s1 s2 x =  
  let g = (G p s)  in
 
     ~(RTC (derives g) [NTS s] (s1 ++ [TS x] ++ s2)) ==>  
     (!w.       
	  (! w1 w2. (RTC (derives (G p s)) s1 w1) ==> 
	     (RTC (derives (G p s)) s2 w2)   ==>
	     (w = w1 ++ [TS x] ++ w2)    ==>
	     (EVERY isTmnlSym w1)    ==>
	     (EVERY isTmnlSym w2) ==>
	     ~(w IN language g))
     )
`;

val lang_doesnot_include_x'_lem = Q.prove(
`!s p s1 s2 x. 
     lang_doesnot_include_x' s p s1 s2 x`,
 
   srw_tac [][lang_doesnot_include_x'_def, rules_def, language_def, derives_def, startSym_def,isTmnlSym_def, LET_DEF]
  \\ CCONTR_TAC
  \\ full_simp_tac (arith_ss)[]
  \\ assume_tac(
      SPECL[``(G (p :rule -> bool) (s :string) :grammar)``, 
	    ``(s1 :symbol list)``, ``(w1 :symbol list)``,
	    ``[TS (x :string)]``, ``[TS (x :string)]``]derives_append_gen
   )
  \\ assume_tac(
      SPECL[``(G (p :rule -> bool) (s :string) :grammar)``, 
	    ``(s1 :symbol list) ++ [TS x]``, ``(w1 :symbol list) ++ [TS x]``,
	    ``(s2 :symbol list)``, ``(w2 :symbol list)``]derives_append_gen
  )
  \\ rev_full_simp_tac (arith_ss) [id_rtc]
  \\ assume_tac(
       SPECL [``s:string``, ``p:rule -> bool``, 
              ``(((((s1 :symbol list) ⧺ [TS (x :string)]) :symbol list) ⧺ (s2 :symbol list)) :symbol list)``,
	      ``(((((w1 :symbol list) ⧺ [TS x]) :symbol list) ⧺ (w2 :symbol list)) :symbol list)``]
	     (SIMP_RULE (srw_ss()) [language_def,startSym_def, LET_DEF] generating_nts_startSym_reachable)
   )
  \\ metis_tac[isTmnlSym_def, EVERY_APPEND, EVERY_DEF]
);


val lang_doesnot_include_x_def = Define`
  lang_doesnot_include_x s p s1 s2 s3 x =  
  let g = (G p s)  in
 
     (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2)) ==>
     (!w1. RTC (derives (G p s)) s1 w1 ==> donotContain w1 [TS x])   ==>
     (!w2. RTC (derives (G p s)) s2 w2 ==> donotContain w2 [TS x])   ==>
     (!w3. RTC (derives (G p s)) s3 w3 ==> donotContain w3 [TS x])   ==>
     (!w. (w IN language g) ==> (RTC (derives g) (s1 ++ s3 ++ s2) w) ==>  
	  (donotContain w [TS x])
     )
`;

val lang_doesnot_include_x'_lem = Q.prove(
`!s p s1 s2 s3 x. 
     lang_doesnot_include_x s p s1 s2 s3 x`,
 
   srw_tac [][lang_doesnot_include_x_def,language_def, derives_def, startSym_def, LET_DEF, donotContain_def]
  \\ CCONTR_TAC
  \\ full_simp_tac (arith_ss)[]
  \\ Q.ABBREV_TAC`w' = w1 ⧺ [TS x] ⧺ w2`
  \\ imp_res_tac LIST_EQ_REWRITE
  \\ qpat_assum `!c. P` (qspecl_then [`LENGTH w1`] ASSUME_TAC)
  \\ SUBGOAL_THEN ``EL (LENGTH (w1:symbol list)) w' = (TS x)`` (fn thm => assume_tac thm)
     >-  full_simp_tac (srw_ss())[ Abbr`w'`, el_append3]
  \\ full_simp_tac (srw_ss ())[]
  \\ SUBGOAL_THEN ``(LENGTH (w1:symbol list)) < (LENGTH (w:symbol list))`` (fn thm => assume_tac thm)
     >- (`(LENGTH (w1:symbol list)) < (LENGTH (w':symbol list))` by full_simp_tac (list_ss)[Abbr`w'`]
         \\ full_simp_tac (srw_ss())[])
  \\ full_simp_tac (srw_ss ())[]
  \\ imp_res_tac MEM_EL
  \\ qpat_assum `!c. P` (qspecl_then [`TS (x:string)`] ASSUME_TAC)
  \\ `MEM (TS x) (w:symbol list)` by rev_full_simp_tac (srw_ss ())[]
  \\ assume_tac(
            SPECL [``s1:symbol list``, ``s3:symbol list``, ``s2:symbol list``,
		   ``(G (p :rule -> bool) (s :string) :grammar)``,
		   ``(((((s1 :symbol list) ⧺ (s3 :symbol list)) :symbol list) ⧺ (s2 :symbol list)) :symbol list)``,
		   ``(w :symbol list)``] split_derive_rel
	)
  \\ `w' = w` by full_simp_tac (srw_ss())[]
  \\ full_simp_tac (srw_ss ())[]
  \\ assume_tac(
       SPECL [``s:string``, ``p:rule -> bool``, 
              ``(((((s1 :symbol list) ⧺ (s3:symbol list)) :symbol list) ⧺ (s2 :symbol list)) :symbol list)``,
	      ``w:symbol list``]
	     (SIMP_RULE (srw_ss()) [language_def,startSym_def, LET_DEF] generating_nts_startSym_reachable)
        )
  \\ rev_full_simp_tac (srw_ss())[]
  \\ full_simp_tac (srw_ss())[MEM_APPEND]
  \\ metis_tac[MEM_SPLIT_APPEND_last]
);

(* ---------------------------------------------------------- *)
(*  Grammar contains exactly-one                              *)
(* ---------------------------------------------------------- *)

val lang_includes_onlyOne_x_def = Define`
  lang_includes_onlyOne_x s p s1 s2 s3 x = 
   let g = (G p s)      in  
        (
	     (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2))                  ==> 
             (!s3'. (RTC (derives g) s3 s3'             ==>
	            (containOnlyone s3' [TS (x:string)] \/
		     donotContain s3' [TS (x:string)])))                 ==> 
             ~(?s11 s12. (RTC (derives g) s1 (s11 ++ [TS x] ++ s12)))    ==> 
             ~(?s21 s22. (RTC (derives g) s2 (s21 ++ [TS x] ++ s22)))    ==> 
             (!w .
	       (w IN language g) ==> (RTC(derives g) (s1 ++ s3 ++ s2) w) ==> 
		 (           
		  (donotContain w [TS x]) \/ (containOnlyone w [TS x])
		 )
	     )
	)
`;

val lang_includes_onlyOne_x_lem = Q.prove(
`! s p s1 s2 s3 x. lang_includes_onlyOne_x s p s1 s2 s3 x`, 

     srw_tac [][lang_includes_onlyOne_x_def, language_def, startSym_def, donotContain_def, containOnlyone_def]
  \\ disj1_tac
  \\ rw[]
  \\ CCONTR_TAC
  \\ Q.ABBREV_TAC`w' = w1 ⧺ [TS x] ⧺ w2`

  \\ full_simp_tac (arith_ss)[]
  \\ imp_res_tac LIST_EQ_REWRITE
  \\ qpat_assum `!c. P` (qspecl_then [`LENGTH w1`] ASSUME_TAC)
  \\ SUBGOAL_THEN ``EL (LENGTH (w1:symbol list)) (w':symbol list) = (TS x)`` (fn thm => assume_tac thm)
     >-  full_simp_tac (srw_ss())[Abbr`w'`,  el_append3]
  \\ full_simp_tac (srw_ss ())[]
  \\ SUBGOAL_THEN ``(LENGTH (w1:symbol list)) < (LENGTH (w:symbol list))`` (fn thm => assume_tac thm)
     >- (`(LENGTH (w1:symbol list)) < (LENGTH (w':symbol list))` by full_simp_tac (list_ss)[Abbr`w'`]
         \\ full_simp_tac (srw_ss())[])
  \\ full_simp_tac (srw_ss ())[]
  \\ imp_res_tac MEM_EL
  \\ qpat_assum `!c. P` (qspecl_then [`TS (x:string)`] ASSUME_TAC)
  \\ `MEM (TS x) (w:symbol list)` by rev_full_simp_tac (srw_ss ())[]
  \\ assume_tac(
            SPECL [``s1:symbol list``, ``s3:symbol list``, ``s2:symbol list``,
		   ``(G (p :rule -> bool) (s :string) :grammar)``,
		   ``(((((s1 :symbol list) ⧺ (s3 :symbol list)) :symbol list) ⧺ (s2 :symbol list)) :symbol list)``,
		   ``(w :symbol list)``] split_derive_rel
	)
  \\ `w' = w` by full_simp_tac (srw_ss())[]
  \\ full_simp_tac (srw_ss ())[]
  \\ assume_tac(
       SPECL [``s:string``, ``p:rule -> bool``, 
              ``(((((s1 :symbol list) ⧺ (s3:symbol list)) :symbol list) ⧺ (s2 :symbol list)) :symbol list)``,
	      ``w:symbol list``]
	     (SIMP_RULE (srw_ss()) [language_def,startSym_def, LET_DEF] generating_nts_startSym_reachable)
        )
  \\ rev_full_simp_tac (srw_ss())[]
  \\ full_simp_tac (srw_ss())[MEM_APPEND]
  \\ metis_tac[MEM_SPLIT_APPEND_last]
);

(* ---------------------------------------------------------- *)
(* Combination                                                *)
(* ---------------------------------------------------------- *)

(* ---------------------------------------------------------- *)
(* at-least-one Conj exactly-one                              *)
(* ---------------------------------------------------------- *)

val atLeastOne_conj_onlyOne_def = Define`
  atLeastOne_conj_onlyOne s p s1 s2 s3 x = 
   let g = (G p s)      in  
        (
	     (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2))                  ==> 
             (!s3'. (RTC (derives g) s3 s3'             ==>
	            (containOnlyone s3' [TS (x:string)])))               /\ 
             ~(?s11 s12. (RTC (derives g) s1 (s11 ++ [TS x] ++ s12)))    /\ 
             ~(?s21 s22. (RTC (derives g) s2 (s21 ++ [TS x] ++ s22)))     
             
	)
`;

val atLeastOne_conj_onlyOne_lem = Q.prove(
`! s p s1 s2 s3 x.
  let g = G p s in
    atLeastOne_conj_onlyOne s p s1 s2 s3 x ==> 
    (derives g)^* [NTS s] (s1 ⧺ s3 ⧺ s2) ==>
      (!w .
	  (w IN language g) ==> (RTC(derives g) (s1 ++ s3 ++ s2) w) ==> 
	  (           
	   (containOnlyone w [TS x])
	  )
      )
`, 
    rw[atLeastOne_conj_onlyOne_def, language_def, startSym_def] 
    \\ full_simp_tac (srw_ss()) []
    \\ assume_tac(
       SPECL [``(s1 :symbol list) ``, ``(s3 :symbol list)``, ``(s2 :symbol list)``,
              ``(G (p :rule -> bool) (s :string) :grammar)``,
	      ``(((((s1 :symbol list)⧺(s3 :symbol list)):symbol list)⧺(s2 :symbol list)):symbol list)``, ``w:symbol list``] split_derive_rel
    )
    \\ rev_full_simp_tac (srw_ss()) []
    \\ CCONTR_TAC
    \\ full_simp_tac (srw_ss())[containOnlyone_def]
    \\ SUBGOAL_THEN ``donotContain (x':symbol list) [TS (x:string)]`` (fn thm => assume_tac thm)
	>- (CCONTR_TAC
            \\ full_simp_tac (srw_ss()) [donotContain_def]
	    \\ TAKE_DOWN_TAC ``!a b. ~P s1 d``
	    \\ qpat_assum `!c d. P` (qspecl_then [`w1:symbol list`, `w2:symbol list`] ASSUME_TAC)
	    \\ full_simp_tac (srw_ss()) []
	   ) 
    \\ SUBGOAL_THEN ``donotContain (z':symbol list) [TS (x:string)]`` (fn thm => assume_tac thm)
	>- (CCONTR_TAC
            \\ full_simp_tac (srw_ss()) [donotContain_def]
	    \\ TAKE_DOWN_TAC ``!a b. ~P s2 d``
	    \\ qpat_assum `!c d. P` (qspecl_then [`w1:symbol list`, `w2:symbol list`] ASSUME_TAC)
	    \\ full_simp_tac (srw_ss()) []
	   )
    \\ TAKE_DOWN_TAC ``!a. b ==> c``
    \\  qpat_assum `!c. P` (qspecl_then [`y':symbol list`] ASSUME_TAC)
    \\ res_tac
    \\ metis_tac[containOnlyone_def, donotContain_def]
);

(* ---------------------------------------------------------- *)
(* at-least-one disj exactly-one                              *)
(* ---------------------------------------------------------- *)

val atLeastOne_disj_onlyOne_def = Define`
  atLeastOne_disj_onlyOne s p s1 s2 s3 x = 
   let g = (G p s)      in  
        (
	     (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2)) ==> 
             (!s3'. (RTC (derives g) s3 s3'             ==>
	            (containAtLeastOne s3' [TS (x:string)])))                      
	)
`;

val atLeastOne_disj_onlyOne_lem = Q.prove(
`! s p s1 s2 s3 x.
  let g = G p s in
    atLeastOne_disj_onlyOne s p s1 s2 s3 x  ==>
    (derives g)^* [NTS s] (s1 ⧺ s3 ⧺ s2)    ==>
       (!w. (w IN language g) ==> (RTC (derives g) (s1 ++ s3 ++ s2) w)  ==> 	  
	    containAtLeastOne w [TS x]
       )
`,
    rw[atLeastOne_disj_onlyOne_def, containAtLeastOne_def, language_def]
    \\ assume_tac(
             SPECL [``s:string``, ``p:rule -> bool``,
		    ``(((((s1 :symbol list) ⧺ (s3 :symbol list)) :symbol list)⧺(s2 :symbol list)) :symbol list)``,
		    ``w:symbol list``]  generating_nts_startSym_reachable)
     \\ rev_full_simp_tac (srw_ss())[language_def, LET_DEF]
     \\ full_simp_tac (srw_ss())[]
     \\ imp_res_tac (SIMP_RULE (srw_ss())[lang_includes_atLeatOne_x'_def, LET_DEF]lang_includes_atLeatOne_x'_lem)
     \\ qpat_assum `!c. P` (qspecl_then [`x:string`] ASSUME_TAC)
     \\ WEAKEN_TAC is_forall
     \\ rev_full_simp_tac (srw_ss()) [containAtLeastOne_def]
     \\ qpat_assum `!c. P` (qspecl_then [`w:symbol list`] ASSUME_TAC)
     \\ WEAKEN_TAC is_forall
     \\ rev_full_simp_tac (srw_ss()) [language_def, startSym_def]
     \\ exists_tac ``w1:symbol list``
     \\ exists_tac ``w2:symbol list``
     \\ rw []
);

val atLeastOne_disj_onlyOne' = Q.prove(
`! s p s1 s2 s3 x.
  let g = G p s in
  ((lang_includes_onlyOne_x s p s1 s2 s3 x) \/ (lang_includes_atLeatOne_x' s p s1 s2 s3 x)) ==>
     (!w3. (derives g)^* s3 w3 ⇒ (~ donotContain w3 [TS x]))          ==>
     (!w. (w IN language g) ==> (RTC (derives g) (s1 ++ s3 ++ s2) w)  ==> 
	  
	  containAtLeastOne w [TS x]
     )
`,
    rw[lang_includes_atLeatOne_x'_def, lang_includes_onlyOne_x_def, containAtLeastOne_def, language_def]
    THENL[assume_tac(
             SPECL [``s:string``, ``p:rule -> bool``,
		    ``(((((s1 :symbol list) ⧺ (s3 :symbol list)) :symbol list)⧺(s2 :symbol list)) :symbol list)``,
		    ``w:symbol list``]  generating_nts_startSym_reachable)
       \\ rev_full_simp_tac (srw_ss())[language_def, LET_DEF]
       \\ full_simp_tac (srw_ss())[]
       \\ assume_tac(
            SPECL [``s1:symbol list``, ``s3:symbol list``, ``s2:symbol list``,
		   ``(G (p :rule -> bool) (s :string) :grammar)``,
		   ``(((((s1 :symbol list) ⧺ (s3 :symbol list)) :symbol list) ⧺ (s2 :symbol list)) :symbol list)``,
		   ``(w :symbol list)``] split_derive_rel
	)
       \\ assume_tac (SPECL [``[TS (x:string)]``, ``s3:symbol list``]neg_donotContain_impl_AtLeastOne)
       \\ rev_full_simp_tac (arith_ss) []
       \\ imp_res_tac (SIMP_RULE (srw_ss()) [lang_includes_atLeatOne_x'_def,LET_DEF]lang_includes_atLeatOne_x'_lem)
       \\ qpat_assum `!c. P` (qspecl_then [`w:symbol list`] ASSUME_TAC)
       \\ WEAKEN_TAC is_forall
       \\ rev_full_simp_tac (srw_ss()) [language_def, startSym_def, containAtLeastOne_def]
       \\ full_simp_tac (srw_ss()) [], 

         assume_tac(
             SPECL [``s:string``, ``p:rule -> bool``,
		    ``(((((s1 :symbol list) ⧺ (s3 :symbol list)) :symbol list)⧺(s2 :symbol list)) :symbol list)``,
		    ``w:symbol list``]  generating_nts_startSym_reachable)
       \\ rev_full_simp_tac (srw_ss())[language_def, LET_DEF]
       \\ full_simp_tac  (srw_ss()) []
       \\ assume_tac (SPECL [``[TS (x:string)]``, ``s3:symbol list``]neg_donotContain_impl_AtLeastOne)
       \\ rev_full_simp_tac (arith_ss) [containAtLeastOne_def]]
);

(* ---------------------------------------------------------- *)
(* at-least-one disj none-at-all                              *)
(* ---------------------------------------------------------- *)
val atLeastOne_disj_none_def = Define`
  atLeastOne_disj_none s p s1 s2 s3 x = 
   let g = (G p s)      in  
        (
	     (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2)) ==> 
             (!s3'. (RTC (derives g) s3 s3'             ==>
	            (containAtLeastOne s3' [TS (x:string)])))                      
	)
`;

val atLeastOne_disj_none = Q.prove(
`! s p s1 s2 s3 x.
  let g = G p s in
  (atLeastOne_disj_none s p s1 s2 s3 x) ==>
     (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2))                       ==>
     (!w. (w IN language g) ==> (RTC (derives g) (s1 ++ s3 ++ s2) w)  ==> 
	  
	  containAtLeastOne w [TS x]
     )
`,
    rw[atLeastOne_disj_none_def, containAtLeastOne_def, language_def]
    \\ assume_tac(
             SPECL [``s:string``, ``p:rule -> bool``,
		    ``(((((s1 :symbol list) ⧺ (s3 :symbol list)) :symbol list)⧺(s2 :symbol list)) :symbol list)``,
		    ``w:symbol list``]  generating_nts_startSym_reachable)
     \\ rev_full_simp_tac (srw_ss())[language_def, LET_DEF]
     \\ full_simp_tac (srw_ss())[]
     \\ imp_res_tac (SIMP_RULE (srw_ss())[lang_includes_atLeatOne_x'_def, LET_DEF]lang_includes_atLeatOne_x'_lem)
     \\ qpat_assum `!c. P` (qspecl_then [`x:string`] ASSUME_TAC)
     \\ WEAKEN_TAC is_forall
     \\ rev_full_simp_tac (srw_ss()) [containAtLeastOne_def]
     \\ qpat_assum `!c. P` (qspecl_then [`w:symbol list`] ASSUME_TAC)
     \\ WEAKEN_TAC is_forall
     \\ rev_full_simp_tac (srw_ss()) [language_def, startSym_def]
     \\ exists_tac ``w1:symbol list``
     \\ exists_tac ``w2:symbol list``
     \\ rw []
);

(* ---------------------------------------------------------- *)
(* negation of exactly one                                    *)
(* ---------------------------------------------------------- *)

val lang_neg_includes_onlyOne_x_def = Define`
  lang_neg_includes_onlyOne_x s p s1 s2 s3 x = 
   let g = (G p s)      in  
        (
	     (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2))                        ==> 
	     (
                ((?s3'. (RTC (derives g) s3 s3'             ==>
	              (containMoreThanOne s3' [TS (x:string)])))               /\ 
                 ~(?s11 s12. (RTC (derives g) s1 (s11 ++ [TS x] ++ s12)))      /\
		 ~(?s21 s22. (RTC (derives g) s2 (s21 ++ [TS x] ++ s22))))     \/

                ((∀s3'.  (derives g)^* s3 s3' ⇒
                       containOnlyone s3' [TS x] ∨ donotContain s3' [TS x])    /\ 
                 (?w1.(RTC (derives g) s1 w1 ==> containAtLeastOne w1 [TS x])) /\
		 ~(?s21 s22. (RTC (derives g) s2 (s21 ++ [TS x] ++ s22))))     \/

                ((∀s3'.  (derives g)^* s3 s3' ⇒
                       containOnlyone s3' [TS x] ∨ donotContain s3' [TS x])    /\ 
                 ~(?s11 s12.(RTC (derives g) s1 (s11 ++ [TS x] ++ s12)))       /\
		 (?w2.(RTC (derives g) s2 w2 ==> containAtLeastOne w2 [TS x])))     
	     )                                                                 ==> 
                   
             (!w .
	       (w IN language g)        ==>
	       (?w1 w2 w3.
		 (RTC(derives g) s1 w1) ==>
		 (RTC(derives g) s2 w2) ==> 
		 (RTC(derives g) s3 w3) ==>
		 (w = w1 ++ w3 ++ w2)   ==>
		 ((containMoreThanOne w [TS x]) \/ (donotContain w [TS x]))
	       )
	      
	     )
	)
`;

val NIL_APPEND = Q.prove(`!l. [] ++ l = l`, full_simp_tac(srw_ss()) []);

val lang_not_includes_onlyOne_x = Q.prove(
`! s p s1 s2 s3 x. lang_neg_includes_onlyOne_x s p s1 s2 s3 x`,

   rw[lang_neg_includes_onlyOne_x_def]
   THENL[MAP_EVERY Q.EXISTS_TAC [`[]:symbol list`,`[]:symbol list`, `s3':symbol list`] 
         \\ full_simp_tac (srw_ss()) [],

         TAKE_DOWN_TAC ``!s3'. a ==> (b \/ c)``
         \\ qpat_assum `!c. P` (qspecl_then [`s3':symbol list`] ASSUME_TAC)
	 \\ WEAKEN_TAC is_forall
	 \\ rev_full_simp_tac (srw_ss()) []
	 \\ full_simp_tac (srw_ss()) []

         \\ `! a b c. (a ==> (b \/ c)) ==> ((a ==> b) \/ (a ==> c))` by metis_tac[]
	 \\ qpat_assum `!c. P` 
          (qspecl_then [`(derives (G (p :rule -> bool) (s :string)))^* (s3 :symbol list) (s3' :symbol list)`,
                `containOnlyone s3' [TS (x :string)]`, `donotContain s3' [TS x]`]
		      ASSUME_TAC)

         \\ rev_full_simp_tac (srw_ss())[]
         THENL[MAP_EVERY Q.EXISTS_TAC [`w1:symbol list`,`[]:symbol list`, `s3':symbol list`] 
               \\ rw[]
	       \\ full_simp_tac (srw_ss()) []
	       \\ disj1_tac
	       \\ full_simp_tac (srw_ss()) [containMoreThanOne_def, containAtLeastOne_def, containOnlyone_def]
	       \\ qpat_assum `!c. P` (qspecl_then [`[]:symbol list`, `[]:symbol list`] ASSUME_TAC)
	       \\ WEAKEN_TAC is_forall
	       \\ full_simp_tac (srw_ss()) []
	       \\  MAP_EVERY Q.EXISTS_TAC [`w1':symbol list`,`w2:symbol list`, `[]:symbol list`] 
	       \\ full_simp_tac (srw_ss()) [],
               MAP_EVERY Q.EXISTS_TAC [`[]:symbol list`,`[]:symbol list`, `s3':symbol list`] 
               \\ rw[]
	       \\ full_simp_tac (srw_ss()) []],

         TAKE_DOWN_TAC ``!s3'. a ==> (b \/ c)``
         \\ qpat_assum `!c. P` (qspecl_then [`s3':symbol list`] ASSUME_TAC)
	 \\ WEAKEN_TAC is_forall
	 \\ rev_full_simp_tac (srw_ss()) []
	 \\ full_simp_tac (srw_ss()) []

         \\ `! a b c. (a ==> (b \/ c)) ==> ((a ==> b) \/ (a ==> c))` by metis_tac[]
	 \\ qpat_assum `!c. P` 
          (qspecl_then [`(derives (G (p :rule -> bool) (s :string)))^* (s3 :symbol list) (s3' :symbol list)`,
                `containOnlyone s3' [TS (x :string)]`, `donotContain s3' [TS x]`]
		      ASSUME_TAC)

         \\ rev_full_simp_tac (srw_ss())[]
         THENL[MAP_EVERY Q.EXISTS_TAC [`[]:symbol list`, `w2:symbol list`, `s3':symbol list`] 
               \\ rw[]
	       \\ full_simp_tac (srw_ss()) []
	       \\ disj1_tac
	       \\ full_simp_tac (srw_ss()) [containMoreThanOne_def, containAtLeastOne_def, containOnlyone_def]
	       \\ qpat_assum `!c. P` (qspecl_then [`[]:symbol list`, `[]:symbol list`] ASSUME_TAC)
	       \\ WEAKEN_TAC is_forall
	       \\ full_simp_tac (arith_ss) [APPEND_NIL, NIL_APPEND]

	       \\  MAP_EVERY Q.EXISTS_TAC [`[]:symbol list`,`w1:symbol list`,`w2':symbol list`] 
	       \\ full_simp_tac (srw_ss()) [],
               MAP_EVERY Q.EXISTS_TAC [`[]:symbol list`,`[]:symbol list`, `s3':symbol list`] 
               \\ rw[]
	       \\ full_simp_tac (srw_ss()) []]

	]
);


(* ---------------------------------------------------------- *)
(* Negation of the none-at-all                                *)
(* ---------------------------------------------------------- *)

val lang_not_doesnot_include_x_def = Define`
  lang_not_doesnot_include_x s p s1 s2 s3 x =  
  let g = (G p s)  in
 
     (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2)) ==>
     (
      (~(!w1. RTC (derives g) s1 w1 ==> EVERY isTmnlSym w1 ==> donotContain w1 [TS x])  /\
      (!w2. RTC (derives g) s2 w2   ==> EVERY isTmnlSym w2 ==> donotContain w2 [TS x])  /\
      (!w3. RTC (derives g) s3 w3   ==> EVERY isTmnlSym w3 ==> donotContain w3 [TS x])) \/

     ((!w1. RTC (derives g) s1 w1   ==> EVERY isTmnlSym w1 ==> donotContain w1 [TS x])  /\
      ~(!w2. RTC (derives g) s2 w2  ==> EVERY isTmnlSym w2 ==> donotContain w2 [TS x])  /\
      (!w3. RTC (derives g) s3 w3   ==> EVERY isTmnlSym w3 ==> donotContain w3 [TS x])) \/

     ((!w1. RTC (derives g) s1 w1   ==> EVERY isTmnlSym w1 ==> donotContain w1 [TS x])  /\
      (!w2. RTC (derives g) s2 w2   ==> EVERY isTmnlSym w2 ==> donotContain w2 [TS x])  /\
      ~(!w3. RTC (derives g) s3 w3  ==> EVERY isTmnlSym w3 ==> donotContain w3 [TS x]))
     ) 
`;

val lang_not_doesnot_include_x_lem = Q.prove(
  `! s p s1 s2 s3 x. 
     let g = (G p s)  in
     lang_not_doesnot_include_x s p s1 s2 s3 x ==>
     (RTC (derives (G p s)) [NTS s] (s1 ++ s3 ++ s2)) ==>

     (!w. (w IN language g) ==>
	  (?w1 w2 w3.
	    (RTC(derives g) s1 w1) ==>
	    (RTC(derives g) s2 w2) ==> 
	    (RTC(derives g) s3 w3) ==>
	    (w = w1 ++ w3 ++ w2)   ==>
	     ~(donotContain w [TS x])
	  )
     )`,
  
   rw[lang_not_doesnot_include_x_def, language_def, LET_DEF, startSym_def]
   \\ full_simp_tac (srw_ss())[]
   THENL[MAP_EVERY Q.EXISTS_TAC [`w1:symbol list`,`[]:symbol list`, `[]:symbol list`] 
         \\ full_simp_tac (srw_ss()) [],
         MAP_EVERY Q.EXISTS_TAC [`[]:symbol list`,`w2:symbol list`, `[]:symbol list`] 
         \\ full_simp_tac (srw_ss()) [],
         MAP_EVERY Q.EXISTS_TAC [`[]:symbol list`,`[]:symbol list`, `w3:symbol list`] 
         \\ full_simp_tac (srw_ss()) []]
);

(* val lang_not_doesnot_include_x2'_def = Define`
  lang_not_doesnot_include_x2' s p s1 s2 s3 x =  
  let g = (G p s)  in
 
     (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2)) ==>
     (!w1. RTC (derives g) s1 w1 ==> containAtLeastOne w1 [TS x])   ==>
     (!w2. RTC (derives g) s2 w2 ==> donotContain w2 [TS x])   ==>
     (!w3. RTC (derives g) s3 w3 ==> donotContain w3 [TS x])   ==>
     (!w. (w IN language g) ==> (RTC (derives g) (s1 ++ s3 ++ s2) w) ==>  
	  ~(donotContain w [TS x])
     )
`;

val neg_noneAtAll' = Q.prove(
  `! s p s1 s2 s3 x. lang_not_doesnot_include_x2' s p s1 s2 s3 x`,
   rw[lang_not_doesnot_include_x2'_def, language_def, LET_DEF, startSym_def]
   \\ assume_tac(
       SPECL [``(s1 :symbol list) ``, ``(s3 :symbol list)``, ``(s2 :symbol list)``,
              ``(G (p :rule -> bool) (s :string) :grammar)``,
	      ``(((((s1 :symbol list)⧺(s3 :symbol list)):symbol list)⧺(s2 :symbol list)):symbol list)``, ``w:symbol list``] split_derive_rel
   )
   \\ full_simp_tac (srw_ss()) []
   \\ rev_full_simp_tac (srw_ss()) []
   \\ qpat_assum `!c. P` (qspecl_then [`y':symbol list`] ASSUME_TAC)
   \\ WEAKEN_TAC is_forall
   \\ qpat_assum `!c. P` (qspecl_then [`z':symbol list`] ASSUME_TAC)
   \\ WEAKEN_TAC is_forall
   \\ qpat_assum `!c. P` (qspecl_then [`x':symbol list`] ASSUME_TAC)
   \\ WEAKEN_TAC is_forall
   \\ rev_full_simp_tac (srw_ss())  [donotContain_def, containAtLeastOne_def]
   \\ exists_tac ``(w1:symbol list) ``
   \\ exists_tac ``(w2 :symbol list) ⧺ (y' :symbol list) ⧺ (z' :symbol list)``
   \\ full_simp_tac (srw_ss())[]
 
);*)
(* ----------------------------- *)

val lang_doesnot_include_x_disj_itsNegation_def = Define`
    lang_doesnot_include_x_disj_itsNegation s p s1 s2 s3 x =
       let g = G p s in

       (((!w1. RTC (derives g) s1 w1 ==> containAtLeastOne w1 [TS x] \/ donotContain w1 [TS x]) /\
        (!w2. RTC (derives g) s2 w2 ==> donotContain w2 [TS x])      /\
        (!w3. RTC (derives g) s3 w3 ==> donotContain w3 [TS x]))     \/

        ((!w1. RTC (derives g) s1 w1 ==> donotContain w1 [TS x])     /\
        (!w2. RTC (derives g) s2 w2 ==> containAtLeastOne w2 [TS x]  \/ donotContain w2 [TS x]) /\
        (!w3. RTC (derives g) s3 w3 ==> donotContain w3 [TS x]))     \/ 

        ((!w1. RTC (derives g) s1 w1 ==> donotContain w1 [TS x])     /\
        (!w2. RTC (derives g) s2 w2 ==> donotContain w2 [TS x])      /\
        (!w3. RTC (derives g) s3 w3 ==> containAtLeastOne w3 [TS x]  \/ donotContain w3 [TS x]))) 
`;

val lang_doesnot_include_x_disj_itsNegation_lem = Q.prove(
`! s p s1 s2 s3 x.
  let g = G p s in
    lang_doesnot_include_x_disj_itsNegation s p s1 s2 s3 x ==>
    (!w. (w IN language g) ==> (RTC (derives g) (s1 ++ s3 ++ s2) w)  ==> 
	 containAtLeastOne w [TS x] \/ donotContain w [TS x]
    )
`,
   rw[language_def, startSym_def, lang_doesnot_include_x_disj_itsNegation_def]
   \\ assume_tac(
       SPECL [``(s1 :symbol list) ``, ``(s3 :symbol list)``, ``(s2 :symbol list)``,
              ``(G (p :rule -> bool) (s :string) :grammar)``,
	      ``(((((s1 :symbol list)⧺(s3 :symbol list)):symbol list)⧺(s2 :symbol list)):symbol list)``, ``w:symbol list``] split_derive_rel
    )
   \\ full_simp_tac (srw_ss()) []
   \\ rev_full_simp_tac (srw_ss()) []
   \\ qpat_assum `!c. P` (qspecl_then [`y':symbol list`] ASSUME_TAC)
   \\ WEAKEN_TAC is_forall
   \\ qpat_assum `!c. P` (qspecl_then [`z':symbol list`] ASSUME_TAC)
   \\ WEAKEN_TAC is_forall
   \\ qpat_assum `!c. P` (qspecl_then [`x':symbol list`] ASSUME_TAC)
   \\ WEAKEN_TAC is_forall
   \\ rev_full_simp_tac (srw_ss())[containAtLeastOne_def]

   \\ FIRST_PROVE[disj1_tac
         \\ exists_tac ``(w1:symbol list) ``
	 \\ exists_tac ``(w2 :symbol list) ⧺ (y' :symbol list) ⧺ (z' :symbol list)``
	 \\ full_simp_tac (srw_ss())[],

         disj1_tac
	 \\ exists_tac ``(x' :symbol list) ⧺ (y' :symbol list) ⧺ (w1 :symbol list)``
         \\ exists_tac ``(w2:symbol list) ``
	 \\ full_simp_tac (srw_ss())[],

         disj1_tac
         \\ exists_tac ``(x':symbol list) ++ (w1:symbol list) ``
	 \\ exists_tac ``(w2 :symbol list) ⧺ (z' :symbol list)``
	 \\ full_simp_tac (srw_ss())[],

        disj2_tac
        \\ full_simp_tac (srw_ss()) [donotContain_def]
	\\ CCONTR_TAC
	\\ full_simp_tac (arith_ss)[]
	\\ Q.ABBREV_TAC`w' = w1 ⧺ [TS x] ⧺ w2`
	\\ imp_res_tac LIST_EQ_REWRITE
	\\ qpat_assum `!c. P` (qspecl_then [`LENGTH w1`] ASSUME_TAC)
	\\ SUBGOAL_THEN ``EL (LENGTH (w1:symbol list)) w' = (TS x)`` (fn thm => assume_tac thm)
	>-  full_simp_tac (srw_ss())[ Abbr`w'`, el_append3]
        \\ full_simp_tac (srw_ss ())[]
	\\ SUBGOAL_THEN ``(LENGTH (w1:symbol list)) < (LENGTH (w:symbol list))`` (fn thm => assume_tac thm)
        >- (`(LENGTH (w1:symbol list)) < (LENGTH (w':symbol list))` by full_simp_tac (list_ss)[Abbr`w'`]
             \\ full_simp_tac (srw_ss())[])
        \\ full_simp_tac (srw_ss ())[]
	\\ imp_res_tac MEM_EL
	\\ qpat_assum `!c. P` (qspecl_then [`TS (x:string)`] ASSUME_TAC)
	\\ `MEM (TS x) (w:symbol list)` by rev_full_simp_tac (srw_ss ())[]
	\\ full_simp_tac (srw_ss())[MEM_APPEND]
	\\ metis_tac[MEM_SPLIT_APPEND_last]]
);

(* ----------------------------- *)

val containAtLeastOne_impl_neg_donotContain = Q.prove(
`(! w3 x.
    (donotContain w3 [TS x]) =
  ~(containAtLeastOne w3 [TS x])      
)`,
      rw[]
   \\ metis_tac[containAtLeastOne_def, donotContain_def]
);


val lang_doesnot_include_x_conj_itsNegation_def = Define`
    lang_doesnot_include_x_conj_itsNegation s p s1 s2 s3 x =  
       let g = (G p s)  in
 
       (RTC (derives g) [NTS s] (s1 ++ s3 ++ s2)) ==>
       (
        ((?w1. RTC (derives g) s1 w1 ==> EVERY isTmnlSym w1 ==>
                (donotContain w1 [TS x] /\  containAtLeastOne w1 [TS x])) /\
        (!w2. RTC (derives g) s2 w2 ==> EVERY isTmnlSym w2 ==> donotContain w2 [TS x])    /\
        (!w3. RTC (derives g) s3 w3 ==> EVERY isTmnlSym w3 ==> donotContain w3 [TS x]))   \/

        ((!w1. RTC (derives g) s1 w1 ==> EVERY isTmnlSym w1 ==> donotContain w1 [TS x])   /\
        (?w2.  RTC (derives g) s2 w2 ==> EVERY isTmnlSym w2 ==>
                (donotContain w2 [TS x] /\  containAtLeastOne w2 [TS x])) /\
        (!w3. RTC (derives g) s3 w3 ==> EVERY isTmnlSym w3 ==> donotContain w3 [TS x]))   \/

        ((!w1. RTC (derives g) s1 w1 ==> EVERY isTmnlSym w1 ==> donotContain w1 [TS x])   /\
        (!w2.  RTC (derives g) s2 w2 ==> EVERY isTmnlSym w2 ==> donotContain w2 [TS x])   /\
        (?w3.  RTC (derives g) s3 w3 ==> EVERY isTmnlSym w3 ==>
              (donotContain w3 [TS x] /\  containAtLeastOne w3 [TS x])))
     )
    
`;

val lang_doesnot_include_x_conj_itsNegation_lem = Q.prove(
`!s p s1 s2 s3 x.
   lang_doesnot_include_x_conj_itsNegation s p s1 s2 s3 x ==>
   (RTC (derives (G p s)) [NTS s] (s1 ++ s3 ++ s2)) ==>
   is_null (G p s) (s1++s3++s2)`,

   rw[lang_doesnot_include_x_conj_itsNegation_def, language_def, LET_DEF, startSym_def, is_null_def]
   \\ full_simp_tac (srw_ss()) []
   THENL[assume_tac(
        SPECL [``s:string``, ``(p :rule -> bool)``, ``s1:symbol list``,
               ``donotContain``, ``containAtLeastOne``] null_rule 
       )
   \\ qpat_assum `!c. P` (qspecl_then [`w1:symbol list`, `[TS (x:string)]`] ASSUME_TAC)
   \\ assume_tac(SPECL [``w1:symbol list``, ``x:string``] containAtLeastOne_impl_neg_donotContain)
   \\ metis_tac [null_grammar, is_null_def],


    assume_tac(
        SPECL [``s:string``, ``(p :rule -> bool)``, ``s2:symbol list``,
               ``donotContain``, ``containAtLeastOne``] null_rule 
       )
   \\ qpat_assum `!c. P` (qspecl_then [`w2:symbol list`, `[TS (x:string)]`] ASSUME_TAC)
   \\ assume_tac(SPECL [``w2:symbol list``, ``x:string``] containAtLeastOne_impl_neg_donotContain)
   \\ metis_tac [null_grammar, is_null_def],


     assume_tac(
        SPECL [``s:string``, ``(p :rule -> bool)``, ``s3:symbol list``,
               ``donotContain``, ``containAtLeastOne``] null_rule 
       )
   \\ qpat_assum `!c. P` (qspecl_then [`w3:symbol list`, `[TS (x:string)]`] ASSUME_TAC)
   \\ assume_tac(SPECL [``w3:symbol list``, ``x:string``] containAtLeastOne_impl_neg_donotContain)
   \\ metis_tac [null_grammar, is_null_def]]
);


(* G & neg(X) == N and G & neg(N) == X, X & neg(X) = empty,  and X | neg(X) == G *)
val _ = export_theory ();








