(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory containerTheory
open pred_setTheory listTheory arithmeticTheory;

val _ = new_theory "listLemma";

(* 14/05/07 AB *)


val list_l1 = store_thm ("list_l1",
``!r.(r=[]) = NULL r``,
Induct_on `r` THEN SRW_TAC [] []);


val filter_l1 = store_thm ("filter_l1",
``!p l.LENGTH (FILTER p l) > 0 ==> (?e.MEM e l /\ p e)``,
Induct_on `l` THEN SRW_TAC [] [] THEN METIS_TAC []
);

val filter_l2 = store_thm ("filter_l2",
``!f l.(LENGTH (FILTER f l) = 0) = ~(?e.MEM e l /\ f e)``,
SRW_TAC [] [EQ_IMP_THM] THEN
Induct_on `l` THEN SRW_TAC [] [] THEN METIS_TAC []
);

val lres = store_thm ("lres",
``(l1 ++ [x] ++ l2 = [y]) ==> ((l1=[]) /\ (l2=[]) /\ (x=y))``,
Cases_on `l1` THEN SRW_TAC [] []
);

val lresb = store_thm ("lresb",
``((l1=[]) /\ (l2=[]) /\ (x=y)) ==> (l1 ++ [x] ++ l2 = [y])``,
SRW_TAC [] []
);

val lreseq = store_thm ("lreseq",
``(l1 ++ [x] ++ l2 = [y]) = ((l1=[]) /\ (l2=[]) /\ (x=y))``,
METIS_TAC [EQ_IMP_THM,lres,lresb]
);


val rgr_r9 = store_thm ("rgr_r9",
``!r.MEM sym r ==> ?r1 r2.r=r1++[sym]++r2``,
Induct_on `r` THENL
[
SRW_TAC [] [],
SRW_TAC [] [] THEN
SRW_TAC [] [] THENL
[
MAP_EVERY Q.EXISTS_TAC [`[]`,`r`] THEN SRW_TAC [] [],
RES_TAC THEN
MAP_EVERY Q.EXISTS_TAC [`h::r1`,`r2`] THEN SRW_TAC [] []
]]
);


 val rgr_r9b = store_thm ("rgr_r9b",
``!r.(?r1 r2.(r=r1++[sym]++r2)) ==> MEM sym r``,
SRW_TAC [] [rgr_r9] THEN SRW_TAC [] [rgr_r9]
);


val rgr_r9eq = store_thm ("rgr_r9eq",
``!r.MEM sym r = (?r1 r2.(r=r1++[sym]++r2))``,
METIS_TAC [rgr_r9,rgr_r9b,EQ_IMP_THM,EQ_SYM]
);

val list_r1 = store_thm ("list_r1",
``!v v' x.(v=v'++[x]) ==> MEM x v``,
SRW_TAC [] []);

val list_r2 = store_thm ("list_r2",
``!s1 s2 rhs x.(s1 ++ rhs ++ s2 = [x]) ==> ~(rhs=[]) ==> (s1=[]) /\ (s2=[])``,

Cases_on `s1` THENL[SRW_TAC [] [] THEN metis_tac[APPEND_EQ_SING],
  SRW_TAC [] [] THEN Cases_on `rhs` THEN SRW_TAC [] [] THEN
`h::t ++ s2 = [h]++(t++s2)` by METIS_TAC [CONS,APPEND,APPEND_11] THEN
`?s.s++[h]++(t++s2) = [h]++(t++s2)` by FULL_SIMP_TAC (srw_ss()) [] THENL[
  Q.EXISTS_TAC `[]` THEN SRW_TAC [] [],
  SRW_TAC [] [] THEN `s ++ [h] ++ (t ++ s2) = [x]` by FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [APPEND_eq_NIL,lres]]]);

val list_r6 = store_thm ("list_r6",
``!s1 s2 s1' s2' x.(s1' ++ [x] ++ s2' = s1 ++ s2) ==> ?l1 l2.((s1=s1'++[x]++l1) /\ (s2=l2) /\ (s2'=l1++l2)) \/ ((s2=l2++[x]++s2') /\ (s1=l1) /\ (s1'=l1++l2))``,
Induct_on `s1'` THENL[
  SRW_TAC [] [EXISTS_OR_THM] THEN
  Cases_on `s1` THEN SRW_TAC [] [] THEN
  FULL_SIMP_TAC (srw_ss()) [],
  SRW_TAC [] [] THEN Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN FULL_SIMP_TAC (srw_ss()) [EXISTS_OR_THM]
]);

val list_lem1 = store_thm ("list_lem1",
``!l.(LENGTH l = 1) = ?e.l=[e]``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Induct_on `l` THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL],
FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL]
]);


val list_lem2 = store_thm ("list_lem2",
``!l.(LENGTH l = 2) = ?e1 e2.l=[e1;e2]``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Induct_on `l` THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,list_lem1],
FULL_SIMP_TAC (srw_ss()) [LENGTH]
])

val list_lem3 = store_thm ("list_lem3",
``!l.(LENGTH l >= 3) = ?e1 e2 e3 r.(l=[e1;e2;e3]++r)``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Induct_on `l` THEN
SRW_TAC [] [] THEN
`LENGTH l >= 2` by DECIDE_TAC THEN
`(LENGTH l = 2) \/ (LENGTH l > 2)` by METIS_TAC [GREATER_OR_EQ] THENL[
METIS_TAC [list_lem2],
`LENGTH l >= 3` by DECIDE_TAC THEN METIS_TAC []],
FULL_SIMP_TAC (srw_ss()) [LENGTH] THEN DECIDE_TAC
])

val list_lem4 = store_thm ("list_lem4",
``!l.(LENGTH l >= 2) = ?e1 e2 r.(l=[e1;e2]++r)``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Induct_on `l` THEN
SRW_TAC [] [] THEN
`LENGTH l >= 1` by DECIDE_TAC THEN
`(LENGTH l = 1) \/ (LENGTH l > 1)` by METIS_TAC [GREATER_OR_EQ] THENL[
METIS_TAC [list_lem1],
`LENGTH l >= 2` by DECIDE_TAC THEN METIS_TAC []],
FULL_SIMP_TAC (srw_ss()) [LENGTH] THEN DECIDE_TAC
])

val l_lemma1 = store_thm("l_lemma1",
``!r.(1 <= LENGTH r) ==> ?h' r'.(r=(h'::r'))``,
Induct_on `r` THEN
SRW_TAC [] []
)

val sl_1 = store_thm ("sl",
``!p s x.LENGTH (p++[x]++s) >= 3 ==> (~NULL s \/ ~NULL p)``,
SRW_TAC [] [] THEN
Cases_on `p` THEN Cases_on `s` THENL[
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL],
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL],
FULL_SIMP_TAC (srw_ss()) [NULL_DEF],
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL]
])

val sl_l2 = store_thm ("sl_l2",
``!p s x.(LENGTH (p ++ [NTS t1] ++ s) >= 2) ==> (~NULL s \/ ~NULL p)``,
SRW_TAC [] [] THEN
Cases_on `p` THEN Cases_on `s` THENL[
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL],
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL],
FULL_SIMP_TAC (srw_ss()) [NULL_DEF],
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL]
])

val sl_l3 = store_thm ("sl_l3",
``!p s.(LENGTH p + LENGTH s >= 1) ==> (~NULL s \/ ~NULL p)``,
SRW_TAC [] [] THEN
Cases_on `p` THEN Cases_on `s` THEN
FULL_SIMP_TAC (srw_ss()) [LENGTH_EQ_NIL]
)

val len0 = store_thm("len0",
``!s.NULL s = (LENGTH s = 0)``,
Cases_on `s` THEN
SRW_TAC [] [])

val notLen1 = store_thm("notLen1",
 ``!p s.(~NULL p \/ ~NULL s) ==> !x.~(LENGTH (p++[x]++s)<=1)``,
SRW_TAC [] [] THENL[
`~(p=[])` by METIS_TAC [list_l1] THEN
`~(LENGTH p = 0)` by METIS_TAC [LENGTH_NIL] THEN
`1 <= LENGTH p` by DECIDE_TAC THEN
`?h' r'.(p=(h'::r'))` by METIS_TAC [l_lemma1] THEN
`LENGTH (h'::r') = LENGTH ([h']++r')` by METIS_TAC [APPEND] THEN SRW_TAC [] [] THEN DECIDE_TAC,
`~(s=[])` by METIS_TAC [list_l1] THEN
`~(LENGTH s = 0)` by METIS_TAC [LENGTH_NIL] THEN
`1 <= LENGTH s` by DECIDE_TAC THEN
`?h' r'.(s=(h'::r'))` by METIS_TAC [l_lemma1] THEN
`LENGTH (h'::r') = LENGTH ([h']++r')` by METIS_TAC [APPEND] THEN SRW_TAC [] [] THEN DECIDE_TAC])

val listNotNull = store_thm("listNotNull",
``!p.~NULL p = ?h t.(p=h::t)``,
SRW_TAC [] [] THEN
Cases_on `p` THEN
SRW_TAC [] [])

val sl_l4 = store_thm("sl_l4",
``!e t1 t2 p s.~([e] = p++[NTS t1;NTS t2]++s)``,
SRW_TAC [] [] THEN Cases_on `p` THEN SRW_TAC [] []
)

val sl_l5 = store_thm("sl_l5",
``!e1 e2 t1 t2 p s.([e1; e2] = p ++ [NTS t1; NTS t2] ++ s) ==> (NULL p /\ NULL s)``,
SRW_TAC [] [] THENL[
Cases_on `p` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC list_ss [] THEN Cases_on `t` THEN FULL_SIMP_TAC list_ss [],
Cases_on `s` THEN SRW_TAC [] [] THEN
Cases_on `p` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC list_ss [] THEN Cases_on `t'` THEN FULL_SIMP_TAC list_ss []]
)


val finiteLists = store_thm("finiteLists",
``!l.FINITE (LIST_TO_SET l)``,
Induct_on `l` THEN
 SRW_TAC [] [LIST_TO_SET_THM]
)

val _ = export_theory ();
