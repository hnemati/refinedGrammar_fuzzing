(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory listTheory;
open pred_setTheory listLemmaTheory;

val _ = new_theory "regexp";

val _ = Hol_datatype `symbol = TS of string| NTS of string`;

(* ??_ case in HOL? *)
(* ??using case construct in HOL *)
val isTmnlSym_def = Define `(isTmnlSym sym = (?s.sym = (TS s)))`;
(* val isTmnlSym_def = Define `isTmnlSym sym = case sym of (TS s) -> T
			|| _ -> F`; *)
val isNonTmnlSym_def = Define `isNonTmnlSym sym = (?s.sym = (NTS s)) \/ F`;

val tmnlSym_def = Define `tmnlSym (TS tmnl) = tmnl`;
val nonTmnlSym_def = Define `nonTmnlSym (NTS ntmnl) = ntmnl`;

val nts2str = Define `nts2str (NTS s) = s`

val ts2str = Define `ts2str (TS s) = s`

val symToStr_def = Define `(symToStr (TS s) = s) /\ (symToStr (NTS s) = s)`;


val sym_r1a = store_thm ("sym_r1a",
``isTmnlSym e ==> ~ isNonTmnlSym e``,
SRW_TAC [] [isTmnlSym_def,isNonTmnlSym_def] THEN
Cases_on `e` THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def] 
);


val sym_r1b = store_thm ("sym_r1b",
``~isTmnlSym e = isNonTmnlSym e``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Cases_on `e` THENL[
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def],
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def,isTmnlSym_def]],
Cases_on `e` THENL[
FULL_SIMP_TAC (srw_ss())[isTmnlSym_def,isNonTmnlSym_def],
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def,isTmnlSym_def]]
]);

val sym_r2 = store_thm ("sym_r2",
``isTmnlSym e ==> ~(?n.e=NTS n)``,
SRW_TAC [] [] THEN 
Cases_on `e=NTS n` THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
);

val sym_r3 = store_thm ("sym_r3",
``!v.EVERY isTmnlSym v ==> ~(?n s1 s2.(v=s1++[n]++s2) /\ isNonTmnlSym n)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM]THEN
Cases_on `n` THENL[
SRW_TAC [] [isTmnlSym_def, isNonTmnlSym_def],
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,isNonTmnlSym_def] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b,EQ_IMP_THM]]);


val sym_r3b = store_thm ("sym_r3b",
``!v.EVERY isNonTmnlSym v ==> ~(?n s1 s2.(v=s1++[n]++s2) /\ isTmnlSym n)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM]THEN
Cases_on `n` THENL[
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,isNonTmnlSym_def] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b,EQ_IMP_THM],
SRW_TAC [] [isTmnlSym_def, isNonTmnlSym_def]
]);


val sym_r4 = store_thm ("sym_r4",
``!v.EVERY isTmnlSym v ==> ~(?n. MEM n v /\ ~isTmnlSym n)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
Cases_on `n` THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,MEM]
);


val sym_r4b = store_thm ("sym_r4b",
``!v.~EVERY isTmnlSym v ==> (?n. MEM n v /\ isNonTmnlSym n)``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM,EXISTS_MEM] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,MEM,sym_r1b]
);


val sym_r5 = store_thm ("sym_r5",
``!v.~(?n s1 s2.(v=s1++[n]++s2) /\ isNonTmnlSym n) ==> EVERY isTmnlSym v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
SRW_TAC [] [] THEN
Cases_on `e` THENL[
SRW_TAC [] [isTmnlSym_def, isNonTmnlSym_def],
SRW_TAC [] [isTmnlSym_def, isNonTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
METIS_TAC [isNonTmnlSym_def,isTmnlSym_def]]);

val sym_r6 = store_thm ("sym_r6",
``!v.EVERY isTmnlSym v = (~(?n s1 s2.(v=s1++[n]++s2) /\ isNonTmnlSym n))``,
SRW_TAC [] [EQ_IMP_THM] THENL[
METIS_TAC [sym_r3], METIS_TAC [sym_r5]
]
);

val sym_r7 = store_thm ("sym_r7",
``!v.~(EVERY isTmnlSym v) ==> ?n s1 s2.(v=s1++[n]++s2) /\ isNonTmnlSym n``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EXISTS_MEM,rgr_r9eq,sym_r1b] THEN
MAP_EVERY Q.EXISTS_TAC [`e`,`r1`,`r2`] THEN
SRW_TAC [] []
);


val sym_r7b = store_thm ("sym_r7b",
``!v.~(EVERY isNonTmnlSym v) ==> ?n s1 s2.(v=s1++[n]++s2) /\ isTmnlSym n``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EXISTS_MEM,rgr_r9eq,sym_r1b] THEN
MAP_EVERY Q.EXISTS_TAC [`e`,`r1`,`r2`] THEN
METIS_TAC [sym_r1b]
);




(* Regular Expressions *)

(* Definition of a regexp *)

val _ = Hol_datatype `rexp =    EmptyLang   | Atom of symbol   | Union of rexp => rexp   | Conc of rexp => rexp   | Star of rexp`;


(* Concatenation *)
(* conc :: a list set => a list set => a list set 
val conc_def = Define `(conc [] (b::bs) = (b::bs)) /\ (conc (a::as) (b::bs) = (MAP (STRCAT a) (b::bs)) ++ (conc as (b::bs)))`;
*)

val conc_def = Define `conc as bs = {s | ?u v. u IN as /\ v IN bs /\ (s = u ++ v)}`;

(* Union *)
val union_def = Define `union as bs = {s | s IN as \/ s IN bs}`;

(* 
Star
(defined inductively)

star :: a list set => a list set
[] <- star A
a <- A and as <- star A => a++as <- star A
*)


val starn_def = Define `(starn l 0 = {[]})  /\ (starn l n = {s | ?u v. u IN l /\ v IN (starn l (n-1)) /\ (s =  u ++ v)})`;
(* Define A* + prove alternate defn of * *)

val (star_rules, star_ind, star_cases) = Hol_reln`  (star A []) /\   (!s. s IN A ==> star A s) /\  (!s1 s2. s1 IN A /\ s2 IN A ==> star A (s1 ++ s2))`;

(* Language denoted by a rexp *)
(* lang :: a rexp => a list set *)
(* Includes nonterms as well *)
val lang_def = Define `(lang EmptyLang = {}) /\ (lang (Atom tmnl) = {[symToStr tmnl]}) /\ (lang (Union r s) = lang r UNION lang s) /\ (lang (Conc r s) = conc (lang r) (lang s)) /\ (lang (Star r) = star (lang r))`;

val _ = export_theory ();

