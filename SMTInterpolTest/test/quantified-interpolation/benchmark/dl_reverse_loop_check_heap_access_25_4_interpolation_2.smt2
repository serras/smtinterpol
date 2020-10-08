(set-option :print-success false)
(set-option :produce-proofs false)
(set-option :interpolant-check-mode true)
(set-option :produce-interpolants true)
(set-option :print-terms-cse false)

(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/dl/dl_reverse.spl:25:4-20:Possible heap access through null or dangling reference
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Axiom_15$0 () Bool)
(declare-fun Axiom_16$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_5$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun end_2$0 () Loc)
(declare-fun end_init$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_4$0 () Loc)
(declare-fun prv_init$0 () Loc)
(declare-fun sk_?X_15$0 () SetLoc)
(declare-fun sk_?X_16$0 () SetLoc)
(declare-fun sk_?X_17$0 () SetLoc)
(declare-fun start_2$0 () Loc)
(declare-fun start_init$0 () Loc)
(declare-fun tmp_2$0 () Loc)
(declare-fun tmp_4$0 () Loc)
(declare-fun tmp_init$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 end_2$0 ?y ?y)) (= end_2$0 ?y)
            (Btwn$0 next$0 end_2$0 (read$0 next$0 end_2$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 start_init$0 ?y ?y)) (= start_init$0 ?y)
            (Btwn$0 next$0 start_init$0 (read$0 next$0 start_init$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_init$0 ?y ?y)) (= curr_init$0 ?y)
            (Btwn$0 next$0 curr_init$0 (read$0 next$0 curr_init$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 end_2$0) end_2$0))
            (not (Btwn$0 next$0 end_2$0 ?y ?y)) (= end_2$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 start_init$0) start_init$0))
            (not (Btwn$0 next$0 start_init$0 ?y ?y)) (= start_init$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_init$0) curr_init$0))
            (not (Btwn$0 next$0 curr_init$0 ?y ?y)) (= curr_init$0 ?y))) :named P7))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P8))

(assert (! (Btwn$0 next$0 end_2$0 (read$0 next$0 end_2$0) (read$0 next$0 end_2$0)) :named P9))

(assert (! (Btwn$0 next$0 start_init$0 (read$0 next$0 start_init$0)
  (read$0 next$0 start_init$0)) :named P10))

(assert (! (Btwn$0 next$0 curr_init$0 (read$0 next$0 curr_init$0)
  (read$0 next$0 curr_init$0)) :named P11))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_17$0)) (not (in$0 null$0 sk_?X_17$0)))) :named P12))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 null$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) null$0))
        (not (in$0 end_2$0 sk_?X_17$0)) (not (in$0 null$0 sk_?X_17$0)))) :named P13))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 null$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) null$0))
        (not (in$0 start_init$0 sk_?X_17$0)) (not (in$0 null$0 sk_?X_17$0)))) :named P14))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 null$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) null$0))
        (not (in$0 curr_init$0 sk_?X_17$0)) (not (in$0 null$0 sk_?X_17$0)))) :named P15))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_17$0)) (not (in$0 curr_init$0 sk_?X_17$0)))) :named P16))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_init$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) curr_init$0))
        (not (in$0 end_2$0 sk_?X_17$0)) (not (in$0 curr_init$0 sk_?X_17$0)))) :named P17))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_init$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) curr_init$0))
        (not (in$0 start_init$0 sk_?X_17$0))
        (not (in$0 curr_init$0 sk_?X_17$0)))) :named P18))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_init$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) curr_init$0))
        (not (in$0 curr_init$0 sk_?X_17$0))
        (not (in$0 curr_init$0 sk_?X_17$0)))) :named P19))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_init$0) null$0)
        (not (= (read$0 next$0 null$0) prv_init$0))
        (not (in$0 null$0 sk_?X_17$0)) (not (in$0 prv_init$0 sk_?X_17$0)))) :named P20))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_init$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) prv_init$0))
        (not (in$0 end_2$0 sk_?X_17$0)) (not (in$0 prv_init$0 sk_?X_17$0)))) :named P21))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_init$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) prv_init$0))
        (not (in$0 start_init$0 sk_?X_17$0))
        (not (in$0 prv_init$0 sk_?X_17$0)))) :named P22))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_init$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) prv_init$0))
        (not (in$0 curr_init$0 sk_?X_17$0))
        (not (in$0 prv_init$0 sk_?X_17$0)))) :named P23))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_16$0)) (not (in$0 null$0 sk_?X_16$0)))) :named P24))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 null$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) null$0))
        (not (in$0 end_2$0 sk_?X_16$0)) (not (in$0 null$0 sk_?X_16$0)))) :named P25))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 null$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) null$0))
        (not (in$0 start_init$0 sk_?X_16$0)) (not (in$0 null$0 sk_?X_16$0)))) :named P26))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 null$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) null$0))
        (not (in$0 curr_init$0 sk_?X_16$0)) (not (in$0 null$0 sk_?X_16$0)))) :named P27))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_16$0)) (not (in$0 curr_init$0 sk_?X_16$0)))) :named P28))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_init$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) curr_init$0))
        (not (in$0 end_2$0 sk_?X_16$0)) (not (in$0 curr_init$0 sk_?X_16$0)))) :named P29))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_init$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) curr_init$0))
        (not (in$0 start_init$0 sk_?X_16$0))
        (not (in$0 curr_init$0 sk_?X_16$0)))) :named P30))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_init$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) curr_init$0))
        (not (in$0 curr_init$0 sk_?X_16$0))
        (not (in$0 curr_init$0 sk_?X_16$0)))) :named P31))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_init$0) null$0)
        (not (= (read$0 next$0 null$0) prv_init$0))
        (not (in$0 null$0 sk_?X_16$0)) (not (in$0 prv_init$0 sk_?X_16$0)))) :named P32))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_init$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) prv_init$0))
        (not (in$0 end_2$0 sk_?X_16$0)) (not (in$0 prv_init$0 sk_?X_16$0)))) :named P33))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_init$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) prv_init$0))
        (not (in$0 start_init$0 sk_?X_16$0))
        (not (in$0 prv_init$0 sk_?X_16$0)))) :named P34))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_init$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) prv_init$0))
        (not (in$0 curr_init$0 sk_?X_16$0))
        (not (in$0 prv_init$0 sk_?X_16$0)))) :named P35))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P36))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_17$0 sk_?X_16$0))
                 (or (in$0 x sk_?X_17$0) (in$0 x sk_?X_16$0)))
            (and (not (in$0 x sk_?X_17$0)) (not (in$0 x sk_?X_16$0))
                 (not (in$0 x (union$0 sk_?X_17$0 sk_?X_16$0)))))) :named P37))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P38))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_17$0) (in$0 x sk_?X_16$0)
                 (in$0 x (intersection$0 sk_?X_17$0 sk_?X_16$0)))
            (and (or (not (in$0 x sk_?X_17$0)) (not (in$0 x sk_?X_16$0)))
                 (not (in$0 x (intersection$0 sk_?X_17$0 sk_?X_16$0)))))) :named P39))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P40))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P41))

(assert (! (= (read$0 next$0 null$0) null$0) :named P42))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P43))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P44))

(assert (! (or
    (and (Btwn$0 next$0 curr_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 end_init$0) null$0)
                  (= (read$0 prev$0 curr_init$0) prv_init$0)
                  (in$0 end_init$0 sk_?X_17$0))
             (and (= curr_init$0 null$0) (= prv_init$0 end_init$0)))
         Axiom_15$0)
    (not
         (dlseg_struct$0 sk_?X_17$0 next$0 prev$0 curr_init$0 prv_init$0
           null$0 end_init$0))) :named P45))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P46))

(assert (! (= curr_5$0 (read$0 next$0 curr_4$0)) :named P47))

(assert (! (= prv_4$0 prv_init$0) :named P48))

(assert (! (= tmp_2$0 tmp_init$0) :named P49))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P50))

(assert (! (= sk_?X_15$0 (union$0 sk_?X_17$0 sk_?X_16$0)) :named P51))

(assert (! (= sk_?X_16$0
  (dlseg_domain$0 next$0 prev$0 prv_init$0 curr_init$0 null$0 start_init$0)) :named P52))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P53))

(assert (! (dlseg_struct$0 sk_?X_17$0 next$0 prev$0 curr_init$0 prv_init$0 null$0
  end_init$0) :named P54))

(assert (! (not (in$0 null$0 Alloc$0)) :named P55))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0
                     null$0 end_init$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0
                          null$0 end_init$0)))))) :named P56))

(assert (! (or
    (and (Btwn$0 next$0 prv_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 start_init$0) null$0)
                  (= (read$0 prev$0 prv_init$0) curr_init$0)
                  (in$0 start_init$0 sk_?X_16$0))
             (and (= curr_init$0 start_init$0) (= prv_init$0 null$0)))
         Axiom_16$0)
    (not
         (dlseg_struct$0 sk_?X_16$0 next$0 prev$0 prv_init$0 curr_init$0
           null$0 start_init$0))) :named P57))

(assert (! (= curr_4$0 curr_init$0) :named P58))

(assert (! (= end_2$0 end_init$0) :named P59))

(assert (! (= start_2$0 start_init$0) :named P60))

(assert (! (= tmp_4$0 curr_4$0) :named P61))

(assert (! (= emptyset$0 (intersection$0 sk_?X_17$0 sk_?X_16$0)) :named P62))

(assert (! (= sk_?X_15$0 FP$0) :named P63))

(assert (! (= sk_?X_17$0
  (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0 null$0 end_init$0)) :named P64))

(assert (! (dlseg_struct$0 sk_?X_16$0 next$0 prev$0 prv_init$0 curr_init$0 null$0
  start_init$0) :named P65))

(assert (! (not (= curr_4$0 null$0)) :named P66))

(assert (! (not (in$0 tmp_4$0 FP$0)) :named P67))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 prv_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 prv_init$0 curr_init$0
                     null$0 start_init$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 prv_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 prv_init$0 curr_init$0
                          null$0 start_init$0)))))) :named P68))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P69))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P70))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P71))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P72))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P73))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P74))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P75))

(check-sat)

(get-interpolants (and P50 P11 P43 P39 P4 P29 P52 P48 P1 P63 P15 P14 P72 P68 P70 P22 P42 P20 P6 P73 P17 P31 P58 P24 P28 P3 P23 P65 P46 P66 P56 P32 P19 P7 P5 P12 P57 P37) (and P34 P71 P54 P16 P59 P33 P38 P26 P9 P25 P61 P47 P21 P35 P30 P8 P62 P55 P53 P44 P75 P49 P74 P0 P27 P18 P13 P60 P40 P41 P69 P64 P36 P2 P10 P67 P45 P51))

(exit)