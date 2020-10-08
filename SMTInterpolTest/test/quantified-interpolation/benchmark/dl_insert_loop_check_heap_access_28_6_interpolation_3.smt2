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
  tests/spl/dl/dl_insert.spl:28:6-24:Possible heap access through null or dangling reference
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
(declare-fun Axiom_32$0 () Bool)
(declare-fun Axiom_33$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun c_6$0 () Loc)
(declare-fun c_init$0 () Loc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun d_5$0 () Loc)
(declare-fun d_init$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun nondet_3$0 () Bool)
(declare-fun nondet_init$0 () Bool)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_4$0 () Loc)
(declare-fun prv_5$0 () Loc)
(declare-fun prv_init$0 () Loc)
(declare-fun sk_?X_91$0 () SetLoc)
(declare-fun sk_?X_92$0 () SetLoc)
(declare-fun sk_?X_93$0 () SetLoc)
(declare-fun sk_?X_94$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_init$0 ?y ?y)) (= curr_init$0 ?y)
            (Btwn$0 next$0 curr_init$0 (read$0 next$0 curr_init$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 d_init$0 ?y ?y)) (= d_init$0 ?y)
            (Btwn$0 next$0 d_init$0 (read$0 next$0 d_init$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y)
            (Btwn$0 next$0 prv_init$0 (read$0 next$0 prv_init$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_init$0) curr_init$0))
            (not (Btwn$0 next$0 curr_init$0 ?y ?y)) (= curr_init$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 d_init$0) d_init$0))
            (not (Btwn$0 next$0 d_init$0 ?y ?y)) (= d_init$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_init$0) prv_init$0))
            (not (Btwn$0 next$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y))) :named P7))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P8))

(assert (! (Btwn$0 next$0 curr_init$0 (read$0 next$0 curr_init$0)
  (read$0 next$0 curr_init$0)) :named P9))

(assert (! (Btwn$0 next$0 d_init$0 (read$0 next$0 d_init$0) (read$0 next$0 d_init$0)) :named P10))

(assert (! (Btwn$0 next$0 prv_init$0 (read$0 next$0 prv_init$0)
  (read$0 next$0 prv_init$0)) :named P11))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_92$0)) (not (in$0 null$0 sk_?X_92$0)))) :named P12))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 null$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) null$0))
        (not (in$0 curr_init$0 sk_?X_92$0)) (not (in$0 null$0 sk_?X_92$0)))) :named P13))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 null$0) d_init$0)
        (not (= (read$0 next$0 d_init$0) null$0))
        (not (in$0 d_init$0 sk_?X_92$0)) (not (in$0 null$0 sk_?X_92$0)))) :named P14))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 null$0) prv_init$0)
        (not (= (read$0 next$0 prv_init$0) null$0))
        (not (in$0 prv_init$0 sk_?X_92$0)) (not (in$0 null$0 sk_?X_92$0)))) :named P15))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 c_6$0) null$0)
        (not (= (read$0 next$0 null$0) c_6$0)) (not (in$0 null$0 sk_?X_92$0))
        (not (in$0 c_6$0 sk_?X_92$0)))) :named P16))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 c_6$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) c_6$0))
        (not (in$0 curr_init$0 sk_?X_92$0)) (not (in$0 c_6$0 sk_?X_92$0)))) :named P17))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 c_6$0) d_init$0)
        (not (= (read$0 next$0 d_init$0) c_6$0))
        (not (in$0 d_init$0 sk_?X_92$0)) (not (in$0 c_6$0 sk_?X_92$0)))) :named P18))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 c_6$0) prv_init$0)
        (not (= (read$0 next$0 prv_init$0) c_6$0))
        (not (in$0 prv_init$0 sk_?X_92$0)) (not (in$0 c_6$0 sk_?X_92$0)))) :named P19))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_92$0)) (not (in$0 curr_init$0 sk_?X_92$0)))) :named P20))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 curr_init$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) curr_init$0))
        (not (in$0 curr_init$0 sk_?X_92$0))
        (not (in$0 curr_init$0 sk_?X_92$0)))) :named P21))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 curr_init$0) d_init$0)
        (not (= (read$0 next$0 d_init$0) curr_init$0))
        (not (in$0 d_init$0 sk_?X_92$0)) (not (in$0 curr_init$0 sk_?X_92$0)))) :named P22))

(assert (! (or (not Axiom_33$0)
    (or (= (read$0 prev$0 curr_init$0) prv_init$0)
        (not (= (read$0 next$0 prv_init$0) curr_init$0))
        (not (in$0 prv_init$0 sk_?X_92$0))
        (not (in$0 curr_init$0 sk_?X_92$0)))) :named P23))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_94$0)) (not (in$0 null$0 sk_?X_94$0)))) :named P24))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 null$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) null$0))
        (not (in$0 curr_init$0 sk_?X_94$0)) (not (in$0 null$0 sk_?X_94$0)))) :named P25))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 null$0) d_init$0)
        (not (= (read$0 next$0 d_init$0) null$0))
        (not (in$0 d_init$0 sk_?X_94$0)) (not (in$0 null$0 sk_?X_94$0)))) :named P26))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 null$0) prv_init$0)
        (not (= (read$0 next$0 prv_init$0) null$0))
        (not (in$0 prv_init$0 sk_?X_94$0)) (not (in$0 null$0 sk_?X_94$0)))) :named P27))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 c_6$0) null$0)
        (not (= (read$0 next$0 null$0) c_6$0)) (not (in$0 null$0 sk_?X_94$0))
        (not (in$0 c_6$0 sk_?X_94$0)))) :named P28))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 c_6$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) c_6$0))
        (not (in$0 curr_init$0 sk_?X_94$0)) (not (in$0 c_6$0 sk_?X_94$0)))) :named P29))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 c_6$0) d_init$0)
        (not (= (read$0 next$0 d_init$0) c_6$0))
        (not (in$0 d_init$0 sk_?X_94$0)) (not (in$0 c_6$0 sk_?X_94$0)))) :named P30))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 c_6$0) prv_init$0)
        (not (= (read$0 next$0 prv_init$0) c_6$0))
        (not (in$0 prv_init$0 sk_?X_94$0)) (not (in$0 c_6$0 sk_?X_94$0)))) :named P31))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_94$0)) (not (in$0 curr_init$0 sk_?X_94$0)))) :named P32))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 curr_init$0) curr_init$0)
        (not (= (read$0 next$0 curr_init$0) curr_init$0))
        (not (in$0 curr_init$0 sk_?X_94$0))
        (not (in$0 curr_init$0 sk_?X_94$0)))) :named P33))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 curr_init$0) d_init$0)
        (not (= (read$0 next$0 d_init$0) curr_init$0))
        (not (in$0 d_init$0 sk_?X_94$0)) (not (in$0 curr_init$0 sk_?X_94$0)))) :named P34))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 curr_init$0) prv_init$0)
        (not (= (read$0 next$0 prv_init$0) curr_init$0))
        (not (in$0 prv_init$0 sk_?X_94$0))
        (not (in$0 curr_init$0 sk_?X_94$0)))) :named P35))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P36))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_93$0 sk_?X_92$0))
                 (or (in$0 x sk_?X_93$0) (in$0 x sk_?X_92$0)))
            (and (not (in$0 x sk_?X_93$0)) (not (in$0 x sk_?X_92$0))
                 (not (in$0 x (union$0 sk_?X_93$0 sk_?X_92$0)))))) :named P37))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P38))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_93$0) (in$0 x sk_?X_92$0)
                 (in$0 x (intersection$0 sk_?X_93$0 sk_?X_92$0)))
            (and (or (not (in$0 x sk_?X_93$0)) (not (in$0 x sk_?X_92$0)))
                 (not (in$0 x (intersection$0 sk_?X_93$0 sk_?X_92$0)))))) :named P39))

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
             (and (= (read$0 next$0 d_init$0) null$0)
                  (= (read$0 prev$0 curr_init$0) prv_init$0)
                  (in$0 d_init$0 sk_?X_92$0))
             (and (= curr_init$0 null$0) (= prv_init$0 d_init$0)))
         Axiom_33$0)
    (not
         (dlseg_struct$0 sk_?X_92$0 next$0 prev$0 curr_init$0 prv_init$0
           null$0 d_init$0))) :named P45))

(assert (! (= c_6$0 c_init$0) :named P46))

(assert (! (= d_5$0 d_init$0) :named P47))

(assert (! (= prv_4$0 prv_init$0) :named P48))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P49))

(assert (! (= emptyset$0 emptyset$0) :named P50))

(assert (! (= sk_?X_91$0 (union$0 sk_?X_93$0 sk_?X_92$0)) :named P51))

(assert (! (= sk_?X_92$0
  (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0 null$0 d_init$0)) :named P52))

(assert (! (= sk_?X_94$0
  (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 curr_init$0 prv_init$0)) :named P53))

(assert (! (dlseg_struct$0 sk_?X_92$0 next$0 prev$0 curr_init$0 prv_init$0 null$0
  d_init$0) :named P54))

(assert (! (not (= curr_init$0 null$0)) :named P55))

(assert (! (not (in$0 null$0 Alloc$0)) :named P56))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_init$0 l1 curr_init$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 curr_init$0
                     prv_init$0))
                 (not (= l1 curr_init$0)))
            (and
                 (or (= l1 curr_init$0)
                     (not (Btwn$0 next$0 c_init$0 l1 curr_init$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_init$0 null$0
                          curr_init$0 prv_init$0)))))) :named P57))

(assert (! (or
    (and (Btwn$0 next$0 c_init$0 curr_init$0 curr_init$0)
         (or (and (= null$0 prv_init$0) (= c_init$0 curr_init$0))
             (and (= (read$0 next$0 prv_init$0) curr_init$0)
                  (= (read$0 prev$0 c_init$0) null$0)
                  (in$0 prv_init$0 sk_?X_94$0)))
         Axiom_32$0)
    (not
         (dlseg_struct$0 sk_?X_94$0 next$0 prev$0 c_init$0 null$0 curr_init$0
           prv_init$0))) :named P58))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P59))

(assert (! (= curr_4$0 curr_init$0) :named P60))

(assert (! (= nondet_3$0 nondet_init$0) :named P61))

(assert (! (= prv_5$0 curr_4$0) :named P62))

(assert (! nondet_3$0 :named P63))

(assert (! (= emptyset$0 (intersection$0 sk_?X_93$0 sk_?X_92$0)) :named P64))

(assert (! (= sk_?X_91$0 FP$0) :named P65))

(assert (! (= sk_?X_93$0 sk_?X_94$0) :named P66))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P67))

(assert (! (dlseg_struct$0 sk_?X_94$0 next$0 prev$0 c_init$0 null$0 curr_init$0
  prv_init$0) :named P68))

(assert (! (not (= (read$0 next$0 curr_4$0) null$0)) :named P69))

(assert (! (not (in$0 curr_4$0 FP$0)) :named P70))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0
                     null$0 d_init$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0
                          null$0 d_init$0)))))) :named P71))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P72))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P73))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P74))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P75))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P76))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P77))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P78))

(check-sat)

(get-interpolants (and P11 P19 P26 P77 P74 P6 P30 P46 P7 P60 P9 P17 P71 P1 P2 P48 P34 P47 P58 P35 P61 P16 P57 P12 P50 P62 P73 P72 P65 P78 P28 P56 P76 P20 P15 P32 P31 P64 P10 P14) (and P54 P8 P53 P39 P27 P49 P68 P36 P24 P29 P22 P41 P33 P44 P40 P66 P45 P21 P3 P55 P42 P70 P59 P13 P63 P43 P0 P51 P67 P23 P5 P37 P4 P18 P69 P38 P52 P25 P75))

(exit)