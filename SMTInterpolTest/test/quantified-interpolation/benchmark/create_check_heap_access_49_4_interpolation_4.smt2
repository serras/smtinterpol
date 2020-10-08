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
  tests/spl/union_find.spl:49:4-19:Possible heap access through null or dangling reference
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_1$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun n_3$0 () Loc)
(declare-fun tmp_1$0 () Loc)

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P0))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 Alloc$0 (setenum$0 tmp_1$0)))
                 (or (in$0 x Alloc$0) (in$0 x (setenum$0 tmp_1$0))))
            (and (not (in$0 x Alloc$0)) (not (in$0 x (setenum$0 tmp_1$0)))
                 (not (in$0 x (union$0 Alloc$0 (setenum$0 tmp_1$0))))))) :named P1))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 (setenum$0 tmp_1$0)))
                 (or (in$0 x FP$0) (in$0 x (setenum$0 tmp_1$0))))
            (and (not (in$0 x FP$0)) (not (in$0 x (setenum$0 tmp_1$0)))
                 (not (in$0 x (union$0 FP$0 (setenum$0 tmp_1$0))))))) :named P2))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P3))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P4))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P5))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P6))

(assert (! (= emptyset$0 FP$0) :named P7))

(assert (! (= FP_1$0 (union$0 FP$0 (setenum$0 tmp_1$0))) :named P8))

(assert (! (= n_3$0 tmp_1$0) :named P9))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P10))

(assert (! (not (in$0 null$0 Alloc$0)) :named P11))

(assert (! (not (in$0 tmp_1$0 Alloc$0)) :named P12))

(assert (! (= Alloc_1$0 (union$0 Alloc$0 (setenum$0 tmp_1$0))) :named P13))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P14))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P15))

(assert (! (not (= tmp_1$0 null$0)) :named P16))

(assert (! (not (in$0 n_3$0 FP_1$0)) :named P17))

(check-sat)

(get-interpolants (and P3 P12 P5 P2 P15 P0 P13 P14 P8) (and P7 P10 P4 P6 P17 P9 P11 P16 P1))

(exit)