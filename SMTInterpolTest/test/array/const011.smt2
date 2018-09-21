(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_AX)
(declare-sort U 0)
(declare-fun v1 () U)
(declare-fun v2 () U)
(define-fun constU ((v U)) (Array U U) ((as const (Array U U)) v))

(assert (not (= (constU v1) (constU v2))))
(check-sat)
(get-model)
(get-value ((@diff (constU v1) (constU v2))
	(constU v1)
	(constU v2)
	(@diff (constU v1) (store (constU v2) (@diff (constU v1) (constU v2)) v1))
	(select (constU v1) 
	        (@diff (constU v1) (store (constU v2) (@diff (constU v1) (constU v2)) v1)))
	(select (store (constU v2) (@diff (constU v1) (constU v2)) v1) 
	        (@diff (constU v1) (store (constU v2) (@diff (constU v1) (constU v2)) v1)))
	(@diff (constU v1) (store (store (constU v2) (@diff (constU v1) (constU v2)) v1)
	                          (@diff (constU v1) (store (constU v2) (@diff (constU v1) (constU v2)) v1)) v1))))
(exit)

