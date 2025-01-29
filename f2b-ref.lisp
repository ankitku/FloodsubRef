(in-package "ACL2S")
(include-book "f2b-commit")

;; -------------------------------------------------------
;; Proof of refinement : FloodNet refines BroadcastNet
;; ------------------------------------------------------- 

(defdata bn (cons 'b s-bn))
(defdata fn (cons 'f s-fn))

(defdata borf (v bn fn))

(property bn->borf (x :bn)
  (borfp x))

(property fn->borf (x :fn)
  (borfp x))

(definec rel-B (x y :borf) :boolean
  (cond
   ((^ (fnp x) (fnp y)) (== (f2b (cdr x))
                            (f2b (cdr y))))
   ((^ (fnp x) (bnp y)) (== (f2b (cdr x))
                            (cdr y)))
   ((^ (fnp y) (bnp x)) (== (f2b (cdr y))
                            (cdr x)))
   (t (== (cdr x)
          (cdr y)))))

(property b-fnbn (s :fn w :bn)
  (== (rel-B s w)
      (== (f2b (cdr s)) (cdr w))))

(property b-fnfn (s w :fn)
  (== (rel-B s w)
      (== (f2b (cdr s))
          (f2b (cdr w)))))

(property b-bnfn (s :bn w :fn)
  (== (rel-B s w)
      (== (f2b (cdr w)) (cdr s))))

(property b-bnbn (s w :bn)
  (== (rel-B s w)
      (== s w)))


(propertyd rel-B-reflexive (x :borf)
  (rel-B x x))
  
(propertyd rel-B-symmetric (x y :borf)
  (== (rel-B x y)
      (rel-B y x)))

(propertyd rel-B-transitive (x y z :borf)
  :h (^ (rel-B x y)
        (rel-B y z))
  (rel-B x z))

(in-theory (disable borfp
                    rel-B
                    rel-B-definition-rule))


;; Refinement Map
(definec f2b-ref (s :fn) :bn
  (cons 'b
        (f2b (cdr s))))


;; WEB 1
(property b-maps-f2b (s :fn)
  (rel-B s (f2b-ref s)))


(encapsulate ()
  ;; Find forwarding peer that will forward m in s
  (property prop=in-m-cdr-pending (s :s-fn m :mssg)
    :h (^ (in m (union-set (mget :pending (cdr (car s)))
                           (fn-pending-mssgs (cdr s))))
          (not (in m (mget :pending (cdr (car s))))))
    (in m (fn-pending-mssgs (cdr s)))
    :hints (("Goal" :use ((:instance in-union2
                                     (x (mget :pending (cdr (car s))))
                                     (y (fn-pending-mssgs (cdr s))))))))
  (local 
   (property h0 (s :s-fn m :mssg)
     :h (in m (isort-set (mget :pending (cdr (car s)))))
     (in m (mget :pending (cdr (car s))))))

  (local
   (in-theory (enable fn-pending-mssgs
                      acl2::maximal-records-theory)))
  
  (definec find-forwarder (s :s-fn m :mssg) :peer
    :ic (in m (fn-pending-mssgs s))
    :oc (^ (mget (find-forwarder s m) s)
           (in m (mget :pending (mget (find-forwarder s m) s)))
           (! (new-fn-mssgp m s)))
    :function-contract-hints (("Goal" :induct (find-forwarder s m)))
    (match s
      (((p . &)) p)
      (((p . pst) . rst)
       (if (in m (mget :pending pst))
           p
         (find-forwarder rst m))))))




(definecd rel-skip-bn (s u :bn) :bool
  (== u s))

(definecd rel-broadcast-bn (m :mssg s u :bn) :bool
  (^ (new-bn-mssgp m (cdr s))
     (mget (mget :or m) (cdr s))
     (in (mget :tp m)
         (mget :pubs (mget  (mget :or m) (cdr s))))
     (== u (cons 'b (broadcast m (cdr s))))))

(definecd rel-subscribe-bn (p :peer topics :lot s u :bn) :bool
  (^ (mget p (cdr s))
     (== u (cons 'b (subscribe-bn p topics (cdr s))))))

(definecd rel-unsubscribe-bn (p :peer topics :lot s u :bn) :bool
  (^ (mget p (cdr s))
     (== u (cons 'b (unsubscribe-bn p topics (cdr s))))))

(definecd rel-leave-bn (p :peer s u :bn) :bool
  (^ (mget p (cdr s))
     (== u (cons 'b (leave-bn p (cdr s))))))

(definecd rel-join-bn (p :peer pubs subs :lot s u :bn) :bool
  (^ (! (mget p (cdr s)))
     (== u (cons 'b (join-bn p pubs subs (cdr s))))))

(definec rel-step-bn (p :peer pubs subs topics :lot m :mssg s u :bn) :bool
  (v (rel-skip-bn s u)
     (rel-broadcast-bn m s u)
     (rel-subscribe-bn p topics s u)
     (rel-unsubscribe-bn p topics s u)
     (rel-leave-bn p s u)
     (rel-join-bn p pubs subs s u)))




(definecd rel-skip-fn (s u :fn) :bool
  (== u s))

(definecd rel-produce-fn (m :mssg s u :fn) :bool
  (^ (new-fn-mssgp m (cdr s))
     (mget (mget :or m) (cdr s))
     (in (mget :tp m)
         (mget :pubs (mget  (mget :or m) (cdr s))))
     (== u (cons 'f (produce-fn m (cdr s))))))

(definecd rel-forward-fn1 (m :mssg s u :fn) :bool
  (^ (in m (fn-pending-mssgs (cdr s)))
     (! (in m (mget :seen (mget (find-forwarder (cdr s) m) (cdr s)))))        ;; Invariant
     (!= (fn-pending-mssgs (forward-fn (find-forwarder (cdr s) m) m (cdr s))) ;; CASE
         (fn-pending-mssgs (cdr s)))
     (^ (mget (mget :or m) (cdr s))   ;; CONDITION 1. origin still exists
        (in (mget :tp m)                           ;; while message is pending
            (mget :pubs (mget  (mget :or m) (cdr s)))))
     (== u (cons 'f (forward-fn (find-forwarder (cdr s) m) m (cdr s))))))

(definecd rel-forward-fn2 (m :mssg s u :fn) :bool
  (^ (in m (fn-pending-mssgs (cdr s)))
     (! (in m (mget :seen (mget (find-forwarder (cdr s) m) (cdr s)))))        ;; Invariant
     (== (fn-pending-mssgs (forward-fn (find-forwarder (cdr s) m) m (cdr s))) ;;CASE
         (fn-pending-mssgs (cdr s)))
     (== u (cons 'f (forward-fn (find-forwarder (cdr s) m) m (cdr s))))))
     
(definecd rel-subscribe-fn (p :peer topics :lot s u :fn) :bool
  (^ (mget p (cdr s))
     (== u (cons 'f (subscribe-fn p topics (cdr s))))))

(definecd rel-unsubscribe-fn (p :peer topics :lot s u :fn) :bool
  (^ (mget p (cdr s))
     (== u (cons 'f (unsubscribe-fn p topics (cdr s))))))

(definecd rel-leave-fn (p :peer s u :fn) :bool
  (^ (mget p (cdr s))
     (== (fn-pending-mssgs (leave-fn p (cdr s)))
         (fn-pending-mssgs (cdr s)))
     (== u (cons 'f (leave-fn p (cdr s))))))

(definecd rel-join-fn (p :peer pubs subs :lot nbrs :lop s u :fn) :bool
  (^ (! (mget p (cdr s)))
     (! (in p nbrs))   ;; Condition for join
     (== u (cons 'f (join-fn p pubs subs nbrs (cdr s))))))

(definec rel-step-fn (p :peer pubs subs topics :lot nbrs :lop m :mssg s u :fn) :bool
  (v (rel-skip-fn s u)
     (rel-produce-fn m s u)
     (rel-forward-fn1 m s u)
     (rel-forward-fn2 m s u)
     (rel-subscribe-fn p topics s u)
     (rel-unsubscribe-fn p topics s u)
     (rel-leave-fn p s u)
     (rel-join-fn p pubs subs nbrs s u)))

(definec rel-> (p :peer pubs subs topics :lot nbrs :lop m :mssg s u :borf) :bool
  (v (^ (fnp s)
        (fnp u)
        (rel-step-fn p pubs subs topics nbrs m s u))
     (^ (bnp s)
        (bnp u)
        (rel-step-bn p pubs subs topics m s u))))

(property rel->fnfn (p :peer pubs subs topics :lot
                       nbrs :lop m :mssg s u :fn)
  (== (rel-> p pubs subs topics nbrs m s u)
      (rel-step-fn p pubs subs topics nbrs m s u)))

(property rel->bnbn (p :peer pubs subs topics :lot
                       nbrs :lop m :mssg s u :bn ) 
  (== (rel-> p pubs subs topics nbrs m s u)
      (rel-step-bn p pubs subs topics m s u)))


;; WEB 3 provables
(propertyd web3-0 (s w u v :bn p :peer
                    pubs subs topics :lot nbrs :lop m :mssg)
 :h (^ (rel-B s w)
       (rel-> p pubs subs topics nbrs m s u)
       ;; exists v
       (== v u))
 (^ (rel-> p pubs subs topics nbrs m w v)
    (rel-B u v)))




(property web3-urel->v1-help1 (s u :fn)
  :h (rel-skip-fn s u)
  (rel-skip-bn (f2b-ref s) (f2b-ref u))
  :hints (("Goal" :in-theory (enable rel-skip-fn
                                     rel-skip-bn))))

(property web3-urel->v1-help2 (s u :fn p :peer topics :lot)
  :h (rel-subscribe-fn p topics s u)
  (rel-subscribe-bn p topics (f2b-ref s) (f2b-ref u))
  :hints (("Goal" :in-theory (enable rel-subscribe-fn
                                     rel-subscribe-bn))))

(property web3-urel->v1-help3 (s u :fn p :peer topics :lot)
  :h (rel-unsubscribe-fn p topics s u)
  (rel-unsubscribe-bn p topics (f2b-ref s) (f2b-ref u))
  :hints (("Goal" :in-theory (enable rel-unsubscribe-fn
                                     rel-unsubscribe-bn))))

(property web3-urel->v1-help4 (s u :fn p :peer pubs subs topics :lot
                         nbrs :lop m :mssg)
  :h (rel-join-fn p pubs subs nbrs s u)
  (rel-join-bn p pubs subs (f2b-ref s) (f2b-ref u))
  :hints (("Goal" :in-theory (enable rel-join-fn
                                     rel-join-bn)
           :use ((:instance prop=f2b-join-fn (s (cdr s)))))))

(property web3-urel->v1-help5 (s u :fn p :peer)
  :check-contracts? nil
  :h (rel-leave-fn p s u)
  (rel-leave-bn p (f2b-ref s) (f2b-ref u))
  :hints (("Goal" :in-theory (enable rel-leave-fn
                                     rel-leave-bn))))

(property web3-urel->v1-help6 (s u :fn m :mssg)
  :h (rel-produce-fn m s u)
  (rel-skip-bn (f2b-ref s) (f2b-ref u))
  :hints (("Goal" :in-theory (enable rel-produce-fn
                                     rel-skip-bn))))

(property web3-urel->v1-help7 (s u :fn m :mssg)
  :check-contracts? nil
  :h (rel-forward-fn2 m s u)
  (rel-skip-bn (f2b-ref s) (f2b-ref u))
  :hints (("Goal" :in-theory (enable rel-forward-fn2
                                     rel-skip-bn))))

(property web3-urel->v1-help8 (s u :fn m :mssg)
  :check-contracts? nil
  :h (^ (rel-forward-fn1 m s u)

        ;; CONDITION 1 :
        (=> (^ (in m (fn-pending-mssgs (cdr s)))
               (! (in m (fn-pending-mssgs (forward-fn (find-forwarder (cdr s) m) m (cdr s))))))
            (== (f2b (forward-fn (find-forwarder (cdr s) m) m (cdr s)))
                (broadcast m (f2b (cdr s))))))
  (rel-broadcast-bn m (f2b-ref s) (cons 'b (broadcast m (f2b (cdr s)))))
  :hints (("Goal" :in-theory (enable rel-forward-fn1
                                     rel-broadcast-bn))))





(definec exists-v1 (s u :fn p :peer pubs subs topics :lot
                      nbrs :lop m :mssg) :bn
                      :body-contracts-hints (("Goal" :use (prop=f2b-broadcast-hyps)
                                              :in-theory (enable rel-forward-fn1)))
  (cond
   ((rel-forward-fn1 m s u) (cons 'b (broadcast m (f2b (cdr s)))))
   ((rel-subscribe-fn p topics s u) (f2b-ref u))
   ((rel-unsubscribe-fn p topics s u) (f2b-ref u))
   ((rel-join-fn p pubs subs nbrs s u) (f2b-ref u))
   ((rel-leave-fn p s u) (f2b-ref u))
   (t (f2b-ref s))))



(property web3-uBv1-help (s u :fn p :peer pubs subs topics :lot
                             nbrs :lop m :mssg)
  :check-contracts? nil
  :h (^ (rel-step-fn p pubs subs topics nbrs m s u)
        
        ;; CONDITION 1 :
        (=> (^ (in m (fn-pending-mssgs (cdr s)))
               (! (in m (fn-pending-mssgs (forward-fn (find-forwarder (cdr s) m) m (cdr s))))))
            (== (f2b (forward-fn (find-forwarder (cdr s) m) m (cdr s)))
                (broadcast m (f2b (cdr s))))))
  (rel-b u (exists-v1 s u p pubs subs topics nbrs m))
  :instructions
  (:pro (:rewrite b-fnbn)
        (:casesplit (rel-forward-fn1 m s u)) :s
        
        (= u (cons 'f (forward-fn (find-forwarder (cdr s) m) m (cdr s)))
           :hints (("Goal" :in-theory (enable rel-forward-fn1))))
        :s
        
        (:claim  (^ (in m (fn-pending-mssgs (cdr s)))
                    (mget (find-forwarder (cdr s) m) (cdr s))
                    (!= (fn-pending-mssgs (forward-fn (find-forwarder (cdr s) m) m (cdr s)))
                        (fn-pending-mssgs (cdr s))))
                 :hints (("Goal" :in-theory (enable rel-forward-fn1))))
        
        (:claim (! (in m (fn-pending-mssgs (forward-fn (find-forwarder (cdr s) m)
                                                       m (cdr s)))))
                :hints (("Goal" :use ((:instance
                                       prop=fn-pending-mssgs-forward-fn
                                       (p (find-forwarder (cdr s) m))
                                       (s (cdr s)))))))
        :prove :s
        (:casesplit (rel-subscribe-fn p topics s u)) :s
        (:casesplit (rel-unsubscribe-fn p topics s u)) :s
        (:casesplit (rel-join-fn p pubs subs nbrs s u)) :s
        (:casesplit (rel-leave-fn p s u)) :s
        (:casesplit (rel-skip-fn s u)) :s
        (:prove :hints (("Goal" :in-theory (enable rel-skip-bn rel-skip-fn)))) :s
        (:casesplit (rel-produce-fn m s u))
        (:prove :hints (("Goal" :in-theory (enable rel-produce-fn))))
        (:claim (rel-forward-fn2 m s u))
        (:prove :hints (("Goal" :in-theory (enable rel-forward-fn2))))
        :prove
        :prove))


(property web3-urel->v1-help (s u :fn p :peer pubs subs topics :lot
                            nbrs :lop m :mssg)
  :check-contracts? nil
  :h (^ (rel-step-fn p pubs subs topics nbrs m s u)

        ;; CONDITION 1 :
        (=> (^ (in m (fn-pending-mssgs (cdr s)))
               (! (in m (fn-pending-mssgs (forward-fn (find-forwarder (cdr s) m) m (cdr s))))))
            (== (f2b (forward-fn (find-forwarder (cdr s) m) m (cdr s)))
                (broadcast m (f2b (cdr s))))))
  (rel-step-bn p pubs subs topics m (f2b-ref s)
               (exists-v1 s u p pubs subs topics nbrs m))

  :instructions
  (:pro (:casesplit (rel-forward-fn1 m s u)) 
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help8)))))
        (:casesplit (rel-forward-fn2 m s u)) 
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help7))
                         :in-theory (enable rel-skip-bn))))
        (:casesplit (rel-subscribe-fn p topics s u)) 
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help2)))))
        (:casesplit (rel-unsubscribe-fn p topics s u)) 
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help3)))))
        (:casesplit (rel-join-fn p pubs subs nbrs s u)) 
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help4)))))
        (:casesplit (rel-leave-fn p s u))
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help5)))))
        (:casesplit (rel-skip-fn s u))
        (:prove :hints (("Goal" :in-theory (enable rel-skip-bn))))
        (:casesplit (rel-produce-fn m s u))
        (:prove :hints (("Goal" :in-theory (enable rel-skip-bn))))
        :bash))



(propertyd web3-1 (s u :fn w :bn p :peer pubs subs topics :lot
                     nbrs :lop m :mssg)
  :check-contracts? nil
  :h (^ (rel-B s w)
        (rel-> p pubs subs topics nbrs m s u)
        
        ;; CONDITION 1 :
        (=> (^ (in m (fn-pending-mssgs (cdr s)))
               (! (in m (fn-pending-mssgs (forward-fn (find-forwarder (cdr s) m) m (cdr s))))))
            (== (f2b (forward-fn (find-forwarder (cdr s) m) m (cdr s)))
                (broadcast m (f2b (cdr s))))))
  
     (^ (rel-> p pubs subs topics nbrs m w
               (exists-v1 s u p pubs subs topics nbrs m))
        (rel-B u
               (exists-v1 s u p pubs subs topics nbrs m)))
  :instructions
  (:pro
   (= w (f2b-ref s))
   (:claim (rel-step-fn p pubs subs topics nbrs m s u))
   (= (rel-> p pubs subs topics nbrs m (f2b-ref s)
             (exists-v1 s u p pubs subs topics nbrs m))
      (rel-step-bn p pubs subs topics m (f2b-ref s)
                   (exists-v1 s u p pubs subs topics nbrs m))
      :hints (("Goal" :in-theory (disable exists-v1-definition-rule))))
   (:claim (rel-step-bn p pubs subs topics m (f2b-ref s)
                        (exists-v1 s u p pubs subs topics nbrs m))
           :hints (("Goal" :use ((:instance web3-urel->v1-help)))))
   (:claim (rel-B u (exists-v1 s u p pubs subs topics nbrs m))
           :hints (("Goal" :use ((:instance web3-uBv1-help)))))
           
   :s))



;;==================================================================  
;; WEB 3-2 provables

(definec exists-v2 (u :bn w :fn p :peer pubs subs topics :lot nbrs :lop m :mssg) :fn
  :ic (! (in p nbrs))
  :body-contracts-hints (("Goal" :use ((:instance prop=f2b-produce-hyps
                                                  (s (cdr w)))
                                       (:instance prop=not-mget=not-mget-f2b
                                                  (s (cdr w))))
                          :in-theory (enable rel-skip-bn
                                             rel-broadcast-bn
                                             rel-subscribe-bn
                                             rel-unsubscribe-bn
                                             rel-join-bn
                                             rel-leave-bn)))
  (cons 'f
        (cond
         ((rel-skip-bn (f2b-ref w) u) (cdr w))
         ((^ (rel-broadcast-bn m (f2b-ref w) u)
             (in m (fn-pending-mssgs (cdr w))))
          (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
         
         ((^ (rel-broadcast-bn m (f2b-ref w) u)
             (! (in m (fn-pending-mssgs (cdr w)))))
          (produce-fn m (cdr w)))

         ((rel-subscribe-bn p topics (f2b-ref w) u)
          (subscribe-fn p topics (cdr w)))

         ((rel-unsubscribe-bn p topics (f2b-ref w) u)
          (unsubscribe-fn p topics (cdr w))) 

         ((rel-join-bn p pubs subs (f2b-ref w) u)
          (join-fn p pubs subs nbrs (cdr w)))

         ((rel-leave-bn p (f2b-ref w) u)
          (leave-fn p (cdr w))))))




(in-theory (disable prop=f2b-leave-fn
                    prop=f2b-join-fn
                    find-forwarder-definition-rule))

(property web3-uBv2-help1 (w :fn u :bn)
  :check-contracts? nil
  :h (rel-skip-bn (f2b-ref w) u)
  (^ (rel-B u (cons 'f (cdr w)))
     (rel-skip-fn w (cons 'f (cdr w))))
  :hints (("Goal" :in-theory (enable rel-skip-fn rel-b
                                     rel-skip-bn))))

(property web3-uBv2-help2 (w :fn u :bn m :mssg)
  :check-contracts? nil
  :h (^ (rel-broadcast-bn m (f2b-ref w) u)
        
        ;; CASE
        (^ (in m (fn-pending-mssgs (cdr w)))
           (!= (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
               (fn-pending-mssgs (cdr w))))

        ;; CONDITION 1 :
        (=> (^ (in m (fn-pending-mssgs (cdr w)))
               (! (in m (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w))))))
            (== (f2b (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
                (broadcast m (f2b (cdr w))))))
  (rel-B u (cons 'f (forward-fn (find-forwarder (cdr w) m) m (cdr w))))
  :instructions
  (:pro
   (= u (cons 'b (broadcast m (f2b (cdr w))))
      :hints (("Goal" :in-theory (enable rel-broadcast-bn))))
   (:claim (! (in m (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m)
                                                  m (cdr w)))))
           :hints (("Goal" :use ((:instance
                                  prop=fn-pending-mssgs-forward-fn
                                  (p (find-forwarder (cdr w) m))
                                  (s (cdr w)))))))
   (:prove :hints (("Goal" :use (b-bnbn))))))



(definec rankl (m :mssg s :fn) :nat
  (rankl-ct m (cdr s)))




(property prop=pending=>new-bn-mssgp (m :mssg w :fn)
  :check-contracts? nil
  :h  (in m (fn-pending-mssgs (cdr w)))
  (^ (mget (find-forwarder (cdr w) m) (cdr w))
     (in m (mget :pending (mget (find-forwarder (cdr w) m) (cdr w))))
     (new-bn-mssgp m (f2b (cdr w))))
  :rule-classes :forward-chaining)


(property web3-v2-help1 (m :mssg w :fn)
  :check-contracts? nil
  :h (^ (mget (find-forwarder (cdr w) m) (cdr w))
        (in m (mget :pending (mget (find-forwarder (cdr w) m) (cdr w))))
        (! (in m (mget :seen (mget (find-forwarder (cdr w) m) (cdr w)))))
        (! (in (find-forwarder (cdr w) m)
               (mget (mget :tp m)
                     (mget :nsubs (mget
                                   (find-forwarder (cdr w) m)
                                   (cdr w))))))
        ;; (B s u)
        (== (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
            (fn-pending-mssgs (cdr w))))
  (^ (== (f2b (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
         (f2b (cdr w)))
     (< (rankl m (cons 'f (forward-fn (find-forwarder (cdr w) m) m (cdr w))))
        (rankl m w)))
  :hints (("Goal" :use ((:instance prop=forward-fn-rank
                                   (p (find-forwarder (cdr w) m))
                                   (s (cdr w)))))))

(property web3-v2-help2 (m :mssg w :fn)
  :check-contracts? nil
  :h (^ (mget (mget :or m) (cdr w))
        (new-fn-mssgp m (cdr w))
        (in (mget :tp m)
            (mget :pubs (mget (mget :or m) (cdr w)))))
  (^ (== (f2b (produce-fn m (cdr w)))
         (f2b (cdr w)))
     (< (rankl m (cons 'f (produce-fn m (cdr w))))
        (rankl m w)))
  :hints (("Goal" :use ((:instance prop=produce-fn-rank
                                   (s (cdr w)))))))



(property web3-v2-help3 (w :fn u :bn m :mssg)
  :check-contracts? nil
  :h (^ (rel-broadcast-bn m (f2b-ref w) u)

        ;; CASE
        (new-fn-mssgp m (cdr w))

        (=> (in m (mget :pending (mget (find-forwarder (cdr w) m) (cdr w)))) 
            (! (in m (mget :seen (mget (find-forwarder (cdr w) m) (cdr w)))))) ;; Invariant

        (! (in (find-forwarder (cdr w) m)
               (mget (mget :tp m)
                     (mget :nsubs (mget (find-forwarder (cdr w) m) (cdr w)))))) ;; Invariant

        ;; CONDITION 1 :
        (=> (^ (in m (fn-pending-mssgs (cdr w)))
               (! (in m (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w))))))
            (== (f2b (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
                (broadcast m (f2b (cdr w))))))
  (^ (rel-B (f2b-ref w)
            (cons 'f (produce-fn m (cdr w))))
     (< (rankl m (cons 'f (produce-fn m (cdr w))))
        (rankl m w)))
  :instructions
  (:pro
  (:claim (^ (mget (mget :or m) (cdr w))
              (in (mget :tp m)
                  (mget :pubs (mget  (mget :or m) (cdr w)))))
           :hints (("Goal" :in-theory (enable rel-broadcast-bn)
                    :use ((:instance prop=f2b-produce-hyps
                                     (s (cdr w)))))))
  (:dv 1) (:rewrite b-bnfn) :s :top
  (:prove :hints (("Goal" :use ((:instance web3-v2-help2)))))
  :bash))


(property web3-v2-help4 (w :fn u :bn m :mssg)
  :check-contracts? nil
  :h (^ (rel-broadcast-bn m (f2b-ref w) u)

        ;; CASE
        (^ (! (new-fn-mssgp m (cdr w)))
           (in m (fn-pending-mssgs (cdr w)))
           (== (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w))) ;; CASE
               (fn-pending-mssgs (cdr w))))

        (=> (in m (mget :pending (mget (find-forwarder (cdr w) m) (cdr w)))) 
            (! (in m (mget :seen (mget (find-forwarder (cdr w) m) (cdr w)))))) ;; Invariant

        (! (in (find-forwarder (cdr w) m)
               (mget (mget :tp m)
                     (mget :nsubs (mget (find-forwarder (cdr w) m) (cdr w)))))) ;; Invariant

        
        ;; CONDITION 1 :
        (=> (^ (in m (fn-pending-mssgs (cdr w)))
               (! (in m (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w))))))
            (== (f2b (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
                (broadcast m (f2b (cdr w))))))
  (^ (rel-B (f2b-ref w)
            (cons 'f (forward-fn (find-forwarder (cdr w) m) m (cdr w))))
     (< (rankl m (cons 'f (forward-fn (find-forwarder (cdr w) m) m (cdr w))))
        (rankl m w)))
  :instructions
  (:pro
   (:claim (^ (mget (mget :or m) (cdr w))
              (in (mget :tp m)
                  (mget :pubs (mget  (mget :or m) (cdr w)))))
           :hints (("Goal" :in-theory (enable rel-broadcast-bn)
                    :use ((:instance prop=f2b-produce-hyps
                                     (s (cdr w)))))))
   (:claim (== (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
               (fn-pending-mssgs (cdr w))))
   (:dv 1) (:rewrite b-bnfn) :s :top
   (:prove :hints (("Goal" :use ((:instance web3-v2-help1)))))
   :bash))

;; TODO
;; (property web3-v2-help5 (w :fn u :bn m :mssg)
;;   :check-contracts? nil
;;   :h (^ (rel-broadcast-bn m (f2b-ref w) u)

;;         ;; CASE
;;         (^ (! (new-fn-mssgp m (cdr w)))
;;            (in m (fn-pending-mssgs (cdr w)))
;;            (!= (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w))) ;; CASE
;;                (fn-pending-mssgs (cdr w))))

;;         (=> (in m (mget :pending (mget (find-forwarder (cdr w) m) (cdr w)))) 
;;             (! (in m (mget :seen (mget (find-forwarder (cdr w) m) (cdr w)))))) ;; Invariant

;;         (! (in (find-forwarder (cdr w) m)
;;                (mget (mget :tp m)
;;                      (mget :nsubs (mget (find-forwarder (cdr w) m) (cdr w)))))) ;; Invariant

        
;;         ;; CONDITION 1 :
;;         (=> (^ (in m (fn-pending-mssgs (cdr w)))
;;                (! (in m (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w))))))
;;             (== (f2b (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
;;                 (broadcast m (f2b (cdr w))))))
;;   (^ (rel-B (f2b-ref w)
;;             (cons 'f (forward-fn (find-forwarder (cdr w) m) m (cdr w))))
;;      (< (rankl m (cons 'f (forward-fn (find-forwarder (cdr w) m) m (cdr w))))
;;         (rankl m w)))
;;   :instructions
;;   (:pro
;;    (:claim (^ (mget (mget :or m) (cdr w))
;;               (in (mget :tp m)
;;                   (mget :pubs (mget  (mget :or m) (cdr w)))))
;;            :hints (("Goal" :in-theory (enable rel-broadcast-bn)
;;                     :use ((:instance prop=f2b-produce-hyps
;;                                      (s (cdr w)))))))
;;    (:claim (== (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
;;                (fn-pending-mssgs (cdr w))))
;;    (:dv 1) (:rewrite b-bnfn) :s :top
;;    (:prove :hints (("Goal" :use ((:instance web3-v2-help1)))))
;;    :bash))


(propertyd web3-2 (s u :bn w :fn p :peer pubs subs topics :lot
                       nbrs :lop m :mssg)
  :check-contracts? nil
  :h (^ (rel-B s w)
        (rel-> p pubs subs topics nbrs m s u)

        ;; CONDITION 1 : Leave : no new pending messages with leavers 
        (=> (mget p (cdr w))
            (== (fn-pending-mssgs (leave-fn p (cdr w)))
                (fn-pending-mssgs (cdr w))))

        ;; CONDITION 1 :
        (=>  (^ (in m (fn-pending-mssgs (cdr w)))
                (! (in m (fn-pending-mssgs
                          (forward-fn
                           (find-forwarder (cdr w) m) m (cdr w))))))
             (== (f2b (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
                 (broadcast m (f2b (cdr w)))))

        (=> (in m (mget :pending (mget (find-forwarder (cdr w) m) (cdr w)))) 
            (! (in m (mget :seen (mget (find-forwarder (cdr w) m) (cdr w)))))) ;; Invariant

        (! (in p nbrs))                            ;; Invariant
        (! (in (find-forwarder (cdr w) m)          ;; Invariant
               (mget (mget :tp m)
                     (mget :nsubs (mget (find-forwarder (cdr w) m) (cdr w)))))))

  (v (^ (rel-> p pubs subs topics nbrs m
               w (exists-v2 u w p pubs subs topics nbrs m))
        (rel-B u (exists-v2 u w p pubs subs topics nbrs m)))
     (^ (rel-> p pubs subs topics nbrs m
               w (exists-v2 u w p pubs subs topics nbrs m))
        (rel-B s (exists-v2 u w p pubs subs topics nbrs m))
        (< (rankl m (exists-v2 u w p pubs subs topics nbrs m))
           (rankl m w))))
  :instructions
  (:pro
   (:claim (== s (f2b-ref w)))
   (:claim (rel-step-bn p pubs subs topics m s u))

   (:casesplit (rel-skip-bn (f2b-ref w) u))
   (:claim (^ (rel-b u (cons 'f (cdr w)))
              (rel-skip-fn w (cons 'f (cdr w))))
           :hints (("Goal" :use ((:instance web3-uBv2-help1)))))
   (= (exists-v2 u w p pubs subs topics nbrs m)
      (cons 'f (cdr w)))
   :prove

   (:casesplit (rel-broadcast-bn m (f2b-ref w) u))
   (:claim (^ (new-bn-mssgp m (cdr (f2b-ref w)))
              (== u (cons 'b (broadcast m (f2b (cdr w)))))
              (mget (mget :or m) (cdr w))
              (in (mget :tp m)
                  (mget :pubs (mget (mget :or m) (cdr w)))))
           :hints (("Goal" :in-theory (enable rel-broadcast-bn)
                    :use ((:instance prop=f2b-produce-hyps
                                     (s (cdr w)))))))
   
   (:casesplit (in m (fn-pending-mssgs (cdr w))))
   (:claim (^ (mget (find-forwarder (cdr w) m) (cdr w))
              (in m (mget :pending (mget (find-forwarder (cdr w) m) (cdr w)))))
           :hints (("Goal" :use ((:instance find-forwarder-contract
                                            (s (cdr w)))))))
   (:claim (v (== (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
                  (remove-equal m (fn-pending-mssgs (cdr w))))
              (== (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
                  (fn-pending-mssgs (cdr w))))
           :hints (("Goal" :use ((:instance prop=fn-pending-mssgs-forward-fn
                                            (s (cdr w))
                                            (p (find-forwarder (cdr w)
                                                               m)))))))

   (:casesplit (!= (fn-pending-mssgs (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
                   (fn-pending-mssgs (cdr w))))
   (= (exists-v2 u w p pubs subs topics nbrs m)
      (cons 'f (forward-fn (find-forwarder (cdr w) m) m
                           (cdr w))))
   (:claim (rel-b u (cons 'f (forward-fn (find-forwarder (cdr w) m) m
                                         (cdr w)))))
   :s
   (:rewrite rel->fnfn)
   (:r 2) :s
   
   (:prove :hints (("Goal" :in-theory (enable rel-forward-fn1))))
   :bash

   
   (= (exists-v2 u w p pubs subs topics nbrs m)
      (cons 'f (forward-fn (find-forwarder (cdr w) m) m
                           (cdr w))))
   (:dv 2 1) (:rewrite rel->fnfn) :top
   (= (rel-step-fn p pubs subs topics nbrs m w
                   (cons 'f
                         (forward-fn (find-forwarder (cdr w) m)
                                     m (cdr w))))
      t
      :hints (("Goal" :in-theory (enable rel-forward-fn2))))

   (:prove :hints (("Goal" :use ((:instance web3-v2-help4)))))
   :bash


   (:claim (new-fn-mssgp m (cdr w)))
   (= (exists-v2 u w p pubs subs topics nbrs m)
      (cons 'f (produce-fn m (cdr w))))
   (:dv 2 1) (:rewrite rel->fnfn) :top

   (= (rel-step-fn p pubs subs topics nbrs m w
                   (cons 'f (produce-fn m (cdr w))))
      t
      :hints (("Goal" :in-theory (enable rel-produce-fn))))
   (:prove :hints (("Goal" :use ((:instance web3-v2-help3)))))
   :bash
   

   (:casesplit (rel-subscribe-bn p topics s u))
   (= (exists-v2 u w p pubs subs topics nbrs m)
      (cons 'f (subscribe-fn p topics (cdr w))))

   (:claim (^ (mget p (cdr s))
              (== u (cons 'b (subscribe-bn p topics (cdr s)))))
           :hints (("Goal" :in-theory (enable rel-subscribe-bn)))) 

   (= (rel-> p pubs subs topics nbrs m w
             (cons 'f
                   (subscribe-fn p topics (cdr w))))
      t
      :hints (("Goal" :in-theory (enable rel->
                                         rel-step-fn
                                         rel-subscribe-fn)
               :use (rel->fnfn))))
   
   (= (rel-b u (cons 'f (subscribe-fn p topics (cdr w))))
      t)

   :s

   (:casesplit (rel-unsubscribe-bn p topics s u))
   (= (exists-v2 u w p pubs subs topics nbrs m)
      (cons 'f (unsubscribe-fn p topics (cdr w))))

   (:claim (^ (mget p (cdr s))
              (== u (cons 'b (unsubscribe-bn p topics (cdr s)))))
           :hints (("Goal" :in-theory (enable rel-unsubscribe-bn)))) 

   (= (rel-> p pubs subs topics nbrs m w
             (cons 'f
                   (unsubscribe-fn p topics (cdr w))))
      t
      :hints (("Goal" :in-theory (enable rel->
                                         rel-step-fn
                                         rel-unsubscribe-fn)
               :use (rel->fnfn))))
   
   (= (rel-b u (cons 'f (unsubscribe-fn p topics (cdr w))))
      t)
   :s

   (:casesplit (rel-join-bn p pubs subs s u))
   (= (exists-v2 u w p pubs subs topics nbrs m)
      (cons 'f (join-fn p pubs subs nbrs (cdr w))))

   (:claim (^ (! (mget p (cdr s)))
              (== u (cons 'b (join-bn p pubs subs (cdr s)))))
           :hints (("Goal" :in-theory (enable rel-join-bn))))
           
   
   (= (rel-> p pubs subs topics nbrs m w
             (cons 'f (join-fn p pubs subs nbrs (cdr w))))
      t
      :hints (("Goal" :in-theory (enable rel->
                                         rel-step-fn
                                         rel-join-fn)
               :use (rel->fnfn))))
   (= (rel-b u (cons 'f (join-fn p pubs subs nbrs (cdr w))))
      t)
   :s

   (:claim (rel-leave-bn p s u))
   (= (exists-v2 u w p pubs subs topics nbrs m)
      (cons 'f (leave-fn p (cdr w))))

   (:claim (^ (mget p (cdr s))
              (== u (cons 'b (leave-bn p (cdr s)))))
           :hints (("Goal" :in-theory (enable rel-leave-bn))))
           
   
   (= (rel-> p pubs subs topics nbrs m w
             (cons 'f (leave-fn p (cdr w))))
      t
      :hints (("Goal" :in-theory (enable rel->
                                         rel-step-fn
                                         rel-leave-fn)
               :use (rel->fnfn))))
   (= (rel-b u (cons 'f (leave-fn p (cdr w))))
      t)
   :s))





  

;;===========================================================================

(property web3-3 (s w u :fn p :peer pubs subs topics :lot
                    nbrs :lop m :mssg)
  :check-contracts? nil

  :h (^ (rel-B s w)
        (rel-> p pubs subs topics nbrs m s u)
      

        ;; CONDITION 1 :
        ;; full propagated => broadcast
        (=>  (^ (in m (fn-pending-mssgs (cdr s)))
                (! (in m (fn-pending-mssgs
                          (forward-fn
                           (find-forwarder (cdr s) m) m (cdr s))))))
             (== (f2b (forward-fn (find-forwarder (cdr s) m) m (cdr s)))
                 (broadcast m (f2b (cdr s)))))

        (=>  (^ (in m (fn-pending-mssgs (cdr w)))
                (! (in m (fn-pending-mssgs
                          (forward-fn
                           (find-forwarder (cdr w) m) m (cdr w))))))
             (== (f2b (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
                 (broadcast m (f2b (cdr w)))))

        ;; CONDITION 1 :
        ;; Leave : no new pending messages with leavers
        (=> (mget p (cdr s))
            (== (fn-pending-mssgs (leave-fn p (cdr s)))
                (fn-pending-mssgs (cdr s))))
        
        (=> (mget p (cdr w))
            (== (fn-pending-mssgs (leave-fn p (cdr w)))
                (fn-pending-mssgs (cdr w))))

        ;; CONDITION 2 : Message originator still in FloodNet as m is pending
        (=> (in m (fn-pending-mssgs (cdr s)))
            (^ (mget (mget :or m) (cdr s)) ;; origin still exists
               (in (mget :tp m)      ;; that can broadcast
                   (mget :pubs (mget  (mget :or m) (cdr s))))))

        ;; Invariant
        (=> (in m (mget :pending (mget (find-forwarder (cdr w) m) (cdr w)))) 
            (! (in m (mget :seen (mget (find-forwarder (cdr w) m) (cdr w))))))
        ;; Invariant
        (=> (in m (mget :pending (mget (find-forwarder (cdr s) m) (cdr s))))     
            (! (in m (mget :seen (mget (find-forwarder (cdr s) m) (cdr s))))))

        ;; Invariant
        (! (in p nbrs))
                
        ;; Invariant
        (! (in (find-forwarder (cdr w) m)
               (mget (mget :tp m)
                     (mget :nsubs (mget (find-forwarder (cdr w) m) (cdr w)))))))
  
  (v (^ (rel-> p pubs subs topics nbrs m
               w (exists-v2
                  (exists-v1 s u p pubs subs topics nbrs m)
                  w p pubs subs topics nbrs m))
        (rel-B u
               (exists-v2
                (exists-v1 s u p pubs subs topics nbrs m)
                w p pubs subs topics nbrs m)))
     (^ (rel-> p pubs subs topics nbrs m
               w (exists-v2
                  (exists-v1 s u p pubs subs topics nbrs m)
                  w p pubs subs topics nbrs m))
        (rel-B s
               (exists-v2
                (exists-v1 s u p pubs subs topics nbrs m)
                w p pubs subs topics nbrs m))
        (< (rankl m (exists-v2
                     (exists-v1 s u p pubs subs topics nbrs m)
                     w p pubs subs topics nbrs m))
           (rankl m w))))
  :instructions
  (:pro
   (:claim (rel-B s (f2b-ref s))
           :hints (("Goal" :use ((:instance b-maps-f2b)))))
   (:claim (bnp (f2b-ref s)))
   (:claim (^ (rel-> p pubs subs topics nbrs m (f2b-ref s)
                     (exists-v1 s u p pubs subs topics nbrs m))
              (rel-B u
                     (exists-v1 s u p pubs subs topics nbrs m)))
           :hints (("Goal" :use ((:instance web3-1
                                            (w (f2b-ref s)))))))

   (:claim (borfp s)
           :hints (("Goal" :use ((:instance fn->borf (x s))))))
   (:claim (borfp (f2b-ref s))
           :hints (("Goal" :use ((:instance bn->borf (x (f2b-ref s)))))))
   (:claim (rel-B (f2b-ref s) s)
           :hints (("Goal" :use ((:instance rel-B-symmetric
                                            (x s) (y (f2b-ref s)))))))
   (:claim (borfp w)
           :hints (("Goal" :use ((:instance fn->borf (x w))))))
   (:claim (rel-B (f2b-ref s) w)
           :hints (("Goal" :use ((:instance rel-B-transitive
                                            (x (f2b-ref s))
                                            (y s) (z w))))))
   
   (:claim (bnp (exists-v1 s u p pubs subs topics nbrs m)))
   
   (:claim (rel-b (f2b-ref s) s)
           :hints (("Goal" :use ((:instance rel-B-symmetric
                                            (x s)
                                            (y (f2b-ref s)))))))


   (:claim (v (^ (rel-> p pubs subs topics nbrs m
                        w (exists-v2
                           (exists-v1 s u p pubs subs topics nbrs m)
                           w p pubs subs topics nbrs m))
                 (rel-B (exists-v1 s u p pubs subs topics nbrs m)
                        (exists-v2
                         (exists-v1 s u p pubs subs topics nbrs m)
                         w p pubs subs topics nbrs m)))
              (^ (rel-> p pubs subs topics nbrs m
                        w (exists-v2
                           (exists-v1 s u p pubs subs topics nbrs m)
                           w p pubs subs topics nbrs m))
                 (rel-B (f2b-ref s)
                        (exists-v2
                         (exists-v1 s u p pubs subs topics nbrs m)
                         w p pubs subs topics nbrs m))
                 (< (rankl m (exists-v2
                              (exists-v1 s u p pubs subs topics nbrs m)
                              w p pubs subs topics nbrs m))
                    (rankl m w))))
           :hints (("Goal" :use ((:instance web3-2
                                            (s (f2b-ref s))
                                            (u (exists-v1 s u p pubs subs
                                                          topics nbrs m)))))))

   (:claim (borfp (exists-v2
                   (exists-v1 s u p pubs subs topics nbrs m)
                   w p pubs subs topics nbrs m))
           :hints (("Goal" :use ((:instance fn->borf (x (exists-v2
                                                         (exists-v1 s u p pubs subs topics nbrs m)
                                                         w p pubs subs topics
                                                         nbrs m)))))))
   
   (:casesplit (^ (rel-> p pubs subs topics nbrs m
                         w (exists-v2
                            (exists-v1 s u p pubs subs topics nbrs m)
                            w p pubs subs topics nbrs m))
                  (rel-B (exists-v1 s u p pubs subs topics nbrs m)
                         (exists-v2
                          (exists-v1 s u p pubs subs topics nbrs m)
                          w p pubs subs topics nbrs m))))

   (:claim (borfp u)
           :hints (("Goal" :use ((:instance fn->borf (x u))))))
   (:claim (borfp (exists-v1 s u p pubs subs topics nbrs m))
           :hints (("Goal" :use ((:instance fn->borf (x (exists-v1 s u p pubs subs topics nbrs m)))))))
   
   (:claim (rel-B u
                  (exists-v2
                   (exists-v1 s u p pubs subs topics nbrs m)
                   w p pubs subs topics nbrs m))
           :hints (("Goal" :use ((:instance rel-B-transitive
                                            (x u)
                                            (y (exists-v1 s u p pubs subs
                                                          topics nbrs m))
                                            (z (exists-v2
                                                (exists-v1 s u p pubs subs topics nbrs m)
                                                w p pubs subs topics nbrs
                                                m)))))))
   :s

   (:claim (and (rel-> p pubs subs topics nbrs m w
                    (exists-v2 (exists-v1 s u p pubs subs topics nbrs m)
                               w p pubs subs topics nbrs m))
             (rel-b (f2b-ref s)
                    (exists-v2 (exists-v1 s u p pubs subs topics nbrs m)
                               w p pubs subs topics nbrs m))
             (< (rankl m
                       (exists-v2 (exists-v1 s u p pubs subs topics nbrs m)
                                  w p pubs subs topics nbrs m))
                (rankl m w))))

   (:claim (rel-b s
                  (exists-v2 (exists-v1 s u p pubs subs topics nbrs m)
                             w p pubs subs topics nbrs m))
           :hints (("Goal" :use ((:instance rel-B-transitive
                                            (x s)
                                            (y (f2b-ref s))
                                            (z (exists-v2 (exists-v1 s u p pubs subs topics nbrs m)
                                                          w p pubs subs topics
                                                          nbrs m)))))))
   :s))


  


(in-theory (disable exists-v1 exists-v2 s-bnp s-fnp
                    rel-> rel-B rankl))

(definec exists-v (s u w :borf p :peer pubs subs topics :lot
                     nbrs :lop m :mssg) :borf
                     :body-contracts-hints (("Goal" :in-theory
                                             (enable borfp rel->)))
                     :ic (^ (! (in p nbrs))
                            (rel-> p pubs subs topics nbrs m s u))
  (cond
   ((^ (bnp s) (bnp w)) u)
   ((^ (fnp s) (bnp w)) (exists-v1 s u p pubs subs topics nbrs m))
   ((^ (bnp s) (fnp w)) (exists-v2 u w p pubs subs topics nbrs m))
   ((^ (fnp s) (fnp w)) (exists-v2 (exists-v1 s u p pubs subs topics nbrs m)
                                   w p pubs subs topics nbrs m))))





(property web3 (s u w :borf p :peer pubs subs topics :lot
                  nbrs :lop m :mssg)
  :check-contracts? nil

  :h (^ (rel-B s w)
        (rel-> p pubs subs topics nbrs m s u)      

        (! (in p nbrs)) ;;Join Condition
        (=> (fnp s)
            (^ ;; CONDITION 1 :
               ;; full propagated => broadcast
             (=>  (^ (in m (fn-pending-mssgs (cdr s)))
                     (! (in m (fn-pending-mssgs
                               (forward-fn
                                (find-forwarder (cdr s) m) m (cdr s))))))
                  (== (f2b (forward-fn (find-forwarder (cdr s) m) m (cdr s)))
                      (broadcast m (f2b (cdr s)))))
             
             ;; CONDITION 1 :
             ;; Leave : no new pending messages with leavers
             (=> (mget p (cdr s))
                 (== (fn-pending-mssgs (leave-fn p (cdr s)))
                     (fn-pending-mssgs (cdr s))))
             
             ;; CONDITION 2 : Message originator still in FloodNet as m is pending
             (=> (in m (fn-pending-mssgs (cdr s)))
                 (^ (mget (mget :or m) (cdr s)) ;; origin still exists
                    (in (mget :tp m)      ;; that can broadcast
                        (mget :pubs (mget  (mget :or m) (cdr s))))))
             
             ;; Invariant
             (=> (in m (mget :pending (mget (find-forwarder (cdr s) m) (cdr s))))     
                 (! (in m (mget :seen (mget (find-forwarder (cdr s) m)
                                            (cdr s))))))))
        
        (=> (fnp w)
            (^ ;; CONDITION 1 :
               ;; full propagated => broadcast
             (=>  (^ (in m (fn-pending-mssgs (cdr w)))
                     (! (in m (fn-pending-mssgs
                               (forward-fn
                                (find-forwarder (cdr w) m) m (cdr w))))))
                  (== (f2b (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
                      (broadcast m (f2b (cdr w)))))
             
             
             (=> (mget p (cdr w))
                 (== (fn-pending-mssgs (leave-fn p (cdr w)))
                     (fn-pending-mssgs (cdr w))))

             
             ;; Invariant
             (=> (in m (mget :pending (mget (find-forwarder (cdr w) m) (cdr w)))) 
                 (! (in m (mget :seen (mget (find-forwarder (cdr w) m)
                                            (cdr w))))))

             ;; Invariant
             (! (in (find-forwarder (cdr w) m)
                    (mget (mget :tp m)
                          (mget :nsubs (mget (find-forwarder (cdr w) m) (cdr w)))))))))
  (v (^ (rel-> p pubs subs topics nbrs m w
               (exists-v s u w p pubs subs topics nbrs m))
        (rel-B u (exists-v s u w p pubs subs topics nbrs m)))
     (^ (rel-> p pubs subs topics nbrs m w
               (exists-v s u w p pubs subs topics nbrs m))
        (rel-B s (exists-v s u w p pubs subs topics nbrs m))
        (< (rankl m (exists-v s u w p pubs subs topics nbrs m))
           (rankl m w))))
  :instructions
  (:pro
   (:casesplit (bnp s))
   (:casesplit (bnp w))
   :prove
   
   
   (:claim (fnp w))
   (:claim (bnp u))
   (= (exists-v s u w p pubs subs topics nbrs m)
      (exists-v2 u w p pubs subs topics nbrs m))
   (:prove :hints (("Goal" :use ((:instance web3-2)))))


   (:claim (fnp s))
   (:claim (fnp u))
   (:casesplit (bnp w))
   (= (exists-v s u w p pubs subs topics nbrs m)
      (exists-v1 s u p pubs subs topics nbrs m))
   (:prove :hints (("Goal" :use ((:instance web3-1)))))

   (:claim (fnp w))
   (= (exists-v s u w p pubs subs topics nbrs m)
      (exists-v2 (exists-v1 s u p pubs subs topics nbrs m)
                 w p pubs subs topics nbrs m)
      :hints (("Goal" :use ((:instance exists-v-definition-rule)))))
   (:claim
    (^ ;; CONDITION 1 :
               ;; full propagated => broadcast
             (=>  (^ (in m (fn-pending-mssgs (cdr w)))
                     (! (in m (fn-pending-mssgs
                               (forward-fn
                                (find-forwarder (cdr w) m) m (cdr w))))))
                  (== (f2b (forward-fn (find-forwarder (cdr w) m) m (cdr w)))
                      (broadcast m (f2b (cdr w)))))
             
             
             (=> (mget p (cdr w))
                 (== (fn-pending-mssgs (leave-fn p (cdr w)))
                     (fn-pending-mssgs (cdr w))))

             
             ;; Invariant
             (=> (in m (mget :pending (mget (find-forwarder (cdr w) m) (cdr w)))) 
                 (! (in m (mget :seen (mget (find-forwarder (cdr w) m)
                                            (cdr w))))))

             ;; Invariant
             (! (in (find-forwarder (cdr w) m)
                    (mget (mget :tp m)
                          (mget :nsubs (mget (find-forwarder (cdr w) m) (cdr
                                                                         w))))))))
   (:claim
    (^ ;; CONDITION 1 :
               ;; full propagated => broadcast
             (=>  (^ (in m (fn-pending-mssgs (cdr s)))
                     (! (in m (fn-pending-mssgs
                               (forward-fn
                                (find-forwarder (cdr s) m) m (cdr s))))))
                  (== (f2b (forward-fn (find-forwarder (cdr s) m) m (cdr s)))
                      (broadcast m (f2b (cdr s)))))
             
             ;; CONDITION 1 :
             ;; Leave : no new pending messages with leavers
             (=> (mget p (cdr s))
                 (== (fn-pending-mssgs (leave-fn p (cdr s)))
                     (fn-pending-mssgs (cdr s))))
             
             ;; CONDITION 2 : Message originator still in FloodNet as m is pending
             (=> (in m (fn-pending-mssgs (cdr s)))
                 (^ (mget (mget :or m) (cdr s)) ;; origin still exists
                    (in (mget :tp m)      ;; that can broadcast
                        (mget :pubs (mget  (mget :or m) (cdr s))))))
             
             ;; Invariant
             (=> (in m (mget :pending (mget (find-forwarder (cdr s) m) (cdr s))))     
                 (! (in m (mget :seen (mget (find-forwarder (cdr s) m)
                                            (cdr s))))))))
   :r))
   
  
