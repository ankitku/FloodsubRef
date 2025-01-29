(in-package "ACL2S")
(include-book "f2b-commit")

;; -------------------------------------------------------
;; Proof of refinement : FloodNet refines BroadcastNet
;; ------------------------------------------------------- 


(defdata borf (v s-bn s-fn))

(property bn->borf (x :s-bn)
  (borfp x))

(property fn->borf (x :s-fn)
  (borfp x))

(definec erankl (s u :borf) :nat
  (b* (((unless (s-fnp s)) 0)
       (m (br-mssg-witness
           (f2b s)
           (if (s-fnp u)
               (f2b u)
             u))))
    (if m
        (rankl m s)
      0)))

(property f2b=>!s-fnp (x :s-fn)
  (=> x
      (! (s-fnp (f2b x))))
  :hints (("Goal" :in-theory
           (enable f2b f2b-help))))

(property prop=erankl-f2b-u (s :borf u :s-fn)
  (== (erankl s u)
      (erankl s (f2b u))))

(property x-s-sb-s-fn (x :s-bn :s-fn)
  (null x) 
  :rule-classes :forward-chaining)



(definec rel-wf (x y :borf) :boolean
  (^ (s-bnp x)
     (s-fnp y)
     (good-s-fnp y)
     (== x (f2b y))))
  
(definec rel-B (x y :borf) :boolean
  (v (rel-wf x y)
     (rel-wf y x)
     (== x y)
     (^ (s-fnp x) (s-fnp y)
        (== (f2b x) (f2b y))
        (good-s-fnp x)
        (good-s-fnp y))))

(property b-fnbn (s :s-fn w :s-bn)
  (== (rel-B s w)
      (^ (== (f2b s) w)
         (good-s-fnp s))))

(property b-fnfn (s w :s-fn)
  (== (rel-B s w)
      (v (== s w)
         (^ (== (f2b s)
                (f2b w))
            (good-s-fnp s)
            (good-s-fnp w)))))

(property b-bnfn (s :s-bn w :s-fn)
  (== (rel-B s w)
      (^ (== (f2b w) s)
         (good-s-fnp w))))

(property b-bnbn (s w :s-bn)
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


;; WEB 1
(property b-maps-f2b (s :s-fn)
  :h (good-s-fnp s)
  (rel-B s (f2b s)))


;; WEB 2
(definec L (s :borf) :borf
  (match s
    (:s-bn s)
    (:s-fn (f2b s))))

(property web2 (s w :borf)
  :h (rel-B s w)
  (== (L s)
      (L w)))




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

(definecd rel-skip-bn (s u :s-bn) :bool
  (== u s))


(definecd rel-broadcast-bn (s u :s-bn) :bool
  (^ (br-mssg-witness s u)
     (broadcast-bn-pre (br-mssg-witness s u) s)
     (== u (broadcast (br-mssg-witness s u) s))))


(defdata maybe-ptops (v nil (cons peer lot)))

(property prop=lomp-subs-diff-bn (pst qst :ps-bn)
  :check-contracts? nil
  :h (set-difference-equal (mget :subs qst) (mget :subs pst))
  (lotp (set-difference-equal (mget :subs qst) (mget :subs pst)))
  :hints (("Goal" :in-theory (enable ps-bnp))))
  
(definec bn-topics-witness (s u :s-bn) :maybe-ptops
  :function-contract-hints (("Goal" :in-theory (enable s-bnp ps-bnp)))
  (cond
   ((v (endp s) (endp u)) nil)
   ((== (car s) (car u)) (bn-topics-witness (cdr s) (cdr u)))
   ((^ (== (caar s)
           (caar u))
       (set-difference-equal (mget :subs (cdar u))
                             (mget :subs (cdar s))))
    (cons (caar s)
          (set-difference-equal (mget :subs (cdar u))
                                (mget :subs (cdar s)))))
   (t nil)))

(definecd rel-subscribe-bn (s u :s-bn) :bool
  (^ (bn-topics-witness s u)
     (mget (car (bn-topics-witness s u)) s)
     (== u (subscribe-bn (car (bn-topics-witness s u))
                         (cdr (bn-topics-witness s u))
                         s))))

(definecd rel-unsubscribe-bn (s u :s-bn) :bool
  (^ (bn-topics-witness u s)
     (mget (car (bn-topics-witness u s)) s)
     (== u (unsubscribe-bn (car (bn-topics-witness u s))
                           (cdr (bn-topics-witness u s))
                           s))))


(defdata maybe-ppsbn (v nil
                        (cons peer ps-bn)))

(definec bn-join-witness (s u :s-bn) :maybe-ppsbn
  (match (list s u)
    ((() ((q . qst) . &)) `(,q . ,qst))
    ((((p . pst) . rs1)
      ((q . qst) . rs2))
     (cond
      ((== `(,p . ,pst)
           `(,q . ,qst))
       (bn-join-witness rs1 rs2))
      ((!= q p)
       `(,q . ,qst))
      (t nil)))
    (& nil)))


(property prop=bn-join-witness-mget (s u :s-bn)
  :h (bn-join-witness s u)
  (== (mget (car (bn-join-witness s u)) u)
      (cdr (bn-join-witness s u)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))

(property prop=bn-join-witness-mset-pst (s :s-bn p :peer pst :ps-bn)
  :h (! (mget p s))
  (bn-join-witness s (mset p pst s))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))

(definecd rel-leave-bn (s u :s-bn) :bool
  (^ (bn-join-witness u s)
     (mget (car (bn-join-witness u s)) s)
     (== u (leave-bn (car (bn-join-witness u s)) s))))

(definecd rel-join-bn (s u :s-bn) :bool
  (^ (bn-join-witness s u)
     (b* ((p (car (bn-join-witness s u)))
          (pst (cdr (bn-join-witness s u))))
       (^ (! (mget p s))
          (== u (join-bn p
                         (mget :pubs pst)
                         (mget :subs pst)
                         s))))))

(definec rel-step-bn (s u :s-bn) :bool
  (v (rel-skip-bn s u)
     (rel-broadcast-bn s u)
     (rel-subscribe-bn s u)
     (rel-unsubscribe-bn s u)
     (rel-leave-bn s u)
     (rel-join-bn s u)))

(property prop=empty-rel-step-bn (s u :s-bn)
  :h (^ (null s)
        (rel-step-bn s u))
  (v (rel-skip-bn s u)
     (rel-join-bn s u))
  :hints (("Goal" :in-theory (enable rel-skip-bn
                                     rel-broadcast-bn
                                     rel-subscribe-bn
                                     rel-unsubscribe-bn
                                     rel-leave-bn
                                     rel-join-bn))))
                                     


(definecd rel-skip-fn (s u :s-fn) :bool
  (== u s))

(definec rel-produce-help-fn (s u :s-fn ms :lom) :bool
  (match ms
    (() nil)
    ((m . rst)
     (v (^ (produce-fn-pre m s)
           (== u (produce-fn m s)))
        (rel-produce-help-fn s u rst)))))

(property prop=rel-produce-help-fn (s u :s-fn m :mssg ms :lom)
  :h (^ (in m ms)
        (produce-fn-pre m s)
        (== u (produce-fn m s)))
  (rel-produce-help-fn s u ms)
  :hints (("Goal" :in-theory (disable produce-fn-pre))))

(definecd rel-produce-fn (s u :s-fn) :bool
  (rel-produce-help-fn s u (fn-pending-mssgs u)))

(definecd rel-forward-fn1 (s u :s-fn) :bool
  (let ((m (br-mssg-witness (f2b s) (f2b u)))) ;; message is broadcasted in rel-forward-fn1
    (^ m
       (in m (fn-pending-mssgs s))
       (! (in m (mget :seen (mget (find-forwarder s m) s))))
       (!= (fn-pending-mssgs (forward-fn (find-forwarder s m) m s))
           (fn-pending-mssgs s))
       (^ (mget (mget :or m) s)
          (in (mget :tp m)
              (mget :pubs (mget (mget :or m) s))))
       (== u (forward-fn (find-forwarder s m) m s)))))

(definec rel-forward-help-fn2 (s u :s-fn ms :lom) :bool
  (match ms
    (() nil)
    ((m . rst)
     (v (^ (in m (fn-pending-mssgs s))
           (! (in m (mget :seen (mget (find-forwarder s m) s))))  ;; Invariant
           (== (fn-pending-mssgs
                (forward-fn (find-forwarder s m) m s)) ;;CASE
               (fn-pending-mssgs s))
           (== u (forward-fn (find-forwarder s m) m s)))
        (rel-forward-help-fn2 s u rst)))))

(property prop=rel-forwardm-help-fn2 (s u :s-fn m :mssg ms :lom)
  :h (^ (in m ms)
        (in m (fn-pending-mssgs s))
        (! (in m (mget :seen (mget (find-forwarder s m) s))))  ;; Invariant
        (== (fn-pending-mssgs
             (forward-fn (find-forwarder s m) m s)) ;;CASE
            (fn-pending-mssgs s))
        (== u (forward-fn (find-forwarder s m) m s)))
  (rel-forward-help-fn2 s u ms))
  
(definecd rel-forward-fn2 (s u :s-fn) :bool
    (rel-forward-help-fn2 s u (fn-pending-mssgs s)))


(definec fn-topics-witness (s u :s-fn) :maybe-ptops
  (bn-topics-witness (f2b s) (f2b u)))

(definecd rel-subscribe-fn (s u :s-fn) :bool
  (^ (fn-topics-witness s u)
     (mget (car (fn-topics-witness s u)) s)
     (== u (subscribe-fn (car (fn-topics-witness s u))
                         (cdr (fn-topics-witness s u))
                         s))))

(definecd rel-unsubscribe-fn (s u :s-fn) :bool
  (^ (fn-topics-witness u s)
     (mget (car (fn-topics-witness u s)) s)
     (== u (unsubscribe-fn (car (fn-topics-witness u s))
                           (cdr (fn-topics-witness u s))
                           s))))


(defdata maybe-ppsfn (v nil
                        (cons peer ps-fn)))

(property mset-psbn->psfn (pst :ps-bn tlm :topic-lop-map)
  :hints (("Goal" :in-theory (enable ps-bnp
                                     ps-fnp)))
  (ps-fnp (mset :0tag 'ps-fn
                (mset :nsubs tlm
                      pst))))

(definec fn-join-witness (s u :s-fn) :maybe-ppsfn
  :function-contract-hints
  (("Goal" :use ((:instance prop=mget-f2b=>mget
                            (p (car (bn-join-witness
                                     (f2b s) (f2b u))))
                            (s u)))))
  (b* ((res (bn-join-witness (f2b s) (f2b u)))
       ((when (null res)) nil))
    (cons (car res)
          (mget (car res) u))))


(definecd rel-leave-fn (s u :s-fn) :bool
  (^ (fn-join-witness u s)
     (mget (car (fn-join-witness u s)) s)
     (== (fn-pending-mssgs (leave-fn (car (fn-join-witness u s)) s))
         (fn-pending-mssgs s))
     (== u (leave-fn (car (fn-join-witness u s)) s))))

(definec topic-lop-map->lop (x :topic-lop-map) :lop
  (match x
    (() ())
    (((& . ps) . rs)
     (app ps (topic-lop-map->lop rs)))))

(definecd rel-join-fn (s u :s-fn) :bool
  :body-contracts-hints (("Goal"
                          :use ((:instance prop=mget-f2b=>mget
                                           (p (car (bn-join-witness (f2b s) (f2b u))))
                                           (s u)))))
  (^ (fn-join-witness s u)
     (b* ((p (car (fn-join-witness s u)))
          (pst (cdr (fn-join-witness s u)))
          (nbrs (topic-lop-map->lop (mget :nsubs pst))))
       (^ (! (mget p s))
          (! (in p nbrs))
          (== u (join-fn p
                         (mget :pubs pst)
                         (mget :subs pst)
                         nbrs
                         s))))))

(property prop=fn-join-witness-preserves-pubs-subs (s u :s-fn)
  :h (fn-join-witness s u)
  (^ (== (mget :pubs (cdr (fn-join-witness s u)))
         (mget :pubs (cdr (bn-join-witness (f2b s) (f2b u)))))
     (== (mget :subs (cdr (fn-join-witness s u)))
         (mget :subs (cdr (bn-join-witness (f2b s) (f2b u))))))
  :instructions
  (:pro
   (:claim (bn-join-witness (f2b s) (f2b u)))
   (= (cdr (bn-join-witness (f2b s) (f2b u)))
      (mget (car (bn-join-witness (f2b s) (f2b u))) (f2b u))
      :hints (("Goal" :use ((:instance prop=bn-join-witness-mget
                                       (s (f2b s))
                                       (u (f2b u)))))))
   (= (car (bn-join-witness (f2b s) (f2b u)))
      (car (fn-join-witness s u)))
   (:claim (mget (car (fn-join-witness s u))
                 (f2b u)))
   (:claim (mget (car (fn-join-witness s u)) u))
   (= (f2b u)
      (f2b-help u (fn-pending-mssgs u))
      :hints (("Goal" :in-theory (enable f2b))))
   (= (mget (car (fn-join-witness s u))
            (f2b-help u (fn-pending-mssgs u)))
      (f2b-st (mget (car (fn-join-witness s u)) u)
              (fn-pending-mssgs u))
      :hints (("Goal" :use ((:instance prop=f2b-st-f2b-mget
                                       (p (car (fn-join-witness s u)))
                                       (s u)
                                       (ms (fn-pending-mssgs u)))))))
   (= (mget :pubs (f2b-st (mget (car (fn-join-witness s u)) u)
                          (fn-pending-mssgs u)))
      (mget :pubs (mget (car (fn-join-witness s u)) u))
      :hints (("Goal" :use ((:instance prop=f2b-st-check
                                       (ps (mget (car (fn-join-witness s u))
                                                 u))
                                       (ms (fn-pending-mssgs u)))))))
   (= (mget :subs (f2b-st (mget (car (fn-join-witness s u)) u)
                          (fn-pending-mssgs u)))
      (mget :subs (mget (car (fn-join-witness s u)) u))
      :hints (("Goal" :use ((:instance prop=f2b-st-check
                                       (ps (mget (car (fn-join-witness s u))
                                                 u))
                                       (ms (fn-pending-mssgs u)))))))
   :prove))


(definec rel-step-fn (s u :s-fn) :bool
  (v (rel-skip-fn s u)
     (rel-produce-fn s u)
     (rel-forward-fn1 s u)
     (rel-forward-fn2 s u)
     (rel-subscribe-fn s u)
     (rel-unsubscribe-fn s u)
     (rel-leave-fn s u)
     (rel-join-fn s u)))

(property prop=empty-rel-produce-fn1 (s u :s-fn ms :lom)
  (! (rel-produce-help-fn nil u ms))) 

(property prop=empty-rel-produce-fn2 (u :s-fn)
  (! (rel-produce-fn nil u))
  :hints (("Goal" :in-theory (enable
                              rel-produce-fn))))
  
(property prop=empty-rel-step-fn (u :s-fn)
  :h (rel-step-fn nil u)
  (v (rel-skip-fn nil u)
     (rel-join-fn nil u))
  :hints (("Goal" :in-theory (enable rel-skip-fn
                                     rel-produce-help-fn
                                     rel-produce-fn
                                     rel-forward-fn1
                                     rel-forward-fn2
                                     rel-subscribe-fn
                                     rel-unsubscribe-fn
                                     rel-leave-fn
                                     rel-join-fn))))

(definec good-rel-step-fn (s u :s-fn) :bool
  (^ (good-s-fnp s)
     (good-s-fnp u)
     (rel-step-fn s u)))

(definec rel-> (s u :borf) :bool
  (v (^ (s-fnp s)
        (s-fnp u)
        (good-rel-step-fn s u))
     (^ (s-bnp s)
        (s-bnp u)
        (rel-step-bn s u))))

(property rel->fnfn (s u :s-fn)
  (== (rel-> s u)
      (^ (good-s-fnp s)
         (good-s-fnp u)
         (rel-step-fn s u))))

(property rel->bnbn (s u :s-bn) 
  (== (rel-> s u)
      (rel-step-bn s u)))


;; WEB 3 provables
(property web3-urel->v1-help1 (s u :s-fn)
  :h (rel-skip-fn s u)
  (rel-skip-bn (f2b s) (f2b u))
  :hints (("Goal" :in-theory (enable rel-skip-fn
                                     rel-skip-bn))))


(property web3-urel->v1-help2 (s u :s-fn)
  :h (rel-subscribe-fn s u)
  (rel-subscribe-bn (f2b s) (f2b u))
  :hints (("Goal" :in-theory (enable rel-subscribe-fn
                                     rel-subscribe-bn)
           :use ((:instance prop=f2b-subscribe-fn
                            (p (car (fn-topics-witness s u)))
                            (topics (cdr (fn-topics-witness s u))))))))

(property web3-urel->v1-help3 (s u :s-fn)
  :h (rel-unsubscribe-fn s u)
  (rel-unsubscribe-bn (f2b s) (f2b u))
  :hints (("Goal" :in-theory (enable rel-unsubscribe-fn
                                     rel-unsubscribe-bn)
           :use ((:instance prop=f2b-unsubscribe-fn
                            (p (car (fn-topics-witness u s)))
                            (topics (cdr (fn-topics-witness u s))))))))

(property web3-urel->v1-help4 (s u :s-fn)
  :h (rel-join-fn s u)
  (rel-join-bn (f2b s) (f2b u))
  :instructions
  (:pro (:r 2) :s
        (:claim (^ (fn-join-witness s u)
                   (! (mget (car (fn-join-witness s u)) (f2b s)))
                   (! (in (car (fn-join-witness s u))
                          (topic-lop-map->lop (mget :nsubs (cdr
                                                            (fn-join-witness s u))))))
                   (== u (join-fn (car (fn-join-witness s u))
                         (mget :pubs (cdr (fn-join-witness s u)))
                         (mget :subs (cdr (fn-join-witness s u)))
                         (topic-lop-map->lop
                          (mget :nsubs
                                (cdr (fn-join-witness s u))))
                         s)))
                :hints (("Goal" :in-theory (enable rel-join-fn))))
        
        (:claim (bn-join-witness (f2b s) (f2b u)))
        (:claim (not (mget (car (bn-join-witness (f2b s) (f2b u)))
                           (f2b s)))
                :hints (("Goal" :in-theory (enable rel-join-fn))))
        :s
        (:claim (not (mget (car (bn-join-witness (f2b s) (f2b u))) s)))
        (:claim (== (car (bn-join-witness (f2b s) (f2b u)))
                    (car (fn-join-witness s u))))
        (:claim (not (mget (car (fn-join-witness s u)) s)))
        (= (car (bn-join-witness (f2b s) (f2b u)))
           (car (fn-join-witness s u)))
        (:claim (== (cdr (fn-join-witness s u))
                    (mget (car (fn-join-witness s u)) u)))
        (= (mget :pubs (cdr (bn-join-witness (f2b s) (f2b u))))
           (mget :pubs (cdr (fn-join-witness s u)))
           :hints (("Goal" :use ((:instance
                                  prop=fn-join-witness-preserves-pubs-subs)))))
        (= (mget :subs (cdr (bn-join-witness (f2b s) (f2b u))))
           (mget :subs (cdr (fn-join-witness s u)))
           :hints (("Goal" :use ((:instance
                                  prop=fn-join-witness-preserves-pubs-subs)))))
        (:dv 1)
        (= u (join-fn (car (fn-join-witness s u))
                      (mget :pubs (cdr (fn-join-witness s u)))
                      (mget :subs (cdr (fn-join-witness s u)))
                      (topic-lop-map->lop (mget :nsubs (cdr (fn-join-witness s u))))
                      s))
        :top
        (:prove :hints (("Goal" :use
                         ((:instance prop=f2b-join-fn
                                     (p (car (fn-join-witness s u)))
                                     (pubs (mget :pubs (cdr (fn-join-witness s u))))
                                     (subs (mget :subs (cdr (fn-join-witness s u))))
                                     (nbrs (topic-lop-map->lop
                                            (mget :nsubs (cdr (fn-join-witness s u)))))
                          )))))))

(property web3-urel->v1-help5 (s u :s-fn)
  :check-contracts? nil
  :h (rel-leave-fn s u)
  (rel-leave-bn (f2b s) (f2b u))
  :instructions
  (:pro
   (:rewrite rel-leave-bn)
   (:claim (^ (fn-join-witness u s)
              (mget (car (fn-join-witness u s)) s)
              (== (fn-pending-mssgs (leave-fn (car (fn-join-witness u s)) s))
                  (fn-pending-mssgs s))
              (== u (leave-fn (car (fn-join-witness u s)) s)))
           :hints (("Goal" :in-theory (enable rel-leave-fn))))
   (:claim (bn-join-witness (f2b u) (f2b s)))
   :s (:dv 1)
   (:equiv u (leave-fn (car (fn-join-witness u s)) s))
   :top
   (:prove :hints (("Goal" :use
                    ((:instance prop=f2b-leave-fn
                                (p (car (fn-join-witness u s))))))))))


(property web3-urel->v1-help60 (s u :s-fn ms :lom)
  :h (rel-produce-help-fn s u ms)
  (== (f2b u) (f2b s)))

(property web3-urel->v1-help6 (s u :s-fn)
  :h (rel-produce-fn s u)
  (rel-skip-bn (f2b s) (f2b u))
  :hints (("Goal" :in-theory (enable rel-produce-fn
                                     rel-skip-bn))))


(property web3-urel->v1-help70 (s u :s-fn ms :lom)
  :h (rel-forward-help-fn2 s u ms)
  (== (f2b u) (f2b s)))

(property web3-urel->v1-help7 (s u :s-fn)
  :check-contracts? nil
  :h (rel-forward-fn2 s u)
  (rel-skip-bn (f2b s) (f2b u))
  :hints (("Goal" :in-theory (enable rel-forward-fn2
                                     rel-skip-bn))))

(property prop=fn-pending!=fwd-pending=>!in-fwd-pending (s :s-fn m :mssg)
  :h (^ (in m (fn-pending-mssgs s))
        (!= (fn-pending-mssgs s)
            (fn-pending-mssgs (forward-fn (find-forwarder s m) m s))))
  (! (in m (fn-pending-mssgs (forward-fn (find-forwarder s m) m s))))
  :instructions
  (:pro 
   (:claim (^ (mget (find-forwarder s m) s)
              (in m (mget :pending (mget
                                    (find-forwarder s m)
                                    s)))))

   (:claim  (or (equal (fn-pending-mssgs (forward-fn (find-forwarder s m) m s))
                       (remove-equal m (fn-pending-mssgs s)))
                (equal (fn-pending-mssgs (forward-fn (find-forwarder s m) m s))
                       (fn-pending-mssgs s)))
                :hints (("Goal" :use ((:instance prop=fn-pending-mssgs-forward-fn
                                                 (p (find-forwarder s m)))))))
   :prove))


(property web3-urel->v1-help8 (s u :s-fn)
  :check-contracts? nil
  :h (^ (rel-forward-fn1 s u)

        ;; CONDITION 1 :
        (=> (^ (in (br-mssg-witness (f2b s) (f2b u))
                   (fn-pending-mssgs s))
               (! (in (br-mssg-witness (f2b s) (f2b u))
                      (fn-pending-mssgs (forward-fn (find-forwarder s (br-mssg-witness (f2b s) (f2b u)))
                                                    (br-mssg-witness (f2b s) (f2b u)) s)))))
            (== (f2b (forward-fn (find-forwarder s (br-mssg-witness (f2b s) (f2b u)))
                                 (br-mssg-witness (f2b s) (f2b u)) s))
                (broadcast (br-mssg-witness (f2b s) (f2b u)) (f2b s)))))
  (rel-broadcast-bn (f2b s) (broadcast (br-mssg-witness (f2b s) (f2b u))
                                       (f2b s)))
  :instructions
  (:pro
   (:claim
    (^ (br-mssg-witness (f2b s) (f2b u))
       (in (br-mssg-witness (f2b s) (f2b u)) (fn-pending-mssgs s))
       (! (in (br-mssg-witness (f2b s) (f2b u))
              (mget :seen (mget
                           (find-forwarder s (br-mssg-witness (f2b s)
                                                              (f2b u))) s)))) ;; Invariant
       (!= (fn-pending-mssgs
            (forward-fn
             (find-forwarder s (br-mssg-witness (f2b s) (f2b u)))
             (br-mssg-witness (f2b s) (f2b u))
             s)) ;; CASE
           (fn-pending-mssgs s))
       (^ (mget (mget :or (br-mssg-witness (f2b s) (f2b u))) s)   
          (in (mget :tp (br-mssg-witness (f2b s) (f2b u)))
              (mget :pubs (mget  (mget :or (br-mssg-witness (f2b s) (f2b u))) s))))
       (== u (forward-fn (find-forwarder s (br-mssg-witness (f2b s) (f2b u)))
                         (br-mssg-witness (f2b s) (f2b u)) s)))
    :hints (("Goal" :in-theory (enable rel-forward-fn1))))
   
   
   (:claim (in (br-mssg-witness (f2b s) (f2b u))
               (fn-pending-mssgs s)))

   (:claim (! (in (br-mssg-witness (f2b s) (f2b u))
                  (fn-pending-mssgs
                   (forward-fn
                    (find-forwarder s (br-mssg-witness (f2b s)
                                                       (f2b u)))
                    (br-mssg-witness (f2b s)
                                     (f2b u))
                    s))))
           :hints (("Goal" :use ((:instance
                                  prop=fn-pending!=fwd-pending=>!in-fwd-pending
                                  (m (br-mssg-witness (f2b s) (f2b u))))))))

   (:claim (and (integerp (car (car s)))
                (not (< (car (car s)) 0))))

   (:claim (equal (f2b (forward-fn
                        (find-forwarder s (br-mssg-witness (f2b s) (f2b u)))
                        (br-mssg-witness (f2b s) (f2b u))
                        s))
                  (broadcast (br-mssg-witness (f2b s) (f2b u))
                             (f2b s))))
   
   (= (broadcast (br-mssg-witness (f2b s) (f2b u))
                 (f2b s))
      (f2b u))
   
   (:claim (^ (mget (mget :or (br-mssg-witness (f2b s) (f2b u)))
                    (f2b s))
              (in (mget :tp (br-mssg-witness (f2b s) (f2b u)))
                  (mget :pubs (mget (mget :or (br-mssg-witness (f2b s) (f2b u)))
                                    (f2b s)))))
           :hints (("Goal" :use ((:instance prop=f2b-broadcast-hyps
                                            (m (br-mssg-witness (f2b s) (f2b u))))))))
   (:prove :hints (("Goal" :in-theory (enable rel-broadcast-bn))))))



(definec exists-v1 (s u :s-fn) :s-bn
  :body-contracts-hints (("Goal" :use (prop=f2b-broadcast-hyps)
                          :in-theory (enable rel-forward-fn1)))
  (cond
   ((rel-forward-fn1 s u) (broadcast (br-mssg-witness (f2b s) (f2b u))
                                     (f2b s)))
   ((rel-subscribe-fn s u) (f2b u))
   ((rel-unsubscribe-fn s u) (f2b u))
   ((rel-join-fn s u) (f2b u))
   ((rel-leave-fn s u) (f2b u))
   (t (f2b s))))


(property web3-uBv1-help (s u :s-fn)
  :check-contracts? nil
  :h (^ (good-rel-step-fn s u)
        
        ;; CONDITION 1 :
        (=> (^ (in (br-mssg-witness (f2b s) (f2b u))
                   (fn-pending-mssgs s))
               (! (in (br-mssg-witness (f2b s) (f2b u))
                      (fn-pending-mssgs (forward-fn (find-forwarder s (br-mssg-witness (f2b s) (f2b u)))
                                                    (br-mssg-witness (f2b s) (f2b u)) s)))))
            (== (f2b (forward-fn (find-forwarder s (br-mssg-witness (f2b s) (f2b u)))
                                 (br-mssg-witness (f2b s) (f2b u)) s))
                (broadcast (br-mssg-witness (f2b s) (f2b u)) (f2b s)))))
  (rel-b u (exists-v1 s u))
  :instructions
  (:pro (:claim (^ (good-s-fnp s)
                   (good-s-fnp u)
                   (rel-step-fn s u)))
        (:rewrite b-fnbn)
        (:casesplit (rel-forward-fn1 s u))
        (:claim (rel-broadcast-bn (f2b s)
                                  (broadcast (br-mssg-witness (f2b s) (f2b u))
                                             (f2b s)))
                :hints (("Goal" :use ((:instance web3-urel->v1-help8)))))
        (= (exists-v1 s u) (broadcast (br-mssg-witness (f2b s) (f2b u))
                                      (f2b s)))           
        
        (:claim
         (^ (br-mssg-witness (f2b s) (f2b u))
            (in (br-mssg-witness (f2b s) (f2b u)) (fn-pending-mssgs s))
            (! (in (br-mssg-witness (f2b s) (f2b u)) (mget :seen (mget (find-forwarder s (br-mssg-witness (f2b s) (f2b u))) s))))        ;; Invariant
            (!= (fn-pending-mssgs (forward-fn (find-forwarder s (br-mssg-witness (f2b s) (f2b u))) (br-mssg-witness (f2b s) (f2b u)) s)) ;; CASE
                (fn-pending-mssgs s))
            (^ (mget (mget :or (br-mssg-witness (f2b s) (f2b u))) s)   
               (in (mget :tp (br-mssg-witness (f2b s) (f2b u)))
                   (mget :pubs (mget  (mget :or (br-mssg-witness (f2b s) (f2b u))) s))))
            (== u (forward-fn (find-forwarder s (br-mssg-witness (f2b s) (f2b u)))
                              (br-mssg-witness (f2b s) (f2b u)) s)))
         :hints (("Goal" :in-theory (enable rel-forward-fn1))))
        (= (f2b u)
           (f2b (forward-fn (find-forwarder s (br-mssg-witness (f2b s) (f2b u)))
                            (br-mssg-witness (f2b s) (f2b u)) s)))

        (:claim (in (br-mssg-witness (f2b s) (f2b u))
                    (fn-pending-mssgs s)))

        (:claim (! (in (br-mssg-witness (f2b s) (f2b u))
                       (fn-pending-mssgs
                        (forward-fn (find-forwarder s (br-mssg-witness (f2b s) (f2b u)))
                                    (br-mssg-witness (f2b s) (f2b u))
                                    s))))
                :hints (("Goal" :use ((:instance prop=fn-pending!=fwd-pending=>!in-fwd-pending
                                                 (m (br-mssg-witness (f2b s) (f2b u))))))))
   
        
        :prove
        (:casesplit (rel-subscribe-fn s u)) :s
        (:casesplit (rel-unsubscribe-fn s u)) :s
        (:casesplit (rel-join-fn s u)) :s
        (:casesplit (rel-leave-fn s u)) :s
        (:casesplit (rel-skip-fn s u)) :s
        (:prove :hints (("Goal" :in-theory (enable rel-skip-bn rel-skip-fn))))
        :s
        (:casesplit (rel-forward-fn2 s u))
        (:claim (rel-skip-bn (f2b s) (f2b u))
                :hints (("Goal" :use ((:instance web3-urel->v1-help7)))))

        (:demote 15) (:dv 1) (:rewrite rel-skip-bn) :s :top :s
                
        (:claim (rel-produce-fn s u))
        (:claim (rel-skip-bn (f2b s) (f2b u))
                :hints (("Goal" :use ((:instance web3-urel->v1-help6)))))
        (:demote 16) (:dv 1) (:rewrite rel-skip-bn) :s :top :s))



;; TODO add conditions about message :or
(defmacro f2b-condition1a (s m)
  `(=> (^ (in ,m (fn-pending-mssgs ,s))
          (! (in ,m (fn-pending-mssgs (forward-fn
                                      (find-forwarder ,s ,m)
                                      ,m ,s)))))
       (== (f2b (forward-fn
                 (find-forwarder ,s ,m)
                 ,m ,s))
           (broadcast ,m (f2b ,s)))))

(defmacro f2b-condition1b (s p)
  `(=> (mget ,p ,s)
       (== (fn-pending-mssgs (leave-fn ,p ,s))
           (fn-pending-mssgs ,s))))

(defmacro f2b-condition2 (s m)
  `(=> (in ,m (fn-pending-mssgs ,s))
       (^ (mget (mget :or ,m) ,s) ;; origin still exists
          (in (mget :tp ,m)      ;; that can broadcast
              (mget :pubs (mget (mget :or ,m) ,s))))))

(defmacro f2b-invariants (s m)
  `(^
    ;; Invariant
    (=> (in ,m (mget :pending (mget (find-forwarder ,s ,m) ,s)))     
        (! (in ,m (mget :seen (mget (find-forwarder ,s ,m) ,s)))))
    
    ;; Invariant
    (! (in (find-forwarder ,s ,m)
           (mget (mget :tp ,m)
                 (mget :nsubs (mget (find-forwarder ,s ,m) ,s)))))))


;; packed condiitons and invariants in a defmacro
(defmacro f2b-refinement-conditions (s m p)
  `(^ (=> (^ (in ,m (fn-pending-mssgs ,s))
             (! (in ,m (fn-pending-mssgs (forward-fn
                                          (find-forwarder ,s ,m)
                                          ,m ,s)))))
          (== (f2b (forward-fn
                    (find-forwarder ,s ,m)
                    ,m ,s))
              (broadcast ,m (f2b ,s))))
      
      (=> (mget ,p ,s)
       (== (fn-pending-mssgs (leave-fn ,p ,s))
           (fn-pending-mssgs ,s)))
      
      (=> (in ,m (fn-pending-mssgs ,s))
          (^ (mget (mget :or ,m) ,s) ;; origin still exists
             (in (mget :tp ,m)       ;; that can broadcast
                 (mget :pubs (mget (mget :or ,m) ,s)))))

      (^
       (=> (in ,m (mget :pending (mget (find-forwarder ,s ,m) ,s)))     
           (! (in ,m (mget :seen (mget (find-forwarder ,s ,m) ,s)))))
       
       (! (in (find-forwarder ,s ,m)
              (mget (mget :tp ,m)
                    (mget :nsubs (mget (find-forwarder ,s ,m) ,s))))))))
   

(property web3-urel->v1-help (s u :s-fn)
  :check-contracts? nil
  :h (^ (rel-step-fn s u)

        ;; CONDITION 1 :
        (f2b-condition1a s (br-mssg-witness (f2b s) (f2b u))))
  (rel-step-bn (f2b s) (exists-v1 s u))

  :instructions
  (:pro (:casesplit (rel-forward-fn1 s u))
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help8)))))
        (:casesplit (rel-forward-fn2 s u)) 
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help7))
                         :in-theory (enable rel-skip-bn))))
        (:casesplit (rel-subscribe-fn s u)) 
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help2)))))
        (:casesplit (rel-unsubscribe-fn s u)) 
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help3)))))
        (:casesplit (rel-join-fn s u)) 
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help4)))))
        (:casesplit (rel-leave-fn s u))
        (:prove :hints (("Goal" :use ((:instance web3-urel->v1-help5)))))
        (:casesplit (rel-skip-fn s u))
        (:prove :hints (("Goal" :in-theory (enable rel-skip-bn))))
        (:casesplit (rel-produce-fn s u))
        (:prove :hints (("Goal" :in-theory (enable rel-step-fn rel-skip-bn))))
        (:prove :hints (("Goal" :in-theory (enable rel-step-fn rel-skip-bn))))))


(propertyd web3-1-help (s u :s-fn w :s-bn)
  :check-contracts? nil
  :h (^ (rel-B s w)
        (rel-> s u)
        
        ;; CONDITION 1 :
        (f2b-condition1a s (br-mssg-witness (f2b s) (f2b u))))
  
     (^ (rel-> w (exists-v1 s u))
        (rel-B u (exists-v1 s u)))
  :instructions
  (:pro
   (= w (f2b s))
   (:claim (rel-step-fn s u))
   (= (rel-> (f2b s)
             (exists-v1 s u))
      (rel-step-bn (f2b s) (exists-v1 s u))
      :hints (("Goal" :in-theory (disable exists-v1-definition-rule))))
   (:claim (rel-step-bn (f2b s) (exists-v1 s u))
           :hints (("Goal" :use ((:instance web3-urel->v1-help)))))
   (:claim (rel-B u (exists-v1 s u))
           :hints (("Goal" :use ((:instance web3-uBv1-help)))))
           
   :s))


(property web3-1 (s u :s-fn w :s-bn)
  :check-contracts? nil
  :h (^ (rel-B s w)
        (rel-> s u)
        
        ;; CONDITION 1 :
        (f2b-refinement-conditions s
                                   (br-mssg-witness (f2b s) (f2b u))
                                   (car (bn-join-witness (f2b u) (f2b s)))))
  
     (^ (rel-> w (exists-v1 s u))
        (rel-B u (exists-v1 s u)))
     :hints (("Goal" :use ((:instance web3-1-help)))))
  
;;==================================================================  
;; WEB 3-2 provables

(definec exists-v21 (u :s-bn w :s-fn) :s-fn
  :body-contracts-hints (("Goal"
                          :in-theory (enable rel-subscribe-bn
                                             rel-unsubscribe-bn)))
  (cond
     ((rel-subscribe-bn (f2b w) u)
      (subscribe-fn (car (bn-topics-witness (f2b w) u))
                    (cdr (bn-topics-witness (f2b w) u))
                    w))

     ((rel-unsubscribe-bn (f2b w) u)
      (unsubscribe-fn (car (bn-topics-witness u (f2b w)))
                      (cdr (bn-topics-witness u (f2b w)))
                      w))))

(definec exists-v22 (u :s-bn w :s-fn) :s-fn
  :body-contracts-hints (("Goal" :use ((:instance prop=f2b-produce-hyps
                                                  (s w)
                                                  (m (br-mssg-witness (f2b w) u))))
                          :in-theory (enable rel-skip-bn
                                             rel-broadcast-bn)))
  (cond
     ((rel-skip-bn (f2b w) u) w)
     ((^ (rel-broadcast-bn (f2b w) u)
         (in (br-mssg-witness (f2b w) u)
             (fn-pending-mssgs w)))
      (forward-fn (find-forwarder w (br-mssg-witness (f2b w) u))
                  (br-mssg-witness (f2b w) u)
                  w))
     
     ((^ (rel-broadcast-bn (f2b w) u)
         (! (in (br-mssg-witness (f2b w) u)
                (fn-pending-mssgs w))))
      (produce-fn (br-mssg-witness (f2b w) u) w))))

(definec exists-v23 (u :s-bn w :s-fn) :s-fn
  :body-contracts-hints (("Goal"
                          :in-theory (enable rel-join-bn
                                             rel-leave-bn)))
  (cond

     ((rel-join-bn (f2b w) u)
      (b* ((ppsbn (bn-join-witness (f2b w) u))
           (p (car ppsbn))
           (pst (cdr ppsbn))
           (pubs (mget :pubs pst))
           (subs (mget :subs pst)))
        (join-fn p pubs subs '() w)))

     ((rel-leave-bn (f2b w) u)
      (leave-fn (car (bn-join-witness u (f2b w))) w))))
   

(definec exists-v2 (u :s-bn w :s-fn) :s-fn
    (cond
     ((v (rel-skip-bn (f2b w) u)
         (rel-broadcast-bn (f2b w) u))
      (exists-v22 u w))
     
     ((v (rel-subscribe-bn (f2b w) u)
         (rel-unsubscribe-bn (f2b w) u))
      (exists-v21 u w))

     ((v (rel-join-bn (f2b w) u)
         (rel-leave-bn (f2b w) u))
      (exists-v23 u w))))


(property web3-uBv2-help1 (w :s-fn u :s-bn)
  :check-contracts? nil
  :h (^ (rel-skip-bn (f2b w) u)
        (good-s-fnp w))
  (^ (rel-B u w)
     (rel-skip-fn w w))
  :hints (("Goal" :in-theory (enable rel-skip-fn rel-b
                                     rel-skip-bn))))

(i-am-here)
;; need to prove that exist-v2 produces good states.

(property web3-uBv2-help2 (w :s-fn u :s-bn)
  :check-contracts? nil
  :h (^ (rel-broadcast-bn (f2b w) u)
        (good-s-fnp w)
        ;; CASE
        (^ (in (br-mssg-witness (f2b w) u) (fn-pending-mssgs w))
           (!= (fn-pending-mssgs (forward-fn (find-forwarder w (br-mssg-witness
                                                                (f2b w) u))
                                             (br-mssg-witness (f2b w) u) w))
               (fn-pending-mssgs w)))

        ;; CONDITION 1 :
        (=> (^ (in (br-mssg-witness (f2b w) u)
                   (fn-pending-mssgs w))
               (! (in (br-mssg-witness (f2b w) u)
                      (fn-pending-mssgs (forward-fn
                                         (find-forwarder w (br-mssg-witness (f2b w) u))
                                         (br-mssg-witness (f2b w) u) w)))))
            (== (f2b (forward-fn (find-forwarder w (br-mssg-witness (f2b w) u))
                                 (br-mssg-witness (f2b w) u) w))
                (broadcast (br-mssg-witness (f2b w) u) (f2b w)))))
  (rel-B u (forward-fn (find-forwarder w (br-mssg-witness (f2b w) u))
                       (br-mssg-witness (f2b w) u) w))
  :instructions
  (:pro
   (:dv 1)
   (= u (broadcast (br-mssg-witness (f2b w) u) (f2b w))
      :hints (("Goal" :in-theory (enable rel-broadcast-bn))))
   :top
   (:claim (br-mssg-witness (f2b w) u)
           :hints (("Goal" :in-theory (enable rel-broadcast-bn))))
   (:claim (in (br-mssg-witness (f2b w) u)
               (mget :pending (mget (find-forwarder w (br-mssg-witness
                                                       (f2b w) u))
                                    w)))
           :hints (("Goal" :use ((:instance find-forwarder-contract
                                            (s w)
                                            (m (br-mssg-witness (f2b w) u)))))))
   
   (:claim (! (in (br-mssg-witness (f2b w) u)
                  (fn-pending-mssgs (forward-fn
                                     (find-forwarder w (br-mssg-witness (f2b w) u))
                                     (br-mssg-witness (f2b w) u)
                                     w))))
           :hints (("Goal" :use ((:instance
                                  prop=fn-pending-mssgs-forward-fn
                                  (m (br-mssg-witness (f2b w) u))
                                  (p (find-forwarder w (br-mssg-witness (f2b w) u)))
                                  (s w))))))
   (:prove :hints (("Goal" :use (b-bnbn))))))


(property web3-v2-help1 (m :mssg w :s-fn)
  :check-contracts? nil
  :h (^ (mget (find-forwarder w m) w)
        (in m (mget :pending (mget (find-forwarder w m) w)))
        (! (in m (mget :seen (mget (find-forwarder w m) w))))
        (! (in (find-forwarder w m)
               (mget (mget :tp m)
                     (mget :nsubs (mget
                                   (find-forwarder w m)
                                   w)))))
        ;; (B s u)
        (== (fn-pending-mssgs (forward-fn (find-forwarder w m) m w))
            (fn-pending-mssgs w)))
  (^ (== (f2b (forward-fn (find-forwarder w m) m w))
         (f2b w))
     (< (rankl m (forward-fn (find-forwarder w m) m w))
        (rankl m w)))
  :hints (("Goal" :use ((:instance prop=forward-fn-rank
                                   (p (find-forwarder w m))
                                   (s w))))))

(property web3-v2-help2 (m :mssg w :s-fn)
  :check-contracts? nil
  :h (^ (mget (mget :or m) w)
        (new-fn-mssgp m w)
        (in (mget :tp m)
            (mget :pubs (mget (mget :or m) w))))
  (^ (== (f2b (produce-fn m w))
         (f2b w))
     (< (rankl m (produce-fn m w))
        (rankl m w)))
  :hints (("Goal" :use ((:instance prop=produce-fn-rank
                                   (s w))))))

(property web3-v2-help3 (w :s-fn u :s-bn)
  :check-contracts? nil
  :h (^ (rel-broadcast-bn (f2b w) u)

        ;; CASE
        (new-fn-mssgp (br-mssg-witness (f2b w) u) w))
  (^ (rel-B (f2b w)
            (produce-fn (br-mssg-witness (f2b w) u) w))
     (< (rankl (br-mssg-witness (f2b w) u)
               (produce-fn (br-mssg-witness (f2b w) u) w))
        (rankl (br-mssg-witness (f2b w) u) w)))
  :instructions
  (:pro
  (:claim (^ (mget (mget :or (br-mssg-witness (f2b w) u)) w)
              (in (mget :tp (br-mssg-witness (f2b w) u))
                  (mget :pubs (mget  (mget :or (br-mssg-witness (f2b w) u)) w))))
           :hints (("Goal" :in-theory (enable rel-broadcast-bn)
                    :use ((:instance prop=f2b-produce-hyps
                                     (s w)
                                     (m (br-mssg-witness (f2b w) u)))))))
  (:dv 1) (:rewrite b-bnfn) :s :top
  (:prove :hints (("Goal" :use ((:instance web3-v2-help2
                                           (m (br-mssg-witness (f2b w) u)))))))))

(property web3-v2-help4 (w :s-fn u :s-bn)
  :check-contracts? nil
  :h (^ (rel-broadcast-bn (f2b w) u)

        ;; CASE
        (^ (! (new-fn-mssgp (br-mssg-witness (f2b w) u) w))
           (in (br-mssg-witness (f2b w) u)
               (fn-pending-mssgs w))
           (== (fn-pending-mssgs (forward-fn
                                  (find-forwarder w (br-mssg-witness (f2b w)
                                                                     u))
                                  (br-mssg-witness (f2b w) u) w)) ;; CASE
               (fn-pending-mssgs w)))

        (=> (in (br-mssg-witness (f2b w) u)
                (mget :pending (mget (find-forwarder w (br-mssg-witness
                                                        (f2b w) u))
                                     w))) 
            (! (in (br-mssg-witness (f2b w) u)
                   (mget :seen (mget (find-forwarder w (br-mssg-witness
                                                        (f2b w) u)) w))))) ;; Invariant

        (! (in (find-forwarder w (br-mssg-witness (f2b w) u))
               (mget (mget :tp (br-mssg-witness (f2b w) u))
                     (mget :nsubs (mget (find-forwarder w (br-mssg-witness
                                                           (f2b w) u))
                                        w)))))) ;; Invariant
  (^ (rel-B (f2b w)
            (forward-fn (find-forwarder w (br-mssg-witness (f2b w) u))
                        (br-mssg-witness (f2b w) u) w))
     (< (rankl (br-mssg-witness (f2b w) u)
               (forward-fn (find-forwarder w (br-mssg-witness
                                              (f2b w) u))
                           (br-mssg-witness (f2b w) u) w))
        (rankl (br-mssg-witness (f2b w) u) w)))
  :instructions
  (:pro 
   (:claim (^ (mget (mget :or (br-mssg-witness (f2b w) u)) w)
              (in (mget :tp (br-mssg-witness (f2b w) u))
                  (mget :pubs (mget  (mget :or (br-mssg-witness (f2b w) u)) w))))
           :hints (("Goal" :in-theory (enable rel-broadcast-bn)
                    :use ((:instance prop=f2b-produce-hyps
                                     (s w)
                                     (m (br-mssg-witness (f2b w) u)))))))
   (:claim (== (fn-pending-mssgs (forward-fn
                                  (find-forwarder w (br-mssg-witness
                                                     (f2b w) u))
                                  (br-mssg-witness (f2b w) u) w))
               (fn-pending-mssgs w)))
   (:dv 1) (:rewrite b-bnfn) :top
   (:prove :hints (("Goal" :use ((:instance web3-v2-help1
                                            (m (br-mssg-witness (f2b w) u)))))))))


(property web3-v2-help50 (w :s-fn u :s-bn p :peer pubs subs :lot)
  :check-contracts? nil
  :h (! (mget p w))
  (! (in p (topic-lop-map->lop
            (mget :nsubs
                  (mget p (join-fn p pubs subs '() w))))))
  :instructions
  (:pro
   (= (join-fn p pubs subs nil w)
      (mset p (new-joinee-st-fn pubs subs '() w) w)
      :hints (("Goal" :use ((:instance join-fn-nbrs-nil
                                       (s w))))))
   (:prove :hints (("Goal" :in-theory (enable ps-fnp
                                              calc-nsubs-fn
                                              new-joinee-st-fn))))))


(property web3-v2-help51 (w :s-fn u :s-bn)
  :check-contracts? nil
  :h (rel-join-bn (f2b w) u)
  (fn-join-witness w
                   (join-fn (car (bn-join-witness (f2b w) u))
                            (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                            (mget :subs (cdr (bn-join-witness (f2b w) u)))
                            nil w))
  :instructions
  (:pro
   (:rewrite fn-join-witness) :s :s
   (:claim (== (rel-join-bn (f2b w) u)
               (and (bn-join-witness (f2b w) u)
                    (not (mget (car (bn-join-witness (f2b w) u))
                               (f2b w)))
                    (equal u
                           (join-bn (car (bn-join-witness (f2b w) u))
                                    (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                                    (mget :subs (cdr (bn-join-witness (f2b w) u)))
                                    (f2b w)))))
           :hints (("Goal" :in-theory (enable rel-join-bn))))
   (:claim (and (bn-join-witness (f2b w) u)
                    (not (mget (car (bn-join-witness (f2b w) u))
                               (f2b w)))
                    (equal u
                           (join-bn (car (bn-join-witness (f2b w) u))
                                    (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                                    (mget :subs (cdr (bn-join-witness (f2b w) u)))
                                    (f2b w)))))
   
   (= (f2b (join-fn (car (bn-join-witness (f2b w) u))
                    (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                    (mget :subs (cdr (bn-join-witness (f2b w) u)))
                    nil w))
      (join-bn (car (bn-join-witness (f2b w) u))
               (mget :pubs (cdr (bn-join-witness (f2b w) u)))
               (mget :subs (cdr (bn-join-witness (f2b w) u)))
               (f2b w))
      :hints (("Goal" :use ((:instance prop=f2b-join-fn
                                       (p (car (bn-join-witness (f2b w) u)))
                                       (s w)
                                       (nbrs nil)
                                       (pubs (mget :pubs (cdr (bn-join-witness
                                                               (f2b w) u))))
                                       (subs (mget :subs (cdr (bn-join-witness
                                                               (f2b w)
                                                               u)))))))))
   :prove))

(property web3-v2-help52 (w :s-fn u :s-bn)
  :check-contracts? nil
  :h (^ (rel-join-bn (f2b w) u)
        (== u (f2b (join-fn (car (bn-join-witness (f2b w) u))
                            (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                            (mget :subs (cdr (bn-join-witness (f2b w) u)))
                            nil
                            w))))
  (rel-join-fn w (join-fn (car (bn-join-witness (f2b w) u))
                          (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                          (mget :subs (cdr (bn-join-witness (f2b w) u)))
                          nil
                          w))
  :instructions
  (:pro
   (:claim (! (mget (car (bn-join-witness (f2b w) u)) w))
           :hints (("Goal" :in-theory (enable rel-join-bn))))
   :r
   (:claim (fn-join-witness w
                            (join-fn (car (bn-join-witness (f2b w) u))
                                     (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                                     (mget :subs (cdr (bn-join-witness (f2b w) u)))
                                     nil w)))
   :s
   (:claim (== (car (fn-join-witness w
                                     (join-fn (car (bn-join-witness (f2b w) u))
                                              (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                                              (mget :subs (cdr (bn-join-witness (f2b w) u)))
                                              nil w)))
               (car (bn-join-witness (f2b w) u))))
   (:claim (bn-join-witness (f2b w) u)) :s :bash
   (= (calc-nsubs-fn nil w nil) nil
      :hints (("Goal" :in-theory (enable calc-nsubs-fn))))
   :bash
   (= (calc-nsubs-fn nil w nil) nil
      :hints (("Goal" :in-theory (enable calc-nsubs-fn))))
   :bash
   (= (calc-nsubs-fn nil w nil) nil
      :hints (("Goal" :in-theory (enable calc-nsubs-fn))))
   :bash))
                   
(property web3-v2-help5 (w :s-fn u :s-bn)
  :h (^ (not (rel-skip-bn (f2b w) u))
        (not (rel-broadcast-bn (f2b w) u))
        (not (rel-subscribe-bn (f2b w) u))
        (not (rel-unsubscribe-bn (f2b w) u))
        (rel-join-bn (f2b w) u))
  (^ (rel-> w (exists-v2 u w))
     (rel-b u (exists-v2 u w)))
  :instructions
  (:pro
   (:claim (^ (bn-join-witness (f2b w) u)
              (! (mget (car (bn-join-witness
                             (f2b w) u))
                       (f2b w)))
              (== u (join-bn (car (bn-join-witness (f2b w) u))
                             (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                             (mget :subs (cdr (bn-join-witness (f2b w) u)))
                             (f2b w))))
           :hints (("Goal" :in-theory (enable rel-join-bn))))
   (:claim (== (exists-v2 u w)
               (join-fn (car (bn-join-witness (f2b w) u))
                        (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                        (mget :subs (cdr (bn-join-witness (f2b w) u)))
                        '()
                        w)))
   (:equiv (exists-v2 u w)
           (join-fn (car (bn-join-witness (f2b w) u))
                    (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                    (mget :subs (cdr (bn-join-witness (f2b w) u)))
                    '()
                    w))

   (:claim (! (mget (car (bn-join-witness (f2b w) u)) w))) 
   (:claim (! (in (car (bn-join-witness (f2b w) u))
                  (topic-lop-map->lop
                   (mget
                    :nsubs (mget (car (bn-join-witness (f2b w) u))
                                 (join-fn (car (bn-join-witness (f2b w) u))
                                          (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                                          (mget :subs (cdr (bn-join-witness (f2b w) u)))
                                          nil
                                          w))))))
           :hints (("Goal" :use ((:instance web3-v2-help50
                                            (p (car (bn-join-witness (f2b w) u)))
                                            (u (f2b w))
                                            (pubs (mget :pubs (cdr
                                                               (bn-join-witness
                                                                (f2b w) u))))
                                            (subs (mget :subs (cdr
                                                               (bn-join-witness
                                                                (f2b w)
                                                                u)))))))))

   (:claim (== (f2b (join-fn (car (bn-join-witness (f2b w) u))
                    (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                    (mget :subs (cdr (bn-join-witness (f2b w) u)))
                    '()
                    w))
               (join-bn (car (bn-join-witness (f2b w) u))
                        (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                        (mget :subs (cdr (bn-join-witness (f2b w) u)))
                        (f2b w)))
           :hints (("Goal" :use ((:instance prop=f2b-join-fn
                                            (nbrs '())
                                            (p (car (bn-join-witness (f2b w)
                                                                     u)))
                                            (s w)
                                            (pubs (mget :pubs (cdr
                                                               (bn-join-witness
                                                                (f2b w) u))))
                                            (subs (mget :subs (cdr
                                                               (bn-join-witness
                                                                (f2b w)
                                                                u)))))))))
   (:claim (s-fnp (join-fn (car (bn-join-witness (f2b w) u))
                     (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                     (mget :subs (cdr (bn-join-witness (f2b w) u)))
                     nil w)))
   (:dv 2) (:rewrite b-bnfn) :s :top
   (:dv 1) (:rewrite rel->fnfn) (:r 2) :top
   (:claim (== u (f2b (join-fn (car (bn-join-witness (f2b w) u))
                            (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                            (mget :subs (cdr (bn-join-witness (f2b w) u)))
                            nil
                            w))))
   (:claim (rel-join-fn w (join-fn (car (bn-join-witness (f2b w) u))
                          (mget :pubs (cdr (bn-join-witness (f2b w) u)))
                          (mget :subs (cdr (bn-join-witness (f2b w) u)))
                          nil
                          w))
           :hints (("Goal" :use ((:instance web3-v2-help52)))))
   :s))


(property web3-v2-help61 (w :s-fn u :s-bn)
  :check-contracts? nil
  :h (^ (rel-leave-bn (f2b w) u)
        (=> (mget (car (bn-join-witness u (f2b w))) w)
            (== (fn-pending-mssgs (leave-fn (car (bn-join-witness u (f2b w))) w))
                (fn-pending-mssgs w))))
  (fn-join-witness (leave-fn (car (bn-join-witness u (f2b w)))
                             w)
                   w)
  :instructions
  (:pro
   (:rewrite fn-join-witness) :s :s
   (:claim (== (rel-leave-bn (f2b w) u)
               (and (bn-join-witness u (f2b w))
                    (mget (car (bn-join-witness u (f2b w)))
                          (f2b w))
                    (equal u
                           (leave-bn (car (bn-join-witness u (f2b w)))
                                     (f2b w)))))
           :hints (("Goal" :in-theory (enable rel-leave-bn))))
   (:claim (and (bn-join-witness u (f2b w))
                (mget (car (bn-join-witness u (f2b w)))
                      (f2b w))
                (equal u
                       (leave-bn (car (bn-join-witness u (f2b w)))
                                 (f2b w)))))
   
   (= (f2b (leave-fn (car (bn-join-witness u (f2b w))) w))
      (leave-bn (car (bn-join-witness u (f2b w))) (f2b w))
      :hints (("Goal" :use ((:instance prop=f2b-leave-fn
                                       (s w)
                                       (p (car (bn-join-witness
                                                u (f2b w)))))))))
   :prove))


(property web3-v2-help62 (w :s-fn u :s-bn)
  :check-contracts? nil
  :h (^ (rel-leave-bn (f2b w) u)
        (=> (mget (car (bn-join-witness u (f2b w))) w)
            (== (fn-pending-mssgs (leave-fn (car (bn-join-witness u (f2b w))) w))
                (fn-pending-mssgs w)))
        (== u (f2b (leave-fn (car (bn-join-witness u (f2b w))) w))))
  (rel-leave-fn w (leave-fn (car (bn-join-witness u (f2b w))) w))
  :instructions
  (:pro
   (:claim (mget (car (bn-join-witness u (f2b w))) (f2b w))
           :hints (("Goal" :in-theory (enable rel-leave-bn))))
   :r
   (:claim (fn-join-witness (leave-fn (car (bn-join-witness
                                            u (f2b w)))
                                      w)
                            w))
   (:claim (== (car (fn-join-witness (leave-fn (car (bn-join-witness u (f2b w)))
                                               w)
                                     w))
               (car (bn-join-witness u (f2b w)))))
   :s
   (:claim (bn-join-witness u (f2b w))) :s :bash))
  

(property web3-v2-help6 (w :s-fn u :s-bn)
  :h (^ (not (rel-skip-bn (f2b w) u))
        (not (rel-broadcast-bn (f2b w) u))
        (not (rel-subscribe-bn (f2b w) u))
        (not (rel-unsubscribe-bn (f2b w) u))
        (not (rel-join-bn (f2b w) u))
        (rel-leave-bn (f2b w) u)

        (=> (mget (car (bn-join-witness u (f2b w))) w)
            (== (fn-pending-mssgs (leave-fn (car (bn-join-witness u (f2b w))) w))
                (fn-pending-mssgs w))))
  (^ (rel-> w
            (exists-v2 u w))
     (rel-b u (exists-v2 u w)))
  :instructions
  (:pro
   (:claim (^ (bn-join-witness u (f2b w))
              (mget (car (bn-join-witness u (f2b w))) (f2b w))
              (== u (leave-bn (car (bn-join-witness u (f2b w)))
                              (f2b w))))
           :hints (("Goal" :in-theory (enable rel-leave-bn))))
   (:claim (== (exists-v2 u w)
               (leave-fn (car (bn-join-witness u (f2b w))) w)))
   (:claim (mget (car (bn-join-witness u (f2b w))) w))
   (:equiv  (exists-v2 u w)
            (leave-fn (car (bn-join-witness u (f2b w))) w))

   (:claim (== (f2b (leave-fn (car (bn-join-witness u (f2b w))) w))
               (leave-bn (car (bn-join-witness u (f2b w))) (f2b w)))
           :hints (("Goal" :use ((:instance prop=f2b-leave-fn
                                            (s w)
                                            (p (car (bn-join-witness
                                                     u (f2b w)))))))))
   (:dv 2) (:rewrite b-bnfn) :s :top
   (:dv 1) (:rewrite rel->fnfn) (:r 2) :top
   (:claim (fn-join-witness (leave-fn
                             (car (bn-join-witness u (f2b w)))
                             w)
                            w)
           :hints (("Goal" :use ((:instance web3-v2-help61)))))
   (:claim (rel-leave-fn w
                          (leave-fn (car (bn-join-witness u (f2b w)))
                                    w))
           :hints (("Goal" :use ((:instance web3-v2-help62)))))
   :s))

;; invariants needed here.
(propertyd web3-v2-help7 (s u :s-bn w :s-fn)
  :check-contracts? nil
  :h (^ (rel-B s w)
        (rel-> s u)
        (! (rel-skip-bn (f2b w) u))
        (rel-broadcast-bn (f2b w) u)
        (f2b-refinement-conditions w
                                   (br-mssg-witness (f2b w) u)
                                   (car (bn-join-witness u (f2b w)))))

  (v (^ (rel-> w (exists-v2 u w))
        (rel-B u (exists-v2 u w)))
     (^ (rel-> w (exists-v2 u w))
        (rel-B s (exists-v2 u w))
        (< (erankl (exists-v2 u w) u)
           (erankl w u))))
  :instructions
  (:pro
   (:claim (== s (f2b w)))
   (:claim (rel-step-bn s u))

   (:claim (^ (br-mssg-witness (f2b w) u)
              (broadcast-bn-pre (br-mssg-witness (f2b w) u) (f2b w))
              (== u (broadcast (br-mssg-witness (f2b w) u) (f2b w))))
           :hints (("Goal" :in-theory (enable rel-broadcast-bn))))
   
   (:claim (^ (new-bn-mssgp (br-mssg-witness (f2b w) u) (f2b w))
              (mget (mget :or (br-mssg-witness (f2b w) u)) (f2b w))
              (in (mget :tp (br-mssg-witness (f2b w) u))
                  (mget :pubs (mget (mget :or (br-mssg-witness
                                               (f2b w) u))
                                    (f2b w))))))
   (:claim (^ (mget (mget :or (br-mssg-witness (f2b w) u)) w)
              (in (mget :tp (br-mssg-witness (f2b w) u))
                  (mget :pubs (mget (mget :or (br-mssg-witness
                                               (f2b w) u))
                                    w))))
           :hints (("Goal" :use ((:instance prop=f2b-produce-hyps
                                            (s w)
                                            (m (br-mssg-witness (f2b w) u)))))))
   
   (:casesplit (in (br-mssg-witness (f2b w) u) (fn-pending-mssgs w)))
   (:claim (^ (mget (find-forwarder w (br-mssg-witness (f2b w) u)) w)
              (in (br-mssg-witness (f2b w) u)
                  (mget :pending (mget (find-forwarder w (br-mssg-witness
                                                          (f2b w) u))
                                       w))))
           :hints (("Goal" :use ((:instance find-forwarder-contract
                                            (s w)
                                            (m (br-mssg-witness (f2b w)
                                                                u)))))))
   
   (:claim (v (== (fn-pending-mssgs (forward-fn
                                     (find-forwarder w (br-mssg-witness
                                                        (f2b w) u))
                                     (br-mssg-witness (f2b w) u) w))
                  (remove-equal (br-mssg-witness (f2b w) u) (fn-pending-mssgs w)))
              (== (fn-pending-mssgs (forward-fn
                                     (find-forwarder w (br-mssg-witness
                                                        (f2b w) u))
                                     (br-mssg-witness (f2b w) u) w))
                  (fn-pending-mssgs w)))
           :hints (("Goal" :use ((:instance prop=fn-pending-mssgs-forward-fn
                                            (s w)
                                            (m (br-mssg-witness (f2b w) u))
                                            (p (find-forwarder w
                                                               (br-mssg-witness
                                                                (f2b w) u))))))))

   (:casesplit (!= (fn-pending-mssgs
                    (forward-fn
                     (find-forwarder w
                                     (br-mssg-witness (f2b w) u))
                                      (br-mssg-witness (f2b w) u) w))
                   (fn-pending-mssgs w)))
   (:prove :hints (("Goal" :in-theory (enable rel-forward-fn1))))


   (:claim (^ (rel-B (f2b w)
                     (forward-fn (find-forwarder w (br-mssg-witness (f2b w) u))
                                 (br-mssg-witness (f2b w) u) w))
              (< (rankl (br-mssg-witness (f2b w) u)
                        (forward-fn (find-forwarder w (br-mssg-witness
                                                       (f2b w) u))
                                    (br-mssg-witness (f2b w) u) w))
                 (rankl (br-mssg-witness (f2b w) u) w)))
           :hints (("Goal" :in-theory (enable rel-forward-fn2)
                    :use ((:instance web3-v2-help4)))))
   (= (exists-v2 u w)
      (forward-fn (find-forwarder w (br-mssg-witness (f2b w) u))
                  (br-mssg-witness (f2b w) u)
                  w))

   :s

   (:claim (equal (f2b (forward-fn (find-forwarder w (br-mssg-witness s u))
                             (br-mssg-witness s u)
                             w))
                  s))
   :s

   (:claim (rel-forward-fn2 w
                            (forward-fn (find-forwarder w (br-mssg-witness (f2b w) u))
                                        (br-mssg-witness (f2b w) u)
                                        w))
           :hints (("Goal" :in-theory (enable rel-forward-fn2)
                    :use ((:instance prop=rel-forwardm-help-fn2
                                     (s w)
                                     (u (forward-fn (find-forwarder w (br-mssg-witness (f2b w) u))
                                                    (br-mssg-witness (f2b w) u)
                                                    w))
                                     (ms (fn-pending-mssgs s)))))))
   (= s (f2b w))
   (:claim (s-bnp u)) :s
   (= (erankl w u)
      (rankl (br-mssg-witness (f2b w) u) w))
   (= (erankl (forward-fn (find-forwarder w (br-mssg-witness s u))
                           (br-mssg-witness s u)
                           w)
              u)
      (rankl (br-mssg-witness (f2b w) u)
              (forward-fn (find-forwarder w (br-mssg-witness (f2b w) u))
                          (br-mssg-witness (f2b w) u)
                          w)))
   :s

   (:claim (new-fn-mssgp (br-mssg-witness (f2b w) u) w))
   (:claim (^ (rel-B (f2b w)
                     (produce-fn (br-mssg-witness (f2b w) u) w))
              (< (rankl (br-mssg-witness (f2b w) u) (produce-fn (br-mssg-witness (f2b w) u) w))
                 (rankl (br-mssg-witness (f2b w) u) w)))
           :hints (("Goal" :in-theory (enable rel-produce-fn)
                    :use ((:instance web3-v2-help3)))))
   (= s (f2b w))
   (= (exists-v2 u w)
      (produce-fn (br-mssg-witness (f2b w) u)
                  w))
   
   (:claim (rel-produce-fn w (produce-fn (br-mssg-witness (f2b w) u) w))
           :hints (("Goal" :in-theory (enable rel-produce-fn))))
   :s
   (= (f2b (produce-fn (br-mssg-witness s u) w)) (f2b w))
   :s
   (= s (f2b w))
   :s
   (= (erankl (produce-fn (br-mssg-witness s u) w)
              u)
      (rankl (br-mssg-witness (f2b w) u)
              (produce-fn (br-mssg-witness (f2b w) u)
                          w)))
   (= (erankl w u)
      (rankl (br-mssg-witness (f2b w) u) w))
   :s))


(in-theory (disable br-mssg-witness bn-join-witness erankl))
(in-theory (disable rel-> exists-v2 exists-v1
                    borfp s-fnp s-bnp join-fn join-bn))

(propertyd web3-2 (s u :s-bn w :s-fn)
  :check-contracts? nil
  :h (^ (rel-B s w)
        (rel-> s u)
        (f2b-refinement-conditions w
                                   (br-mssg-witness (f2b w) u)
                                   (car (bn-join-witness u (f2b w)))))

  (v (^ (rel-> w (exists-v2 u w))
        (rel-B u (exists-v2 u w)))
     (^ (rel-> w (exists-v2 u w))
        (rel-B s (exists-v2 u w))
        (< (erankl (exists-v2 u w) u)
           (erankl w u))))
  :instructions
  (:pro
   (:claim (== s (f2b w)))
   (:claim (rel-step-bn s u))

   (:casesplit (rel-skip-bn (f2b w) u))
   (:prove :hints (("Goal" :use ((:instance web3-uBv2-help1)))))

   (:casesplit (rel-broadcast-bn (f2b w) u))
   (:prove :hints (("Goal" :use ((:instance web3-v2-help7)))))
   
   (:casesplit (rel-subscribe-bn s u))                    
   (:claim (^ (bn-topics-witness s u)
              (mget (car (bn-topics-witness s u)) s)
              (== u (subscribe-bn (car (bn-topics-witness s u))
                                  (cdr (bn-topics-witness s u))
                                  s)))
           :hints (("Goal" :in-theory (enable rel-subscribe-bn))))
   (:claim (rel-> w
                  (subscribe-fn (car (bn-topics-witness s u))
                                (cdr (bn-topics-witness s u)) w))
           :hints (("Goal" :in-theory (enable rel->
                                              rel-step-fn
                                              rel-subscribe-fn))))
   :prove

   (:casesplit (rel-unsubscribe-bn s u))                    
   (:claim (^ (bn-topics-witness u s)
              (mget (car (bn-topics-witness u s)) s)
              (== u (unsubscribe-bn (car (bn-topics-witness u s))
                                    (cdr (bn-topics-witness u s))
                                    s)))
           :hints (("Goal" :in-theory (enable rel-unsubscribe-bn)))) 
   (:claim (rel-> w
                  (unsubscribe-fn (car (bn-topics-witness u s))
                                  (cdr (bn-topics-witness u s))
                                  w))
           :hints (("Goal" :in-theory (enable rel->
                                              rel-step-fn
                                              rel-unsubscribe-fn))))
   :prove

   (:casesplit (rel-join-bn s u))
   (:prove :hints (("Goal" :use ((:instance web3-v2-help5)))))

   (:claim (rel-leave-bn s u))
   (:prove :hints (("Goal" :use ((:instance web3-v2-help6)))))))


;;===========================================================================

(propertyd web3-help1 (s w u :s-fn)
  :check-contracts? nil
  :h (^ (rel-B (f2b s) w)
        (rel-> (f2b s) (f2b u))
        (f2b-refinement-conditions w
                                   (br-mssg-witness (f2b s) (f2b u))
                                   (car (bn-join-witness (f2b u) (f2b s)))))
  (v (^ (rel-> w (exists-v2 (f2b u) w))
        (rel-B (f2b u) (exists-v2 (f2b u) w)))
     (^ (rel-> w (exists-v2 (f2b u) w))
        (rel-B (f2b s) (exists-v2 (f2b u) w))
        (< (erankl (exists-v2 (f2b u) w) (f2b u))
           (erankl w (f2b u)))))
  :instructions
  (:pro
   (:claim (== (f2b w) (f2b s)))
   (:demote 4 5 6 7 8 9)
   (:equiv (f2b s) (f2b w))
   :pro :r :s))



(property web3-3 (s w u :s-fn)
  :check-contracts? nil

  :h (^ (rel-B s w)
        (rel-> s u)
      
        (f2b-refinement-conditions s
                                   (br-mssg-witness (f2b s) (f2b u))
                                   (car (bn-join-witness (f2b u) (f2b s))))
        (f2b-refinement-conditions w
                                   (br-mssg-witness (f2b s) (f2b u))
                                   (car (bn-join-witness (f2b u) (f2b s)))))
  
  (v (^ (rel-> w (exists-v2 (exists-v1 s u) w))
        (rel-B u (exists-v2 (exists-v1 s u) w)))
     
     (^ (rel-> w (exists-v2 (exists-v1 s u) w))
        (rel-B s (exists-v2 (exists-v1 s u) w))
        (< (erankl (exists-v2 (exists-v1 s u) w) u)
           (erankl w u))))
  :instructions
  (:pro
   (:claim (rel-B s (f2b s))
           :hints (("Goal" :use ((:instance b-maps-f2b)))))
   (:claim (s-bnp (f2b s)))
   (:claim (^ (rel-> (f2b s)
                     (exists-v1 s u))
              (rel-B u
                     (exists-v1 s u)))
           :hints (("Goal" :use ((:instance web3-1
                                            (w (f2b s)))))))
   (:claim (== (exists-v1 s u) (f2b u))
           :hints (("Goal" :use ((:instance b-fnbn
                                            (s u)
                                            (w (exists-v1 s u)))))))
   (:demote 18 19)
   (:equiv (exists-v1 s u)
           (f2b u))
   :pro
   
   (:claim (borfp s)
           :hints (("Goal" :use ((:instance fn->borf (x s))))))
   (:claim (borfp (f2b s))
           :hints (("Goal" :use ((:instance bn->borf (x (f2b s)))))))
   (:claim (rel-B (f2b s) s)
           :hints (("Goal" :use ((:instance rel-B-symmetric
                                            (x s) (y (f2b s)))))))
   (:claim (borfp w)
           :hints (("Goal" :use ((:instance fn->borf (x w))))))
   (:claim (rel-B (f2b s) w)
           :hints (("Goal" :use ((:instance rel-B-transitive
                                            (x (f2b s))
                                            (y s) (z w))))))
   
   (:claim (s-bnp (exists-v1 s u)))
   
   (:claim (rel-b s (f2b s))
           :hints (("Goal" :use ((:instance rel-B-symmetric
                                            (x s)
                                            (y (f2b s)))))))

   (:claim (rel-b s w)
           :hints (("Goal" :use ((:instance rel-B-transitive
                                            (x s)
                                            (y (f2b s))
                                            (z w))))))
   (:claim (rel-b (f2b s) w)
           :hints (("Goal" :use ((:instance rel-B-transitive
                                            (x (f2b s))
                                            (y s)
                                            (z w))))))
   
   (:claim (s-bnp (f2b u)))
   (:claim (== (f2b s) (f2b w)))
   (:claim (v (^ (rel-> w (exists-v2 (f2b u) w))
                 (rel-B (f2b u) (exists-v2 (f2b u) w)))
              (^ (rel-> w (exists-v2 (f2b u) w))
                 (rel-B (f2b s) (exists-v2 (f2b u) w))
                 (< (erankl (exists-v2 (f2b u) w) (f2b u))
                    (erankl w (f2b u)))))
           :hints (("Goal" :use ((:instance web3-help1)))))


   (:claim (borfp (exists-v2 (f2b u) w)))
   (= (erankl (exists-v2 (f2b u) w) u)
      (erankl (exists-v2 (f2b u) w) (f2b u))
      :hints (("Goal" :use ((:instance prop=erankl-f2b-u
                                       (s (exists-v2 (f2b u) w)))))))
   (:claim (borfp w))
   (= (erankl w u)
      (erankl w (f2b u))
      :hints (("Goal" :use ((:instance prop=erankl-f2b-u
                                       (s w))))))
   
   (:casesplit (^ (rel-> w (exists-v2 (f2b u) w))
                  (rel-B (f2b u) (exists-v2 (f2b u) w))))

   (:claim (borfp u)
           :hints (("Goal" :use ((:instance fn->borf (x u))))))
   (:claim (borfp (exists-v2 (f2b u) w))
           :hints (("Goal" :use ((:instance fn->borf (x (exists-v2 (f2b u)
                                                                   w)))))))
   (:claim (borfp (f2b u)))
   (:claim (rel-B u (exists-v2 (f2b u) w))
           :hints (("Goal" :use ((:instance rel-B-transitive
                                            (x u)
                                            (y (f2b u))
                                            (z (exists-v2 (f2b u) w)))))))
   :s
   
   (:claim (borfp (exists-v2 (f2b u) w)))
   
   (:claim (^ (rel-> w (exists-v2 (f2b u) w))
              (rel-B (f2b s) (exists-v2 (f2b u) w))
              (< (erankl (exists-v2 (f2b u) w) (f2b u))
                 (erankl w (f2b u)))))
   
   (:claim (rel-B s (exists-v2 (f2b u) w))
           :hints (("Goal" :use ((:instance rel-B-transitive
                                            (x s)
                                            (y (f2b s))
                                            (z (exists-v2 (f2b u) w)))))))
   :s))






(in-theory (e/d (rel->) (exists-v1 exists-v2 rel-B rankl)))


(property prop=rel-B-nil (s w :borf)
  :h (^ (null s)
        (rel-B s w))
  (endp w)
  :hints  (("Goal" :in-theory (enable rel-B f2b f2b-help))))

(property prop=rel-B-cons (s w :borf)
  :h (^ (not (null s))
        (rel-B s w))
  (consp w)
  :hints (("Goal" :in-theory (enable rel-B f2b f2b-help))))

(property prop=empty-rel-step-borf (u :borf)
  :check-contracts? nil
  :h (^ u (rel-> nil u))
  (v (rel-join-bn nil u)
     (rel-join-fn nil u))
  :instructions
  (:pro
   (:casesplit (s-bnp u))
   (:prove :hints (("Goal" :in-theory (enable rel-skip-bn)
                    :use ((:instance prop=empty-rel-step-bn
                                     (s nil))))))
   (:prove :hints (("Goal" :in-theory (enable rel-skip-fn)
                    :use ((:instance prop=empty-rel-step-fn)))))
   ))


(definec exists-nil-v (u :borf) :borf
  :function-contract-hints (("Goal"
                             :instructions
                             (:pro
                              (:claim (borfp (exists-v2 u nil)))
                              (:claim (borfp (exists-v1 nil u)))
                              (:claim (v (rel-join-bn nil u)
                                         (rel-join-fn nil u))
                                      :hints (("Goal"
                                               :use ((:instance prop=empty-rel-step-borf)))))
                              :prove)))
  :ic (^ u (rel-> nil u))
    (cond
     ((s-bnp u) (exists-v2 u nil))
     ((s-fnp u) (exists-v1 nil u))))


(definec exists-cons-v (s u w :borf) :borf
  :ic (^ s
         (rel-B s w)
         (rel-> s u))
  (cond
   ((^ (s-bnp s) (s-bnp w)) u)
   ((^ (s-fnp s) (s-bnp w)) (exists-v1 s u))
   ((^ (s-bnp s) (s-fnp w)) (exists-v2 u w))
   ((^ (s-fnp s) (s-fnp w)) (exists-v2
                             (exists-v1 s u)
                             w))))

(definec exists-v (s u w :borf) :borf
  :function-contract-hints (("Goal" :in-theory
                             (disable exists-nil-v-definition-rule
                                      exists-cons-v-definition-rule)))
  :ic (^ (rel-B s w)
         (rel-> s u))
  (if (null s)
      (if (null u)
          nil
        (exists-nil-v u))
    (exists-cons-v s u w)))

(property prop=cons-s-exists-v (s u w :borf)
  :h (^ s
        (rel-B s w)
        (rel-> s u))
  (== (exists-v s u w)
      (exists-cons-v s u w)))

(in-theory (disable rel-B rel-> exists-v2 exists-v1
                    borfp s-fnp s-bnp join-fn join-bn))

(property prop=exists-cons-v1 (s u w :borf)
  :h (^ s
        (rel-B s w)
        (rel-> s u)
        (s-bnp s)
        (s-bnp w))
  (== (exists-cons-v s u w) u))

(property prop=exists-cons-v2 (s u w :borf)
  :h (^ s
        (rel-B s w)
        (rel-> s u)
        (s-fnp s)
        (s-bnp w))
  (== (exists-cons-v s u w) (exists-v1 s u)))

(property prop=exists-cons-v3 (s u w :borf)
  :h (^ s
        (rel-B s w)
        (rel-> s u)
        (s-bnp s)
        (s-fnp w))
  (== (exists-cons-v s u w) (exists-v2 u w)))

(property prop=exists-cons-v4 (s u w :borf)
  :h (^ s
        (rel-B s w)
        (rel-> s u)
        (s-fnp s)
        (s-fnp w))
  (== (exists-cons-v s u w)
      (exists-v2 (exists-v1 s u) w)))      
  
(in-theory (disable exists-cons-v
                    exists-v1
                    exists-v2))
  

(property web3-nil (s u w :borf)
  :check-contracts? nil
  :h (^ (rel-B s w)
        (rel-> s u)
        (null s))
  (^ (rel-> w (exists-v s u w))
     (rel-B u (exists-v s u w)))
  :instructions
  (:pro
   
   (:claim (== w nil)
           :hints (("Goal" :use ((:instance prop=rel-B-nil)))))
      
   (:casesplit (null u))
   (= u nil)
   (= (exists-v s nil w) nil)
   (:prove :hints (("Goal" :use ((:instance
                                  web3-1 (s nil) (w nil))))))

   (:casesplit (s-fnp u))
   (= (exists-v s u w)
      (exists-v1 nil u))
   (:prove :hints (("Goal" :use ((:instance
                                  web3-1 (s nil) (w nil))))))

   (:claim (s-bnp u))
   (= (exists-v s u w)
      (exists-v2 u nil))
   (:prove :hints (("Goal" :use ((:instance
                                  web3-2 (s nil) (w nil))))))
   ))



(in-theory (disable br-mssg-witness bn-join-witness erankl))

(property web3 (s u w :borf)
  :check-contracts? nil

  :h (^ (rel-B s w)
        (rel-> s u)      

        (=> (s-fnp s)
            (f2b-refinement-conditions s
                                       (br-mssg-witness (f2b s) (f2b u))
                                       (car (bn-join-witness (f2b u)
                                                             (f2b s)))))
        (=> (^ (s-bnp s) (s-fnp w))
            (f2b-refinement-conditions w
                                       (br-mssg-witness (f2b w) u)
                                       (car (bn-join-witness u (f2b w)))))
        (=> (^ (s-fnp s) (s-fnp w))
            (f2b-refinement-conditions w
                                       (br-mssg-witness (f2b s) (f2b u))
                                       (car (bn-join-witness (f2b u)
                                                             (f2b s))))))
  (v (^ (rel-> w (exists-v s u w))
        (rel-B u (exists-v s u w)))
     (^ (rel-> w (exists-v s u w))
        (rel-B s (exists-v s u w))
        (< (erankl (exists-v s u w) u)
           (erankl w u))))
  :instructions
  (:pro
   (:casesplit (null s))
   (:prove :hints (("Goal" :use ((:instance web3-nil)))))

   (:claim s)
   (:claim (consp w)
           :hints (("Goal" :use ((:instance
                                  prop=rel-B-cons)))))
   (= (exists-v s u w)
      (exists-cons-v s u w)
      :hints (("Goal" :use ((:instance prop=cons-s-exists-v)))))
   
   (:casesplit (s-bnp w))
   (:casesplit (s-bnp s))
   (= (exists-cons-v s u w) u
      :hints (("Goal" :use (:instance prop=exists-cons-v1))))
   (= w s)
   (:claim (rel-b u u)
           :hints (("Goal" :use (:instance rel-B-reflexive (x u)))))
   :s

   (:claim (s-fnp s))
   (= (exists-cons-v s u w) (exists-v1 s u)
      :hints (("Goal" :use (:instance prop=exists-cons-v2))))
   (:claim (s-fnp u))
   (:claim (f2b-refinement-conditions s
                                      (br-mssg-witness (f2b s) (f2b u))
                                      (car (bn-join-witness (f2b u) (f2b s)))))
   (:drop 6 7 8 17 18 19 20)
   (:prove :hints (("Goal" :use ((:instance web3-1-help)))))
   
   (:claim (s-fnp w)) 
   (:casesplit (s-bnp s))
   (:claim (! (s-fnp s)))
   (:claim (s-bnp u))
   (= (exists-cons-v s u w) (exists-v2 u w)
      :hints (("Goal" :use ((:instance prop=exists-cons-v3)))))

   (:claim (f2b-refinement-conditions w
                                      (br-mssg-witness (f2b w) u)
                                      (car (bn-join-witness u (f2b w)))))
   (:drop 6 7 8)
   (:prove :hints (("Goal" :use ((:instance web3-2)))))
   
   (:claim (s-fnp s))
   (:claim (s-fnp u))
   (= (exists-cons-v s u w)
      (exists-v2 (exists-v1 s u) w)
      :hints (("Goal" :use ((:instance prop=exists-cons-v4)))))

   (:claim (f2b-refinement-conditions s
                                      (br-mssg-witness (f2b s) (f2b u))
                                      (car (bn-join-witness (f2b u) (f2b s)))))
   (:claim (f2b-refinement-conditions w
                                      (br-mssg-witness (f2b s) (f2b u))
                                      (car (bn-join-witness (f2b u) (f2b s)))))
   (:drop 6 7 8)
   (:prove :hints (("Goal" :use ((:instance web3-3)))))))

