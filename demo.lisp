(in-package "ACL2S")
(include-book "good-fn")

;;---------------------------------------------------
;; Broadcast Network state and transition
;;---------------------------------------------------

;; A Broadcastnet state is a map from peers to their states
(defdata s-bn (map peer ps-bn))

;; Peers are natural numbers
;; Topics are variables
(defdata-alias peer nat)
(defdata-alias topic var)

;; A Broadcastnet peer state tracks topics it publishes in,
;; topics it subscribes to, and messages it has seen.
(defdata ps-bn (record
                (pubs . lot)
                (subs . lot)
                (seen . lom)))

(defdata lot (listof topic))
(defdata lom (listof mssg))

;; A message contains a payload,
;; topic and an originating peer
(defdata mssg (record
               (pld . string)
               (tp . topic)
               (or . peer)))



;; We define the transition relation rel-step-bn as follows : Given Broadcastnet
;; (s-bn) states s and u, peer p, lists of topics pubs, subs and topics,
;; and message m, (rel-step-bn p pubs subs topics m s u) iff one of the
;; several s-bn transitions holds:
;; (rel-skip-bn s u)
;; (rel-broadcast-bn m s u)
;; (rel-subscribe-bn p topics s u)
;; (rel-unsubscribe-bn p topics s u)
;; (rel-leave-bn p s u)
;; (rel-join-bn p pubs subs s u)

;; Each of the above transition relation holds iff u is obtained by
;; applying some enabled BN rule to s.

(definec rel-step-bn (s u :s-bn) :bool
  (v (rel-skip-bn s u)
     (rel-broadcast-bn s u)
     (rel-subscribe-bn s u)
     (rel-unsubscribe-bn s u)
     (rel-leave-bn s u)
     (rel-join-bn s u)))

(definecd rel-skip-bn (s u :s-bn) :bool
  (== u s))

(definecd rel-broadcast-bn (s u :s-bn) :bool
  (^ (br-mssg-witness s u)
     (broadcast-bn-pre (br-mssg-witness s u) s)
     (== u (broadcast (br-mssg-witness s u) s))))

(defdata maybe-mssg (v nil mssg))
;; Finds the message that was broadcast in state s.
(definec br-mssg-witness (s u :s-bn) :maybe-mssg
  (cond
   ((v (endp s) (endp u)) nil)
   ((== (car s) (car u)) (br-mssg-witness (cdr s) (cdr u)))
   (t (car (set-difference-equal (mget :seen (cdar u))
                                 (mget :seen (cdar s)))))))


(definec broadcast-bn-pre (m :mssg s :s-bn) :bool
  (b* ((origin (mget :or m))
       (origin-st (mget origin s)))
    (^ (new-bn-mssgp m s)
       origin-st
       (in (mget :tp m)
           (mget :pubs origin-st)))))

;; A message is broadcast if it is new i.e. not already in the network.
(definecd new-bn-mssgp (m :mssg s :s-bn) :bool
  (v (endp s)
     (^ (! (in m (mget :seen (cdar s))))
        (new-bn-mssgp m (cdr s)))))

(definecd broadcast (m :mssg s :s-bn) :s-bn
  :ic (broadcast-bn-pre m s)
  (broadcast-help m s))

(definecd broadcast-help (m :mssg st :s-bn) :s-bn
  (match st
    (() nil)
    (((p . pst) . rst)
     (cons `(,p . ,(if (in (mget :tp m)
                           (mget :subs pst))
                       (mset :seen
                             (insert-unique m (mget :seen pst))
                             pst)
                     pst))
           (broadcast-help m rst)))))

(definecd rel-subscribe-bn (s u :s-bn) :bool
  (^ (bn-topics-witness s u)
     (mget (car (bn-topics-witness s u)) s)
     (== u (subscribe-bn (car (bn-topics-witness s u))
                         (cdr (bn-topics-witness s u))
                         s))))

(defdata maybe-ptops (v nil (cons peer lot)))
(definec bn-topics-witness (s u :s-bn) :maybe-ptops
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

(definecd subscribe-bn (p :peer topics :lot s :s-bn) :s-bn
  :ic (mget p s)
  (let ((pst (mget p s)))
    (mset p
          (mset :subs (union-equal (mget :subs pst) topics) pst)
          s)))


;; Notice that to find the topics unsubscribed, we simply flip the args to
;; bn-topics-witness
(definecd rel-unsubscribe-bn (s u :s-bn) :bool
  (^ (bn-topics-witness u s)
     (mget (car (bn-topics-witness u s)) s)
     (== u (unsubscribe-bn (car (bn-topics-witness u s))
                           (cdr (bn-topics-witness u s))
                           s))))

(definecd unsubscribe-bn (p :peer topics :lot s :s-bn) :s-bn
  :ic (mget p s)
  (let ((pst (mget p s)))
    (mset p
          (mset :subs (set-difference-equal (mget :subs pst) topics) pst)
          s)))



(definecd rel-join-bn (s u :s-bn) :bool
  (^ (bn-join-witness s u)
     (b* ((p (car (bn-join-witness s u)))
          (pst (cdr (bn-join-witness s u))))
       (^ (! (mget p s))
          (== u (join-bn p
                         (mget :pubs pst)
                         (mget :subs pst)
                         s))))))

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

(definecd join-bn (p :peer pubs subs :lot st :s-bn) :s-bn
  :ic (! (mget p st))
  (mset p (ps-bn pubs subs '()) st))


;; Notice that to find the peer that left, we simply flip the args to
;; bn-topics-witness
(definecd rel-leave-bn (s u :s-bn) :bool
  (^ (bn-join-witness u s)
     (mget (car (bn-join-witness u s)) s)
     (== u (leave-bn (car (bn-join-witness u s)) s))))

(definecd leave-bn (p :peer s :s-bn) :s-bn
  :ic (mget p s)
  (match s
    (((!p . &) . rst) rst)
    ((r . rst) (cons r (leave-bn p rst)))))

;;---------------------------------------------------
;; Floods Network state and transition
;;---------------------------------------------------

;; A Floodnet state is a map from peers to their states
(defdata s-fn (map peer ps-fn))

;; A Floodnet peer state tracks topics it publishes in, topics it subscribes
;; to, neighboring peer subscriptions, pending messages (that are yet to be
;; processed), and messages it has seen.
(defdata ps-fn
  (record  (pubs . lot)
           (subs . lot)            ;; self subscriptions
           (nsubs . topic-lop-map) ;; nbr topic subscriptions
           (pending . lom)
           (seen . lom)))

(defdata topic-lop-map (map topic lop))
(defdata-alias lop nat-list)

;; The FN step relation
(definec rel-step-fn (s u :s-fn) :bool
  (v (rel-skip-fn s u)
     (rel-produce-fn s u)
     (rel-forward-fn1 s u)
     (rel-forward-fn2 s u)
     (rel-subscribe-fn s u)
     (rel-unsubscribe-fn s u)
     (rel-leave-fn s u)
     (rel-join-fn s u)))

(definecd rel-skip-fn (s u :s-fn) :bool
  (== u s))

(definecd rel-produce-fn (s u :s-fn) :bool
  (rel-produce-help-fn s u (fn-pending-mssgs u)))

(definec rel-produce-help-fn (s u :s-fn ms :lom) :bool
  (match ms
    (() nil)
    ((m . rst)
     (v (^ (produce-fn-pre m s)
           (== u (produce-fn m s)))
        (rel-produce-help-fn s u rst)))))

(definec produce-fn-pre (m :mssg s :s-fn) :bool
  (b* ((origin (mget :or m))
       (origin-st (mget origin s)))
    (^ (new-fn-mssgp m s)
       origin-st
       (in (mget :tp m)
           (mget :pubs origin-st)))))

;; A message is produced if it is new i.e. not already in the network.
(definecd new-fn-mssgp (m :mssg s :s-fn) :bool
  (v (endp s)
     (^ (== nil (member-equal m (mget :seen (cdar s))))
        (== nil (member-equal m (mget :pending (cdar s))))
        (new-fn-mssgp m (cdr s)))))

(definecd produce-fn (m :mssg s :s-fn) :s-fn
  :ic (produce-fn-pre m s)
  (mset (mget :or m)
        (add-pending-psfn m
                          (mget (mget :or m) s))
        s))

(definecd add-pending-psfn (m :mssg pst :ps-fn) :ps-fn
  ;; A message already seen is not forwarded.
  ;; We assume that each messages is augmented with a timestamp such that no
  ;; two messages are the same.
  (if (v (member-equal m (mget :pending pst))
         (member-equal m (mget :seen pst)))
      pst
    (mset :pending
          (cons m (mget :pending pst))
          pst)))



;; rel-forward-fn1 and rel-forward-fn2 both relate states after applying
;; forward-fn rule. They differ in the outcome of this rule application. We
;; prove that when
;; (!= (fn-pending-mssgs (forward-fn p m s))
;;     (fn-pending-mssgs s))
;; then
;; (== (fn-pending-mssgs (forward-fn p m s))
;;     (remove-equal m (fn-pending-mssgs s)))
(definecd rel-forward-fn1 (s u :s-fn) :bool
  (let ((m (br-mssg-witness (f2b s) (f2b u)))) ;; message is broadcasted in rel-forward-fn1
    (^ m
       (in m (fn-pending-mssgs s))
       (! (in m (mget :seen (mget (find-forwarder s m) s))))        ;; Invariant
       (!= (fn-pending-mssgs (forward-fn (find-forwarder s m) m s)) ;; CASE
           (fn-pending-mssgs s))
       (^ (mget (mget :or m) s)   ;; CONDITION 1. origin still exists
          (in (mget :tp m)                           ;; while message is pending
              (mget :pubs (mget (mget :or m) s))))
       (== u (forward-fn (find-forwarder s m) m s)))))

(definecd rel-forward-fn2 (s u :s-fn) :bool
  (rel-forward-help-fn2 s u (fn-pending-mssgs s)))

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

;; The peer that forwards the pending message m
(definec find-forwarder (s :s-fn m :mssg) :peer
    :ic (in m (fn-pending-mssgs s))
    :oc (^ (mget (find-forwarder s m) s)
           (in m (mget :pending (mget (find-forwarder s m) s)))
           (! (new-fn-mssgp m s)))
    (match s
      (((p . &)) p)
      (((p . pst) . rst)
       (if (in m (mget :pending pst))
           p
         (find-forwarder rst m)))))


(definecd forward-fn (p :peer m :mssg s :s-fn) :s-fn
  :ic (^ (mget p s)
         (in m (mget :pending (mget p s))))
  (b* ((tp (mssg-tp m))
       (pst (mget p s))
       (nsubs (mget :nsubs pst))
       (fwdnbrs (mget tp nsubs)))
    (forward-help-fn (update-forwarder-fn p m s)
                     fwdnbrs m)))

(definecd forward-help-fn (s :s-fn nbrs :lop m :mssg) :s-fn
  (match s
    (() '())
    (((q . qst) . rst)
     (cons (if (in q nbrs)
               `(,q . ,(add-pending-psfn m qst))
             `(,q . ,qst))
           (forward-help-fn rst nbrs m)))))


(definec update-forwarder-fn (p :peer m :mssg s :s-fn) :s-fn
  (match s
    (() '())
    (((!p . pst) . rst)
     (cons `(,p . ,(forwarder-new-pst pst m)) rst))
    ((r . rst)
     (cons r (update-forwarder-fn p m rst)))))

(definecd forwarder-new-pst (pst :ps-fn m :mssg) :ps-fn
  (mset :seen
        (insert-unique m (mget :seen pst))
        (mset :pending
              (remove-equal m (mget :pending pst))
              pst)))




(definecd rel-subscribe-fn (s u :s-fn) :bool
  (^ (fn-topics-witness s u)
     (mget (car (fn-topics-witness s u)) s)
     (== u (subscribe-fn (car (fn-topics-witness s u))
                         (cdr (fn-topics-witness s u))
                         s))))

;; Based on bn-topics-witness definition 
(definec fn-topics-witness (s u :s-fn) :maybe-ptops
  (bn-topics-witness (f2b s) (f2b u)))

(definecd subscribe-fn (p :peer topics :lot s :s-fn) :s-fn
  :ic (mget p s)
  (let ((pst (mget p s)))
    (set-subs-sfn (ps-fn-nbrs pst)
                  topics
                  p
                  (mset p 
                        (mset :subs (union-equal
                                     (mget :subs pst)
                                     topics)
                              pst)
                        s))))

(definecd set-subs-sfn (nbrs :lop topics :lot p :peer s :s-fn) :s-fn
  (match s
    (() '())
    (((n . pst) . rst)
     (cons `(,n . ,(set-subs-psfn nbrs topics n p pst))
           (set-subs-sfn nbrs topics p rst)))))

(definecd rel-unsubscribe-fn (s u :s-fn) :bool
  (^ (fn-topics-witness u s)
     (mget (car (fn-topics-witness u s)) s)
     (== u (unsubscribe-fn (car (fn-topics-witness u s))
                           (cdr (fn-topics-witness u s))
                           s))))

(definecd unsubscribe-fn (p :peer topics :lot s :s-fn) :s-fn
  :ic (mget p s)
  (let ((pst (mget p s)))
          (set-subs-sfn (ps-fn-nbrs pst)
                                     topics
                                     p
                                     (mset p 
                                           (mset :subs (set-difference-equal
                                                        (mget :subs pst)
                                                        topics)
                                                 pst)
                                           s))))

(definecd rel-join-fn (s u :s-fn) :bool
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


(defdata maybe-ppsfn (v nil
                        (cons peer ps-fn)))

(definec fn-join-witness (s u :s-fn) :maybe-ppsfn
  (b* ((res (bn-join-witness (f2b s) (f2b u)))
       ((when (null res)) nil))
    (cons (car res)
          (mget (car res) u))))

(definecd join-fn (p :peer pubs subs :lot nbrs :lop s :s-fn) :s-fn
  :ic (^ (! (mget p s))
	 (! (in p nbrs)))
  (set-subs-sfn nbrs
                subs
                p
                (mset p
                      (new-joinee-st-fn pubs subs nbrs s)
                      s)))


(definecd rel-leave-fn (s u :s-fn) :bool
  (^ (fn-join-witness u s)
     (mget (car (fn-join-witness u s)) s)
     (== (fn-pending-mssgs (leave-fn (car (fn-join-witness u s)) s))
         (fn-pending-mssgs s))
     (== u (leave-fn (car (fn-join-witness u s)) s))))

(definecd leave-fn (p :peer s :s-fn) :s-fn
  :ic (mget p s)
  (match s
    (() '())
    (((!p . &) . rst) rst)
    ((r . rst) (cons r (leave-fn p rst)))))

;;---------------------------------------------------
;; Commitment refinement map
;; from Floodnetwork State to Broadcastnetwork State
;;---------------------------------------------------

;; peer state refinement map
(definecd f2b-st (ps :ps-fn ms :lom) :ps-bn
  (ps-bn (mget :pubs ps)
         (mget :subs ps)
         (set-difference-equal (mget :seen ps) ms)))

(definec f2b-help (s :s-fn ms :lom) :s-bn
  (if (endp s)
      '()
    (cons `(,(caar s) . ,(f2b-st (cdar s) ms))
          (f2b-help (cdr s) ms))))

;; refinement map f2b : s-fn -> s-bn
(definec f2b (s :s-fn) :s-bn
  (f2b-help s (fn-pending-mssgs s)))


;;---------------------------------------------------
;; Combined States and Transition Relations
;;---------------------------------------------------

;; Combined State
(defdata borf (v s-bn s-fn))

;; Intersection of s-bn and s-fn states is the empty map.
(property prop=s-sb-s-fn-nil (x :s-bn :s-fn)
  (null x))

;;---------------------------------------------------
;; B relation between borf states
;;---------------------------------------------------

;; We define the rel-B relation on a union of s-fn and s-bn states as
;; follows. The refinement theorem will prove that for states s and w
;; such that (rel-B s w), and for states s and u related by some transition
;; relation, there exists a state v such that it is obtained by applying some
;; rule to w, and either uBv or sBv and there is a measure that
;; decreases when going from w to v.
(definec rel-B (x y :borf) :boolean
  (cond
   ((^ (s-fnp x) (s-fnp y)) (== (f2b x) (f2b y)))
   ((^ (s-fnp x) (s-bnp y)) (== (f2b x) y))
   ((^ (s-fnp y) (s-bnp x)) (== (f2b y) x))
   (t (== x y))))

;; rel-B is an equivalence relation

(propertyd rel-B-reflexive (x :borf)
  (rel-B x x))
  
(propertyd rel-B-symmetric (x y :borf)
  (== (rel-B x y)
      (rel-B y x)))

(propertyd rel-B-transitive (x y z :borf)
  :h (^ (rel-B x y)
        (rel-B y z))
  (rel-B x z))

;;---------------------------------------------------
;; Combined Transition relation
;;---------------------------------------------------

;; Relation rel-> is a union of rel-step-fn and rel-step-bn relations
(definec rel-> (s u :borf) :bool
  (v (^ (s-fnp s)
        (s-fnp u)
        (rel-step-fn s u))
     (^ (s-bnp s)
        (s-bnp u)
        (rel-step-bn s u))))

;; NOTICE : the following forms are from f2b-ref2, which is not imported at
;; this time.

;; We are now ready to prove refinement.
;;---------------------------------------------------
;; WEB 1
;;---------------------------------------------------

(property b-maps-f2b (s :s-fn)
  (rel-B s (f2b s)))

;;---------------------------------------------------
;; WEB 2
;;---------------------------------------------------

(definec L (s :borf) :borf
  (match s
    (:s-bn s)
    (:s-fn (f2b s))))

(property web2 (s w :borf)
  :h (rel-B s w)
  (== (L s)
      (L w)))

;;---------------------------------------------------
;; WEB 3
;;---------------------------------------------------

;; exists-v is a witness to the existence of v in our refinement
;; theorem. Given the empty state s, and given (rel-B s w), w is empty
;; as well. So, the only possible transitions from empty w are either
;; skip (producing nil) or join.
;; Otherwise, s and w are non-empty maps.

(definec exists-v (s u w :borf) :borf
  :ic (^ (rel-B s w)
         (rel-> s u))
  (if (null s)
      (if (null u)
          nil
        (exists-nil-v u))
    (exists-cons-v s u w)))

(definec exists-nil-v (u :borf) :borf
  :ic (^ u
         (rel-> nil u))
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

;; Following functions are witnesses to the existence of v in case of
;; non-empty s and w.
(definec exists-v1 (s u :s-fn) :s-bn
  (cond
   ((rel-forward-fn1 s u) (broadcast (br-mssg-witness (f2b s) (f2b u))
                                     (f2b s)))
   ((rel-subscribe-fn s u) (f2b u))
   ((rel-unsubscribe-fn s u) (f2b u))
   ((rel-join-fn s u) (f2b u))
   ((rel-leave-fn s u) (f2b u))
   (t (f2b s))))

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


(definec exists-v21 (u :s-bn w :s-fn) :s-fn
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



;; erankl function is a measure for the second case of our refinement
;; proof, where (rel-B s v)

;; The rank function
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

(definec rankl (m :mssg s :s-fn) :nat
  (if (new-fn-mssgp m s)
      (1+ (len s))
    (m-nct m s)))

(definec m-nct (m :mssg s :s-fn) :nat
  (match s
    (() 0)
    (((& . pst) . rst)
     (+ (if (! (in m (mget :seen pst)))
            1
          0)
        (m-nct m rst)))))



;; Finally, our refinement theorem, along with required conditions in
;; the hypotheses.

;; Currently working on cleaning up this thm, remove refinement conditions
(property web3x (s u w :borf)
  :check-contracts? nil

  :h (^ (rel-B s w)
        (rel-> s u)      

        (=> (s-fnp s)
            (f2b-refinement-conditions s
                                       (br-mssg-witness (f2b s) (f2b u))
                                       (car (bn-join-witness (f2b u)
                                                             (f2b s))))))
  (let ((v (exists-v s u w)))
    (v (^ (rel-> w v)
          (rel-B u v))
       (^ (rel-> w v)
          (rel-B s v)
          (< (erankl v u)
             (erankl w u))))))

