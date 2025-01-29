(in-package "ACL2S")
(include-book "fn")

(defdata keywd1 (enum '(IHAVE IWANT)))
(defdata keywd2 (enum '(GRAFT PRUNE)))
(defdata ctrl-mssg (v (list keywd1 mssg peer)
                      (list keywd2 topic peer)))
(defdata loc (listof ctrl-mssg))
(defdata lolom (listof lom))

(defdata ps-mn
  (record  (pubs . lot)
           (subs . lot)            ;; self subscriptions
           (nsubs . topic-lop-map) ;; nbr topic subscriptions
           (mesh . topic-lop-map)
           (fanout . topic-lop-map)
           (pending . lom)
           (ctrl . loc)
           (rseen . lolom)         ;; movinf window of recently seen messages
           (seen . lom)))

(property ps-mn-check-prop (x :ps-mn)
  (^ (lomp (mget :seen x))
     (lomp (mget :pending x))
     (locp (mget :ctrl x))
     (lolomp (mget :rseen x))
     (topic-lop-mapp (mget :nsubs x))
     (topic-lop-mapp (mget :mesh x))
     (topic-lop-mapp (mget :fanout x))
     (lotp (mget :subs x))
     (lotp (mget :pubs x)))
  :rule-classes :forward-chaining)

(defdata s-mn (map peer ps-mn))
(property s-mn-check (s :s-mn i :peer)
          (=> (mget i s)
              (ps-mnp (mget i s)))
          :rule-classes :forward-chaining)


(property prop=mget-mesh-lopp (p :peer s :s-mn tp :topic)
  :h (mget p s)
  (lopp (mget tp (mget :mesh (mget p s)))))

(property prop=mget-nsubs-lopp (p :peer s :s-mn tp :topic)
  :h (mget p s)
  (lopp (mget tp (mget :nsubs (mget p s)))))

(property prop=mget-fanout-lopp (p :peer s :s-mn tp :topic)
  :h (mget p s)
  (lopp (mget tp (mget :fanout (mget p s)))))



;; MN RULES
(definec skip-mn (s :s-mn) :s-mn
  s)

(definecd add-pending-psmn (m :mssg pst :ps-mn) :ps-mn
  ;; A message already seen is not forwarded.
  ;; We assume that each messages is augmented with a timestamp such that no
  ;; two messages are the same.
  (if (v (in m (mget :pending pst))
         (in m (mget :seen pst)))
      pst
    (mset :pending
          (cons m (mget :pending pst))
          pst)))

(property prop=add-pending-psmn-seen (m :mssg pst :ps-mn)
  (== (mget :seen (add-pending-psmn m pst))
      (mget :seen pst))
  :hints (("Goal" :in-theory (enable add-pending-psmn))))

(property prop=add-pending-psmn-pending (m :mssg pst :ps-mn)
  :h (! (v (in m (mget :pending pst))
           (in m (mget :seen pst))))
  (in m (mget :pending (add-pending-psmn m pst)))
  :hints (("Goal" :in-theory (enable add-pending-psmn))))

(property prop=add-pending-psmn-pending2 (m :mssg pst :ps-mn)
  :h (in m (mget :pending pst))
  (in m (mget :pending (add-pending-psmn m pst)))
  :hints (("Goal" :in-theory (enable add-pending-psmn))))

(definecd new-mn-mssgp (m :mssg s :s-mn) :bool
  :function-contract-hints
  (("Goal" :in-theory (enable acl2::maximal-records-theory)))
  (if (endp s)
      t
    (^ (! (in m (mget :seen (cdar s))))
       (! (in m (mget :pending (cdar s))))
       (new-mn-mssgp m (cdr s)))))

(property new-mssg=>not-seen-peer2 (s :s-mn p :peer m :mssg)
  :h (^ (new-mn-mssgp m s)
        (mget p s))
  (! (v (in m (mget :pending (mget p s)))
        (in m (mget :seen (mget p s)))))
  :hints (("Goal" :in-theory (enable new-mn-mssgp
                                     acl2::maximal-records-theory))))

(definecd produce-mn (m :mssg s :s-mn) :s-mn
  :ic (^ (mget (mget :or m) s)
	 (new-mn-mssgp m s)
         (in (mget :tp m)
             (mget :pubs (mget  (mget :or m) s))))
  (mset (mget :or m)
        (add-pending-psmn m
                          (mget (mget :or m) s))
        s))

;; We try to define all transitions in terms of FN transitions

;; (definecd mnst->fnst-proj (st :ps-mn) :ps-fn
;;   :function-contract-hints (("Goal" :in-theory (enable ps-fnp)))
;;   (ps-fn (mget :pubs st)
;;          (mget :subs st)
;;          (mget :nsubs st)
;;          (mget :pending st)
;;          (mget :seen st)))

;; (definecd mns->fns-proj (s :s-mn) :s-fn
;;   :function-contract-hints (("Goal" :in-theory
;;                              (enable acl2::maximal-records-theory)))
;;   (match s
;;     (() '())
;;     (((q . qst) . rst)
;;      (cons `(,q . ,(mnst->fnst-proj qst))
;;            (mns->fns-proj rst)))))

(definecd add-recent-message (m :mssg rs :lolom) :lolom
  (cons (insert-unique m (car rs))
        (cdr rs)))

(definecd select-d (d :nat ps :lop) :lop
  (if (< d (len ps))
      (take d ps)
    ps))


(definecd update-fanout-mn (d :nat top :topic pst :ps-mn) :ps-mn
  (mset :fanout
        (mset top (select-d d (mget top (mget :nsubs pst)))
              (mget :fanout pst))
        pst))
  

(definecd forwarder-new-pst-mn (pst :ps-mn m :mssg d :nat) :ps-mn
  (mset :rseen
        (add-recent-message m (mget :rseen pst))
        (mset :seen
              (insert-unique m (mget :seen pst))
              (mset :pending
                    (remove-equal m (mget :pending pst))
                    (if (== nil (mget (mget :tp m)
                                      (mget :fanout pst)))
                        (update-fanout-mn d (mget :tp m) pst)
                      pst)))))


(definecd forward-help-mn (s :s-mn nbrs :lop m :mssg) :s-mn
  :function-contract-hints (("Goal" :in-theory
                             (enable acl2::maximal-records-theory)))
  :body-contracts-hints (("Goal" :in-theory (enable add-pending-psmn)))
  (match s
    (() '())
    (((q . qst) . rst)
     (cons (if (in q nbrs)
               `(,q . ,(add-pending-psmn m qst))
             `(,q . ,qst))
           (forward-help-mn rst nbrs m)))))


(propertyd prop=forward-help-mn-cdr (m :mssg nbrs :lop s :s-mn)
  :h (consp s)
  (== (cdr (forward-help-mn s nbrs m))
      (forward-help-mn (cdr s) nbrs m))
  :hints (("Goal" :in-theory (enable forward-help-mn))))

(property prop=forward-help-mn-seen (p :peer s :s-mn nbrs :lop m :mssg)
  :check-contracts? nil
  :h (mget p s)
  (== (mget :seen (mget p (forward-help-mn s nbrs m)))
      (mget :seen (mget p s)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory
                                     forward-help-mn))))

(definec update-forwarder-mn (p :peer m :mssg d :nat s :s-mn) :s-mn
  :function-contract-hints (("Goal" :in-theory
                             (enable acl2::maximal-records-theory)))
  :body-contracts-hints (("Goal" :in-theory
                          (enable forwarder-new-pst-mn)))
  (match s
    (() '())
    (((!p . pst) . rst)
     (cons `(,p . ,(forwarder-new-pst-mn pst m d)) rst))
    ((r . rst)
     (cons r (update-forwarder-mn p m d rst)))))

(property prop=update-forwarder-mn-cdr (p :peer m :mssg d :nat s :s-mn)
  :h (consp s)
  (== (cdr (update-forwarder-mn p m d s))
      (update-forwarder-mn p m d (cdr s)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))


;; (property topic-lop-map-check (tp :topic subs :topic-lop-map)
;;   (lopp (mget tp subs)))

(definecd forward-mn (p :peer m :mssg d :nat s :s-mn) :s-mn
  :body-contracts-hints (("Goal" :in-theory (enable ps-mn)))
  :ic (^ (mget p s)
         (in m (mget :pending (mget p s))))
  (b* ((tp (mssg-tp m))
       (pst (mget p s))
       (mesh-peers (mget tp (mget :mesh pst)))
       (fanout-peers (mget tp (mget :fanout pst)))
       (fwdnbrs (if (in tp (mget :subs pst))
                    mesh-peers
                  (if (== nil fanout-peers)
                      (select-d d (mget tp (mget :nsubs pst)))
                    fanout-peers))))
    (forward-help-mn (update-forwarder-mn p m d s) fwdnbrs m)))

(property prop=forward-mn-cdr (p :peer m :mssg d :nat s :s-mn)
  :check-contracts? nil
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (mget p (cdr s)))
  (== (forward-mn p m d (cdr s))
      (cdr (forward-mn p m d s)))
  :hints (("Goal" :in-theory (enable forward-mn
                                     forward-help-mn
                                     acl2::maximal-records-theory))))


(definecd set-subs-psmn (nbrs :lop topics :lot n p :peer pst :ps-mn) :ps-mn
  (if (in n nbrs)
      (mset :nsubs
            (set-subs topics p (mget :nsubs pst) '()) pst)
    pst))

(property prop=set-subs-psmn-check (nbrs :lop topics :lot n p :peer pst :ps-mn)
  (^ (== (mget :pubs (set-subs-psmn nbrs topics n p pst))
         (mget :pubs pst))
     (== (mget :subs (set-subs-psmn nbrs topics n p pst))
         (mget :subs pst))
     (== (mget :seen (set-subs-psmn nbrs topics n p pst))
         (mget :seen pst))
     (== (mget :pending (set-subs-psmn nbrs topics n p pst))
         (mget :pending pst))) 
  :hints (("Goal" :in-theory (enable set-subs-psmn))))


;; Given a peer p and topics it subscribes to, share p subs with its
;; neighboring peers
(definecd set-subs-smn (nbrs :lop topics :lot p :peer s :s-mn)
  :s-mn
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (match s
    (() '())
    (((n . pst) . rst)
     (cons `(,n . ,(set-subs-psmn nbrs topics n p pst))
           (set-subs-smn nbrs topics p rst)))))

(property prop=cdr-set-subs-smn (nbrs :lop subs :lot p :peer s
                                                   :s-mn)
  (== (cdr (set-subs-smn nbrs subs p s))
      (set-subs-smn nbrs subs p (cdr s)))
  :hints (("Goal" :in-theory (enable set-subs-smn))))

;; Calculate nsubs, given neighbors in a mn state
(definecd calc-nsubs-mn (nbrs :lop st :s-mn acc :topic-lop-map) :topic-lop-map
  (match nbrs
    (() acc)
    ((n . rst) (b* ((pst (mget n st))
                    ((when (null pst))
                     (calc-nsubs-mn rst st acc)))
                 (calc-nsubs-mn rst
                                st
                                (set-subs (mget :subs pst)
                                                       n
                                                       acc
                                                       '()))))))

(sig set-difference-equal ((listof :a) (listof :a)) => (listof :a))
(sig union-equal ((listof :a) (listof :a)) => (listof :a))


(definecd ps-mn-nbrs (pst :ps-mn) :lop
  (ps-fn-nbrs-help (mget :nsubs pst) '()))


(definecd add-ctrl-mn (cm :ctrl-mssg pst :ps-mn) :ps-mn
    (mset :ctrl
          (cons cm (mget :ctrl pst))
          pst))

(definecd snd-grapru-tp-mn (i :peer tp :topic nbrs :lop gp :bool s :s-mn) :s-mn
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (match s
    (() '())
    (((p . pst) . rst)
     `((,p . ,(if (in p nbrs)
                  (if gp
                      (add-ctrl-mn `(GRAFT ,tp ,i) pst)
                    (add-ctrl-mn `(PRUNE ,tp ,i) pst))
                pst))
       . ,(snd-grapru-tp-mn i tp nbrs gp rst)))))

(definecd snd-grapru-mn (i :peer mesh :topic-lop-map gp :bool s :s-mn) :s-mn
  (match mesh
    (() s)
    (((tp . nbrs) . rst)
     (snd-grapru-mn i rst gp (snd-grapru-tp-mn i tp nbrs gp s)))))

  
(definec new-joinee-st-mn (pubs subs :lot nbrs :lop mesh :topic-lop-map s :s-mn) :ps-mn
  :function-contract-hints (("Goal" :in-theory (enable ps-mnp)))
  (ps-mn pubs subs (calc-nsubs-mn nbrs s '()) mesh '() '()
         '() '() '()))

(definecd join-mn (p :peer pubs subs :lot nbrs :lop mesh :topic-lop-map s :s-mn) :s-mn
  :ic (! (mget p s))
  (set-subs-smn nbrs
                subs
                p
                (mset p
                      (new-joinee-st-mn pubs subs nbrs mesh s)
                      (snd-grapru-mn p mesh t s))))

(definecd calc-mesh-mn (d :nat topics :lot pst :ps-mn acc :topic-lop-map) :topic-lop-map
  (match topics
    (() acc)
    ((tp . rst)
     (calc-mesh-mn d rst pst
                   (let ((fnbrs (mget tp (mget :fanout pst)))
                         (nbrs (mget tp (mget :nsubs pst))))
                     (mset tp
                           (app fnbrs
                                (select-d (if (< d (len fnbrs))
                                              0
                                            (- d (len fnbrs)))
                                          (set-difference-equal nbrs fnbrs)))
                           acc))))))

(definecd subscribe-mn (p :peer topics :lot d :nat st :s-mn) :s-mn
  :function-contract-hints (("Goal" :in-theory (enable ps-mnp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-mnp)))
  :ic (mget p st)
  (b* ((pst (mget p st))
       (mesh (calc-mesh-mn d topics pst '())))
    (set-subs-smn (ps-mn-nbrs pst)
                  topics
                  p
                  (mset p 
                        (mset :subs (union-equal (mget :subs pst)
                                                 topics)
                              pst)
                        (snd-grapru-mn p mesh t st)))))


(definecd remove-topic-map (tp :topic m :topic-lop-map) :topic-lop-map
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (match m
    (() '())
    (((!tp . &) . rst) rst)
    ((r . rst) (cons r
                     (remove-topic-map tp rst)))))

(definecd remove-topics-map (tps :lot m :topic-lop-map) :topic-lop-map
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (match tps
    (() '())
    ((tp . rst) (remove-topics-map rst (remove-topic-map tp m)))))


(definecd retain-topics-map (tps :lot m :topic-lop-map acc :topic-lop-map) :topic-lop-map
  (match tps
    (() '())
    ((tp . rst) (retain-topics-map rst m (mset tp (mget tp m) acc)))))

(definecd unsubscribe-mn (p :peer topics :lot st :s-mn) :s-mn
  :function-contract-hints (("Goal" :in-theory (enable ps-mnp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-mnp)))
  :ic (mget p st)
  (let ((pst (mget p st)))
          (set-subs-smn (ps-mn-nbrs pst)
                                     topics
                                     p
                                     (mset p
                                           (mset :subs (set-difference-equal
                                                        (mget :subs pst)
                                                        topics)
                                                 (mset :mesh
                                                       (remove-topics-map
                                                        topics
                                                        (mget :mesh pst))
                                                       pst))
                                           (snd-grapru-mn p (retain-topics-map
                                                             topics (mget :mesh pst) nil)
                                                          nil
                                                          st)))))

(definecd leave-mn-help (p :peer s :s-mn) :s-mn
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (match s
    (() '())
    (((!p . &) . rst) rst)
    ((r . rst) (cons r (leave-mn-help p rst)))))

(definecd leave-mn (p :peer s :s-mn) :s-mn
  :ic (mget p s)
  (leave-mn-help p s))



(definecd pld-req-mn (i :peer cm :ctrl-mssg s :s-mn) :s-mn
  :ic (^ (mget i s)
         (== 'IHAVE (first cm))
         (mget (third cm) s)
         (in cm (mget :ctrl (mget i s))))
  (mset i
        (mset :ctrl
              (remove-equal cm (mget :ctrl (mget i s)))
              (mget i s))
        (mset (third cm)
              (mset :ctrl
                    (cons `(IWANT ,(second cm) ,i)
                          (mget :ctrl (mget (third cm) s)))
                    (mget (third cm) s))
              s)))


(definecd pld-snd-mn (i :peer cm :ctrl-mssg s :s-mn) :s-mn
  :ic (^ (mget i s)
         (== 'IWANT (first cm))
         (mget (third cm) s)
         (in cm (mget :ctrl (mget i s))))
  (mset i
        (mset :ctrl
              (remove-equal cm (mget :ctrl (mget i s)))
              (mget i s))
        (mset (third cm)
              (add-pending-psmn (second cm) (mget (third cm) s))
              s)))


(definecd prune-mn (i :peer cm :ctrl-mssg s :s-mn) :s-mn
  :ic (^ (mget i s)
         (in cm (mget :ctrl (mget i s)))
         (== 'PRUNE (first cm)))
  (b* ((pst (mget i s))
       (mesh (mget :mesh pst))
       (tp (second cm))
       (j (third cm)))
    (mset i
          (mset :mesh
                (mset tp
                      (remove-equal j (mget tp mesh))
                      mesh)
                pst)
          s)))


(definecd graft-help-mn (i :peer cm :ctrl-mssg s :s-mn) :s-mn
  :ic (^ (mget i s)
         (in cm (mget :ctrl (mget i s)))
         (== 'GRAFT (first cm))
         (mget (third cm) s))
  (b* ((pst (mget i s))
       (mesh (mget :mesh pst))
       (tp (second cm))
       (j (third cm)))
    (mset i
          (mset :ctrl
                (remove-equal cm (mget :ctrl pst))
                (if (in tp (mget :subs pst))
                    (mset :mesh
                          (mset tp
                                (cons j (mget tp mesh))
                                mesh)
                          pst)
                  pst))
          s)))

(definecd graft-mn (i :peer cm :ctrl-mssg s :s-mn) :s-mn
  :ic (^ (mget i s)
         (in cm (mget :ctrl (mget i s)))
         (== 'GRAFT (first cm))
         (mget (third cm) s))
  (b* ((pst (mget i s))
       (tp (second cm))
       (j (third cm)))
    (if (in tp (mget :subs pst))
        (graft-help-mn i cm s)
      (mset j
            (mset :ctrl
                  (cons `(PRUNE ,tp ,i)
                        (mget :ctrl (mget j s)))
                  (mget j s))
            (graft-help-mn i cm s)))))
  
                    
(definecd gossip-help1-mn (i :peer cm :ctrl-mssg nbrs :lop s :s-mn) :s-mn
  :function-contract-hints (("Goal" :in-theory (e/d
                                                (acl2::maximal-records-theory)
                                                (ctrl-mssgp
                                                 ps-mnp))))
  (match s
    (() '())
    (((p . pst) . rst)
     `((,p . ,(if (in p nbrs)
                  (add-ctrl-mn cm pst)
                pst))
       . ,(gossip-help1-mn i cm nbrs rst)))))

(property prop=gossip-help1-mn-mget (i :peer cm :ctrl-mssg nbrs :lop s :s-mn)
  :h (mget i s)
  (mget i (gossip-help1-mn i cm nbrs s))
  :hints (("Goal" :in-theory (e/d (gossip-help1-mn
                                   acl2::maximal-records-theory)
                                  (ctrl-mssgp
                                   ps-mnp)))))

(definecd gossip-mn (i :peer ms :lom d :nat s :s-mn) :s-mn
  :ic (mget i s)
  :function-contract-hints (("Goal" :in-theory
                             (enable acl2::maximal-records-theory)))
  (match ms
    (() s)
    ((m . rst)
     (b* ((pst (mget i s))
          (tp (mget :tp m))
          (nbrs
           (select-d d (set-difference-equal
                        (mget tp (mget :nsubs pst))
                        (app (mget tp (mget :mesh pst))
                             (mget tp (mget :fanout pst)))))))
       (gossip-mn i rst d (gossip-help1-mn i `(IHAVE ,m ,i) nbrs s))))))


(definecd fanout-maint-help2-mn  (ch :bool tp :topic d :nat pst :ps-mn) :ps-mn
  (b* ((fanout (mget :fanout pst))
        (tpf (mget tp fanout)))
    (mset :fanout
          (mset tp
                (if ch
                    '()
                  (if (< (len tpf) d)
                      (append (select-d (- d (len tpf))
                                        (set-difference-equal
                                         (mget tp (mget :nsubs pst))
                                         tpf))
                              tpf)
                    tpf))
                fanout)
          pst)))

(definecd fanout-maint-help1-mn (i :peer ch :bool tp :topic d :nat s :s-mn) :s-mn
  :ic (mget i s)
  (let ((pst (mget i s)))
    (mset i
          (fanout-maint-help2-mn ch tp d pst)
          s)))

(property prop=fanout-maint-help1-mn-mget (i :peer ch :bool tp :topic d :nat s :s-mn)
  :h (mget i s)
  (mget i (fanout-maint-help1-mn i ch tp d s))
  :instructions
  (:pro
   (:dv 2) (:r 2) :top :s :bash
   ))
  

(definecd fanout-maint-mn (i :peer ch :bool tps :lot d :nat s :s-mn) :s-mn
  :ic (mget i s)
  (match tps
    (() s)
    ((tp . rst) 
     (fanout-maint-mn i ch rst d
                      (fanout-maint-help1-mn i ch tp d s)))))


(property prop=fanout-maint-mn-mget (i :peer ch :bool tps :lot d :nat
                                       s :s-mn)
  :h (mget i s)
  (mget i (fanout-maint-mn i ch tps d s))
  :hints (("Goal" :in-theory (enable fanout-maint-mn))))

(property prop=alist-keys-topic-lop-map (m :topic-lop-map)
  (lotp (alist-keys m)))

(definec app-msg-list (rs :lolom) :lom
  (match rs
    (() '())
    ((ms . rst) (binary-append ms
                               (app-msg-list rst)))))


(definecd hbm-mn (i :peer ch :bool d w :nat s :s-mn) :s-mn
  :ic (mget i s)
  (b* ((pst (mget i s))
       (fanout-tps (alist-keys
                    (mget :fanout pst)))
       (s (fanout-maint-mn i ch fanout-tps d s))
       (rs (mget :rseen pst))
       (gs-ms (app-msg-list
               (if (< w (len rs))
                   (take w rs)
                 rs)))
       (s (gossip-mn i gs-ms d s)))
    s))












;; These are in HBM




;; (definecd add-mesh-mn (p q :peer s :s-mn tp :topic) :s-mn
;;   :body-contracts-hints (("Goal" :use (prop=mget-nsubs-lopp)))
;;   :ic (^ (mget p s)
;;          (mget q s)
;;          (in tp (mget :subs (mget p s)))
;;          (in tp (mget :subs (mget q s)))
;;          (in q (mget tp (mget :nsubs (mget p s))))
;;          (! (in q (mget tp (mget :mesh (mget p s))))))
;;   (let ((pst (mget p s))
;;         (qst (mget q s)))
;;     (mset p
;;           (mset :mesh
;;                 (mset tp
;;                       (cons q (mget tp
;;                                     (mget :mesh pst)))
;;                       (mget :mesh pst))
;;                 pst)
;;           (mset q
;;                 (mset :mesh
;;                       (mset tp
;;                             (cons p (mget tp
;;                                           (mget :mesh qst)))
;;                             (mget :mesh qst))
;;                       qst)
;;                 s))))


;; (definecd prune-mesh-mn (p q :peer s :s-mn tp :topic) :s-mn
;;   :body-contracts-hints (("Goal" :use (prop=mget-nsubs-lopp)))
;;   :ic (^ (mget p s)
;;          (mget q s)
;;          (in tp (mget :subs (mget p s)))
;;          (in tp (mget :subs (mget q s)))
;;          (in q (mget tp (mget :nsubs (mget p s))))
;;          (! (in q (mget tp (mget :mesh (mget p s))))))
;;   (let ((pst (mget p s))
;;         (qst (mget q s)))
;;     (mset p
;;           (mset :mesh
;;                 (mset tp
;;                       (remove-equal q (mget tp
;;                                             (mget :mesh pst)))
;;                       (mget :mesh pst))
;;                 pst)
;;           (mset q
;;                 (mset :mesh
;;                       (mset tp
;;                             (remove-equal p (mget tp
;;                                                   (mget :mesh qst)))
;;                             (mget :mesh qst))
;;                       qst)
;;                 s))))


;; (definecd add-fanout-mn (p q :peer s :s-mn tp :topic) :s-mn
;;   :body-contracts-hints (("Goal" :use (prop=mget-mesh-lopp
;;                                        prop=mget-fanout-lopp)))
;;   :ic (^ (mget p s)
;;          (mget q s)
;;          (in tp (mget :pubs (mget p s)))
;;          (! (in tp (mget :subs (mget p s))))
;;          (in q (mget tp (mget :nsubs (mget p s))))
;;          (! (in q (mget tp (mget :mesh (mget p s)))))
;;          (! (in q (mget tp (mget :fanout (mget p s))))))
;;   (b* ((pst (mget p s))
;;        (fanout (mget :fanout pst)))
;;     (mset p
;;           (mset :fanout
;;                 (mset tp
;;                       (cons q (mget tp fanout))
;;                       fanout)
;;                 pst)
;;           s)))


;; (definecd prune-fanout-mn (p q :peer s :s-mn tp :topic) :s-mn
;;   :body-contracts-hints (("Goal" :use (prop=mget-mesh-lopp
;;                                        prop=mget-fanout-lopp)))
;;   :ic (^ (mget p s)
;;          (mget q s)
;;          (in tp (mget :pubs (mget p s)))
;;          (! (in tp (mget :subs (mget p s))))
;;          (in q (mget tp (mget :nsubs (mget p s))))
;;          (! (in q (mget tp (mget :mesh (mget p s)))))
;;          (! (in q (mget tp (mget :fanout (mget p s))))))
;;   (b* ((pst (mget p s))
;;        (fanout (mget :fanout pst)))
;;     (mset p
;;           (mset :fanout
;;                 (mset tp
;;                       (remove-equal q (mget tp fanout))
;;                       fanout)
;;                 pst)
;;           s)))

;; (definecd update-scores-mn (p :peer ptscore :pt-score s :s-mn) :s-mn
;;   :ic (mget p s)
;;   (mset p
;;         (mset :ptscore
;;               ptscore
;;               (mget p s))
;;         s))

;; (definec score-based-prunes-mn (p q :peer tp :topic ptscore :pt-score s :s-mn)
;;   :s-mn
;;   :body-contracts-hints (("Goal" :use (prop=mget-nsubs-lopp)))
;;   :ic (^ (mget p s)
;;          (mget q s)
;;          (in tp (mget :subs (mget p s)))
;;          (in tp (mget :subs (mget q s)))
;;          (in q (mget tp (mget :nsubs (mget p s))))
;;          (! (in q (mget tp (mget :mesh (mget p s)))))
;;          (mget `(,q . ,tp) ptscore))
;;   (if (< (mget `(,q . ,tp) ptscore) 0)
;;       (prune-mesh-mn p q s tp)
;;     s))  

;; (definec step-mn (p :peer pubs subs ts :lot nbrs :lop m :mssg s :s-mn i :nat) :s-mn
;;   (if (mget p s)
;;       (match (mod i 6)
;;         (0 (skip-mn s))
;;         (1 (subscribe-mn p ts s))
;;         (2 (unsubscribe-mn p ts s))
;;         (3 (leave-mn p s))
;;         (4 (if (^ (mget p s)
;;                   (in m (mget :pending (mget p s))))
;;                (forward-mn p m s)
;;              (skip-mn s)))
;;         (5 (if (^ (mget (mget :or m) s)
;;                   (new-mn-mssgp m s)
;;                   (in (mget :tp m)
;;                       (mget :pubs (mget (mget :or m) s))))
;;                (produce-mn m s)
;;              (skip-mn s))))
;;     (match (mod i 6)
;;       (0 (skip-mn s))
;;       (& (join-mn p pubs subs nbrs s)))))
