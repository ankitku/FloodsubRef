(in-package "ACL2S")
(include-book "mn")

(defdata p-score (map peer rational))

(defdata ps-gpn
  (record  (pubs . lot)
           (subs . lot)            ;; self subscriptions
           (nsubs . topic-lop-map) ;; nbr topic subscriptions
           (mesh . topic-lop-map)
           (fanout . topic-lop-map)
           (pending . lom)
           (ctrl . loc)
           (ptscore . pt-score)
           (pscore . p-score)
           (seen . lom)))

(property ps-gpn-check-prop (x :ps-gpn)
  (^ (lomp (mget :seen x))
     (lomp (mget :pending x))
     (locp (mget :ctrl x))
     (topic-lop-mapp (mget :nsubs x))
     (topic-lop-mapp (mget :mesh x))
     (topic-lop-mapp (mget :fanout x))
     (pt-scorep (mget :ptscore x))
     (p-scorep (mget :pscore x))
     (lotp (mget :subs x))
     (lotp (mget :pubs x)))
  :rule-classes :forward-chaining)

(defdata s-gpn (map peer ps-gpn))
(property s-gpn-check (s :s-gpn i :peer)
          (=> (mget i s)
              (ps-gpnp (mget i s)))
          :rule-classes :forward-chaining)

;; GPN RULES
(definec skip-gpn (s :s-gpn) :s-gpn
  s)

(definecd add-pending-psgpn (m :mssg pst :ps-gpn) :ps-gpn
  ;; A message already seen is not forwarded.
  ;; We assume that each messages is augmented with a timestamp such that no
  ;; two messages are the same.
  (if (v (member-equal m (mget :pending pst))
         (member-equal m (mget :seen pst)))
      pst
    (mset :pending
          (cons m (mget :pending pst))
          pst)))

(property prop=add-pending-psgpn-seen (m :mssg pst :ps-gpn)
  (== (mget :seen (add-pending-psgpn m pst))
      (mget :seen pst))
  :hints (("Goal" :in-theory (enable add-pending-psgpn))))

(property prop=add-pending-psgpn-pending (m :mssg pst :ps-gpn)
  :h (! (v (member-equal m (mget :pending pst))
           (member-equal m (mget :seen pst))))
  (in m (mget :pending (add-pending-psgpn m pst)))
  :hints (("Goal" :in-theory (enable add-pending-psgpn))))

(property prop=add-pending-psgpn-pending2 (m :mssg pst :ps-gpn)
  :h (in m (mget :pending pst))
  (in m (mget :pending (add-pending-psgpn m pst)))
  :hints (("Goal" :in-theory (enable add-pending-psgpn))))

(encapsulate ()
  (local
   (property prop=in-member (x :tl m :all)
     (iff (in m x)
          (member-equal m x))))
  (property prop=add-pending-psgpn-pending3 (m :mssg pst :ps-gpn)
    :h (in m (mget :pending pst))
    (== (mget :pending (add-pending-psgpn m pst))
        (mget :pending pst))
    :hints (("Goal" :in-theory (enable add-pending-psgpn)))))

(definecd new-gpn-mssgp (m :mssg s :s-gpn) :bool
  :function-contract-hints
  (("Goal" :in-theory (enable acl2::maximal-records-theory)))
  (if (endp s)
      t
    (^ (== nil (member-equal m (mget :seen (cdar s))))
       (== nil (member-equal m (mget :pending (cdar s))))
       (new-gpn-mssgp m (cdr s)))))

(property new-mssg=>not-seen-peer3 (s :s-gpn p :peer m :mssg)
  :h (^ (new-gpn-mssgp m s)
        (mget p s))
  (! (v (member-equal m (mget :pending (mget p s)))
        (member-equal m (mget :seen (mget p s)))))
  :hints (("Goal" :in-theory (enable new-gpn-mssgp
                                     acl2::maximal-records-theory))))

(definecd produce-gpn (m :mssg st :s-gpn) :s-gpn
  :ic (^ (mget (mget :or m) st)
	 (new-gpn-mssgp m st)
         (in (mget :tp m)
             (mget :pubs (mget  (mget :or m) st))))
  (mset (mget :or m)
        (add-pending-psgpn m
                          (mget (mget :or m) st))
        st))

(definecd forwarder-new-pst-gpn (pst :ps-gpn m :mssg) :ps-gpn
  (mset :seen
        (insert-unique m (mget :seen pst))
        (mset :pending
              (remove-equal m (mget :pending pst))
              pst)))

(definecd forward-help-gpn (s :s-gpn nbrs :lop m :mssg) :s-gpn
  :function-contract-hints (("Goal" :in-theory
                             (enable acl2::maximal-records-theory)))
  :body-contracts-hints (("Goal" :in-theory
                          (enable add-pending-psgpn)))
  (match s
    (() '())
    (((q . qst) . rst)
     (cons (if (in q nbrs)
               `(,q . ,(add-pending-psgpn m qst))
             `(,q . ,qst))
           (forward-help-gpn rst nbrs m)))))


(propertyd prop=forward-help-gpn-cdr (m :mssg nbrs :lop s :s-gpn)
  :h (consp s)
  (== (cdr (forward-help-gpn s nbrs m))
      (forward-help-gpn (cdr s) nbrs m))
  :hints (("Goal" :in-theory (enable forward-help-gpn))))

(property prop=forward-help-gpn-seen (p :peer s :s-gpn nbrs :lop m :mssg)
  :check-contracts? nil
  :h (mget p s)
  (== (mget :seen (mget p (forward-help-gpn s nbrs m)))
      (mget :seen (mget p s)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory
                                     forward-help-gpn))))


(definec update-forwarder-gpn (p :peer m :mssg s :s-gpn) :s-gpn
  :function-contract-hints (("Goal" :in-theory
                             (enable acl2::maximal-records-theory)))
  :body-contracts-hints (("Goal" :in-theory
                          (enable forwarder-new-pst-gpn)))
  (match s
    (() '())
    (((!p . pst) . rst)
     (cons `(,p . ,(forwarder-new-pst-gpn pst m)) rst))
    ((r . rst)
     (cons r (update-forwarder-gpn p m rst)))))

(propertyd prop=update-forwarder-gpn-cdr (p :peer m :mssg s :s-gpn)
  :h (consp s)
  (== (cdr (update-forwarder-gpn p m s))
      (update-forwarder-gpn p m (cdr s)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))


(property topic-lop-map-check (tp :topic subs :topic-lop-map)
  (lopp (mget tp subs)))

(definecd forward-gpn (p :peer m :mssg s :s-gpn) :s-gpn
  :body-contracts-hints (("Goal" :in-theory (enable ps-gpn)))
  :ic (^ (mget p s)
         (in m (mget :pending (mget p s))))
  (b* ((tp (mssg-tp m))
       (pst (mget p s))
       (nsubs (mget :nsubs pst))
       (fwdnbrs (mget tp nsubs)))
    (forward-help-gpn (update-forwarder-gpn p m s) fwdnbrs m)))

(property prop=forward-gpn-cdr (p :peer m :mssg s :s-gpn)
  :check-contracts? nil
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (mget p (cdr s)))
  (== (forward-gpn p m (cdr s))
      (cdr (forward-gpn p m s)))
  :hints (("Goal" :in-theory (enable forward-gpn
                                     forward-help-gpn
                                     acl2::maximal-records-theory))))

(definecd set-subs-psgpn (nbrs :lop topics :lot n p :peer pst :ps-gpn) :ps-gpn
  (if (in n nbrs)
      (mset :nsubs (set-subs topics p (mget :nsubs pst) '()) pst)
    pst))

(property prop=set-subs-psgpn-check (nbrs :lop topics :lot n p :peer pst :ps-gpn)
  (^ (== (mget :pubs (set-subs-psgpn nbrs topics n p pst))
         (mget :pubs pst))
     (== (mget :subs (set-subs-psgpn nbrs topics n p pst))
         (mget :subs pst))
     (== (mget :seen (set-subs-psgpn nbrs topics n p pst))
         (mget :seen pst))
     (== (mget :pending (set-subs-psgpn nbrs topics n p pst))
         (mget :pending pst))) 
  :hints (("Goal" :in-theory (enable set-subs-psgpn))))


;; Given a peer p and topics it subscribes to, share p subs with its
;; neighboring peers
(definecd set-subs-sgpn (nbrs :lop topics :lot p :peer s :s-gpn)
  :s-gpn
  :timeout 600
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (match s
    (() '())
    (((n . pst) . rst)
     (cons `(,n . ,(set-subs-psgpn nbrs topics n p pst))
           (set-subs-sgpn nbrs topics p rst)))))

(property prop=cdr-set-subs-sgpn (nbrs :lop subs :lot p :peer s
                                                   :s-gpn)
  (== (cdr (set-subs-sgpn nbrs subs p s))
      (set-subs-sgpn nbrs subs p (cdr s)))
  :hints (("Goal" :in-theory (enable set-subs-sgpn))))

;; Calculate nsubs, given neighbors in a gpn state
(definecd calc-nsubs-gpn (nbrs :lop st :s-gpn acc :topic-lop-map) :topic-lop-map
  (match nbrs
    (() acc)
    ((n . rst) (b* ((pst (mget n st))
                    ((when (null pst))
                     (calc-nsubs-gpn rst st acc)))
                 (calc-nsubs-gpn rst
                                st
                                (set-subs (mget :subs pst)
                                                       n
                                                       acc
                                                       '()))))))

(sig set-difference-equal ((listof :a) (listof :a)) => (listof :a))
(sig union-equal ((listof :a) (listof :a)) => (listof :a))


(definecd ps-gpn-nbrs (pst :ps-gpn) :lop
  (ps-fn-nbrs-help (mget :nsubs pst) '()))

(definec new-joinee-st-gpn (pubs subs :lot nbrs :lop s :s-gpn) :ps-gpn
  :function-contract-hints (("Goal" :in-theory (enable ps-gpnp)))
  (ps-gpn pubs subs (calc-nsubs-gpn nbrs s '()) '() '() '()
          '() '() '() '()))

(definecd join-gpn (p :peer pubs subs :lot nbrs :lop s :s-gpn) :s-gpn
  :ic (! (mget p s))
  (set-subs-sgpn nbrs
                 subs
                 p
                 (mset p
                       (new-joinee-st-gpn pubs subs nbrs s)
                       s)))

(definecd subscribe-gpn (p :peer topics :lot st :s-gpn) :s-gpn
  :function-contract-hints (("Goal" :in-theory (enable ps-gpnp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-gpnp)))
  :ic (mget p st)
  (let ((pst (mget p st)))
    (set-subs-sgpn (ps-gpn-nbrs pst)
                  topics
                  p
                  (mset p 
                        (mset :subs (union-equal (mget :subs pst)
                                                 topics)
                              pst)
                        st))))

(definecd unsubscribe-gpn (p :peer topics :lot st :s-gpn) :s-gpn
  :function-contract-hints (("Goal" :in-theory (enable ps-gpnp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-gpnp)))
  :ic (mget p st)
  (let ((pst (mget p st)))
          (set-subs-sgpn (ps-gpn-nbrs pst)
                                     topics
                                     p
                                     (mset p 
                                           (mset :subs (set-difference-equal
                                                        (mget :subs pst)
                                                        topics)
                                                 pst)
                                           st))))

(definecd leave-gpn-help (p :peer s :s-gpn) :s-gpn
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (match s
    (() '())
    (((!p . &) . rst) rst)
    ((r . rst) (cons r (leave-gpn-help p rst)))))

(definecd leave-gpn (p :peer s :s-gpn) :s-gpn
  :ic (mget p s)
  (leave-gpn-help p s))


(property prop=mget-mesh-lopp-gpn (p :peer s :s-gpn tp :topic)
  :h (mget p s)
  (lopp (mget tp (mget :mesh (mget p s)))))

(property prop=mget-nsubs-lopp-gpn (p :peer s :s-gpn tp :topic)
  :h (mget p s)
  (lopp (mget tp (mget :nsubs (mget p s)))))

(property prop=mget-fanout-lopp-gpn (p :peer s :s-gpn tp :topic)
  :h (mget p s)
  (lopp (mget tp (mget :fanout (mget p s)))))


(definecd add-mesh-gpn (p q :peer s :s-gpn tp :topic) :s-gpn
  :body-contracts-hints (("Goal" :use (prop=mget-nsubs-lopp-gpn)))
  :ic (^ (mget p s)
         (mget q s)
         (in tp (mget :subs (mget p s)))
         (in tp (mget :subs (mget q s)))
         (in q (mget tp (mget :nsubs (mget p s))))
         (! (in q (mget tp (mget :mesh (mget p s))))))
  (let ((pst (mget p s))
        (qst (mget q s)))
    (mset p
          (mset :mesh
                (mset tp
                      (cons q (mget tp
                                    (mget :mesh pst)))
                      (mget :mesh pst))
                pst)
          (mset q
                (mset :mesh
                      (mset tp
                            (cons p (mget tp
                                          (mget :mesh qst)))
                            (mget :mesh qst))
                      qst)
                s))))


(definecd prune-mesh-gpn (p q :peer s :s-gpn tp :topic) :s-gpn
  :body-contracts-hints (("Goal" :use (prop=mget-nsubs-lopp-gpn)))
  :ic (^ (mget p s)
         (mget q s)
         (in tp (mget :subs (mget p s)))
         (in tp (mget :subs (mget q s)))
         (in q (mget tp (mget :nsubs (mget p s))))
         (! (in q (mget tp (mget :mesh (mget p s))))))
  (let ((pst (mget p s))
        (qst (mget q s)))
    (mset p
          (mset :mesh
                (mset tp
                      (remove-equal q (mget tp
                                            (mget :mesh pst)))
                      (mget :mesh pst))
                pst)
          (mset q
                (mset :mesh
                      (mset tp
                            (remove-equal p (mget tp
                                                  (mget :mesh qst)))
                            (mget :mesh qst))
                      qst)
                s))))


(definecd add-fanout-gpn (p q :peer s :s-gpn tp :topic) :s-gpn
  :body-contracts-hints (("Goal" :use (prop=mget-mesh-lopp-gpn
                                       prop=mget-fanout-lopp-gpn)))
  :ic (^ (mget p s)
         (mget q s)
         (in tp (mget :pubs (mget p s)))
         (! (in tp (mget :subs (mget p s))))
         (in q (mget tp (mget :nsubs (mget p s))))
         (! (in q (mget tp (mget :mesh (mget p s)))))
         (! (in q (mget tp (mget :fanout (mget p s))))))
  (b* ((pst (mget p s))
       (fanout (mget :fanout pst)))
    (mset p
          (mset :fanout
                (mset tp
                      (cons q (mget tp fanout))
                      fanout)
                pst)
          s)))

(definecd prune-fanout-gpn (p q :peer s :s-gpn tp :topic) :s-gpn
  :body-contracts-hints (("Goal" :use (prop=mget-mesh-lopp-gpn
                                       prop=mget-fanout-lopp-gpn)))
  :ic (^ (mget p s)
         (mget q s)
         (in tp (mget :pubs (mget p s)))
         (! (in tp (mget :subs (mget p s))))
         (in q (mget tp (mget :nsubs (mget p s))))
         (! (in q (mget tp (mget :mesh (mget p s)))))
         (! (in q (mget tp (mget :fanout (mget p s))))))
  (b* ((pst (mget p s))
       (fanout (mget :fanout pst)))
    (mset p
          (mset :fanout
                (mset tp
                      (remove-equal q (mget tp fanout))
                      fanout)
                pst)
          s)))

(definecd update-scores-gpn (p :peer ptscore :pt-score s :s-gpn) :s-gpn
  :ic (mget p s)
  (mset p
        (mset :ptscore
              ptscore
              (mget p s))
        s))

(definecd update-pscores-gpn (p :peer pscore :p-score s :s-gpn) :s-gpn
  :ic (mget p s)
  (mset p
        (mset :pscore
              pscore
              (mget p s))
        s))

(definec calc-total-score-gpn (q :peer ptscore :pt-score) :rational
  (match ptscore
    (() 0)
    ((((p . &) . topicscore) . rst)
     (+ (if (== p q)
            topicscore
          0)
        (calc-total-score-gpn q rst)))))


(definec total-score-gpn-help (ps :lop ptscore :pt-score) :p-score
  (match ps
    (() '())
    ((p . rst) (mset p
                     (calc-total-score-gpn p ptscore)
                     (total-score-gpn-help rst ptscore)))))


(property prop=alist-alist-ptscore (ptscore :pt-score)
  (lopp (alist-keys (alist-keys ptscore))))

(property prop=hons-rem-dupes (ps :lop)
  (lopp (remove-duplicates-equal ps)))

(definec p-score-gpn (ptscore :pt-score) :p-score
  (total-score-gpn-help (remove-duplicates-equal (alist-keys
                                                  (alist-keys ptscore)))
                        ptscore))

(definec score-based-prunes-gpn (p q :peer tp :topic ptscore :pt-score s :s-gpn)
  :s-gpn
  :body-contracts-hints (("Goal" :use (prop=mget-nsubs-lopp-gpn)))
  :ic (^ (mget p s)
         (mget q s)
         (in tp (mget :subs (mget p s)))
         (in tp (mget :subs (mget q s)))
         (in q (mget tp (mget :nsubs (mget p s))))
         (! (in q (mget tp (mget :mesh (mget p s)))))
         (mget `(,q . ,tp) ptscore))
  (if (< (calc-total-score-gpn q ptscore) 0)
      (prune-mesh-gpn p q s tp)
    s))

(definecd g2m-st (ps :ps-gpn) :ps-mn
  (ps-mn  (mget :pubs ps)
          (mget :subs ps)
          (mget :nsubs ps)
          (mget :mesh ps)
          (mget :fanout ps)
          (mget :pending ps)
          (mget :ctrl ps)
          (mget :ptscore ps)
          (mget :seen ps)))

(definec g2m (s :s-gpn) :s-mn
  :timeout 600
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (if (endp s)
      '()
    (cons `(,(caar s) . ,(g2m-st (cdar s)))
          (g2m (cdr s)))))


;;======================== PROPERTY-BASED-TESTING=====================


(definec nth-peer-custom (n :nat) :peer
  n)

(definec gen-peers (b n :nat) :lop
  (match n
    (0 '())
    (& (cons b (gen-peers (1+ b) (1- n))))))

(defdata-attach nat :enumerator nth-peer-custom)

(definec topics () :tl
  ;; topics in ETH
  '(AGG BLOCKS SUB1 SUB2 SUB3))  

(definec nth-topic-custom (n :nat) :symbol
  (nth (mod n (len (topics))) (topics)))

(defdata-attach var :enumerator nth-topic-custom)

(definec nth-lot-custom (n :nat) :lot
  (topics))

(defdata-attach lot :enumerator nth-lot-custom)



(defun pt-score-peer (p tops i)
  (if (endp tops)
      '()
    (cons `((,p . ,(car tops)) .
            ,(if (zp (mod i 2)) -6 5))
          (pt-score-peer p (cdr tops) (1- i)))))

(defun nth-ptscore-custom (n)
  (app
   (pt-score-peer (+ 1 n) (topics) 5)
   (pt-score-peer (+ 2 n) (topics) 5)
   (pt-score-peer (+ 3 n) (topics) 5)))

(defdata-attach pt-score :enumerator nth-ptscore-custom)

(defdata-attach pt-score
  :constraint (^ (mget `(,p . ,tp) pts)
		 (mget `(,q . ,tp) pts))
  :rule (implies (and (natp p)
                      (topicp tp)
                      (pt-scorep pts))
                 (equal q (1+ p)))
  :match-type :subterm-match)



(defun p-nbrs (tops nbrs)
  (if (endp tops)
      '()
    (cons (cons (car tops)
                nbrs)
          (p-nbrs (cdr tops) nbrs))))

(defun nth-p-nbrs-custom-help (n)
  (if (= n 1)
      (p-nbrs (topics) `(,(- n 1) ,(+ n 1)))
  (p-nbrs (topics) `(,(- n 2) ,n ,(+ n 1)))))

(defun nth-p-nbrs-custom (n)
  (nth-p-nbrs-custom-help (1+ n)))
  

(property nth-p-nbrs-custom-topic-lop-mapp (n :nat)
  :check-contracts? nil
  :proofs? nil
  (topic-lop-mapp (nth-p-nbrs-custom n)))

(defun nth-ps-gpn-custom (n)
  (ps-gpn (topics)
          (topics)
          (nth-p-nbrs-custom n)
          (nth-p-nbrs-custom n)
          nil
          nil
          nil
          (nth-ptscore-custom n)
          (p-score-gpn (nth-ptscore-custom n))
          nil))
          
(property nth-ps-gpn-custom-ps-gpnp (n :nat)
  :check-contracts? nil
  :proofs? nil
  (ps-gpnp (nth-ps-gpn-custom n)))
          
(defdata-attach ps-gpn :enumerator nth-ps-gpn-custom)


(defun nth-s-gpn-custom-help (n)
  `((,(- n 2) . ,(nth-ps-gpn-custom (- n 2)))
    (,(- n 1) . ,(nth-ps-gpn-custom (- n 1)))
    (,n . ,(nth-ps-gpn-custom n))
    (,(+ n 1) . ,(nth-ps-gpn-custom (+ n 1)))))

(defun nth-s-gpn-custom (n)
  (nth-s-gpn-custom-help (1+ n)))

(defdata-attach s-gpn :enumerator nth-s-gpn-custom)


(defdata-attach s-gpn
  :constraint (mget i s)
  :rule (implies (and (natp i)
                      (zp (mod i 2))
                      (s-gpnp s))
                 (equal i (caar s)))
  :match-type :subterm-match)


(defdata-attach s-gpn
  :constraint (mget i s)
  :rule (implies (and (natp i)
                      (! (zp (mod i 2)))
                      (s-gpnp s))
                 (equal i (caadr s)))
  :match-type :subterm-match)

(acl2::must-fail
 (property ref-ctrdex (q :peer tp :topic ptscore :pt-score)
   :check-contracts? nil
   :proofs? nil
   :h (mget `(,q . ,tp) ptscore)
   (== (> (calc-total-score-gpn q ptscore) 0)
       (> (mget `(,q . ,tp) ptscore) 0)))
 )


;(acl2s-defaults :set :verbosity-level 2)
(acl2s-defaults :set testing-enabled t)



(property (p q :peer tp :topic ptscore :pt-score s :s-gpn)
  :check-contracts? nil
  :testing? t
  :proofs? nil
  :h (^ (= p (caar s))
	(= q (caadr s))
        (in tp (mget :subs (mget p s)))
        (in tp (mget :subs (mget q s)))
        (in q (mget tp (mget :nsubs (mget p s)))))
        ;(! (in q (mget tp (mget :mesh (mget p s)))))
	;(mget `(,q . ,tp) ptscore))
  (== (g2m (score-based-prunes-gpn p q tp ptscore s))
      (score-based-prunes-mn p q tp ptscore (g2m s))))






(property (p q :peer tp :topic ptscore :pt-score s :s-gpn)
  :check-contracts? nil
  :testing? t
  :proofs? nil
  :h (^ (!= p q)
        (mget p s)
        (mget q s)
        (in tp (mget :subs (mget p s)))
        (in tp (mget :subs (mget q s)))
        (in q (mget tp (mget :nsubs (mget p s))))
        (! (in q (mget tp (mget :mesh (mget p s)))))
       (mget `(,q . ,tp) ptscore))
  (== (g2m (score-based-prunes-gpn p q tp ptscore s))
      (score-based-prunes-mn p q tp ptscore (g2m s))))


;; (definec step-gpn (p :peer pubs subs ts :lot nbrs :lop m :mssg s :s-gpn i :nat) :s-gpn
;;   (if (mget p s)
;;       (match (mod i 6)
;;         (0 (skip-gpn s))
;;         (1 (subscribe-gpn p ts s))
;;         (2 (unsubscribe-gpn p ts s))
;;         (3 (leave-gpn p s))
;;         (4 (if (^ (mget p s)
;;                   (in m (mget :pending (mget p s))))
;;                (forward-gpn p m s)
;;              (skip-gpn s)))
;;         (5 (if (^ (mget (mget :or m) s)
;;                   (new-gpn-mssgp m s)
;;                   (in (mget :tp m)
;;                       (mget :pubs (mget (mget :or m) s))))
;;                (produce-gpn m s)
;;              (skip-gpn s))))
;;     (match (mod i 6)
;;       (0 (skip-gpn s))
;;       (& (join-gpn p pubs subs nbrs s)))))
 
