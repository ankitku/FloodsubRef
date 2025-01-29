(in-package "ACL2S")
(include-book "fn")

(defdata ps-gn
  (record  (pubs . lot)
           (subs . lot) ;; self subscriptions
           (nsubs . topic-lop-map) ;; nbr topic subscriptions
           (mesh . topic-lop-map)  ;; mesh nbrs
           (fanout . topic-lop-map);; fanout nbrs
           (pending . lom)
           (seen . lom)))

(property ps-gn-check-prop (x :ps-gn)
  (^ (lomp (mget :seen x))
     (lomp (mget :pending x))
     (topic-lop-mapp (mget :nsubs x))
     (topic-lop-mapp (mget :mesh x))
     (topic-lop-mapp (mget :fanout x))
     (lotp (mget :subs x))
     (lotp (mget :pubs x)))
  :rule-classes :forward-chaining)

(defdata s-gn (map peer ps-gn))

(property s-gn-check (st :s-gn p :peer)
          (=> (mget p st)
              (ps-gnp (mget p st)))
          :rule-classes :forward-chaining)

(definec skip-gn (st :s-gn) :s-gn
  st)

(definecd add-pending-gn (p :peer m :mssg st :s-gn) :s-gn
  :ic (mget p st)
  :oc (mget p (add-pending-gn p m st))
  (b* ((pst (mget p st)))
    (mset p
          (mset :pending
                (cons m (mget :pending pst))
                pst)
          st)))

(definecd produce-gn (m :mssg st :s-gn) :s-gn
  :ic (mget (mget :or m) st)
  (add-pending-gn (mget :or m) m st))

(definecd forward-help-gn (nbrs :lop m :mssg st :s-gn) :s-gn
  (match nbrs
    (() st)
    ((p . rst)
     (forward-help-gn rst m (if (mget p st)
                                (add-pending-gn p m st)
                              st)))))

(definecd forward-gn (p :peer m :mssg st :s-gn) :s-gn
  :body-contracts-hints (("Goal" :in-theory (enable ps-gn)))
  :ic (^ (mget p st)
         (in m (mget :pending (mget p st))))
  :oc (mget p (forward-gn p m st))
  (b* ((tp (mssg-tp m))
       (pst (mget p st))
       (mesh-nbrs (mget tp (mget :mesh pst)))
       (fanout-nbrs (mget tp (mget :fanout pst)))
       (fwdnbrs (union-equal mesh-nbrs fanout-nbrs))
       (new-pst (mset :seen
                      (cons m (mget :seen pst))
                      (mset :pending
                            (remove-equal m (mget :pending pst))
                            pst))))
    (mset p new-pst (forward-help-gn fwdnbrs m st))))

;; actually forward only to a subset with some probability
(definecd fwd-gsps (p gp :peer st :s-gn m :mssg) :s-gn
  :ic (mget p st)
  :oc (mget p (fwd-gsps p gp st m))
  (b* ((pst (mget p st))
       (tp (mssg-tp m))
       (sub-nbrs (mget tp (mget :nsubs pst)))
       (mesh-nbrs (mget tp (mget :mesh pst)))
       (fanout-nbrs (mget tp (mget :fanout pst))) ;; if mesh then not fanout, viceversa
       (fwdnbrs (union-equal mesh-nbrs fanout-nbrs))
       (gspnbrs (set-difference-equal sub-nbrs fwdnbrs))
       ((unless (in gp gspnbrs)) st))
    (mset p pst (forward-help-gn `(,gp) m st))))

(definecd fwd-gsps-iter (p gp :peer ms :lom st :s-gn) :s-gn
  :ic (mget p st)
  (match ms
    (() st)
    ((m . rst)
     (fwd-gsps-iter p gp rst (fwd-gsps p gp st m)))))


(definecd hbm-gn (p gp :peer st :s-gn) :s-gn
  :ic (mget p st)
  (fwd-gsps-iter p gp (mget :seen (mget p st)) st))

;----


(definecd set-topics-subscriber-psgn (topics :lot p :peer pst :ps-gn) :ps-gn
  (mset :nsubs (set-topics-subscriber topics p (mget :nsubs pst) '()) pst))

;; Given a peer p and topics it subscribes to, share p subs with its
;; neighboring peers
(definecd set-topics-subscriber-sgn (nbrs :lop topics :lot p :peer st :s-gn)
  :s-gn
  (match nbrs
    (() st)
    ((n . rst) (b* ((pst (mget n st))
                    ((when (null pst))
                     (set-topics-subscriber-sgn rst topics p st)))
                 (set-topics-subscriber-sgn
                  rst topics p
                  (mset n
                        (set-topics-subscriber-psgn topics p pst)
                        st))))))

;; Calculate nsubs, given neighbors in a gn state
(definecd calc-nsubs-gn (nbrs :lop st :s-gn acc :topic-lop-map) :topic-lop-map
  (match nbrs
    (() acc)
    ((n . rst) (b* ((pst (mget n st))
                    ((when (null pst))
                     (calc-nsubs-gn rst st acc)))
                 (calc-nsubs-gn rst
                                st
                                (set-topics-subscriber (mget :subs pst)
                                                       n
                                                       acc
                                                       '()))))))

(sig set-difference-equal ((listof :a) (listof :a)) => (listof :a))
(sig union-equal ((listof :a) (listof :a)) => (listof :a))

(definecd ps-gn-nbrs-help (xs :topic-lop-map acc :lop) :lop
  (match xs
    (() acc)
    (((& . peers) . rst)
     (ps-gn-nbrs-help rst (union-equal peers acc)))))

(definecd ps-gn-nbrs (pst :ps-gn) :lop
  (ps-gn-nbrs-help (mget :nsubs pst) '()))

(definecd join-gn (p :peer pubs subs :lot nbrs :lop st :s-gn) :s-gn
  :timeout 600
  :function-contract-hints (("Goal" :in-theory (enable ps-gnp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-gnp)))
  :ic (! (mget p st))
  (mset p
        (ps-gn pubs subs (calc-nsubs-gn nbrs st '()) '() '() '() '())
        (set-topics-subscriber-sgn nbrs subs p st)))

(definecd subscribe-gn (p :peer topics :lot st :s-gn) :s-gn
  :function-contract-hints (("Goal" :in-theory (enable ps-gnp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-gnp)))
  :ic (mget p st)
  (b* ((pst (mget p st))
       (ts (union-equal topics (mget :subs pst))))
    (mset p 
          (mset :subs ts pst)
          (set-topics-subscriber-sgn (ps-gn-nbrs pst)
				     ts
				     p
				     st))))

(definecd leave-gn (p :peer st :s-gn) :s-gn
  :ic (mget p st)
  (let ((pst (mget p st)))
    (mset p nil (set-topics-subscriber-sgn (ps-gn-nbrs pst)
					   '()
					   p
					   st))))

(definecd unsubscribe-gn (p :peer topics :lot st :s-gn) :s-gn
  :function-contract-hints (("Goal" :in-theory (enable ps-gnp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-gnp)))
  :ic (mget p st)
  (b* ((pst (mget p st))
       (ts (set-difference-equal (mget :subs pst) topics)))
    (mset p 
          (mset :subs ts pst)
          (set-topics-subscriber-sgn (ps-gn-nbrs pst)
				     ts
				     p
				     st))))


(definecd add-mesh-psgn (p q :peer tp :topic pst :ps-gn) :ps-gn
  :body-contracts-hints (("Goal" :in-theory (enable ps-gnp)))
  :ic (^ (! (in q (mget tp (mget :fanout pst))))
	 (! (in q (mget tp (mget :mesh pst))))
	 (in q (mget tp (mget :nsubs pst))))
  (let ((mesh (mget :mesh pst)))
    (mset :mesh
	  (mset tp
		(cons q (mget tp mesh))
		mesh)
	  pst)))

(definecd add-mesh-gn (p q :peer tp :topic st :s-gn) :s-gn
  :timeout 200
  :body-contracts-hints (("Goal" :in-theory (enable ps-gnp s-gnp topic-lop-mapp)))
  :ic (^ (mget p st)
	 (mget q st)
	 (! (in p (mget tp (mget :fanout (mget q st)))))
	 (! (in p (mget tp (mget :mesh (mget q st)))))
	 (in p (mget tp (mget :nsubs (mget q st))))
	 (! (in q (mget tp (mget :fanout (mget p st)))))
	 (! (in q (mget tp (mget :mesh (mget p st)))))
	 (in q (mget tp (mget :nsubs (mget p st)))))
  (mset q
	(add-mesh-psgn q p tp (mget q st))
	(mset p
	      (add-mesh-psgn p q tp (mget p st))
	      st)))

(definecd rem-mesh-psgn (p q :peer tp :topic pst :ps-gn) :ps-gn
  :body-contracts-hints (("Goal" :in-theory (enable ps-gnp)))
  :ic (^ (! (in q (mget tp (mget :fanout pst))))
	 (in q (mget tp (mget :mesh pst)))
	 (in q (mget tp (mget :nsubs pst))))
  (let ((mesh (mget :mesh pst)))
    (mset :mesh
	  (mset tp
		(remove-equal q (mget tp mesh))
		mesh)
	  pst)))

(definecd rem-mesh-gn (p q :peer tp :topic st :s-gn) :s-gn
  :timeout 200
  :body-contracts-hints (("Goal" :in-theory (enable ps-gnp s-gnp topic-lop-mapp)))
  :ic (^ (mget p st)
	 (mget q st)
	 (! (in p (mget tp (mget :fanout (mget q st)))))
	 (in p (mget tp (mget :mesh (mget q st))))
	 (in p (mget tp (mget :nsubs (mget q st))))
	 (! (in q (mget tp (mget :fanout (mget p st)))))
	 (in q (mget tp (mget :mesh (mget p st))))
	 (in q (mget tp (mget :nsubs (mget p st)))))
  (mset q
	(rem-mesh-psgn q p tp (mget q st))
	(mset p
	      (rem-mesh-psgn p q tp (mget p st))
	      st)))

(definecd add-fanout-psgn (p q :peer tp :topic pst :ps-gn) :ps-gn
  :body-contracts-hints (("Goal" :in-theory (enable ps-gnp)))
  :ic (^ (! (in q (mget tp (mget :fanout pst))))
	 (! (in q (mget tp (mget :mesh pst))))
	 (in q (mget tp (mget :nsubs pst))))
  (let ((mesh (mget :fanout pst)))
    (mset :fanout
	  (mset tp
		(cons q (mget tp mesh))
		mesh)
	  pst)))

(definecd add-fanout-gn (p q :peer tp :topic st :s-gn) :s-gn
  :body-contracts-hints (("Goal" :in-theory (enable ps-gnp s-gnp topic-lop-mapp)))
  :ic (^ (mget p st)
	 (! (in q (mget tp (mget :fanout (mget p st)))))
	 (! (in q (mget tp (mget :mesh (mget p st)))))
	 (in q (mget tp (mget :nsubs (mget p st)))))
  (mset p
	(add-fanout-psgn p q tp (mget p st))
	st))

(definecd rem-fanout-psgn (p q :peer tp :topic pst :ps-gn) :ps-gn
  :body-contracts-hints (("Goal" :in-theory (enable ps-gnp)))
  :ic (^ (in q (mget tp (mget :fanout pst)))
	 (! (in q (mget tp (mget :mesh pst))))
	 (in q (mget tp (mget :nsubs pst))))
  (let ((mesh (mget :fanout pst)))
    (mset :fanout
	  (mset tp
		(remove-equal q (mget tp mesh))
		mesh)
	  pst)))

(definecd rem-fanout-gn (p q :peer tp :topic st :s-gn) :s-gn
  :body-contracts-hints (("Goal" :in-theory (enable ps-gnp s-gnp topic-lop-mapp)))
  :ic (^ (mget p st)
	 (in q (mget tp (mget :fanout (mget p st))))
	 (! (in q (mget tp (mget :mesh (mget p st)))))
	 (in q (mget tp (mget :nsubs (mget p st)))))
  (mset p
	(rem-fanout-psgn p q tp (mget p st))
	st))


;; add add-mesh, rem-fanout steps
(definec step-gn (p :peer pubs subs ts :lot nbrs :lop m :mssg st :s-gn i :nat) :s-gn
  (if (mget p st)
      (match (mod i 6)
        (0 (unsubscribe-gn p ts st))
        (1 (subscribe-gn p ts st))
        (2 (leave-gn p st))
        (4 (if (mget (mget :or m) st)
               (produce-gn m st)
             (skip-gn st)))
        (5 (if (^ (mget p st)
                  (in m (mget :pending (mget p st))))
               (forward-gn p m st)
             (skip-gn st)))
        (& (skip-gn st)))
    (match i
      (3 (join-gn p pubs subs nbrs st))
      (& (skip-gn st)))))

;;----------------

(definecd g2f-help (s :s-gn acc :s-fn) :s-fn
  :function-contract-hints (("Goal" :in-theory (enable s-gnp ps-fnp)))
  :body-contracts-hints (("Goal" :in-theory (enable s-gnp ps-fnp)))
  (match s
    (() '())
    (((p . pst) . rst)
     (g2f-help rst
               (mset p
                     (ps-fn (mget :pubs pst)
			    (mget :subs pst)
			    (mget :nsubs pst)
			    (mget :pending pst)
			    (mget :seen pst))
                     acc)))))

(definecd g2f (s :s-gn) :s-fn
  (g2f-help s '()))
