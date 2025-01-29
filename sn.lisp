(in-package "ACL2S")
(include-book "gn")

(defdata ps-sn
  (record  (pubs . lot)
           (subs . lot) ;; self subscriptions
           (nsubs . topic-lop-map) ;; nbr topic subscriptions
           (mesh . topic-lop-map)  ;; mesh nbrs
           (fanout . topic-lop-map);; fanout nbrs
           (pending . lom)
           (seen . lom)))

(property ps-sn-check-prop (x :ps-sn)
  (^ (lomp (mget :seen x))
     (lomp (mget :pending x))
     (topic-lop-mapp (mget :nsubs x))
     (topic-lop-mapp (mget :mesh x))
     (topic-lop-mapp (mget :fanout x))
     (lotp (mget :subs x))
     (lotp (mget :pubs x)))
  :rule-classes :forward-chaining)

(defdata s-sn (map peer ps-sn))

(property s-sn-check (st :s-sn p :peer)
          (=> (mget p st)
              (ps-snp (mget p st)))
          :rule-classes :forward-chaining)

(definec skip-sn (st :s-sn) :s-sn
  st)

(definecd add-pending-sn (p :peer m :mssg st :s-sn) :s-sn
  :ic (mget p st)
  :oc (mget p (add-pending-sn p m st))
  (b* ((pst (mget p st)))
    (mset p
          (mset :pending
                (cons m (mget :pending pst))
                pst)
          st)))

(definecd produce-sn (m :mssg st :s-sn) :s-sn
  :ic (mget (mget :or m) st)
  (add-pending-sn (mget :or m) m st))

(definecd forward-help-sn (nbrs :lop m :mssg st :s-sn) :s-sn
  (match nbrs
    (() st)
    ((p . rst)
     (forward-help-sn rst m (if (mget p st)
                                (add-pending-sn p m st)
                              st)))))

(definecd forward-sn (p :peer m :mssg st :s-sn) :s-sn
  :body-contracts-hints (("Goal" :in-theory (enable ps-sn)))
  :ic (^ (mget p st)
         (in m (mget :pending (mget p st))))
  :oc (mget p (forward-sn p m st))
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
    (mset p new-pst (forward-help-sn fwdnbrs m st))))

;; actually forward only to a subset with some probability
(definecd fwd-gsps-sn (p gp :peer st :s-sn m :mssg) :s-sn
  :ic (mget p st)
  :oc (mget p (fwd-gsps-sn p gp st m))
  (b* ((pst (mget p st))
       (tp (mssg-tp m))
       (sub-nbrs (mget tp (mget :nsubs pst)))
       (mesh-nbrs (mget tp (mget :mesh pst)))
       (fanout-nbrs (mget tp (mget :fanout pst))) ;; if mesh then not fanout, viceversa
       (fwdnbrs (union-equal mesh-nbrs fanout-nbrs))
       (gspnbrs (set-difference-equal sub-nbrs fwdnbrs))
       ((unless (in gp gspnbrs)) st))
    (mset p pst (forward-help-sn `(,gp) m st))))

(definecd fwd-gsps-iter (p gp :peer ms :lom st :s-sn) :s-sn
  :ic (mget p st)
  (match ms
    (() st)
    ((m . rst)
     (fwd-gsps-iter p gp rst (fwd-gsps-sn p gp st m)))))


(definecd hbm-sn (p gp :peer st :s-sn) :s-sn
  :ic (mget p st)
  (fwd-gsps-iter p gp (mget :seen (mget p st)) st))

;----


(definecd set-topics-subscriber-pssn (topics :lot p :peer pst :ps-sn) :ps-sn
  (mset :nsubs (set-topics-subscriber topics p (mget :nsubs pst) '()) pst))

;; Given a peer p and topics it subscribes to, share p subs with its
;; neighboring peers
(definecd set-topics-subscriber-ssn (nbrs :lop topics :lot p :peer st :s-sn)
  :s-sn
  (match nbrs
    (() st)
    ((n . rst) (b* ((pst (mget n st))
                    ((when (null pst))
                     (set-topics-subscriber-ssn rst topics p st)))
                 (set-topics-subscriber-ssn
                  rst topics p
                  (mset n
                        (set-topics-subscriber-pssn topics p pst)
                        st))))))

;; Calculate nsubs, given neighbors in a sn state
(definecd calc-nsubs-sn (nbrs :lop st :s-sn acc :topic-lop-map) :topic-lop-map
  (match nbrs
    (() acc)
    ((n . rst) (b* ((pst (mget n st))
                    ((when (null pst))
                     (calc-nsubs-sn rst st acc)))
                 (calc-nsubs-sn rst
                                st
                                (set-topics-subscriber (mget :subs pst)
                                                       n
                                                       acc
                                                       '()))))))

(sig set-difference-equal ((listof :a) (listof :a)) => (listof :a))
(sig union-equal ((listof :a) (listof :a)) => (listof :a))

(definecd ps-sn-nbrs-help (xs :topic-lop-map acc :lop) :lop
  (match xs
    (() acc)
    (((& . peers) . rst)
     (ps-sn-nbrs-help rst (union-equal peers acc)))))

(definecd ps-sn-nbrs (pst :ps-sn) :lop
  (ps-sn-nbrs-help (mget :nsubs pst) '()))

(definecd join-sn (p :peer pubs subs :lot nbrs :lop st :s-sn) :s-sn
  :timeout 600
  :function-contract-hints (("Goal" :in-theory (enable ps-snp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-snp)))
  :ic (! (mget p st))
  (mset p
        (ps-sn pubs subs (calc-nsubs-sn nbrs st '()) '() '() '() '())
        (set-topics-subscriber-ssn nbrs subs p st)))

(definecd subscribe-sn (p :peer topics :lot st :s-sn) :s-sn
  :function-contract-hints (("Goal" :in-theory (enable ps-snp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-snp)))
  :ic (mget p st)
  (b* ((pst (mget p st))
       (ts (union-equal topics (mget :subs pst))))
    (mset p 
          (mset :subs ts pst)
          (set-topics-subscriber-ssn (ps-sn-nbrs pst)
				     ts
				     p
				     st))))

(definecd leave-sn (p :peer st :s-sn) :s-sn
  :ic (mget p st)
  (let ((pst (mget p st)))
    (mset p nil (set-topics-subscriber-ssn (ps-sn-nbrs pst)
					   '()
					   p
					   st))))

(definecd unsubscribe-sn (p :peer topics :lot st :s-sn) :s-sn
  :function-contract-hints (("Goal" :in-theory (enable ps-snp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-snp)))
  :ic (mget p st)
  (b* ((pst (mget p st))
       (ts (set-difference-equal (mget :subs pst) topics)))
    (mset p 
          (mset :subs ts pst)
          (set-topics-subscriber-ssn (ps-sn-nbrs pst)
				     ts
				     p
				     st))))


(definecd add-mesh-pssn (p q :peer tp :topic pst :ps-sn) :ps-sn
  :body-contracts-hints (("Goal" :in-theory (enable ps-snp)))
  :ic (^ (! (in q (mget tp (mget :fanout pst))))
	 (! (in q (mget tp (mget :mesh pst))))
	 (in q (mget tp (mget :nsubs pst))))
  (let ((mesh (mget :mesh pst)))
    (mset :mesh
	  (mset tp
		(cons q (mget tp mesh))
		mesh)
	  pst)))

(definecd add-mesh-sn (p q :peer tp :topic st :s-sn) :s-sn
  :timeout 200
  :body-contracts-hints (("Goal" :in-theory (enable ps-snp s-snp topic-lop-mapp)))
  :ic (^ (mget p st)
	 (mget q st)
	 (! (in p (mget tp (mget :fanout (mget q st)))))
	 (! (in p (mget tp (mget :mesh (mget q st)))))
	 (in p (mget tp (mget :nsubs (mget q st))))
	 (! (in q (mget tp (mget :fanout (mget p st)))))
	 (! (in q (mget tp (mget :mesh (mget p st)))))
	 (in q (mget tp (mget :nsubs (mget p st)))))
  (mset q
	(add-mesh-pssn q p tp (mget q st))
	(mset p
	      (add-mesh-pssn p q tp (mget p st))
	      st)))

(definecd rem-mesh-pssn (p q :peer tp :topic pst :ps-sn) :ps-sn
  :body-contracts-hints (("Goal" :in-theory (enable ps-snp)))
  :ic (^ (! (in q (mget tp (mget :fanout pst))))
	 (in q (mget tp (mget :mesh pst)))
	 (in q (mget tp (mget :nsubs pst))))
  (let ((mesh (mget :mesh pst)))
    (mset :mesh
	  (mset tp
		(remove-equal q (mget tp mesh))
		mesh)
	  pst)))

(definecd rem-mesh-sn (p q :peer tp :topic st :s-sn) :s-sn
  :timeout 200
  :body-contracts-hints (("Goal" :in-theory (enable ps-snp s-snp topic-lop-mapp)))
  :ic (^ (mget p st)
	 (mget q st)
	 (! (in p (mget tp (mget :fanout (mget q st)))))
	 (in p (mget tp (mget :mesh (mget q st))))
	 (in p (mget tp (mget :nsubs (mget q st))))
	 (! (in q (mget tp (mget :fanout (mget p st)))))
	 (in q (mget tp (mget :mesh (mget p st))))
	 (in q (mget tp (mget :nsubs (mget p st)))))
  (mset q
	(rem-mesh-pssn q p tp (mget q st))
	(mset p
	      (rem-mesh-pssn p q tp (mget p st))
	      st)))

(definecd add-fanout-pssn (p q :peer tp :topic pst :ps-sn) :ps-sn
  :body-contracts-hints (("Goal" :in-theory (enable ps-snp)))
  :ic (^ (! (in q (mget tp (mget :fanout pst))))
	 (! (in q (mget tp (mget :mesh pst))))
	 (in q (mget tp (mget :nsubs pst))))
  (let ((mesh (mget :fanout pst)))
    (mset :fanout
	  (mset tp
		(cons q (mget tp mesh))
		mesh)
	  pst)))

(definecd add-fanout-sn (p q :peer tp :topic st :s-sn) :s-sn
  :body-contracts-hints (("Goal" :in-theory (enable ps-snp s-snp topic-lop-mapp)))
  :ic (^ (mget p st)
	 (! (in q (mget tp (mget :fanout (mget p st)))))
	 (! (in q (mget tp (mget :mesh (mget p st)))))
	 (in q (mget tp (mget :nsubs (mget p st)))))
  (mset p
	(add-fanout-pssn p q tp (mget p st))
	st))

(definecd rem-fanout-pssn (p q :peer tp :topic pst :ps-sn) :ps-sn
  :body-contracts-hints (("Goal" :in-theory (enable ps-snp)))
  :ic (^ (in q (mget tp (mget :fanout pst)))
	 (! (in q (mget tp (mget :mesh pst))))
	 (in q (mget tp (mget :nsubs pst))))
  (let ((mesh (mget :fanout pst)))
    (mset :fanout
	  (mset tp
		(remove-equal q (mget tp mesh))
		mesh)
	  pst)))

(definecd rem-fanout-sn (p q :peer tp :topic st :s-sn) :s-sn
  :body-contracts-hints (("Goal" :in-theory (enable ps-snp s-snp topic-lop-mapp)))
  :ic (^ (mget p st)
	 (in q (mget tp (mget :fanout (mget p st))))
	 (! (in q (mget tp (mget :mesh (mget p st)))))
	 (in q (mget tp (mget :nsubs (mget p st)))))
  (mset p
	(rem-fanout-pssn p q tp (mget p st))
	st))


;; add add-mesh, rem-fanout steps
(definec step-sn (p :peer pubs subs ts :lot nbrs :lop m :mssg st :s-sn i :nat) :s-sn
  (if (mget p st)
      (match (mod i 6)
        (0 (unsubscribe-sn p ts st))
        (1 (subscribe-sn p ts st))
        (2 (leave-sn p st))
        (4 (if (mget (mget :or m) st)
               (produce-sn m st)
             (skip-sn st)))
        (5 (if (^ (mget p st)
                  (in m (mget :pending (mget p st))))
               (forward-sn p m st)
             (skip-sn st)))
        (& (skip-sn st)))
    (match i
      (3 (join-sn p pubs subs nbrs st))
      (& (skip-sn st)))))

;;----------------

(definecd g2f-help (s :s-sn acc :s-gn) :s-gn
  :function-contract-hints (("Goal" :in-theory (enable s-snp ps-gnp)))
  :body-contracts-hints (("Goal" :in-theory (enable s-snp ps-gnp)))
  (match s
    (() '())
    (((p . pst) . rst)
     (g2f-help rst
               (mset p
                     (ps-gn (mget :pubs pst)
			    (mget :subs pst)
			    (mget :nsubs pst)
			    (mget :pending pst)
			    (mget :seen pst))
                     acc)))))

(definecd s2g (s :s-sn) :s-gn
  (s2g-help s '()))
