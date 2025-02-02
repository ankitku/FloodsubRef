(in-package "ACL2S")
(include-book "f2b-commit")


(definec pending-!in-seen-ps-fn (st :ps-fn ms :lom) :bool
  (match ms
    (() t)
    ((m . rs) (^ (! (in m (mget :seen st)))
                 (pending-!in-seen-ps-fn st rs)))))

(property prop=pending-!in-seen-ps-fn (st :ps-fn m :mssg ms :lom)
  :h (^ (in m ms)
        (pending-!in-seen-ps-fn st ms))
  (! (in m (mget :seen st)))
  :hints (("Goal" :in-theory (enable ps-fnp))))

(property prop=pending-!in-seen-ps-fn-set-pending (st :ps-fn m :mssg
                                                         ms ns :lom)
  :h (^ (! (in m (mget :seen st)))
        (pending-!in-seen-ps-fn st ms))
  (pending-!in-seen-ps-fn (mset :pending ns st)
                             (cons m ms)))

(definec pending-!in-seen-s-fn (s :s-fn) :bool
  (match s
    (() t)
    (((& . pst) . rst)
     (^ (pending-!in-seen-ps-fn pst (mget :pending pst))
        (pending-!in-seen-s-fn rst)))))

(propertyd prop=pending-!in-seen-s-fn (s :s-fn p :peer m :mssg)
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (pending-!in-seen-s-fn s))
  (! (in m (mget :seen (mget p s))))
  :hints (("Goal" :in-theory
           (enable acl2::maximal-records-theory))))


(in-theory (enable new-fn-mssgp
                   produce-fn
                   produce-fn-pre
                   pending-!in-seen-s-fn
                   pending-!in-seen-ps-fn
                   acl2::maximal-records-theory))

(property prop=in-member (x :tl m :all)
  (=> (in m x)
      (member-equal m x)))

(propertyd prop=pending-!in-seen-s-fn-produce (s :s-fn m :mssg)
  :check-contracts? nil
  :h (^ (pending-!in-seen-s-fn s)
        (produce-fn-pre m s))
  (pending-!in-seen-s-fn (produce-fn m s))
  :instructions
  (:pro (:dv 1) (:r produce-fn) :s :top
        :induct :pro
        (:claim (produce-fn-pre m (cdr s)))
        (:claim (pending-!in-seen-s-fn (cdr s)))
        (:claim (pending-!in-seen-s-fn
                  (mset (mget :or m)
                        (add-pending-psfn m (mget (mget :or m) (cdr s)))
                        (cdr s))))
        (= (mset (mget :or m)
                 (add-pending-psfn m (mget (mget :or m) s))
                 s)
           (cons (car s)
                 (mset (mget :or m)
                       (add-pending-psfn m (mget (mget :or m) s))
                       (cdr s))))
        (:claim (s-fnp (cons (car s)
                             (mset (mget :or m)
                                   (add-pending-psfn m (mget (mget :or m) s))
                                   (cdr s)))))
        (= (^ (pending-!in-seen-ps-fn (cdar s) (mget :pending (cdar s)))
              (pending-!in-seen-s-fn (mset (mget :or m)
                                              (add-pending-psfn m (mget (mget :or m) s))
                                              (cdr s)))))
        (= (mget (mget :or m) s)
           (mget (mget :or m) (cdr s)))
        :s :bash
        
       

        :pro
        (:claim (== (mget :seen (add-pending-psfn m (cdr (car s))))
                    (mget :seen (cdr (car s))))
                :hints (("Goal" :use ((:instance prop=add-pending-psfn-seen
                                                 (pst (cdr (car s))))))))
        (:claim (add-pending-psfn m (cdr (car s))))
        (= (mget :or m) (caar s))
        (= (mget (car (car s)) s) (cdar s))
        (= (add-pending-psfn m (cdar s))
           (mset :pending
                 (cons m (mget :pending (cdar s)))
                 (cdr (car s)))
           :hints (("Goal" :in-theory (enable add-pending-psfn))))
        (:dv 1) :r :s :s :up
        (= (mget :or m) (caar s))
        

        (:claim (pending-!in-seen-s-fn (cdr s)))
        (:claim (new-fn-mssgp m s))
        (:claim (^ (! (in m (mget :pending (cdar s))))
                   (! (in m (mget :seen (cdar s))))))
        (= (^ (pending-!in-seen-ps-fn (mset :pending
                                               (cons m (mget :pending (cdr (car s))))
                                               (cdr (car s)))
                                         (cons m (mget :pending (cdr (car s)))))
              (pending-!in-seen-s-fn (cdr s))))
        (:claim (pending-!in-seen-ps-fn (cdr (car s))
                                        (mget :pending (cdr (car s)))))
        (:claim (pending-!in-seen-ps-fn (mset :pending
                                              (cons m (mget :pending (cdr (car s))))
                                              (cdr (car s)))
                                        (cons m (mget :pending (cdr (car
                                                                     s)))))
                :hints (("Goal" :use ((:instance
                                       prop=pending-!in-seen-ps-fn-set-pending
                                       (ns (cons m (mget :pending (cdr (car
                                                                        s)))))
                                       (ms (mget :pending (cdr (car s))))
                                       (st (cdr (car s))))))))
        :s
        :bash :bash))




(in-theory (enable subscribe-fn
                   unsubscribe-fn
                   set-subs-sfn))

(encapsulate ()
  (local
   (property prop=pending-!in-seen-ps-fn-set-nsubs (st :ps-fn m :mssg
                                                       ms :lom ns :topic-lop-map)
     :h (pending-!in-seen-ps-fn st ms)
     (pending-!in-seen-ps-fn
      (mset :nsubs ns st) ms)))

  (local
   (property prop=pending-!in-seen-set-nsubs-psfn (nbrs :lop topics :lot ms :lom
                                                        n p :peer st :ps-fn)
     :h (pending-!in-seen-ps-fn st ms)
     (pending-!in-seen-ps-fn (set-subs-psfn nbrs topics n p st) ms)))

   (property prop=pending-!in-seen-set-nsubs-sfn (nbrs :lop topics :lot
                                                       p :peer s :s-fn)
     :h (pending-!in-seen-s-fn s)
     (pending-!in-seen-s-fn
      (set-subs-sfn nbrs topics p s)))

  (local
   (property prop=pending-!in-seen-ps-fn-set-subs (st :ps-fn ms :lom ts :lot)
     :h (pending-!in-seen-ps-fn st ms)
     (pending-!in-seen-ps-fn
      (mset :subs ts st) ms)))

  (local
   (property prop=pending-!in-seen-set-subs-sfn (ts :lot p :peer s :s-fn)
     :h (^ (mget p s)
           (pending-!in-seen-s-fn s))
     (pending-!in-seen-s-fn (mset p
                                  (mset :subs ts (mget p s))
                                  s))))

  
  (propertyd prop=pending-!in-seen-s-fn-subscribe (s :s-fn p :peer topics :lot)
    :h (^ (mget p s)
          (pending-!in-seen-s-fn s))
    (pending-!in-seen-s-fn (subscribe-fn p topics s))
    :instructions
    (:pro
     (= (subscribe-fn p topics s)
        (set-subs-sfn (ps-fn-nbrs (mget p s))
                      topics
                      p
                      (mset p 
                            (mset :subs (union-equal (mget :subs (mget p s))
                                                     topics)
                                  (mget p s))
                            s)))

     (:claim (pending-!in-seen-s-fn
              (mset p
                    (mset :subs
                          (union-equal (mget :subs (mget p s))
                                       topics)
                          (mget p s))
                    s))
             :hints (("Goal" :use ((:instance
                                    prop=pending-!in-seen-set-subs-sfn
                                    (ts (union-equal (mget :subs (mget p s))
                                                     topics)))))))

     (:prove :hints (("Goal" :use ((:instance
                                    prop=pending-!in-seen-set-nsubs-sfn
                                    (nbrs (ps-fn-nbrs (mget p s)))
                                    (s (mset p 
                                             (mset :subs (union-equal (mget :subs (mget p s))
                                                                      topics)
                                                   (mget p s))
                                             s)))))))))


  (propertyd prop=pending-!in-seen-s-fn-unsubscribe (s :s-fn p :peer topics :lot)
    :h (^ (mget p s)
          (pending-!in-seen-s-fn s))
    (pending-!in-seen-s-fn (unsubscribe-fn p topics s))
    :instructions
    (:pro
     (= (unsubscribe-fn p topics s)
        (set-subs-sfn (ps-fn-nbrs (mget p s))
                      topics
                      p
                      (mset p 
                            (mset :subs (set-difference-equal
                                         (mget :subs (mget p s))
                                         topics)
                                  (mget p s))
                            s)))
     
     (:claim (pending-!in-seen-s-fn
              (mset p 
                    (mset :subs (set-difference-equal
                                 (mget :subs (mget p s))
                                 topics)
                          (mget p s))
                    s))
             :hints (("Goal" :use ((:instance
                                    prop=pending-!in-seen-set-subs-sfn
                                    (ts (set-difference-equal
                                         (mget :subs (mget p s))
                                         topics)))))))

     (:prove :hints (("Goal" :use ((:instance
                                    prop=pending-!in-seen-set-nsubs-sfn
                                    (nbrs (ps-fn-nbrs (mget p s)))
                                    (s (mset p 
                                             (mset :subs (set-difference-equal
                                                          (mget :subs (mget p s))
                                                          topics)
                                                   (mget p s))
                                             s))))))))))

(in-theory (enable leave-fn
                   join-fn))

(property prop=pending-!in-seen-s-fn-leave (s :s-fn p :peer)
  :h (^ (mget p s)
        (pending-!in-seen-s-fn s))
  (pending-!in-seen-s-fn (leave-fn p s)))


(encapsulate ()
  (local
   (property prop=pending-!in-seen-ps-fn-new-joinee-st
     (pubs subs :lot nbrs :lop ms :lom s :s-fn)
     (pending-!in-seen-ps-fn
      (new-joinee-st-fn pubs subs nbrs s)
      ms)))
  
  (local
   (property prop=pending-!in-seen-s-fn-new-joinee-st (p :peer pst :ps-fn s :s-fn)
     :h (^ (! (mget p s))
           (pending-!in-seen-s-fn s)
           (== (mget :pending pst) nil)
           (== (mget :seen pst) nil))
     (pending-!in-seen-s-fn (mset p pst s))))

   (propertyd prop=pending-!in-seen-s-fn-join (p :peer pubs subs :lot nbrs :lop s :s-fn)
     :h (^ (! (mget p s))
           (! (in p nbrs))
           (pending-!in-seen-s-fn s))
     (pending-!in-seen-s-fn (join-fn p pubs subs nbrs s))
     :instructions
     (:pro
      (:claim (== (mget :pending (new-joinee-st-fn pubs subs nbrs s))
                  nil))
      (:claim (== (mget :seen (new-joinee-st-fn pubs subs nbrs s))
                  nil))
      (:claim (pending-!in-seen-s-fn (mset p
                                           (new-joinee-st-fn pubs subs nbrs s)
                                           s))
              :hints (("Goal" :use ((:instance
                                     prop=pending-!in-seen-s-fn-new-joinee-st
                                     (pst (new-joinee-st-fn pubs subs nbrs
                                                            s)))))))
      (= (join-fn p pubs subs nbrs s)
      (set-subs-sfn nbrs
                    subs
                    p
                    (mset p
                          (new-joinee-st-fn pubs subs nbrs s)
                          s)))
      
      (:prove :hints (("Goal" :use ((:instance
                                     prop=pending-!in-seen-set-nsubs-sfn
                                     (s (mset p (new-joinee-st-fn pubs subs nbrs s)
                                              s))))))))))
   


(encapsulate ()
  (local
   (property prop=!in-insert (x y :all xs :tl)
     :h (^ (!= x y)
           (! (in x xs)))
     (! (in x (insert-unique y xs)))))
  (local
   (property prop=pending-!in-seen-ps-fn-remove-pending
     (pst :ps-fn m :mssg ms :lom)
     :h (pending-!in-seen-ps-fn pst ms)
     (pending-!in-seen-ps-fn pst (remove-equal m ms))))

  (local
   (property prop=pending-!in-seen-ps-fn-remove-pending-insert-seen
     (pst :ps-fn m :mssg ms :lom)
     :h (pending-!in-seen-ps-fn pst ms)
     (pending-!in-seen-ps-fn (mset :seen
                                   (insert-unique m (mget :seen pst))
                                   pst)
                             (remove-equal m ms))))

  (local
   (property prop=pending-!in-seen-ps-fn-forwarder-new-pst
     (pst :ps-fn m :mssg ms :lom)
     :h (pending-!in-seen-ps-fn pst ms)
     (pending-!in-seen-ps-fn (mset :seen
                                   (insert-unique m (mget :seen pst))
                                   (mset :pending
                                         (remove-equal m (mget :pending pst))
                                         pst))
                             (remove-equal m ms))))

  (local
   (property prop=pending-!in-seen-ps-fn-forwarder-new-pst1
     (pst :ps-fn m :mssg ms :lom)
     :h (^ (in m ms)
           (pending-!in-seen-ps-fn pst ms))
     (pending-!in-seen-ps-fn (forwarder-new-pst pst m)
                             (remove-equal m ms))
     :hints (("Goal" :in-theory (enable forwarder-new-pst)
              :use ((:instance prop=pending-!in-seen-ps-fn-forwarder-new-pst))))))

  (local
   (property prop=pending-!in-seen-ps-fn-forwarder-new-pst2
     (pst :ps-fn m :mssg)
     :h (^ (in m (mget :pending pst))
           (pending-!in-seen-ps-fn pst (mget :pending pst)))
     (pending-!in-seen-ps-fn (forwarder-new-pst pst m)
                             (mget :pending (forwarder-new-pst pst m)))
     :instructions
     (:pro
      (= (mget :pending (forwarder-new-pst pst m))
         (remove-equal m (mget :pending pst))
         :hints (("Goal" :in-theory (enable forwarder-new-pst))))
      (:prove :hints (("Goal" :use ((:instance
                                     prop=pending-!in-seen-ps-fn-forwarder-new-pst1
                                     (ms (mget :pending pst))))))))))


  (property prop=pending-!in-seen-s-fn-update-forwarder
    (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s)))
          (pending-!in-seen-s-fn s))
    (pending-!in-seen-s-fn (update-forwarder-fn p m s))))        




(encapsulate ()
  (local
   (property prop=pending-!in-seen-ps-fn-h1 (m :mssg ms :lom
                                               pst :ps-fn)
     :h (pending-!in-seen-ps-fn pst ms)
     (pending-!in-seen-ps-fn (add-pending-psfn m pst) ms)
     :hints (("Goal" :in-theory (enable add-pending-psfn)))))

  (local
   (property prop=pending-!in-seen-ps-fn-h2 (m :mssg ms :lom
                                               pst :ps-fn)
     :h (^ (pending-!in-seen-ps-fn pst ms)
           (not (member-equal m (mget :pending pst)))
           (not (member-equal m (mget :seen pst))))
     (pending-!in-seen-ps-fn (add-pending-psfn m pst)
                             (cons m ms))
     :hints (("Goal" :in-theory (enable add-pending-psfn)))))

  (local
   (property prop=pending-!in-seen-ps-fn-help (m :mssg ms :lom
                                                 pst :ps-fn)
     :h (pending-!in-seen-ps-fn pst (mget :pending pst))
     (pending-!in-seen-ps-fn (add-pending-psfn m pst)
                             (mget :pending (add-pending-psfn m pst)))
     :hints (("Goal" :in-theory (enable add-pending-psfn)
              :use ((:instance prop=pending-!in-seen-ps-fn-h1
                               (ms (mget :pending pst)))
                    (:instance prop=pending-!in-seen-ps-fn-h2
                               (ms (mget :pending pst))))))))
  
  (local
   (property prop=pending-!in-seen-s-fn-forward-help
     (nbrs :lop m :mssg s :s-fn)
     :h (pending-!in-seen-s-fn s)
     (pending-!in-seen-s-fn (forward-help-fn s nbrs m))
     :instructions
     (:pro
      :induct :pro :bash
      :pro
      (:claim (pending-!in-seen-s-fn (cdr s)))
      (:claim (pending-!in-seen-s-fn (forward-help-fn (cdr s) nbrs m)))
      (:dv 1) (:r 2) :s
      
      (:casesplit (in (car (car s)) nbrs)) :s :up :r :s
      (:claim (pending-!in-seen-ps-fn (cdar s)
                                      (mget :pending (cdar s))))
      (:prove :hints (("Goal" :use ((:instance prop=pending-!in-seen-ps-fn-help
                                               (pst (cdr (car s))))))))
      (= (cons (cons (car (car s))
                     (add-pending-psfn m (cdr (car s))))
               (forward-help-fn (cdr s) nbrs m))
         (forward-help-fn s nbrs m)
         :hints (("Goal" :in-theory (enable forward-help-fn))))
      :s
      
      :s :up :r :s
      (:claim (pending-!in-seen-ps-fn (cdar s)
                                      (mget :pending (cdar s))))
      :s
      (= (cons (car s)
               (forward-help-fn (cdr s) nbrs m))
         (forward-help-fn s nbrs m)
         :hints (("Goal" :in-theory (enable forward-help-fn))))
      :s

      :pro
      (:prove :hints (("Goal" :in-theory (enable forward-help-fn)))))))



  (propertyd prop=pending-!in-seen-s-fn-forward (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s)))
          (pending-!in-seen-s-fn s))
    (pending-!in-seen-s-fn (forward-fn p m s))
    :instructions
    (:pro
     (:claim (pending-!in-seen-s-fn (update-forwarder-fn p m s)))
     (= (forward-fn p m s)
        (forward-help-fn (update-forwarder-fn p m s)
                         (mget (mssg-tp m)
                               (mget :nsubs (mget p s)))
                         m)
        :hints (("Goal" :in-theory (enable forward-fn))))
     (:prove :hints (("Goal" :use ((:instance
                                    prop=pending-!in-seen-s-fn-forward-help
                                    (nbrs (mget (mssg-tp m)
                                                (mget :nsubs
                                                      (mget p s))))))))))))

(in-theory (disable pending-!in-seen-ps-fn
                    pending-!in-seen-s-fn
                    prop=pending-!in-seen-ps-fn
                    prop=pending-!in-seen-ps-fn-set-pending))

(definec p!in-nsubs-ps-fn-help (p :peer nsubs :topic-lop-map) :bool
  (match nsubs
    (() t)
    (((& . ps) . rst)
     (^ (! (in p ps))
        (p!in-nsubs-ps-fn-help p rst)))))

(definec p!in-nsubs-ps-fn (p :peer st :ps-fn) :bool
  :body-contracts-hints (("Goal" :in-theory (enable ps-fnp)))
  (p!in-nsubs-ps-fn-help p (mget :nsubs st)))


(encapsulate ()
  (local
   (property prop=p!in-nsubs-ps-fn-help (p :peer tp :topic nsubs :topic-lop-map)
     :check-contracts? nil
     :h (p!in-nsubs-ps-fn-help p nsubs)
     (! (in p (mget tp nsubs)))))
  
  (property prop=p!in-nsubs-ps-fn (p :peer tp :topic st :ps-fn)
     :check-contracts? nil
     :h (p!in-nsubs-ps-fn p st)
     (! (in p (mget tp (mget :nsubs st))))))


(definec p!in-nsubs-s-fn (s :s-fn) :bool
  (match s
    (() t)
    (((p . pst) . rst)
     (^ (p!in-nsubs-ps-fn p pst)
        (p!in-nsubs-s-fn rst)))))

(propertyd prop=p!in-nsubs-s-fn (p :peer tp :topic s :s-fn)
     :check-contracts? nil
     :h (^ (mget p s)
           (p!in-nsubs-s-fn s))
     (! (in p (mget tp (mget :nsubs (mget p s))))))


(propertyd prop=p!in-nsubs-s-fn-produce (s :s-fn m :mssg)
  :check-contracts? nil
  :h (^ (p!in-nsubs-s-fn s)
        (produce-fn-pre m s))
  (p!in-nsubs-s-fn (produce-fn m s))
  :instructions
  (:pro (:dv 1) (:r produce-fn) :s :top
        :induct :pro
        (:claim (produce-fn-pre m (cdr s)))
        (:claim (p!in-nsubs-s-fn (cdr s)))
        (:claim (p!in-nsubs-s-fn (mset (mget :or m)
                                       (add-pending-psfn m (mget (mget :or m) (cdr s)))
                                       (cdr s))))
        (= (mset (mget :or m)
                 (add-pending-psfn m (mget (mget :or m) s))
                 s)
           (cons (car s)
                 (mset (mget :or m)
                       (add-pending-psfn m (mget (mget :or m) s))
                       (cdr s))))
        (= (mget (mget :or m) s)
           (mget (mget :or m) (cdr s)))
        (:claim (s-fnp (cons (car s)
                             (mset (mget :or m)
                                   (add-pending-psfn m (mget (mget :or m) (cdr s)))
                                   (cdr s)))))
        (= (^ (p!in-nsubs-ps-fn (caar s) (cdar s))
              (p!in-nsubs-s-fn (mset (mget :or m)
                                     (add-pending-psfn m (mget (mget :or m) (cdr s)))
                                     (cdr s)))))
        (:claim (p!in-nsubs-ps-fn (car (car s))
                                  (cdr (car s))))
        :s

        :pro
        (= (mget :or m) (caar s))
        (= (mget (car (car s)) s) (cdar s))
        (:claim (add-pending-psfn m (cdr (car s))))
        (= (add-pending-psfn m (cdar s))
           (mset :pending
                 (cons m (mget :pending (cdar s)))
                 (cdr (car s)))
           :hints (("Goal" :in-theory (enable add-pending-psfn))))
         (:dv 1) :r :s :s :up
         (= (mget :or m) (caar s))
         (:claim (p!in-nsubs-s-fn (cdr s)))
         (:claim (p!in-nsubs-ps-fn (car (car s))
                                   (cdr (car s))))
         :prove :bash :bash))


(encapsulate ()
  (local
   (property prop=p!in-nsubs-ps-fn-set-subs-help0
     (tp :topic topics :lot n p :peer acc :topic-lop-map ps :lop)
     :h (^ (p!in-nsubs-ps-fn-help n acc)
           (! (in n ps))
           (!= p n))
     (p!in-nsubs-ps-fn-help n
                            (mset tp ps acc))))

  (local
   (property prop=p!in-nsubs-ps-fn-set-subs-help1
     (tp :topic topics :lot n p :peer acc :topic-lop-map ps :lop)
     :h (^ (p!in-nsubs-ps-fn-help n acc)
           (! (in n ps))
           (!= p n))
     (p!in-nsubs-ps-fn-help n
                            (mset tp
                                  (union-equal (list p) ps)
                                  acc))))

  (local
   (property prop=p!in-nsubs-ps-fn-set-subs-help2
     (tp :topic topics :lot n p :peer acc :topic-lop-map ps :lop)
     :h (^ (p!in-nsubs-ps-fn-help n acc)
           (! (in n ps))
           (!= p n))
     (p!in-nsubs-ps-fn-help n
                            (mset tp
                                  (remove-equal p ps)
                                  acc))
     :instructions
     (:pro
      (:claim (! (in n (remove-equal p ps))))
      (:prove :hints (("Goal" :use ((:instance
                                     prop=p!in-nsubs-ps-fn-set-subs-help0
                                     (ps (remove-equal p ps))))))))))

  (local
   (property prop=p!in-nsubs-ps-fn-set-subs
     (topics :lot n p :peer nsubs acc :topic-lop-map)
     :h (^ (p!in-nsubs-ps-fn-help n nsubs)
           (p!in-nsubs-ps-fn-help n acc)
           (!= p n))
     (p!in-nsubs-ps-fn-help n (set-subs topics p nsubs acc))
     :instructions
     (:pro (:induct (set-subs topics p nsubs acc))
           :bash
           
           :pro
           (:dv 2) :r :s
           (:claim (p!in-nsubs-ps-fn-help n (cdr nsubs)))
           (:claim (p!in-nsubs-ps-fn-help
                    n
                    (set-subs topics p (cdr nsubs)
                              (if (in (car (car nsubs)) topics)
                                  (mset (car (car nsubs))
                                        (union-equal (list p) (cdr (car nsubs)))
                                        acc)
                                (mset (car (car nsubs))
                                      (remove-equal p (cdr (car nsubs)))
                                      acc)))))
           :top :bash

           :pro
           (= (set-subs topics p nsubs acc)
              acc
              :hints (("Goal" :in-theory (enable set-subs))))
           :prove)))

  (local
   (property prop=p!in-nsubs-ps-fn-set-nsubs (p n :peer st :ps-fn
                                                nbrs :lop topics :lot)
     :h (^ (p!in-nsubs-ps-fn n st)
           (! (in p nbrs)))
     (p!in-nsubs-ps-fn n (set-subs-psfn nbrs topics n p st))
     :instructions
     (:pro
      (= (set-subs-psfn nbrs topics n p st)
         (if (in n nbrs)
             (mset :nsubs (set-subs topics p (mget :nsubs st) '()) st)
           st)
         :hints (("Goal" :in-theory (enable set-subs-psfn))))
      (:casesplit (in n nbrs))
      :s

      (:claim (p!in-nsubs-ps-fn-help n nil))
      (:claim (p!in-nsubs-ps-fn-help n (mget :nsubs st)))
      (:claim (!= p n))
      (:claim (p!in-nsubs-ps-fn-help n (set-subs topics p (mget :nsubs st)
                                                 nil)))
      :prove
      :s)))

   (property prop=p!in-nsubs-s-fn-set-subs (nbrs :lop topics :lot p :peer s :s-fn)
     :h (^ (p!in-nsubs-s-fn s)
           (! (in p nbrs)))
     (p!in-nsubs-s-fn (set-subs-sfn nbrs topics p s))
     :instructions
     (:pro
      :induct :bash
      :pro
      (:claim (p!in-nsubs-s-fn (cdr s)))
      (:claim (p!in-nsubs-s-fn (set-subs-sfn nbrs topics p (cdr s))))
      (:dv 1) :r :s :up :r :s :prove
      (= (cons (cons (car (car s))
                     (set-subs-psfn nbrs topics (car (car s))
                                    p (cdr (car s))))
               (set-subs-sfn nbrs topics p (cdr s)))
         (set-subs-sfn nbrs topics p s)
         :hints (("Goal" :in-theory (enable set-subs-sfn))))
      :s :prove))

  (local
   (property not-in-union-equal (x y :tl p :all)
     (== (^ (! (in p x))
            (! (in p y)))
         (! (in p (union-equal x y))))))

  (local
   (property prop=p!in-nsubs-ps-fn-nbrs-help (p :peer nsubs :topic-lop-map acc :lop)
     :h (^ (! (in p acc))
           (p!in-nsubs-ps-fn-help p nsubs))
     (! (in p (ps-fn-nbrs-help nsubs acc)))
     :instructions
     (:pro :induct :bash
           :pro
           (:claim (p!in-nsubs-ps-fn-help p (cdr nsubs)))
           (:claim (! (in p (cdr (car nsubs)))))
           (:claim (! (in p (union-equal (cdr (car nsubs)) acc)))
                   :hints (("Goal" :use ((:instance not-in-union-equal
                                                    (x (cdr (car nsubs)))
                                                    (y acc))))))
           (:claim (not (in p
                            (ps-fn-nbrs-help (cdr nsubs)
                                             (union-equal (cdr (car nsubs)) acc)))))
           (:dv 1 2) :r :s :top :s

           :pro
           (= (ps-fn-nbrs-help nsubs acc)
              acc
              :hints (("Goal" :in-theory (enable ps-fn-nbrs-help))))
           :s)))

  (local
   (property prop=p!in-nsubs-ps-fn-nbrs (p :peer st :ps-fn)
     :h (p!in-nsubs-ps-fn p st)
     (! (in p (ps-fn-nbrs st)))
     :hints (("Goal" :in-theory (enable ps-fn-nbrs)))))

  (local
   (property prop=p!in-nsubs-s-fn-mset (p :peer ts :lot s :s-fn)
     :h (^ (mget p s)
           (p!in-nsubs-s-fn s))
     (p!in-nsubs-s-fn (mset p
                            (mset :subs ts (mget p s))
                            s))))
  
  (propertyd prop=p!in-nsubs-s-fn-subscribe (p :peer topics :lot s :s-fn)
     :h (^ (mget p s)
           (p!in-nsubs-s-fn s))
     (p!in-nsubs-s-fn (subscribe-fn p topics s))
     :instructions
     (:pro
      (= (subscribe-fn p topics s)
         (set-subs-sfn (ps-fn-nbrs (mget p s))
                       topics
                       p
                       (mset p 
                             (mset :subs (union-equal (mget :subs (mget p s))
                                                      topics)
                                   (mget p s))
                             s))
         :hints (("Goal" :in-theory (enable subscribe-fn))))

      (:claim (! (in p (ps-fn-nbrs (mget p s)))))
      (:claim (p!in-nsubs-s-fn (mset p
                                     (mset :subs
                                           (union-equal (mget :subs (mget p s))
                                                        topics)
                                           (mget p s))
                                     s)))
      :prove))


  (propertyd prop=p!in-nsubs-s-fn-unsubscribe (p :peer topics :lot s :s-fn)
    :h (^ (mget p s)
          (p!in-nsubs-s-fn s))
    (p!in-nsubs-s-fn (unsubscribe-fn p topics s))
    :instructions
    (:pro
     (= (unsubscribe-fn p topics s)
        (set-subs-sfn (ps-fn-nbrs (mget p s))
                      topics
                      p
                      (mset p 
                            (mset :subs (set-difference-equal
                                         (mget :subs (mget p s))
                                         topics)
                                  (mget p s))
                            s))
        :hints (("Goal" :in-theory (enable unsubscribe-fn))))

     (:claim (! (in p (ps-fn-nbrs (mget p s)))))
     (:claim (p!in-nsubs-s-fn (mset p
                                    (mset :subs
                                          (set-difference-equal
                                           (mget :subs (mget p s))
                                           topics)
                                          (mget p s))
                                    s)))
     :prove))

  (local
   (property prop=p!in-nsubs-ps-fn-calc-nsubs-fn
     (p :peer nbrs :lop s :s-fn acc :topic-lop-map)
     :h (^ (p!in-nsubs-ps-fn-help p acc)
           (! (in p nbrs)))
     (p!in-nsubs-ps-fn-help p (calc-nsubs-fn nbrs s acc))
     :instructions
     (:pro
      :induct :bash
      :pro
      (:claim (p!in-nsubs-ps-fn-help p nil))
      (:claim (!= p (car nbrs)))
      (:claim (p!in-nsubs-ps-fn-help p
                                     (set-subs (mget :subs
                                                     (mget (car nbrs)
                                                           s))
                                               (car nbrs)
                                               acc nil))
              :hints (("Goal" :use ((:instance prop=p!in-nsubs-ps-fn-set-subs
                                               (n p)
                                               (p (car nbrs))
                                               (nsubs acc)
                                               (acc nil))))))
      (:claim (p!in-nsubs-ps-fn-help
               p
               (calc-nsubs-fn (cdr nbrs)
                              s
                              (set-subs (mget :subs (mget (car nbrs) s))
                                        (car nbrs)
                                        acc nil))))
      (:dv 2) :r :s :top :s
      :pro
      (:claim (p!in-nsubs-ps-fn-help p (calc-nsubs-fn
                                        (cdr nbrs) s acc)))
      (:dv 2) :r :s :top :s
      :pro
      (= (calc-nsubs-fn nbrs s acc)
         acc
         :hints (("Goal" :in-theory (enable calc-nsubs-fn))))
      :s)))
  
  
  (local
   (property prop=p!in-nsubs-ps-fn-new-joinee-st
     (p :peer pubs subs :lot nbrs :lop s :s-fn)
     :h (! (in p nbrs))
     (p!in-nsubs-ps-fn p (new-joinee-st-fn pubs subs nbrs s))
     :instructions
     (:pro
      (:dv 2) (:r 2) :s :top
      :r :s
      (:casesplit (calc-nsubs-fn nbrs s nil)) :s
      (:claim (p!in-nsubs-ps-fn-help p nil))
      (:prove :hints
              (("Goal" :use ((:instance
                              prop=p!in-nsubs-ps-fn-calc-nsubs-fn
                              (acc nil))))))
      :s
      (:claim (p!in-nsubs-ps-fn-help p nil)) :s :s
      (:dv 1)
      (= (new-joinee-st-fn pubs subs nbrs s))
      :top :s)))

  (local
   (property prop=p!in-nsubs-s-fn-mset-pst (p :peer st :ps-fn s :s-fn)
     :h (^ (p!in-nsubs-ps-fn p st)
           (p!in-nsubs-s-fn s))
     (p!in-nsubs-s-fn (mset p st s))))


  (propertyd prop=p!in-nsubs-s-fn-join
    (p :peer pubs subs :lot nbrs :lop s :s-fn)
    :h (^ (! (mget p s))
          (! (in p nbrs))
          (p!in-nsubs-s-fn s))
    (p!in-nsubs-s-fn (join-fn p pubs subs nbrs s))
    :instructions
    (:pro
     (= (join-fn p pubs subs nbrs s)
        (set-subs-sfn nbrs
                      subs
                      p
                      (mset p
                            (new-joinee-st-fn pubs subs nbrs s)
                            s)))
     (:claim (p!in-nsubs-ps-fn p (new-joinee-st-fn pubs subs nbrs s))
             :hints (("Goal"
                      :use ((:instance
                             prop=p!in-nsubs-ps-fn-new-joinee-st)))))
     (:claim (p!in-nsubs-s-fn (mset p
                                    (new-joinee-st-fn
                                     pubs subs nbrs s)
                                    s))
             :hints (("Goal" :use ((:instance
                                    prop=p!in-nsubs-s-fn-mset-pst
                                    (st (new-joinee-st-fn
                                         pubs subs nbrs s)))))))
     
     (:prove :hints (("Goal" :use ((:instance prop=p!in-nsubs-s-fn-set-subs
                                              (topics subs)
                                              (s (mset p (new-joinee-st-fn pubs subs nbrs s)
                                                       s))))))))))



(property prop=p!in-nsubs-s-fn-leave (p :peer s :s-fn)
  :h (^ (mget p s)
        (p!in-nsubs-s-fn s))
  (p!in-nsubs-s-fn (leave-fn p s))
  :instructions
  (:pro :induct :bash
        :pro
        (:claim (p!in-nsubs-s-fn (cdr s)))
        (:claim (p!in-nsubs-s-fn (leave-fn p (cdr s))))
        (:dv 1) (:r 2) :s :top
        (:casesplit (equal (car (car s)) p)) :s
        :s :r :s :bash
        (= (cons (car s) (leave-fn p (cdr s)))
           (leave-fn p s))
        :s :bash :bash))


(encapsulate ()
  (local
   (property prop=p!in-nsubs-s-fn-forwarder-new-pst (p :peer m :mssg st :ps-fn)
     :h (p!in-nsubs-ps-fn p st)
     (p!in-nsubs-ps-fn p (forwarder-new-pst st m))
     :instructions
     (:pro
      (:dv 2) (:r forwarder-new-pst) :s :top
      (:r p!in-nsubs-ps-fn)
      (:claim (ps-fnp (mset :pending
                            (remove-equal m (mget :pending st))
                            (mset :seen (insert-unique m (mget :seen st))
                                  st))))
      :s :bash)))

  (local
   (property prop=p!in-nsubs-s-fn-update-forwarder
     (p :peer m :mssg s :s-fn)
     :h (^ (mget p s)
           (in m (mget :pending (mget p s)))
           (p!in-nsubs-s-fn s))
     (p!in-nsubs-s-fn (update-forwarder-fn p m s))
     :instructions
     (:pro :induct :bash
           :pro
           (:claim (mget p (cdr s)))
           (:claim (in m (mget :pending (mget p (cdr s)))))
           (:claim (p!in-nsubs-s-fn (cdr s)))
           (:claim (p!in-nsubs-s-fn (update-forwarder-fn p m (cdr s))))
           (:dv 1) (:r update-forwarder-fn) :s :up
           (:casesplit (equal (car (car s)) p)) :s :bash
           :s :r :s :bash :prove
           :pro
           (:dv 1) (:r update-forwarder-fn)
           :s :up :bash :bash)))

  (local
   (property prop=p!in-nsubs-s-fn-forward-help (m :mssg nbrs :lop s :s-fn)
     :h (p!in-nsubs-s-fn s)
     (p!in-nsubs-s-fn (forward-help-fn s nbrs m))
     :instructions
     (:pro
      :induct :pro :bash
      :pro
      (:claim (p!in-nsubs-s-fn (cdr s)))
      (:claim (p!in-nsubs-s-fn (forward-help-fn (cdr s) nbrs m)))
      (:dv 1) (:r forward-help-fn) :s :up

      (:casesplit (in (car (car s)) nbrs)) :s
      :r :s
      (:claim (ps-fnp (add-pending-psfn m (cdr (car s)))))
      (:claim (s-fnp (cons (cons (car (car s))
                                 (add-pending-psfn m (cdr (car s))))
                           (forward-help-fn (cdr s) nbrs m)))
              :hints (("Goal" :in-theory (enable forward-help-fn))))
      
      (= (^ (p!in-nsubs-ps-fn (caar s) (add-pending-psfn m (cdr (car s))))
            (p!in-nsubs-s-fn (forward-help-fn (cdr s) nbrs m))))
      (:claim (== (mget :nsubs (add-pending-psfn m (cdr (car s))))
                  (mget :nsubs (cdr (car s))))
              :hints (("Goal" :in-theory (enable add-pending-psfn))))
      :s :bash

      (= (cons (cons (car (car s))
                     (add-pending-psfn m (cdr (car s))))
               (forward-help-fn (cdr s) nbrs m))
         (forward-help-fn s nbrs m)
         :hints (("Goal" :in-theory (enable forward-help-fn))))
      :s :s
      (:claim (s-fnp (cons (car s)
                           (forward-help-fn (cdr s) nbrs m)))
              :hints (("Goal" :in-theory (enable forward-help-fn))))
      (= (^ (p!in-nsubs-ps-fn (caar s) (cdr (car s)))
            (p!in-nsubs-s-fn (forward-help-fn (cdr s) nbrs m))))
      :bash :s
      :pro
      (:prove :hints (("Goal" :in-theory (enable forward-help-fn)))))))

  (propertyd prop=p!in-nsubs-s-fn-forward (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s)))
          (p!in-nsubs-s-fn s))
    (p!in-nsubs-s-fn (forward-fn p m s))
    :instructions
    (:pro
     
     (= (forward-fn p m s)
        (forward-help-fn (update-forwarder-fn p m s)
                         (mget (mssg-tp m)
                               (mget :nsubs (mget p s)))
                         m)
        :hints (("Goal" :in-theory (enable forward-fn))))

     (:claim (p!in-nsubs-s-fn (update-forwarder-fn p m s)))

     (:prove :hints (("Goal"
                      :use ((:instance prop=p!in-nsubs-s-fn-forward-help
                                       (s (update-forwarder-fn p m s))
                                       (nbrs (mget (mssg-tp m)
                                                   (mget :nsubs (mget p s))))))))))))







(definec pending-origins-ps-fn (m :mssg pst :all) :bool
  (^ (ps-fnp pst)
     (in (mget :tp m)
         (mget :pubs pst))))
  
(definec pending-origins-s-fn-help (ms :lom s :s-fn) :bool
  (match ms
    (() t)
    ((m . rs) (^ (pending-origins-ps-fn m (mget (mget :or m) s))
                 (pending-origins-s-fn-help rs s)))))
                 
(definec pending-origins-s-fn (s :s-fn) :bool
  (pending-origins-s-fn-help (fn-pending-mssgs s) s))

(encapsulate ()
  (local
   (property prop=pending-origins-s-fn-help (m :mssg ms :lom s :s-fn)
     :h (^ (in m ms)
           (pending-origins-s-fn-help ms s))
     (^ (mget (mget :or m) s)
        (in (mget :tp m)
            (mget :pubs (mget (mget :or m) s))))))

  (propertyd prop=pending-origins-s-fn (m :mssg s :s-fn)
    :h (^ (in m (fn-pending-mssgs s))
          (pending-origins-s-fn s))
    (^ (mget (mget :or m) s)
       (in (mget :tp m)
           (mget :pubs (mget (mget :or m) s))))))
  
(encapsulate ()
  (local
   (property prop=pending-origins-s-fn-produce-help (s :s-fn m :mssg ms :lom)
     :h (^ (pending-origins-s-fn-help ms s)
           (produce-fn-pre m s))
     (pending-origins-s-fn-help (insert-unique m ms) s)))

  (local
   (property prop=pending-origins-s-fn-produce-help2
     (s :s-fn p q :peer pst :ps-fn)
     :h (mget q s)
     (mget q (mset p pst s))))

  (local
   (property prop=pending-origins-s-fn-produce-help3
     (s :s-fn p q :peer tp :topic ms :lom pst :ps-fn)
     :check-contracts? nil
     :h (^ (mget q s)
           (in tp (mget :pubs (mget q s))))
     (in tp (mget :pubs (mget q (mset p
                                      (mset :pending ms (mget p s))
                                      s))))))

  (local
   (property prop=pending-origins-s-fn-produce-help4
     (m :mssg ns :lom pst :ps-fn)
     :h (pending-origins-ps-fn m pst)
     (pending-origins-ps-fn m (mset :pending ns pst))))
  

  (local
   (property prop=pending-origins-s-fn-produce-help5 (s :s-fn p :peer ms ns :lom)
     :h (^ (mget p s)
           (pending-origins-s-fn-help ms s))
     (pending-origins-s-fn-help ms (mset p
                                         (mset :pending ns (mget p s))
                                         s))
     :instructions
     (:pro (:induct (pending-origins-s-fn-help ms s))
           :bash :bash
           :pro :bash
           :pro
           (:claim (! (<< p (car (car s)))))
           (:claim (pending-origins-s-fn-help (cdr ms) s))
           (:claim (pending-origins-s-fn-help (cdr ms)
                                              (mset p (mset :pending ns (mget p s))
                                                    s)))
           (:dv 2) :r :s :top
           
           (:casesplit (== p (car (car s)))) :s
           (:claim (mset :pending ns (cdr (car s)))) :s :bash
           :s :r :s :s :prove)))


  (local
   (property prop=in->member-equal (m :all x :tl)
     :h (! (in m x))
     (! (member-equal m x))))

  (propertyd prop=pending-origins-s-fn-produce (s :s-fn m :mssg)
    :h (^ (pending-origins-s-fn s)
          (produce-fn-pre m s))
    (pending-origins-s-fn (produce-fn m s))
    :instructions
    (:pro
     (:dv 1) (:r produce-fn) :s :up
     (:claim (^ (! (in m (mget :pending (mget (mget :or m) s))))
                (! (in m (mget :seen (mget (mget :or m) s))))))
     (:claim (^ (! (member-equal m (mget :pending (mget (mget :or m) s))))
                (! (member-equal m (mget :seen (mget (mget :or m) s)))))
             :hints (("Goal" :use ((:instance prop=in->member-equal
                                              (x (mget :pending
                                                       (mget (mget :or m) s))))))))
     (= (add-pending-psfn m (mget (mget :or m) s))
        (mset :pending
              (cons m (mget :pending (mget (mget :or m) s)))
              (mget (mget :or m) s))
        :hints (("Goal" :in-theory (enable add-pending-psfn))))
     :r
     (= (fn-pending-mssgs (mset (mget :or m)
                                (mset :pending
                                      (cons m (mget :pending (mget (mget :or m) s)))
                                      (mget (mget :or m) s))
                                s))
        (insert-unique m (fn-pending-mssgs s)))

     (:claim (pending-origins-s-fn-help
              (insert-unique m (fn-pending-mssgs s))
              s))
     :prove
     :prove)))



(encapsulate ()
  (local
   (property prop=pending-origins-ps-fn-set-subs (st :ps-fn m :mssg ns :topic-lop-map)
     :h (pending-origins-ps-fn m st)
     (pending-origins-ps-fn m (mset :nsubs ns st))))

  (local
   (property prop=pending-origins-set-subs-psfn (nbrs :lop topics :lot m :mssg
                                                      n p :peer st :ps-fn)
     :h (pending-origins-ps-fn m st)
     (pending-origins-ps-fn m (set-subs-psfn nbrs topics n p st))))

  (local
   (in-theory (disable set-subs-psfn)))

  (local
   (property prop=pending-origins-set-subs-mget-sfn (nbrs :lop topics :lot
                                                          m :mssg p q :peer s :s-fn)
     :h (^ (mget p s)
           (pending-origins-ps-fn m (mget p s)))
     (pending-origins-ps-fn m (mget p (set-subs-sfn nbrs topics q s)))))

  (local
   (in-theory (disable set-subs-sfn)))

  (local
   (property prop=pending-origins-help-set-subs-sfn
     (nbrs :lop topics :lot p :peer ms :lom s :s-fn)
     :h (pending-origins-s-fn-help ms s)
     (pending-origins-s-fn-help ms (set-subs-sfn nbrs topics p s))
     :instructions
     (:pro (:induct (pending-origins-s-fn-help ms s))
           :bash :bash
           :pro
           (:claim (pending-origins-s-fn-help (cdr ms) s))
           (:claim (pending-origins-s-fn-help (cdr ms)
                                              (set-subs-sfn nbrs topics p s)))
           :r :s

           (:claim (pending-origins-ps-fn (car ms)
                                          (mget (mget :or (car ms)) s)))
           (:claim (mget (mget :or (car ms)) s))
           
           (:claim (pending-origins-ps-fn (car ms)
                                          (mget (mget :or (car ms))
                                                (set-subs-sfn nbrs topics p s)))
                   :hints (("Goal" :use ((:instance
                                          prop=pending-origins-set-subs-mget-sfn
                                          (m (car ms))
                                          (q p)
                                          (p (mget :or (car ms))))))))
           (:demote 16) (:dv 1) (:r pending-origins-ps-fn) :s :top :s

           :pro :bash)))

  (local
   (property prop=pending-origins-ps-fn-mset-subs (st :ps-fn m :mssg ts :lot)
     :h (pending-origins-ps-fn m st)
     (pending-origins-ps-fn m (mset :subs ts st))))


  (local
   (property prop=pending-origins-help-mset-sfn (p :peer pst :ps-fn ms :lom s :s-fn)
     :h (^ (mget p s)
           (pending-origins-s-fn-help ms s)
           (== (mget :pubs pst)
               (mget :pubs (mget p s))))
     (pending-origins-s-fn-help ms (mset p pst s))
     :instructions
     (:pro
      (:induct (tlp ms)) :bash
      :pro
      (:claim (pending-origins-s-fn-help (cdr ms) s))
      (:claim (pending-origins-s-fn-help (cdr ms)
                                         (mset p pst s)))
      (:claim (! (<< p (car (car s)))))
      (:dv 2) :r :s :top
      
      (:casesplit (== p (car (car s)))) :s
      :r :s :bash :bash

      :s :r :s
      (:casesplit (equal (mget :or (car ms))
                         (car (car s))))
      :s :prove
      :s
      (:claim (not (lexorder (mget :or (car ms))
                             (car (car s)))))
      (= (cons (car s) (mset p pst (cdr s)))
         (mset p pst s))

      :s

      (:casesplit (== p (mget :or (car ms))))
      (= p (mget :or (car ms))) :s :bash

      :s :bash
      (= (cons (car s) (mset p pst (cdr s)))
         (mset p pst s))
      :s)))
  
  
  (propertyd prop=pending-origins-s-fn-subscribe (s :s-fn p :peer topics :lot)
    :h (^ (mget p s)
          (pending-origins-s-fn s))
    (pending-origins-s-fn (subscribe-fn p topics s))
    :instructions
    (:pro
     (:dv 1) (:r subscribe-fn) :s :up

     (:claim (== (mget :pubs (mset :subs
                                   (union-equal (mget :subs (mget p s))
                                                topics)
                                   (mget p s)))
                 (mget :pubs (mget p s))))
     (:claim (pending-origins-s-fn-help (fn-pending-mssgs s) s))
     (:claim (pending-origins-s-fn-help
              (fn-pending-mssgs s)
              (mset p
                    (mset :subs
                          (union-equal (mget :subs (mget p s))
                                       topics)
                          (mget p s))
                    s))
             :hints (("Goal" :use ((:instance prop=pending-origins-help-mset-sfn
                                              (ms (fn-pending-mssgs s))
                                              (pst (mset :subs
                                                         (union-equal (mget :subs (mget p s))
                                                                      topics)
                                                         (mget p s))))))))
     
     (:prove :hints (("Goal" :use ((:instance
                                    prop=pending-origins-help-set-subs-sfn
                                    (nbrs (ps-fn-nbrs (mget p s)))
                                    (s (mset p
                                             (mset :subs
                                                   (union-equal (mget :subs (mget p s))
                                                                topics)
                                                   (mget p s))
                                             s)))))))))

  (propertyd prop=pending-origins-s-fn-unsubscribe (s :s-fn p :peer topics :lot)
    :h (^ (mget p s)
          (pending-origins-s-fn s))
    (pending-origins-s-fn (unsubscribe-fn p topics s))
    :instructions
    (:pro
     (:dv 1) (:r unsubscribe-fn) :s :up

     (:claim (== (mget :pubs (mset :subs
                                   (union-equal (mget :subs (mget p s))
                                                topics)
                                   (mget p s)))
                 (mget :pubs (mget p s))))
     (:claim (pending-origins-s-fn-help (fn-pending-mssgs s) s))
     (:claim (pending-origins-s-fn-help
              (fn-pending-mssgs s)
              (mset p
                    (mset :subs
                          (set-difference-equal
                           (mget :subs (mget p s))
                           topics)
                          (mget p s))
                    s))
             :hints (("Goal" :use ((:instance prop=pending-origins-help-mset-sfn
                                              (ms (fn-pending-mssgs s))
                                              (pst (mset :subs
                                                         (set-difference-equal
                                                          (mget :subs (mget p s))
                                                          topics)
                                                         (mget p s))))))))
     
     (:prove :hints (("Goal" :use ((:instance
                                    prop=pending-origins-help-set-subs-sfn
                                    (nbrs (ps-fn-nbrs (mget p s)))
                                    (s (mset p
                                             (mset :subs
                                                   (set-difference-equal
                                                    (mget :subs (mget p s))
                                                    topics)
                                                   (mget p s))
                                             s)))))))))

  (local
   (property prop=pending-origins-s-fn-set-subs
     (nbrs :lop topics :lot ms :lom p :peer s :s-fn)
     :h (^ (pending-origins-s-fn-help ms s)
           (! (in p nbrs)))
     (pending-origins-s-fn-help ms (set-subs-sfn nbrs topics p s))
     :hints (("Goal" :in-theory (enable set-subs-sfn)))))

  (local
   (property prop=mget-set-p (s :s-fn p q :peer qst :ps-fn)
     :h (^ (! (mget q s))
           (mget p s))
     (== (mget p (mset q qst s))
         (mget p s))))

  (local
   (property prop=pending-origins-s-fn-mset2 (s :s-fn p :peer pst :ps-fn ms :lom)
     :h (^ (! (mget p s))
           (pending-origins-s-fn-help ms s))
     (pending-origins-s-fn-help ms (mset p pst s))
     :instructions
     (:pro (:induct (pending-origins-s-fn-help ms s))
           :bash :bash
           :pro
           (:claim (pending-origins-s-fn-help (cdr ms) s))
           (:claim (pending-origins-s-fn-help (cdr ms)
                                              (mset p pst s)))

           (:claim (!= p (car (car s))))
           (:r pending-origins-s-fn-help) :s
           (:claim (mget (mget :or (car ms))
                         (mset p pst s)))
           (:claim (ps-fnp (mget (mget :or (car ms))
                                 (mset p pst s))))

           (:claim (== (mget (mget :or (car ms))
                             (mset p pst s))
                       (mget (mget :or (car ms)) s))
                   :hints (("Goal" :use ((:instance prop=mget-set-p
                                                    (p (mget :or (car ms)))
                                                    (qst pst))))))
           :s :bash :bash)))

  (local
   (property prop=pending-origins-help-s-fn-join (p :peer pubs subs :lot
                                                    nbrs :lop ms :lom s :s-fn)
     :h (^ (! (mget p s))
           (! (in p nbrs))
           (pending-origins-s-fn-help ms s))
     (pending-origins-s-fn-help ms (join-fn p pubs subs nbrs s))
     :instructions
     (:pro
      (= (join-fn p pubs subs nbrs s)
         (set-subs-sfn nbrs
                       subs
                       p
                       (mset p
                             (new-joinee-st-fn pubs subs nbrs s)
                             s))
         :hints (("Goal" :in-theory (enable join-fn))))
      (:claim (pending-origins-s-fn-help ms
                                         (mset p
                                               (new-joinee-st-fn pubs subs nbrs s)
                                               s))
              :hints (("Goal" :use ((:instance prop=pending-origins-s-fn-mset2
                                               (pst (new-joinee-st-fn
                                                     pubs subs nbrs s)))))))

      (:claim (s-fnp (mset p (new-joinee-st-fn pubs subs nbrs s) s)))
      (:prove :hints (("Goal" :use ((:instance
                                     prop=pending-origins-s-fn-set-subs
                                     (topics subs)
                                     (s (mset p (new-joinee-st-fn
                                                 pubs subs nbrs s)
                                              s))))))))))
  
  (propertyd prop=pending-origins-s-fn-join (p :peer pubs subs :lot
                                               nbrs :lop s :s-fn)
    :h (^ (! (mget p s))
          (! (in p nbrs))
          (pending-origins-s-fn s))
    (pending-origins-s-fn (join-fn p pubs subs nbrs s))
    :instructions
    (:pro :r
          (= (fn-pending-mssgs (join-fn p pubs subs nbrs s))
             (fn-pending-mssgs s)
             :hints (("Goal" :use ((:instance
                                    prop=f2b-join-pending-mssgs)))))
          (:claim (pending-origins-s-fn-help (fn-pending-mssgs s) s))
          (:prove :hints (("Goal" :use ((:instance
                                         prop=pending-origins-help-s-fn-join
                                         (ms (fn-pending-mssgs s))))))))))


(encapsulate ()
  (local
   (property prop=mget-pubs-forwarder-new-pst (pst :ps-fn m :mssg)
     (== (mget :pubs (forwarder-new-pst pst m))
         (mget :pubs pst))
     :hints (("Goal" :in-theory (enable forwarder-new-pst)))))

  (local
   (property prop=mget-pubs-update-forwarder-fn (s :s-fn p q :peer m :mssg)
     (== (mget :pubs (mget q (update-forwarder-fn p m s)))
         (mget :pubs (mget q s)))
     :hints (("Goal" :in-theory (enable update-forwarder-fn)))))

  (local
   (property prop=mget-pubs-update-forwarder-fn-mget (s :s-fn p q :peer m :mssg)
     :h (mget q s)
     (ps-fnp (mget q (update-forwarder-fn p m s)))
     :hints (("Goal" :in-theory (enable update-forwarder-fn)))))


  (property prop=pending-origins-s-fn-update-forwarder-help
    (p :peer m :mssg ms :lom s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s)))
          (pending-origins-s-fn-help ms s))
    (pending-origins-s-fn-help ms (update-forwarder-fn p m s))
    :instructions
    (:pro
     (:induct (pending-origins-s-fn-help ms s)) :bash
     :pro :bash
     :pro
     (:claim (pending-origins-s-fn-help (cdr ms)
                                        (update-forwarder-fn p m s)))
     (:claim (! (<< (mget :or (car ms)) (car (car s)))))
     :r :s :prove :bash)))

(encapsulate ()
  (local
   (property prop=pending-origins-ps-fn-add-pending-psfn (m n :mssg pst :ps-fn)
     :h (pending-origins-ps-fn m pst)
     (pending-origins-ps-fn m (add-pending-psfn n pst))
     :hints (("Goal" :in-theory (enable add-pending-psfn)))))

  (local
   (property prop=mget-pubs-add-pending-psfn (pst :ps-fn n :mssg)
     (== (mget :pubs (add-pending-psfn n pst))
         (mget :pubs pst))
     :hints (("Goal" :in-theory (enable add-pending-psfn)))))

  (local
   (property prop=mget-pubs-forward-help-fn (s :s-fn q :peer
                                               nbrs :lop m :mssg)
     :check-contracts? nil
     (== (mget :pubs (mget q (forward-help-fn s nbrs m)))
         (mget :pubs (mget q s)))
     :hints (("Goal" :in-theory (enable forward-help-fn)))))

  (local
   (property prop=mget-pubs-update-forward-help-fn-mget (s :s-fn q :peer nbrs :lop m :mssg)
     :h (mget q s)
     (ps-fnp (mget q (forward-help-fn s nbrs m)))
     :hints (("Goal" :in-theory (enable forward-help-fn)))))


  (property prop=pending-origins-s-fn-forward-help-fn
    (s :s-fn nbrs :lop m :mssg ms :lom)
    :h (pending-origins-s-fn-help ms s)
    (pending-origins-s-fn-help ms (forward-help-fn s nbrs m))
    :instructions
    (:pro
     (:induct (pending-origins-s-fn-help ms s)) :bash
     :pro :bash
     :pro
     (:claim (pending-origins-s-fn-help (cdr ms) s))
     (:claim (pending-origins-s-fn-help (cdr ms)
                                        (forward-help-fn s nbrs m)))
     :r :s :prove :bash)))

(property prop=pending-origins-s-fn-help-forward-fn (p :peer m :mssg
                                                  ms :lom s :s-fn)
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (pending-origins-s-fn-help ms s))
  (pending-origins-s-fn-help ms (forward-fn p m s))
  :instructions
  (:pro
   (= (forward-fn p m s)
      (forward-help-fn (update-forwarder-fn p m s)
                       (mget (mssg-tp m)
                             (mget :nsubs (mget p s)))
                       m)
      :hints (("Goal" :in-theory (enable forward-fn))))
   (:claim (pending-origins-s-fn-help ms (update-forwarder-fn p m s)))
   :prove))

(in-theory (disable prop=pending-origins-s-fn-forward-help-fn
                    prop=pending-origins-s-fn-update-forwarder-help
                    prop=p!in-nsubs-s-fn-set-subs))

(propertyd prop=pending-origins-s-fn-remove-ms (m :mssg ms :lom s :s-fn)
  :h (pending-origins-s-fn-help ms s)
  (pending-origins-s-fn-help (remove-equal m ms) s))

  
(propertyd prop=pending-origins-s-fn-forward-fn (p :peer m :mssg s :s-fn)
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (pending-origins-s-fn s))
  (pending-origins-s-fn (forward-fn p m s))
  :instructions
  (:pro
   (= (pending-origins-s-fn (forward-fn p m s))
      (pending-origins-s-fn-help (fn-pending-mssgs (forward-fn p m s))
                                 (forward-fn p m s)))
   (:casesplit (== (fn-pending-mssgs (forward-fn p m s))
                   (fn-pending-mssgs s)))
   :s
   (:claim (pending-origins-s-fn-help (fn-pending-mssgs s) s))
   (:r prop=pending-origins-s-fn-help-forward-fn)
   (= (fn-pending-mssgs (forward-fn p m s))
      (remove-equal m (fn-pending-mssgs s))
      :hints (("Goal" :use ((:instance prop=fn-pending-mssgs-forward-fn)))))
   (:prove :hints (("Goal" :use ((:instance
                                  prop=pending-origins-s-fn-remove-ms
                                  (ms (fn-pending-mssgs s)))))))))



  
(definec good-s-fnp (s :s-fn) :bool
  (^ (pending-!in-seen-s-fn s)
     (p!in-nsubs-s-fn s)
     (pending-origins-s-fn s)))


(in-theory (disable new-fn-mssgp pending-origins-ps-fn
                    produce-fn pending-origins-s-fn
                    produce-fn-pre pending-!in-seen-ps-fn
                    subscribe-fn pending-!in-seen-s-fn
                    unsubscribe-fn p!in-nsubs-ps-fn-help
                    set-subs-sfn p!in-nsubs-ps-fn
                    leave-fn p!in-nsubs-s-fn pending-origins-ps-fn
                    join-fn pending-origins-s-fn-help
                    pending-origins-s-fn
                    acl2::maximal-records-theory))
                    

(property prop=good-s-fn1 (s :s-fn p :peer m :mssg)
    :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (good-s-fnp s))
    (! (in m (mget :seen (mget p s))))
    :hints (("Goal" :use ((:instance prop=pending-!in-seen-s-fn)))))

(property prop=good-s-fn2 (p :peer tp :topic s :s-fn)
  :check-contracts? nil
  :h (^ (mget p s)
        (good-s-fnp s))
  (! (in p (mget tp (mget :nsubs (mget p s)))))
  :hints (("Goal" :use ((:instance prop=p!in-nsubs-s-fn)))))

(property prop=good-s-fn3 (m :mssg s :s-fn)
  :h (^ (in m (fn-pending-mssgs s))
        (good-s-fnp s))
  (^ (mget (mget :or m) s)
     (in (mget :tp m)
         (mget :pubs (mget (mget :or m) s))))
  :hints (("Goal" :use ((:instance prop=pending-origins-s-fn)))))


(property prop=good-s-fn-produce (s :s-fn m :mssg)
  :check-contracts? nil
  :h (^ (good-s-fnp s)
        (produce-fn-pre m s))
  (good-s-fnp (produce-fn m s))
  :hints (("Goal" :use ((:instance prop=pending-!in-seen-s-fn-produce)
                        (:instance prop=p!in-nsubs-s-fn-produce)
                        (:instance prop=pending-origins-s-fn-produce)))))


(property prop=good-s-fn-forward (p :peer m :mssg s :s-fn)
  :check-contracts? nil
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (good-s-fnp s))
  (good-s-fnp (forward-fn p m s))
  :hints (("Goal" :use ((:instance prop=pending-!in-seen-s-fn-forward)
                        (:instance prop=p!in-nsubs-s-fn-forward)
                        (:instance prop=pending-origins-s-fn-forward-fn)))))

(property prop=good-s-fn-subscribe (s :s-fn p :peer topics :lot)
  :h (^ (mget p s)
        (good-s-fnp s))
  (good-s-fnp (subscribe-fn p topics s))
  :hints (("Goal" :use ((:instance prop=pending-!in-seen-s-fn-subscribe)
                        (:instance prop=p!in-nsubs-s-fn-subscribe)
                        (:instance prop=pending-origins-s-fn-subscribe)))))

(property prop=good-s-fn-unsubscribe (s :s-fn p :peer topics :lot)
  :h (^ (mget p s)
        (good-s-fnp s))
  (good-s-fnp (unsubscribe-fn p topics s))
  :hints (("Goal" :use ((:instance prop=pending-!in-seen-s-fn-unsubscribe)
                        (:instance prop=p!in-nsubs-s-fn-unsubscribe)
                        (:instance prop=pending-origins-s-fn-unsubscribe)))))

(property prop=good-s-fn-join (p :peer pubs subs :lot nbrs :lop s :s-fn)
  :h (^ (! (mget p s))
        (! (in p nbrs))
        (good-s-fnp s))
  (good-s-fnp (join-fn p pubs subs nbrs s))
  :instructions
  (:pro
   (:claim (^ (pending-!in-seen-s-fn s)
              (p!in-nsubs-s-fn s)
              (pending-origins-s-fn s)))
           
   (:claim (pending-origins-s-fn (join-fn p pubs subs nbrs s))
           :hints (("Goal" :use ((:instance prop=pending-origins-s-fn-join)))))
   (:claim (pending-!in-seen-s-fn (join-fn p pubs subs nbrs s))
           :hints (("Goal" :use ((:instance prop=pending-!in-seen-s-fn-join)))))
   (:claim (p!in-nsubs-s-fn (join-fn p pubs subs nbrs s))
           :hints (("Goal" :use ((:instance prop=p!in-nsubs-s-fn-join)))))
   :bash))

(in-theory (disable good-s-fnp))
