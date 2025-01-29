(in-package "ACL2S")
(include-book "fn")

(definecd f2b-st (ps :ps-fn ms :lom) :ps-bn
  (ps-bn (mget :pubs ps)
         (mget :subs ps)
         (set-difference-equal (mget :seen ps) ms)))

(property prop=f2b-st-check (ps :ps-fn ms :lom)
  (^ (== (mget :pubs (f2b-st ps ms))
         (mget :pubs ps))
     (== (mget :subs (f2b-st ps ms))
         (mget :subs ps))
     (== (mget :seen (f2b-st ps ms))
         (set-difference-equal (mget :seen ps) ms)))
  :hints (("Goal" :in-theory (enable f2b-st ps-fnp ps-bnp))))

(property prop=f2b-st-check2 (ps :ps-fn)
  (^ (== (mget :pubs (f2b-st ps '()))
         (mget :pubs ps))
     (== (mget :subs (f2b-st ps '()))
         (mget :subs ps))
     (== (mget :seen (f2b-st ps '()))
         (mget :seen ps))))

(property prop=f2b-st-set-subs-psfn (nbrs :lop subs :lot n p :peer pst :ps-fn ms :lom)
  (== (f2b-st (set-subs-psfn nbrs subs n p pst) ms)
      (f2b-st pst ms))
  :hints (("Goal" :in-theory (enable f2b-st set-subs-psfn))))

(property prop=f2b-st-ignore-pending-mset (p :peer s :s-fn ms ls :lom pst :ps-fn)
          (== (f2b-st (mset :pending ms pst) ls)
              (f2b-st pst ls))
          :hints (("Goal" :in-theory (enable f2b-st))))

(property prop=f2b-st-add-pending (m :mssg pst :ps-fn ms :lom)
  (== (f2b-st (add-pending-psfn m pst) ms)
      (f2b-st pst ms))
  :hints (("Goal" :in-theory (enable f2b-st add-pending-psfn))))

(property prop=f2b-st-forwarder (m :mssg pst :ps-fn ms :lom)
  :h (in m ms)
  (equal (f2b-st (forwarder-new-pst pst m) ms)
         (f2b-st pst ms))
  :hints (("Goal" :in-theory (enable f2b-st forwarder-new-pst))))

;; We now define our refinement map f2b
(definec f2b-help (s :s-fn ms :lom) :s-bn
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (if (endp s)
      '()
    (cons `(,(caar s) . ,(f2b-st (cdar s) ms))
          (f2b-help (cdr s) ms))))

(property f2b-st-new-pending-mssg (s :s-fn m :mssg ms :lom)
  :h (^ (consp s)
        (new-fn-mssgp m s))
  (== (f2b-st (cdr (car s)) (insert-unique m ms))
      (f2b-st (cdr (car s)) ms))
  :hints (("Goal" :in-theory (enable new-fn-mssgp f2b-st ps-bnp)
           :use ((:instance insert-unique-diff (x (mget :seen (cdr (car s))))
                            (y ms))))))

(property f2b-help-new-pending-mssg (s :s-fn m :mssg ms :lom)
  :h (new-fn-mssgp m s)
  (== (f2b-help s (insert-unique m ms))
      (f2b-help s ms))
  :hints (("Goal" :in-theory (enable new-fn-mssgp f2b-st
                                     acl2::maximal-records-theory))))

(definec f2b (s :s-fn) :s-bn
  (f2b-help s (fn-pending-mssgs s)))

(property prop=f2b-help-mset (s :s-fn p :peer pst :ps-fn ms :lom)
  (== (f2b-help (mset p pst s) ms)
      (mset p (f2b-st pst ms) (f2b-help s ms)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))

(property prop=f2b-mset (s :s-fn p :peer pst :ps-fn)
  :h (== (fn-pending-mssgs (mset p pst s))
         (fn-pending-mssgs s))
  (== (f2b (mset p pst s))
      (mset p (f2b-st pst (fn-pending-mssgs s)) (f2b s))))
                      

;; mget traversal properties
(encapsulate ()
  (local
   (in-theory (enable acl2::maximal-records-theory)))

  (property prop=f2b-st-f2b-mget (s :s-fn p :peer ms :lom)
            :h (mget p s)
            (== (mget p (f2b-help s ms))
                (f2b-st (mget p s) ms))
            :hints (("Goal" :in-theory (enable ps-bnp))))
  
  (property prop=f2b-car (s :s-fn)
            (== (caar (f2b s))
                (caar s)))

  (property prop=f2b-cdar (s :s-fn)
    :h (consp s)
    (== (cdar (f2b s))
        (f2b-st (cdar s)
                (fn-pending-mssgs s)))))


(encapsulate ()
   (property prop=f2b-help-set-subs-sfn
     (nbrs :lop subs :lot p :peer s :s-fn ms :lom)
     (== (f2b-help (set-subs-sfn nbrs subs p s) ms)
         (f2b-help s ms))
     :instructions
     (:induct :pro :bash
              (:dv 1 1 1) :r :top :s
              :bash
              (:dv 1 1 1 1) :r :top :s
              :bash :r :s :bash
              :pro
              (:dv 1 1) :r :top :s))

  (property prop=f2b-set-subs-sfn (s :s-fn p :peer nbrs :lop subs :lot )
    (== (f2b (set-subs-sfn nbrs subs p s))
        (f2b s)))

  (local
   (in-theory (enable acl2::maximal-records-theory)))
  
  (property prop=mget-f2b-pdg-irrelevance (p :peer s :s-fn ms ns :lom)
    :h (mget p (f2b-help s ms))
    (mget p (f2b-help s ns)))

  (property prop=mget-f2b=>mget (s :s-fn p :peer)
    :h (mget p (f2b s))
    (mget p s)
    :instructions
    (:pro :induct :pro
          (:claim (mget p (cdr (f2b s))))
          (:claim (mget p (f2b-help (cdr s)
                                    (fn-pending-mssgs s))))
          (:claim (mget p (f2b-help (cdr s) (fn-pending-mssgs (cdr s)))))
          (:claim (mget p (f2b (cdr s))))
          (:claim (mget p (cdr s)))
          (:r 2) :s :pro :bash
          :pro (:claim nil) :s)))

(property prop=f2b-help-cdr (s :s-fn x :lom)
  (== (cdr (f2b-help s x))
      (f2b-help (cdr s) x)))

(property prop=mget=>mget-f2b (s :s-fn p :peer)
  :h (mget p s)
  (mget p (f2b s)))

;; Danger, Should be disabled later
(property prop=mget-f2b=mget (s :s-fn p :peer)
  (iff (mget p s)
       (mget p (f2b s))))

(property prop=not-mget=not-mget-f2b (s :s-fn p :peer)
          (== (! (mget p s))
              (! (mget p (f2b s)))))



;;===== BROADCAST-BN HYPS =========                          

(encapsulate ()
  (local
   (in-theory (enable new-fn-mssgp new-bn-mssgp)))

  (local
   (property prop=in-member (x :tl m :all)
     (iff (in m x)
          (member-equal m x))))

  (property prop=in-fn-pending=>new-bn-mssgp-help (s :s-fn m :mssg ms :lom)
    :h (in m ms)
    (new-bn-mssgp m (f2b-help s ms))
    :instructions
    (:pro  
     :induct :pro
     (:claim (consp (f2b-help s ms)))
     (:claim (new-bn-mssgp m (f2b-help (cdr s) ms)))
     :r :s
     (:dv 1 2 2 1 1) :r :s :up :up :s :top
     (:claim (member-equal m ms)) :bash
     :pro :bash))

  (property prop=in-fn-pending=>new-bn-mssgp (s :s-fn m :mssg)
    :h (in m (fn-pending-mssgs s))
    (new-bn-mssgp m (f2b s)))


  (property h10 (w :s-fn x y :lom m :mssg)
    :h (not (member-equal m x))
    (== (new-bn-mssgp m (f2b-help w (union-set x y)))
        (new-bn-mssgp m (f2b-help w y)))
    :instructions
    (:pro
     (:induct (f2b-help w y)) :pro
     (:casesplit (consp (f2b-help w (union-set x y))))
     (:dv 1) (:r 3) :s
     (= (cdr (f2b-help w (union-set x y)))
        (f2b-help (cdr w) (union-set x y)))
     (:claim (equal (new-bn-mssgp m (f2b-help (cdr w) (union-set x y)))
                    (new-bn-mssgp m (f2b-help (cdr w) y))))
     (= (new-bn-mssgp m (f2b-help (cdr w) (union-set x y)))
        (new-bn-mssgp m (f2b-help (cdr w) y)))

     (= (cdr (car (f2b-help w (union-set x y))))
        (f2b-st (cdr (car w)) (union-set x y)))
     (= (mget :seen (f2b-st (cdr (car w))(union-set x y)))
        (set-difference-equal (mget :seen (cdr (car w)))
                              (union-set x y))
        :hints (("Goal" :use ((:instance prop=f2b-st-check
                                         (ps (cdr (car w)))
                                         (ms (union-set x y)))))))
     (:claim (not (in m x)))
     (= (in m (set-difference-equal (mget :seen (cdr (car w)))
                                    (union-set x y)))
        (in m (mget :seen (cdr (car (f2b-help w y)))))
        :hints (("Goal" :use ((:instance prop=in-set-difference-union2
                                         (z (mget :seen (cdr (car w)))))))))
     :top
     (:claim (consp (f2b-help w y)))
     (:dv 2) (:r 2) :s :top :s
     :bash :bash))

  (property prop=new-bn-mssgp=>in-fn-pending (w :s-fn m :mssg)
    :h (^ (new-bn-mssgp m (f2b w))
          (! (new-fn-mssgp m w)))
    (in m (fn-pending-mssgs w))
    :instructions
    (:pro
     :induct :bash :pro
     (:claim (== (new-fn-mssgp m w)
                 (and (not (member-equal m (mget :seen (cdr (car w)))))
                      (not (member-equal m (mget :pending (cdr (car w)))))
                      (new-fn-mssgp m (cdr w))))
             :hints (("Goal" :use ((:instance new-fn-mssgp-definition-rule
                                              (s w))))))
     (:claim (or (member-equal m (mget :seen (cdr (car w))))
                 (member-equal m (mget :pending (cdr (car w))))
                 (not (new-fn-mssgp m (cdr w)))))
     
     (:casesplit (member-equal m (mget :pending (cdr (car w)))))
     (:claim (in m (mget :pending (cdr (car w)))))
     (= (fn-pending-mssgs w)
        (union-set (mget :pending (cdr (car w)))
                   (fn-pending-mssgs (cdr w)))
        :hints (("Goal" :use ((:instance fn-pending-mssgs-definition-rule
                                         (s w))))))
     (:prove :hints (("Goal" :use ((:instance in-union
                                              (x (mget :pending (cdr (car w))))
                                              (y (fn-pending-mssgs (cdr
                                                                    w))))))))

     (:casesplit (in m (mget :seen (cdr (car w)))))
     (:claim (consp (f2b w)))
     (:demote 7)
     (:dv 1) (:r 2) :s
     (= (f2b-help w (fn-pending-mssgs w))
        (f2b w))
     (= (mget :seen (cdr (car (f2b w))))
        (mget :seen (f2b-st (cdr (car w))
                            (fn-pending-mssgs w))))
     (= (mget :seen (f2b-st (cdr (car w))
                            (fn-pending-mssgs w)))
        (set-difference-equal (mget :seen (cdr (car w)))
                              (fn-pending-mssgs w)))
     :top :pro
     (:claim (member-equal m (mget :seen (cdr (car w)))))
     (:claim (member-equal m (fn-pending-mssgs w)))
     (:claim (in m (fn-pending-mssgs w)))
     :s

     (:claim (not (new-fn-mssgp m (cdr w))))
     (:claim (== (f2b (cdr w))
                 (f2b-help (cdr w) (fn-pending-mssgs (cdr w))))
             :hints (("Goal" :use ((:instance f2b-definition-rule
                                              (s w))))))
     ;(:claim (f2b-help (cdr w) (fn-pending-mssgs (cdr w))))
     (:demote 7) (:dv 1)
     (= (f2b w)
        (f2b-help w (fn-pending-mssgs w)))
     (= (fn-pending-mssgs w)
        (union-set (mget :pending (cdr (car w)))
                   (fn-pending-mssgs (cdr w)))
        :hints (("Goal" :use ((:instance fn-pending-mssgs-definition-rule
                                         (s w))))))
     :top
     (= (new-bn-mssgp m
                       (f2b-help w
                                 (union-set (mget :pending (cdr (car w)))
                                            (fn-pending-mssgs (cdr w)))))
        (new-bn-mssgp m (f2b-help w (fn-pending-mssgs (cdr w))))
        :hints (("Goal" :use ((:instance h10
                                         (x (mget :pending (cdr (car w))))
                                         (y (fn-pending-mssgs (cdr w))))))))
     (:dv 1) (:r 3) :s :top :pro
     (:claim (in m (fn-pending-mssgs (cdr w))))
     (:claim (in m (union-set (fn-pending-mssgs (cdr w))
                              (mget :pending (cdr (car w)))))
             :hints (("Goal" :in-theory (disable prop=in-member in-union)
                      :use ((:instance in-union
                                       (x (fn-pending-mssgs (cdr w)))
                                       (y (mget :pending (cdr (car w)))))))))
     (= (fn-pending-mssgs w)
        (union-set (mget :pending (cdr (car w)))
                   (fn-pending-mssgs (cdr w)))
        :hints (("Goal" :use ((:instance fn-pending-mssgs-definition-rule
                                         (s w))))))
     (= (union-set (mget :pending (cdr (car w)))
                   (fn-pending-mssgs (cdr w)))
        (union-set (fn-pending-mssgs (cdr w))
                   (mget :pending (cdr (car w))))
        :hints (("Goal" :use ((:instance union-set-symm
                                         (x (mget :pending (cdr (car w))))
                                         (y (fn-pending-mssgs (cdr w))))))))
     :s
     :bash))
    
  
  (property prop=new-mssg-fn-pending-mssgs (s :s-fn m :mssg)
    :h (new-fn-mssgp m s)
    (! (in m (fn-pending-mssgs s)))
    :instructions
    (:pro
     :induct :bash :pro
     (:claim (not (in m (mget :pending (cdr (car s))))))
     (:claim (not (in m (fn-pending-mssgs (cdr s)))))
     (:claim (not (in m (union-set (mget :pending (cdr (car s)))
                                   (fn-pending-mssgs (cdr s)))))
             :hints (("Goal" :use ((:instance not-in-union
                                              (x (mget :pending (cdr (car s))))
                                              (y (fn-pending-mssgs (cdr s))))))))
     
     (:dv 1 2) (:r 2) :s :top :s
     :pro :bash))


  (property prop=f2b-broadcast-help (s :s-fn m :mssg)
    :h (new-fn-mssgp m s)
    (new-bn-mssgp m (f2b s))
    :instructions
    (:pro
     :induct :bash
     :pro
     (:claim (== (new-fn-mssgp m s) (^ (== nil (member-equal m (mget :seen (cdar s))))
                                       (== nil (member-equal m (mget :pending (cdar s))))
                                       (new-fn-mssgp m (cdr s)))))
     :s
     :pro
     (:claim (new-bn-mssgp m (f2b (cdr s))))
     (:r 2)
     (:claim (consp (f2b-help s (fn-pending-mssgs s))))
     (:claim (! (member-equal m (mget :seen (cdr (car s))))))
     (:claim (! (member-equal m (mget :seen
                                      (cdar (f2b-help s (fn-pending-mssgs s)))))))
     :s
     (:claim (! (member-equal m (mget :seen (f2b-st (cdr (car s))
                                                    (fn-pending-mssgs s))))))
     (:claim (! (member-equal m (mget :seen (cdr (car (f2b s)))))))
     (:claim (not (in m
                      (mget :seen (cdr (car (f2b-help s (fn-pending-mssgs s))))))))


     (:claim (new-bn-mssgp m (f2b-help (cdr s) (fn-pending-mssgs (cdr s)))))
     (:claim (new-bn-mssgp m (f2b-help (cdr s)
                                       (union-set (mget :pending (cdr (car
                                                                       s)))
                                                  (fn-pending-mssgs (cdr s))))))
     (:claim (== (fn-pending-mssgs s)
                 (union-set (mget :pending (cdr (car s)))
                            (fn-pending-mssgs (cdr s))))
             :hints (("Goal" :use ((:instance fn-pending-mssgs-definition-rule)))))

     (:claim (new-bn-mssgp m (f2b-help (cdr s) (fn-pending-mssgs s))))
     :s :pro :bash)))

(property prop=f2b-broadcast-hyps (s :s-fn m :mssg)
  :h (^ (mget (mget :or m) s)
        (in (mget :tp m)
            (mget :pubs (mget (mget :or m) s))))
  (^ (mget (mget :or m) (f2b s))
     (in (mget :tp m)
         (mget :pubs (mget (mget :or m) (f2b s)))))
  :instructions
  (:pro
   (:claim (mget (mget :or m) (f2b s)))
   :bash))
           

(propertyd prop=f2b-produce-hyps (s :s-fn m :mssg)
  :h (^ (mget (mget :or m) (f2b s))
        (in (mget :tp m)
            (mget :pubs (mget (mget :or m) (f2b s)))))
  (^ (mget (mget :or m) s)
     (in (mget :tp m)
         (mget :pubs (mget (mget :or m) s)))))


;;===== PRODUCE - F2B =========                          

(property prop=f2b-produce-fn (s :s-fn m :mssg)
  :check-contracts? nil
  :h (^ (mget (mget :or m) s)
        (new-fn-mssgp m s)
        (in (mget :tp m)
            (mget :pubs (mget (mget :or m) s))))
  (== (f2b (produce-fn m s))
      (f2b s))
  :instructions
  (:pro
   (:dv 1 1)
   (:r 2) :s :up (:r 2) :s
   (:claim (! (v (member-equal m (mget :pending (mget (mget :or m) s)))
                 (member-equal m (mget :seen (mget (mget :or m) s)))))
           :hints (("Goal" :use ((:instance new-mssg=>not-seen-peer
                                            (p (mget :or m)))))))                  

   (:claim (== (add-pending-psfn m (mget (mget :or m) s))
               (mset :pending
                     (cons m (mget :pending (mget (mget :or m) s)))
                     (mget (mget :or m) s)))
           :hints (("Goal" :in-theory (enable add-pending-psfn))))
   
   (= (add-pending-psfn m (mget (mget :or m) s))
      (mset :pending
            (cons m (mget :pending (mget (mget :or m) s)))
            (mget (mget :or m) s)))
      
   
   (:claim (== (fn-pending-mssgs
                (mset (mget :or m)
                      (mset :pending
                            (cons m (mget :pending (mget (mget :or m) s)))
                            (mget (mget :or m) s))
                      s))
               (insert-unique m (fn-pending-mssgs s)))
           :hints (("Goal" :use ((:instance prop=fn-pending-mssgs-mset-pending
                                            (p (mget :or m)))))))
   
   (= (fn-pending-mssgs
       (mset (mget :or m)
             (mset :pending
                   (cons m (mget :pending (mget (mget :or m) s)))
                   (mget (mget :or m) s))
             s))
      (insert-unique m (fn-pending-mssgs s)))

   (:claim (== (f2b-st (mget (mget :or m) s)
                       (insert-unique m (fn-pending-mssgs s)))
               (mget (mget :or m) (f2b-help s (insert-unique m (fn-pending-mssgs s)))))
           :hints (("Goal" :use ((:instance prop=f2b-st-f2b-mget
                                            (p (mget :or m))
                                            (ms (insert-unique m
                                                               (fn-pending-mssgs s))))))))
   (= (f2b-st (mget (mget :or m) s)
              (insert-unique m (fn-pending-mssgs s)))
      (mget (mget :or m) (f2b-help s (insert-unique m (fn-pending-mssgs
                                                       s)))))

   :r :top :bash :bash))

;;---- SUBSCRIBE ------

(property prop=f2b-st-mset-subs (pst :ps-fn subs :lot ms :lom)
  (== (f2b-st (mset :subs subs pst) ms)
      (mset :subs subs (f2b-st pst ms)))
  :hints (("Goal" :in-theory (enable f2b-st))))

(property prop=f2b-subscribe-fn (s :s-fn p :peer topics :lot)
          :h (mget p s)
          (== (f2b (subscribe-fn p topics s))
              (subscribe-bn p topics (f2b s)))
          :instructions
          (:pro (:dv 1 1)
                (:rewrite subscribe-fn) :s :up
                (:rewrite prop=f2b-set-subs-sfn)
                (:rewrite prop=f2b-mset)
                (:dv 2) (:rewrite prop=f2b-st-mset-subs)
                (= (mget :subs (mget p s))
                   (mget :subs (mget p (f2b s))))
                :s
                :top (:dv 2)
                (:rewrite subscribe-bn) :s :top :s
                (:repeat :bash)))

;;---- UNSUBSCRIBE ------

(property prop=f2b-unsubscribe-fn (s :s-fn p :peer topics :lot)
          :h (mget p s)
          (== (f2b (unsubscribe-fn p topics s))
              (unsubscribe-bn p topics (f2b s)))
          :instructions
          (:pro (:dv 1 1)
                (:rewrite unsubscribe-fn) :s :up
                (:rewrite prop=f2b-set-subs-sfn)
                (:rewrite prop=f2b-mset)
                (:dv 2) (:rewrite prop=f2b-st-mset-subs)
                (= (mget :subs (mget p s))
                   (mget :subs (mget p (f2b s))))
                :s
                :top (:dv 2)
                (:rewrite unsubscribe-bn) :s :top :s
                (:repeat :bash)))

;;---- JOIN ------

(property prop=f2b-join-pending-mssgs (p :peer pubs subs :lot nbrs :lop s :s-fn)
  :h (^ (! (mget p s))
        (! (in p nbrs)))
  (== (fn-pending-mssgs (join-fn p pubs subs nbrs s))
      (fn-pending-mssgs s))
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
   (:dv 1)
   (:rewrite prop=pending-mssgs-set-topics-subscribe)
   (:rewrite prop=fn-pending-mssgs-mset-pending-new)
   :top :s :bash :bash))


(property prop=f2b-join-mset (p :peer pubs subs :lot nbrs :lop s :s-fn)
  :h (^ (! (mget p s))
        (! (in p nbrs)))
  (== (f2b (join-fn p pubs subs nbrs s))
      (mset p
            (f2b-st (new-joinee-st-fn pubs subs nbrs s)
                    (fn-pending-mssgs s))
            (f2b s)))
  :instructions
  (:pro
   (= (f2b (join-fn p pubs subs nbrs s))
      (f2b-help (join-fn p pubs subs nbrs s)
                (fn-pending-mssgs (join-fn p pubs subs nbrs s))))
   (= (fn-pending-mssgs (join-fn p pubs subs nbrs s))
      (fn-pending-mssgs s)
      :hints (("Goal" :use ((:instance prop=f2b-join-pending-mssgs)))))
   
   (= (join-fn p pubs subs nbrs s)
      (set-subs-sfn nbrs
                subs
                p
                (mset p
                      (new-joinee-st-fn pubs subs nbrs s)
                      s))
      :hints (("Goal" :in-theory (enable join-fn))))
   (:dv 1) (:rewrite prop=f2b-help-set-subs-sfn)
   (:rewrite prop=f2b-help-mset) :top
   :prove :bash))

(property prop=f2b-new-joinee-st-fn (pubs subs :lot nbrs :lop s :s-fn)
  (== (f2b-st (new-joinee-st-fn pubs subs nbrs s)
              (fn-pending-mssgs s))
      (ps-bn pubs subs '()))
  :instructions
  (:pro
   (:claim (ps-fnp (new-joinee-st-fn pubs subs nbrs s)))
   (:prove :hints (("Goal" :in-theory (enable f2b-st
                                              new-joinee-st-fn)
                    :use ((:instance prop=f2b-st-check
                                     (ps (new-joinee-st-fn
                                          pubs subs nbrs s))
                                     (ms (fn-pending-mssgs s)))))))))
  
(property prop=f2b-join-fn (p :peer pubs subs :lot nbrs :lop s :s-fn)
  :h (^ (! (mget p s))
        (! (in p nbrs)))
  (== (f2b (join-fn p pubs subs nbrs s))
      (join-bn p pubs subs (f2b s)))
  :instructions
  (:pro
   (= (f2b (join-fn p pubs subs nbrs s))
      (mset p
            (f2b-st (new-joinee-st-fn pubs subs nbrs s)
                    (fn-pending-mssgs s))
            (f2b s))
      :hints (("Goal" :use ((:instance prop=f2b-join-mset)))))
   (:claim (! (mget p (f2b s))))
   (:claim (ps-fnp (new-joinee-st-fn pubs subs nbrs s)))
   (= (f2b-st (new-joinee-st-fn pubs subs nbrs s)
              (fn-pending-mssgs s))
      (ps-bn pubs subs '())
      :hints (("Goal" :use ((:instance prop=f2b-new-joinee-st-fn)))))
   (:prove :hints (("Goal" :in-theory (enable join-bn))))))

;;---- LEAVE ------

(property prop=leave-cdr (s :s-fn p :peer)
  :check-contracts? nil
  :h (^ (mget p (cdr s))
        (!= p (car (car s))))
  (== (cdr (leave-fn p s))
      (leave-fn p (cdr s)))
  :hints (("Goal" :in-theory (enable leave-fn
                                     acl2::maximal-records-theory))))

(encapsulate ()
  (local
   (in-theory (enable acl2::maximal-records-theory
                      leave-fn
                      leave-bn)))
  (local
   (in-theory (disable prop=mget-f2b=mget)))

  (property prop=f2b-leave-fn-help (s :s-fn p :peer ms :lom)
    :h (mget p s)
    (== (f2b-help (leave-fn p s) ms)
        (leave-bn p (f2b-help s ms)))
  
    :instructions
    (:pro (:induct (f2b-help s ms))
        :pro
        (:casesplit (!= (car (car s)) p))
        (:claim (mget p (cdr s)))
        (:claim (== (f2b-help (leave-fn p (cdr s)) ms)
                    (leave-bn p (f2b-help (cdr s) ms))))


        (= (leave-bn p (f2b-help s ms))
           (cons (cons (caar s) (f2b-st (cdar s) ms))
                 (leave-bn p (f2b-help (cdr s) ms))))
        (= (leave-bn p (f2b-help (cdr s) ms))
           (f2b-help (leave-fn p (cdr s)) ms))
        (= (leave-fn p (cdr s))
           (cdr (leave-fn p s)))
        (= (car (car s))
           (car (car (leave-fn p s))))
        (= (cdr (car s))
           (cdr (car (leave-fn p s))))
        (:claim (consp (leave-fn p s)))
        (:dv 1) (:r 2) :s :top
        :s


        (= (leave-fn p s)
           (cdr s))
        (= (f2b-help s ms)
           (cons (cons (caar s) (f2b-st (cdar s) ms))
                 (f2b-help (cdr s) ms)))
        (= (leave-bn p
                 (cons (cons (car (car s))
                             (f2b-st (cdr (car s)) ms))
                       (f2b-help (cdr s) ms)))
           (f2b-help (cdr s) ms))
           

        :bash
        ))

(property prop=f2b-leave-fn (s :s-fn p :peer)
  :h (^ (mget p s)
        ;; Condition 1 : Full Propagation (no pending messages lost)
        (== (fn-pending-mssgs (leave-fn p s))
            (fn-pending-mssgs s)))
  (== (f2b (leave-fn p s))
      (leave-bn p (f2b s)))
  :instructions
  (:pro
   (:dv 1) :r
   (:equiv (fn-pending-mssgs (leave-fn p s))
           (fn-pending-mssgs s))
   :top
   (:dv 2 2) :r :top
   (:claim (== (f2b-help (leave-fn p s) (fn-pending-mssgs s))
               (leave-bn p (f2b-help s (fn-pending-mssgs s))))
               :hints (("Goal" :use ((:instance prop=f2b-leave-fn-help
                                                (ms (fn-pending-mssgs s)))))))
   :s))
)

(property prop=f2b-join-bn (w :s-fn p :peer pubs subs :lot nbrs :lop)
  :h (^ (! (mget p (f2b w)))
        (! (in p nbrs)))
  (== (f2b (join-fn p pubs subs nbrs w))
      (join-bn p pubs subs (f2b w)))
  :hints (("Goal" :use ((:instance prop=f2b-join-fn
                                   (s w))))))

(propertyd prop=f2b-leave-bn (w :s-fn p :peer)
  :check-contracts? nil
  :h  (^ (mget p (f2b w))
         ;; Condition 1 : Full Propagation
         (== (fn-pending-mssgs (leave-fn p w))
             (fn-pending-mssgs w)))
  (== (leave-bn p (f2b w))
      (f2b (leave-fn p w)))
  :instructions
  (:pro
   (:claim (mget p w))
   (:prove :hints (("Goal" :use ((:instance
                                  prop=f2b-leave-fn (s w))))))))


(property prop=f2b-forward-fn-help (p :peer s :s-fn nbrs :lop m :mssg ms :lom)
  (== (f2b-help (forward-help-fn s nbrs m) ms)
      (f2b-help s ms))
  :instructions
  (:pro
   (:induct (forward-help-fn s nbrs m)) :bash
   :pro
   (:claim (== (f2b-help (forward-help-fn (cdr s) nbrs m)
                         ms)
               (f2b-help (cdr s) ms)))
   
   (:casesplit (in (car (car s)) nbrs))
   

   (:dv 1 1) :r :s :up :r :s (:dv 1 2) :r :top
   :bash :bash
   (:claim (== (forward-help-fn s nbrs m)
               (cons (cons (car (car s))
                           (add-pending-psfn m (cdr (car s))))
                     (forward-help-fn (cdr s) nbrs m)))
           :hints (("Goal" :in-theory (enable forward-help-fn))))
   (= (cons (cons (car (car s))
                           (add-pending-psfn m (cdr (car s))))
            (forward-help-fn (cdr s) nbrs m))
      (forward-help-fn s nbrs m))
   :bash
   
   
   (:dv 1 1) :r :s :up :r :s :top :bash
   (:claim (== (forward-help-fn s nbrs m)
               (cons (car s)
                     (forward-help-fn (cdr s) nbrs m)))
           :hints (("Goal" :in-theory (enable forward-help-fn))))
   (= (cons (car s)
            (forward-help-fn (cdr s) nbrs m))
      (forward-help-fn s nbrs m))
   :bash
   :pro
   (:dv 1 1) :r :s :up :r :s :top :bash :r))



(property prop=f2b-update-forwarder-fn (p :peer m :mssg s :s-fn ms :lom)
  :h (in m ms)
  (== (f2b-help (update-forwarder-fn p m s) ms)
      (f2b-help s ms))
  :instructions
  (:pro
   (:induct (update-forwarder-fn p m s)) :bash :pro
   (:claim (equal (f2b-help (update-forwarder-fn p m (cdr s))
                             ms)
                  (f2b-help (cdr s) ms)))
   
   (:casesplit (== (car (car s)) p))

   (:dv 1 1) (:r 2) :s :up :r :s (:dv 1 2) :r :top
   :bash :bash :bash
   (:claim (== (update-forwarder-fn p m s)
               (cons (car s)
                     (update-forwarder-fn p m (cdr s))))
           :hints (("Goal" :in-theory (enable update-forwarder-fn))))
   (= (update-forwarder-fn p m s)
      (cons (car s)
            (update-forwarder-fn p m (cdr s))))
   :bash
   (:dv 1) :r :s :top :s
   (= (cons (car s)
            (update-forwarder-fn p m (cdr s)))
      (update-forwarder-fn p m s))
   :s :pro
   (= (update-forwarder-fn p m s)
      (cons (cons p (forwarder-new-pst (cdr (car s)) m))
            (cdr s)))
   (:dv 1) :r :s
   (= (f2b-st (forwarder-new-pst (cdr (car s)) m) ms)
      (f2b-st (cdr (car s)) ms))
   :top
   (=  (cons (cons p (f2b-st (cdr (car s)) ms))
             (f2b-help (cdr s) ms))
       (f2b-help s ms))
   (= (cons (cons p (forwarder-new-pst (cdr (car s)) m))
            (cdr s))
      (update-forwarder-fn p m s))
   :s :bash))


(property prop=in-pending-p=>new-bn-mssgp (s :s-fn p :peer m :mssg)
  :h (^ (mget p s)
        (in m (mget :pending (mget p s))))
  (new-bn-mssgp m (f2b s))
  :instructions
  (:pro 
   (:claim (in m (fn-pending-mssgs s))
           :hints (("Goal" :use ((:instance prop=in-p-fn-pending)))))
   :bash)
  :rule-classes :forward-chaining)

(property prop=forward-fn (p :peer m :mssg s :s-fn)
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (! (in m (mget :seen (mget p s))))
        ;; (B s u)
        (== (fn-pending-mssgs (forward-fn p m s))
            (fn-pending-mssgs s)))
  (== (f2b (forward-fn p m s))
      (f2b s))
  :hints (("Goal" :in-theory (enable forward-fn f2b))))


;; (in-theory (enable f2b f2b-definition-rule forward-fn forward-fn-definition-rule
;;                    f2b-help f2b-help-definition-rule prop=mget-f2b=mget
;;                    fn-pending-mssgs fn-pending-mssgs-definition-rule))

;; (property prop=forward-broadcast (p :peer m :mssg s :s-fn ms :lom)
;;   :h (^ (mget p s)
;;         (in m (mget :pending (mget p s)))
;;         (! (in m (mget :seen (mget p s))))
;;         (! (in m ms))

;;         (=> (^ (! (new-fn-mssgp m s))
;;                (! (in m (fn-pending-mssgs s))))
;;             (== (f2b s)
;;                 (broadcast m (f2b s))))
;;         )
  
  
;;   (equal (f2b-help (update-forwarder-fn p m s) ms)
;;          (broadcast m (f2b s))))

;; TODO
;; Prove

;; (equal (f2b-help (update-forwarder-fn p m s)
;;                  (remove-equal m (fn-pending-mssgs s)))
;;        (broadcast m (f2b s)))


;; (property prop=forward-fn2 (p :peer m :mssg s :s-fn)
;;   :check-contracts? nil
;;   :h (^ (mget p s)
;;         (in m (mget :pending (mget p s)))
;;         (! (in m (mget :seen (mget p s))))
;;         (== (fn-pending-mssgs (forward-fn p m s))
;;             (remove-equal m (fn-pending-mssgs s)))
        
;;         (mget (mget :or m) s)
;;         (in (mget :tp m)
;;             (mget :pubs (mget  (mget :or m) s)))

;;         ;;Condition
;;         (=> (^ (! (in m (fn-pending-mssgs (forward-fn p m s))))
;;                (! (new-fn-mssgp m (forward-fn p m s))))
;;             (broadcastedp m (forward-fn p m s)))


;;         )
;;   (== (f2b (forward-fn p m s))
;;       (broadcast m (f2b s)))
;;   :instructions
;;   (:pro
;;    (= (f2b (forward-fn p m s))
;;       (f2b-help (forward-fn p m s)
;;                 (fn-pending-mssgs (forward-fn p m s))))
;;    (= (fn-pending-mssgs (forward-fn p m s))
;;       (remove-equal m (fn-pending-mssgs s)))
;;    (= (forward-fn p m s)
;;       (forward-help-fn (update-forwarder-fn p m s)
;;                        (mget (mget :tp m)
;;                              (mget :nsubs (mget p s)))
;;                        m))
;;    (= (f2b-help (forward-help-fn (update-forwarder-fn p m s)
;;                                  (mget (mget :tp m)
;;                                        (mget :nsubs (mget p s)))
;;                                  m)
;;                 (remove-equal m (fn-pending-mssgs s)))
;;       (f2b-help (update-forwarder-fn p m s)
;;                 (remove-equal m (fn-pending-mssgs s))))

;;    (:claim (in m (fn-pending-mssgs s)))
;;    (:claim (new-bn-mssgp m (f2b s)))

;;    (:claim (! (in m (remove-equal m (fn-pending-mssgs s))))
;;            :hints (("Goal" :use ((:instance not-in-rem
;;                                             (x (fn-pending-mssgs s)))))))
   
;;    (:claim (! (in m (fn-pending-mssgs (forward-fn p m s)))))

;;    (:claim (^ (mget (mget :or m) (f2b s))
;;               (in (mget :tp m)
;;                   (mget :pubs (mget (mget :or m) (f2b s))))))

;;    (:claim (in m (mget :seen (mget p (update-forwarder-fn p m s)))))

;;    (:claim (! (new-fn-mssgp m (update-forwarder-fn p m s))))
   
   

   
;;    ))
  






(in-theory (disable prop=mget-f2b=mget f2b f2b-definition-rule
                    f2b-help f2b-help-definition-rule
                    fn-pending-mssgs fn-pending-mssgs-definition-rule))


;;------------------ RANK FUNCTION AND RELATED PROPERTIES -----------------------------

(definec m-nct (m :mssg s :s-fn) :nat
  (match s
    (() 0)
    (((& . pst) . rst)
     (+ (if (! (in m (mget :seen pst)))
            1
          0)
        (m-nct m rst)))))

(property prop=m-nct-upper-bound (m :mssg s :s-fn)
  (<= (m-nct m s)
      (len s)))

(definec rankl (m :mssg s :s-fn) :nat
  (if (new-fn-mssgp m s)
      (1+ (len s))
    (m-nct m s)))

(property prop=f2b-update-forwarder-rank (p :peer m :mssg s :s-fn ms :lom)
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (! (in m (mget :seen (mget p s)))))
    (< (m-nct m (update-forwarder-fn p m s))
       (m-nct m s))
  :instructions
  (:pro
   (:induct (tlp s)) :bash :pro
   
   (:casesplit (== (car (car s)) p))
   (:dv 1 2) (:r 2) :s :up :r :s
   (= (forwarder-new-pst (cdr (car s)) m)
      (mset :pending
            (remove-equal m (mget :pending (cdr (car s))))
            (mset :seen
                  (insert-unique m (mget :seen (cdr (car s))))
                  (cdr (car s))))
      :hints (("Goal" :in-theory (enable forwarder-new-pst))))
   (:claim (in m (mget :seen (forwarder-new-pst (cdr (car s)) m)))
           :hints (("Goal" :in-theory (enable forwarder-new-pst))))
   (:claim (in m (insert-unique m (mget :seen (cdr (car s))))))
   :s :up
   (= (m-nct m s)
      (+ 1 (m-nct m (cdr s))))
   :s :bash
   (= (cons (cons p (forwarder-new-pst (cdr (car s)) m))
            (cdr s))
      (update-forwarder-fn p m s))
   :bash

   (:claim (mget p (cdr s))
           :hints (("Goal" :use ((:instance prop=mget-cdr)))))
   (:claim (== (mget p s) (mget p (cdr s)))
           :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))
   (:claim (! (in m (mget :seen (mget p (cdr s))))))
   (:claim (< (m-nct m (update-forwarder-fn p m (cdr s)))
              (m-nct m (cdr s))))


   (:dv 1 2) (:r 2) :s :top
   (= (m-nct m s)
      (m-nct m (cons (car s) (cdr s))))
   (:dv 1) :r :s :up (:dv 2) :r :s :up
   (:casesplit (in m (mget :seen (cdr (car s)))))
   :s :s :bash :bash
   (= (cons (car s)
            (update-forwarder-fn p m (cdr s)))
      (update-forwarder-fn p m s))
   :bash))

(property prop=forward-help-fn-rank (p :peer s :s-fn m :mssg nbrs :lop)
  (= (m-nct m (forward-help-fn s nbrs m))
     (m-nct m s))
  :instructions
  (:pro
   :induct :bash :pro

   
   (:dv 1 2) (:r 2) :s :up
   :r :s
   (= (m-nct m (forward-help-fn (cdr s) nbrs m))
      (m-nct m (cdr s)))
   

   :top
   (= (mget :seen (add-pending-psfn m (cdr (car s))))
      (mget :seen (cdr (car s))))
   (:casesplit (in (car (car s)) nbrs))
   :s :bash :bash
   (= (if (in (car (car s)) nbrs)
           (cons (cons (car (car s))
                       (add-pending-psfn m (cdr (car s))))
                 (forward-help-fn (cdr s) nbrs m))
         (cons (car s)
               (forward-help-fn (cdr s) nbrs m)))
      (forward-help-fn s nbrs m)
      :hints (("Goal" :in-theory (enable forward-help-fn))))
   :s

   :pro
   (= (forward-help-fn s nbrs m)
      nil
      :hints (("Goal" :in-theory (enable forward-help-fn))))
   :s))

(encapsulate ()
  
  (local
   (property prop=m-nct-notin-car (m :mssg s :s-fn)
     :h (^ s
           (not (in m (mget :seen (cdr (car s))))))
     (< (m-nct m (cdr s))
        (m-nct m s))))

  (local
   (property prop=m-nct-cdr-in-car (m :mssg s :s-fn)
     :h (^ s
           (in m (mget :seen (cdr (car s)))))
     (= (m-nct m (cdr s))
        (m-nct m s))))

  (local
   (in-theory (enable acl2::maximal-records-theory)))

  (property prop=m-nct-mset-add-pending (p :peer s :s-fn m :mssg)
    :h (^ (mget p s)
          (! (in m (mget :seen (mget p s)))))
    (= (m-nct m (mset p (add-pending-psfn m (mget p s)) s))
       (m-nct m s))
    :instructions
    (:pro
     :induct :bash
     :pro
     (:casesplit (== p (car (car s))))
     (= (mget p s) (cdr (car s)))
     (:dv 1 2) :r
     (:claim (consp (add-pending-psfn m (cdr (car s)))))
     :s :up
     (:claim (! (in m (mget :seen (add-pending-psfn m (cdr (car s)))))))
     :r
     (:claim (consp (cons (cons p (add-pending-psfn m (cdr (car s))))
                          (cdr s))))
     (:claim (consp (car (cons (cons p (add-pending-psfn m (cdr (car s))))
                               (cdr s)))))
     :s :top :bash :bash

     (:claim (mget p (cdr s)))
     (:claim (! (in m (mget :seen (mget p (cdr s))))))
     (:claim (= (m-nct m
                       (mset p (add-pending-psfn m (mget p (cdr s)))
                             (cdr s)))
                (m-nct m (cdr s))))
     (:dv 1 2) :r (:claim s)
     (:claim (! (lexorder p (car (car s))))) :s :up :r :s
     (:casesplit (in m (mget :seen (cdr (car s))))) :s
     :top
     (= (m-nct m s) (m-nct m (cdr s))) :s
     (= (m-nct m s) (m-nct m (cdr s))) :s
     
     (= (mget p s) (mget p (cdr s)))
     (= (m-nct m s) (m-nct m (cdr s))) :s
     :top :s :bash :bash :pro :bash))
  
  (local 
   (property prop=in-member (x :tl m :all)
     (iff (in m x)
          (member-equal m x))))

  (local
   (in-theory (enable new-fn-mssgp)))

  (property prop=new-fn-mssgp1 (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s))))
    (! (new-fn-mssgp m s)))
  
  (property prop=new-fn-mssgp2 (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :seen (mget p s))))
    (! (new-fn-mssgp m s)))

  (property prop=new-fn-mssgp-produce-fn (p :peer m :mssg s :s-fn)
    :h (^ (mget (mget :or m) s)
          (new-fn-mssgp m s)
          (in (mget :tp m)
              (mget :pubs (mget  (mget :or m) s))))
    (! (new-fn-mssgp m (produce-fn m s)))
    :instructions
    (:pro
     (:dv 1 2) (:r 2) :s :top
     (:claim (! (in m (mget :pending (mget (mget :or m) s)))))
     (:claim (! (in m (mget :seen (mget (mget :or m) s)))))
     (:claim (! (member-equal m (mget :pending (mget (mget :or m) s)))))
     (:claim (! (member-equal m (mget :seen (mget (mget :or m) s)))))
     (:claim (in m (mget :pending (add-pending-psfn m (mget (mget :or m) s))))
             :hints (("Goal" :use ((:instance prop=add-pending-psfn-pending
                                      (pst (mget (mget :or m) s)))))))
     :bash))

 (local
  (property prop=forwarder-new-pst-m (p :peer m :mssg s :s-fn)
    :h (mget p s)
    (in m (mget :seen (forwarder-new-pst (mget p s) m)))
    :instructions
    (:pro (:dv 2 2) :r :up :s :up (:r 4))))

 (property prop=forward-fn-peer-state (p :peer m :mssg s :s-fn)
   :h (^ (mget p s)
         (in m (mget :pending (mget p s)))
         (not (in m (mget :seen (mget p s))))
         (not (in p (mget (mget :tp m)
                          (mget :nsubs (mget p s))))))
   (== (mget p (forward-fn p m s))
       (forwarder-new-pst (mget p s) m))
   :hints (("Goal" :in-theory (enable forward-fn
                                      forward-help-fn))))

  (property prop=new-fn-mssgp-forward-fn (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s)))
          (not (in m (mget :seen (mget p s))))
          (not (in p (mget (mget :tp m)
                           (mget :nsubs (mget p s))))))
    (! (new-fn-mssgp m (forward-fn p m s)))
    :instructions
    (:pro
     (:claim (== (mget p (forward-fn p m s))
                 (forwarder-new-pst (mget p s) m))
             :hints (("Goal" :use (prop=forward-fn-peer-state))))
     (:claim (in m (mget :seen (forwarder-new-pst (mget p s) m)))
             :hints (("Goal" :use (prop=forwarder-new-pst-m))))
     (:prove :hints (("Goal" :use ((:instance prop=new-fn-mssgp2
                                              (s (forward-fn p m s)))))))))


  (property prop=forward-fn-rank (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s)))
          (! (in m (mget :seen (mget p s))))
          (not (in p (mget (mget :tp m)
                           (mget :nsubs (mget p s))))))
    (< (rankl m (forward-fn p m s))
       (rankl m s))
    :instructions
    (:pro
     (:claim (! (new-fn-mssgp m (forward-fn p m s)))
             :hints (("Goal" :use prop=new-fn-mssgp-forward-fn)))
     :bash
     (:dv 1 2) (:r 2) :s :top
     (= (m-nct m (forward-help-fn (update-forwarder-fn p m s)
                                  (mget (mget :tp m)
                                        (mget :nsubs (mget p s)))
                                  m))
        (m-nct m (update-forwarder-fn p m s))
        :hints (("Goal" :use ((:instance prop=forward-help-fn-rank
                                         (s (update-forwarder-fn p m s))
                                         (nbrs (mget (mget :tp m)
                                                     (mget :nsubs (mget p
                                                                        s)))))))))
     (:prove :hints (("Goal" :use (prop=f2b-update-forwarder-rank)))))))
              

(property prop=produce-fn-rank (m :mssg s :s-fn)
  :h (^ (mget (mget :or m) s)
        (new-fn-mssgp m s)
        (in (mget :tp m)
            (mget :pubs (mget  (mget :or m) s))))
  (< (rankl m (produce-fn m s))
     (rankl m s))
  :instructions
  (:pro
   (:dv 1) (:r 2) :s (:dv 2) (:r 2) :s :up
   (:claim (! (in m (mget :seen (mget (mget :or m) s)))))
   :r :top
   (:claim (<= (m-nct m s) (len s)))
   (:dv 2) :r :s :up :bash))


(in-theory (disable f2b f2b-definition-rule forward-fn forward-fn-definition-rule
                    f2b-help f2b-help-definition-rule
                    fn-pending-mssgs fn-pending-mssgs-definition-rule))

(defdata maybe-mssg (v nil mssg))

(property prop=cadr-sbn (s :s-bn)
  :h (consp s)
  (ps-bnp (cdar s))
  :hints (("Goal" :in-theory (enable s-bnp))))

(property prop=lomp-seen-diff-bn (pst qst :ps-bn)
  :check-contracts? nil
  :h (set-difference-equal (mget :seen qst) (mget :seen pst))
  (mssgp (car (set-difference-equal (mget :seen qst) (mget :seen pst))))
  :hints (("Goal" :in-theory (enable ps-bnp))))

(definec br-mssg-witness (s u :s-bn) :maybe-mssg
  :function-contract-hints (("Goal" :in-theory (enable s-bnp ps-bnp)))
  (cond
   ((v (endp s) (endp u)) nil)
   ((== (car s) (car u)) (br-mssg-witness (cdr s) (cdr u)))
   (t (car (set-difference-equal (mget :seen (cdar u))
                                 (mget :seen (cdar s)))))))
