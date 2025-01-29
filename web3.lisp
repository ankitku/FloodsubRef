(in-package "ACL2S")
(include-book "f2b-ref2")




(property prop=cadr-sbn (s :s-bn)
  :h (consp s)
  (ps-bnp (cdar s))
  :hints (("Goal" :in-theory (enable s-bnp
                                     acl2::maximal-records-theory))))

(defdata s-bn-change (list symbol
                           peer
                           (v mssg
                              lot
                              ps-bn)))
      
(in-theory (enable s-bnp ps-bnp s-bn-changep))

(property prop=lomp-seen-diff-bn (pst qst :ps-bn)
  :check-contracts? nil
  :h (consp
      (set-difference-equal (mget :seen qst)
                            (mget :seen pst)))
  (mssgp (car
          (set-difference-equal (mget :seen qst)
                                (mget :seen pst))))
  :hints (("Goal" :in-theory (enable ps-bnp))))


(definecd state-diff-psbn (p :peer pst qst :ps-bn) :s-bn-change
  (let ((p-seen (mget :seen pst))
        (q-seen (mget :seen qst))
        (p-subs (mget :subs pst))
        (q-subs (mget :subs qst)))
    (cond ((consp
            (set-difference-equal q-seen p-seen))
           (let ((m (car (set-difference-equal q-seen p-seen))))
             `(broadcast
               ,(mget :or m)
               ,m)))
          ((consp
            (set-difference-equal q-subs p-subs))
           `(subscribe-bn
             ,p
             ,(set-difference-equal q-subs p-subs)))
          ((consp
            (set-difference-equal p-subs q-subs))
           `(unsubscribe-bn
             ,p
             ,(set-difference-equal p-subs q-subs)))
          (t `(unknown-trx
               ,p
               ())))))

(in-theory (disable ps-bnp))

(definec diff-sbn (s u :s-bn) :s-bn-change
  :ic (!= s u)
  (match (list s u)
    ((() ((q . qst) . &)) `(join-bn ,q ,qst))
    ((((p . pst) . &) ()) `(leave-bn ,p ,pst))
    ((((p . pst) . rs1)
      ((q . qst) . rs2))
     (cond
      ((== `(,p . ,pst)
           `(,q . ,qst))
       (diff-sbn rs1 rs2))
      
      ((< (len s) (len u))
       `(join-bn ,q ,qst))

      ((> (len s) (len u))
       `(leave-bn ,p ,pst))

      ;; If lengths are same, then p and q are same, their pubs are
      ;; same, and only the rest of the state components differ.

      (t (state-diff-psbn p pst qst))
    ))))








(property prop=cdar-sfn (s :s-fn)
  :h (consp s)
  (ps-fnp (cdar s))
  :hints (("Goal" :in-theory (enable s-fnp
                                     acl2::maximal-records-theory))))

(defdata s-fn-change (list symbol
                           peer
                           (v mssg
                              lot
                              ps-fn)))

(in-theory (enable s-fnp ps-fnp s-fn-changep))


(property prop=lomp-seen-diff-fn (pst qst :ps-fn)
  :check-contracts? nil
  :h (consp
      (set-difference-equal (mget :seen qst)
                            (mget :seen pst)))
  (mssgp (car
          (set-difference-equal (mget :seen qst)
                                (mget :seen pst)))))


(property prop=lomp-pending-diff-fn (pst qst :ps-fn)
  :check-contracts? nil
  :h (consp
      (set-difference-equal (mget :pending qst)
                            (mget :pending pst)))
  (mssgp (car
          (set-difference-equal (mget :pending qst)
                                (mget :pending pst)))))


(definec state-diff-psfn (p :peer pst qst :ps-fn) :s-fn-change
  (let ((p-seen (mget :seen pst))
        (q-seen (mget :seen qst))
        (p-pending (mget :pending pst))
        (q-pending (mget :pending qst))
        (p-subs (mget :subs pst))
        (q-subs (mget :subs qst)))
    (cond ((consp
            (set-difference-equal q-seen p-seen))
           (let ((m (car (set-difference-equal q-seen p-seen))))
             `(forward-fn ,p ,m)))
          ((consp
            (set-difference-equal q-pending p-pending))
           (let ((m (car (set-difference-equal q-pending p-pending))))
             (if (== p (mget :or m))
                 `(produce-fn ,p ,m)
               `(forward-fn ,p ,m))))
          ((consp
            (set-difference-equal q-subs p-subs))
           `(subscribe-fn
             ,p
             ,(set-difference-equal q-subs p-subs)))
          ((consp
            (set-difference-equal p-subs q-subs))
           `(unsubscribe-fn
             ,p
             ,(set-difference-equal p-subs q-subs)))
          (t `(unknown-trx
               ,p
               ())))))

(in-theory (disable ps-fnp))

(definec diff-sfn (s u :s-fn) :s-fn-change
  :ic (!= s u)
  (match (list s u)
    ((() ((q . qst) . &)) `(join-fn ,q ,qst))
    ((((p . pst) . &) ()) `(leave-fn ,p ,pst))
    ((((p . pst) . rs1)
      ((q . qst) . rs2))
     (cond
      ((== `(,p . ,pst)
           `(,q . ,qst))
       (diff-sfn rs1 rs2))
      
      ((< (len s) (len u))
       `(join-fn ,q ,qst))

      ((> (len s) (len u))
       `(leave-fn ,p ,pst))

      ;; If lengths are same, then p and q are same, their pubs are
      ;; same, and only the rest of the state components differ.

      (t (state-diff-psfn p pst qst))
      ))))




