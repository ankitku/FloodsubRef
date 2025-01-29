(in-package "ACL2S")
(include-book "f2b-commit")



(definec broadcastedp (m :mssg s :s-fn) :boolean
  (match s
    (() t)
    (((& . pst) . rst)
     (^ (if (in (mget :tp m)
                (mget :subs pst))
            (in m (mget :seen pst))
          t)
        (broadcastedp m rst)))))

;; CONDITION 2
(=> (^ (! (new-fn-mssgp m s))
       (! (in m (fn-pending-mssgs s))))
    (broadcastedp m s))










;; IDEATION ---->>>>>>>>>>>>>>>>>>


;; Need to prove this theorem
(=> (!= (fn-pending-mssgs (forward-fn p m s))
        (fn-pending-mssgs s))
    (== (fn-pending-mssgs (forward-fn p m s))
        (remove-equal m (fn-pending-mssgs s))))



(fn-pending-mssgs (forward-fn p m s))
==
(fn-pending-mssgs (forward-help-fn
                   (mset p
                        (forwarder-new-pst (mget p s) m)
                        s)
                   nbrs
                   m))


(v (== (fn-pending-mssgs (forward-help-fn s nbrs m))
            (insert-unique m (fn-pending-mssgs s)))
        (== (fn-pending-mssgs (forward-help-fn s nbrs m))
            (fn-pending-mssgs s)))


Case 1:

(fn-pending-mssgs (forward-fn p m s))
==
(fn-pending-mssgs (insert-unique m
                   (mset p
                         (forwarder-new-pst (mget p s) m)
                         s)))
== {manipulation}
(fn-pending-mssgs s) which is CONTRA

Case 2: So finally this:
(fn-pending-mssgs (forward-fn p m s))
==
(fn-pending-mssgs (mset p
                        (forwarder-new-pst (mget p s) m)
                        s))
==
(fn-pending-mssgs (mset p
                        (mset :pending
                              (remove-equal m (mget :pending (mget p s)))
                              (mget p s))
                        s))
== 
;; i think rewriting forward-fn would be easier
;; so that it is iterative instead of msetting.







(v (== (fn-pending-mssgs (forward-fn p m s))
       (insert-unique m (fn-pending-mssgs (mset p
                                                (forwarder-new-pst (mget p st) m)
                                                st))))
   
   (== (fn-pending-mssgs (forward-fn p m s))
       (fn-pending-mssgs (mset p
                               (forwarder-new-pst (mget p st) m)
                               st))))

(:casesplit (in m (fn-pending-mssgs (mset p
                                          (forwarder-new-pst (mget p st) m)
                                          st))))

(== (fn-pending-mssgs (forward-fn p m s))
    (fn-pending-mssgs (mset p
                            (forwarder-new-pst (mget p st) m)
                            st)))
So
(!= (fn-pending-mssgs (mset p
                            (forwarder-new-pst (mget p st) m)
                            st))
    (fn-pending-mssgs s))
Contra based on  (in m (fn-pending-mssgs (mset p
                            (forwarder-new-pst (mget p st) m)
                            st)) ) =>
(== (fn-pending-mssgs (mset p
                            (forwarder-new-pst (mget p st) m)
                            st))
                                                    (fn-pending-mssgs s))
Prove

Else,
(! (in m (fn-pending-mssgs (mset p (forwarder-new-pst (mget p st) m)
                                 s))))
So,

(! (in m (fn-pending-mssgs s)))

Contra!





                                                    
    
    
        


(fn-pending-mssgs (forward-fn p m s))
==
(fn-pending-mssgs
 (forward-help-fn (mset p
                        (forwarder-new-pst (mget p st) m)
                        st)
                  fwdnbrs m))
==










NEED THIS THM : (=> (!= (fn-pending-mssgs (forward-fn p m s))
                        (fn-pending-mssgs s))
                    (==  (fn-pending-mssgs (forward-fn p m s))
                         (remove-equal m (fn-pending-mssgs s))))




NEED THIS THM  : (==  (fn-pending-mssgs (forward-fn p m s))
                      (remove-equal m (fn-pending-mssgs s)))



(mset :seen
      (insert-unique m
                     (set-difference-equal (mget :seen ps)
                                           (remove-equal m (fn-pending-mssgs s))))
      pst)



(equal (f2b-help s (fn-pending-mssgs (forward-fn p m s)))
       (broadcast m (f2b s)))



(in-theory (disable f2b f2b-help broadcast fn-pending-mssgs
                   forward-fn forward-help-fn))
(property prop=forward-fn2 (p :peer m :mssg s :s-fn)
  :check-contracts? nil
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (! (in m (mget :seen (mget p s))))
        ;; (! (B s u))
        (! (in m (fn-pending-mssgs (forward-fn p m s))))
        (broadcastedp m (forward-fn p m s)))
  (== (f2b (forward-fn p m s))
      (broadcast m (f2b s)))
  :instructions

  
  (:pro

   (:dv 1 1) :r :s :up :r :r :r
   (:dv 2) :r :up
   (:claim (== (mget p (f2b-help s
                                 (fn-pending-mssgs
                                  (forward-help-fn
                                                   (mset p (forwarder-new-pst (mget p s) m)
                                                         s)
                                                   (mget (mget :tp m)
                                                         (mget :nsubs (mget p s)))
                                                   m))))
               (f2b-st (mget p s)
                       (fn-pending-mssgs
                        (forward-help-fn
                                         (mset p (forwarder-new-pst (mget p s) m)
                                               s)
                                         (mget (mget :tp m)
                                               (mget :nsubs (mget p s)))
                                         m)))))
   (= (f2b-st (mget p s)
              (fn-pending-mssgs
               (forward-help-fn
                                (mset p (forwarder-new-pst (mget p s) m)
                                      s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p s)))
                                m)))
      (mget p (f2b-help s
                        (fn-pending-mssgs
                         (forward-help-fn
                                          (mset p (forwarder-new-pst (mget p s) m)
                                                s)
                                          (mget (mget :tp m)
                                                (mget :nsubs (mget p s)))
                                          m)))))
   :r :top

   (:claim (==  (forward-fn p m s)
                (forward-help-fn
                                 (mset p (forwarder-new-pst (mget p s) m) s)
                                 (mget (mget :tp m) (mget :nsubs (mget p s)))
                                 m))
           :hints (("Goal" :in-theory (enable forward-fn))))
   (= (forward-help-fn
                       (mset p (forwarder-new-pst (mget p s) m) s)
                       (mget (mget :tp m) (mget :nsubs (mget p s)))
                       m)
      (forward-fn p m s))

   ))



















(progn
 (encapsulate nil
   (encapsulate
             ((acl2s-s-fn-undefined (x y)
                                    t
                                    :guard (and (symbolp x) (true-listp y))))
     (local (defun acl2s-s-fn-undefined (x y)
              (declare (ignorable x y))
              'nil))
     (defthm acl2s-s-fn-undefined-s-fnp
       (s-fnp (acl2s-s-fn-undefined x y))
       :rule-classes ((:type-prescription) (:rewrite))))
   (defun acl2s-s-fn-undefined-attached (x y)
     (declare (xargs :guard (and (symbolp x) (true-listp y))))
     (prog2$ (cw? (show-contract-violations?)
                  "~|**Input contract  violation in ~x0**: ~x1 ~%"
                  'acl2s-s-fn-undefined-attached
                  (cons x y))
             'nil))
   (defattach acl2s-s-fn-undefined
              acl2s-s-fn-undefined-attached))
 (encapsulate nil
  (with-output
   :off :all :on (comment error)
   (defun exists-v-2 (s p pubs subs topics nbrs m i)
    (declare
      (xargs :guard (and (s-fnp s)
                         (natp p)
                         (lotp pubs)
                         (lotp subs)
                         (lotp topics)
                         (nat-listp nbrs)
                         (mssgp m)
                         (natp i)
                         (=> (^ (mget (mget :or m) (f2b s))
                                (in (mget :tp m)
                                    (mget :pubs (mget (mget :or m) (f2b s))))
                                (new-bn-mssgp m (f2b (mget :or m))))
                             (^ (mget (mget :or m) s)
                                (new-fn-mssgp m (mget :or m)))))
             :verify-guards nil
             :normalize nil
             :time-limit 150))
    (mbe
      :logic
      (if
       (and (s-fnp s)
            (natp p)
            (lotp pubs)
            (lotp subs)
            (lotp topics)
            (nat-listp nbrs)
            (mssgp m)
            (natp i)
            (=> (^ (mget (mget :or m) (f2b s))
                   (in (mget :tp m)
                       (mget :pubs (mget (mget :or m) (f2b s))))
                   (new-bn-mssgp m (f2b (mget :or m))))
                (^ (mget (mget :or m) s)
                   (new-fn-mssgp m (mget :or m)))))
       (if (mget p (f2b s))
           (match (mod i 6)
                  (0 (unsubscribe-fn p topics s))
                  (1 (subscribe-fn p topics s))
                  (2 (leave-fn p s))
                  (3 (cond ((^ (mget (mget :or m) (f2b s))
                               (new-bn-mssgp m (f2b s))
                               (in (mget :tp m)
                                   (mget :pubs (mget (mget :or m) (f2b s)))))
                            (produce-fn m s))
                           (t (skip-fn s))))
                  (& (skip-fn s)))
         (if (zp (mod i 6))
             (skip-fn s)
           (join-fn p pubs subs nbrs s)))
       (acl2s-s-fn-undefined 'exists-v-2
                             (list s p pubs subs topics nbrs m i)))
      :exec
      (if (mget p (f2b s))
          (match (mod i 6)
                 (0 (unsubscribe-fn p topics s))
                 (1 (subscribe-fn p topics s))
                 (2 (leave-fn p s))
                 (3 (cond ((^ (mget (mget :or m) (f2b s))
                              (new-bn-mssgp m (f2b s))
                              (in (mget :tp m)
                                  (mget :pubs (mget (mget :or m) (f2b s)))))
                           (produce-fn m s))
                          (t (skip-fn s))))
                 (& (skip-fn s)))
        (if (zp (mod i 6))
            (skip-fn s)
          (join-fn p pubs subs nbrs s)))))))
 (defthm exists-v-2-contract
   (implies (and (s-fnp s)
                 (natp p)
                 (lotp pubs)
                 (lotp subs)
                 (lotp topics)
                 (nat-listp nbrs)
                 (mssgp m)
                 (natp i)
                 (=> (^ (mget (mget :or m) (f2b s))
                        (in (mget :tp m)
                            (mget :pubs (mget (mget :or m) (f2b s))))
                        (new-bn-mssgp m (f2b (mget :or m))))
                     (^ (mget (mget :or m) s)
                        (new-fn-mssgp m (mget :or m)))))
            (s-fnp (exists-v-2 s p pubs subs topics nbrs m i)))
   :hints (("Goal" :use (prop=not-mget=not-mget-f2b))))
 (encapsulate nil
   (with-output
        :off :all :on (comment error)
        (verify-guards exists-v-2
                       :guard-debug t
                       :hints (("Goal" :in-theory (enable prop=mget-f2b=mget)
                                       :use (prop=mget-f2b=mget)))))))





   (:claim (== (mget :pubs (f2b-st (forwarder-new-pst (mget p s) m)
                                   (fn-pending-mssgs (forward-fn p m s))))
               (mget :pubs (forwarder-new-pst (mget p s) m)))
           :hints (("Goal" :use ((:instance prop=f2b-st-check
                                            (ps (forwarder-new-pst (mget p s)
                                                                   m))
                                            (ms (fn-pending-mssgs (forward-fn p m s))))))))

   (:claim (== (mget :pubs (f2b-st (mget p s)
                                   (fn-pending-mssgs s)))
               (mget :pubs (mget p s)))
           :hints (("Goal" :use ((:instance prop=f2b-st-check
                                            (ps (mget p s))
                                            (ms (fn-pending-mssgs s)))))))
   
   (:claim (== (mget :pubs (forwarder-new-pst (mget p s) m))
               (mget :pubs (mget p s))))

   (:claim (== (f2b-st (mget p s)
                       (fn-pending-mssgs s))
               (mget p s)))


























;; tries





(property h9 (p :peer s :s-fn m :mssg)
  :check-contracts? nil
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (! (in m (mget :seen (mget p s))))
        (== (f2b (forward-fn p m s))
            (f2b s)))
  (in m (fn-pending-mssgs (forward-fn p m s)))
  :instructions
  (:pro
   (:claim (== (f2b-help (forward-fn p m s)
                         (fn-pending-mssgs (forward-fn p m s)))
               (f2b-help s
                         (fn-pending-mssgs s)))
           :hints (("Goal" :in-theory (enable f2b-definition-rule))))

   (:claim (== (forward-fn p m s)
               (forward-help-fn p
                                (mset p
                                      (forwarder-new-pst (mget p s) m)
                                      s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p s)))
                                m))
           :hints (("Goal" :in-theory (enable forward-fn-definition-rule))))

   (:claim (== (f2b-help (forward-help-fn p
                                (mset p
                                      (forwarder-new-pst (mget p s) m)
                                      s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p s)))
                                m)
                         (fn-pending-mssgs (forward-fn p m s)))
               (f2b-help s
                         (fn-pending-mssgs s))))


   (:claim (== (f2b-help (forward-help-fn p
                                (mset p
                                      (forwarder-new-pst (mget p s) m)
                                      s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p s)))
                                m)
                         (fn-pending-mssgs (forward-fn p m s)))
               (f2b-help (mset p (forwarder-new-pst (mget p s) m) s)
                         (fn-pending-mssgs (forward-fn p m s))))
           :hints (("Goal" :use ((:instance prop=f2b-forward-fn-help
                                            (s (mset p
                                                     (forwarder-new-pst (mget p s) m)
                                                     s))
                                            (nbrs (mget (mget :tp m)
                                                        (mget :nsubs (mget p
                                                                           s))))
                                            (ms (fn-pending-mssgs (forward-fn p
                                                                              m s))))))))

   (:claim (== (f2b-help (mset p (forwarder-new-pst (mget p s) m) s)
                         (fn-pending-mssgs (forward-fn p m s)))
               (f2b-help s (fn-pending-mssgs s))))

   (:claim (== (f2b-help (mset p (forwarder-new-pst (mget p s) m) s)
                         (fn-pending-mssgs (forward-fn p m s)))
               (mset p (f2b-st (forwarder-new-pst (mget p s) m)
                               (fn-pending-mssgs (forward-fn p m s)))
                     (f2b-help s (fn-pending-mssgs (forward-fn p m s))))))
   
   (:claim (== (mset p (f2b-st (forwarder-new-pst (mget p s) m)
                               (fn-pending-mssgs (forward-fn p m s)))
                     (f2b-help s (fn-pending-mssgs (forward-fn p m s))))
               (f2b-help s (fn-pending-mssgs s))))

   (:claim (== (mget p (mset p (f2b-st (forwarder-new-pst (mget p s) m)
                               (fn-pending-mssgs (forward-fn p m s)))
                             (f2b-help s (fn-pending-mssgs (forward-fn p m s)))))
               (mget p (f2b-help s (fn-pending-mssgs s)))))

   (drop 8 9 10 11 12 13 14) 

   (:demote 8)
   (:dv 1 1) (:r 2) :top :pro

   (:claim (== (mget p (f2b-help s (fn-pending-mssgs s)))
               (f2b-st (mget p s) (fn-pending-mssgs s))))

   (:claim (== (f2b-st (forwarder-new-pst (mget p s) m)
                       (fn-pending-mssgs (forward-fn p m s)))
               (f2b-st (mget p s)
                       (fn-pending-mssgs s))))
               
   (:claim (== (mget :seen (f2b-st (forwarder-new-pst (mget p s) m)
                                   (fn-pending-mssgs (forward-fn p m s))))
               (mget :seen (f2b-st (mget p s)
                                   (fn-pending-mssgs s)))))

   (:claim (== (mget :seen (f2b-st (forwarder-new-pst (mget p s) m)
                                   (fn-pending-mssgs (forward-fn p m s))))
               (set-difference-equal (mget :seen (forwarder-new-pst (mget p s) m))
                                     (fn-pending-mssgs (forward-fn p m s))))
               :hints (("Goal" :use ((:instance prop=f2b-st-check
                                            (ps (forwarder-new-pst (mget p s) m))
                                            (ms (fn-pending-mssgs (forward-fn p
                                                                              m s))))))))

   (:claim (== (mget :seen (f2b-st (mget p s)
                                   (fn-pending-mssgs s)))
               (set-difference-equal (mget :seen (mget p s))
                                     (fn-pending-mssgs s)))
           :hints (("Goal" :use ((:instance prop=f2b-st-check
                                            (ps (mget p s))
                                            (ms (fn-pending-mssgs s)))))))

   (:claim (== (set-difference-equal (mget :seen (forwarder-new-pst (mget p s) m))
                                     (fn-pending-mssgs (forward-fn p m s)))
               (set-difference-equal (mget :seen (mget p s))
                                     (fn-pending-mssgs s))))

   (:claim  (== (forwarder-new-pst (mget p s) m)
                (mset :seen
                      (insert-unique m (mget :seen (mget p s)))
                      (mset :pending
                            (remove-equal m (mget :pending (mget p s)))
                            (mget p s))))
            :hints (("Goal" :use ((:instance forwarder-new-pst-definition-rule
                                             (pst (mget p s)))))))
   
   (:claim  (== (mget :seen (forwarder-new-pst (mget p s) m))
                (mget :seen
                      (mset :seen
                            (insert-unique m (mget :seen (mget p s)))
                            (mset :pending
                                  (remove-equal m (mget :pending (mget p s)))
                                  (mget p s))))))
   (:demote 16)
   (:dv 1 2) (:r 4) :top :pro
            
   (:claim (== (set-difference-equal (mget :seen (mget p s))
                                     (fn-pending-mssgs s))
               (set-difference-equal (insert-unique m (mget :seen (mget p s)))
                                     (fn-pending-mssgs (forward-fn p m s)))
               ))

   (:drop 8 9 10 11 12 13 14 15 16)

   (:claim (in m (insert-unique m (mget :seen (mget p s))))
           :hints (("Goal" :use ((:instance in-insert-unique
                                            (x (mget :seen (mget p s))))))))
   (:claim (in m (fn-pending-mssgs s))
           :hints (("Goal" :use ((:instance prop=in-p-fn-pending)))))
   
   (:claim (! (in m (set-difference-equal (mget :seen (mget p s))
                                          (fn-pending-mssgs s))))
           :hints (("Goal" :use ((:instance not-in-diff2
                                            (x (mget :seen (mget p s)))
                                            (y (fn-pending-mssgs s)))))))

   (:demote 11) (:dv 1 1 2)
   (:equiv (set-difference-equal (mget :seen (mget p s))
                                 (fn-pending-mssgs s))
           (set-difference-equal (insert-unique m (mget :seen (mget p s)))
                                 (fn-pending-mssgs (forward-fn p m s))))
   :pro

   (:claim (in m (fn-pending-mssgs (forward-fn p m s)))
           :hints (("Goal" :use ((:instance in-diff1
                                            (x (insert-unique m (mget :seen
                                                                      (mget p s))))
                                            (y (fn-pending-mssgs (forward-fn p m s))))))))
   :s
   ))


.


;; (property h12 (p :peer s :s-fn nbrs :lop m :mssg)
;;   :h (^ (mget p s)
;;         (! (in p nbrs))
;;         (in m (mget :pending (mget p s)))
;;         (! (in m (mget :seen (mget p s))))
;;         (!= (fn-pending-mssgs (forward-help-fn p s nbrs m))
;;             (fn-pending-mssgs s)))
;;   (! (in m (fn-pending-mssgs (forward-fn p m s))))
;;   :instructions
;;   (:pro
;;    :induct :bash :pro
;;    (:casesplit (== p (car (car s))))
;;    (:claim (== (mget p s) (cdr (car s))))

;;    (:dv 1 2 1) :r :s

;;    (:claim (ps-fnp (cdr (car s))))
;;    (= p (car (car s)))
   


;;    :up :r :s :up
;;    (:claim (in m (mget :pending (cdr (car s)))))
;;    (= (v (in m (mget :pending (cdr (car s))))
;;          (in m (fn-pending-mssgs (forward-help-fn p (cdr s) nbrs m)))))
   

   

;; (property h11 (p :peer s :s-fn nbrs :lop m :mssg)
;;   (== (insert-unique m (fn-pending-mssgs (forward-help-fn p s nbrs m)))
;;       (fn-pending-mssgs s))
;;   :instructions
;;   (:pro ))
;;    :induct :bash :pro
;;    (:claim (== (insert-unique m
;;                               (fn-pending-mssgs
;;                                (forward-help-fn p (cdr s) nbrs m)))
;;                (fn-pending-mssgs (cdr s))))
;;    (:dv 1 2 1) :r :s
;;    (:casesplit (in (car (car s)) nbrs))
;;    :s :up :r :s (:dv 1 2) :r
;;    (:casesplit (^ (! (member-equal m (mget :pending (cdr (car s)))))
;;                   (! (member-equal m (mget :seen (cdr (car s)))))))

;;    :s :up :s :up :r (:r 2) :up :s
;;    (= (insert-unique
;;        m
;;        (union-set (fn-pending-mssgs (forward-help-fn p (cdr s) nbrs m))
;;                   (mget :pending (cdr (car s)))))
;;       (union-set (insert-unique
;;                   m
;;                   (fn-pending-mssgs (forward-help-fn p (cdr s) nbrs m)))
;;                  (mget :pending (cdr (car s)))))
;;    :s :r
;;    (= (union-set (mget :pending (cdr (car s)))
;;                  (fn-pending-mssgs (cdr s)))
;;       (fn-pending-mssgs s))
;;    :top :s :bash :bash :bash :s

;;    (:casesplit (member-equal m (mget :pending (cdr (car s)))))
;;    :s :up :up :up
;;    (= (insert-unique
;;        m
;;        (union-set (mget :pending (cdr (car s)))
;;                   (fn-pending-mssgs (forward-help-fn p (cdr s) nbrs m))))
;;       (union-set (mget :pending (cdr (car s)))
;;                  (insert-unique  m (fn-pending-mssgs (forward-help-fn p (cdr s)
;;                                                                       nbrs m)))))
;;    :s
;;    (= (union-set (mget :pending (cdr (car s)))
;;                  (fn-pending-mssgs (cdr s)))
;;       (fn-pending-mssgs s))
;;    :top :s

;;    (:claim (member-equal m (mget :seen (cdr (car s)))))
;;    :s :up :up :up
;;    (= (insert-unique
;;        m
;;        (union-set (mget :pending (cdr (car s)))
;;                   (fn-pending-mssgs (forward-help-fn p (cdr s) nbrs m))))
;;       (union-set (mget :pending (cdr (car s)))
;;                  (insert-unique  m (fn-pending-mssgs (forward-help-fn p (cdr s)
;;                                                                       nbrs m)))))
;;    :s
;;    (= (union-set (mget :pending (cdr (car s)))
;;                  (fn-pending-mssgs (cdr s)))
;;       (fn-pending-mssgs s))
;;    :top :s

;;    :bash
;;    (= (cons (cons (car (car s))
;;                    (add-pending-psfn m (cdr (car s))))
;;             (forward-help-fn p (cdr s) nbrs m))
;;       (forward-help-fn p s nbrs m)
;;       :hints (("Goal" :in-theory (enable forward-help-fn))))
;;    :s

;;    :s :up :r :s :up
;;    (= (insert-unique
;;        m
;;        (union-set (mget :pending (cdr (car s)))
;;                   (fn-pending-mssgs (forward-help-fn p (cdr s) nbrs m))))
;;       (union-set (mget :pending (cdr (car s)))
;;                  (insert-unique  m (fn-pending-mssgs (forward-help-fn p (cdr s)
;;                                                                       nbrs m)))))
;;    :s
;;    (= (union-set (mget :pending (cdr (car s)))
;;                  (fn-pending-mssgs (cdr s)))
;;       (fn-pending-mssgs s))
;;    :top :s

;;    (= (cons (car s)
;;             (forward-help-fn p (cdr s) nbrs m))
;;       (forward-help-fn p s nbrs m)
;;       :hints (("Goal" :in-theory (enable forward-help-fn))))
;;    :s
;;    ))
   
   
   

   

   
   
;; TODO : ASSUMING for now, need to do this
(property prop=forward-fn2 (p :peer m :mssg s :s-fn)
  :check-contracts? nil
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (! (in m (mget :seen (mget p s))))
        ;; (not (B s u))
        (!= (fn-pending-mssgs (forward-fn p m s))
            (fn-pending-mssgs s))
        ;; Condition 2 : Origin hasn't left yet
        (mget (mget :or m) (f2b s))
        (in (mget :tp m)
            (mget :pubs (mget  (mget :or m) (f2b s)))))
  (== (f2b (forward-fn p m s))
      (broadcast m (f2b s)))

  :instructions
  (:pro
   (:dv 1 1) :r :s :up :r :r :r
   (:dv 2) :r :up
   (:claim (== (mget p (f2b-help s
                                 (fn-pending-mssgs
                                  (forward-help-fn p
                                                   (mset p (forwarder-new-pst (mget p s) m)
                                                         s)
                                                   (mget (mget :tp m)
                                                         (mget :nsubs (mget p s)))
                                                   m))))
               (f2b-st (mget p s)
                       (fn-pending-mssgs
                        (forward-help-fn p
                                         (mset p (forwarder-new-pst (mget p s) m)
                                               s)
                                         (mget (mget :tp m)
                                               (mget :nsubs (mget p s)))
                                         m)))))
   (= (f2b-st (mget p s)
              (fn-pending-mssgs
               (forward-help-fn p
                                (mset p (forwarder-new-pst (mget p s) m)
                                      s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p s)))
                                m)))
      (mget p (f2b-help s
                        (fn-pending-mssgs
                         (forward-help-fn p
                                          (mset p (forwarder-new-pst (mget p s) m)
                                                s)
                                          (mget (mget :tp m)
                                                (mget :nsubs (mget p s)))
                                          m)))))
   :r :top
   (:claim (==  (forward-fn p m s)
                (forward-help-fn p
                                 (mset p (forwarder-new-pst (mget p s) m) s)
                                 (mget (mget :tp m) (mget :nsubs (mget p s)))
                                 m))
           :hints (("Goal" :in-theory (enable forward-fn))))
   (= (forward-help-fn p
                       (mset p (forwarder-new-pst (mget p s) m) s)
                       (mget (mget :tp m) (mget :nsubs (mget p s)))
                       m)
      (forward-fn p m s))
))

(= (fn-pending-mssgs (forward-fn p m s))
   (set-difference-equal (fn-pending-mssgs s) (list m)))
   (:claim (== (f2b s)
               (f2b-help s (fn-pending-mssgs s)))
           :hints (("Goal" :in-theory (enable f2b))))
   :s


   (:claim (! (in m (fn-pending-mssgs s))))
   (:claim (in m (fn-pending-mssgs (forward-fn p m s))))
   (:claim (in m (fn-pending-mssgs (forward-help-fn p
                                     (mset p (forwarder-new-pst (mget p s) m)
                                           s)
                                     (mget (mget :tp m)
                                           (mget :nsubs (mget p s)))
                                     m)))
           :hints (("Goal" :in-theory (enable forward-fn))))
   :s

   :bash :bash))



  
  
(progn
 (encapsulate nil
   (encapsulate
              ((acl2s-nat-undefined (x y)
                                    t
                                    :guard (and (symbolp x) (true-listp y))))
     (local (defun acl2s-nat-undefined (x y)
              (declare (ignorable x y))
              '0))
     (defthm acl2s-nat-undefined-natp
       (natp (acl2s-nat-undefined x y))
       :rule-classes ((:type-prescription) (:rewrite))))
   (defun acl2s-nat-undefined-attached (x y)
     (declare (xargs :guard (and (symbolp x) (true-listp y))))
     (prog2$ (cw? (show-contract-violations?)
                  "~|**Input contract  violation in ~x0**: ~x1 ~%"
                  'acl2s-nat-undefined-attached
                  (cons x y))
             '0))
   (defattach acl2s-nat-undefined
              acl2s-nat-undefined-attached))
 (encapsulate nil
   (with-output :off :all :on (comment error)
                (defun find-forwarder (s m)
                  (declare (xargs :guard (and (s-fnp s)
                                              (mssgp m)
                                              (in m (fn-pending-mssgs s)))
                                  :verify-guards nil
                                  :normalize nil
                                  :time-limit 150))
                  (mbe :logic
                       (if (and (s-fnp s)
                                (mssgp m)
                                (in m (fn-pending-mssgs s)))
                           (b* ((- (consp s)))
                             (match s (((p . &)) p)
                                    (((p . pst) . rst)
                                     (if (in m (mget :pending pst))
                                         p
                                       (find-forwarder rst m)))))
                         (acl2s-nat-undefined 'find-forwarder
                                              (list s m)))
                       :exec
                       (b* ((- (consp s)))
                         (match s (((p . &)) p)
                                (((p . pst) . rst)
                                 (if (in m (mget :pending pst))
                                     p
                                   (find-forwarder rst m)))))))))
 (defthm find-forwarder-contract
   (implies (and (s-fnp s)
                 (mssgp m)
                 (in m (fn-pending-mssgs s)))
            (natp (find-forwarder s m))))
 (encapsulate nil
  (with-output
    :off :all :on (comment error)
    (verify-guards find-forwarder
                   :guard-debug t
                   :hints (("Goal" :in-theory (enable fn-pending-mssgs)))))))










(encapsulate ()
  (local
   (propertyd x1 (s w :s-fn p :peer)
     :check-contracts? nil
     :h (^ (!= s w)
           (== (f2b s) (f2b w))
           (mget p s))
     (== (mget :subs (mget p (f2b s)))
         (mget :subs (mget p (f2b w))))
     :hints (("Goal" :in-theory (enable f2b f2b-help)))))

  (local
   (propertyd x3 (s w :s-fn p :peer)
     :check-contracts? nil
     :h (^ (!= s w)
           (== (f2b s) (f2b w))
           (mget p s))
     (== (mget :pubs (mget p (f2b s)))
         (mget :pubs (mget p (f2b w))))
     :hints (("Goal" :in-theory (enable f2b f2b-help)))))

  (local
   (propertyd x5 (s w :s-fn p :peer)
     :check-contracts? nil
     :h (^ (!= s w)
           (== (f2b s) (f2b w))
           (mget p s))
     (== (mget :nsubs (mget p (f2b s)))
         (mget :nsubs (mget p (f2b w))))
     :hints (("Goal" :in-theory (enable f2b f2b-help)))))

  (local
   (propertyd x2 (s w :s-fn p :peer)
     :check-contracts? nil
     :h (^ (!= s w)
           (mget p s)
           (mget p w)
           (== (mget :subs (mget p (f2b s)))
               (mget :subs (mget p (f2b w)))))
     (== (mget :subs (mget p s))
         (mget :subs (mget p w)))
     :hints (("Goal" :in-theory (enable f2b f2b-help)))))

  (local
   (propertyd x4 (s w :s-fn p :peer)
     :check-contracts? nil
     :h (^ (!= s w)
           (mget p s)
           (mget p w)
           (== (mget :pubs (mget p (f2b s)))
               (mget :pubs (mget p (f2b w)))))
     (== (mget :pubs (mget p s))
         (mget :pubs (mget p w)))
     :hints (("Goal" :in-theory (enable f2b f2b-help)))))

  (local
   (propertyd x6 (s w :s-fn p :peer)
     :check-contracts? nil
     :h (^ (!= s w)
           (mget p s)
           (mget p w)
           (== (mget :nsubs (mget p (f2b s)))
               (mget :nsubs (mget p (f2b w)))))
     (== (mget :nsubs (mget p s))
         (mget :nsubs (mget p w)))
     :hints (("Goal" :in-theory (enable f2b f2b-help)))))

  (property x7 (s w :s-fn p :peer)
    :check-contracts? nil  
    :h (^ (!= s w)
          (== (f2b s) (f2b w))
          (mget p s))
    (^ (== (mget :subs (mget p s))
           (mget :subs (mget p w)))
       (== (mget :pubs (mget p s))
           (mget :pubs (mget p w))))
    :instructions
    (:pro
     (:claim
      (== (mget :subs (mget p (f2b s)))
          (mget :subs (mget p (f2b w))))
      :hints (("Goal" :use (x1))))
     (:claim
      (== (mget :pubs (mget p (f2b s)))
          (mget :pubs (mget p (f2b w))))
      :hints (("Goal" :use (x3))))
     (:claim (mget p w))
     (= (mget :subs (mget p s))
        (mget :subs (mget p w))
        :hints (("Goal" :use (x2))))
     (= (mget :pubs (mget p s))
        (mget :pubs (mget p w))
        :hints (("Goal" :use (x4)))))))


(property not-eq-sub (s w :s-fn p :peer topics :lot)
     :check-contracts? nil
     :h (^ (!= s w)
           (== (f2b s) (f2b w))
           (== (ps-fn-nbrs (mget p s))
               (ps-fn-nbrs (mget p w)))
           (mget p s))
     (!= (subscribe-fn p topics s)
         (subscribe-fn p topics w))
     :hints (("Goal" :in-theory (enable subscribe-fn
                                        set-subs-sfn))))
  

(property not-eq-pub (s u w v :s-fn p :peer pubs subs topics :lot
                          nbrs :lop m :mssg i :nat)
  :check-contracts? nil
  :h (^ (!= s w)
        (== (f2b s) (f2b w))
        (mget p s))
  (== (mget :pubs (mget p (f2b s)))
      (mget :pubs (mget p (f2b w))))
  :hints (("Goal" :in-theory (enable f2b f2b-help))))

(property not-eq-nbrs (s u w v :s-fn p :peer pubs subs topics :lot
                          nbrs :lop m :mssg i :nat)
  :check-contracts? nil
  :h (^ (!= s w)
        (== (f2b s) (f2b w))
        (mget p s))
  (== (mget :nbrs (mget p (f2b s)))
      (mget :nbrs (mget p (f2b w))))
  :hints (("Goal" :in-theory (enable f2b f2b-help))))

(property not-eq-subq (s u w v :s-fn p :peer pubs subs topics :lot
                          nbrs :lop m :mssg i :nat)
  :check-contracts? nil
  :h (^ (!= s w)
        (== (f2b s) (f2b w))
        (mget p s))
  (== (subscribe-fn p topics s)
      (subscribe-fn p topics w))
  :hints (("Goal" :in-theory (enable f2b f2b-help
                                     subscribe-fn))))















   


      
   
       
   (= (forward-help-fn s nbrs m)
      (if (in (car (car s)) nbrs)
          (cons (cons (car (car s))
                      (add-pending-psfn m (cdr (car s))))
                (forward-help-fn (cdr s) nbrs m))
        (cons (car s)
              (forward-help-fn (cdr s) nbrs m))))

   :s

   (= (fn-pending-mssgs (cons (cons (car (car s))
                                          (add-pending-psfn m (cdr (car s))))
                              (forward-help-fn (cdr s) nbrs m)))
      (union-set (mget :pending (cdr (car (forward-help-fn s nbrs m))))

   

   (:claim (v (== (mget :pending (cdr (car (forward-help-fn s nbrs m))))
         (mget :pending (cdr (car s))))
     (== (mget :pending (cdr (car (forward-help-fn s nbrs m))))
         (cons m (mget :pending (cdr (car s))))))




   (:casesplit (in (car (car s)) nbrs))
   :s :up :r :s (:dv 1 2) :r
   (:casesplit (^ (! (member-equal m (mget :pending (cdr (car s)))))
                  (! (member-equal m (mget :seen (cdr (car s)))))))

   :s :up :s :up :r (:r 2) :up :s
   (= (insert-unique
       m
       (union-set (fn-pending-mssgs (forward-help-fn p (cdr s) nbrs m))
                  (mget :pending (cdr (car s)))))
      (union-set (insert-unique
                  m
                  (fn-pending-mssgs (forward-help-fn p (cdr s) nbrs m)))
                 (mget :pending (cdr (car s)))))
   :s :r
   (= (union-set (mget :pending (cdr (car s)))
                 (fn-pending-mssgs (cdr s)))
      (fn-pending-mssgs s))
   :top :s :bash :bash :bash :s

   (:casesplit (member-equal m (mget :pending (cdr (car s)))))
   :s :up :up :up
   (= (insert-unique
       m
       (union-set (mget :pending (cdr (car s)))
                  (fn-pending-mssgs (forward-help-fn p (cdr s) nbrs m))))
      (union-set (mget :pending (cdr (car s)))
                 (insert-unique  m (fn-pending-mssgs (forward-help-fn p (cdr s)
                                                                      nbrs m)))))
   :s
   (= (union-set (mget :pending (cdr (car s)))
                 (fn-pending-mssgs (cdr s)))
      (fn-pending-mssgs s))
   :top :s

   (:claim (member-equal m (mget :seen (cdr (car s)))))
   :s :up :up :up
   (= (insert-unique
       m
       (union-set (mget :pending (cdr (car s)))
                  (fn-pending-mssgs (forward-help-fn p (cdr s) nbrs m))))
      (union-set (mget :pending (cdr (car s)))
                 (insert-unique  m (fn-pending-mssgs (forward-help-fn p (cdr s)
                                                                      nbrs m)))))
   :s
   (= (union-set (mget :pending (cdr (car s)))
                 (fn-pending-mssgs (cdr s)))
      (fn-pending-mssgs s))
   :top :s

   :bash
   (= (cons (cons (car (car s))
                   (add-pending-psfn m (cdr (car s))))
            (forward-help-fn p (cdr s) nbrs m))
      (forward-help-fn p s nbrs m)
      :hints (("Goal" :in-theory (enable forward-help-fn))))
   :s

   :s :up :r :s :up
   (= (insert-unique
       m
       (union-set (mget :pending (cdr (car s)))
                  (fn-pending-mssgs (forward-help-fn p (cdr s) nbrs m))))
      (union-set (mget :pending (cdr (car s)))
                 (insert-unique  m (fn-pending-mssgs (forward-help-fn p (cdr s)
                                                                      nbrs m)))))
   :s
   (= (union-set (mget :pending (cdr (car s)))
                 (fn-pending-mssgs (cdr s)))
      (fn-pending-mssgs s))
   :top :s

   (= (cons (car s)
            (forward-help-fn p (cdr s) nbrs m))
      (forward-help-fn p s nbrs m)
      :hints (("Goal" :in-theory (enable forward-help-fn))))
   :s
   ))









 (encapsulate nil
   (encapsulate
          ((acl2s-boolean-undefined (x y)
                                    t
                                    :guard (and (symbolp x) (true-listp y))))
     (local (defun acl2s-boolean-undefined (x y)
              (declare (ignorable x y))
              't))
     (defthm acl2s-boolean-undefined-booleanp
       (booleanp (acl2s-boolean-undefined x y))
       :rule-classes ((:type-prescription) (:rewrite))))
   (defun acl2s-boolean-undefined-attached (x y)
     (declare (xargs :guard (and (symbolp x) (true-listp y))))
     (prog2$ (cw? (show-contract-violations?)
                  "~|**Input contract  violation in ~x0**: ~x1 ~%"
                  'acl2s-boolean-undefined-attached
                  (cons x y))
             't))
   (defattach acl2s-boolean-undefined
              acl2s-boolean-undefined-attached))
 (encapsulate nil
  (with-output
   :off :all :on (comment error)
   (defun exists-v (s u w v p pubs subs topics nbrs m opt ept)
    (declare (xargs :guard (and (borfp s)
                                (borfp u)
                                (borfp w)
                                (borfp v)
                                (natp p)
                                (lotp pubs)
                                (lotp subs)
                                (lotp topics)
                                (nat-listp nbrs)
                                (mssgp m)
                                (optp opt)
                                (optp ept))
                    :verify-guards nil
                    :normalize nil
                    :time-limit 300))
    (mbe
     :logic
     (if (and (borfp s)
              (borfp u)
              (borfp w)
              (borfp v)
              (natp p)
              (lotp pubs)
              (lotp subs)
              (lotp topics)
              (nat-listp nbrs)
              (mssgp m)
              (optp opt)
              (optp ept))
         (cond ((^ (bnp s) (bnp w))
                (^ (== v u) (== ept opt)))
               ((^ (fnp s) (bnp w))
                (^ (== v (f2b-ref u))
                   (== ept (exists-v1-ept (cdr s) p m opt))))
               ((^ (bnp s) (fnp w))
                (^ (rel->borf w v p pubs subs topics nbrs m opt)
                   (== ept opt)))
               ((^ (fnp s) (fnp w))
                (^ (rel->borf w v p pubs subs topics
                              nbrs m (exists-v1-ept (cdr s) p m opt))
                   (== ept (exists-v1-ept (cdr s) p m opt)))))
      (acl2s-boolean-undefined 'exists-v
                               (list s u
                                     w v p pubs subs topics nbrs m opt ept)))
     :exec (cond ((^ (bnp s) (bnp w))
                  (^ (== v u) (== ept opt)))
                 ((^ (fnp s) (bnp w))
                  (^ (== v (f2b-ref u))
                     (== ept (exists-v1-ept (cdr s) p m opt))))
                 ((^ (bnp s) (fnp w))
                  (^ (rel->borf w v p pubs subs topics nbrs m opt)
                     (== ept opt)))
                 ((^ (fnp s) (fnp w))
                  (^ (rel->borf w v p pubs subs topics
                                nbrs m (exists-v1-ept (cdr s) p m opt))
                     (== ept
                         (exists-v1-ept (cdr s) p m opt)))))))))
 (defthm exists-v-contract
   (implies (and (borfp s)
                 (borfp u)
                 (borfp w)
                 (borfp v)
                 (natp p)
                 (lotp pubs)
                 (lotp subs)
                 (lotp topics)
                 (nat-listp nbrs)
                 (mssgp m)
                 (optp opt)
                 (optp ept))
            (booleanp (exists-v s u w
                                v p pubs subs topics nbrs m opt ept))))
 (encapsulate nil
  (with-output :off :all :on (comment error)
               (verify-guards exists-v
                              :guard-debug t
                              :hints (("Goal" :in-theory (enable borfp)))))))





