(in-package "ACL2S")
(include-book "fn")

;;----- forward-fn ----- 

(property prop=forward-fn-def (p :peer m :mssg s :s-fn)
  :h  (^ (mget p s)
         (in m (mget :pending (mget p s)))
         (! (in m (mget :seen (mget p s)))))
  (== (forward-fn p m s)
      (forward-help-fn p
                       s
                       (mget (mget :tp m)
                             (mget :nsubs (mget p s)))
                       m))
  :hints (("Goal" :in-theory (enable forward-fn))))

(property prop=mget-add-pending-psfn (m :mssg pst :ps-fn)
  (^ (== (mget :seen (add-pending-psfn m pst))
         (mget :seen pst))
     (== (mget :subs (add-pending-psfn m pst))
         (mget :subs pst))
     (== (mget :pubs (add-pending-psfn m pst))
         (mget :pubs pst)))
  :hints (("Goal" :in-theory (enable add-pending-psfn))))

(property prop=f2b-st-add-pending-psfn (m :mssg pst :ps-fn ms :lom)
  (== (f2b-st (add-pending-psfn m pst) ms)
      (f2b-st pst ms))
  :hints (("Goal" :in-theory (enable f2b-st))))


(in-theory (enable acl2::maximal-records-theory))
(property prop=forward-fn (p :peer s :s-fn ms :lom m :mssg)
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (! (in m (mget :seen (mget p s)))))
  (== (f2b-help (forward-fn p m s) ms)
      (f2b-help s ms))
  :instructions
  ((:induct (mget p s))
   :pro
   (:claim (! (lexorder p (car (car s)))))
   (:claim (mget p (cdr s)))
   (:claim (in m (mget :pending (mget p (cdr s)))))
   (:claim (not (in m (mget :seen (mget p (cdr s))))))
   (:claim (equal (f2b-help (forward-fn p m (cdr s)) ms)
                  (f2b-help (cdr s) ms)))
   (:dv 1 1) (:r 2) :s :r :s

   (:casesplit (in (car (car s))
                   (mget (mget :tp m)
                         (mget :nsubs (mget p s)))))

   (:claim (== (mget p s) (mget p (cdr s))))
   (:equiv (mget p s) (mget p (cdr s)))

   (:claim (== (forward-help-fn p (cdr s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p (cdr s))))
                                m)
               (forward-fn p m (cdr s)))
           :hints (("Goal" :use ((:instance prop=forward-fn-def (s (cdr
                                                                    s)))))))
   (:equiv (forward-help-fn p (cdr s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p (cdr s))))
                                m)
           (forward-fn p m (cdr s)))
   (:equiv (mget p s) (mget p (cdr s)))
   (:equiv (forward-help-fn p (cdr s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p (cdr s))))
                                m)
           (forward-fn p m (cdr s)))
   (:equiv (f2b-help (forward-fn p m (cdr s)) ms)
           (f2b-help (cdr s) ms))
  
   ))


   (:casesplit (! (in (car (car s))
                      (mget (mget :tp m)
                            (mget :nsubs (mget p s))))))
   :s
  
   (:claim (== (mget p s) (mget p (cdr s))))
   (:equiv (mget p s) (mget p (cdr s)))

   (:claim (== (forward-help-fn p (cdr s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p (cdr s))))
                                m)
               (forward-fn p m (cdr s)))
           :hints (("Goal" :use ((:instance prop=forward-fn-def (s (cdr
                                                                    s)))))))
   (:equiv (forward-help-fn p (cdr s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p (cdr s))))
                                m)
           (forward-fn p m (cdr s)))
   :up :r :s
   (:equiv (mget p s) (mget p (cdr s)))
   (:equiv (forward-help-fn p (cdr s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p (cdr s))))
                                m)
           (forward-fn p m (cdr s)))
   (:equiv (f2b-help (forward-fn p m (cdr s)) ms)
           (f2b-help (cdr s) ms))
   (:claim (== (cons (cons (car (car s))
                           (f2b-st (cdr (car s)) ms))
                     (f2b-help (cdr s) ms))
               (f2b-help s ms)))
   (:equiv (cons (cons (car (car s))
                           (f2b-st (cdr (car s)) ms))
                     (f2b-help (cdr s) ms))
           (f2b-help s ms))
   :up :s


   
   ))
  
   
   
   (:claim (equal (f2b (forward-fn p m (cdr s)))
                  (f2b (cdr s))))
   (:dv 1 1) (:r 2) :s :r :s

   ))

   (:casesplit (! (in (car (car s))
                      (mget (mget :tp m)
                            (mget :nsubs (mget p s))))))
   ;; in this case fn-pdg-mssgs is just (fn-pdg-mssgs (forward-fn (cdr s)))

   :s
   
   (:claim (== (mget p s) (mget p (cdr s))))
   (:equiv (mget p s) (mget p (cdr s)))

   (:claim (== (forward-help-fn p (cdr s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p (cdr s))))
                                m)
               (forward-fn p m (cdr s)))
           :hints (("Goal" :use ((:instance prop=forward-fn-def (s (cdr
                                                                    s)))))))
   (:equiv (forward-help-fn p (cdr s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p (cdr s))))
                                m)
           (forward-fn p m (cdr s)))

   
   
   ))





   :up :r :s
   (:dv 2) :r :s :up
   (:dv 3) :r :s :up




   (:claim (== (forward-help-fn p s
                                 (mget (mget :tp m)
                                       (mget :nsubs (mget p s)))
                                 m)
                (cons (car s)
                  (forward-help-fn p (cdr s)
                                   (mget (mget :tp m)
                                         (mget :nsubs (mget p s)))
                                   m)))
           :hints (("Goal" :in-theory (enable forward-help-fn))))
   
   (:equiv (cons (car s)
                 (forward-help-fn p (cdr s)
                                  (mget (mget :tp m)
                                        (mget :nsubs (mget p s)))
                                  m))
           (forward-help-fn p s
                                 (mget (mget :tp m)
                                       (mget :nsubs (mget p s)))
                                 m))
   :s
   (:claim (== (forward-help-fn p s
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p s)))
                                m)
               (forward-fn p m s))
           :hints (("Goal" :use ((:instance prop=forward-fn-def (s (cdr
                                                                    s)))))))
   (:equiv (forward-help-fn p s
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p s)))
                                m)
           (forward-fn p m s))
   (:claim (== (mget p s) (mget p (cdr s))))
   (:equiv (mget p s) (mget p (cdr s)))

   (:claim (== (forward-help-fn p (cdr s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p (cdr s))))
                                m)
               (forward-fn p m (cdr s)))
           :hints (("Goal" :use ((:instance prop=forward-fn-def (s (cdr
                                                                    s)))))))
   (:equiv (forward-help-fn p (cdr s)
                                (mget (mget :tp m)
                                      (mget :nsubs (mget p (cdr s))))
                                m)
           (forward-fn p m (cdr s)))
   (:claim (== (forward-fn p m (cdr s))
               (cdr (forward-fn p m s)))
           :hints (("Goal" :use ((:instance prop=forward-fn-cdr)))))
   (:equiv (forward-fn p m (cdr s))
           (cdr (forward-fn p m s)))
   (:claim (== (f2b (forward-fn p m s))
               (cons (cons (car (car s))
                           (f2b-st (cdr (car s))
                                   (fn-pending-mssgs (forward-fn p m s))))
                     (f2b-help (cdr (forward-fn p m s))
                               (fn-pending-mssgs (forward-fn p m s))))))
   
   ))




   
   (:claim (== (forward-help-fn p s
                         (mget (mget :tp m)
                               (mget :nsubs (mget p s)))
                         m)
               (forward-fn p m s))
           :hints (("Goal" :use ((:instance prop=forward-fn-def (s (cdr
                                                                    s)))))))
   (:equiv (forward-help-fn p (cdr s)
                            (mget (mget :tp m)
                                  (mget :nsubs (mget p (cdr s))))
                            m)
           (forward-fn p m (cdr s)))

   
   (:dv 2) :r :s (:dv 1 2) :r


   
   :top
   

   ))
   

