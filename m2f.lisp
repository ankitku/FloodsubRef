(in-package "ACL2S")
(include-book "mn")
(include-book "fn")

(definecd m2f-st-proj (ps :ps-mn) :ps-fn
  (ps-fn (mget :pubs ps)
         (mget :subs ps)
         (mget :nsubs ps)
         (mget :pending ps)
         (mget :seen ps)))

(definec m2f-help (s :s-mn) :s-fn
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (if (endp s)
      '()
    (cons `(,(caar s)
            . ,(m2f-st-proj (cdar s)))
          (m2f-help (cdr s)))))








(property prop=m2f-st-check (ps :ps-mn ms :lom)
  (^ (== (mget :pubs (m2f-st ps ms))
         (mget :pubs ps))
     (== (mget :subs (m2f-st ps ms))
         (mget :subs ps))
     (== (mget :nsubs (m2f-st ps ms))
         (mget :nsubs ps))
     (== (mget :pending (m2f-st ps ms))
         (app ms (mget :pending ps)))
     (== (mget :seen (m2f-st ps ms))
         (mget :seen ps)))
  :hints (("Goal" :in-theory (enable m2f-st ps-fnp ps-fnp))))


;; We now define our refinement map m2f



(definec m2f (s :s-fn) :s-fn
  (m2f-help s (fn-pending-mssgs s)))
