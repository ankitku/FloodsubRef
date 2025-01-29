(in-package "ACL2S")
(include-book "f2b-ref2")
(include-book "std/util/define-sk" :dir :system)

(acl2::define-sk web3-exist ((s borfp)
                             (u borfp)
                             (w borfp))
  (exists ((v))
    (=> (^ (rel-B s w)
           (rel-> s u)      
           
           (=> (s-fnp s)
               (f2b-refinement-conditions s
                                          (br-mssg-witness (f2b s) (f2b u))
                                          (car (bn-join-witness (f2b u)
                                                                (f2b s)))))
           (=> (^ (s-bnp s) (s-fnp w))
               (f2b-refinement-conditions w
                                          (br-mssg-witness (f2b w) u)
                                          (car (bn-join-witness u (f2b w)))))
           (=> (^ (s-fnp s) (s-fnp w))
               (f2b-refinement-conditions w
                                          (br-mssg-witness (f2b s) (f2b u))
                                          (car (bn-join-witness (f2b u)
                                                                (f2b s))))))
        (v (^ (rel-> w v)
              (rel-B u v))
           (^ (rel-> w v)
              (rel-B s v)
              (< (erankl v u)
                 (erankl w u)))))))
