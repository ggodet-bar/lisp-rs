(def fib (N)
    (if (<= N 1) N (+ (fib (- N 1)) (fib (- N 2)))))
(fib 16)