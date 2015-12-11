(let print (fun [d]
  (Printf.printf "%d\n" d)))

(let a '(1 2 3 4))

(List.map (fun [x] (print (+ x 1))) a)

(let b [1 2 3 4])

(Array.map (fun [x] (print (+ x 1))) b)

(let f (fun [x]
  (match x
    true (print 10)
    false (print 9999999))))

(f false)

(let f2 (fun [x]
  (match x
    '(a b) (print a)
    '(a) (print a)
    _ (print 111111))))

(f2 '(898989 2 3 4 5))

(f2 '(78787878))

(let [a 10
       (b : int) 10
       c 12] (+ a (+ b c)))

(let abc (fun [x] (print x)))

(type a int)

(let abcd (fun [(a : string) (b : a)]
  a))

(type something {a int})
