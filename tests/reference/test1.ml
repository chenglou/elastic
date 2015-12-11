(let print (fun [d]
  (Printf.printf "%d\n" d)))

(let f (+ 2 (+ 5 (+ 6 10))))

(print (* 9 (* 9 9)))

(let [x 10
       y (+ x 11)
       z (&& (> x 12) (= y 100))]
  (print (+ x y)))

((fun [a f] (let [b (f a)] (print (b 10)))) 11 (fun [x y] (+ x y)))

(let [f (fun [x] (* 2 x))] (f 10))

(let f (fun [a b c] (+ a (+ b c))))

(f 1 2 3)

(+ 1 2)

(let bla (fun [a] (+ a a)))

(let [x (bla 10)] (+ x 11))

(let [a 10
       b 11
       c 12]
  (+ a (+ b c)))

(let abc [1 2 3 4])

(print (Array.length abc))

(Array.map print abc)

(if false
   (print_string "heyyy") (print 10))