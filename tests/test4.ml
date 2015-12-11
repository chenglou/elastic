(let print (fun [d]
  (Printf.printf "%d\n" d)))

(type vec2d {a int b int})

(let some_map {a 10 b 11})

(print (match some_map
          {a b} (+ a b)))

(type some_tuple <int int int>)

(let tuple <1 2 3>)

(print (match tuple
          <a b c> (+ a (+ b c))))

(type vec3d {x int y int z int})

(let some_map2 (update some_map {a 99 b 100}))

(match some_map2
   {a b} (print a))

(print
 (match '(1 2 3 4 5 6 7 8)
   '(a b) (+ a b)
   '(a b) (+ a
             (+ b (List.fold_right (fun [acc x] (+ acc x)) rest 0)))))

(let (some_func : (-> int int int)) (fun [x y]
  (+ x y)))

(if true
   1 (if false
       2 3))
