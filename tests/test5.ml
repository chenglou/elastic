(let print (fun [d]
  (Printf.printf "%d\n" d)))

(let some_var (+ 1 2))

(let some_func (fun [(? a 10) b]
  (+ a b)))

(print (some_func 2))

(print (some_func (~ a 1) 2))

(let some_func2 (fun [(~ b) (? a 10)]
  (+ a b)))

(print ((some_func2 111) (~ a 111)))
