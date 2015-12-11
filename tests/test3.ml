(let print (fun [d] (Printf.printf "%d\n" d)))

(let bla (fun [(x : int)] x))

(let [a (bla 10)] a)

(let [(abc : int) (bla 10)]
  abc)

(type str_alias string)

(let (string_identity : (-> str_alias str_alias)) (fun [x]
  x))

(string_identity "string")

(let [test ((fun [x] 10) : (-> int int))]
  (test 11))

(type int_to_int (-> int int))

(print (let [(test : int_to_int) (fun [x] 10)] (test 11)))

(match (`Int 10)
   (`Int x) (+ x 11)
   _ 0)

(type (option 'a)
   (| (None)
      (Some 'a)))

(let [a (Some 10)
       b (None)]
  (match a
    (Some x) x
    (None) 0))

(type (leaf 'a)
   (| (Left int)
      (Right int)))

(let something (fun [leaf]
  (match leaf
    (Left a) a
    (Right a) a)))

(print (something (Left 10)))
