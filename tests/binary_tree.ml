(type (binaryTree 'a)
  (| (Empty)
     (Leaf <'a (binaryTree 'a) (binaryTree 'a)>)))

(letrec insert (fun [node t]
  (match t
    (Empty) (Leaf <node (Empty) (Empty)>)
    (Leaf <x y z>) (if (< node x)
                     (Leaf <x (insert node y) z>)
                     (Leaf <x y (insert node z)>)))))

(letrec findMin (fun [t]
  (match t
    (Empty) (None)
    (Leaf <x (Empty) _>) (Some x)
    (Leaf <x y _>) (findMin y))))

(letrec findMax (fun [t]
  (match t
    (Empty) (None)
    (Leaf <x _ (Empty)>) (Some x)
    (Leaf <x _ z>) (findMax z))))

(letrec delete (fun [node t]
  (match t
    (Empty) (Empty)
    (Leaf <x y z>) (if (= node x)
                     (match (findMin z)
                       (None) y
                       (Some min) (Leaf <min y (delete min z)>))
                     (if (< node x)
                       (Leaf <x (delete node y) z>)
                       (Leaf <x y (delete node z)>))))))

(letrec count (fun [t]
  (match t
    (Empty) 0
    (Leaf <x y z>) (+ 1 (+ (count y) (count z))))))

(let a (Leaf <5 (Leaf <3 (Empty) (Empty)>)
              (Leaf <7 (Empty) (Empty)>)>))

(let b (Leaf <5 (Leaf <3 (Empty) (Leaf <4 (Empty) (Empty)>)>)
              (Leaf <7 (Empty) (Empty)>)>))

(let repeat (Leaf <5 (Leaf <3 (Empty) (Empty)>)
                   (Leaf <7 (Leaf <5 (Empty) (Empty)>) (Empty)>)>))

(let single (Leaf <1 (Empty) (Empty)>))

(assert (= (insert 4 a) b))

(assert (= (insert 5 a) repeat))

(assert (= (insert 1 (Empty)) single))

(assert (= (findMin single) (Some 1)))

(assert (= (findMin a) (Some 3)))

(assert (= (findMin (insert 1 a)) (Some 1)))

(assert (= (findMax single) (Some 1)))

(assert (= (findMax a) (Some 7)))

(assert (= (findMax (insert 9 a)) (Some 9)))

(assert (= (delete 4 a) a))

(assert
   (= (delete 5 a) (Leaf <7 (Leaf <3 (Empty) (Empty)>) (Empty)>)))

(assert
   (= (delete 3 a) (Leaf <5 (Empty) (Leaf <7 (Empty) (Empty)>)>)))

(assert
   (= (delete 7 a) (Leaf <5 (Leaf <3 (Empty) (Empty)>) (Empty)>)))

(assert (= (delete 4 b) a))

(assert (= (delete 5 repeat) a))

(assert (= (delete 5 (delete 7 a)) (Leaf <3 (Empty) (Empty)>)))

(assert (= (count a) 3))

(assert (= (count b) 4))

(assert (= (count single) 1))

(assert
   (= (delete 7 a) (Leaf <5 (Leaf <3 (Empty) (Empty)>) (Empty)>)))

(assert (= (delete 4 b) a))

(assert (= (delete 5 repeat) a))

(assert (= (delete 5 (delete 7 a)) (Leaf <3 (Empty) (Empty)>)))

(assert (= (count a) 3))

(assert (= (count b) 4))

(assert (= (count single) 1))
