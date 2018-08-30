qf:(and (>= a 0) (>= b 0) (= (pow a 0) 1) (= (pow a 1) a) (= (pow 1 b) 1) (=> (and (> a 1) (> b 1)) (> (pow a b) a))  ) 
weak:(and (>= a 0) (>= b 0) (= (pow a 0) 1) (forall ((i Int))  (=> (and (> i 0) (<= i b)) (>= (pow a i) a)))  ) 
weaker:(and (>= a 0) (>= b 0) (= (pow a 0) 1) (forall ((i Int))  (=> (and (> i 0) (<= i b)) (>= (pow a i) 0)))  ) 
full:(and (>= a 0) (>= b 0) (= (pow a 0) 1) (forall ((i Int))  (=> (and (> i 0) (<= i b)) (= (pow a i) (* (pow a (- i 1)) a))))  )
uf:true
