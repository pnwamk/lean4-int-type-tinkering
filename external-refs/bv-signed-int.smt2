(simplify ((_ int2bv 32) -2147483648))


(simplify
  (bvsdiv ((_ int2bv 32) -2147483648)
          ((_ int2bv 32) -1)))

(simplify
  (bvsmod ((_ int2bv 32) -2147483648)
          ((_ int2bv 32) -1)))

(simplify ((_ int2bv 64) -9223372036854775808))


(simplify
  (bvsdiv ((_ int2bv 64) -9223372036854775808)
          ((_ int2bv 64) -1)))

(simplify
  (bvsmod ((_ int2bv 64) -9223372036854775808)
          ((_ int2bv 64) -1)))
