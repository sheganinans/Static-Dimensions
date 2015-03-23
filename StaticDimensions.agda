module StaticDimensions where

  open import Data.Bool
    renaming (T to TT)
  open import Data.Nat
    renaming (_+_ to _ℕ+ℕ_; _*_ to _ℕ*ℕ_; suc to ℕsuc; pred to ℕpred)
  open import Data.Integer
    renaming (_+_ to _ℤ+ℤ_; _-_ to _ℤ-ℤ_; _*_ to _ℤ*ℤ_; suc to ℤsuc)
  open import Data.Maybe
  open import Function
  open import Algebra.Structures
  import Data.Nat.Coprimality as C
  open import Relation.Nullary.Decidable


-- The tiniest prelude.

  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

  _ℕ≡ℕ_ : ℕ → ℕ → Bool
  zero   ℕ≡ℕ zero   = true
  zero   ℕ≡ℕ ℕsuc _ = false
  ℕsuc _ ℕ≡ℕ zero   = false
  ℕsuc a ℕ≡ℕ ℕsuc b = a ℕ≡ℕ b

  _ℤ≡ℤ_ : ℤ → ℤ → Bool
  -[1+ n ]  ℤ≡ℤ -[1+ n₁ ] = n ℕ≡ℕ n₁
  (ℤ.+   _) ℤ≡ℤ -[1+ _ ]  = false
  -[1+ _ ]  ℤ≡ℤ (ℤ.+ _)   = false
  (ℤ.+   n) ℤ≡ℤ (ℤ.+ n₁)  = n ℕ≡ℕ n₁


-- Basic Exponents.

  _ℤ² : ℤ → ℤ
  z ℤ² = z ℤ*ℤ z

  _ℤ³ : ℤ → ℤ
  z ℤ³ = z ℤ*ℤ z ℤ*ℤ z

  _ℤ⁴ : ℤ → ℤ
  z ℤ⁴ = z ℤ² ℤ²


{-
  Dim is the central datastructure in this file, each physical quantity has a dimension.
  A dimension is a pair of DimT, which represent the positive and negative components of a dimension.
  You can add only like dimensions and you can multiply like and unlike dimensions.
  However that logic comes later, this is simply the definition.
  Would rather have Naturals in each component instead of Integers, but the Naturals are not closed
  under subtraction, and thus not total. So much for making illegal states unrepresentable!
-}

  record DimT : Set where
    constructor dimt
    field
      m : ℤ
      l : ℤ
      t : ℤ
      q : ℤ
      θ : ℤ
      n : ℤ
      j : ℤ

  record Dim : Set where
    constructor dim
    field
      pos : DimT
      neg : DimT


{-
  Equality of dimensions, simply makes sure that all the integers in each position are
  equal between the two dimensions.
-}

  _DT≡DT_ : DimT → DimT → Bool
  dimt m l t q θ n j DT≡DT
    dimt m₁ l₁ t₁ q₁ θ₁ n₁ j₁
      = m ℤ≡ℤ m₁
      ∧ l ℤ≡ℤ l₁
      ∧ t ℤ≡ℤ t₁
      ∧ q ℤ≡ℤ q₁
      ∧ θ ℤ≡ℤ θ₁
      ∧ n ℤ≡ℤ n₁
      ∧ j ℤ≡ℤ j₁

  _D≡D_ : Dim -> Dim -> Bool
  dim p n D≡D dim p₁ n₁ = p DT≡DT p₁ ∧ n DT≡DT n₁


{-
  Helper functions to lift functions from DimT to Dim.
-}

  liftDim1 : (DimT -> DimT) -> Dim -> Dim
  liftDim1 f (dim p n) = dim (f p) (f n)

  liftDim2 : (DimT -> DimT -> DimT) -> Dim -> Dim -> Dim
  liftDim2 f (dim p n) (dim p₁ n₁) = dim (f p p₁) (f n n₁)


{-
  Addition, subtraction, multiplication, and exponentiation of dimensions.
  Simply wrapping integer operations.
-}

  _DT+DT_ : DimT → DimT → DimT
  dimt m l t q θ n j DT+DT
    dimt m₁ l₁ t₁ q₁ θ₁ n₁ j₁
      = dimt (m ℤ+ℤ m₁)
             (l ℤ+ℤ l₁)
             (t ℤ+ℤ t₁)
             (q ℤ+ℤ q₁)
             (θ ℤ+ℤ θ₁)
             (n ℤ+ℤ n₁)
             (j ℤ+ℤ j₁)

  infixl 5 _D+D_
  _D+D_ : Dim -> Dim -> Dim
  a D+D b = liftDim2 _DT+DT_ a b

  _DT-DT_ : DimT → DimT → DimT
  dimt m l t q θ n j DT-DT
    dimt m₁ l₁ t₁ q₁ θ₁ n₁ j₁
      = dimt (m ℤ-ℤ m₁)
             (l ℤ-ℤ l₁)
             (t ℤ-ℤ t₁)
             (q ℤ-ℤ q₁)
             (θ ℤ-ℤ θ₁)
             (n ℤ-ℤ n₁)
             (j ℤ-ℤ j₁)

  _D-D_ : Dim -> Dim -> Dim
  a D-D b = liftDim2 _DT-DT_ a b

  _DT*DT_ : DimT → DimT → DimT
  dimt m l t q θ n j DT*DT
    dimt m₁ l₁ t₁ q₁ θ₁ n₁ j₁
      = dimt (m ℤ*ℤ m₁)
             (l ℤ*ℤ l₁)
             (t ℤ*ℤ t₁)
             (q ℤ*ℤ q₁)
             (θ ℤ*ℤ θ₁)
             (n ℤ*ℤ n₁)
             (j ℤ*ℤ j₁)

  _D*D_ : Dim -> Dim -> Dim
  a D*D b = liftDim2 _DT*DT_ a b

  _DT² : DimT → DimT
  dimt m l t q θ n j DT²
    = dimt (m ℤ²)
           (l ℤ²)
           (t ℤ²)
           (q ℤ²)
           (θ ℤ²)
           (n ℤ²)
           (j ℤ²)

  _D² : Dim -> Dim
  a D² = liftDim1 _DT² a

  _DT³ : DimT → DimT
  dimt m l t q θ n j DT³
    = dimt (m ℤ³)
           (l ℤ³)
           (t ℤ³)
           (q ℤ³)
           (θ ℤ³)
           (n ℤ³)
           (j ℤ³)

  _D³ : Dim -> Dim
  a D³ = liftDim1 _DT³ a

  _DT⁴ : DimT → DimT
  dimt m l t q θ n j DT⁴
    = dimt (m ℤ⁴)
           (l ℤ⁴)
           (t ℤ⁴)
           (q ℤ⁴)
           (θ ℤ⁴)
           (n ℤ⁴)
           (j ℤ⁴)

  _D⁴ : Dim -> Dim
  a D⁴ = liftDim1 _DT⁴ a


{-
  Wrappers for addition, subtraction, and multiplication of a specific component by a scalar.
-}

  _m+ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j m+ℤ z = dimt (m ℤ+ℤ z) l  t  q  θ  n  j
  _l+ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j l+ℤ z = dimt  m (l ℤ+ℤ z) t  q  θ  n  j
  _t+ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j t+ℤ z = dimt  m  l (t ℤ+ℤ z) q  θ  n  j
  _q+ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j q+ℤ z = dimt  m  l  t (q ℤ+ℤ z) θ  n  j
  _θ+ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j θ+ℤ z = dimt  m  l  t  q (θ ℤ+ℤ z) n  j
  _n+ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j n+ℤ z = dimt  m  l  t  q  θ (n ℤ+ℤ z) j
  _j+ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j j+ℤ z = dimt  m  l  t  q  θ  n (j ℤ+ℤ z)

  _m-ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j m-ℤ z = dimt (m ℤ-ℤ z) l  t  q  θ  n  j
  _l-ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j l-ℤ z = dimt  m (l ℤ-ℤ z) t  q  θ  n  j
  _t-ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j t-ℤ z = dimt  m  l (t ℤ-ℤ z) q  θ  n  j
  _q-ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j q-ℤ z = dimt  m  l  t (q ℤ-ℤ z) θ  n  j
  _θ-ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j θ-ℤ z = dimt  m  l  t  q (θ ℤ-ℤ z) n  j
  _n-ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j n-ℤ z = dimt  m  l  t  q  θ (n ℤ-ℤ z) j
  _j-ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j j-ℤ z = dimt  m  l  t  q  θ  n (j ℤ-ℤ z)

  _m*ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j m*ℤ z = dimt (m ℤ*ℤ z) l  t  q  θ  n  j
  _l*ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j l*ℤ z = dimt  m (l ℤ*ℤ z) t  q  θ  n  j
  _t*ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j t*ℤ z = dimt  m  l (t ℤ*ℤ z) q  θ  n  j
  _q*ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j q*ℤ z = dimt  m  l  t (q ℤ*ℤ z) θ  n  j
  _θ*ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j θ*ℤ z = dimt  m  l  t  q (θ ℤ*ℤ z) n  j
  _n*ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j n*ℤ z = dimt  m  l  t  q  θ (n ℤ*ℤ z) j
  _j*ℤ_ : DimT → ℤ → DimT
  dimt m l t q θ n j j*ℤ z = dimt  m  l  t  q  θ  n (j ℤ*ℤ z)


{-
  Nicer names for integer zero and one.
-}

  ℤ0 = (+ 0)
  ℤ1 = (+ 1)


{-
  Using the previously defined scalar operations to define succ and pred for pos and neg for each component.
-}

  _Mp++ : Dim → Dim
  dim p n Mp++ = dim (p m+ℤ ℤ1) n
  _Lp++ : Dim → Dim
  dim p n Lp++ = dim (p l+ℤ ℤ1) n
  _Tp++ : Dim → Dim
  dim p n Tp++ = dim (p t+ℤ ℤ1) n
  _Qp++ : Dim → Dim
  dim p n Qp++ = dim (p q+ℤ ℤ1) n
  _Θp++ : Dim → Dim
  dim p n Θp++ = dim (p θ+ℤ ℤ1) n
  _Np++ : Dim → Dim
  dim p n Np++ = dim (p n+ℤ ℤ1) n
  _Jp++ : Dim → Dim
  dim p n Jp++ = dim (p j+ℤ ℤ1) n

  _Mn++ : Dim → Dim
  dim p n Mn++ = dim p (n m+ℤ ℤ1)
  _Ln++ : Dim → Dim
  dim p n Ln++ = dim p (n l+ℤ ℤ1)
  _Tn++ : Dim → Dim
  dim p n Tn++ = dim p (n t+ℤ ℤ1)
  _Qn++ : Dim → Dim
  dim p n Qn++ = dim p (n q+ℤ ℤ1)
  _Θn++ : Dim → Dim
  dim p n Θn++ = dim p (n θ+ℤ ℤ1)
  _Nn++ : Dim → Dim
  dim p n Nn++ = dim p (n n+ℤ ℤ1)
  _Jn++ : Dim → Dim
  dim p n Jn++ = dim p (n j+ℤ ℤ1)


  _Mp-- : Dim → Dim
  dim p n Mp-- = dim (p m-ℤ ℤ1) n
  _Lp-- : Dim → Dim
  dim p n Lp-- = dim (p l-ℤ ℤ1) n
  _Tp-- : Dim → Dim
  dim p n Tp-- = dim (p t-ℤ ℤ1) n
  _Qp-- : Dim → Dim
  dim p n Qp-- = dim (p q-ℤ ℤ1) n
  _Θp-- : Dim → Dim
  dim p n Θp-- = dim (p θ-ℤ ℤ1) n
  _Np-- : Dim → Dim
  dim p n Np-- = dim (p n-ℤ ℤ1) n
  _Jp-- : Dim → Dim
  dim p n Jp-- = dim (p j-ℤ ℤ1) n

  _Mn-- : Dim → Dim
  dim p n Mn-- = dim p (n m-ℤ ℤ1)
  _Ln-- : Dim → Dim
  dim p n Ln-- = dim p (n l-ℤ ℤ1)
  _Tn-- : Dim → Dim
  dim p n Tn-- = dim p (n t-ℤ ℤ1)
  _Qn-- : Dim → Dim
  dim p n Qn-- = dim p (n q-ℤ ℤ1)
  _Θn-- : Dim → Dim
  dim p n Θn-- = dim p (n θ-ℤ ℤ1)
  _Nn-- : Dim → Dim
  dim p n Nn-- = dim p (n n-ℤ ℤ1)
  _Jn-- : Dim → Dim
  dim p n Jn-- = dim p (n j-ℤ ℤ1)


{-
  The zeroth dimension, along with an enumeration of the lower dimensions.
-}

  D0T : DimT -- m  l  t  q  θ  n  j
  D0T = dimt   ℤ0 ℤ0 ℤ0 ℤ0 ℤ0 ℤ0 ℤ0
  D0 : Dim
  D0 = dim D0T D0T

  M  = D0 Mp++
  L  = D0 Lp++
  T  = D0 Tp++
  Q  = D0 Qp++
  Θ  = D0 Θp++
  N  = D0 Np++
  J  = D0 Jp++

  M⁻¹ = D0 Mn++
  L⁻¹ = D0 Ln++
  T⁻¹ = D0 Tn++
  Q⁻¹ = D0 Qn++
  Θ⁻¹ = D0 Θn++
  N⁻¹ = D0 Nn++
  J⁻¹ = D0 Jn++

  M² = M Mp++
  L² = L Lp++
  T² = T Tp++
  Q² = Q Qp++
  Θ² = Θ Θp++
  N² = N Np++
  J² = J Jp++

  M⁻² = M⁻¹ Mn++
  L⁻² = L⁻¹ Ln++
  T⁻² = T⁻¹ Tn++
  Q⁻² = Q⁻¹ Qn++
  Θ⁻² = Θ⁻¹ Θn++
  N⁻² = N⁻¹ Nn++
  J⁻² = J⁻¹ Jn++

  M³ = M² Mp++
  L³ = L² Lp++
  T³ = T² Tp++
  Q³ = Q² Qp++
  Θ³ = Θ² Θp++
  N³ = N² Np++
  J³ = J² Jp++

  M⁻³ = M⁻² Mn++
  L⁻³ = L⁻² Ln++
  T⁻³ = T⁻² Tn++
  Q⁻³ = Q⁻² Qn++
  Θ⁻³ = Θ⁻² Θn++
  N⁻³ = N⁻² Nn++
  J⁻³ = J⁻² Jn++

  M⁴ = M³ Mp++
  L⁴ = L³ Lp++
  T⁴ = T³ Tp++
  Q⁴ = Q³ Qp++
  Θ⁴ = Θ³ Θp++
  N⁴ = N³ Np++
  J⁴ = J³ Jp++

  M⁻⁴ = M⁻³ Mn++
  L⁻⁴ = L⁻³ Ln++
  T⁻⁴ = T⁻³ Tn++
  Q⁻⁴ = Q⁻³ Qn++
  Θ⁻⁴ = Θ⁻³ Θn++
  N⁻⁴ = N⁻³ Nn++
  J⁻⁴ = J⁻³ Jn++


{-
  Nicer wrapper for D+D, only used for the next section to avoid noise in the definitions.
-}

  infixl 5 _⊚_
  _⊚_ : Dim → Dim → Dim
  a ⊚ b = a D+D b


{-
  Names of commonly used dimensions and their definitions.
-}

  IntegerHarmonic = D0
  Radius          = D0
  Radian          = D0
  Setrian         = D0

  Kilogram = M
  Meter    = L
  Second   = T
  Ampere   = Q
  Kelvin   = Θ
  Mol      = N
  Candela  = J

  Hertz    =           T⁻¹
  Velocity =     L   ⊚ T⁻¹
  Newton   = M ⊚ L   ⊚ T⁻²
  Pascal   = M ⊚ L⁻¹ ⊚ T⁻²
  Joule    = M ⊚ L²  ⊚ T⁻²
  Watt     = M ⊚ L²  ⊚ T⁻³

  Coulomb      =       Q ⊚ T
  CoulombMeter = Coulomb ⊚ L

  Volt   = M   ⊚ L²  ⊚ T⁻³ ⊚ Q⁻¹
  Farad  = M⁻¹ ⊚ L⁻² ⊚ T⁴  ⊚ Q²
  Ohm    = M   ⊚ L²  ⊚ T⁻³ ⊚ Q⁻²
  Siemen = M⁻¹ ⊚ L⁻² ⊚ T³  ⊚ Q²
  Weber  = M   ⊚ L²  ⊚ T⁻² ⊚ Q⁻¹
  Tesla  = M   ⊚       T⁻² ⊚ Q⁻¹
  Henry  = M   ⊚ L²  ⊚ T⁻² ⊚ Q⁻²

  Celcius = Kelvin

  Lumen     =                J
  Lux       = L⁻²          ⊚ J
  Bacquerel =      T⁻¹
  Gray      = L² ⊚ T⁻²
  Katal     =      T⁻¹ ⊚ N

  SpringConstant  = Newton


{-
  The second most important (and only other) datastructure.
  Every quanitity has a scalar value and a positive dimension and a negative dimension.
-}

  record Quantity : Set where
    constructor quant
    field
      dims : Dim
      quantity  : ℤ


{-
  Equality, addition, multiplication, and exponentiation of quantities.
  Addition and multiplication are interesting in their own rights and
  their peculiarities are detailed in their own comments.
-}

  _Q≡Q_ : Quantity → Quantity → Bool
  quant d q Q≡Q quant d₁ q₁ = d D≡D d₁ ∧ q ℤ≡ℤ q₁


{-
  Addition may not succeed because one may attempt to add unlike quantities together.
  To illustate this, there is no proper physical way to add a meter to a meter², or
  adding a kilogram to a newton. So either of these attempts would result in a Nothing.
  You can multiply quantities with unlike dimensions and the details of which are rather simple.
  This could be improved by either upgrading the Maybe to an Either or by tracking
  the dimension in the type and rejecting such additions at compile-time.
  However this is not the goal of this file and the path of least resistance is used.
-}

  _Q+Q_ : Quantity → Quantity → Maybe Quantity
  quant d q Q+Q quant d₁ q₁
    = if d D≡D d₁
      then just (quant d (q ℤ+ℤ q₁))
      else nothing


{-
  Multiplying two quanitities is simply multiplying the two scalar values and adding together
  the two dimensions componentwise.
-}

  _Q*Q_ : Quantity → Quantity → Quantity
  quant d q Q*Q quant d₁ q₁
      = quant (d D+D d₁) (q ℤ*ℤ q₁)

  _Q² : Quantity → Quantity
  quant d q Q² = quant (d D+D d) (q ℤ²)

  _Q³ : Quantity → Quantity
  quant d q Q³ = quant (d D+D d D+D d) (q ℤ³)

  _Q⁴ : Quantity → Quantity
  quant d q Q⁴ = quant (d D+D d D+D d D+D d) (q ℤ⁴)

  _Q+ℤ_ : Quantity → ℤ → Quantity
  quant d q Q+ℤ z = quant d (q ℤ+ℤ z)

  _Q-ℤ_ : Quantity → ℤ → Quantity
  quant d q Q-ℤ z = quant d (q ℤ-ℤ z)

  _Q*ℤ_ : Quantity → ℤ → Quantity
  quant d q Q*ℤ z = quant d (q ℤ*ℤ z)

  -Q_ : Quantity → Quantity
  -Q q = q Q*ℤ -[1+ 0 ]

  _Q*10 : Quantity → Quantity
  q Q*10 = q Q*ℤ (+ 10)

  _Q*-10 : Quantity → Quantity
  q Q*-10 = q Q*ℤ -[1+ 9 ]


{-
  Takes a Quantity and simply projects out the Dimension.
  Used in the final proof.
-}

  Q→D_ : Quantity → Dim
  Q→D (quant d q) = d


{-
  Enumerating the postfix constructors for the Quantitys to make them more English-like.
  Decided to ignore the standard pluralization rules to make the names more consistent.
-}

  _kilograms : ℤ → Quantity
  k kilograms = quant M k

  _meters : ℤ → Quantity
  m meters = quant L m

  _seconds : ℤ → Quantity
  s seconds = quant T s

  _amperes : ℤ → Quantity
  a amperes = quant Q a

  _mols : ℤ → Quantity
  m mols = quant N m

  _candelas : ℤ → Quantity
  c candelas = quant J c

  _integerHarmonics : ℤ → Quantity
  i integerHarmonics = quant D0 i

  _radiuss : ℤ → Quantity
  r radiuss = quant D0 r

  _radians : ℤ → Quantity
  r radians = quant D0 r

  _sterians : ℤ → Quantity
  s sterians = quant D0 s

  _hertzs : ℤ → Quantity
  h hertzs = quant Hertz h

  _velocitys : ℤ → Quantity
  v velocitys = quant Velocity v

  _newtons : ℤ → Quantity
  n newtons = quant Newton n

  _pascals : ℤ → Quantity
  p pascals = quant Pascal p

  _joules : ℤ → Quantity
  j joules = quant Joule j

  _watts : ℤ → Quantity
  w watts = quant Watt w

  _coulombs : ℤ → Quantity
  c coulombs = quant Coulomb c

  _coublombMeters : ℤ → Quantity
  c coublombMeters = quant CoulombMeter c

  _volts : ℤ → Quantity
  v volts = quant Volt v

  _farads : ℤ → Quantity
  f farads = quant Farad f

  _siemens : ℤ → Quantity
  s siemens = quant Siemen s

  _webers : ℤ → Quantity
  w webers = quant Weber w

  _teslas : ℤ → Quantity
  t teslas = quant Tesla t

  _henrys : ℤ → Quantity
  h henrys = quant Henry h

  _celciuss : ℤ → Quantity
  c celciuss = quant Celcius c

  _lumens : ℤ → Quantity
  l lumens = quant Lumen l

  _luxs : ℤ → Quantity
  l luxs = quant Lux l

  _bacquerels : ℤ → Quantity
  b bacquerels = quant Bacquerel b

  _grays : ℤ → Quantity
  g grays = quant Gray g

  _katals : ℤ → Quantity
  k katals = quant Katal k

  _springConstants : ℤ → Quantity
  s springConstants = quant SpringConstant s


{-
  The definition of e = mc².
  It is defined as a function that takes two arguments, m and c.
  m is a mass, measured kilograms, c is a velocity, measured in meters per second.
  e is defined as m kilograms times the velocity c squared.
-}

  e=_∙_² : ℤ → ℤ → Quantity
  e= m ∙ c ² = m kilograms Q*Q (c velocitys Q²)


{-
  This is the proof, it is actually more general than stated, since it is valid for all speeds of light.
  In english the proposition reads: Projecting the dimension of e=mc², it is equal to Joule for all m and c.
  To prove the proposition, the trivial proof is used, ie: reflexivity.
  Which simply states that the RHS and the LHS are indeed equal by the law of identity.
  Thank you Curry–Howard isomorphism!
-}

--                                        LHS                            RHS
--                                        ----------------------------   ----
  e=mc²isMeasuredInJoules : ∀ {m c : ℤ} → ((Q→D e= m ∙ c ²) D≡D Joule) ≡ true
  e=mc²isMeasuredInJoules = refl -- QED. Simply evoking reflexivity.
