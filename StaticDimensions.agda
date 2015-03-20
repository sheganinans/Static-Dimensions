module StaticDimensions where

  open import Data.Bool
    renaming (T to TT)
  open import Data.Nat
    renaming (_+_ to _ℕ+ℕ_; _*_ to _ℕ*ℕ_; suc to ℕsuc)
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
  z ℤ⁴ = z ℤ*ℤ z ℤ*ℤ z ℤ*ℤ z


{-
  Dim is the central datastructure in this file, each physical quantity has a dimension.
  Quantities can also be dimensionless by having zeroes in all seven positions.
  You can add only like dimensions and you can multiply like and unlike dimensions.
  However that logic comes later, this is simply the definition.
-}

  record Dim : Set where
    constructor dim
    field
      m : ℤ
      l : ℤ
      t : ℤ
      q : ℤ
      θ : ℤ
      n : ℤ
      j : ℤ


{-
  Equality of dimensions, simply makes sure that all the integers in each position are
  equal between the two dimensions.
-}

  _D≡D_ : Dim → Dim → Bool
  dim m l t q θ n j D≡D
    dim m₁ l₁ t₁ q₁ θ₁ n₁ j₁
      = m ℤ≡ℤ m₁
      ∧ l ℤ≡ℤ l₁
      ∧ t ℤ≡ℤ t₁
      ∧ q ℤ≡ℤ q₁
      ∧ θ ℤ≡ℤ θ₁
      ∧ n ℤ≡ℤ n₁
      ∧ j ℤ≡ℤ j₁


{-
  Addition, subtraction, multiplication, and exponentiation of dimensions. Simply wrapping integer operations.
-}

  _D+D_ : Dim → Dim → Dim
  dim m l t q θ n j D+D
    dim m₁ l₁ t₁ q₁ θ₁ n₁ j₁
      = dim (m ℤ+ℤ m₁)
            (l ℤ+ℤ l₁)
            (t ℤ+ℤ t₁)
            (q ℤ+ℤ q₁)
            (θ ℤ+ℤ θ₁)
            (n ℤ+ℤ n₁)
            (j ℤ+ℤ j₁)

  _D-D_ : Dim → Dim → Dim
  dim m l t q θ n j D-D
    dim m₁ l₁ t₁ q₁ θ₁ n₁ j₁
      = dim (m ℤ-ℤ m₁)
            (l ℤ-ℤ l₁)
            (t ℤ-ℤ t₁)
            (q ℤ-ℤ q₁)
            (θ ℤ-ℤ θ₁)
            (n ℤ-ℤ n₁)
            (j ℤ-ℤ j₁)

  _D*D_ : Dim → Dim → Dim
  dim m l t q θ n j D*D
    dim m₁ l₁ t₁ q₁ θ₁ n₁ j₁
      = dim (m ℤ*ℤ m₁)
            (l ℤ*ℤ l₁)
            (t ℤ*ℤ t₁)
            (q ℤ*ℤ q₁)
            (θ ℤ*ℤ θ₁)
            (n ℤ*ℤ n₁)
            (j ℤ*ℤ j₁)

  _D² : Dim → Dim
  dim m l t q θ n j D²
    = dim (m ℤ²)
          (l ℤ²)
          (t ℤ²)
          (q ℤ²)
          (θ ℤ²)
          (n ℤ²)
          (j ℤ²)

  _D³ : Dim → Dim
  dim m l t q θ n j D³
    = dim (m ℤ³)
          (l ℤ³)
          (t ℤ³)
          (q ℤ³)
          (θ ℤ³)
          (n ℤ³)
          (j ℤ³)

  _D⁴ : Dim → Dim
  dim m l t q θ n j D⁴
    = dim (m ℤ⁴)
          (l ℤ⁴)
          (t ℤ⁴)
          (q ℤ⁴)
          (θ ℤ⁴)
          (n ℤ⁴)
          (j ℤ⁴)


{-
  Wrappers for addition, subtraction, and multiplication of a specific component by a scalar.
-}

  _m+ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j m+ℤ z = dim (m ℤ+ℤ z) l  t  q  θ  n  j
  _l+ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j l+ℤ z = dim  m (l ℤ+ℤ z) t  q  θ  n  j
  _t+ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j t+ℤ z = dim  m  l (t ℤ+ℤ z) q  θ  n  j
  _q+ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j q+ℤ z = dim  m  l  t (q ℤ+ℤ z) θ  n  j
  _θ+ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j θ+ℤ z = dim  m  l  t  q (θ ℤ+ℤ z) n  j
  _n+ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j n+ℤ z = dim  m  l  t  q  θ (n ℤ+ℤ z) j
  _j+ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j j+ℤ z = dim  m  l  t  q  θ  n (j ℤ+ℤ z)

  _m-ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j m-ℤ z = dim (m ℤ-ℤ z) l  t  q  θ  n  j
  _l-ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j l-ℤ z = dim  m (l ℤ-ℤ z) t  q  θ  n  j
  _t-ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j t-ℤ z = dim  m  l (t ℤ-ℤ z) q  θ  n  j
  _q-ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j q-ℤ z = dim  m  l  t (q ℤ-ℤ z) θ  n  j
  _θ-ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j θ-ℤ z = dim  m  l  t  q (θ ℤ-ℤ z) n  j
  _n-ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j n-ℤ z = dim  m  l  t  q  θ (n ℤ-ℤ z) j
  _j-ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j j-ℤ z = dim  m  l  t  q  θ  n (j ℤ-ℤ z)

  _m*ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j m*ℤ z = dim (m ℤ*ℤ z) l  t  q  θ  n  j
  _l*ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j l*ℤ z = dim  m (l ℤ*ℤ z) t  q  θ  n  j
  _t*ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j t*ℤ z = dim  m  l (t ℤ*ℤ z) q  θ  n  j
  _q*ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j q*ℤ z = dim  m  l  t (q ℤ*ℤ z) θ  n  j
  _θ*ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j θ*ℤ z = dim  m  l  t  q (θ ℤ*ℤ z) n  j
  _n*ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j n*ℤ z = dim  m  l  t  q  θ (n ℤ*ℤ z) j
  _j*ℤ_ : Dim → ℤ → Dim
  dim m l t q θ n j j*ℤ z = dim  m  l  t  q  θ  n (j ℤ*ℤ z)


{-
  Nicer names for integer zero and one.
-}

  ℤ0 = (+ 0)
  ℤ1 = (+ 1)


{-
  Using the previously defined scalar operations to define succ and pred for each component.
-}

  _M++ : Dim → Dim
  d M++ = d m+ℤ ℤ1
  _L++ : Dim → Dim
  d L++ = d l+ℤ ℤ1
  _T++ : Dim → Dim
  d T++ = d t+ℤ ℤ1
  _Q++ : Dim → Dim
  d Q++ = d q+ℤ ℤ1
  _Θ++ : Dim → Dim
  d Θ++ = d θ+ℤ ℤ1
  _N++ : Dim → Dim
  d N++ = d n+ℤ ℤ1
  _J++ : Dim → Dim
  d J++ = d j+ℤ ℤ1

  _M-- : Dim → Dim
  d M-- = d m-ℤ ℤ1
  _L-- : Dim → Dim
  d L-- = d l-ℤ ℤ1
  _T-- : Dim → Dim
  d T-- = d t-ℤ ℤ1
  _Q-- : Dim → Dim
  d Q-- = d q-ℤ ℤ1
  _Θ-- : Dim → Dim
  d Θ-- = d θ-ℤ ℤ1
  _N-- : Dim → Dim
  d N-- = d n-ℤ ℤ1
  _J-- : Dim → Dim
  d J-- = d j-ℤ ℤ1


{-
  The zeroth dimension, along with an enumeration of the lower dimensions.
-}

  D0 : Dim -- m  l  t  q  θ  n  j
  D0 = dim   ℤ0 ℤ0 ℤ0 ℤ0 ℤ0 ℤ0 ℤ0
  M  = D0 M++
  L  = D0 L++
  T  = D0 T++
  Q  = D0 Q++
  Θ  = D0 Θ++
  N  = D0 N++
  J  = D0 J++

  M⁻¹ = D0 M--
  L⁻¹ = D0 L--
  T⁻¹ = D0 T--
  Q⁻¹ = D0 Q--
  Θ⁻¹ = D0 Θ--
  N⁻¹ = D0 N--
  J⁻¹ = D0 J--

  M² = M M++
  L² = L L++
  T² = T T++
  Q² = Q Q++
  Θ² = Θ Θ++
  N² = N N++
  J² = J J++

  M⁻² = M⁻¹ M--
  L⁻² = L⁻¹ L--
  T⁻² = T⁻¹ T--
  Q⁻² = Q⁻¹ Q--
  Θ⁻² = Θ⁻¹ Θ--
  N⁻² = N⁻¹ N--
  J⁻² = J⁻¹ J--

  M³ = M² M++
  L³ = L² L++
  T³ = T² T++
  Q³ = Q² Q++
  Θ³ = Θ² Θ++
  N³ = N² N++
  J³ = J² J++

  M⁻³ = M⁻² M--
  L⁻³ = L⁻² L--
  T⁻³ = T⁻² T--
  Q⁻³ = Q⁻² Q--
  Θ⁻³ = Θ⁻² Θ--
  N⁻³ = N⁻² N--
  J⁻³ = J⁻² J--


{-
  Nicer wrapper for D+D, only used for the next section to avoid noise in the definitions.
-}

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

  Hertz    =             T⁻¹
  Velocity =      L    ⊚ T⁻¹
  Newton   = (M ⊚ L)   ⊚ T⁻²
  Pascal   = (M ⊚ L⁻¹) ⊚ T⁻²
  Joule    = (M ⊚  L²) ⊚ T⁻²
  Watt     = (M ⊚  L²) ⊚ T⁻³

  Coulomb      =       Q ⊚ T
  CoulombMeter = Coulomb ⊚ L

  Volt   = (M   ⊚  L²) ⊚   (T⁻³ ⊚ Q⁻¹)
  Farad  = (M⁻¹ ⊚ L⁻²) ⊚ (T² D² ⊚  Q²)
  Ohm    = (M   ⊚  L²) ⊚   (T⁻³ ⊚ Q⁻²)
  Siemen = (M⁻¹ ⊚ L⁻²) ⊚    (T³ ⊚  Q²)
  Weber  = (M   ⊚  L²) ⊚   (T⁻² ⊚ Q⁻¹)
  Tesla  = (M   ⊚ T⁻²)          ⊚ Q⁻¹
  Henry  = (M   ⊚  L²) ⊚   (T⁻² ⊚ Q⁻²)

  Celcius = Kelvin

  Lumen     =                J
  Lux       = L⁻²          ⊚ J
  Bacquerel =      T⁻¹
  Gray      = L² ⊚ T⁻²
  Katal     =      T⁻¹ ⊚ N

  SpringConstant  = Newton


{-
  The second most important (and only other) datastructure.
  Every quanitity has a scalar value and a dimension.
-}

  record Quantity : Set where
    constructor quant
    field
      dimension : Dim
      quantity  : ℤ


{-
  Equality, addition, multiplication, and exponentiation of quantities.
  Addition and multiplication are interesting in their own rights and
  are their peculiarities are detailed in their own comments.
-}

  _Q≡Q_ : Quantity → Quantity → Bool
  quant d q Q≡Q quant d₁ q₁ = d D≡D d₁ ∧ q ℤ≡ℤ q₁


{-
  Addition may not succeed because one may attempt to add unlike quantities together.
  To illustate this, their is no proper physical way to add a meter to a meter², or
  adding a kilogram to a newton. So either of these attempts would result in a Nothing.
  You can multiply quantities with unlike dimensions and the details of which are rather simple.
  This could be improved by either upgrading the Maybe to an Either or by tracking
  the dimension in the type and rejecting such additions at compile-time.
  However this is not the goal of this project and the path of least resistance is used.
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
  quant d q Q³ = quant ((d D+D d) D+D d) (q ℤ³)

  _Q⁴ : Quantity → Quantity
  quant d q Q⁴ = quant (((d D+D d) D+D d) D+D d) (q ℤ⁴)

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

  Q→D : Quantity → Dim
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

  e=mc²isMeasuredInJoules : ∀ {m c : ℤ} → ((Q→D e= m ∙ c ²) D≡D Joule) ≡ true
  e=mc²isMeasuredInJoules = refl -- QED. Simply evoking reflexivity.
