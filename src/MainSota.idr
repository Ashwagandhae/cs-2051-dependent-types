module MainSota
import Data.Vect
import Data.Nat


data Sorted : (xs : Vect n Nat) -> Type where
  SortedZero :
    Sorted Nil
  SortedOne  :
    (x:Nat) ->
    Sorted (x::Nil)
  SortedMany :
    (x : Nat) -> (y : Nat) -> (ys : Vect n Nat) ->
    (LTE x y) -> Sorted (y :: ys) ->
    Sorted (x :: (y :: ys))

data Elem : a -> Vect n a -> Type where
  Here  : Elem x (x :: xs)
  There : Elem x xs -> Elem x (y :: xs)


sortedImpliesSortedSmaller : (x: Nat) -> (xs : Vect n Nat) -> (Sorted (x::xs)) -> Sorted xs
sortedImpliesSortedSmaller x [] _ = SortedZero
sortedImpliesSortedSmaller x (y::ys) (SortedMany x y ys _ sor) = sor

data Permutation : Vect n Nat -> Vect n Nat -> Type where
    PermutationZero: Permutation [] []
    PermutationGrow: (as, bs: Vect n Nat) -> (x : Nat) ->
      Permutation as bs -> Permutation (x::as) (x::bs)
    PermutationSwap: (as, bs : Vect n Nat) -> (a, b : Nat) -> Permutation as bs ->
      Permutation (a::(b::as)) (b::(a::bs))
    PermutationTrans : (as, bs, cs : Vect n Nat) ->
      Permutation as bs -> Permutation bs cs -> Permutation as cs


permutationId : (xs : Vect n Nat) -> Permutation xs xs
permutationId [] = PermutationZero
permutationId (x::xs) = PermutationGrow xs xs x (permutationId xs)


permutationRev : (xs, ys: Vect n Nat) -> Permutation xs ys -> Permutation ys xs
permutationRev [] [] (PermutationZero) = PermutationZero
permutationRev (x::as) (x::bs) (PermutationGrow as bs x p) = (PermutationGrow bs as x (permutationRev as bs p))
permutationRev (a::(b::as)) (b::(a::bs)) (PermutationSwap as bs a b p) = PermutationSwap bs as b a (permutationRev as bs p)
permutationRev as cs (PermutationTrans as bs cs perm1 perm2) = PermutationTrans cs bs as (permutationRev bs cs perm2) (permutationRev as bs perm1)


-- theorem7: (as, bs, cs: Vect n Nat) -> (a, b, u : Nat) -> Permutation (u::as) (b::bs) -> Permutation bs cs -> Permutation (a::(u::as)) (b::(a::cs))
-- theorem7 [] [] [] a b b (PermutationGrow [] [] b PermutationZero) pbc = PermutationSwap [] [] a b pbc
-- theorem7 (ae::as) (u::bs) (ce::cs) a ae u (PermutationSwap as bs u ae pab) pbc = ?hmmm


-- permutationTrans : (as, bs, cs : Vect n Nat) -> Permutation as bs -> Permutation bs cs -> Permutation as cs
-- permutationTrans [] [] [] PermutationZero PermutationZero = PermutationZero
-- permutationTrans (a::(b::as)) (b::(a::bs)) (a::(b::cs)) (PermutationSwap as bs a b pab) (PermutationSwap bs cs b a pbc) = ?what
-- permutationTrans (x::as) (x::bs) (x::cs) (PermutationGrow as bs x pab) (PermutationGrow bs cs x pbc) =
--   PermutationGrow as cs x (permutationTrans as bs cs pab pbc)
-- permutationTrans (a::(u::as)) (a::(b::bs)) (b::(a::cs)) (PermutationGrow (u::as) (b::bs) a pab) (PermutationSwap bs cs a b pbc) =
--   let
--     -- Permutation bs cs
--     -- Permutation b::bs u::as
--     -- by grow: Perm a::bs a::cs, Perm u::bs u::cs, Perm b::bs b::cs
--     -- by trans Perm u::as b::cs
--     --
--     skibidi: Permutation (a::(u::as)) (b::(a::cs)) = ?hmm
--   in
--   skibidi


theorem3: (as, cs : Vect n Nat) -> (a : Nat) -> Permutation as cs -> Elem a as -> Elem a cs
theorem3 (a::(b::xs)) (b::(a::ys)) c (PermutationSwap xs ys a b p) elem = case elem of
  Here => There (Here)
  There (Here) => Here
  There (There pos) => There (There (theorem3 xs ys c p pos))
theorem3 (x::xs) (x::ys) l (PermutationGrow xs ys x p1) elem = case elem of
  Here => Here
  There elem => There (theorem3 xs ys l p1 elem)
theorem3 as cs a (PermutationTrans as bs cs p1 p2) aElemAs = let
  aElemBs : (Elem a bs) = theorem3 as bs a p1 aElemAs
  in theorem3 bs cs a p2 aElemBs

theorem2: (Permutation (x::xs) (y::ys)) -> Either (y = x) (Elem y xs)
theorem2 (PermutationSwap xs ys a b p) = Right (Here)
theorem2 (PermutationGrow as bs x p1) = Left Refl
theorem2 (PermutationTrans (a::as) (b::bs) (c::cs) perm1 perm2) = let
  cInBs : Elem c (b::bs) = theorem3 (c::cs) (b::bs) c (permutationRev (b::bs) (c::cs) perm2) Here
  cInAs : Elem c (a::as) = theorem3 (b::bs) (a::as) c (permutationRev (a::as) (b::bs) perm1) cInBs
  in case cInAs of
    Here => Left Refl
    There x => Right x


theorem4: (x, y : Nat) -> (xs : Vect n Nat) -> (Sorted (x::xs)) -> (Elem y xs) -> (LTE x y)
theorem4 x y (y::xs) (SortedMany x y xs prfLte sor) Here = prfLte
theorem4 x y (f::xs) (SortedMany x f xs prfLte sor) (There n) = let
  fLteY : LTE f y = theorem4 f y xs sor n
  xLteF : LTE x f = prfLte
  in transitive xLteF fLteY

theorem1:
  (x, y: Nat) -> (ys: Vect n Nat) -> (x_ys : Vect (S n) Nat) ->
  (LTE y x) -> (Sorted (y::ys)) -> (Sorted x_ys) -> (Permutation (x::ys) x_ys) -> (Sorted (y::x_ys))
theorem1 x y ys (f::x_ys) yLteX y'ysSor x_ysSor x'ysPermX_ys =
  let
    either: Either (f = x) (Elem f ys) = theorem2 x'ysPermX_ys
    in case either of
      Left fEqX => let
        yLteF = replace {p=(\k => LTE y k)} (sym fEqX) yLteX
        in SortedMany y f x_ys yLteF x_ysSor
      Right fElemYs => let
        yLteF = theorem4 y f ys y'ysSor fElemYs
        in SortedMany y f x_ys yLteF x_ysSor



lteTotal : (x, y : Nat) -> Either (LTE x y) (LTE y x)
lteTotal Z Z = Left LTEZero
lteTotal Z (S m) = Left LTEZero
lteTotal (S n) Z = Right LTEZero
lteTotal (S n) (S m) =
  case lteTotal n m of
    Left p => Left (LTESucc p)
    Right p => Right (LTESucc p)

notLteXyImpliesLteYx : (x, y : Nat) -> (Not (LTE x y)) -> LTE y x
notLteXyImpliesLteYx x y notLte = case lteTotal x y of
  Left prf => absurd (notLte prf)
  Right prf => prf





insert : (inList : Vect n Nat) -> (Sorted inList) -> (x : Nat) -> (outList : Vect (S n) Nat ** (Sorted outList, Permutation (x::inList) outList))
insert [] sor x = ([x] ** (SortedOne x, permutationId [x]))
insert (y::ys) sor x =
  case isLTE x y of
    Yes prf =>
      let
        ysSorted = sortedImpliesSortedSmaller y ys sor
        retSor = SortedMany x y ys prf sor
        ret = (x::(y::ys) ** (retSor, permutationId (x::(y::ys)) ))
      in ret
    No prf =>
      let
        ysSorted = sortedImpliesSortedSmaller y ys sor
        recursiveCase = insert ys ysSorted x
        (x_ys ** (sor1, perm1)) = recursiveCase
        lteYx = notLteXyImpliesLteYx x y prf
        y_x_ysSorted = theorem1 x y ys x_ys lteYx sor sor1 perm1
        intermediatePerm: Permutation (y::(x::ys)) (y::x_ys) = PermutationGrow (x::ys) (x_ys) y perm1
        retPerm: Permutation (x::(y::ys)) (y::x_ys) =
          PermutationTrans (x::(y::ys)) (y::(x::ys)) (y::x_ys) (PermutationSwap ys ys x y (permutationId ys)) intermediatePerm
        ret = (y::x_ys ** (y_x_ysSorted, retPerm))
      in ret



insertionSort : (n: Nat) -> (inList : Vect n Nat) -> (outList : Vect n Nat ** (Sorted outList, Permutation inList outList))
insertionSort 0 [] = ([] ** (SortedZero, PermutationZero))
insertionSort (S n) (x::xs) =
  let recursiveCase : (xsSorted : Vect n Nat ** (Sorted xsSorted, Permutation xs xsSorted)) = insertionSort n xs
      (xsSorted ** (sor1, perm1)) = recursiveCase
      insertRet : (xsSortedInserted : Vect (S n) Nat ** (Sorted xsSortedInserted, Permutation (x::xsSorted) xsSortedInserted)) = insert xsSorted sor1 x
      (xsSortedInserted ** (sor2, perm2)) = insertRet
      perm3 : Permutation (x :: xs) (x :: xsSorted) = PermutationGrow xs xsSorted x perm1
      permRet : Permutation (x::xs) (xsSortedInserted) = PermutationTrans (x::xs) (x::xsSorted) xsSortedInserted perm3 perm2
    in (xsSortedInserted ** (sor2, permRet))


main : IO ()
main = do
  let list = [23, 23, 4352, 532, 123, 143, 214, 2, 142, 412]
  let (sortedList **_) = insertionSort 10 list

  putStrLn $ show list
  putStrLn $ show sortedList
