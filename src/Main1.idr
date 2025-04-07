module Main1
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
    PermutationId: (as : Vect n Nat) -> Permutation as as
    PermutationGrow: (as, bs: Vect n Nat) -> (x : Nat) ->
      Permutation as bs -> Permutation (x::bs) (x::as)
    PermutationSwap: (xs : Vect n Nat) -> (a, b : Nat) ->
      Permutation (a::(b::xs)) (b::(a::xs))
    PermutationTrans : (as, bs, cs : Vect n Nat) ->
      Permutation as bs -> Permutation bs cs -> Permutation as cs



permutationRev : (xs, ys: Vect n Nat) -> Permutation xs ys -> Permutation ys xs
permutationRev (x::as) (x::bs) (PermutationGrow bs as x p) = (PermutationGrow as bs x (permutationRev bs as p))
permutationRev xs xs (PermutationId xs) = PermutationId xs
permutationRev (a::(b::xs)) (b::(a::xs)) (PermutationSwap xs a b) = PermutationSwap xs b a
permutationRev as cs (PermutationTrans as bs cs perm1 perm2) = PermutationTrans cs bs as (permutationRev bs cs perm2) (permutationRev as bs perm1)


theorem3: (as, cs : Vect n Nat) -> (a : Nat) -> Permutation as cs -> Elem a as -> Elem a cs
theorem3 xs xs x (PermutationId xs) elem = elem
theorem3 (a::(b::xs)) (b::(a::xs)) c (PermutationSwap xs a b) elem = case elem of
  Here => There (Here)
  There (Here) => Here
  There (There x) => There (There x)
theorem3 (x::ys) (x::xs) l (PermutationGrow xs ys x p1) elem = case elem of
  Here => Here
  There elem => There (theorem3 ys xs l (permutationRev xs ys p1) elem)
theorem3 as cs a (PermutationTrans as bs cs p1 p2) aElemAs = let
  aElemBs : (Elem a bs) = theorem3 as bs a p1 aElemAs
  in theorem3 bs cs a p2 aElemBs

theorem2: (Permutation (x::xs) (y::ys)) -> Either (y = x) (Elem y xs)
theorem2 (PermutationId (a::as)) = Left Refl
theorem2 (PermutationSwap xs a b) = Right (Here)
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
insert [] sor x = ([x] ** (SortedOne x, PermutationId [x]))
insert (y::ys) sor x =
  case isLTE x y of
    Yes prf =>
      let
        ysSorted = sortedImpliesSortedSmaller y ys sor
        retSor = SortedMany x y ys prf sor
        ret = (x::(y::ys) ** (retSor, PermutationId (x::(y::ys)) ))
      in ret
    No prf =>
      let
        ysSorted = sortedImpliesSortedSmaller y ys sor
        recursiveCase = insert ys ysSorted x
        (x_ys ** (sor1, perm1)) = recursiveCase
        lteYx = notLteXyImpliesLteYx x y prf
        y_x_ysSorted = theorem1 x y ys x_ys lteYx sor sor1 perm1
        intermediatePerm: Permutation (y::(x::ys)) (y::x_ys) =
          PermutationGrow (x_ys) (x::ys) y (permutationRev (x :: ys) x_ys perm1)
        retPerm: Permutation (x::(y::ys)) (y::x_ys) =
          PermutationTrans (x::(y::ys)) (y::(x::ys)) (y::x_ys) (PermutationSwap ys x y) intermediatePerm
        ret = (y::x_ys ** (y_x_ysSorted, retPerm))
      in ret



insertionSort : (n: Nat) -> (inList : Vect n Nat) -> (outList : Vect n Nat ** (Sorted outList, Permutation inList outList))
insertionSort 0 [] = ([] ** (SortedZero, PermutationId []))
insertionSort (S n) (x::xs) =
  let recursiveCase : (xsSorted : Vect n Nat ** (Sorted xsSorted, Permutation xs xsSorted)) = insertionSort n xs
      (xsSorted ** (sor1, perm1)) = recursiveCase
      insertRet : (xsSortedInserted : Vect (S n) Nat ** (Sorted xsSortedInserted, Permutation (x::xsSorted) xsSortedInserted)) = insert xsSorted sor1 x
      (xsSortedInserted ** (sor2, perm2)) = insertRet
      perm3 : Permutation (x :: xs) (x :: xsSorted)  = permutationRev (x::xsSorted) (x::xs) (PermutationGrow xs xsSorted x perm1)
      permRet : Permutation (x::xs) (xsSortedInserted) = PermutationTrans (x::xs) (x::xsSorted) xsSortedInserted perm3 perm2
    in (xsSortedInserted ** (sor2, permRet))


main : IO ()
main = do
  let list = [23, 23, 4352, 532, 123, 143, 214, 2, 142, 412]
  let (sortedList **_) = insertionSort 10 list

  putStrLn $ show list
  putStrLn $ show sortedList
