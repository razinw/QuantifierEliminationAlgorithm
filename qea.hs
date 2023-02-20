module Math where

--Тип данных переменной
data Var = Var String deriving (Show, Eq)

--Функция печати переменной
showVar::Var->String
showVar (Var a) = a

--Тип данных квантора
data Quantifier = ForAll Var | Exist Var deriving (Show, Eq)

--Функция печати квантора
showQuantifier::Quantifier->String
showQuantifier (ForAll a) = "ForAll " ++ (showVar a)
showQuantifier (Exist a) = "Exist " ++ (showVar a)

--Тип данных предиката
data Predicate = Equal Var Var | Less Var Var | One | Zero deriving (Show, Eq)

--Функция печати предиката
showPredicate::Predicate->String
showPredicate (Equal a b) = (showVar a) ++ "=" ++ (showVar b)
showPredicate (Less a b) = (showVar a) ++ "<" ++ (showVar b)
showPredicate One = "1"
showPredicate Zero = "0"

--Тип данных формулы
data Formula = Solo Predicate | Or [Formula] | And [Formula] deriving (Show, Eq)

--Функция печати формулы
showFormula::Formula->String
showFormula (Or a) = firstLast(showFormulaAux (Or a))
showFormula a = showFormulaAux a

--Вспомогательная функция печати формулы
showFormulaAux::Formula->String
showFormulaAux (And x) = (showAnd x)
showFormulaAux (Or x) = "("++(showOr x)++")"
showFormulaAux (Solo a) = showPredicate a

--Функция печати списка конъюнкций
showAnd::[Formula]->String
showAnd [] = ""
showAnd (x:[]) = (showFormulaAux x)
showAnd (x:xs) = (showFormulaAux x) ++ "&" ++ (showAnd xs)

--Функция печати списка дизъюнкций
showOr::[Formula]->String
showOr [] = ""
showOr (x:[]) = (showFormulaAux x)
showOr (x:xs) = (showFormulaAux x) ++ "|" ++ (showOr xs)

--Функция взятия отрицания от формулы
negFormula::Formula->Formula
negFormula (And ((Solo x):[])) = negFormula (Solo x)
negFormula (And (x:[])) = Or [negFormula x]
negFormula (And ((Solo x):xs)) = combineFormula (negFormula (Solo x)) (negFormula (And xs))
negFormula (And (x:xs)) = combineFormula (Or [negFormula x]) (negFormula (And xs))
negFormula (Or (x:[])) = And [negFormula x]
negFormula (Or (x:xs)) = combineFormula (And [negFormula x]) (negFormula (Or xs))
negFormula (Solo (Less a b)) = Or [Solo (Less b a), Solo (Equal a b)]
negFormula (Solo (Equal a b)) = Or [Solo (Less b a), Solo (Less a b)]
negFormula (Solo One) = Solo Zero
negFormula (Solo Zero) = Solo One

--Функция проверки эквивалентности двух формул
isEqual::Formula->Formula->Bool
isEqual (And a) (And b) = length arrayA == length arrayB && foundArray arrayA arrayB
    where
        arrayA = removeRepeats a
        arrayB = removeRepeats b
isEqual (Or a) (Or b) = length arrayA == length arrayB && foundArray arrayA arrayB
    where
        arrayA = removeRepeats a
        arrayB = removeRepeats b
isEqual (Solo (Equal a b)) (Solo (Equal c d)) = (a==c && b==d) || (a==d && b==c)
isEqual (Solo a) (Solo b) = a==b
isEqual a b = False

--Функция преобразования двух формул в одну
combineFormula::Formula->Formula->Formula
combineFormula (And a) (And b) = And (a ++ b)
combineFormula (Or a) (Or b) = Or (a ++ b)
combineFormula (Solo a) (And b) = And ([Solo a] ++ b)
combineFormula (And a) (Solo b) = And (a ++ [Solo b])
combineFormula (Solo a) (Or b) = Or ([Solo a] ++ b)
combineFormula (Or a) (Solo b) = Or (a ++ [Solo b])
combineFormula _ _ = error "Wrong combination of formulas."

--Функция приведения к плоским спискам
flat::Formula->Formula
flat (And a)
    | length a == 1 = flat (a!!0)
    | a /= flatAnd a = flat (And (flatAnd a))
    | otherwise = And a
flat (Or a)
    | length a == 1 = flat (a!!0)
    | a /= flatOr a = flat (Or (flatOr a))
    | otherwise = Or a
flat a = a

--Функция приведения к плоским спискам для конъюнкции
flatAnd::[Formula]->[Formula]
flatAnd [] = []
flatAnd ((And a):xs) = flatAnd a ++ flatAnd xs
flatAnd ((Or a):xs) = [flat (Or a)] ++ flatAnd xs
flatAnd (x:xs) = [x] ++ flatAnd xs

--Функция приведения к плоским спискам для дизъюнкции
flatOr::[Formula]->[Formula]
flatOr [] = []
flatOr ((Or a):xs) = flatOr a ++flatOr xs
flatOr ((And a):xs) = [flat (And a)]++ flatOr xs
flatOr (x:xs) = [x] ++ flatOr xs

--Функция упрощения формулы
simple = genSimple.flat

--Функция упрощения "плоской" формулы
genSimple::Formula->Formula
genSimple (Solo (Equal a b))
    | a==b = Solo One
    | otherwise = Solo (Equal a b)
genSimple (Solo (Less a b))
    | a==b = Solo Zero
    | otherwise = Solo (Less a b)
genSimple (Or a)
    | found (Solo One) simpledArray = Solo One
    | foundArray array simpledArray == False = simple(Or simpledArray)
    | simpledArray == [] = Solo Zero
    | length simpledArray == 1 = simple (simpledArray !! 0)
    | checkAdd (Or simpledArray) 0 == True = Solo One
    | otherwise = simpledFormula
    where
        array = remove (Solo Zero) (removeRepeats a)
        simpledArray = simpleArray array
        simpledFormula = simpleOr (getCouples simpledArray) simpledArray
genSimple (And a)
    | found (Solo Zero) simpledArray = Solo Zero
    | foundArray array simpledArray == False = simple(And simpledArray)
    | simpledArray == [] = Solo One
    | length simpledArray == 1 = simple (simpledArray !! 0)
    | checkAdd (And simpledArray) 0 == True = Solo Zero
    | otherwise = simpledFormula
    where
        array = remove (Solo One) (removeRepeats a)
        simpledArray = simpleArray array
        simpledFormula = simpleAnd (getCouples simpledArray) simpledArray
genSimple a = a

--Функция упрощения списка "плоских" формул
simpleArray::[Formula]->[Formula]
simpleArray [] = []
simpleArray (x:xs) = [simple x]++simpleArray xs

--Функция упрощения списка конъюнкций
simpleAnd::[[Formula]]->[Formula]->Formula
simpleAnd couples [] = Solo One
simpleAnd couples (x:[]) = x
simpleAnd [] array = And array
simpleAnd (((Or first):((Or second):a)):ys) array
    | length commonArray > 0 = simpleAnd couplesCommon arrayCommon
	| otherwise = simpleAnd ys array
    where
        commonArray = common first second
        arrayCommon = takeList (simple (And ([Or commonArray]++(removeArray [Or first, Or second] array))))
        couplesCommon = getCouples arrayCommon
simpleAnd (((Solo first):((Or second):a)):ys) array
    | found (Solo first) second == True = simpleAnd couplesCommon arrayCommon
	| otherwise = simpleAnd ys array
    where
        arrayCommon = takeList (simple (And (remove (Or second) array)))
        couplesCommon = getCouples arrayCommon
simpleAnd (((Or first):((Solo second):a)):ys) array
    | found (Solo second) first == True = simpleAnd couplesCommon arrayCommon
	| otherwise = simpleAnd ys array
    where
        arrayCommon = takeList (simple (And (remove (Or first) array)))
        couplesCommon = getCouples arrayCommon
simpleAnd (((Solo (Less a b)):((Solo (Equal c d)):empty)):ys) array
    | a==d && b==c = Solo Zero
    | a==c && b==d = Solo Zero
    | otherwise = simpleAnd ys array
simpleAnd (((Solo (Equal a b)):((Solo (Less c d)):empty)):ys) array
    | a==d && b==c = Solo Zero
    | a==c && b==d = Solo Zero
    | otherwise = simpleAnd ys array
simpleAnd (((Solo (Less a b)):((Solo (Less c d)):empty)):ys) array
    | a==d && b==c = Solo Zero
    | otherwise = simpleAnd ys array
simpleAnd (((_):((And second):a)):ys) array = error "AND NOT FLAT"  
simpleAnd (((And first):((_):a)):ys) array = error "AND NOT FLAT"    
simpleAnd (x:xs) array = simpleAnd xs array 

--Функция упрощения списка дизъюнкций
simpleOr::[[Formula]]->[Formula]->Formula
simpleOr couples [] = Solo Zero
simpleOr couples (x:[]) = x
simpleOr [] array = Or array
simpleOr (((And first):((And second):empty)):ys) array
	| length commonArray > 0 = simpleOr couplesCommon arrayCommon
    | found notFirst second == True = simpleOr couplesOrtFirst arrayOrtFirst
    | found notSecond first == True = simpleOr couplesOrtSecond arrayOrtSecond
	| otherwise = simpleOr ys array
    where
        commonArray = common first second
        arrayCommon = takeList (simple (Or ([And commonArray]++(removeArray [And first, And second] array))))
        couplesCommon = getCouples arrayCommon
        notFirst = negFormula (And first)
        arrayOrtFirst = takeList (simple (Or ([And (remove notFirst second)]++(remove (And second) array))))
        couplesOrtFirst = getCouples arrayOrtFirst
        notSecond = negFormula (And second)
        arrayOrtSecond = takeList (simple (Or ([And (remove notSecond first)]++(remove (And first) array))))
        couplesOrtSecond = getCouples arrayOrtSecond
simpleOr (((Solo first):((And second):a)):ys) array
    | found (Solo first) second == True = simpleOr couplesCommon arrayCommon
    | found notFirst second == True = simpleOr couplesOrt arrayOrt
	| otherwise = simpleOr ys array
    where
        arrayCommon = takeList (simple (Or (remove (And second) array)))
        couplesCommon = getCouples arrayCommon
        notFirst = negFormula (Solo first)
        arrayOrt = takeList (simple (Or ([And (remove notFirst second)]++(remove (And second) array))))
        couplesOrt = getCouples arrayOrt
simpleOr (((And first):((Solo second):a)):ys) array
    | found (Solo second) first == True = simpleOr couplesCommon arrayCommon
    | found notSecond first == True = simpleOr couplesOrt arrayOrt
	| otherwise = simpleOr ys array
    where
        arrayCommon = takeList (simple (Or (remove (And first) array)))
        couplesCommon = getCouples arrayCommon
        notSecond = negFormula (Solo second)
        arrayOrt = takeList (simple (Or ([And (remove notSecond first)]++(remove (And first) array))))
        couplesOrt = getCouples arrayOrt
simpleOr (((_):((Or second):a)):ys) array = error "OR NOT FLAT"  
simpleOr (((Or first):((_):a)):ys) array = error "OR NOT FLAT"      
simpleOr (x:xs) array = simpleOr xs array

--Функция проверки закона дополнительности
checkAdd::Formula->Int->Bool
checkAdd (Or a) n
    | n == length a = False
    | foundArray (takeList notX) (remove x a) == True = True
    | otherwise = checkAdd (Or a) (n+1)
    where
        x = a !! n
        notX = negFormula x
checkAdd (And a) n
    | n == length a = False
    | returnType x == "Or" && foundArray (takeList notX) (remove x a) == True = True
    | returnType x == "Solo" && found notX (remove x a) == True = True
    | otherwise = checkAdd (Or a) (n+1)
    where
        x = a !! n
        notX = negFormula x
checkAdd _ _ = False

--Функция приведения к ДНФ
dnf::Formula->Formula
dnf (Or a)
    | a /= dnfArray = Or (dnfArray)
    | otherwise = Or a
	where 
		dnfArray = dnfOr (flatOr a)
dnf (And a)
	| length da == 1 = head da
    | damo /= da = And da
    | otherwise = And a
	where 
		da = dnfAnd a
		damo = dnfAndMoveOr a		
dnf a = a

--Функция сдвига первой дизъюнкции влево в конъюкции списков формул
dnfAndMoveOr::[Formula]->[Formula]
dnfAndMoveOr [] = []
dnfAndMoveOr ((Or a):xs) = [Or a]++xs
dnfAndMoveOr (x:xs) = dnfAndMoveOr xs++[x]

--Функция приведения списка конъюнкций к ДНФ после сдвига первой дизъюнкции 
dnfAndMul::[Formula]->[Formula]
dnfAndMul [] = []
dnfAndMul (x:[]) = [x]
dnfAndMul ((Solo first):xs) = [Solo first] ++ xs 
dnfAndMul ((Or first):((Or second):xs)) = dnfAndMul ([Or (couplesToFormula "And" (couplesArrays (dnfOr.flatOr$first) (dnfOr.flatOr$second)))]++xs)
dnfAndMul ((Or first):((Solo second):xs)) = dnfAndMul ([Or (couplesToFormula "And" (сouplesElemArray (Solo second) (dnfOr.flatOr$first)))]++xs)

--Функция приведения списка конъюнкций к ДНФ
dnfAnd::[Formula]->[Formula]
dnfAnd = dnfAndMul.dnfAndMoveOr

--Функция приведения списка дизъюнкций к ДНФ
dnfOr::[Formula]->[Formula]
dnfOr [] = []
dnfOr ((And first):ys)
    | returnType daf  == "Or" = takeList(daf) ++ dnfOr ys
    | otherwise = [daf] ++ dnfOr ys
    where
		daf = dnf (And first)
dnfOr (y:ys) = [y] ++ dnfOr ys

--Функция элиминации квантора существования
deep::Var->Formula->Formula
deep z (Solo(Less a b)) 
    | z == a || z == b = Solo One
    | otherwise = Solo(Less a b)
deep z (Solo(Equal a b)) 
    | z == a || z == b = Solo One
    | otherwise = Solo(Equal a b)
deep z (Or a) = Or (deepArray z a)
deep z (And a)  
   | new /= z = And newArray
   | less == [] || more == [] = And (deepArray z a)
   | otherwise  = And ((deepArray z a)++comboLessMore)
   where 
        new = findVarEqualAnd z a
        newArray = changeVarAnd z new a
        foundVars = findVarsLessMoreAnd z a [] []
        less = foundVars!!0
        more = foundVars!!1
        comboLessMore = createNewPreds (couplesArrays less more)
deep z a = a

--Функция составления новых предикатов из пар переменных
createNewPreds::[[Var]]->[Formula]
createNewPreds [] = []
createNewPreds (x:xs) = [Solo (Less (x!!0) (x!!1))] ++ createNewPreds xs

--Функция элиминация квантора для массива формул
deepArray::Var->[Formula]->[Formula]
deepArray z [] = []
deepArray z (x:xs) = [deep z x]++(deepArray z xs) 

--Функция поиска переменной в предикатах равенства
findVarEqualAnd::Var->[Formula]->Var
findVarEqualAnd z ([]) = z
findVarEqualAnd z ((Solo (Equal a b)):xs) 
    | z == a = b
    | z == b = a
    | otherwise = findVarEqualAnd z xs
findVarEqualAnd z (_:xs) = findVarEqualAnd z xs 

--Функция замены переменной на новую 
changeVarAnd::Var->Var->[Formula]->[Formula]
changeVarAnd old new [] = []
changeVarAnd old new (Solo(Less a b):xs) 
    | a == old = [Solo (Less new b)] ++ changeVarAnd old new xs
    | b == old = [Solo (Less a new)] ++ changeVarAnd old new xs
    | otherwise = [Solo (Less a b)] ++ changeVarAnd old new xs
changeVarAnd old new (Solo(Equal a b):xs) 
    | a == old = [Solo (Equal new b)] ++ changeVarAnd old new xs
    | b == old = [Solo (Equal a new)] ++ changeVarAnd old new xs
    | otherwise = [Solo (Equal a b)] ++ changeVarAnd old new xs
changeVarAnd old new (x:xs) = [x] ++ changeVarAnd old new xs

--Функция поиска переменных в массиве предикатов с ограничениями снизу и сверху
findVarsLessMoreAnd::Var->[Formula]->[Var]->[Var]->[[Var]]
findVarsLessMoreAnd z [] less more = [less,more]
findVarsLessMoreAnd z (Solo(Less a b):xs) less more 
    | a == z = findVarsLessMoreAnd z xs less (more++[b])
    | b == z = findVarsLessMoreAnd z xs (less++[a]) more
    | otherwise = findVarsLessMoreAnd z xs less more
findVarsLessMoreAnd z (_:xs) less more = findVarsLessMoreAnd z xs less more

--Функция преобразования списков пар формулы в список формул
couplesToFormula::String->[[Formula]]->[Formula]
couplesToFormula _ [] = []
couplesToFormula "And" (((And x):((And y):a)):ys) = [And (x ++ y)] ++ (couplesToFormula "And" ys)
couplesToFormula "And" (((Solo x):((And y):a)):ys) = [And ([Solo x] ++ y)] ++ (couplesToFormula "And" ys)
couplesToFormula "And" (((And x):((Solo y):a)):ys) = [And (x ++ [Solo y])] ++ (couplesToFormula "And" ys)
couplesToFormula "And" (((Solo x):((Solo y):a)):ys) = [And ([Solo x] ++ [Solo y])] ++ (couplesToFormula "And" ys)
couplesToFormula "Or" (x:xs) = [Or x] ++ (couplesToFormula "Or" xs)

--Функция, возвращающая список от конъюнкции или дизъюнкции
takeList::Formula->[Formula]
takeList (Or a) = a
takeList (And a) = a
takeList (Solo a) = [Solo a]

--Функция, возвращая тип формулы
returnType::Formula->String
returnType (And a) = "And"
returnType (Or a) = "Or"
returnType (Solo a) = "Solo"

--Функция, возвращая тип предиката
returnTypePred::Formula->String
returnTypePred (Solo (Less a b)) = "Less"
returnTypePred (Solo (Equal a b)) = "Equal"

returnVarsPred::Formula->[Var]
returnVarsPred (Solo (Less a b)) = [a,b]

--Функция, убирающая повторы в списке конъюнкций и дизъюнкций в формуле
removeRepFormula::Formula->Formula
removeRepFormula (And x)
    | length newX == 1 = head x
    | otherwise = And newX
    where
        newX = removeRepeats x
removeRepFormula (Or x)
    | length newX == 1 = head x
    | otherwise = Or newX
    where
        newX = removeRepeats x
removeRepFormula x = x

--Функция, убирающая первый и последний элемент списка
firstLast::[a]->[a]
firstLast [] = []
firstLast [x] = []
firstLast xs = tail (init xs)

--Функция поиска списка в списке
foundArray::[Formula]->[Formula]->Bool
foundArray [] y = True
foundArray (x:xs) y
    | found x y == False = False
    | otherwise = foundArray xs y

--Функция поиска элемента в списке
found::Formula->[Formula]->Bool
found a [] = False
found a (b:bs)
    | isEqual a b = True
    | otherwise = found a bs

--Функция удаления повторов в списке
removeRepeats::[Formula]->[Formula]
removeRepeats [] = []
removeRepeats (x:xs) =  [x] ++ removeRepeats (remove x xs)

--Функция, возвращающая список, состоящий из элементов, принадлежащих обоим спискам
common::[Formula]->[Formula]->[Formula]
common [] y = []
common (x:xs) y
    | found x y = [x] ++ (common xs y)
    | otherwise = (common xs y)

--Функция, выполняющая замену в список дизъюнкции списков формулы
changeOr::Formula->Formula->[Formula]->[Formula] 
changeOr (Solo One) _ array = [Solo One]
changeOr (Solo Zero) old array = removeOne old array
changeOr new old array = (removeOne old array) ++ [new]

--Функция, выполняющая замену в списке конъюнкции списков формулы	
changeAnd::Formula->Formula->[Formula]->[Formula]
changeAnd (Solo Zero) _ array = [Solo Zero]
changeAnd (Solo One) old array = removeOne old array
changeAnd new old array = (removeOne old array) ++ [new]

--Функция, выполняющая вставку формулы в список дизъюнкции списков формулы с проверкой на повторы
insertOr::Formula->[Formula]->[Formula]
insertOr (Solo One) array = [Solo One]
insertOr (Solo Zero) array = array
insertOr new array 
	| found new array = array
	| otherwise = array++[new]

--Функция, выполняющая вставку формулы в список конъюнкции списков формулы с проверкой на повторы
insertAnd::Formula->[Formula]->[Formula]
insertAnd (Solo Zero) array = [Solo Zero]
insertAnd (Solo One) array = array
insertAnd new array 
	| found new array = array
	| otherwise = array++[new]	

--Функция, удаляющая элементы первого списка (при возможности) из второго
removeArray [] a = a
removeArray (x:xs) a = removeArray xs (remove x a)

--Функция, удаляющая элемент (при возможности) из списка
remove x [] = []
remove x (y : xs)
  | isEqual x y = remove x xs
  | otherwise = y : remove x xs
  
--Функция, удаляющая элемент (при возможности) из списка один раз
removeOne x [] = []
removeOne x (y : xs)
  | isEqual x y = xs
  | otherwise = y : removeOne x xs

--Функция, создающая все возможные пары, состоящие из переданного элемента и всех элементов списка
сouplesElemArray::a->[a]->[[a]]
сouplesElemArray _ [] = []
сouplesElemArray x (y:ys) = [[x,y]] ++ сouplesElemArray x ys

--Функция, создающая все возможные пары элементов обоих списков
couplesArrays::[a]->[a]->[[a]]
couplesArrays [] _ = []
couplesArrays (x:xs) y = сouplesElemArray x y ++ couplesArrays xs y

--Функция, создающая все возможные пары элементов списка
getCouples::[a]->[[a]]
getCouples [] = []
getCouples (x:xs) = сouplesElemArray x xs ++ (getCouples xs)

--Тип данных предложения
data Sentence = Sentence [Quantifier] Formula deriving (Show, Eq)

--Алгоритм элиминации кванторов	
algorithm::Sentence->Bool
algorithm (Sentence [] formula)
    | isEqual (simple formula) (Solo Zero) = False
    | isEqual (simple formula) (Solo One) = True
	| otherwise = error "This sentence is incorrect."
algorithm (Sentence ((ForAll a):xs) formula) = algorithm (Sentence xs newFormula)
    where
        newFormula = negFormula (simple (deep a (dnf (negFormula (simple formula)))))
algorithm (Sentence ((Exist a):xs) formula) = algorithm (Sentence xs newFormula) 
    where
        newFormula = deep a (dnf (simple formula))

--Функция печати конкретного заданного примера c результатом работы алгоритма элиминации кванторов
showExample::Sentence->String
showExample (Sentence quantifiers formula)
    | algorithm (Sentence (reverse quantifiers) formula) = "The sentence '"++(showStackQuantifiers quantifiers)++" . "++showFormula (formula)++"' is linear order theorem."
    | otherwise = "The sentence '" ++ showStackQuantifiers quantifiers ++ " . " ++ showFormula (formula) ++ "' is not linear order theorem."

--Функция печати стека кванторов
showStackQuantifiers::[Quantifier]->String
showStackQuantifiers [] = []
showStackQuantifiers (x:xs) = showQuantifier x ++ " " ++ showStackQuantifiers xs 

--Объявление переменных x, y, z, u
x = Var "x"
y = Var "y"
z = Var "z"
u = Var "u"

--Пример#1
quant0 = [ForAll x, ForAll y, Exist z, ForAll u]
form0 = And [Or [Solo(Less x z), Solo(Equal x z)],Or [Solo(Less z u), Solo(Equal z u), Solo(Less u y)]]
sent0 = Sentence quant0 form0
demo0 = showExample sent0

--Пример#2
quant1 = [ForAll x, Exist y, ForAll z]
form1 = Or [And[Or[Solo(Less x y), Solo(Equal x y)],Solo(Less z y)],And[Or[Solo(Less x z),Solo(Equal x z)],Solo(Less y z)]]
sent1 = Sentence quant1 form1
demo1 = showExample sent1
