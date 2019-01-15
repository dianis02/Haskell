
data Var = A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z deriving (Show,Eq,Ord)
data Formula = Prop Var
	| Verdadero
	| Falso
	|Neg Formula
	|Formula :&: Formula
	|Formula :|: Formula
	|Formula :=>: Formula
	|Formula :<=>: Formula deriving (Show, Eq, Ord)

infixl 9 :&:
infixl 9 :|:
infixr 8 :=>:
infixl 7 :<=>:



negacion :: Formula -> Formula
negacion (Prop x) = Neg (Prop x)
negacion(Verdadero) = Falso
negacion(Falso) = Verdadero
negacion(Neg f) = f
negacion(a :&: b) = negacion(a) :|: negacion(b)
negacion(a :|: b) = negacion(a) :&: negacion(b)
negacion(a :=>: b) = a :&: negacion(b)
negacion(a :<=>: b) = (a :&: negacion(b)):|:(b :&: negacion(a))

equivalencia :: Formula -> Formula
equivalencia(Prop x) = Prop x
equivalencia(Verdadero) = Verdadero
equivalencia(Falso) = Falso
equivalencia(Neg f) = negacion f
equivalencia(a :&: b) = a :&: b
equivalencia(a :|: b) = a:|: b
equivalencia(a :=>: b) = (negacion a :|: b)
--equivalencia (a :<=>: b) = (negacion a :|: b) :&: (negacion b :|: a)
--equivalencia(a :=>: b) = negacion(a :&: negacion(b))
equivalencia(a :<=>: b) = equivalencia (a :=>:b) :&: equivalencia (b :=>:a) 

fnn:: Formula -> Formula
fnn (Prop x)= Prop x
fnn (Verdadero)= Verdadero
fnn (Falso)= Falso
fnn (Neg x)= equivalencia( Neg x)
fnn (x :&: y)= equivalencia (x :&: y)
fnn (x :|: y)= equivalencia ( x :|: y)
fnn (x :=>: y)= equivalencia (x :=>: y)
fnn (x :<=>: y)= equivalencia (x :<=>: y)

sustituye :: Formula -> [(Var,Var)] -> Formula
sustituye (Prop x) [] = Prop x
sustituye (Prop x) ((a,b):xs)= if x == a then (Prop b) else sustituye (Prop x) xs
sustituye Verdadero (v) = Verdadero
sustituye Falso (v)= Falso
sustituye (Neg x) (v) = Neg(sustituye(x) (v))
sustituye (x :&: y) (v) = sustituye (x) (v) :&: sustituye (y) (v) 
sustituye (x :|: y) (v) = sustituye (x) (v)  :|: sustituye (y) (v) 
sustituye (x :=>: y) (v) = sustituye (x) (v)  :=>: sustituye (y) (v) 
sustituye (x :<=>: y) (v) = sustituye (x) (v)  :<=>: sustituye (y) (v) 

varList :: Formula -> [Var]
varList (Prop x)= [x]
varList(Verdadero)=[]
varList(Falso)=[]
varList(Neg x)= varList(x)
varList(x :&: y)= elimina(varList(x)++ varList(y))
varList(x :|: y)= elimina(varList(x)++ varList(y))
varList(x :=>: y)= elimina(varList(x)++ varList(y))
varList(x :<=>: y) = elimina(varList(x)++ varList(y))

elimina []= []
elimina (x:xs)= if (notElem x xs) then [x] ++ elimina xs else elimina xs

fnc:: Formula -> Formula
fnc (Prop x)= Prop x
fnc (Verdadero)= Verdadero
fnc (Falso)= Falso
fnc (Neg x)= negacion x
fnc (Neg (x :&: y))= fnc(negacion(x :&: y))
fnc (Neg (x :|: y))= fnc(negacion(x :|: y))
fnc (x :&: y)= fnc x :&: fnc y
fnc (x :|: y)= distr(fnc x) (fnc y)
fnc (x :=>: y)=  fnc(fnn(x :=>:y))
fnc (x :<=>: y) =  fnc(fnn(x:<=>: y))

distr:: Formula -> Formula -> Formula
--distr (x :&: y) z = (x :|: z) :&: (y :|: z) 
--distr z (x :&: y) = (x :|: z) :&: (y :|: z)
distr (x :&: y) z = (distr x z :&: distr y z )
distr ((x :&: y) :|: (z :&: w)) p =  distr((distr (x:&:y) z):&:(distr (x:&:y) w)) p
---caso la neta bien chacalon pero funciona :o 
distr z (x :&: y) = (distr x z :&: distr y z)
distr x y = fnn(x :|: y)


------------------Practica3--------------------------------------------------------
--------------------------------------------------------------------------------------
aConjunto [] = []
aConjunto (x:xs)|(x `elem` xs)= aConjunto xs
             |otherwise =(x:aConjunto xs)
             
             
             
interp :: Formula -> [(Var,Bool)] -> Bool
interp (Prop a) [] = error"No todas las variables estan definidas"
interp (Prop a) ((var,val):xs) = if var==a then val else interp (Prop a) xs 
interp (Verdadero)l = True
interp (Falso)l = False
interp (Neg a)l = not(interp a l)
interp (a :&: b)l = (interp a l) && (interp b l)
interp (a :|: b)l = (interp a l) || (interp b l)
interp (a :=>:b)l = not(interp a l) || (interp b l)
interp (a :<=>:b)l = (interp a l) == (interp b l)

combinaciones:: Formula -> [[(Var,Bool)]]
combinaciones a = renglones (varList a)

renglones [] = [[]]
renglones (x:xs) = [(x,True):y | y <- ys] ++ [(x,False):y | y <- ys]
					where ys = renglones xs

tablaVerdad:: Formula -> [([(Var,Bool)], Bool)]
tablaVerdad f = (aux (combinaciones f) f)

aux [] f =[]
aux (x:xs) f = (x,(interp f x)):(aux xs f)

aux1 gr = [ y | (x,y) <- gr]

esTautologia:: Formula -> Bool
esTautologia f = if False `elem` (aux1 (tablaVerdad f)) then False else True

esContradicción:: Formula -> Bool
esContradicción f = if True `elem` (aux1 (tablaVerdad f)) then False else True

esSatisfacible:: Formula -> Bool
esSatisfacible f = if True `elem` (aux1 (tablaVerdad f)) then True else False


------------------------------------------------------------------------------



calculaS:: Formula -> [[Formula]]
calculaS (Prop x)= [[Prop x]]
calculaS (Neg(Prop x)) =[[Neg(Prop x)]]
calculaS (x :&: y)= calculaS x ++ calculaS y
calculaS (x:|: y) =[[x,y]]
calculaS (x:=>:y)= calculaS(fnc(x:=>:y))
calculaS (x:<=>:y)= calculaS(fnc(x:<=>:y))
calculaS (Neg(x:|:y))= calculaS(negacion(x:|:y))
calculaS (Neg(x:&:y))= calculaS(negacion(x:&:y))
calculaS (Neg(x:=>:y))= calculaS(negacion(x:=>:y))
calculaS (Neg(x:<=>:y))= calculaS(negacion(x:<=>:y))


res:: [Formula] -> [Formula] -> [Formula]
res [] [] = []
res [] _ = []
res  _ [] = []
res (x:xs) (y:ys) = if buscaPar1 (x:xs) (y:ys) /= [] then  resolvente (x:xs) (y:ys) (buscaPar1 (x:xs)(y:ys))  else []


resolucionBinaria:: Formula -> Bool
resolucionBinaria (Prop x)= False
resolucionBinaria (Verdadero)= False
resolucionBinaria (Falso)= False
resolucionBinaria (Neg x)= resolucionBinaria(fnc(Neg x))
resolucionBinaria (Neg (x :&: y))= encontrar2(calculaS(fnc (Neg(x :&: y))))
resolucionBinaria (Neg (x :|: y))= encontrar2(calculaS(fnc(Neg (x :|: y))))
resolucionBinaria (x :&: y)= encontrar2(calculaS((x :&: y)))
resolucionBinaria (x :|: y)=  encontrar2(calculaS(fnc(x :&: y)))
resolucionBinaria (x :=>: y)=  resolucionBinaria (fnc (x :=>: y))
resolucionBinaria (x :<=>: y) =  resolucionBinaria (fnc (x :<=>: y))


----------------------------AUXILIARES RES-----------------------------
--elimina la literal y su complemento y hace una sola lista
resolvente [] [] _ = []
resolvente [] _ _ = []
resolvente  _ []_ = []
resolvente (x:xs) (y:ys) [[a,b]] = filter (/=a) (x:xs) ++ filter (/=b) (y:ys)

--funcion que devuelve una lista de una literal y su complemento
buscaPar [] [] = []
buscaPar [] _ = []
buscaPar  _ [] = []
buscaPar (x:xs) (y:ys) = [[x,y] | x<-(x:xs) ,y <-(y:ys) , x== negacion y ]
------------------------------AUXILIARES BINARIA------------------------

--igual que buscaPar pero elimina un par cuando este sobra  
buscaPar1 [] [] = []
buscaPar1 [] _ = []
buscaPar1  _ [] = []
buscaPar1 (x:xs) (y:ys) = if eliminaCabeza(buscaPar (x:xs) (y:ys)) == [] then buscaPar (x:xs) (y:ys) else eliminaCabeza(buscaPar (x:xs) (y:ys))



--AUXILIARES RESOLUCIONBin
--encuentra la clausula vacía
encontrar [] = False
encontrar (x:xs) = if x == [] then True else encontrar xs

--algoritmo de saturación 
encontrar2 [] = False
encontrar2 (x:xs) = if encontrar (x:xs) == False then if encontrar2(calculaNuevoS (listaPares(x:xs))) == True then True  else if (calculaNuevoS (listaPares(x:xs))) /= (x:xs) then False else encontrar2 (calculaNuevoS (listaPares(x:xs))++(x:xs)) else True


calculaNuevoS [] = []
calculaNuevoS [x]=[]
calculaNuevoS (x:xs)= [res (cabeza(cabeza (x:xs)))  (cabeza(eliminaCabeza(cabeza (x:xs)))) ] ++ calculaNuevoS xs


---AUXILIARES CALCULANUEVOS
--pares de la literal y su negacion
listaPares [] = [[[Falso]]]
listaPares (x:xs) = productoCruz [x] xs ++ listaPares xs
   
--regresa una lista de todas las posibles pares de literal y su negación en la fórmula   
productoCruz []_= []
productoCruz _[]=[]
productoCruz (x:xs) (y:ys) = [[x,y]| x<-(x:xs), y<-(y:ys), existePar x y]

--elimina Clausula
eliminaCabeza [] = []
eliminaCabeza (x:xs) = xs

--Clausula
cabeza [] = []
cabeza (x:xs) = x


existePar (x:xs) (y:ys) = if buscaPar1 (x:xs) (y:ys) /= [] then True else False





---------ejemplos fórmulas---------
ejemplo1=((Neg(Prop P) :&: Prop Q) :&:((Prop R :=>: Prop P) :=>: Neg(Prop R) :|: Neg(Prop R)):&: Neg(Prop R :|: Neg (Prop P)))
ejemplo=((Neg(Prop P) :|: Prop Q) :&: (Neg(Prop Q) :|: Prop P) :&: (Neg(Prop Q) :|: Prop S) :&:(Neg (Prop S) :|: Prop Q) :&: Prop P :&: Neg(Prop S)) 
ejemplo11=((Prop P :=>: Prop Q):&:(Prop Q :=>:(Prop P :|: Prop R)):&: Neg(Prop P :=>: (Prop P :=>: Prop Q):=>: Prop R))

--Ejemplos de las auxiliares
ejemplo2= [[Neg (Prop P),Prop Q],[Neg (Prop Q),Prop P],[Neg (Prop Q),Prop S],[Neg (Prop S),Prop Q],[Prop P],[Neg (Prop S)]]
ejemplo3 =[[Neg(Prop P)],[Prop Q], [Prop R , Neg(Prop Q) , Neg(Prop R)],[Neg(Prop P), Neg(Prop Q), Neg(Prop R)],[Neg(Prop R)],[Prop P]]
ejemplo4 = [[Neg(Prop P)],[Prop P], [Prop R , Neg(Prop Q) , Neg(Prop R)],[Neg(Prop P), Neg(Prop Q), Neg(Prop R)],[Neg(Prop R)]]
ejemplo5 = [[Prop Q], [Prop R , Neg(Prop Q) , Neg(Prop R)],[Neg(Prop P), Neg(Prop Q), Neg(Prop R)],[Neg(Prop R)],[Prop P]]
ejemploP6 = [[[Neg (Prop P)],[Prop P]],[[Prop Q],[Prop R,Neg (Prop Q),Neg (Prop R)]],[[Prop Q],[Neg (Prop P),Neg (Prop Q),Neg (Prop R)]],[[Prop R,Neg (Prop Q),Neg (Prop R)],[Neg (Prop P),Neg (Prop Q),Neg (Prop R)]],[[Prop R,Neg (Prop Q),Neg (Prop R)],[Neg (Prop R)]],[[Neg (Prop P),Neg (Prop Q),Neg (Prop R)],[Prop P]]]
ejemploP7= [[[Neg (Prop P),Prop Q],[Neg (Prop Q),Prop P]],[[Neg (Prop P),Prop Q],[Neg (Prop Q),Prop S]],[[Neg (Prop P),Prop Q],[Prop P]],[[Neg (Prop Q),Prop P],[Neg (Prop S),Prop Q]],[[Neg (Prop Q),Prop S],[Neg (Prop S),Prop Q]],[[Neg (Prop Q),Prop S],[Neg (Prop S)]]]
ejemploP8= [[[Neg (Prop P),Prop Q],[Neg (Prop Q),Prop S]],[[Neg (Prop P),Prop Q],[Prop P]],[[Neg (Prop Q),Prop P],[Neg (Prop S),Prop Q]],[[Neg (Prop Q),Prop S],[Neg (Prop S),Prop Q]],[[Neg (Prop Q),Prop S],[Neg (Prop S)]]]
