#Example
G := GrigorchukGroup;
#BS := BranchStructure(G);
#pi := BS.quo;
AssignGeneratorVariables(G);
F := FreeGroup(infinity,"xn",["x1","x2","x3","x4","x5","x6"]);
SetName(F,"FX");
EqG := EquationGroup(G,F);
Eq := Equation(EqG,[Comm(F.1,F.2),(a*b)^2]);
id := IdentityMapping(G);

DEqG := DecompositionEquationGroup(EqG);
constr := GroupHomomorphismByImages(Group(EquationVariables(Eq)),SymmetricGroup(2),[(),()]);
DEq:=DecompositionEquation(DEqG,Eq,constr);

h := EquationHomomorphism(EqG,[F.1],[[F.2,a]]);
ev := EquationEvaluation(Eq,[F.1,F.2],[b,a]);

IsSolution(ev,Eq);

#
#
#TODO More Testcases!
#

testfuncNF := function()
	local elms,e,L,K,xn,x,F,a,b,c,d,f1,f2,f3,G2,others,count;
	G := GrigorchukGroup;
	a := G.1;
	b := G.2;
	c := G.3;
	d := G.4;
	G2 := FreeGroup(5);
	f1 := G2.1;
	f2 := G2.2;
	f3 := G2.3;
	F := FreeGroup(infinity,"xn",["x1","x2","x3","x4","x5","x6","x7","x8","x9"]);
	SetName(F,"FX");
	SetName(G2,"F5");
	elms := [[1,1],[-1,-1],[1,1,2,2],[-2,-1,2,1],[-1,-2,1,2],[2,1,1,2],[2,1,-2,1],[2,-1,-2,-1],[2,-1,2,-1],[-2,-1,-1,2,a],[-2,-1,-1,-2,a],[-1,3,-1,2,3,2],[3,2,1,-3,1,a,2],[-1,-4,3,4,a,-1,2,3,c,2],[1,-5,a,5,b,-1,-2,3,a,4,-3,b,-4,c,2]];
	elms:=List(elms,e->List(e,function(i)
						 if IsInt(i) then
						 	return AssocWordByLetterRep(FamilyObj(Representative(F)),[i]);
						 fi; 
						 return i; end));
	
	others := [	Equation(EquationGroup(G2,F),[F.9^-1,f1,F.8^-1,f2,F.9,F.8,f3]),
				Equation(EquationGroup(G2,F),[F.1^-1*F.2^-1*F.1*F.3*F.2, f2, F.3^-1, f1]) ]
	
	L := [];
	K := [];
	EqG := EquationGroup(G,F);
	count := 1;
	for e in elms do
		Print("Testing : ",count," \r");
		x := Equation(EqG,e);
		xn := EquationNormalForm(x);
		if x^xn.hom <> xn.nf then
			Add(L,x);
		fi;
		if xn.nf^xn.homInv <> x then
			Add(K,x);
		fi;
		count := count+1;
	od;
	for e in others do
		xn := EquationNormalForm(e);
		if e^xn.hom <> xn.nf then
			Add(L,e);
		fi;
		if xn.nf^xn.homInv <> e then
			Add(K,e);
		fi;
	od;
	Print("\nErrors happened at L: ",Size(L),"\n");
	Print("\nErrors happened at K: ",Size(K),"\n");
	
	return [L,K];
end;
