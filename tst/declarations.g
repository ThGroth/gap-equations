LoadPackage("fr");

F := FreeGroup(infinity,"xn",["x1","x2","x3","x4","x5","x6","x7","x8","x9"]);
SetName(F,"FX");

G := GrigorchukGroup;
a:=G.1;b:=G.2;c:=G.3;d:=G.4;

G2 := FreeGroup(5);
f1 := G2.1;	f2 := G2.2;	f3 := G2.3;
SetName(G2,"F5");
elms := [[1,1],[-1,-1],[1,1,2,2],[-2,-1,2,1],[-1,-2,1,2],[2,1,1,2],[2,1,-2,1],[2,-1,-2,-1],[2,-1,2,-1],[-2,-1,-1,2,a],[-2,-1,-1,-2,a],[-1,3,-1,2,3,2],[3,2,1,-3,1,a,2],[-1,-4,3,4,a,-1,2,3,c,2],[1,-5,a,5,b,-1,-2,3,a,4,-3,b,-4,c,2]];
elms:=List(elms,e->List(e,function(i)
						 if IsInt(i) then
						 	return AssocWordByLetterRep(FamilyObj(Representative(F)),[i]);
						 fi; 
						 return i; end));
others := [[F.1^-1,F.2,f1,F.1,F.2^2,f.1,F.2^-1],[F.9^-1,f1,F.8^-1,f2,F.9,F.8,f3],[F.1^-1*F.2^-1*F.1*F.3*F.2, f2, F.3^-1, f1] ];

