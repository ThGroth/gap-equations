p := function(q)
	local g;
	if not q in GmodKP then
		Error("q needs to be in G/K'");
	fi;
	g := PreImagesRepresentative(tauLP,q)^isoGLPtoG;
	return ((State(g,2)*State(g,1))^isoGtoGLP)^homGtoGmodKxK;
end;
StateLP := function(q,i)
	if not q in GmodKP then
		Error("State: q needs to be in G/K'");
	fi;
	return (State(PreImagesRepresentative(tauLP,q)^isoGLPtoG,i)^isoGtoGLP)^piLP;
end;


nextGammas := function(gamma,q)
		local Gamma1,Dep,i,ga,first,gp,acts,F,EqG,DEqG,FF,DEqQ,Eq,DEq,nf,num,U,q1,q2,H,gaP,Suc;
	Gamma1 := []; 
    Dep := [];
    i := 1;
    for ga in gamma do
        first := true;
        Add(Dep,[2*i-1,2*i]); i := i+1;
        for gp in PreImages(BS.epi,ga) do
            if first then
                Add(Gamma1,[gp![1]]);
                Add(Gamma1,[gp![2]]);
                first := false;
            else
                Add(Gamma1[Size(Gamma1)-1],gp![1]);
                Add(Gamma1[Size(Gamma1)],gp![2]);
            fi; 
        od;
    od;
    Gamma1 := DEP_CARTESIAN@fr(Gamma1,Dep);;#Size of Gamma1 about 1024	
	
	F := FreeGroup(infinity,"xn",["x1","x2","x3","x4","x5","x6"]);SetName(F,"FX");
    EqG := EquationGroup(G,F);
    DEqG := DecompositionEquationGroup(EqG);
    FF := DEqG!.free;
    DEqQ := EquationGroup(Q,FF);

    num := 5;    
	Eq := Equation(Equation(EqG,Concatenation(List([1..num],i->[F.(i)^-1,a,F.(i)]) ))*a);

	acts := ActivityConstraint(gamma);
	acts := GroupHomomorphismByImages(Group(EquationVariables(Eq)),SymmetricGroup(2),acts);
	DEq := DecompositionEquation(DEqG,Eq,acts);
	q1:= StateLP(q,1)^isoGmodKtoQ;
	q2:= StateLP(q,2)^isoGmodKtoQ;
	DEq := Equation(DEqQ,DEq!.words,DEq!.activity)*Equation(DEqQ,[[q1],[q2]],()); #Let this equation be defined over Q

	U := DecomposedEquationDisjointForm(DEq);
	nf := EquationNormalForm(First(EquationComponents(U.eq),eq->not IsOne(eq)));
	Assert(0,nf.nf=Equation(DEqQ,[Comm(FF.1,FF.2)*Comm(FF.3,FF.4)]));

	for gp in Gamma1 do
		H := EquationEvaluation(DEqQ,List([1..10],i->FF.(i)),gp);
		if ForAll(EquationComponents(DEq),eq->IsOne(eq^H))then
			#Compute the image of γ' under the normalization hommorphism and simplify it to the F₅ case
    		gaP := MakeImmutable(ReducedConstraint( List([1..10],i->ImageElm(nf.homInv*H,FF.(i))) ));
    		Suc := List(PreImages(varpiPrimeLP,p(q)));
            #Added check for nontrivial activity.
    		if HasNontrivialActivity(gaP) and ForAll(Suc, r->IsGoodPair(r,gaP)) then
    			return gaP; #[γ',z,{q₁,…,q₁₆}]
    		fi;          
		fi;
	od;
	return fail;
end;

L := Cartesian(ListWithIdenticalEntries(5,Q));;
i:=1;
GoodOnes := [];
Taken := [];
for q in GPmodKP do
	Info(InfoCW,1,"Doing ",i," from 128\n");
	j := 1;
	found := false;
	for gamma in Taken do
		next := nextGammas(gamma,q);
		if not next = fail then
			Add(GoodOnes,[q,gamma,next!.constraint]);
			found := true;
			break;
		fi;
		Info(InfoCW,1,"Try ",j,"\r");
		j:=j+1;
	od;
	if not found then
		while true do
			gamma := Random(L);
			Info(InfoCW,1,"Not found looking further ",j,"\r");
			next := nextGammas(gamma,q);
			if not next = fail then
				Add(Taken,gamma);
				Add(GoodOnes,[q,gamma,next!.constraint]);
				found := true;
				break;
			fi;
			j:=j+1;
		od;
	fi;
	i:=i+1;
od;
#All chosen gammas have a chance to be solvable
Assert(0,ForAll(GoodOnes,dup->IsOne(f4^dup[2][1]*f4^dup[2][2]*f4^dup[2][3]*f4^dup[2][4]*f4^dup[2][5]*f4*(dup[1]^varpiLP)^isoGmodKtoQ)));
#Write result to a file.
ConjugacyWidthFile := Filename(dir,"PCD/conjugacyConstraints.go");
PrintTo(ConjugacyWidthFile,Concatenation("return ",ReplacedString(String(GoodOnes),"<identity> of ...","One(Q)"),";"));
Assert(0,ReadAsFunction(ConjugacyWidthFile)()=GoodOnes);


#GoodOnes := ReadAsFunction(ConjugacyWidthFile)();
#i := 1;
#for q in GPmodKP do
#	Info(InfoCW,1,"Doing ",i," from 128\r");
#	L:=First(GoodOnes,L->L[1]=q);
#	next := nextGammas(L[2],q);
#	if next = fail then
#		break;
#	fi;
#	i:=i+1;
#od;

