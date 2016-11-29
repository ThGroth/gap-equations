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
	local Gamma1,Dep,i,ga,first,gp,acts,num,frvars,frinvvars,t,ac,newwords,U,NoFI,q1,q2,NoFIhom,trans,GHOnList,H,gpp,gaP,Suc;
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
	#statements
	acts := ActivityConstraint(gamma);
	num := 5;
	frvars := List([1..num],x->FRGrpWordUnknown(3*x,acts[x],GrigorchukGroup));
	frinvvars := List([1..num],x->FRGrpWordUnknown(-3*x,acts[x],GrigorchukGroup));
	t := Product(List([1..num],y->frinvvars[y]*a*frvars[y]))*a;
	#Remove the trivial G elements from the group word
	Apply(t!.states,w->GrpWordReducedForm(w));

	newwords := ShallowCopy(t!.states);
	#F2 := FreeGroup(2); g1:=F2.1;g2:=F2.2;
	#ac := f1*f3; #
	#q1 := ac^m;
	#q2 := ac^-m;
	q1:= StateLP(q,1)^isoGmodKtoQ;
	q2:= StateLP(q,2)^isoGmodKtoQ;
	newwords[1]!.group := Q;
	newwords[2]!.group := Q;
	newwords[1] := newwords[1]*GrpWord([q1],Q);
	newwords[2] := newwords[2]*GrpWord([q2],Q);
	#<<u₁xu₂,v₁x⁻¹v₂>> ↦ <<u₁v₁v₂uᵤ,1>>
	U := Uniquify(newwords)[1];
	Assert(0,IsOne(U[2]));
	NoFI := GrpWordNormalFormInverseHom(U[1]);
	#g@2⋅g@1 = 1 mod Q.
	Assert(0,NoFI[1]!.word=[-1,-2,1,2,-3,-4,3,4]);
	NoFIhom := GrpWordHom(NoFI[2]!.rules{[1..4]},Q);
	trans := function(n)
		return 3+n+Int((n-1)/2);
	end;
	GHOnList := function(hom,gam)
		#hom should be a grpWordHom Fₓ → Fₓ ∗ {g₁,g₂}
		local newgam,i,r;
		newgam := ListWithIdenticalEntries(Size(hom!.rules),One(Q));

		for i in [1..Size(gam)] do
			if IsBound(hom!.rules[i]) then
				for r in hom!.rules[i]!.word do
					if IsInt(r) then
						if r>0 then
							newgam[i] := newgam[i]*gam[r];
						else
							newgam[i] := newgam[i]*(gam[-r])^-1;
						fi;
					else
						newgam[i] := newgam[i]*r;	
					fi;
				od;
			fi;
		od;
		return newgam;
	end;
	for gp in Gamma1 do
		H := [];
		for i in [1..Size(gp)] do
			H[trans(i)] := GrpWord([gp[i]],Q);
		od;
		H := GrpWordHom(H,Q);

		if IsOne(ImageOfGrpWordHom(H,t!.states[1])*GrpWord([q1],Q)) and IsOne(ImageOfGrpWordHom(H,t!.states[2])*GrpWord([q2],Q)) then
			gpp := [];
			for i in [1..Size(gp)] do
				if IsBound(gp[i]) then
					gpp[trans(i)]:=gp[i];
				fi;
			od;
			#return GHOnList(NoFIhom,gpp);
    		#Compute the image of γ' under the normalization hommorphism and simplify it to the F₅ case
    		gaP := MakeImmutable(ReducedConstraint(GHOnList(NoFIhom,gpp)));
    		#return gaP.index;
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
for q in GPmodKP do
	Print("Doing ",i," from 128\n");
	j := 1;
	found := false;
	for gamma in PCD.orbitReps do
		gamma := gamma{[1..5]};
		#gamma := Random(L);
		next := nextGammas(gamma,q);
		if not next = fail then
			Add(GoodOnes,[q,gamma,next!.constraint]);
			found := true;
			break;
		fi;
		Print("Try ",j,"\r");
		j:=j+1;
	od;
	if not found then
		while true do
			gamma := Random(L);
			Print("Not found looking further ",j,"\r");
			next := nextGammas(gamma,q);
			if not next = fail then
				Add(GoodOnes,[q,gamma,next!.constraint]);
				found := true;
				break;
			fi;
			j:=j+1;
		od;
	fi;
	i:=i+1;
od;


#Show how succeccing pairs look like


num := 4;
F2 := FreeGroup(2); g1:=F2.1;g2:=F2.2;
Acts := Cartesian(ListWithIdenticalEntries(num,[(),(1,2)]));
for acts in Acts do
	frvars := List([1..num],x->FRGrpWordUnknown(3*x,acts[x],GrigorchukGroup));
	frinvvars := List([1..num],x->FRGrpWordUnknown(-3*x,acts[x],GrigorchukGroup));
	t := Product(List([1..num],y->frinvvars[y]*a*frvars[y]));
	#I := Intersection(List(Filtered(t!.states[1]!.word,IsInt),AbsInt),List(Filtered(t!.states[2]!.word,IsInt),AbsInt));
	newwords := t!.states;
	newwords[1] := newwords[1]*GrpWord([g1],F2);
	newwords[2] := newwords[2]*GrpWord([g2],F2);
	U := Uniquify(newwords)[1];
	Assert(0,IsOne(U[2]));
	NoFI := GrpWordNormalFormInverseHom(U[1]);
	Print(acts,": ",NoFI[1]!.word,"\n");
od;