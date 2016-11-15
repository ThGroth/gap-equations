#
#
# Function to compute an element φ in the mcg wich transorm a given γ:F₂ₙ → Q to γ': F₅→Q
# and reduces this further to an element in orbitReps
#
# Implementation takes γ as homomorphism and converts it to a list.
#
GammaSimplify := function(gamma,F)
    local gens, d, L, i, phi,psi,swi,id,imgs,Phi,ph,ActionOnList,x,
    KillBlock,KillAllBlocks,NormalizeBlock,NormalizeAllBlocks,step,
    RepresentativeInOrbitReps;
    if IsGroupHomomorphism(gamma) then
    	F := Source(gamma);
    	gamma := List(GeneratorsOfGroup(F),x->x^gamma);
    fi;
    step := 0; #Variable just for debugging. Remove it!

    #Setup the mcg generators 
    #φᵢ acts on pairs [xᵢ,xᵢ₊₁] (for i odd) 
    #φᵢ acts on pairs [xᵢ₋₁,xᵢ] (for i even)
    #ψᵢ acts on 4 blocks.
    gens := GeneratorsOfGroup(F);
    d := Length(gens);
    phi := [];
    psi := [];
    swi := [];
    id := GroupHomomorphismByImages(F,F,gens);
    for i in [2,4..d] do
        imgs := ShallowCopy(gens);
        imgs[i] := gens[i-1]*gens[i];
        phi[i] := GroupHomomorphismByImages(F,F,imgs);
    od;
    for i in [1,3..d-1] do
        imgs := ShallowCopy(gens);
        imgs[i] := gens[i+1]*gens[i];
        phi[i] := GroupHomomorphismByImages(F,F,imgs);
    od;
    for i in [1,3..d-3] do
        imgs := ShallowCopy(gens);
        x := gens[i+1]/gens[i+2];
        imgs[i] := x*gens[i];
        imgs[i+1] := x*gens[i+1]/x;
        imgs[i+2] := x*gens[i+2]/x;
        imgs[i+3] := x*gens[i+3];
        psi[i] := GroupHomomorphismByImages(F,F,imgs);
    od;

    #added by Thorsten probehably already contained in mcg
    #Switch two neighbouring pairs
    #swi[i]: (q₁,q₂,…,qᵢ,qᵢ₊₁,qᵢ₊₂,qᵢ₊₃,…,qₙ) ↦ (q₁,q₂,…,qᵢ₊₂,qᵢ₊₃,qᵢ,qᵢ₊₁,…,qₙ)
    for i in [1,3..d-3] do
        imgs := ShallowCopy(gens);
        imgs[i+2] := gens[i]^Comm(gens[i+2],gens[i+3]);
        imgs[i+3] := gens[i+1]^Comm(gens[i+2],gens[i+3]);
        imgs[i] := gens[i+2];
        imgs[i+1] := gens[i+3];
        swi[i]:=GroupHomomorphismByImages(F,F,imgs);
    od;

    ActionOnList := function(L,m)
		local Gen, i,j,w,newL ,letter;
		newL := ListWithIdenticalEntries(Length(L),One(L[1]));
		Gen := GeneratorsOfGroup(Source(m));
		for j in [1..Length(L)] do
			w := Gen[j]^m;
			for i in [1..Length(w)] do
				letter := Subword(w,i,i);
				if letter in Gen then
					newL[j]:=newL[j]*L[Position(Gen,letter)];
				else
					newL[j]:=newL[j]/L[Position(Gen,letter^-1)];
				fi;
			od;
		od;
		return newL;
	end;

    #
    # killblock sends blocks of the form (Mod,1,Mod,1) to (Mod,1,1,1)
    #
    KillBlock := function(i,gamma,Mod)
    	local Phi;
    	if IsEvenInt(i) then
    		Error("killblock wrong i");
    	fi;
    	if not gamma[i+1] in Mod or not gamma[i+3] in Mod then
    		Error("killblock wrong gamma");
    	fi;
    	if gamma[i] in Mod then
    		return swi[i];
    	fi;
    	if gamma[i+2] in Mod then
    		return id;
    	fi;
    	if not IsTrivial(Mod) then
    		#So we are in the cyclic two case
    		return swi[i]*phi[i+3]*psi[i];
    	fi;
    	#So we are in cyclic 4
    	if gamma[i]=gamma[i+2] then
    		return swi[i]*phi[i+3]*psi[i];;
    	fi;
    	if ForAll(ActionOnList(gamma,psi[i]^2){[i,i+1]},x->x in Mod) then
    		Phi := swi[i]*psi[i]^2;
    	else
    		Phi := swi[i]*psi[i]^2*swi[i];
    	fi;
    	gamma := ActionOnList(gamma,Phi);
    	return NormalizeBlock(i,gamma,Mod)*Phi;
    end;
    #
    # killallblocks sends gamma of the form (Mod, 1,Mod,1,Mod…) to (Mod,1,1,1,1…)
    # 
    KillAllBlocks := function(offset,gamma,Mod)
    	local Phi,i,phi;
    	if IsEvenInt(offset) then
    		Error("killallblock offset must be odd");
    	fi;
    	Phi := id;
    	for i in [Size(gamma)-3,Size(gamma)-5..offset] do
    		phi := KillBlock(i,gamma,Mod);
    		gamma:= ActionOnList(gamma,phi);
    		Phi :=  phi * Phi;
    	od;
    	return Phi;
    end;
    #
    # NormalizeBlock sends block of the form [G,G] to [G,Mod]
    # 
    NormalizeBlock := function(i,gamma,Mod)
    	local Phi;
    	if IsEvenInt(i) then
    		Error("NormalizeBlock Block index i must be odd");
    	fi;

    	if not IsTrivial(Mod) then #So we are in the cyclic two case
    		if gamma[i+1] in Mod then
    			return id;
    		fi;
    		if gamma[i] in Mod then
    			return phi[i+1]*phi[i];
    		fi;
   			return phi[i+1];
    	else # So we are in the cyclic four case
    		Phi := id;
    		#rule out the cases (1,*) and (x²,x),(x²,x³)
    		if gamma[i] in Mod  or 
    				(gamma{[i,i+1]} = ActionOnList(gamma{[i,i+1]},phi[2]^2)
    				and not ActionOnList(gamma{[i,i+1]},phi[2])[2] in Mod)
    				then 
    			Phi := phi[i]* Phi  ;
    			gamma := ActionOnList(gamma,phi[i]);
    			#so now gamma[i] ≠ 1 and not other problematic one.
    		fi;
    		while not gamma[i+1] in Mod do
    			Phi := phi[i+1]*Phi;
    			gamma := ActionOnList(gamma,phi[i+1]);
    		od;
    		# rule out one additional case: 
    		# A representative system for the action of MCG on C₂² 
    		# is (1,1), (ad³,1) (ad²,1) as (ad³,1)~(ad,1)
    		if gamma[i] = GeneratorsOfGroup(C2)[1] then
    			return phi[i+1]*phi[i]^2*phi[i+1]*Phi;
    		fi;
    		return Phi;
    	fi;
    end;
    NormalizeAllBlocks := function(offset,gamma,Mod)
    	local Phi;
   		if IsEvenInt(offset) then
    		Error("NormalizeAllBlocks offset i must be odd");
    	fi;	
    	Phi := id;
    	for i in [offset,offset+2..Size(gamma)-1] do
    		Phi := NormalizeBlock(i,gamma,Mod) * Phi;
    	od;
    	return Phi;
    end;
    # given γ:F₅→Q
	# Returns the element γᵣ in orbitReps such that 
	# γ and γᵣ are in the same orbit under the mcg
	# 
	#
	RepresentativeInOrbitReps := function(gamma)
		local hash;
		hash := function(q)
			if q in Q then
				return Position(List(Q),q);
			else 
				Error("Can't compute hash ",q," is not in Q.");
			fi;
		end;
		return orbitTable[hash(gamma[1])][hash(gamma[2])][hash(gamma[3])][hash(gamma[4])][hash(gamma[5])];
	end;

    #Now do the real work...
    Phi := id;
    ph := NormalizeAllBlocks(1,gamma,C1);
   	Phi := ph;

    gamma := ActionOnList(gamma,ph); # (Q,C1,Q,C1,Q,C1,Q,C1…)
    Assert(2,ForAll(gamma{[2,4..Size(gamma)]},x->x in C1));
    step := 1;

    ph := KillAllBlocks(1,gamma,C1);
	#	Phi := ph*Phi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C1,C1,C1,C1,C1…)
    Assert(2,ForAll(gamma{[2..Size(gamma)]},x->x in C1));
    step := 2;

	ph := NormalizeAllBlocks(3,gamma,C2);
	#	Phi := ph*Phi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C1,C2,C1,C2,C1,C2…)
    Assert(2,ForAll(gamma{[4,6..Size(gamma)]},x->x in C2));
    step := 3;

    ph := KillAllBlocks(3,gamma,C2);
	#	Phi := ph*Phi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C2,C2,C2,C2,C2,C2…)
    Assert(2,ForAll(gamma{[4..Size(gamma)]},x->x in C2));
    step := 4;

    ph := NormalizeAllBlocks(5,gamma,Group(One(C1))); #Trivial Mod
	#	Phi := ph*Phi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C2,1,C2,1,C2,1…)
    Assert(2,ForAll(gamma{[6,8..Size(gamma)]},IsOne));
    step := 5;

	ph := KillAllBlocks(5,gamma,Group(One(C1))); #Trivial Mod
	#	Phi := ph*Phi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C2,1,1,1,1,1…)
    Assert(2,ForAll(gamma{[6..Size(gamma)]},IsOne));
    step := 6;

	#   Assert(2,surface_relator(F)^Phi=surface_relator(F));
	#Finally chose representing element.
	#
	#no Lookup:
	#return gamma{[1..6]};
	#
    return orbitReps[RepresentativeInOrbitReps(gamma{[1..5]})];
end;
F6 := FreeGroup(6);
#Test whether (g,γ) is a good pair.
IsGoodPair := function(q,gamma)
    if not q in GPmodKP then
        Info(InfoFRGW,2,"work mod KP\n");
        if not q in GLP then
            q := q^isoGtoGLP;
        fi;
        q := q^tauLP;
    fi;
    if not gamma in orbitReps then
        gamma := GammaSimplify(gamma,F6);
    fi;
    return q in AGP[Position(orbitReps,gamma)];
end;
#For q in G'/K'
#Get List of all γ∈OrbitReps such that (q,γ) is a good pair.
GetAllGoodGammas := function(q)
    local i,GoodGammas;
    GoodGammas := [];
    for i in [1..Size(AGP)] do
        if q in AGP[i] then
            Add(GoodGammas,orbitReps[i]);
        fi;
    od;
    return GoodGammas;
end;

GetNext:= function(g,gamma)
    local gaP,q,inLP,next;
    #Compute the image of g in G'/K' if not already in G'/K'
    if g in G then
        q:= (g^isoGtoGLP)^tauLP; 
        inLP := false;
    elif g in GLP then
        q:= g^tauLP;
        g:= g^isoGPLtoG;
        inLP := true;
    else 
        Error("g has to be in G or GLP\n");
    fi;
    gamma:= GammaSimplify(gamma,FreeGroup(6));
    if not IsGoodPair(q,gamma) then
        Error("(q,gamma) needs to be a good pair.\n");
    fi;
    if HasNontrivialActivity(gamma) then
        gaP := First(RGP,L->L[1]=q and L[2]=gamma)[3];
        next := [State(g,2)^PreImagesRepresentative(pi,gaP[2])*State(g,1),gaP[1]];
        if inLP then
            next[1] := next[1]^isoGtoGLP;
        fi;
        return next;
    else
        Error("gamma has no activity\n");
    fi;
end;

FindGoodGamma := function(g)
    local q;
    if g in G then
        q:= (g^isoGtoGLP)^tauLP; 
    elif g in GLP then
        q:= g^tauLP;
        g:= g^isoGPLtoG;
    else 
        Error("g has to be in G or GLP\n");
    fi;
    if not q in GPmodKP then
        return fail;
    fi;
    return nontrivialGammas[PositionProperty(AGPnontrivial,L->q in L)];
end;

findCycle:= function(g)
    local All,gamma,L;
    gamma := FindGoodGamma(g);
    All := [g,gamma];
    while true do
        L:=GetNext(g,gamma);
        if L in All then
            return All;
        fi;
        Add(All,L);
        g:=L[1];gamma:=L[2];
    od;
end;