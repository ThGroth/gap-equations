#
# Directory where the Saved results are as specified in ComputeOrbit. Needs a trailing /
#
dir := "~/Repositories/git/GrigorchukCommutator/90orbs/";
Read("/home/thorsten/Repositories/git/GrigorchukCommutator/grpwords/grpwords.gd");
Read("/home/thorsten/Repositories/git/GrigorchukCommutator/grpwords/grpwords.gi");

dir := "~/Repositories/GrigorchukCommutator/90orbs/";
Read("/home/tgroth/Repositories/GrigorchukCommutator/grpwords/grpwords.gd");
Read("/home/tgroth/Repositories/GrigorchukCommutator/grpwords/grpwords.git");

#Set up all Branchstructure, quotients etc.
#Working with L presentation
G := GrigorchukGroup;
a := G.1; b := G.2; c := G.3; d:=G.4;
isoGtoGLP := IsomorphismLpGroup(G);
isoGPLtoG := InverseGeneralMapping(isoGtoGLP);
GLP := Image(isoGtoGLP);
aL := GLP.1; bL := GLP.2; cL := GLP.3; dL:=GLP.4;
k1 := (aL*bL)^2; k2 := (aL*bL*aL*dL)^2; k3 := (bL*aL*dL*aL)^2;
GPGen := [k1,k3,k2,(aL*dL)^2];
GpLP := Subgroup(GLP,GPGen);
Gp := Group((a*b)^2,(a*b*a*d)^2,(b*a*d*a)^2,(a*d)^2);
LGen := [k2,k3,bL,aL*bL*aL];
LLP := Subgroup(GLP,LGen);
KGen := [k1,k3,k2];
KLP := Subgroup(GLP,KGen);
KxKGen := [k2,k3,Comm(k2^-1,k1),Comm(k2,k1^-1),Comm(k2^-1,k1)^aL,Comm(k2,k1^-1)^aL];
KxKLP := Subgroup(GLP,KxKGen);
GenKPLP := [(dL*aL*cL*aL*bL*aL*cL*aL)^2*(bL*aL*cL*aL)^4,((cL*aL)^2*bL*aL*cL*aL)^2,(dL*aL*cL*aL*bL*aL*cL*aL)^2*cL*(aL*cL*aL*bL)^3*aL*cL*aL*dL,((aL*cL)^3*aL*bL)^2, (bL*aL*cL*aL)*dL*aL*cL*aL*bL*(aL*cL)^2*(aL*cL*aL*bL)^3, (aL*cL*aL*dL*aL*cL*aL*bL)^2*(aL*cL*aL*bL)^4];
AllGenKPLP := [];
for h in GenKPLP do
	Add(AllGenKPLP,h);
	Add(AllGenKPLP,h^aL);
od;
KPLP := Subgroup(GLP,AllGenKPLP);
piLP := NaturalHomomorphismByNormalSubgroup(GLP,KLP);
tauLP := NaturalHomomorphismByNormalSubgroup(GLP,KPLP);
homGtoGmodKxK := NaturalHomomorphismByNormalSubgroup(GLP,KxKLP);;
GmodKP := Image(tauLP);;
GmodK := Image(piLP);;
GPmodKP := Group(List(GPGen,g->g^tauLP));;
KmodKP := Group(List(KGen,g->g^tauLP));;
KxKmodKP := Group(List(KxKGen,g->g^tauLP));;
GmodKxK := Image(homGtoGmodKxK);
varpiLP := NaturalHomomorphismByNormalSubgroup(GmodKP,KmodKP);;
varpiLP := varpiLP*IsomorphismGroups(Image(varpiLP),GmodK) ;; 
varpiPrimeLP := NaturalHomomorphismByNormalSubgroup(GmodKP,KxKmodKP);;
varpiPrimeLP := varpiPrimeLP*IsomorphismGroups(Image(varpiPrimeLP),GmodKxK);; 

AnGpLPElement := function()
	local n,g;
	g := One(GpLP);
	for n in [1..Random([1..100])] do
		g := g*Random(GPGen);
	od;
	return g;
end;
	#statements
end

Assert(0,ForAll(GenKPLP,x->ForAll([1,2],i->State(x^isoGPLtoG,i)^isoGtoGLP in KxKLP)));
#the map pₕ: G'/K' → G'/K×K, gK' ↦ ((g@2)ʰ⋅g@1)K×K is well defined
p_h := function(q,h)
	local g;
	if not q in GmodKP then
		Error("q needs to be in G/K'");
	fi;
	if not h in G then
		Error("h needs to be in G");
	fi;
	g := PreImagesRepresentative(tauLP,q)^isoGPLtoG;
	return ((State(g,2)^h*State(g,1))^isoGtoGLP)^homGtoGmodKxK;
end;
# p = p₁
p := function(q)
	local g;
	if not q in GmodKP then
		Error("q needs to be in G/K'");
	fi;
	g := PreImagesRepresentative(tauLP,q)^isoGPLtoG;
	return ((State(g,2)*State(g,1))^isoGtoGLP)^homGtoGmodKxK;
end;
#the maps @i: G'/K' → G'/K, gK' ↦ g@i K are well defined
StateLP := function(q,i)
	if not q in GmodKP then
		Error("State: q needs to be in G/K'");
	fi;
	return (State(PreImagesRepresentative(tauLP,q)^isoGPLtoG,i)^isoGtoGLP)^piLP;
end;

BS := BranchStructure(G);
Q := BS.group;
w := BS.epi;
pi := BS.quo;
F := BS.wreath;
Q := Image(pi);
AssignGeneratorVariables(G);
f4:= Q.1; # = ā 
f2 := Q.2; # = b
f1 := Q.3; # = c̄
f3 := f1*f2*f4*f1*f2; # = dād
A := Filtered(List(Q),x->Activity(PreImagesRepresentative(pi,x))=(1,2));
AC := Filtered(List(Q),x->Activity(PreImagesRepresentative(pi,x))=());

ab := f4;
bb := f2;
cb := f1;
db := f1*f2;


ad := ab*db;

C1 := Group(a^pi,d^pi);
C2 := Group((a*d)^pi);

#This leads to problem, becaus it's the wrong iso...
#isoQtoGmodK := IsomorphismGroups(Q,GmodK);
#isoGmodKtoQ := IsomorphismGroups(GmodK,Q);

isoQtoGmodK :=GroupHomomorphismByImages(Q,GmodK,[f1,f2,f4],List([c,b,a],x->(x^isoGtoGLP)^piLP));
isoGmodKtoQ :=GroupHomomorphismByImages(GmodK,Q,List([c,b,a],x->(x^isoGtoGLP)^piLP),[f1,f2,f4]);

goodPairs := function(gamma)
	local S1,S2,S3,F,P,P2,p,q,r;
	if ForAny(gamma,q-> not q in GmodK) then
		gamma:=List(gamma,q->q^isoQtoGmodK);
	fi;
	S1 := [];
	S2 := [];
	S3 := [];
	P := PreImages(varpiLP,gamma[1]);
	P2 := PreImages(varpiLP,gamma[2]);
	for p in P do
		for q in P2 do
			AddSet(S1,Comm(p,q));
		od;
	od;	
	P := PreImages(varpiLP,gamma[3]);
	P2 := PreImages(varpiLP,gamma[4]);
	for p in P do
		for q in P2 do
			AddSet(S2,Comm(p,q));
		od;
	od;	
	P := PreImages(varpiLP,gamma[5]);
	P2 := PreImages(varpiLP,gamma[6]);
	for p in P do
		for q in P2 do
			AddSet(S3,Comm(p,q));
		od;
	od;
	F := [];
	for p in S1 do for q in S2 do for r in S3 do
		AddSet(F,(p*q*r)^-1);
	od;od;od;
	return F;
end;

GetAllGoodPairs := function(AllGammas)
	local AGP, gamma;
	AGP := [];
	for gamma in AllGammas do
		Add(AGP,goodPairs(gamma));
	od;
	return AGP;
end;

#Load orbits here:
orbitReps := ReadAsFunction(Concatenation(dir,"orbitReps.go"))();;
orbitTable := ReadAsFunction(Concatenation(dir,"orbitTable.go"))();;
#Takes 1 min
AGP := GetAllGoodPairs(orbitReps);;

# γ: Fₙ→Q is mapped to Act(γ): Fₙ→ {(),(1,2)}
#
ActivityGamma := function(gamma)
	return List(gamma,x->Activity(PreImagesRepresentative(pi,x)));
end;
HasNontrivialActivity := function(gamma)
	return not ForAll(ActivityGamma(gamma),IsOne);
end;
nontrivialGammas := Filtered(orbitReps,HasNontrivialActivity);
#Takes 1 min
AGPnontrivial := GetAllGoodPairs(nontrivialGammas);;

#Make sure that forach q in G'/K' there is a good active pair involving q.
Assert(0,ForAll(GPmodKP,q->ForAny(AGPnontrivial,L->q in L)));


GammaForR2 := Filtered(orbitReps,L->IsOne(L[5]));
GammaForR2Active := Filtered(nontrivialGammas,L->IsOne(L[5]));
AGPForR2 := GetAllGoodPairs(GammaForR2);;
AGPForR2Active := GetAllGoodPairs(GammaForR2Active);;
#Make sure that forach q in G'/K' there is a good active pair active only on first 4.
Badqs := [];
for q in GPmodKP do
	found := false;
	for L in AGPForR2Active do
		if q in L then
			found := true;
			break;
		fi;
	od;
	if not found then
		Add(Badqs,q);
	fi;
od;

Assert(0,ForAll(GPmodKP,q->ForAny(AGPForR2,L->q in L)));



surface_relator := function(F)
    local gens;
    gens := GeneratorsOfGroup(F);
    return Product([2,4..Length(gens)],i->Comm(gens[i-1],gens[i]),One(F));
end;

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

#
# Given a good pair (q,γ) where γ has nontrivial activity 
# 
# This method tries to compute a pair (γ',x) with the following property:
# ̇ γ' has nontrivial activity
# ̇ forall g with g^τ=q 
# 	the sattisfiabillity of (R₂ₙ-₁ (g@2)^x ⋅ g@1 ,γ') implies the 
# 	sattisfiabillity of Rₙg,γ
# ̇ (γ',(g@2)^x ⋅ g@1) is a good pair 
# 
# If the search for such a pair fails, the method returns fail, this doesn't 
# mean that such a pair does not exists.
# 
#
CompGammaCheckInkl := function(q,gamma)
	local Gamma1,g1,g2,F2,F,GammAPrime,count,acts,frvars, frinvvars,
		t,I,x,v,w,indx,v1,v2,w1,w2,newEq,NoFI,NoFIhom,z,GHOnList,gam,
		Dep,i,g,first,gp,gpp,trans,H,normalforms,nf,gaP,q1,q2;

	if Size(gamma)>6 then
		#gamma := GammaSimplify(gamma,F6);
		Error("gamma is too large!\n");
	elif Size(gamma)=5  then
		Append(gamma,One(gamma[1]));
	elif Size(gamma)<4  then
		Error("gamma is too small!\n");
	fi;
	if not q in GmodKP then
		Error("q has to be in G/K'\n");
	fi;
		
	q1:= StateLP(q,1)^isoGmodKtoQ;
	q2:= StateLP(q,2)^isoGmodKtoQ;
	F := FreeGroup(4*3-2);
	acts := ActivityGamma(gamma);

	if ForAll(acts,IsOne) then
		#act(γ) = (1,1,1…1) doesn't help
		Print("gamma need to have activity in some component");
		return[];
	fi;
	
	F2 := FreeGroup(2); g1:=F2.1;g2:=F2.2;
	frvars := List([1..6],x->FRGrpWordUnknown(3*x,acts[x],GrigorchukGroup));
	frinvvars := List([1..6],x->FRGrpWordUnknown(-3*x,acts[x],GrigorchukGroup));
	t := Product(List(Filtered([1..Size(gamma)],IsOddInt),y->frinvvars[y]*frinvvars[y+1]*frvars[y]*frvars[y+1]));
	I := Intersection(List(t!.states[1]!.word,AbsInt),List(t!.states[2]!.word,AbsInt));
	#I is nonempty as #act(γ) ≠ (1,1,1…1)
	#x := I[1]; #What if we choose something different here?
	#We now do. We take all.
	normalforms := [];
	for x in I do
		v := t!.states[1]!.word;
		w := t!.states[2]!.word;
		indx := Position(List(v,AbsInt),x);
		v1 := v{[1..indx-1]};
		v2 := v{[indx+1..Size(v)]};
		indx := Position(List(w,AbsInt),x);
		w1 := w{[1..indx-1]};
		w2 := w{[indx+1..Size(w)]};
		newEq := GrpWord(Concatenation(v1,w2,[g2],w1,v2,[g1]),F2);
		NoFI := GrpWordNormalFormInverseHom(newEq);
		NoFIhom := GrpWordHom(NoFI[2]!.rules{[1..4*3-1]});
		#z consist only of one element
		z := NoFIhom!.rules[4*3-1]!.word; #z=x₁₁
		Assert(0,Size(z)=1);
		z := z[1];
		Add(normalforms,[z,NoFIhom]);
	od;
		
	#Compute the image of a G-Homomorphism with values in F₄ₙ ∗ {g₁,g₂} 
	#of a γ ∈ Γ' mod K 
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
						if r = g1 then
							newgam[i] := newgam[i]*q1;	
						elif r = g2 then #r = g2
							newgam[i] := newgam[i]*q2;	
						elif r = g1^-1 then
							newgam[i] := newgam[i]*q1^-1;	
						elif r = g2^-1 then #r = g2
							newgam[i] := newgam[i]*q2^-1;	
						else
							Error("Compute GammAPrime Well this shouldn't happen...");
						fi;
					fi;
				od;
			fi;
		od;
		return newgam;
	end;
	Gamma1 := []; 
	Dep := [];
	i := 1;
	for ga in gamma do
		first := true;
		Add(Dep,[2*i-1,2*i]); i := i+1;
		for gp in PreImages(BS.epi,ga) do
			if true then
				if first then
					Add(Gamma1,[gp![1]]);
					Add(Gamma1,[gp![2]]);
					first := false;
				else
					Add(Gamma1[Size(Gamma1)-1],gp![1]);
					Add(Gamma1[Size(Gamma1)],gp![2]);
				fi;	
			fi;
		od;
	od;
	Gamma1 := DEP_CARTESIAN@fr(Gamma1,Dep);;#Size of Gamma1 about 4096
	trans := function(n)
		return 3+n+Int((n-1)/2);
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
			for nf in normalforms do
				z := nf[1];
				NoFIhom := nf[2];
				#Compute the image of γ' under the normalization hommorphism and simplify it to the F₅ case
				gaP := [MakeImmutable(GammaSimplify(GHOnList(NoFIhom,gpp){[1..4*3-2]},F)),gpp[AbsInt(z)]];
				Suc := List(PreImages(varpiPrimeLP,p_h(q,PreImagesRepresentative(pi,gaP[2]))));
				#Added check for nontrivial activity.
				if HasNontrivialActivity(gaP[1]) and ForAll(Suc, r->IsGoodPair(r,gaP[1])) then
					return gaP;
				fi;
				#Print(count," of ",Size(Gamma1)," done. Size of Gamma3 is now ",Size(Gamma3),".\r");
			od;
		fi;
	od;
	return fail;
end;


CompGammaCheckInklAllowedx := function(q,gamma,Allowedx)
	local Gamma1,g1,g2,F2,F,GammAPrime,count,acts,frvars, frinvvars,
		t,I,x,v,w,indx,v1,v2,w1,w2,newEq,NoFI,NoFIhom,z,GHOnList,gam,
		Dep,i,g,first,gp,gpp,trans,H,normalforms,nf,gaP,q1,q2;

	if Size(gamma)>6 then
		#gamma := GammaSimplify(gamma,F6);
		Error("gamma is too large!\n");
	elif Size(gamma)=5  then
		Append(gamma,One(gamma[1]));
	elif Size(gamma)<4  then
		Error("gamma is too small!\n");
	fi;
	if not q in GmodKP then
		Error("q has to be in G/K'\n");
	fi;
		
	q1:= StateLP(q,1)^isoGmodKtoQ;
	q2:= StateLP(q,2)^isoGmodKtoQ;
	F := FreeGroup(4*3-2);
	acts := ActivityGamma(gamma);

	if ForAll(acts,IsOne) then
		#act(γ) = (1,1,1…1) doesn't help
		Print("gamma need to have activity in some component");
		return[];
	fi;
	
	F2 := FreeGroup(2); g1:=F2.1;g2:=F2.2;
	frvars := List([1..6],x->FRGrpWordUnknown(3*x,acts[x],GrigorchukGroup));
	frinvvars := List([1..6],x->FRGrpWordUnknown(-3*x,acts[x],GrigorchukGroup));
	t := Product(List(Filtered([1..Size(gamma)],IsOddInt),y->frinvvars[y]*frinvvars[y+1]*frvars[y]*frvars[y+1]));
	I := Intersection(List(t!.states[1]!.word,AbsInt),List(t!.states[2]!.word,AbsInt));
	#I is nonempty as #act(γ) ≠ (1,1,1…1)
	#x := I[1]; #What if we choose something different here?
	#We now do. We take all.
	normalforms := [];
	for x in I do
		v := t!.states[1]!.word;
		w := t!.states[2]!.word;
		indx := Position(List(v,AbsInt),x);
		v1 := v{[1..indx-1]};
		v2 := v{[indx+1..Size(v)]};
		indx := Position(List(w,AbsInt),x);
		w1 := w{[1..indx-1]};
		w2 := w{[indx+1..Size(w)]};
		newEq := GrpWord(Concatenation(v1,w2,[g2],w1,v2,[g1]),F2);
		NoFI := GrpWordNormalFormInverseHom(newEq);
		NoFIhom := GrpWordHom(NoFI[2]!.rules{[1..4*3-1]});
		#z consist only of one element
		z := NoFIhom!.rules[4*3-1]!.word; #z=x₁₁
		Assert(0,Size(z)=1);
		z := z[1];
		Add(normalforms,[z,NoFIhom]);
	od;
		
	#Compute the image of a G-Homomorphism with values in F₄ₙ ∗ {g₁,g₂} 
	#of a γ ∈ Γ' mod K 
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
						if r = g1 then
							newgam[i] := newgam[i]*q1;	
						elif r = g2 then #r = g2
							newgam[i] := newgam[i]*q2;	
						elif r = g1^-1 then
							newgam[i] := newgam[i]*q1^-1;	
						elif r = g2^-1 then #r = g2
							newgam[i] := newgam[i]*q2^-1;	
						else
							Error("Compute GammAPrime Well this shouldn't happen...");
						fi;
					fi;
				od;
			fi;
		od;
		return newgam;
	end;
	Gamma1 := []; 
	Dep := [];
	i := 1;
	for ga in gamma do
		first := true;
		Add(Dep,[2*i-1,2*i]); i := i+1;
		for gp in PreImages(BS.epi,ga) do
			if true then
				if first then
					Add(Gamma1,[gp![1]]);
					Add(Gamma1,[gp![2]]);
					first := false;
				else
					Add(Gamma1[Size(Gamma1)-1],gp![1]);
					Add(Gamma1[Size(Gamma1)],gp![2]);
				fi;	
			fi;
		od;
	od;
	Gamma1 := DEP_CARTESIAN@fr(Gamma1,Dep);;#Size of Gamma1 about 4096
	trans := function(n)
		return 3+n+Int((n-1)/2);
	end;
	count := 0;
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
			for nf in normalforms do
				z := nf[1];
				NoFIhom := nf[2];
				#Compute the image of γ' under the normalization hommorphism and simplify it to the F₅ case
				if gpp[AbsInt(z)] in Allowedx then
					
					gaP := [MakeImmutable(GammaSimplify(GHOnList(NoFIhom,gpp){[1..4*3-2]},F)),gpp[AbsInt(z)]];
					Suc := List(PreImages(varpiPrimeLP,p_h(q,PreImagesRepresentative(pi,gaP[2]))));
					Add(gaP,Suc);
					#Added check for nontrivial activity.
					if HasNontrivialActivity(gaP[1]) and ForAll(Suc, r->IsGoodPair(r,gaP[1])) then
						return gaP;
					fi;
				fi;
				#Print(count," of ",Size(Gamma1)," done. Size of Gamma3 is now ",Size(Gamma3),".\r");
				#count := count+1;
			od;
		fi;
	od;
	return fail;
end;

#
#
# Doing stuff for allwed x
# Get good and bad pairs
#The following takes about 10 hours...
#
BadPairs := [];
countGoodOnes := 0;
size := Sum(List(AGP,Size));
count := 0;
RealRealGoodPairs := [];
for gamma in nontrivialGammas do
	k := Position(orbitReps,gamma);
	for q in AGP[k] do
		gammap := CompGammaCheckInklAllowedx(q,gamma,[One(Q)]);
			if not gammap = fail then
				countGoodOnes := countGoodOnes+1;
				Add(RealRealGoodPairs,[q,gamma,gammap]);
			else
				Add(BadPairs,[q,gamma]);
			fi;
			Print("For ",Allowedx,": ",Int(count*100/size),"% done. ",countGoodOnes," good ones so far.", Size(RealGoodPairsByAllowedx)," good Allowedx.\r");
			count := count+1;
		od;
	od;
od;

GoodPairs := [];
countq := 1;
size := Size(BadPairs);
for q in Q do
	if IsOne(q) then
		countq := countq +1;
		continue;
	fi;
	RealGoodPairsq := [];
	count := 0;
	for L in BadPairs do
		gammap := CompGammaCheckInklAllowedx(L[1],L[2],[q]);
		if not gammap = fail then
				Add(RealGoodPairsq,[L,gammap]);
		fi;
		Print("For ",q," (",countq,"/16): ",Int(count*100/size),"% done. ",Size(RealGoodPairsq)," good ones so far.", "\r");
		count := count+1;
	od;
	Add(GoodPairs,RealGoodPairsq);
	countq := countq +1;
od;
GoodCombis := [];
for L in Combinations([1..15]) do
	if Size(L) = 7 then
		All := [];
		for l in L do
			for elm in GoodPairs[l] do
				if not elm[1] in All then
					Add(All,elm[1]);
				fi; 
			od;
		od;
		#Print(Size(All));
		if Size(All) = Size(BadPairs) then
			Add(GoodCombis,L);
		fi;
	fi;
od;
Size(GoodCombis);
RGP2 := [];
RGP2Starts := [];
count := 0;
for P in RealRealGoodPairs do	
	Add(RGP2,[[P[1],P[2]],P[3]]);
	Add(RGP2Starts,[P[1],P[2]]);
	count := count +1;
od;
Print(count,"\n");
for i in [1,4,8,12,5,14,9] do
	count := 0;
	for P in GoodPairs[i] do
		if not P[1] in RGP2Starts then
			Add(RGP2Starts,P[1]);
			Add(RGP2,P);
			count := count +1;
		fi;
	od;
	Print(count,"\n");
od;
Size(RGP2);

List(GPmodKP,q->Size(Filtered(RealRealGoodPairs,R->R[1]=q)));

#Good descendent gammas
DescGamma1 := Set(List(RGP,P->P[3][1]));;
DescGamma2 := [];;
for gamm in DescGamma1 do
	Append(DescGamma2,Set(Filtered(RGP,P->P[2]=gamm),P->P[3][1]));
od;
DescGamma2 := Set(DescGamma2);;
Size(DescGamma2);
DescGamma3 := [];;
for gamm in DescGamma2 do
	Append(DescGamma3,Set(Filtered(RGP,P->P[2]=gamm),P->P[3][1]));
od;
DescGamma3 := Set(DescGamma3);
Size(DescGamma3);

oldsize := 60;
DescGamma := Set(List(RealGoodPairs,P->P[3][1]));;
while true do
	DescGamma2 := [];;
	oldsize := Size(DescGamma);
	for gamm in DescGamma do
		Append(DescGamma2,Set(Filtered(RGP,P->P[2]=gamm),P->P[3][1]));
	od;
	DescGamma2 := Set(DescGamma2);
	if DescGamma = DescGamma2 then
		break;
	fi;	
	DescGamma := Set(DescGamma2);
	Print("Size: ",Size(DescGamma),"\n");
od;
List(Filtered(RGP,P->P[2] in DescGamma),P->P[1]);

#The following takes about an hour
countGoodOnes := 0;
countBadOnes := 0;
size := Sum(List(AGP,Size));
count := 0;
RealGoodPairs := [];
BadPairs := [];
for gamma in nontrivialGammas do
	k := Position(orbitReps,gamma);
	for q in AGP[k] do
		gammap := CompGammaCheckInkl(q,gamma);
		if not gammap = fail then
			countGoodOnes := countGoodOnes+1;
			Add(RealGoodPairs,[q,gamma,gammap]);
		else
			countBadOnes := countBadOnes+1;
			Add(BadPairs,[q,gamma]);
		fi;
		Print(Int(count*100/size),"% done. ",countGoodOnes," good ones so far and ",countBadOnes," bad ones.\r");
		count := count+1;
	od;
od;
Print("\n",Size(BadPairs),"\n\n");

###################################################################################################
############################                     ##################################################
############################   Smaller Set S     ##################################################
############################                     ##################################################
###################################################################################################
#
#
#Doing it again for a good choice of allowedX and remember succecor q's:
countGoodOnes := 0;
countBadOnes := 0;
size := Sum(List(AGP,Size));
count := 0;
RealGoodPairs := [];
BadPairs := [];
Allowedx := List(Q){[1,2,5,9,13,6,15,10]}; # = [1,a,b,c,d,ab,ad,ba]
for gamma in nontrivialGammas do
	k := Position(orbitReps,gamma);
	for q in AGP[k] do
		gammap := CompGammaCheckInklAllowedx(q,gamma,Allowedx);
			if not gammap = fail then
				countGoodOnes := countGoodOnes+1;
				Add(RealGoodPairs,[q,gamma,gammap]);
			else
				countBadOnes := countBadOnes+1;
				Add(BadPairs,[q,gamma]);
			fi;
			Print(Int(count*100/size),"% done. ",countGoodOnes," good ones so far and ",countBadOnes," bad ones.\r");
			count := count+1;
		od;
	od;
od;
###################################################################################################
############################                     ##################################################
############################   Playing around    ##################################################
############################  not nec. anymore   ##################################################
#############################    get Graph       ##################################################
############################                     ##################################################
###################################################################################################
#

List(Allowedx,x->Size(Filtered(RealGoodPairs,P->P[3][2]=x)));

DescGamma := Set(List(RealGoodPairs,P->P[3][1]));;
while true do
	DescGamma2 := [];;
	oldsize := Size(DescGamma);
	for gamm in DescGamma do
		Append(DescGamma2,Set(Filtered(RealGoodPairs,P->P[2]=gamm),P->P[3][1]));
	od;
	DescGamma2 := Set(DescGamma2);
	if DescGamma = DescGamma2 then
		break;
	fi;	
	DescGamma := Set(DescGamma2);
	Print("Size: ",Size(DescGamma),"\n");
od;
ReducedRGP := Filtered(RealGoodPairs,P->P[2] in DescGamma);

FindInReducedRGP:=function(q,gamma)
	return First(ReducedRGP,P->P[1]=q and P[2]=gamma);
end;
AGPRed := AGP{Filtered([1..Size(AGP)],i->orbitReps[i] in DescGamma)};
cbad := 0;
for i in [1..Size(DescGamma)] do
	gamma := DescGamma[i];
	for q in AGPRed[i] do
		if FindInReducedRGP(q,gamma)=fail then
			cbad := cbad+1;
		fi;
	od;
od;
cbad;
getTree := function(P)
	local tree, q, P2, sizeoldtree;
	sizeoldtree := 0;
	tree := [P[1]];
	while not Size(tree) = sizeoldtree do
		sizeoldtree := Size(tree);
		for q in P[3][3] do
			P2 := FindInReducedRGP(q,P[3][1]);
			if P2 = fail then 
				return fail;
			else
				AddSet(tree,P2[1]);
			fi;
		od;
		P := P2;
	od;
	return tree;
end;
M := [];
for P in ReducedRGP do
	Add(M,getTree(P));
od;
#
# DotLanguage
#
dotLangGraph := List([1..Size(ReducedRGP)],i->
		[i,List(ReducedRGP[i][3][3],q->
			First([1..Size(ReducedRGP)],k->
				ReducedRGP[k][1]=q and ReducedRGP[k][2]=ReducedRGP[i][3][1]))]);;
dotLangGraph:=Concatenation(List(dotLangGraph,P->Concatenation([String(P[1]),"->{",String(P[2]),"};\n"])));;

Vertices := [1..Size(ReducedRGP)];
Edges := [];
for i in [1..Size(ReducedRGP)] do
	for q in ReducedRGP[i][3][3] do
		j:= First([1..Size(ReducedRGP)],k->ReducedRGP[k][1]=q and ReducedRGP[k][2]=ReducedRGP[i][3][1]);
		if j = fail then
			Error("Doof gelaufen...\n");
		fi;
		Add(Edges,[i,j]);
	od;
od;

##################################################################################################

#Save RealGoodPairs to a file
RealGoodPairsFile := Concatenation(dir,"RealGoodPairs.go");
PrintTo(RealGoodPairsFile,List(RealGoodPairs,L->[Position(List(GPmodKP),L[1]),L[2],L[3]]));
#Replace <identy>.... by One(Q)
Exec("sed","-i","\"s/<identity> of .../One(Q)/g\"",RealGoodPairsFile);
#Add a return and a semicolon
Exec("sed","-i","\"1i return \"",RealGoodPairsFile);
Exec("sed","-i","\"\\$a ;\"",RealGoodPairsFile);

#Read the file again:
RGP := List(ReadAsFunction(RealGoodPairsFile)(),L->[List(GPmodKP)[L[1]],L[2],L[3]]);;
Assert(0,RGP=RealGoodPairs);

###################################################################################################
############################                     ##################################################
############################   Show K,G' have 	 ##################################################
############################		f.c.w 		 ##################################################
############################                     ##################################################
###################################################################################################

CompGammaCheckInkltrivialAct := function(q,gamma)
	local Gamma1,acts,x,Dep,i,ga,g,first,gp,qs,q1,q2,StateModKxK,Sucs;

	if Size(gamma)>6 then
		#gamma := GammaSimplify(gamma,F6);
		Error("gamma is too large!\n");
	elif Size(gamma)=5  then
		Append(gamma,One(gamma[1]));
	elif Size(gamma)<4  then
		Error("gamma is too small!\n");
	fi;
	if not q in GmodKP then
		Error("q has to be in G/K'\n");
	fi;
		
	q1:= StateLP(q,1)^isoGmodKtoQ;
	q2:= StateLP(q,2)^isoGmodKtoQ;
	acts := ActivityGamma(gamma);

	if not ForAll(acts,IsOne) then
		#act(γ) = (1,1,1…1) doesn't help
		Print("gamma need to have trivial activity everywhere");
		return[];
	fi;
	
	Gamma1 := []; 
	Dep := [];
	i := 1;
	for ga in gamma do
		first := true;
		Add(Dep,[2*i-1,2*i]); i := i+1;
		for gp in PreImages(BS.epi,ga) do
			if true then
				if first then
					Add(Gamma1,[gp![1]]);
					Add(Gamma1,[gp![2]]);
					first := false;
				else
					Add(Gamma1[Size(Gamma1)-1],gp![1]);
					Add(Gamma1[Size(Gamma1)],gp![2]);
				fi;	
			fi;
		od;
	od;
	Gamma1 := DEP_CARTESIAN@fr(Gamma1,Dep);;#Size of Gamma1 about 4096

	StateModKxK := function(q,i)
		local g;
		if not q in GmodKP then
			Error("q needs to be in G/K'");
		fi;
		g := PreImagesRepresentative(tauLP,q)^isoGPLtoG;
		return (State(g,i)^isoGtoGLP)^homGtoGmodKxK;
	end;

	for gp in Gamma1 do
		gp := [gp{[1,3,5,7,9,11]},gp{[2,4,6,8,10,12]}];
		qs := [q1,q2];
		if ForAll(gp,gpi->HasNontrivialActivity(gpi)) then
			if ForAll([1,2],i->IsOne(Comm(gp[i][1],gp[i][2])*Comm(gp[i][3],gp[i][4])*Comm(gp[i][5],gp[i][6])*qs[i])) then
				Sucs := Cartesian(List([1,2],i->PreImages(varpiPrimeLP,StateModKxK(q,i))));
				if ForAll(Sucs, r->ForAll([1,2],i->IsGoodPair(r[i],gp[i]))) then
					return gp;
				fi;
			fi;
		fi;
	od;
	return fail;
end;

CompGammaCheckInkltrivialAct(One(GPmodKP),ListWithIdenticalEntries(6,One(Q)));
###################################################################################################
############################                     ##################################################
############################   Playing around    ##################################################
############################  not nec. anymore   ##################################################
############################ find finite Cycles  ##################################################
############################                     ##################################################
###################################################################################################
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

#Perform some tests
for n in [1..200] do
	testg:= AnGpLPElement()^isoGPLtoG;
	Cy := findCycle(testg);
	Print(Size(Cy),"\n");
od;