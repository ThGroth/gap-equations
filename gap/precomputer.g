#Precompute the 90 orbits of Q⁶/Stab(R₆)
#
# Directory for Saved results. Needs a trailing /
#
dirRep := "~/Repositories/GrigorchukCommutatorWidth/";
#
dir := Concatenation(dirRep,"gap/90orbs/");

################################################################
# action on images of automorphism.
# typical usage: action on tuples of images of generators.
OnImages := function(list,aut)
    local gens;
    gens := GeneratorsOfGroup(Source(aut));
    return List(gens,g->MappedWord(g^aut,gens,list));
end;

################################################################
# surface relator of a free group F.
surface_relator := function(F)
    local gens;
    gens := GeneratorsOfGroup(F);
    return Product([2,4..Length(gens)],i->Comm(gens[i-1],gens[i]),One(F));
end;

################################################################
# the pure mapping class group of a surface group F / surface_relator,
# written in terms of automorphisms of F.
pure_mcg := function(F)
    local gens, d, L, i, imgs, x;
    gens := GeneratorsOfGroup(F);
    d := Length(gens);
    L := [];

    for i in [2,4..d] do
        imgs := ShallowCopy(gens);
        imgs[i] := gens[i-1]*gens[i];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;
    for i in [1,3..d-1] do
        imgs := ShallowCopy(gens);
        imgs[i] := gens[i+1]*gens[i];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;
    for i in [1,3..d-3] do
        imgs := ShallowCopy(gens);
        x := gens[i+1]/gens[i+2];
        imgs[i] := x*gens[i];
        imgs[i+1] := x*gens[i+1]/x;
        imgs[i+2] := x*gens[i+2]/x;
        imgs[i+3] := x*gens[i+3];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;

    #Switch two neighbours 
    #added by Thorsten prob. already contained in mcg
    for i in [1,3..d-3] do
        imgs := ShallowCopy(gens);
        imgs[i+2] := gens[i]^Comm(gens[i+2],gens[i+3]);
        imgs[i+3] := gens[i+1]^Comm(gens[i+2],gens[i+3]);
        imgs[i] := gens[i+2];
        imgs[i+1] := gens[i+3];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;

    # check that indeed the surface relator is preserved
    x := surface_relator(F);
    Assert(0,ForAll(L,g->x^g=x));
    
    return Group(L);
end;


# a larger group, containing the "flip" (x_i -> y_{g+1-i}, y_i -> x_{g+1-i})
extended_mcg := function(F)
    local gens;
    gens := GeneratorsOfGroup(F);
    
    return ClosureGroup(pure_mcg(F),GroupHomomorphismByImages(F,F,Reversed(gens)));
end;

################################################################
# construct orbits on Q^{2n}
BS := BranchStructure(GrigorchukGroup);
F6 := FreeGroup(6);
#
#orbits of pure mcg
#
#The following lines take about 12h
orbits := OrbitsDomain(DirectProduct(pure_mcg(F6),BS.group),
                  Cartesian(ListWithIdenticalEntries(6,BS.group)),
                  function(list,elm)
    return OnTuples(OnImages(list,elm![1]),elm![2]);
end);;
Print("Orbits computed; there are ",Size(orbits)," orbits\n");
orbits := List(orbits,ShallowCopy);;
#The following lines take about 5min
for i in orbits do Sort(i); MakeImmutable(i); od; # for fast lookup
MakeImmutable(orbits);;

##################################################################
# Find Representatives with maximal number of ones and one in last coord.
MinimalReprOrbit := function(O)
    local cone,o,L,R,max,elm;
    cone := function(L)
        return Size(Filtered(L,IsOne));
    end;
    R := [];
    for o in O do
        max := 0;
        elm := 0;
        for L in o do
            if IsOne(L[6]) and cone(L) > max then
                max:=cone(L);
                elm := L;
            fi;
        od;
        if elm = 0 then
            Error("No fitting element found in orbit\n");
        fi;
        Add(R,elm);
    od;
    return R;
end;
orbitReps := MinimalReprOrbit(orbits);

#
# Save the orbit Representations to a file.
# Needs the following lines to be read again properly
#
orbitRepsFile := Concatenation(dir,"orbitReps.go");
PrintTo(orbitRepsFile,orbitReps);
#Replace <identy>.... by One(Q)
Exec("sed","-i","\"s/<identity> of .../One(Q)/g\"",orbitRepsFile);
#Add a return and a semicolon
Exec("sed","-i","\"1i return \"",orbitRepsFile);
Exec("sed","-i","\"\\$a ;\"",orbitRepsFile);
Q:= BS.group;
f4:= Q.1; # = a^π
f2 := Q.2; # = b^π
f1 := Q.3; # = c^π
f3 := f1*f2*f4*f1*f2; # = (dad)^π
Assert(0,ReadAsFunction(orbitRepsFile)()=orbitReps);


#
# Save a map which assigns to each element of Q⁵ the corresponding orbit.
#
hash := function(q)
	if q in Q then
		return Position(List(Q),q);
	else 
		Error("Can't compute hash ",q," is not in Q.");
	fi;
end;
ComputeTable := function(O)
	local Values,i,q1,q2,q3,q4,q5,o;
	i := 0;
	Values := ListWithIdenticalEntries(16,0);
	for q1 in Q do 
		Values[hash(q1)]:=ListWithIdenticalEntries(16,0);
		for q2 in Q do
			Values[hash(q1)][hash(q2)]:=ListWithIdenticalEntries(16,0);
			for q3 in Q do
				Values[hash(q1)][hash(q2)][hash(q3)]:=ListWithIdenticalEntries(16,0);
				for q4 in Q do
					Values[hash(q1)][hash(q2)][hash(q3)][hash(q4)]:=ListWithIdenticalEntries(16,0);
					for q5 in Q do
						Values[hash(q1)][hash(q2)][hash(q3)][hash(q4)][hash(q5)] := PositionProperty(O,o->[q1,q2,q3,q4,q5,One(Q)] in o);
						if i mod 1000 =0 then
							Print(i," Done ", Int(i*100/16^5),"%.\r");
						fi;
						i := i+1;
	od;od;od;od;od;
	Print("Done\n");
	return Values;
end;
#Takes ~10 Minutes 
orbitTable := ComputeTable(orbits);;

orbitTableFile := Concatenation(dir,"orbitTable.go");
PrintTo(orbitTableFile,orbitTable);
#Add a return and a semicolon
Exec("sed","-i","\"1i return \"",orbitTableFile);
Exec("sed","-i","\"\\$a ;\"",orbitTableFile);
#######################################################################################
#######################################################################################
#######################################################################################
#					Computation of the orbits now done
#######################################################################################
#######################################################################################
#######################################################################################


Read(Concatenation(dirRep,"gap/grpwords/grpwords.gd"));
Read(Concatenation(dirRep,"gap/grpwords/grpwords.gi"));
#Set up all Branchstructure, quotients etc.
#Working with L presentation
#All groups with LP in the name means that they are subgroups of the 
#L-Presented Grigorchuk group.
G := GrigorchukGroup;
a := G.1; b := G.2; c := G.3; d:=G.4;
isoGtoGLP := IsomorphismLpGroup(G);
isoGPLtoG := InverseGeneralMapping(isoGtoGLP);
GLP := Image(isoGtoGLP);
# G'
aL := GLP.1; bL := GLP.2; cL := GLP.3; dL:=GLP.4;
k1 := (aL*bL)^2; k2 := (aL*bL*aL*dL)^2; k3 := (bL*aL*dL*aL)^2;
GPGen := [k1,k3,k2,(aL*dL)^2];
GpLP := Subgroup(GLP,GPGen); 
Gp := Group((a*b)^2,(a*b*a*d)^2,(b*a*d*a)^2,(a*d)^2);
LGen := [k2,k3,bL,aL*bL*aL];
LLP := Subgroup(GLP,LGen);
# K
KGen := [k1,k3,k2];
KLP := Subgroup(GLP,KGen);
# K×K
KxKGen := [k2,k3,Comm(k2^-1,k1),Comm(k2,k1^-1),Comm(k2^-1,k1)^aL,Comm(k2,k1^-1)^aL];
KxKLP := Subgroup(GLP,KxKGen);
# K'
GenKPLP := [(dL*aL*cL*aL*bL*aL*cL*aL)^2*(bL*aL*cL*aL)^4,((cL*aL)^2*bL*aL*cL*aL)^2,(dL*aL*cL*aL*bL*aL*cL*aL)^2*cL*(aL*cL*aL*bL)^3*aL*cL*aL*dL,((aL*cL)^3*aL*bL)^2, (bL*aL*cL*aL)*dL*aL*cL*aL*bL*(aL*cL)^2*(aL*cL*aL*bL)^3, (aL*cL*aL*dL*aL*cL*aL*bL)^2*(aL*cL*aL*bL)^4];
AllGenKPLP := [];
for h in GenKPLP do
	Add(AllGenKPLP,h);
	Add(AllGenKPLP,h^aL);
od;
KPLP := Subgroup(GLP,AllGenKPLP);
# G/K
piLP := NaturalHomomorphismByNormalSubgroup(GLP,KLP);
GmodK := Image(piLP);;
# G/K'
tauLP := NaturalHomomorphismByNormalSubgroup(GLP,KPLP);
homGtoGmodKxK := NaturalHomomorphismByNormalSubgroup(GLP,KxKLP);;
GmodKP := Image(tauLP);;
# G'/K'
GPmodKP := Group(List(GPGen,g->g^tauLP));;
# K/K'
KmodKP := Group(List(KGen,g->g^tauLP));;
# (K×K)/K'
KxKmodKP := Group(List(KxKGen,g->g^tauLP));;
# G/(K×K)
GmodKxK := Image(homGtoGmodKxK);
# G'/(K×K)
varpiLP := NaturalHomomorphismByNormalSubgroup(GmodKP,KmodKP);;
varpiLP := varpiLP*IsomorphismGroups(Image(varpiLP),GmodK) ;; 
varpiPrimeLP := NaturalHomomorphismByNormalSubgroup(GmodKP,KxKmodKP);;
varpiPrimeLP := varpiPrimeLP*IsomorphismGroups(Image(varpiPrimeLP),GmodKxK);; 

# A "random" Element of G' as word of at most 100 generators
AnGpLPElement := function()
	local n,g;
	g := One(GpLP);
	for n in [1..Random([1..100])] do
		g := g*Random(GPGen);
	od;
	return g;
end;

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

# The non L-Presented pendant to the groups before
BS := BranchStructure(G);
Q := BS.group; #G/K
w := BS.epi;
pi := BS.quo;

f4:= Q.1; # = a^π
f2 := Q.2; # = b^π
f1 := Q.3; # = c^π
f3 := f1*f2*f4*f1*f2; # = (dad)^π
A := Filtered(List(Q),x->Activity(PreImagesRepresentative(pi,x))=(1,2));
AC := Filtered(List(Q),x->Activity(PreImagesRepresentative(pi,x))=());

#Needed for the ReduceConstraint function. 
#This is the polycylcic decomposition of G
C1 := Group(a^pi,d^pi);
C2 := Group((a*d)^pi);

#This leads to problem, becaus it's the wrong isomorphism
#isoQtoGmodK := IsomorphismGroups(Q,GmodK);
#isoGmodKtoQ := IsomorphismGroups(GmodK,Q);

isoQtoGmodK :=GroupHomomorphismByImages(Q,GmodK,[f1,f2,f4],List([c,b,a],x->(x^isoGtoGLP)^piLP));
isoGmodKtoQ :=GroupHomomorphismByImages(GmodK,Q,List([c,b,a],x->(x^isoGtoGLP)^piLP),[f1,f2,f4]);

# The below function returns for a given γ∈Q⁶ 
# the list of all q∈G'/K' such that (q,γ) is a good pair
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

#Load orbits here:
orbitReps:=ReadAsFunction(Concatenation(dir,"orbitReps.go"))();;
ReducedConstraints := List([1..Size(orbitReps)],
    i->rec(index:= i, constraint:=orbitReps[i]));;
orbitTable := ReadAsFunction(Concatenation(dir,"orbitTable.go"))();;

#Takes about 1 min
# Compute the full list of good pairs
# Such that for each entry e in ReducedConstraints the list e.goodPairs contains
# all q∈Q such that (q,e.constraint) is a good pair.
Perform(ReducedConstraints,function(entry) entry.goodPairs:=goodPairs(entry.constraint); end);

#Write AllGoodPairs to a file
AllGoodPairsFile := Concatenation(dir,"AllGoodPairs.go");
PrintTo(AllGoodPairsFile,List(ReducedConstraints,E->List(E.goodPairs,q->Position(List(GPmodKP),q))));
#Replace <identy>.... by One(Q)
Exec("sed","-i","\"1i return \"",AllGoodPairsFile);
Exec("sed","-i","\"\\$a ;\"",AllGoodPairsFile);

#Read the file again and check its correct
AGP := List(ReadAsFunction(AllGoodPairsFile)(),L->List(L,i->List(GPmodKP)[i]));;
Assert(0,ForAll(ReducedConstraints,E->E.goodPairs = AGPt[E.index]));
#Usage of the file:
#Perform(ReducedConstraints,function(E) E.goodPairs:=AGP[E.index]; end);

#######################################################################################
#######################################################################################
#					Computation of the good pairs is done
#######################################################################################
#######################################################################################

# γ: Fₙ→Q is mapped to Act(γ): Fₙ→ {(),(1,2)}
#
ActivityConstraint := function(gamma)
	return List(gamma,x->Activity(PreImagesRepresentative(pi,x)));
end;
HasNontrivialActivity := function(gamma)
	return not ForAll(ActivityConstraint(gamma),IsOne);
end;
# Rₐₜ active representatives
ReducedConstraintsActive := Filtered(ReducedConstraints,E->HasNontrivialActivity(E.constraint));;

#Make sure that forach q in G'/K' there is a good active pair involving q.
Assert(0,ForAll(GPmodKP,q->ForAny(ReducedConstraintsActive,E->q in E.goodPairs)));

#The surface relator Rₙ=[x₁,x₂]…[x₂ₙ-₁,x₂ₙ] where the free group F is generated by x₁,x₂,…,x₂ₙ
surface_relator := function(F)
    local gens;
    gens := GeneratorsOfGroup(F);
    return Product([2,4..Length(gens)],i->Comm(gens[i-1],gens[i]),One(F));
end;

#
# Function to compute an element φ fixing Rₙ which transorms a given
# constraint γ:F₂ₙ → Q to γ': F₅→Q 
# 
# The input can be either a group homomorphism from a free group to Q 
# or a list with entries in Q
# 
# By default ReducedConstraint returns an element of ReducedConstraints 
# but there are two different modes specified by a second argument mode:
# ∙ if mode = 0: 
#       This is the default mode. The returned value is a record from 
#       the list ReducedConstraints.
# ∙ if mode = 1:
#       No lookup is done in the orbit table. This is usefull if the
#       orbit table is not computed. The output is then not a record
#       but a List with 6 element in Q.
# ∙ if mode = 2:
#       No lookup is done either and the return value is a list [γ,φ]
#       where γ is the reducedConstraint as in mode 1 and 
#       φ is a an automorphism of F₂ₙ which performs the reduction
#   
# There are aliases available:
# ReducedConstraint(γ)=ReducedConstraint(γ,0)
# ReducedConstraintnoLookup(γ)=ReducedConstraint(γ,1)
# ReducedConstraintReturnHom(γ)=ReducedConstraint(γ,2)
# 
#
ReducedConstraintnoLookup := function(gamma)
    return ReduceConstraint(gamma,1);
end;
ReducedConstraintReturnHom := function(gamma)
    return ReducedConstraint(gamma,2);
end;
ReducedConstraint := function(gamma,arg...)
    local mode, TempOrbitTable, F, gens, d, L, i, phi,psi,swi,id,imgs,Phi,ph,ActionOnList,x,
    KillBlock,KillAllBlocks,NormalizeBlock,NormalizeAllBlocks,step,
    RepresentativeInOrbitReps;

    if Size(arg)=0 then
        mode := 0;
    else 
        mode := arg[1];
    fi;
    if IsGroupHomomorphism(gamma) then
    	F := Source(gamma);
    	gamma := List(GeneratorsOfGroup(F),x->x^gamma);
    elif IsList(gamma)  then
        F := FreeGroup(2*Int(Ceil(Float(Size(gamma)/2))));
    else
        Error("Wrong input: gamma must be either a homorphism from a free group or a list");
    fi;

    if mode = 0 then
        if not IsBound(orbitTable) then
            Error("To use lookup mode the orbitTable must be present. Try using mode 1");
        fi;
        TempOrbitTable := orbitTable;
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

    #already contained in mcg
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

    #TODO: Adapt On images so that this can be used instead
    ##  OnImages := function(list,aut)
  #      local gens;
  #      gens := GeneratorsOfGroup(Source(aut));
  #      return List(gens,g->MappedWord(g^aut,gens,list));
  #  end;
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
	# Returns the index of the element γᵣ in ReducedConstraints such that 
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
		return TempOrbitTable[hash(gamma[1])][hash(gamma[2])][hash(gamma[3])][hash(gamma[4])][hash(gamma[5])];
	end;

    #Now do the real work...
    ph := NormalizeAllBlocks(1,gamma,C1);
    if mode = 2 then
   	    Phi := ph;
    fi;

    gamma := ActionOnList(gamma,ph); # (Q,C1,Q,C1,Q,C1,Q,C1…)
    Assert(2,ForAll(gamma{[2,4..Size(gamma)]},x->x in C1));
    step := 1;

    ph := KillAllBlocks(1,gamma,C1);
    if mode = 2 then
        Phi := ph*Phi;
    fi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C1,C1,C1,C1,C1…)
    Assert(2,ForAll(gamma{[2..Size(gamma)]},x->x in C1));
    step := 2;

	ph := NormalizeAllBlocks(3,gamma,C2);
	if mode = 2 then
        Phi := ph*Phi;
    fi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C1,C2,C1,C2,C1,C2…)
    Assert(2,ForAll(gamma{[4,6..Size(gamma)]},x->x in C2));
    step := 3;

    ph := KillAllBlocks(3,gamma,C2);
	if mode = 2 then
        Phi := ph*Phi;
    fi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C2,C2,C2,C2,C2,C2…)
    Assert(2,ForAll(gamma{[4..Size(gamma)]},x->x in C2));
    step := 4;

    ph := NormalizeAllBlocks(5,gamma,Group(One(C1))); #Trivial Mod
	if mode = 2 then
        Phi := ph*Phi;
    fi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C2,1,C2,1,C2,1…)
    Assert(2,ForAll(gamma{[6,8..Size(gamma)]},IsOne));
    step := 5;

	ph := KillAllBlocks(5,gamma,Group(One(C1))); #Trivial Mod
	if mode = 2 then
        Phi := ph*Phi;
    fi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C2,1,1,1,1,1…)
    Assert(2,ForAll(gamma{[6..Size(gamma)]},IsOne));
    step := 6;

	if mode = 2 then
        Phi := ph*Phi;
        Assert(2,surface_relator(F)^Phi=surface_relator(F));
    fi;
	if mode = 2 then
	   return [gamma{[1..6]},Phi];
    elif mode = 1 then
	   return gamma{[1..6]};
	else
       return ReducedConstraints[RepresentativeInOrbitReps(gamma{[1..5]})];
    fi;
end;


# IsGoodPair(g,γ)
# Test whether a given pair is a good pair.
# Input:
#    g ∈ G, GLP, or G/K'
#    γ  ∈ Q^n for some n≥5  or
#       group homomorphism from a free group to Q
#       ∈ ReducedConstraints
# Output:
#    true or false depending if (g,γ) is a good pair or not.
IsGoodPair := function(q,gamma)
	if not q in GPmodKP then
		Info(InfoFRGW,2,"work mod KP\n");
		if not q in GLP then
			q := q^isoGtoGLP;
		fi;
		q := q^tauLP;
	fi;
    if IsRecord(gamma) then
        return q in gamma.constraint;
    fi;
    if IsGroupHomomorphism then
        gamma := List(GeneratorsOfGroup(Source(gamma)),gen->gen^gamma);
    fi;
    gammaRec := First(ReducedConstraints,E->E.constraint=gamma);
    if gammaRec = fail then
		gammaRec := ReducedConstraint(gamma);
	fi;
	return q in gammaRec.goodPairs;
end;
#For q in G'/K'
#Get List of all reduced constraints γ such that (q,γ) is a good pair.
GetAllGoodGammas := function(q)
    return Filtered(ReducedConstraints,E->q in E.goodPairs);
end;

#
# Given a good pair (q,γ) where γ has nontrivial activity 
# 
# This method tries to compute a pair (γ',x) with the following property:
# ̇ γ' has nontrivial activity
# ̇ x ∈ {1,a,b,c,d,ab,ad,ba}
# ̇ for all g with g^τ=q 
# 	the sattisfiabillity of (R₂ₙ-₁ (g@2)^x ⋅ g@1 ,γ') implies the 
# 	sattisfiabillity of Rₙg,γ
# ̇ (γ',(g@2)^x ⋅ g@1) is a good pair 
# 
# If the search for such a pair fails, the method returns fail, this doesn't 
# guarantee that such a pair does not exists.
# 
#
GetSuccessor  := function(q,gamma)
	local Gamma1,g1,g2,F2,F,GammAPrime,count,acts,frvars, frinvvars,
		t,I,x,v,w,indx,v1,v2,w1,w2,newEq,NoFI,NoFIhom,z,GHOnList,gam,
		Dep,i,g,first,gp,gpp,trans,H,normalforms,nf,gaP,q1,q2;

	if Size(gamma)>6 then
		Error("gamma is too large!\n It need to be a reduced constraint");
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
	acts := ActivityConstraint(gamma);

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
    #TODO should be part of the grpword package
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
	Gamma1 := DEP_CARTESIAN@fr(Gamma1,Dep);;#Size of Gamma1 about 4096
    #Gamma1 contains all possible γ' such that <<γ'₂ₖ-₁,γ'₂ₖ>> = γₖ for k=1…6
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
				z := gpp[AbsInt(nf[1])]^SignInt(nf[1]);
                if z in List(Q){[1,2,5,9,13,6,15,10]} then # = [1,a,b,c,d,ab,ad,ba]^π
    				NoFIhom := nf[2];
    				#Compute the image of γ' under the normalization hommorphism and simplify it to the F₅ case
    				gaP := [MakeImmutable(ReducedConstraint(GHOnList(NoFIhom,gpp){[1..4*3-2]})),z];
    				Suc := List(PreImages(varpiPrimeLP,p_h(q,PreImagesRepresentative(pi,z))));
                    #Add(gaP,Suc); #Adding all possible succeccors mod K' to the returned list
    				#Added check for nontrivial activity.
    				if HasNontrivialActivity(gaP[1]) and ForAll(Suc, r->IsGoodPair(r,gaP[1])) then
    					return gaP; #[γ',z,{q₁,…,q₁₆}]
    				fi;
                fi;
			od;
		fi;
	od;
	return fail;
end;


# The following takes about 30 min.
# and computes for each active good pair (q,γ) the succesing (γ',x) as in Prop. 2.16
#
# The resulting list RealGoodPairs contains tuples (q,γ,[γ',x,[q₁,…,q₁₆]]) foreach
# q ∈ G'/K', γ∈Red such that γ has nontrivial activity and (q,γ) is a good pair.
# The element [γ',x,[q₁,…,q₁₆]] has the property that 
#   ∙(γ',qᵢ) are good pairs ∀i=1,…,16 and γ' has activity in some component
#   ∙if g ∈ τ⁻¹(q) then (g@2)^Rep(x) ⋅ (g@1) ∈ τ⁻¹(qᵢ) for some i ∈ {1,…,16}
#   ∙if (R₂ₙ-₁ (g@2)^Rep(x) ⋅ g@1 ,γ') is sattisfiable then so is (Rₙ g,γ)
countGoodOnes := 0;
countBadOnes := 0;
size := Sum(List(AGP,Size));
count := 0;
RealGoodPairs := [];
BadPairs := [];
for E in ReducedConstraintsActive do
    gamma := E.constraint;
    for q in E.goodPairs do
        gammap := GetSuccessor(q,gamma);
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
Assert(0,Size(BadPairs)=0);

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

#statistics:
#Get the number of occurences of each element x in RGP
List(List(Q){[1,2,5,9,13,6,15,10]},q->Size(Filtered(List(RGP,P->P[3][2]),z->z=q)));


####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
#
#						Computation of all real good pairs is done
#
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
####################################################################################################################
