##########################################################################
######                                                               #####
######         Commutator width Gupta-Sidki-Group                    #####
######                                                               #####
######			prove that c.w.(GuSidGrp)≤2							 #####
########################################################################## 

#Load fr, lpres and equation package
if not IsExistingFile("./examples/init.g") then
    Error("Please start this script in the main directory.");
fi;
dir := Directory("examples");
Read(Filename(dir,"init.g"));


G := GuptaSidkiGroup;
a := G.1; t := G.2;
t1 := t; t2:=t1^a; t3:=t2^a;
Info(InfoExamples,2,"Computing the BranchStructure takes a minute: \n");
BS := BranchStructure(G);
Q := BS.group;
pi := BS.quo;
#=========================================================================
# Compute the orbits and a representative system for Q⁴/U₂
#
# orbit2 is the list of all orbits
# redConstraints is a list of representatives of the orbits
# 
# reducedConstraint is a function that reduces a given constraint to one
# 					in redConstraints
#========================================================================= 
OnImages := function(list,aut)
    local gens;
    gens := GeneratorsOfGroup(Source(aut));
    return List(gens,g->MappedWord(g^aut,gens,list));
end;

# Given a free group group F = ⟨X₁,X₂,…,X₂ₙ⟩ 
# returns the element [X₁,X₂]…[X₂ₙ₋₁,X₂ₙ]
surface_relator := function(F)
    local gens;
    gens := GeneratorsOfGroup(F);
    return Product([2,4..Length(gens)],i->Comm(gens[i-1],gens[i]),One(F));
end;

# Given a free group group F = ⟨X₁,X₂,…,X₂ₙ⟩ 
# returns the group Uₙ
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
    #already contained in the previous but makes computations easier.
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

# Choose a nice representative for each orbit.
# I.e. containing a maximal number of trivial elements.
MinimalReprOrbitOld := function(O)
    local cone,o,L,R,max,elm;
    cone := function(L)
        return Size(Filtered(L,IsOne));
    end;
    R := [];
    for o in O do
        max := -1;
        elm := 0;
        for L in o do
            if IsOne(L[4]) and cone(L) > max then
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

MinimalReprOrbit := function(O)
    local cone,o,L,R,max,elm,C1;
    cone := function(L)
        return Size(Filtered(L,IsOne));
    end;
    R := [];
    C1 := Group(a^pi);
    for o in O do
        max := -1;
        elm := 0;
        for L in o do
            if IsOne(L[4]) and cone(L) > max and L[2] in C1 and L[3] in C1 then
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
# Just for curiosity see how the orbits of Q²/U₁ look like.
# 
Info(InfoExamples,2,"Computing the orbits of Q²/U₂: \n");
orbits1 := OrbitsDomain(pure_mcg(FreeGroup(2)),
                   Cartesian(ListWithIdenticalEntries(2,BS.group)),
                   OnImages);;
#Get the orbits of Q⁴/U₂
orbits2 := OrbitsDomain(pure_mcg(FreeGroup(4)),
                   Cartesian(ListWithIdenticalEntries(4,BS.group)),
                   OnImages);;
redConstraints := MinimalReprOrbit(orbits2);

# Given an arbitrary element γ∈Q²ⁿ returns a representative in redConstraints
# Can replace this by a more deterministic algorythm since Q is polycylic of deg. 2
ReducedConstraint := function(list)
    local i, ijk, sublist, length;
    
    list := ShallowCopy(list);
    length := Length(list);
    while length>4 do
        ijk := Random(Arrangements([2,4..length],2));
        ijk := Union(ijk-1,ijk);
        sublist := list{ijk};
        list{ijk} := First(orbits2,o->sublist in o)[1];
        for i in [length,length-2..2] do
            if IsOne(list[i-1]) and IsOne(list[i]) then
                Remove(list,i); Remove(list,i-1); length := length-2;
            fi;
        od;
    od;
    while length<4 do Add(list,One(BS.group)); length := length+1; od;
    return redConstraints[PositionProperty(orbits2,o->list in o)];
end;


#=========================================================================
# Quotients and L-presented version of Subgroups
# π: G → G/G'
# τ: G → G/G''
# ρ: G → G/Stab(2)
# ϖ: G/G'' → G/G'
#========================================================================= 
Info(InfoExamples,2,"Computing the Quotients takes a few minutes: \n");
isoGtoGLP := IsomorphismLpGroup(G);
GLP := Image(isoGtoGLP);
isoGLPtoG := GroupHomomorphismByImagesNC(GLP,G,[a,t1,t2,t3]);
#isoGLPtoG := InverseGeneralMapping(isoGtoGLP); #This produces nonsense... TODO: Check why! 

#-------------    GP    -----------
GPGen := [Comm(a,t),Comm(a,t)^a,Comm(a,t)^t,Comm(a,t)^(a*t)];
GP := Group(GPGen);
GPLP := Subgroup(GLP,List(GPGen,g->g^isoGtoGLP));
#-------------    GPP    -----------
Gen := Set(ListX(Cartesian(GPGen,GPGen),Comm));
GPPGen :=[];
for g in Gen do
	AddSet(GPPGen,g);
	AddSet(GPPGen,g^a);
	AddSet(GPPGen,g^t);
od;
GPP := Group(GPPGen);
GPPLP := Subgroup(GLP,List(GPPGen,g->g^isoGtoGLP));
verifyIsGPP := function()
	return IsNormal(GLP,GPPLP);
end; #returns true :)
#-------------    GPxGPxGP    -----------
x1:=GPGen[1];x2:=GPGen[2];x3:=GPGen[3];x4:=GPGen[4];
TempGPxGPxGPGen := [x2*x1^2*x4^-1*x1,#=<<1,1,x1>> 
				x1^2*x4^-1*x1*x2,#=<<1,1,x2>>
				x1^-1*x4*x2*x1*x4,#=<<1,1,x3>>
				x3*x2*x3^-1*x4^-1];#=<<1,1,x4>>
GPxGPxGPGen := [];
for g in TempGPxGPxGPGen do
	AddSet(GPxGPxGPGen,g);
	AddSet(GPxGPxGPGen,g^a);
	AddSet(GPxGPxGPGen,g^(a^2));
od;
GPxGPxGP := Group(GPxGPxGPGen);
GPxGPxGPLP := Subgroup(GLP,List(GPxGPxGPGen,g->g^isoGtoGLP));

verifyIsGPxGPxGP := function()
	return IsNormal(GLP,GPxGPxGPLP);
end; #returns true :)

#ForAll(GPPGen,g->ForAll([1,2,3],i->State(g,i) in GPxGPxGP))
# returns false :(

#-------------    Stab(2)    -----------
ttt := UnderlyingMealyElement(FRElement([[[t],[t],[t]]],[()],[1]));
Stab2Gen := Concatenation(GPxGPxGPGen,[ttt]);
Stab2 := Group(Stab2Gen);
Stab2LP := Subgroup(GLP,List(Stab2Gen,g->g^isoGtoGLP));
#
#ForAll(GPPGen,g->ForAll([1,2,3],i->State(g,i) in Stab2));
# Still returns false :(
# 


#-------------    GmodGP, GmodGPP, GPmodGPP    -----------
piLP := NaturalHomomorphismByNormalSubgroup(GLP,GPLP);
tauLP := NaturalHomomorphismByNormalSubgroup(GLP,GPPLP);;
rhoLP := NaturalHomomorphismByNormalSubgroup(GLP,Stab2LP);;

GmodGP := Image(piLP);;
GmodGPP := Image(tauLP);;
GmodStab2 := Image(rhoLP);;

GPmodGPP := Group(List(GPGen,g->(g^isoGtoGLP)^tauLP));;
Stab2modGPP := Group(List(Stab2Gen,g->(g^isoGtoGLP)^tauLP));;

varpiLP := GroupHomomorphismByImages(GmodGPP,GmodGP,List([a,t],x->(x^isoGtoGLP)^tauLP),List([a,t],x->(x^isoGtoGLP)^piLP));

isoQtoGmodGP :=GroupHomomorphismByImages(Q,GmodGP,[Q.1,Q.2],List([a,t],x->(x^isoGtoGLP)^piLP));
isoGmodGPtoQ :=GroupHomomorphismByImages(GmodGP,Q,List([a,t],x->(x^isoGtoGLP)^piLP),[Q.1,Q.2]);

#Check that ∏g@i ∈ Stab₂ if g∈G''
Info(InfoExamples,2,"Verify that ∏g@i ∈ Stab₂ if g∈G'' \n");
Assert(0,ForAll(GPPGen,g->IsOne(Product([1,2,3],i->(State(g,i)^isoGtoGLP)^rhoLP))));

#=========================================================================
# Good pairs
#
# gP[i] is the list with all q∈G'/G'' such that (q,redConstraints[i)) 
# is a good pair
# 
#========================================================================= 

# The function returns for a given γ∈Q⁴ 
# the list of all q∈G'/K' such that (q,γ) is a good pair
goodPairs := function(gamma)
    local S1,S2,F,p,q;
    if ForAny(gamma,q-> not q in GmodGP) then
        gamma:=List(gamma,q->q^isoQtoGmodGP);
    fi;
    S1 := Set(ListX(Cartesian(PreImages(varpiLP,gamma[1]),PreImages(varpiLP,gamma[2])),Comm));
    S2 := Set(ListX(Cartesian(PreImages(varpiLP,gamma[3]),PreImages(varpiLP,gamma[4])),Comm));
    F := [];
    for p in S1 do for q in S2 do 
        AddSet(F,(p*q)^-1);
    od;od;
    return F;
end;
Info(InfoExamples,2,"Compute the set of good pairs.\n");
gP:= List(redConstraints,gam->goodPairs(gam));;
# The first two constraints are inactive, 


getGoodGammas := function(q)
	return redConstraints{Filtered([4..8],i->q in gP[i])};
end;


IsGoodPair := function(q,gamma)
	return q in gP[Position(redConstraints,gamma)];
end;

#Store the inverse lookup:
# Given q∈ G'/G'' give all reduced constraints γ s.t. (q,γ) is a good pair.
#
goGamms := rec();
for q in [1..Size(GPmodGPP)] do
    goGamms.(q) := redConstraints{Filtered([1..Size(redConstraints)],
                                    i->List(GPmodGPP)[q] in gP[i])};
od;
getGoodConst := function(q)
    return goGamms.(Position(List(GPmodGPP),q));
end;

#=========================================================================
# Succeeding pairs
#========================================================================= 

#the maps @i: G'/G'' → G/G', gG'' ↦ g@i G' are well defined since 
#if g'' ∈ G'' then g''@i ∈ G'
StateLP := function(q,i)
	if not q in GmodGPP then
		Error("State: q needs to be in G/K'");
	fi;
	return (State(PreImagesRepresentative(tauLP,q)^isoGLPtoG,i)^isoGtoGLP)^piLP;
end;
# γ: Fₙ→Q is mapped to Act(γ): Fₙ→ {(),(1,2,3),(1,3,2)}
#
ActivityConstraint := function(gamma)
    return List(gamma,x->Activity(PreImagesRepresentative(pi,x)));
end;
HasNontrivialActivity := function(gamma)
    return not ForAll(ActivityConstraint(gamma),IsOne);
end;

#ReducedConstraints{[4..8]} will be the the Red₁
GoodRedConstraints := [4..8]; 

verifyExistsGoodPairs := function()
    return ForAll(GPmodGPP,q->ForAny(gP{GoodRedConstraints},qs->q in qs));
end;
Assert(0,verifyExistsGoodPairs());


#################
# Returns all derived (γ',Sucs) ∈Γ₁×Pow(G'/G'') s.t. 
# ∙ γ' solves the equation components Φ_γ^nf(R₂g) modulo G' 
#   for every g ∈ τ⁻¹(q)
# ∙ γ' ∈ Red₁ mod U₄ (so especiallly it is active)
# ∙ (q',γ') is good Pair for all q'∈Sucs
# ∙ If g^τ=q and Φ_γⁿᶠ(R₂g) = R₄ g@σ(1)^(Z₁)g@σ(2)^(Z₂)g@σ(3) then
#   (g@σ(1)^γ'(Z₁) g@σ(2)^γ'(Z₂)g@σ(3))^τ ∈ Sucs
#   
#   In particular it computes the set Γ₂^q(γ).
#
GetSuccessor  := function(q,gamma)
    local n,q1,q2,q3,Gamma1,Dep,i,ga,first,gp,acts,
        FG,F,EqG,DEqG,Eq,DEq,DEqdf,newEq,z1,z2,FF,
        DEqQ, DEqGtoDEqQ, DEqGmodGPP,qRepInG,fullfillsProp,Res,res;

    n := Length(gamma);
    Assert(0,n=4);
    if not q in GmodGPP then
        Error("q has to be in G/K'\n");
    fi;
        
    q1:= StateLP(q,1)^isoGmodGPtoQ;
    q2:= StateLP(q,2)^isoGmodGPtoQ; 
    q3:= StateLP(q,3)^isoGmodGPtoQ; 

    Gamma1 := []; 
    Dep := [];
    i := 1;
    for ga in gamma do
        first := true;
        Add(Dep,[3*i-2,3*i-1,3*i]); i := i+1;
        for gp in PreImages(BS.epi,ga) do
            if first then
                Add(Gamma1,[gp![1]]);
                Add(Gamma1,[gp![2]]);
                Add(Gamma1,[gp![3]]);
                first := false;
            else
                Add(Gamma1[Size(Gamma1)-2],gp![1]);
                Add(Gamma1[Size(Gamma1)-1],gp![2]);
                Add(Gamma1[Size(Gamma1)],gp![3]);
            fi; 
        od;
    od;
    #Gamma1 contains all possible γ' such that 
    # <<γ'₃ₖ₋₂,γ'₃ₖ-₁,γ'₃ₖ>> = γₖ for k=1…4
    Gamma1 := DEP_CARTESIAN@fr(Gamma1,Dep);;
        
    acts := ActivityConstraint(gamma);
    Assert(0,HasNontrivialActivity(gamma));
    #
    FG := FreeGroup(1); SetName(FG,"FG");
    F := FreeGroup(infinity,"xn",["x1","x2","x3","x4","x5","x6"]);SetName(F,"FX");

    EqG := EquationGroup(FG,F);
    DEqG := DecompositionEquationGroup(EqG,3,[()]);
    Eq := Equation(EqG,[Comm(F.1,F.2)*Comm(F.3,F.4),FG.1]);
    DEq := DecompositionEquation(DEqG,Eq,acts);
    DEqdf := DecomposedEquationDisjointForm(DEq);
    Assert(0,ForAll(EquationComponents(DEqdf.eq){[2,3]},IsOne));

    newEq := EquationNormalForm(EquationComponent(DEqdf.eq,1));
    Assert(0,Genus(newEq.nf)=4);
    z1 := Equation(DEqG,[DEqG!.free.(3*n-3)])^newEq.homInv;
    z2 := Equation(DEqG,[DEqG!.free.(3*n-2)])^newEq.homInv;

    FF := DEqG!.free;

    DEqQ := EquationGroup(Q,DEqG!.free);
    DEqGtoDEqQ := FreeProductHomomorphism(DEqG,DEqQ,[
                GroupHomomorphismByImages(DEqG!.const,Q,[q1,q2,q3]),
                IdentityMapping(FF) ]);
    DEqGmodGPP := EquationGroup(GmodGPP,DEqG!.free);

    qRepInG := PreImagesRepresentative(tauLP,q)^isoGLPtoG;

    # γ'∈Γ₁: ∀ q'∈ q₁^γ'(Z₁) q₂^γ'(Z₂) q₃ Stab₂ 
    # ∙ γ' solves the equation components modulo G'
    # ∙ γ' is active
    # ∙ γ' ∈ Red₁ mod U₄
    # ∙ (q',γ') is good Pair 
    # #################
    # returns false if gp does not fullfill any of the above properties
    # 
    # otherwise it returns the the set Sucs= q₁^γ'(Z₁) q₂^γ'(Z₂) q₃ Stab₂ this 
    # set Sucs has the property that if 
    # g^τ=q and Φ_γⁿᶠ(R₂g) = R₄ g@σ(1)^(Z₁)g@σ(2)^(Z₂)g@σ(3) then
    # (g@σ(1)^γ'(Z₁)g@σ(2)^γ'(Z₂)g@σ(3))^τ ∈ Sucs
    # and the elements 
    fullfillsProp := function(gp)
        local evQ,evGmodGPP,gaP,DEqGtoDEqGmodGPP,newqoffset;
        evQ := EquationEvaluation(DEqQ,EquationVariables(DEq),gp);
        if not ForAll(EquationComponents(DEqdf.eq),c->IsOne((c^DEqGtoDEqQ)^evQ)) then
            return false;
        fi;

        gaP := MakeImmutable( ReducedConstraint( List([1..3*n-4],i->(ImageElm(newEq.homInv,FF.(i))^DEqGtoDEqQ)^evQ) ) );
        
        if not gaP in redConstraints{GoodRedConstraints} then
            return false;
        fi;
        DEqGtoDEqGmodGPP := FreeProductHomomorphism(DEqG,DEqGmodGPP,[
            GroupHomomorphismByImages(DEqG!.const,GmodGPP,List([1,2,3],i->((State(qRepInG,i))^isoGtoGLP)^tauLP)),
            IdentityMapping(FF) ]);
        evGmodGPP := EquationEvaluation(DEqGmodGPP,
            EquationVariables(newEq.nf),
            Concatenation(ListWithIdenticalEntries(8,One(GmodGPP)),
                List([z1,z2],z->((PreImagesRepresentative(pi,(z^DEqGtoDEqQ)^evQ))^isoGtoGLP)^tauLP) ) );
        newqoffset := (newEq.nf^DEqGtoDEqGmodGPP)^evGmodGPP;
        if ForAll(Stab2modGPP,newq->IsGoodPair(newqoffset*newq,gaP)) then
            return List(Stab2modGPP,newq->newqoffset*newq);
        else
            return false;
        fi;
    end;
    Res := [];
    for gp in Gamma1 do
        res := fullfillsProp(gp);
        if not res = false then
            Add(Res, [gp,res]);
        fi;
    od;
    return Res;
end;
########
#
# Verifies for all γ∈Red₁ and all q∈G'/G'' such that (q,γ) is a good pair
# that there exists a good successing constraint γ'. (See getSuccessor)
# 
# - If there is no such successor then (q,γ) will be a bad pair 
#   (turns out there are no)
# - If for every q' in Sucs(q,γ') there is only one good constraint for q 
#   then (q,γ) will be a real good pair.
# - Otherwise it is a good pair.
#
CheckAllSuccessors := function()
    local IntermediatePairs,BadPairs,RealGoodPairs,i,gamma,q,res;
    RealGoodPairs := [];
    IntermediatePairs := [];
    BadPairs := [];
    for i in GoodRedConstraints do
        gamma := redConstraints[i];
        Info(InfoExamples,2,"Testing gamma_",i," of 8:");
        for q in gP[i] do
            res := GetSuccessor(q,gamma);
            if Size(res)=0 then
                Add(BadPairs,[gamma,q]);
                continue;
            fi;
            if ForAny(res,r->ForAll(r[2],q->Size(getGoodConst(q))=1)) then
                Add(RealGoodPairs,[gamma,q]);
            else
                Add(IntermediatePairs,[gamma,q,res]);
            fi;
            Info(InfoExamples,2,Size(IntermediatePairs),
                " good ones and ",Size(RealGoodPairs),
                " real good and ",Size(BadPairs),
                " bad ones so far\r");
        od;
    od;
    Info(InfoExamples,2,Size(IntermediatePairs)," good ones and ",Size(RealGoodPairs)," real good and ",Size(BadPairs)," bad ones so far\n");
    return [RealGoodPairs,IntermediatePairs,BadPairs];
end;

Info(InfoExamples,2,"Verify that forall γ∈R₁ there are good succeccors. Takes about two hours\n");
if GasmanLimits().max <= 6*(1024)^2 then
    Info(InfoExamples,2,"There is prop. not enoug memory. Consider restarting with the -o parameter.\n But trying anyway...\n");
fi;
ReReR := CheckAllSuccessors();;
Assert(0,Size(ReReR[3])=0);

Inter := ReReR[2];;
S1 := List(Inter,r->[r[1],r[2]]);;

Info(InfoExamples,2,"Verify that all pairs in S₁ have real good descendents\n");
i:=1;
for I in Inter do
    gamma := I[1];
    q := I[2];
    res := List(I[3],r->[ ReducedConstraint(r[1]),r[2] ]);
    if ForAny(res,r->ForAll(r[2],q->not [r[1],q] in S1)) then 
        Info(InfoExamples,2,i," done of ",Size(Inter),".\r");
    else
        Error("Inter[",i,"] has no real good descendents\n");
    fi;
    i := i+1;
od;
Info(InfoExamples,2,"Everything done, everything fine\n");

