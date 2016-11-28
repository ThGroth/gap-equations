if not IsBound(dir) then
    dir := Directory("gap");
fi;
# action on images of automorphism.
# typical usage: action on tuples of images of generators.
OnImages := function(list,aut)
    local gens;
    gens := GeneratorsOfGroup(Source(aut));
    return List(gens,g->MappedWord(g^aut,gens,list));
end;

NestedListElm := function(L,entry)
    if Size(entry) = 1 then
        return L[entry[1]];
    fi;
    return NestedListElm(L[entry[1]],entry{[2..Size(entry)]});
end;

#The surface relator Rₙ=[x₁,x₂]…[x₂ₙ-₁,x₂ₙ] where the free group F is generated by x₁,x₂,…,x₂ₙ
surface_relator := function(F)
    local gens;
    gens := GeneratorsOfGroup(F);
    return Product([2,4..Length(gens)],i->Comm(gens[i-1],gens[i]),One(F));
end;

#
# Save a map which assigns to each element of Q⁵ the corresponding orbit.
#
hashInQ := function(q)
    if q in Q then
        return Position(List(Q),q);
    else 
        Error("Can't compute hash ",q," is not in Q.");
    fi;
end;

# A "random" Element of G' as word of at most 100 generators
AnGpLPElement := function()
    local n,g;
    g := One(GpLP);
    for n in [1..Random([1..100])] do
        g := g*Random(GPGen);
    od;
    return g;
end;

# The below function returns for a given γ∈Q⁶ 
# the list of all q∈G'/K' such that (q,γ) is a good pair
goodPairs := function(gamma)
    local S1,S2,S3,F,P,P2,p,q,r;
    if Size(gamma)<6 then
        gamma := ShallowCopy(gamma);
        Append(gamma,ListWithIdenticalEntries(6-Size(gamma),One(gamma[1])));
    fi;
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

# γ: Fₙ→Q is mapped to Act(γ): Fₙ→ {(),(1,2)}
#
ActivityConstraint := function(gamma)
    if IsList(gamma) then
        return List(gamma,x->Activity(PreImagesRepresentative(pi,x)));
    elif IsRecord(gamma) then
        return List(gamma.constraint,x->Activity(PreImagesRepresentative(pi,x)));
    fi;
end;
HasNontrivialActivity := function(gamma)
    return not ForAll(ActivityConstraint(gamma),IsOne);
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
#       the list ReducedConstraints. To use this mode give the List 
#       of reduced constraints as a third and the orbit table as 
#       a fourth argument. 
# ∙ if mode = 1:
#       No lookup is done in the orbit table. This is usefull if the
#       orbit table is not computed. The output is then not a record
#       but a List with 6 element in Q.
# ∙ if mode = 2:
#       No lookup is done either and the return value is a list [γ,φ]
#       where γ is the reducedConstraint as in mode 1 and 
#       φ is a an automorphism of F₂ₙ which performs the reduction
#   
# 
#
ReducedConstraintAllModes := function(gamma,mode,arg...)
    local TempOrbitTable, F, gens, d, L, i, phi,psi,swi,id,imgs,Phi,ph,ActionOnList,x,
    KillBlock,KillAllBlocks,NormalizeBlock,NormalizeAllBlocks,offset,
    RepresentativeInOrbitReps,ReducedConstraints,gammasize;

    
    if mode = 0 then
        if Size(arg)<3 then
            Error("To use lookup mode the orbitTable, the ReducedConstraints and the offset must be present. Try using mode 1");
        fi;
        TempOrbitTable := arg[2];
        ReducedConstraints := arg[1];
        offset := arg[3];
    fi;
    if IsGroupHomomorphism(gamma) then
        gamma := List(GeneratorsOfGroup(Source(gamma)),x->x^gamma);
    fi;
    if IsList(gamma)  then
        if IsOddInt(Size(gamma)) then
            Error("Wrong input: gamma must be defined on a even number of generators");
        fi;
        F := FreeGroup(2*Int(Ceil(Float(Size(gamma)/2))));
    else
        Error("Wrong input: gamma must be either a homorphism from a free group or a list");
    fi;


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
    # NormalizeBlock sends block of the form (G,G) to (G,Mod)
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
        return NestedListElm(TempOrbitTable,List(gamma,hashInQ));
    end;

    #Now do the real work...
    ph := NormalizeAllBlocks(1,gamma,C1);
    if mode = 2 then
        Phi := ph;
    fi;

    gamma := ActionOnList(gamma,ph); # (Q,C1,Q,C1,Q,C1,Q,C1…)
    Assert(2,ForAll(gamma{[2,4..Size(gamma)]},x->x in C1));

    ph := KillAllBlocks(1,gamma,C1);
    if mode = 2 then
        Phi := ph*Phi;
    fi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C1,C1,C1,C1,C1…)
    Assert(2,ForAll(gamma{[2..Size(gamma)]},x->x in C1));

    ph := NormalizeAllBlocks(3,gamma,C2);
    if mode = 2 then
        Phi := ph*Phi;
    fi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C1,C2,C1,C2,C1,C2…)
    Assert(2,ForAll(gamma{[4,6..Size(gamma)]},x->x in C2));

    ph := KillAllBlocks(3,gamma,C2);
    if mode = 2 then
        Phi := ph*Phi;
    fi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C2,C2,C2,C2,C2,C2…)
    Assert(2,ForAll(gamma{[4..Size(gamma)]},x->x in C2));

    ph := NormalizeAllBlocks(5,gamma,Group(One(C1))); #Trivial Mod
    if mode = 2 then
        Phi := ph*Phi;
    fi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C2,1,C2,1,C2,1…)
    Assert(2,ForAll(gamma{[6,8..Size(gamma)]},IsOne));

    ph := KillAllBlocks(5,gamma,Group(One(C1))); #Trivial Mod
    if mode = 2 then
        Phi := ph*Phi;
    fi;
    gamma := ActionOnList(gamma,ph); # (Q,C1,C1,C2,C2,1,1,1,1,1…)
    Assert(2,ForAll(gamma{[6..Size(gamma)]},IsOne));

    if mode = 2 then
        Phi := ph*Phi;
        Assert(2,surface_relator(F)^Phi=surface_relator(F));
    fi;
    if mode = 2 then
       return [gamma{[1..Minimum(6,Size(gamma))]},Phi];
    elif mode = 1 then
       return gamma{[1..Minimum(6,Size(gamma))]};
    else
       return ReducedConstraints[offset+RepresentativeInOrbitReps(gamma{[1..Minimum(6,Size(gamma))]})];
    fi;
end;

#returns a record of all precomputed data
# ∙ orbitReps : A list of representatives for the orbits of Aut(F₆)/Stab(R₃)
# ∙ orbitReps2 : A list of representatives for the orbits of Aut(F₄)/Stab(R₂)
# ∙ orbitTable : A nested list where the entry orbitTable[i₁][i₂][i₃][i₄][i₅][1] is 
#                the index of the element γ:xₖ↦List(Q)[iₖ] in the list of orbits #                
#                especially orbitReps[orbitTable[i₁][i₂][i₃][i₄][i₅][1]] is a representative.
# ∙ orbitTable2 : A nested list where the entry orbitTable[i₁][i₂][i₃][i₄] is 
#                the index of the element γ:xₖ↦List(Q)[iₖ] in the list of orbits 
#                especially orbitReps2[orbitTable2[i₁][i₂][i₃][i₄]] is a representative.#                
# ∙ ReducedConstraints : The list of all reduced constraints as records with additional information
# ∙ ReducedConstraintsActive : The list of active reduced constraints as records with additional information
# ∙ RealGoodPairs : The list of all good pairs where a successor exists.
# ∙ specialSuccessor : The successor of (1,[1,1,1,1]) 
LoadPrecomputedData := function()
    local PCD,AGP,RGP;
    PCD := rec( orbitReps :=ReadAsFunction(Filename(dir,"PCD/orbitReps.go"))(),
                orbitReps2 :=ReadAsFunction(Filename(dir,"PCD/orbitReps2.go"))(),
                orbitTable := ReadAsFunction(Filename(dir,"PCD/orbitTable.go"))(),
                orbitTable2 := ReadAsFunction(Filename(dir,"PCD/orbitTable2.go"))()
            );
    PCD.ReducedConstraints := List([1..Size(PCD.orbitReps)],
                                i->rec(index:= i, length := 6, constraint:=PCD.orbitReps[i]));
    Append(PCD.ReducedConstraints,List([1..Size(PCD.orbitReps2)],
    i->rec(index:= i+Size(PCD.orbitReps), length := 4, constraint:=PCD.orbitReps2[i])));;
    PCD.ReducedConstraintsActive := Filtered(PCD.ReducedConstraints,E->HasNontrivialActivity(E.constraint));
    AGP := List(ReadAsFunction(Filename(dir,"PCD/AllGoodPairs.go"))(),
                L->List(L,i->List(GPmodKP)[i]));
    Perform(PCD.ReducedConstraints,function(E) E.goodPairs:=AGP[E.index]; end);
    RGP := List(ReadAsFunction(Filename(dir,"PCD/RealGoodPairs.go"))(),
                L->[List(GPmodKP)[L[1]],
                    PCD.ReducedConstraints[L[2]],
                    [PCD.ReducedConstraints[L[3][1]],L[3][2]]]);;
    PCD.RealGoodPairs := RGP;
    PCD.specialSuccessor := ReadAsFunction(Filename(dir,"PCD/specSuc.go"))();
    return PCD;
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
#       the list ReducedConstraints. To use this mode give the orbit table
#       as a third argument. 
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
# ReducedConstraint(γ)=ReducedConstraintAllModes(γ,0,orbitTable)
PCD := LoadPrecomputedData();;
ReducedConstraint := function(gamma)
    if IsList(gamma) and Size(gamma) = 4 then
        return ReducedConstraintAllModes(gamma,0,PCD.ReducedConstraints,PCD.orbitTable2,Size(PCD.orbitReps));
    fi;
    return ReducedConstraintAllModes(gamma,0,PCD.ReducedConstraints,PCD.orbitTable,0);
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
    local gammaRec,E;
    if not q in GPmodKP then
        if not q in GLP then
            q := q^isoGtoGLP;
        fi;
        q := q^tauLP;
    fi;
    if IsRecord(gamma) then
        return q in gamma.goodPairs;
    fi;
    if IsGroupHomomorphism(gamma) then
        gamma := List(GeneratorsOfGroup(Source(gamma)),gen->gen^gamma);
    fi;
    gammaRec := First(PCD.ReducedConstraints,E->E.constraint=gamma);
    if gammaRec = fail then
        gammaRec := ReducedConstraint(gamma);
    fi;
    return q in gammaRec.goodPairs;
end;

# Returns the next good pair (g',γ') such that (Rₙg,γ) is solvable if 
# (R₂ₙ-₁ g' ,γ') is solvable for n≥2.
# Input: 
#    g ∈ G,GLP 
#    γ ∈ Q^n for some n≥4 with activity in some component
# Output:
#    [g',γ'] ∈ G,GLP × orbitReps  accordingly to the input
GetSuccessorLookup := function(g,gamma) 
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
    gamma:= ReducedConstraint(gamma);
    if not IsGoodPair(q,gamma) then
        Error("(q,gamma) needs to be a good pair.\n");
    fi;
    if HasNontrivialActivity(gamma) then
        gaP := First(PCD.RealGoodPairs,L->L[1]=q and L[2]=gamma);
        if gaP = fail then
            return fail;
        fi;
        gaP := gaP[3];
        next := [State(g,2)^PreImagesRepresentative(pi,gaP[2])*State(g,1),gaP[1]];
        if inLP then
            next[1] := next[1]^isoGtoGLP;
        fi;
        Assert(0,IsGoodPair(next[1],next[2]));
        return next;
    else
        Error("gamma has no activity\n");
    fi;
end;