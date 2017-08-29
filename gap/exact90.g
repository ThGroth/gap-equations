if not IsBound(dir) then
    dir := Directory("gap");
fi;
if not IsBound(DeclarationsLoadedFR)  then
    LoadPackage("fr");
    Read(Filename(dir,"declarationsFR.g"));
    Read(Filename(dir,"functionsFR.g"));
fi;
#For checking that Red₃=Red₄ it's enough to check that 
# forall γ∈Q⁸ and θ ∈ U₄ we have rep(y)=rep(θ(γ)) 
# Furthermore we can reduce this to γ∈Red₂×Q⁴, and θ a generator of U₄
#  that changes one of the last 2 coordinates.

U_n_interesting_gens := function(F)
    local gens, d, L, i, imgs, x;
    gens := GeneratorsOfGroup(F);
    d := Length(gens);
    L := [];

    for i in [d] do
        imgs := ShallowCopy(gens);
        imgs[i] := gens[i-1]*gens[i];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;
    for i in [d-1] do
        imgs := ShallowCopy(gens);
        imgs[i] := gens[i+1]*gens[i];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;
    for i in [d-3] do
        imgs := ShallowCopy(gens);
        x := gens[i+1]/gens[i+2];
        imgs[i] := x*gens[i];
        imgs[i+1] := x*gens[i+1]/x;
        imgs[i+2] := x*gens[i+2]/x;
        imgs[i+3] := x*gens[i+3];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;

    # check that indeed the surface relator is preserved
    x := surface_relator(F);
    Assert(0,ForAll(L,g->x^g=x));
    
    return L;
end;

#Show that Red₃=Red₄
TheTest := function(n)
    local gens, Firstpa,Secondpa,size,gamma,gamma1,gamma2,theta,count,ind1,ind2;
    gens := U_n_interesting_gens(FreeGroup(2*n));
    if n=4 then
        Firstpa := PCD.orbitReps2;;
    else
        Firstpa := PCD.orbitReps;;
    fi;
    if n=4 then
        Secondpa:= Cartesian(ListWithIdenticalEntries(4,BS.group));;
    else
        Secondpa:= Cartesian(ListWithIdenticalEntries(2*n-6,BS.group));;
    fi;
    size := Size(Firstpa)*Size(Secondpa);
    # Storing the results in a lookup dictionary doesn't help. 
    # The lookup of all elements is not much faster.
    count := 1;
    for gamma1 in Secondpa do
        for gamma2 in Firstpa do
            gamma := Concatenation(gamma1,gamma2);
            for theta in gens do
                if not ReducedConstraint(OnImages(gamma,theta)).index=ReducedConstraint(gamma).index then
                    Info(InfoCW,1,"Claim not true for gamma:",gamma," and theta:",theta,"\n\n");
                    return [gamma,theta];
                fi;
            od;
            Info(InfoCW,1,count," that are ",Int(100*count/size),"% done\r");
            count := count +1;
    od;od;
    Info(InfoCW,1,"\nClaim true\n");
    return [];
end;
Info(InfoCW,1,"Check wheater Red₄=Red₃\n");
res:=TheTest(4);
Info(InfoCW,1,"Took ",Int(time/(60*1000))," minutes\nCheck wheater Red₅=Red₃\n");
res:=TheTest(5);
Info(InfoCW,1,"Took ",Int(time/(60*1000))," minutes\n.);



