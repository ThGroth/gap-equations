if not IsBound(dir) then
    dir := Directory("gap");
fi;



NestedListElm := function(L,entry)
    if Size(entry) = 1 then
        return L[entry[1]];
    fi;
    return NestedListElm(L[entry[1]],entry{[2..Size(entry)]});
end;

#
# Save a map which assigns to each element of Q⁵ the corresponding orbit.
#
hashInQ := function(q)
    if q in Q then
        return Position(QL,q);
    else 
        Error("Can't compute hash ",q," is not in Q.");
    fi;
end;


# γ: Fₙ→Q is mapped to Act(γ): Fₙ→ {(),(1,2)}
#
ActivityQ := function(q)
    if Position(QL,q) in [ 2, 3, 6, 7, 10, 11, 14, 15 ] then
        return (1,2);
    fi;
    return ();
end;

ActivityConstraint := function(gamma)
    if IsList(gamma) then
        return List(gamma,x->ActivityQ(x));
    elif IsRecord(gamma) then
        return List(gamma.constraint,x->ActivityQ(x));
    fi;
end;

HasNontrivialActivity := function(gamma)
    return not ForAll(ActivityConstraint(gamma),IsOne);
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
# ∙ ConjugacyConstraints : For each q∈G'/K' a constraint γ and γ' such that 
#   forall g ∈ τ⁻¹(q) the successor of 
#   (a^x₁a^x₂a^x₃a^x₄a^x₅ag,γ) is (R₂(g@2)(g@1),γ') and ((g@2)(g@1),γ') is a good pair. 
LoadPrecomputedData := function()
    local PCD,AGP,RGP,NonCom;
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
    PCD.ConjugacyConstraints := ReadAsFunction(Filename(dir,"PCD/conjugacySuccessors.go"))();
    NonCom := ReadAsFunction(Filename(dir,"noncommutatorNoFR.g"))();
    PCD.GermGroup4 := NonCom.GermGroup4;
    PCD.nonCommutatorGermGroup4 := NonCom.noncom;
    return PCD;
end;