dirRep := "~/Repositories/GrigorchukCommutatorWidth/";
dir := Concatenation(dirRep,"gap/90orbs/");

LoadPackage("fr");
Read(Concatenation(dirRep,"gap/declarations.g"));
Read(Concatenation(dirRep,"gap/functions.g"));

#PCD.
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
PCD := LoadPrecomputedData();;

#
# Allow recomputation of the precomputed data. 
# possible modes are:
# ∙ "orbits" : compute the orbits of Aut(F₆)/Stab(R₃). Runtime: ~12h
# ∙ "goodpairs" : computes all good pairs for all possible constraints and 
# 				  the graph of the successors. Runtime: ~3/4h
# ∙ "all" : Do both.
#
#
RedoPrecomputation := function(mode)
	#TODO remove the existsing precomputed files first?
	if LowercaseString(mode) = "orbits" then
		Read(Concatenation(dirRep,"gap/precomputeOrbits.g"));
	elif  LowercaseString(mode) = "goodpairs"  then
		Read(Concatenation(dirRep,"gap/precomputeGoodPairs.g"));
	elif  LowercaseString(mode) = "all"  then
		Read(Concatenation(dirRep,"gap/precomputeOrbits.g"));
		Read(Concatenation(dirRep,"gap/precomputeGoodPairs.g"));
	else
		Error("Input must be \"orbits\", \"goodPairs\" or \"all\"");
	fi;
	PCD := LoadPrecomputedData();;
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
# ReducedConstraintnoLookup(γ)=ReducedConstraintAllModes(γ,1)
# ReducedConstraintReturnHom(γ)=ReducedConstraintAllModes(γ,2)
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
    if IsGroupHomomorphism then
        gamma := List(GeneratorsOfGroup(Source(gamma)),gen->gen^gamma);
    fi;
    gammaRec := First(PCD.ReducedConstraints,E->E.constraint=gamma);
    if gammaRec = fail then
        gammaRec := PCD.ReducedConstraint(gamma);
    fi;
    return q in gammaRec.goodPairs;
end;

# Returns the next good pair (g',γ') such that (Rₙg,γ) is solvable if 
# (R₂ₙ-₁ g' ,γ') is solvable for n≥2.
# Input: 
#    g ∈ G,GLP 
#    γ ∈ Q^n for some n≥4 with activity in some component
# Output:
# 	 [g',γ'] ∈ G,GLP × orbitReps  accordingly to the input
GetSuccessor := function(g,gamma) 
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

##################################################################################
##################################################################################
##################################################################################
#####################     verify functions        ################################
##################################################################################
##################################################################################
##################################################################################


#TODO doublecheck this
#Well this is kind of strange.. now there are only 66 orbits. But
#even if this wouldn't be all they are sufficient to do the job.
verifyLemma90orbits := function()
	return Size(PCD.orbitReps)=90;
end;

verifyLemma66orbits := function()
	return Size(PCD.orbitReps)=66;
end;

verifyLemmaExistGoodGammas := function()
	return ForAll(GPmodKP,q->ForAny(PCD.ReducedConstraintsActive,E->q in E.goodPairs));
end;

verifyPropExistsSuccessor := function()
	return ForAll(PCD.ReducedConstraintsActive,
		gamma->ForAll(gamma.goodPairs,
			q->not PositionProperty(PCD.RealGoodPairs,
				L->L[1]=q and L[2]=gamma) = fail));
end;

verifyLemmaStatesOfKPinKxK := function()
	return ForAll(GenKPLP,x->ForAll([1,2],i->State(x^isoGPLtoG,i)^isoGtoGLP in KxKLP));
end;

verifyCorollaryFiniteCWK := function()
	return not  PCD.specialSuccessor = fail;
end;

verifyAll := function()
	local func;
	for func in [	verifyLemma66orbits,
					verifyLemmaExistGoodGammas,
					verifyPropExistsSuccessor,
					verifyLemmaStatesOfKPinKxK,
					verifyCorollaryFiniteCWK
				] do
		Print(NameFunction(func),": ",func(),"\n");
	od;
end;
