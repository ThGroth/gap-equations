if not IsExistingFile("./gap/declarations.g") then
    Error("Please start this 'verify.g' script in the main directory of the archive.");
fi;

dir := Directory("gap");
Read(Filename(dir,"init.g"));
if not TestPackageAvailability( "fr","2.3") = fail then
	LoadPackage("fr");
	Read(Filename(dir,"declarationsFR.g"));
	Read(Filename(dir,"functionsFR.g"));
else
	Read(Filename(dir,"declarations.g"));
	Read(Filename(dir,"functions.g"));
fi;

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
	if not DeclarationsLoadedFR then
		Error("To redo the precomputation the fr package must be available.");
	fi;
	if LowercaseString(mode) = "orbits" then
		Read(Filename(dir,"precomputeOrbits.g"));
	elif  LowercaseString(mode) = "goodpairs"  then
		Read(Filename(dir,"precomputeGoodPairs.g"));
	elif  LowercaseString(mode) = "all"  then
		Read(Filename(dir,"precomputeOrbits.g"));
		Read(Filename(dir,"precomputeGoodPairs.g"));
	else
		Error("Input must be \"orbits\", \"goodPairs\" or \"all\"");
	fi;
	PCD := LoadPrecomputedData();;
end;



##################################################################################
##################################################################################
##################################################################################
#####################     verify functions        ################################
##################################################################################
##################################################################################
##################################################################################


verifyLemma90orbits := function()
	return Size(PCD.orbitReps)=90;
end;

verifyLemmaExistGoodConstraints := function()
	return ForAll(GPmodKP,q->ForAny(Filtered(PCD.ReducedConstraintsActive,E->E.length=6),E->q in E.goodPairs));
end;

verifyLemmaExistGoodConstraints4 := function()
	return ForAll(GPmodKP,q->ForAny(Filtered(PCD.ReducedConstraintsActive,E->E.length=4),E->q in E.goodPairs));
end;

verifyPropExistsSuccessor := function()
	return ForAll(PCD.ReducedConstraintsActive,
		gamma->ForAll(gamma.goodPairs,
			q->not PositionProperty(PCD.RealGoodPairs,
				L->L[1]=q and L[2]=gamma) = fail));
end;

#verifyLemmaStatesOfKPinKxK := function()
#	return ForAll(GenKPLP,x->ForAll([1,2],i->State(x^isoGPLtoG,i)^isoGtoGLP in KxKLP));
#end;

verifyCorollaryFiniteCWK := function()
	return not  PCD.specialSuccessor = fail;
end;

verifyAll := function()
	local func;
	for func in [	verifyLemma90orbits,
					verifyLemmaExistGoodConstraints4,
					verifyLemmaExistGoodConstraints,
					verifyPropExistsSuccessor,
					verifyCorollaryFiniteCWK,
#					verifyLemmaStatesOfKPinKxK
				] do
		Info(InfoCW,1,NameFunction(func),": ",func(),"\n");
	od;
end;
verifyAll();