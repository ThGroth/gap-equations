if not IsExistingFile("./gap/declarations.g") then
    Error("Please start this 'verify.g' script in the main directory of the archive.");
fi;

dir := Directory("gap");
Read(Filename(dir,"init.g"));
if not TestPackageAvailability( "fr","3.3") = fail then
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
# ∙ ConjugacyConstraints : For each q∈G'/K' a constraint γ and γ' such that 
#   					   forall g ∈ τ⁻¹(q) the successor of 
#   					   (a^x₁a^x₂a^x₃a^x₄a^x₅ag,γ) is (R₂(g@2)(g@1),γ')
#   					   and ((g@2)(g@1),γ') is a good pair. 
# ∙ GermGroup4 : The 4ᵗʰ level germgroup of the Grigorchuk group.
# ∙ CharTblGermGroup4 : The character table of the 4ᵗʰ level germgroup
# 						together with the list of irreducible characters.
# ∙ nonCommutatorGermGroup4 : An element of derived of the 4ᵗʰ level germgroup 
# 							  which is not a commutator.
# (∙ nonCommutatorG : Only available with loaded FR package: an element of G' which is not
# 					  a commutator. )
# (∙ epiGermGroup4 : Only available with loaded FR package: The epimorphism G → GermGroup4 )
PCD := LoadPrecomputedData();;

#
# Allow recomputation of the precomputed data. 
# possible modes are:
# ∙ "orbits" : compute the orbits of Aut(F₆)/Stab(R₃). Runtime: ~12h
# ∙ "goodpairs" : computes all good pairs for all possible constraints and 
# 				  the graph of the successors. Runtime: ~3/4h
# ∙ "conjugacywidth" : computes the succecors for the product of 6 conjugate equations.
# 				  Runtime: ~1h
# ∙ "charactertable" : computes the character table with irreducibles of 
# 					   the 4ᵗʰ germ group. Runtime ~16h
# ∙ "noncommutator" : computes an element of G which is not a commutator.
# 					  Runtime ~2h 					  
# ∙ "all" : Do all of the above.
# Additionally it is possible to give a list of modes. They are then performed in
# the given order. 
#
RedoPrecomputation := function(mode)
	if not DeclarationsLoadedFR then
		Error("To redo the precomputation the fr package must be available.");
	fi;
	if IsList(mode) and not IsString(mode) then
		Perform(mode,RedoPrecomputation);
	elif LowercaseString(mode) = "orbits" then
		Read(Filename(dir,"precomputeOrbits.g"));
	elif  LowercaseString(mode) = "goodpairs"  then
		Read(Filename(dir,"precomputeGoodPairs.g"));
	elif  LowercaseString(mode) = "conjugacywidth"  then
		Read(Filename(dir,"precomputeConjugacyWidth.g"));
	elif  LowercaseString(mode) = "charactertable"  then
		Read(Filename(dir,"precomputeCharacterTableGermGroup.g"));	
	elif  LowercaseString(mode) = "noncommutator"  then
		Read(Filename(dir,"precomputeNonCommutator.g"));	
		Read(Filename(dir,"precomputeNonCommutatorNoFR.g"));	
	elif  LowercaseString(mode) = "all"  then
		Read(Filename(dir,"precomputeOrbits.g"));
		Read(Filename(dir,"precomputeGoodPairs.g"));
		Read(Filename(dir,"precomputeConjugacyWidth.g"));
		Read(Filename(dir,"precomputeCharacterTableGermGroup.g"));	
		Read(Filename(dir,"precomputeNonCommutator.g"));	
		Read(Filename(dir,"precomputeNonCommutatorNoFR.g"));
	else
		Error("Input must be \"orbits\", \"goodPairs\" , \"conjugacywidth\", \"charactertable\", \"noncommutator\" or \"all\"");
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
verifyLemma86orbits := function()
	return Size(PCD.orbitReps2)=86;
end;
verifyLemmaExistGoodConstraints := function()
	return ForAll(GPmodKP,q->ForAny(Filtered(PCD.ReducedConstraintsActive,E->E.length=6),E->q in E.goodPairs));
end;

verifyLemmaExistGoodConstraints4 := function()
	return ForAll(GPmodKP,q->ForAny(Filtered(PCD.ReducedConstraintsActive,E->E.length=4),E->q in E.goodPairs));
end;

verifyExistGoodConjugacyConstraints := function()
	return ForAll(GPmodKP,q->ForAny(PCD.ConjugacyConstraints,cc->cc[1]=q));
end;

verifyPropExistsSuccessor := function()
	return ForAll(PCD.ReducedConstraintsActive,
		gamma->ForAll(gamma.goodPairs,
			q->not PositionProperty(PCD.RealGoodPairs,
				L->L[1]=q and L[2]=gamma) = fail));
end;

#verifyLemmaStatesOfKPinKxK := function()
#	return ForAll(GenKPLP,x->ForAll([1,2],i->State(x^isoGLPtoG,i)^isoGtoGLP in KxKLP));
#end;

verifyCorollaryFiniteCWK := function()
	return not  PCD.specialSuccessor = fail;
end;

verifyGermGroup4hasCW2 := function()
	return IsBound(PCD.nonCommutatorGermGroup4);
end;

verifyAll := function()
	local func;
	for func in [	verifyLemma90orbits,
					verifyLemma86orbits,
					verifyLemmaExistGoodConstraints,
					verifyLemmaExistGoodConstraints4,
					verifyPropExistsSuccessor,
					verifyCorollaryFiniteCWK,
					verifyExistGoodConjugacyConstraints,
					verifyGermGroup4hasCW2
#					verifyLemmaStatesOfKPinKxK
				] do
		Info(InfoCW,1,NameFunction(func),": ",func(),"\n");
	od;
end;
verifyAll();