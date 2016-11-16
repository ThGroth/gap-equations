ReduceConstraint := function(gamma)
	local F;
	if IsGroupHomomorphism(gamma) then
    	F := Source(gamma);
    elif  IsList(gamma)  then
    	F := FreeGroup(2*Int(Ceil(Float(Size(gamma)/2))));
    else
    	Error("Wrong input: gamma must be either a homorphism from a free group or a list");
    fi;
	return GammaSimplify(gamma,F);
end;

verifyLemma90orbits := function(usePrecomputed)
	if  usePrecomputed  then
		#statements
		#TODO
	else 

	fi;
end;

verifyLemmaExistGoodGammas := function(usePrecomputed)
	if  usePrecomputed  then
		return ForAll(GPmodKP,q->ForAny(ReducedConstraintsActive,E->q in E.goodPairs));
	else
		#TODO
	fi;
end;

verifyPropExistsSuccessor := function(usePrecomputed)
	# The resulting list RealGoodPairs contains tuples (q,γ,[γ',x,[q₁,…,q₁₆]]) foreach
	# q ∈ G'/K', γ∈orbitReps such that γ has nontrivial activity and (q,γ) is a good pair.
	# The element [γ',x,[q₁,…,q₁₆]] has the property that 
	#   ∙(γ',qᵢ) are good pairs ∀i=1,…,16 and γ' has activity in some component
	#   ∙if g ∈ τ⁻¹(q) then (g@2)^Rep(x) ⋅ (g@1) ∈ τ⁻¹(qᵢ) for some i ∈ {1,…,16}
	#   ∙if (R₂ₙ-₁ (g@2)^Rep(x) ⋅ g@1 ,γ') is sattisfiable then so is (Rₙ g,γ)
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
			Print(Int(count*100/size),"% done. ",Size(RealGoodPairs)," good ones so far.\r");
			count := count+1;
		od;
	od;
	return(Size(BadPairs)=0)
end;

verifyLemmaStatesOfKPinKxK := function()
	return ForAll(GenKPLP,x->ForAll([1,2],i->State(x^isoGPLtoG,i)^isoGtoGLP in KxKLP));
end;

verifyCorollaryFiniteCWK := function(#param)
	#TODO
	#statements
end;

