# Directory for Saved results. Needs a trailing /
#
if not IsBound(dirRep) then
    dirRep := "~/Repositories/GrigorchukCommutatorWidth/";
    #
    dir := Concatenation(dirRep,"gap/90orbs/");
fi;

if not IsBound(DeclarationsLoaded)  then
    Read(Concatenation(dirRep,"gap/declarations.g"));
    Read(Concatenation(dirRep,"gap/functions.g"));
fi;

#Set up all Branchstructure, quotients etc.
#Working with L presentation
#All groups with LP in the name means that they are subgroups of the 
#L-Presented Grigorchuk group.

#Assert(0,ForAll(GenKPLP,x->ForAll([1,2],i->State(x^isoGPLtoG,i)^isoGtoGLP in KxKLP)));
#See verifyLemmaStatesOfKPinKxK instead
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
StateModKxK := function(q,i)
    local g;
    if not q in GmodKP then
        Error("q needs to be in G/K'");
    fi;
    g := PreImagesRepresentative(tauLP,q)^isoGPLtoG;
    return (State(g,i)^isoGtoGLP)^homGtoGmodKxK;
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
Assert(0,ForAll(ReducedConstraints,E->E.goodPairs = AGP[E.index]));
#Usage of the file:
#Perform(ReducedConstraints,function(E) E.goodPairs:=AGP[E.index]; end);

#######################################################################################
#######################################################################################
#					Computation of the good pairs is done
#######################################################################################
#######################################################################################

# Rₐₜ active representatives
ReducedConstraintsActive := Filtered(ReducedConstraints,E->HasNontrivialActivity(E.constraint));;

#Make sure that forach q in G'/K' there is a good active pair involving q.
#See verifyLemmaExistGoodGammas instead
#Assert(0,ForAll(GPmodKP,q->ForAny(ReducedConstraintsActive,E->q in E.goodPairs)));


ReducedConstraint := function(gamma)
    return ReducedConstraintAllModes(gamma,0,orbitTable);
end;

#For q in G'/K'
#Get List of all reduced constraints γ such that (q,γ) is a good pair.
GetAllGoodGammas := function(q)
    return Filtered(ReducedConstraints,E->q in E.goodPairs);
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
    local gammaRec;
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
    gammaRec := First(ReducedConstraints,E->E.constraint=gamma);
    if gammaRec = fail then
        gammaRec := ReducedConstraint(gamma);
    fi;
    return q in gammaRec.goodPairs;
end;


#
# Given a good pair (q,γ) where γ has nontrivial activity 
# 
# This method tries to compute a pair (γ',x) with the following property:
# ∙ γ' has nontrivial activity
# ∙ x ∈ {1,a,b,c,d,ab,ad,ba}
# ∙ for all g with g^τ=q 
# 	the sattisfiabillity of (R₂ₙ-₁ (g@2)^x ⋅ g@1 ,γ') implies the 
# 	sattisfiabillity of Rₙg,γ
# ∙ ((g@2)^x ⋅ g@1 , γ') is a good pair 
# 
# If the search for such a pair fails, the method returns fail, this doesn't 
# guarantee that such a pair does not exists.
# 
# 
# Given a good pair (q,γ) where γ has trivial activity 
# 
# This method tries to compute a pair (γ₁,γ₂) with the following property:
# ∙ γ₁,γ₂ have both nontrivial activity
# ∙ for all g with g^τ=q 
#   the sattisfiabillity of both (Rₙ(g@1),γ₁) and (Rₙ(g@2),γ₂) implies the 
#   sattisfiabillity of (Rₙg,γ)
# ∙ ((g@1),γ₁) and ((g@2),γ₂) are good pairs
# If the length of γ is 4 then the computed pair (γ₁,γ₂) has the additional 
# property that γ₁,γ₂ are again of length four.
GetSuccessor  := function(q,gamma)
	local q1,q2,F,acts,F2,frvars,frinvvars,t,I,normalforms,x,v,w,indx,v1,
          v2,w1,w2,newEq,NoFI,NoFIhom,z,GHOnList,Gamma1,Dep,i,ga,first,gp,
          trans,H,gpp,nf,gaP,Suc,r,ShortConstraintCase,qs;

    ShortConstraintCase := false;
    if IsGroupHomomorphism(gamma) then
        gamma = List(GeneratorsOfGroup(Source(gamma)),x->x^gamma);
    fi;
	if Size(gamma)>6 then
		Error("gamma is too large!\n It need to be a reduced constraint");
	elif Size(gamma)=5  then
		Add(gamma,One(gamma[1]));
    elif Size(gamma)=4  then
        ShortConstraintCase := true;
	elif Size(gamma)<4  then
		Error("invalid gamma!\n");
	fi;
	if not q in GmodKP then
		Error("q has to be in G/K'\n");
	fi;
		
	q1:= StateLP(q,1)^isoGmodKtoQ;
	q2:= StateLP(q,2)^isoGmodKtoQ;
	F := FreeGroup(4*3-2);
	

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
    #Gamma1 contains all possible γ' such that <<γ'₂ₖ-₁,γ'₂ₖ>> = γₖ for k=1…6
    Gamma1 := DEP_CARTESIAN@fr(Gamma1,Dep);;#Size of Gamma1 about 4096
    
    #Needed for the product of two commutator case. Make sure the last constraints are trivial.
    if ShortConstraintCase then
        Perform(Gamma1,ga->Append(ga,[One(Q),One(Q)]));
    fi;
    
    acts := ActivityConstraint(gamma);
	if ForAll(acts,IsOne) then #this is needed for the product of two commutators and the f.c.w. of K' corrolary
        for gp in Gamma1 do
            gp := [gp{[1,3,5,7,9,11]},gp{[2,4,6,8,10,12]}]; #split gamma in two parts
            qs := [q1,q2];
            if ForAll(gp,gpi->HasNontrivialActivity(gpi)) then #No need for those with trivial activity
                if ForAll([1,2],i->IsOne(Comm(gp[i][1],gp[i][2])*Comm(gp[i][3],gp[i][4])*Comm(gp[i][5],gp[i][6])*qs[i])) then
                    Sucs := Cartesian(List([1,2],i->PreImages(varpiPrimeLP,StateModKxK(q,i))));
                    if ForAll(Sucs, r->ForAll([1,2],i->IsGoodPair(r[i],gp[i]))) then
                        if ShortConstraintCase then
                            Apply(gp,gpp->gpp{[1..4]});
                        fi;
                        return gp;
                    fi;
                fi;
            fi;
        od;
    
        return fail;
	fi;
    #Now the "regular" case. gamma has activity in some component.
	
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
                    Add(gaP,Suc); #Adding all possible succeccors mod K' to the returned list
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
ComputeAllSuccessors := function()
    local size,count,RealGoodPairs,BadPairs,E,gamma,q,gammap;
    size := Sum(List(AGP,Size));
    count := 0;
    RealGoodPairs := [];
    BadPairs := [];
    for E in ReducedConstraintsActive do
        gamma := E.constraint;
        for q in E.goodPairs do
            gammap := GetSuccessor(q,gamma);
            if not gammap = fail then
                Add(RealGoodPairs,[q,E,gammap]);
            else
                Add(BadPairs,[q,gamma]);
            fi;
            Print(Int(count*100/size),"% done. ",Size(RealGoodPairs)," good ones so far and ",Size(BadPairs)," bad ones.\r");
            count := count+1;
        od;
    od;
    return [RealGoodPairs,BadPairs];
end;
T := ComputeAllSuccessors();;
RealGoodPairs := T[1];;
BadPairs := T[2];
Assert(0,Size(BadPairs)=0);

#Save RealGoodPairs to a file
#Just store the index of the constraint and forget the successing qᵢs
RealGoodPairsFile := Concatenation(dir,"RealGoodPairs.go");
PrintTo(RealGoodPairsFile,List(RealGoodPairs,L->[Position(List(GPmodKP),L[1]),L[2].index,[L[3][1].index,L[3][2]]]));
#Replace <identy>.... by One(Q)
Exec("sed","-i","\"s/<identity> of .../One(Q)/g\"",RealGoodPairsFile);
#Add a return and a semicolon
Exec("sed","-i","\"1i return \"",RealGoodPairsFile);
Exec("sed","-i","\"\\$a ;\"",RealGoodPairsFile);

#Read the file again:
RGP := List(ReadAsFunction(RealGoodPairsFile)(),
    L->[List(GPmodKP)[L[1]],ReducedConstraints[L[2]],[ReducedConstraints[L[3][1]],L[3][2]]]);;
#Check only the succesing qᵢs are forgotten.
Assert(0,List(RealGoodPairs,P->[P[1],P[2],[P[3][1],P[3][2]]] )=RGP);

