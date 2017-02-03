# Directory for Saved results. 
#
if not IsBound(dir) then
    dir := Directory("gap");
fi;
################################################################

if not IsBound(DeclarationsLoadedFR)  then
    LoadPackage("fr");
    Read(Filename(dir,"declarationsFR.g"));
    Read(Filename(dir,"functionsFR.g"));
fi;

#Assert(0,ForAll(GenKPLP,x->ForAll([1,2],i->State(x^isoGLPtoG,i)^isoGtoGLP in KxKLP)));
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
	g := PreImagesRepresentative(tauLP,q)^isoGLPtoG;
	return ((State(g,2)^h*State(g,1))^isoGtoGLP)^homGtoGmodKxK;
end;
# p = p₁
p := function(q)
	local g;
	if not q in GmodKP then
		Error("q needs to be in G/K'");
	fi;
	g := PreImagesRepresentative(tauLP,q)^isoGLPtoG;
	return ((State(g,2)*State(g,1))^isoGtoGLP)^homGtoGmodKxK;
end;
#the maps @i: G'/K' → G/K, gK' ↦ g@i K are well defined
StateLP := function(q,i)
	if not q in GmodKP then
		Error("State: q needs to be in G/K'");
	fi;
	return (State(PreImagesRepresentative(tauLP,q)^isoGLPtoG,i)^isoGtoGLP)^piLP;
end;
StateModKxK := function(q,i)
    local g;
    if not q in GmodKP then
        Error("q needs to be in G/K'");
    fi;
    g := PreImagesRepresentative(tauLP,q)^isoGLPtoG;
    return (State(g,i)^isoGtoGLP)^homGtoGmodKxK;
end;
#Load orbits here:
orbitReps:=ReadAsFunction(Filename(dir,"PCD/orbitReps.go"))();;
ReducedConstraints := List([1..Size(orbitReps)],
    i->rec(index:= i, length := 6, constraint:=orbitReps[i]));;
orbitTable := ReadAsFunction(Filename(dir,"PCD/orbitTable.go"))();;
orbitReps2:=ReadAsFunction(Filename(dir,"PCD/orbitReps2.go"))();;
Append(ReducedConstraints,List([1..Size(orbitReps2)],
    i->rec(index:= i+Size(orbitReps), length := 4, constraint:=orbitReps2[i])));;
orbitTable2 := ReadAsFunction(Filename(dir,"PCD/orbitTable2.go"))();;

#Takes about 1 min
# Compute the full list of good pairs
# Such that for each entry e in ReducedConstraints the list e.goodPairs contains
# all q∈Q such that (q,e.constraint) is a good pair.
Info(InfoCW,1,"Compute the good pairs for each ReducedConstraint. Takes a Minute.\n");
Perform(ReducedConstraints,function(entry) entry.goodPairs:=goodPairs(entry.constraint); end);


#Write AllGoodPairs to a file
AllGoodPairsFile := Filename(dir,"PCD/AllGoodPairs.go");
PrintTo(AllGoodPairsFile,Concatenation("return ",String(List(ReducedConstraints,E->List(E.goodPairs,q->Position(List(GPmodKP),q)))),";"));

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
    if IsList(gamma) and Size(gamma) = 4 then
        return ReducedConstraintAllModes(gamma,0,PCD.ReducedConstraints,PCD.orbitTable2,Size(PCD.orbitReps));
    fi;
    return ReducedConstraintAllModes(gamma,0,PCD.ReducedConstraints,PCD.orbitTable,0);
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
    if IsGroupHomomorphism(gamma) then
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
	local n,q1,q2,Gamma1,Dep,i,ga,first,gp,acts,qs,Suc,
	F2,F,EqG,DEqG,FF,DEqQ,DEqF2,Bridge,Eq,DEq,EqComp,I,normalforms,x,indx,newEq,z,
	H,nf,gaP,ShortConstraintCase,g1,g2;


    ShortConstraintCase := false;
    if IsGroupHomomorphism(gamma) then
        gamma := List(GeneratorsOfGroup(Source(gamma)),x->x^gamma);
    fi;
    n := Length(gamma);
	if n>6 then
		Error("gamma is too large!\n It need to be a reduced constraint");
	elif n=5  then
		Add(gamma,One(gamma[1]));
		n:=6;
    elif n=4  then
        ShortConstraintCase := true;
	elif n<4  then
		Error("invalid gamma!\n");
	fi;
	if not q in GmodKP then
		Error("q has to be in G/K'\n");
	fi;
		
	q1:= StateLP(q,1)^isoGmodKtoQ;
	q2:= StateLP(q,2)^isoGmodKtoQ;	

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
    
    acts := ActivityConstraint(gamma);
	if ForAll(acts,IsOne) then #this is needed for the product of two commutators and the f.c.w. of K' corrolary
        for gp in Gamma1 do
            gp := [gp{[1,3..2*n-1]},gp{[2,4..2*n]}]; #split gamma in two parts
            qs := [q1,q2];
            if ForAll(gp,gpi->HasNontrivialActivity(gpi)) then #No need for those with trivial activity
                if ForAll([1,2],i->IsOne(Product(List([1..Size(gamma)/2],k->Comm(gp[i][2*k-1],gp[i][2*k])))*qs[i])) then
                    Suc := Cartesian(List([1,2],i->PreImages(varpiPrimeLP,StateModKxK(q,i))));
                    if ForAll(Suc, r->ForAll([1,2],i->IsGoodPair(r[i],gp[i]))) then
                        return gp;
                    fi;
                fi;
            fi;
        od;
    
        return fail;
	fi;
    #Now the "regular" case. gamma has activity in some component.
    #
    F2 := FreeGroup(2); g1:=F2.1;g2:=F2.2; SetName(F2,"F2");
    F := FreeGroup(infinity,"xn",["x1","x2","x3","x4","x5","x6"]);SetName(F,"FX");
    EqG := EquationGroup(G,F);
    DEqG := DecompositionEquationGroup(EqG);
    FF := DEqG!.free;
    DEqQ := EquationGroup(Q,FF);
    DEqF2 := EquationGroup(F2,DEqG!.free);
    #Bridge: F₂⋆Fₓ⋆Fₓ → Q⋆Fₓ⋆Fₓ, g₁,g₂↦q1,q2 
    Bridge := FreeProductHomomorphism(DEqF2,DEqQ,[GroupHomomorphismByImages(F2,Q,[q1,q2]),IdentityMapping(FF)]);
    SetIsEquationHomomorphism(Bridge,true);
    
    Eq := Equation(EqG,[Product( List(List([1,3..n-1],i->Comm(F.(i),F.(i+1)))) )]);
    acts := GroupHomomorphismByImages(Group(EquationVariables(Eq)),SymmetricGroup(2),acts);
    DEq := DecompositionEquation(DEqG,Eq,acts);
    EqComp := List(EquationComponents(DEq),EquationLetterRep);
    I := Intersection(EquationVariables(EqComp[1]),EquationVariables(EqComp[2]));
	#I is nonempty as #act(γ) ≠ (1,1,1…1)
	normalforms := [];
	for x in I do
		#fail> n ∀n
		newEq := []; #v1*w2*g2*w1*v2*g1;
		indx := Minimum(Position(EqComp[1],x),Position(EqComp[1],x^-1));
		newEq[1] := EqComp[1]{[1..indx-1]};
		newEq[5] := EqComp[1]{[indx+1..Length(EqComp[1])]};
		indx := Minimum(Position(EqComp[2],x),Position(EqComp[2],x^-1));
		newEq[4] := EqComp[2]{[1..indx-1]};
		newEq[2] := EqComp[2]{[indx+1..Length(EqComp[1])]};

		Apply(newEq,eq->Equation(DEqF2,eq!.word));
		newEq[3] := g2; 
		newEq[6] := g1;
		newEq := Equation(Product(newEq));
		
		nf := EquationNormalForm(newEq);
		#Changed NormalForm algorithm, so make sure everything is still correct:
		Assert(0,nf.nf^nf.homInv=newEq);
		#normal form is [x₁₁,x₁₂]…[x₅₁,x₅₂] x₆₁⁻¹g₂g₁x₆₁ 
		Assert(0,nf.nf=Equation(DEqF2,[Product([1,3..2*n-3],i->Comm(FF.(i),FF.(i+1))),FF.(2*n-1)^-1,g2,FF.(2*n-1),g1]));
		#z is the preimage of x₆₁ or z=x₄₁ depending on |γ|=n
		z := Equation(FreeProductElm(DEqF2,[DEqG!.free.(2*n-1)]))^nf.homInv;
		#Assert(0,Size(z)=1); #not nec. anymore, but true?
		Add(normalforms,[z,nf,newEq]);
	od;

	for gp in Gamma1 do
		H := Bridge*EquationEvaluation(DEqQ,EquationVariables(DEq),gp);
		
		if IsOne(Equation(DEqF2,Concatenation(EqComp[1]!.word,[g1]))^H) and 
		   IsOne(Equation(DEqF2,Concatenation(EqComp[2]!.word,[g2]))^H) then
			for nf in normalforms do
				z := nf[1]^H;nf:=nf[2];
                if z in List(Q){[1,2,5,9,13,6,15,10]} then # = [1,a,b,c,d,ab,ad,ba]^π
    				#Compute the image of γ' under the normalization hommorphism and simplify it to the F₅ case
    				
    				gaP := [MakeImmutable( ReducedConstraint( List([1..2*n-2],i->ImageElm(nf.homInv*H,FF.(i))) ) ),z];
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


# The following function computes for each active good pair (q,γ) 
# the succesing (γ',x) as in Prop. 2.16
#
# The resulting list RealGoodPairs contains tuples (q,γ,[γ',x,[q₁,…,q₁₆]]) foreach
# q ∈ G'/K', γ∈Red such that γ has nontrivial activity and (q,γ) is a good pair.
# The element [γ',x,[q₁,…,q₁₆]] has the property that 
#   ∙(γ',qᵢ) are good pairs ∀i=1,…,16 and γ' has activity in some component
#   ∙if g ∈ τ⁻¹(q) then (g@2)^Rep(x) ⋅ (g@1) ∈ τ⁻¹(qᵢ) for some i ∈ {1,…,16}
#   ∙if (R₂ₙ-₁ (g@2)^Rep(x) ⋅ g@1 ,γ') is sattisfiable then so is (Rₙ g,γ)
ComputeAllSuccessors := function(Constraints)
    local size,count,RealGoodPairs,BadPairs,E,gamma,q,gammap;
    size := Sum(List(Constraints,C->Size(C.goodPairs)));
    count := 0;
    RealGoodPairs := [];
    BadPairs := [];
    for E in Constraints do
        gamma := E.constraint;
        for q in E.goodPairs do
            gammap := GetSuccessor(q,gamma);
            if not gammap = fail then
                Add(RealGoodPairs,[q,E,gammap]);
            else
                Add(BadPairs,[q,gamma]);
            fi;
            Info(InfoCW,1,Int(count*100/size),"% done. ",Size(RealGoodPairs)," good ones so far and ",Size(BadPairs)," bad ones.\r");
            count := count+1;
        od;
    od;
    return [RealGoodPairs,BadPairs];
end;
# The following takes about 30 min.
Info(InfoCW,1,"Compute the successor of each good pair with activity Constraint\nWill take about 2hours.\n");
T := ComputeAllSuccessors(ReducedConstraintsActive);;
RealGoodPairs := T[1];;
BadPairs := T[2];
Info(InfoCW,1,"Done. There should be no bad pairs. ",Size(BadPairs),"bad one found.\n");

#Save RealGoodPairs to a file
#Just store the index of the constraint and forget the successing qᵢs
RealGoodPairsFile := Filename(dir,"PCD/RealGoodPairs.go");
RGPstring := String(List(RealGoodPairs,L->[Position(List(GPmodKP),L[1]),L[2].index,[L[3][1].index,L[3][2]]]));
PrintTo(RealGoodPairsFile,Concatenation("return ",ReplacedString(RGPstring,"<identity> of ...","One(Q)"),";"));

#Read the file again:
RGP := List(ReadAsFunction(RealGoodPairsFile)(),
    L->[List(GPmodKP)[L[1]],ReducedConstraints[L[2]],[ReducedConstraints[L[3][1]],L[3][2]]]);;
#Check only the succesing qᵢs are forgotten.
Assert(0,ForAll([1..Size(RealGoodPairs)],
    i->(ForAll([1,2],k->RGP[i][k]=RealGoodPairs[i][k])
    and RGP[i][3][2] = RealGoodPairs[i][3][2]
    and RGP[i][3][1].constraint = RealGoodPairs[i][3][1].constraint)));
#Special Successor for (g,1) for g in K'
specSuc := GetSuccessor(One(GPmodKP),[One(Q),One(Q),One(Q),One(Q)]);
specSucFile := Filename(dir,"PCD/specSuc.go");
PrintTo(Concatenation("return ",ReplacedString(String(specSuc),"<identity> of ...","One(Q)"),";"));

Assert(0,specSuc=ReadAsFunction(specSucFile)());
