#Read the definition of GetCommutators
if not IsExistingFile("./examples/init.g") then
    Error("Please start this script in the main directory.");
fi;

dir := Directory("examples");
Read(Filename(dir,"init.g"));
Read(Filename(dir,"Ore.g"));

#Definition of the Neumann Segal group with its generators. 
api := function(pi,n)
	return MealyElement([List([1..n],i->2),List([1..n],i->2)],[pi,()],1);
end;

alphapi := function(pi,n)
	return MealyElement([List([1..n],i->2),List([1..n],i->2),Concatenation([1,3],ListWithIdenticalEntries(n-2,2))],[pi,(),()],3);
end;

NeumannSegalGroup := function(n)
	return Group(Concatenation(List(GeneratorsOfGroup(AlternatingGroup(n)),pi->[api(pi,n),alphapi(pi,n)])));
end;

#######
#
# Solve the equations [X,Y]g in the Neumann Segal group. 
# Input: g ∈ NeumannSegalGroup
# 		 Opitional: The sets N,M
# Output: h,f ∈ NeumanSegalGroup such that [h,f]g is the identity.
#
#######
Solver := function(g,arg...)
	local n,Nn,G,F,EqG,EqGN,DEqGN,DEqG,eq,Solverinner,N,M;
	n := Size(AlphabetOfFRObject(g));
	Nn := NeumannSegalGroup(n);
	#If more tests for the same n are done, then define N and M outside of 
	# this function!
	if Length(arg) = 0 then
		N := List(AlternatingGroup(n),s->api(s,n));;
		M := List(AlternatingGroup(n),s->alphapi(s,n));;
	else
		if not Length(arg)=2 then
			Error("Solver needs either one or three arguments.");
		fi;
		if not api((1,2,3),n) in arg[1] or not alphapi((1,2,3),n) in arg[2] then
			Error("Solver second and third argument needs to be \"N\" and \"M\".");
		fi;
		N := arg[1];
		M := arg[2];
	fi;
	G := FreeGroup("g"); F := FreeGroup(2,"Z");
	EqG := EquationGroup(G,F);
	EqGN := EquationGroup(Nn,F);
	DEqGN := DecompositionEquationGroup(EqGN);
	eq := Equation(EqG,[Comm(F.1,F.2),G.1]);

	DEqG := DecompositionEquationGroup(EqG,n,[()]);

	Solverinner := function(g)
		local gamma,deq,neq,L,l,Res,i,m,sol,eqN,deqN,deqN1,neqN,neqk,imgs,x,sols,lvars,vars,k;
		gamma := GetCommutators(Activity(g)^-1);
		if g in N then
			imgs := [api(gamma[1],n),api(gamma[2],n)];
			Assert(2,IsOne(Comm(imgs)*g));
			return imgs;
		fi;
		if g in M then
			gamma := GetCommutators(Activity(State(g,1)^-1));
			imgs := [alphapi(gamma[1],n),alphapi(gamma[2],n)];
			Assert(2,IsOne(Comm(imgs)*g));
			return imgs;
		fi;
		if Activity(g) = () then
			Res := List([1..n],i->Solverinner(State(g,i)));
			imgs:= List([1,2],i->ComposeElement(List(Res,r->r[i]),()));
			Assert(2,IsOne(Comm(imgs)*g));
			return imgs;
		fi;
		
		#Version in free group
		deq := DecomposedEquationDisjointForm(DecompositionEquation(DEqG,eq,gamma));
		neq := EquationComponents(deq.eq);
		eqN := Equation(EqGN,[Comm(F.1,F.2),g]);
		#Version in neumann group
		deqN1 := DecompositionEquation(DEqGN,eqN,gamma);
		deqN := DecomposedEquationDisjointForm(deqN1);
		
		imgs := [];
		vars := [];
		for k in Filtered([1..n],i-> not IsOne(neq[i])) do
			neqk := EquationNormalForm(neq[k]);
			neqN := EquationNormalForm(EquationComponent(deqN.eq,k));
			# neq.nf = ∏[X₂ᵢ₋₁,X₂ᵢ] ∏g@τ(i)^Xᵢ then L= [τ(1),τ(2),… ]
			L := LetterRepAssocWord(ImageElm( FreeProductHomomorphism(DEqG,DEqG,[
				   IdentityMapping(DEqG!.const),
					GroupHomomorphismByImages(DEqG!.free,
					DEqG!.free,
					List(GeneratorsOfGroup(DEqG!.free),g->One(DEqG!.free)))]),
				 neqk.nf)!.word[1]);
		
			l := Int(Ceil(Float(n/Genus(neqk.nf))));
			Res := [];
			i := 0;
			#Try to decompose the set L in somehow pieces of similar size but 
			# so that no piece represents the identity of the element g
			while i< Length(L) do
				m := Minimum(i+l,Length(L));
				x := Product(L{[i+1..m]},k->State(g,k));
				if IsOne(x) then
					i := m;
					continue;
				fi;
				while x=g do
					m := m-1;
					x := Product(L{[i+1..m]},k->State(g,k));
				od;
				Append(Res,Reversed(Solverinner(x)));
				i := m;
			od;
			
			sol := EquationEvaluationNC(
					DEqGN,
					GeneratorsOfGroup(DEqGN!.free),
					Concatenation(Reversed(Res),List([1..2*n-Length(Res)],i->One(Nn))) );
			Assert(2,IsSolution(sol,neqN.nf));
			Assert(2,IsSolution(neqN.hom*sol,EquationComponent(deqN.eq,k)));
			lvars := EquationVariables(EquationComponent(deqN.eq,k));
			Append(vars,lvars );
			Append(imgs,List(lvars,x->ImageElm(deqN.hom*neqN.hom*sol,x)));
		od;
		#Combine the solution for the different states
		sol:=EquationEvaluationNC(DEqGN,vars,imgs);
		imgs := List(GeneratorsOfGroup(DEqGN!.free),x->ImageElm(deqN.hom*sol,x));

		imgs := [ComposeElement(imgs{[1..n]},gamma[1]),
				 ComposeElement(imgs{[n+1..2*n]},gamma[2])];		
		Assert(2,IsOne(Comm(imgs)*g));
		return imgs;
	end;
	return Solverinner(g);
end;

#####  Example
# g := api((1,2,3,4,5),6)*alphapi((1,2,3)(4,5,6),6);
# s := Solver(g);
# IsOne(Comm(s)*g);

#####
# Test 'num' random elements from the NeumannSegalGroup of degree 'deg' 
# that are of length 'len' corresponding to the generators of the group.
#
NeumannSegalRandomTest := function(deg,len,num)
	local Nn,RandomNn,N,M,i,g;
	Nn := NeumannSegalGroup(deg);
	RandomNn := m ->Product([1..m],i->Random(GeneratorsOfGroup(Nn)));
	N := List(AlternatingGroup(deg),s->api(s,deg));;
	M := List(AlternatingGroup(deg),s->alphapi(s,deg));;
	Info(InfoExamples,2,"Nucleus computed\n");
	for i in [1..num] do
		g := RandomNn(Random([1..len]));
		if not IsOne(Comm(Solver(g,N,M))*g) then
			Error("There is a problem with g",g);
		fi;
		Info(InfoExamples,1,Int(i*100/num),"% done.\r");
	od;
	Info(InfoExamples,1,"100% done. Everythings great\n");
end;


####################################################################
####################################################################
#		All equations in the Neumann-Segal Group
####################################################################
####################################################################
#
#
#Proof of Claim 1 in the n=5 case:
# For every two element σ,τ∈A₅, σ≠1 there are x,y,z∈A₅ such that σˣσʸσᶻ=τ
CheckClaim1 := function()
	local A5,sig,L,x,y,z;
	A5 := AlternatingGroup(5);
	for sig in ConjugacyClasses(A5) do
		sig := Representative(sig);
		L:=[];
		if IsOne(sig) then
			continue;
		fi;
		for x in A5 do
			for y in A5 do 
				for z in A5 do 
					AddSet(L,sig^x*sig^y*sig^z);
					if Size(L)=60 then
						return true;
					fi;
				od;
			od;
		od;
		return false;
	od;	
end;
#CheckClaim1();


#Proof of Claim 2 in the n=5 case:
# ∀σ∈A₅, σ≠1 and ∀g∈Neumann₅ there is a constraint γ:⟨X,Y,Z⟩→A₅ such that 
# Φ_γ(σ^Xσ^Yσ^Zg) consist of exactly one nontrivial equaiton and that is 
# of positive genus
CheckClaim2 := function()
	local FG,F,A5,EqG,eq,sig,DEqG,good,gamma,gam1,gam2,gam3,deq,parEv,imgs,i,n;
	FG := FreeGroup(4,"g"); SetName(FG,"N");
	F := FreeGroup(3,"Z"); SetName(F,"F");
	A5 := AlternatingGroup(5);
	EqG := EquationGroup(FG,F);
	#The equation g₁^X g₂^Y g₃^Z g₄
	eq := Equation(EqG,[F.1^-1,FG.1,F.1*F.2^-1,FG.2,F.2*F.3^-1,FG.3,F.3,FG.4]);
	for sig in ConjugacyClasses(A5) do
		sig := Representative(sig);
		if IsOne(sig) then continue; fi;

		# The activity of g is of no interest
		DEqG := DecompositionEquationGroup(EqG,5,[sig,sig,sig,()]); 
		#The states of the first 3 group elements are trivial
		imgs := ListWithIdenticalEntries(5*3,One(DEqG!.const));
		Append(imgs,List([3*5+1..4*5],i->DEqG!.const.(i) ) );
		parEv := FreeProductHomomorphism(DEqG,DEqG,[
				GroupHomomorphismByImages(DEqG!.const,DEqG!.const,imgs),
				IdentityMapping(DEqG!.free) ]);
		good := false;
		for gam1 in A5 do
			for gam2 in A5 do 
				for gam3 in A5 do
					gamma := [gam1,gam2,gam3];
					deq := DecomposedEquationDisjointForm(DecompositionEquation(DEqG,eq,gamma)).eq;
					if ForAll(EquationComponents(deq),E->IsOne(E^parEv) or Genus(Equation(E^parEv))>0) then
						good := true;
						break;
					fi;
				od;
				if good then break; fi;
			od;
			if good then break; fi;
		od;
		if not good then
			return false;
		fi;
	od;
	return true;
end;
#CheckClaim2();


#######
# 
# The equations of the type σ^X₁ σ^X₂ σ^X₃ g for
# σ=(1,2,3.…,n), σ=(1,2,3.…,n-2,n,n-1) and σ=(1,2,3.…,n-2,n)
# result in descendents with nontrivial Genus. Compute this geni for 
# small values of n
#
ComputeGeni := function()
	local F, FG,X1,X2,X3,g1,g2,g3,EqG,eq,n,sig,DEqG,deq,imgs,parEv;
	F := FreeGroup("X1","X2","X3");
	FG := FreeGroup("g1","g2");
	X1 := F.1;X2:=F.2;X3:=F.3;g1:=FG.1;g2:=FG.2;
	EqG := EquationGroup(FG,F);
	eq := Equation(EqG,[X1^-1,g1,X1*X2^-1,g1,X2*X3^-1,g1,X3,g2]);
	Info(InfoExamples,2,"σ₁=(1,2,3,…,n):\n");
	for n in [5..20] do
		sig := PermList(Concatenation([2..n],[1]));#(1,2,3.…,n)
		DEqG := DecompositionEquationGroup(EqG,n,[sig,()]); 
		deq := DecompositionEquation(DEqG,eq,[(),(),()]);
		imgs := Concatenation(List([1..n],i->One(DEqG!.const)),List([n+1..2*n],i->DEqG!.const.(i)));
		parEv := FreeProductHomomorphism(DEqG,DEqG,[
						GroupHomomorphismByImages(DEqG!.const,DEqG!.const,imgs),
						IdentityMapping(DEqG!.free) ]);
		#Print(List(EquationComponents(deq),E->Equation(E^parEv)));
		Info(InfoExamples,1,"n=",n,": ",Genus(EquationComponent(DecomposedEquationDisjointForm(deq).eq,1)),"\n");
	od;
	# σ=(1,2,3.…,n-2,n,n-1)
	Info(InfoExamples,2,"σ₂=(1,2,3,…,n-2,n,n-1):\n");
	for n in [5..20] do
		sig := PermList(Concatenation([2..n-2],[n,1,n-1]));# (1,2,3.…,n-2,n,n-1)
		DEqG := DecompositionEquationGroup(EqG,n,[sig,()]); 
		deq := DecompositionEquation(DEqG,eq,[(),(),()]);
		imgs := Concatenation(List([1..n],i->One(DEqG!.const)),List([n+1..2*n],i->DEqG!.const.(i)));
		parEv := FreeProductHomomorphism(DEqG,DEqG,[
					GroupHomomorphismByImages(DEqG!.const,DEqG!.const,imgs),
					IdentityMapping(DEqG!.free) ]);
		#Print(List(EquationComponents(deq),E->Equation(E^parEv)));
		Info(InfoExamples,1,"n=",n,": ",Genus(EquationComponent(DecomposedEquationDisjointForm(deq).eq,1)),"\n");
	od;
	# σ=(1,2,3.…,n-2,n)
	Print("σ₃=(1,2,3,…,n-2,n):\n");
	for n in [5..20] do
		sig := PermList(Concatenation([2..n-2],[n,n-1,1]));#(1,2,3.…,n-2,n)
		DEqG := DecompositionEquationGroup(EqG,n,[sig,()]); 
		deq := DecompositionEquation(DEqG,eq,[(),(),()]);
		imgs := Concatenation(List([1..n],i->One(DEqG!.const)),List([n+1..2*n],i->DEqG!.const.(i)));
		parEv := FreeProductHomomorphism(DEqG,DEqG,[
					GroupHomomorphismByImages(DEqG!.const,DEqG!.const,imgs),
					IdentityMapping(DEqG!.free) ]);
		#Print(List(EquationComponents(deq),E->Equation(E^parEv)));
		Info(InfoExamples,1,"n=",n,": ",Genus(EquationComponent(DecomposedEquationDisjointForm(deq).eq,1)),"\n");
	od;
end;
#ComputeGeni();


######################
#
# Proof of Claim 2 in the n=5…10 case:
# ∀σ∈A₅, σ≠1 and ∀g∈Neumann₅ there is a constraint γ:⟨Z₁,…,Z₆⟩→A₅ such that 
# Φ_γ(σ^Z₁σ^Z₂σ^Z₃σ^Z₄σ^Z₅σ^Z₆g) consist of exactly one nontrivial equaiton 
# and that is of positive genus
CheckClaim2n := function(n)
	local FG,F,An,A5,EqG,eq,sig,DEqG,good,gamma,gam1,gam2,gam3,deq,parEv,
		imgs,i,Seq,eqL,r,actG,Choices,L,tau,taus;
	r := 6;
	FG := FreeGroup(r+1,"g"); SetName(FG,"N");
	F := FreeGroup(r,"Z"); SetName(F,"F");
	An := AlternatingGroup(n);
	A5 := AlternatingGroup(5);
	EqG := EquationGroup(FG,F);
	
	#The equation g₁^X g₂^Y g₃^Z g₄
	eq := Equation(EqG,[F.1^-1,FG.1,F.1*F.2^-1,FG.2,F.2*F.3^-1,FG.3,F.3,FG.(r+1)]);
	Choices := [];
	Info(InfoExamples,2,"n=",n,"\n");
	for sig in ConjugacyClasses(A5) do
		sig := Representative(sig);
		if IsOne(sig) then continue; fi;

		# The activity of g is of no interest
		actG := ListWithIdenticalEntries(r,sig);
		Add(actG,());
		DEqG := DecompositionEquationGroup(EqG,n,actG); 
		#The states of the first 3 group elements are trivial
		imgs := ListWithIdenticalEntries(n*r,One(DEqG!.const));
		Append(imgs,List([r*n+1..(r+1)*n],i->DEqG!.const.(i) ) );
		parEv := FreeProductHomomorphism(DEqG,DEqG,[
				GroupHomomorphismByImages(DEqG!.const,DEqG!.const,imgs),
				IdentityMapping(DEqG!.free) ]);
		good := false;
		for gam1 in A5 do
			for gam2 in A5 do 
				for gam3 in A5 do
					gamma := [gam1,gam2,gam3];
					deq := DecomposedEquationDisjointForm(DecompositionEquation(DEqG,eq,gamma)).eq;
					if ForAll(EquationComponents(deq){[1..5]},e->IsOne(e^parEv) or Genus(Equation(e^parEv))>0) then
						good := true;
						#Print(sig,": ",gamma,"\n");
						Add(Choices,[sig,gamma]);
						break;
					fi;

				od;
				if good then break; fi;
			od;
			if good then break; fi;
		od;
		if not good then
			return false;
		fi;
	od;
	taus := [(),(),(),(),(),(1,6)(2,5),(1,7)(2,6),(1,8)(2,7)(3,6)(4,5),(1,9)(2,8)(3,7)(4,6),(1,10)(2,9)(3,8)(4,7)(5,6)*(7,8)];
	eqL := [];
	for i in [1..r] do
		Append(eqL,[F.(i)^-1,FG.(i),F.(i)]);
	od;
	Add(eqL,FG.(r+1));
	Seq := Equation(EqG,eqL);
	for sig in ConjugacyClasses(An) do
		sig := Representative(sig);
		if IsOne(sig) then continue; fi;
		if not sig in A5 then continue; fi;

		actG := ListWithIdenticalEntries(r,sig);
		Add(actG,());
		DEqG := DecompositionEquationGroup(EqG,n,actG); 

		imgs := ListWithIdenticalEntries(n*r,One(DEqG!.const));
		Append(imgs,List([r*n+1..(r+1)*n],i->DEqG!.const.(i) ) );
		parEv := FreeProductHomomorphism(DEqG,DEqG,[
				GroupHomomorphismByImages(DEqG!.const,DEqG!.const,imgs),
				IdentityMapping(DEqG!.free) ]);
		
		gamma := First(Choices,L->L[1]=sig)[2];
		tau := taus[n];

		gamma := Concatenation(List(gamma,p->p*tau),gamma);
		deq := DecomposedEquationDisjointForm(DecompositionEquation(DEqG,Seq,gamma)).eq;
		if not ForAll(EquationComponents(deq),E->IsOne(E^parEv) or Genus(Equation(E^parEv))>0) then
			return false;
		fi;
		Info(InfoExamples,2,sig,": ",gamma,"\n");
	od;

	return true;
end;
#ForAll([5..10],i->CheckClaim2n(i));
