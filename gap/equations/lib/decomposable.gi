InstallMethod( DecompositionEquationGroup, "for an EquationGroup with fr const group",
	[IsEquationGroup],
	function(eqG)
		local DG,alph,DEqG;
		if not IsFRGroup(eqG!.const) then
			TryNextMethod();
		fi; 
		if not IsFinitelyGeneratedGroup(eqG!.const) then
			TryNextMethod();
		fi; 
		alph := AlphabetOfFRSemigroup(eqG!.const);
		if IsStateClosed(eqG!.const) then
			DG := eqG!.const;
		else
			DG := Group(List(alph,a->Concatenation(
					List(GeneratorsOfGroup(eqG!.const),gen->State(gen,a))) ));
		fi;
		DEqG := EquationGroup(DG,FreeProduct(ListWithIdenticalEntries(Size(alph),eqG!.free)));
		DEqG!.alph := alph;
		DEqG!.statefunc := State;
		DEqG!.activityfunc := Activity;
		SetIsDecompositionEquationGroup(DEqG,true);
		return DEqG;
	end);

InstallOtherMethod( DecompositionEquationGroup, "for an EquationGroup with free const group, size of alphabet and activities of generators",
	[IsEquationGroup,IsInt,IsList],
	function(eqG,alphsize,acts)
		local DG,DEqG;
		if not IsFreeGroup(eqG!.const) then
			TryNextMethod();
		fi; 
		if not IsFinitelyGeneratedGroup(eqG!.const) then
			TryNextMethod();
		fi; 
		if not ForAll(acts,s->s in SymmetricGroup(alphsize)) then
			Error("All activities have to be in S_",alphsize,"!");
		fi; 
		DG := FreeProduct(ListWithIdenticalEntries(alphsize,eqG!.const));
		DEqG := EquationGroup(DG,FreeProduct(ListWithIdenticalEntries(alphsize,eqG!.free)));
		DEqG!.alph := [1..alphsize];
		DEqG!.activityfunc := function(elm)
			if not elm in eqG!.const then
				Error("Not in correct group!");
			fi;
			return Product(LetterRepAssocWord(elm),i->acts[AbsInt(i)]^SignInt(i));
		end;
		DEqG!.statefunc := function(elm,state)
			local newelm,act,i;
			if not elm in eqG!.const then
				Error("Not in correct group!");
			fi;
			newelm := One(DG);
			act := ();
			for i in LetterRepAssocWord(elm) do
				if i<0 then
					newelm := newelm*AssocWordByLetterRep(FamilyObj(elm),[i])^FreeProductInfo(DG).embeddings[state^(acts[AbsInt(i)]^-1*act)];
				else 
					newelm := newelm*AssocWordByLetterRep(FamilyObj(elm),[i])^FreeProductInfo(DG).embeddings[state^act];
				fi;
				act := act*acts[AbsInt(i)]^SignInt(i);
			od;
			return newelm;
		end;

		SetIsDecompositionEquationGroup(DEqG,true);
		return DEqG;
	end);

InstallMethod( IsDecompositionEquationGroup, "for an EquationGroup",
	[IsEquationGroup],
	EqG->HasFreeProductInfo(EqG!.free));

#################################################################################
####                                                                         ####
####	                     DecomposedEquations                             #### 
####                                                                         ####
#################################################################################
InstallOtherMethod( Equation, "(Equation) for a list of lists, a DecompositionEquationGroup and a permutation",
	[IsEquationGroup,IsList,IsPerm],
	function(G,words,perm)
		local factors,red,Ob;
		if not IsDecompositionEquationGroup(G)then
			TryNextMethod();
		fi;
		factors := List(words,w->List(w,function(e) 
					if e in G!.free then return 2;fi;return 1;end));
		red := List([1..Length(words)],i->FREE_PRODUCTS_REDUCE_WORDS(words[i],factors[i]));
		Ob:= Objectify(
				NewType(ElementsFamily(FamilyObj(G)), IsFreeProductElm and IsDecomposedEquationRep),
				rec(words := List(red,r->r.word),
	    			factors := List(red,r->r.factors),
	       			group := G,
	       			const := G!.const,
	       			free := G!.free,
	       			activity := perm));
		SetIsEquation(Ob,true);
		return Ob;
	end);
InstallOtherMethod( DecompositionEquation, "for an Equation a list and an DecompositionEquationGroup",
		[IsEquationGroup,IsEquation,IsList],
		function(DEqG,eq,acts)
			return DecompositionEquation(DEqG,
										 eq,
										 GroupHomomorphismByImages(
										 	Group(EquationVariables(eq)),
										 	SymmetricGroup(DEqG!.alph),
										 	acts));
		end);
InstallMethod( DecompositionEquation, "for an Equation a group homomorphism and an DecompositionEquationGroup",
		[IsEquationGroup,IsEquation,IsGroupHomomorphism],
		function(DEqG,eq,acts)
			local alph,vars,DecompEq,lastperm,x,i;
			if not IsDecompositionEquationGroup(DEqG)then
				TryNextMethod();
			fi;
			alph := DEqG!.alph;
			if not ForAll([1..Size(alph)],i->Source(Embedding(DEqG!.free,i))=eq!.free) then
				Error("DecompositionEquationGroup doesn't correspond to EquationGroup.");
			fi;
			vars := EquationVariables(eq);
			if Length(vars)=0 then
				vars := One(eq!.free);
			fi;
			if not Group(vars)=Source(acts) then
				Error("acts needs to be defined on the variables.");
			fi;
			if not IsPermGroup(Range(acts)) then
				TryNextMethod();
			fi;
			eq := EquationLetterRep(eq);
			DecompEq := List(alph,a->[]);
			lastperm := ();
			for x in eq!.word do
				if x in eq!.const then
					for i in [1..Size(alph)] do
						Add(DecompEq[i^lastperm],DEqG!.statefunc(x,alph[i]));
					od;
					lastperm := lastperm*DEqG!.activityfunc(x);
				else
					if LetterRepAssocWord(x)[1]<0 then
						#eq is in LetterRep so this is the inverse of a gen.
						lastperm := lastperm*(x^acts)^-1;
					fi;
					for i in [1..Size(alph)] do
						Add(DecompEq[i^lastperm],x^Embedding(DEqG!.free,i));
					od;
					if not LetterRepAssocWord(x)[1]<0 then
						lastperm := lastperm*x^acts;
					fi;
				fi;
			od;
			DecompEq := Equation(DEqG,DecompEq,lastperm);
			#Quadratic equation is invariant under decomposition.
			if IsQuadraticEquation(eq) then
				SetIsQuadraticEquation(DecompEq,true);
			fi;
			return DecompEq;
		end);

InstallMethod( IsQuadraticEquation, "for an DecomposedEquation and Integer",
	[IsEquation and IsDecomposedEquationRep],
	function(eq)
		local Val,i;
		Val := rec();
		for i in Flat(Concatenation(List(eq!.words,word->
					List(Filtered(word,e->e in eq!.free),
						fw -> LetterRepAssocWord(fw) ) ) )) do
			i := AbsInt(i);
			if IsBound(Val.(i)) then
				if Val.(i) > 1 then
					return false;
				fi;
				Val.(i) := 2;	
			else
				Val.(i) := 1;
			fi;
		od;
		return true;
	end);

InstallMethod( EquationComponent, "for an DecomposedEquation and Integer",
	[IsEquation and IsDecomposedEquationRep, IsInt],
	function(eq,comp)
		if Length(eq!.words)<comp then
			Error("This component does not exist.");
		fi;
		return Equation(eq!.group,eq!.words[comp]);
	end);

InstallMethod( EquationComponents, "for an DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep ],
	eq->List([1..Length(eq!.words)],
			i->EquationComponent(eq,i) ));

InstallMethod( EquationVariables, "for an DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep],
	function(x)
		return Set(Concatenation(List(EquationComponents(x),EquationVariables)));
	end);

InstallMethod( ViewObj,   "for DecomposedEquations)",
   [ IsEquation and IsDecomposedEquationRep ],
    function( x )
		local s;
		Print("DecomposedEquation in ",EquationVariables(x));
	   end);

InstallMethod( PrintObj,   "for DecomposedEquations)",
   [ IsEquation and IsDecomposedEquationRep ],
    function( x )
		local s;
		Print("Equation(",EquationComponents(x),")");
	   end);

InstallMethod( \=,  "for two DecomposedEquations",
		IsIdenticalObj,
    [ IsEquation and IsDecomposedEquationRep,
      IsEquation and IsDecomposedEquationRep ],
    function( x, y )
			return Size(x!.words) = Size(y!.words) and
					ForAll([1..Size(x!.words)],
						i->EquationComponent(x,i)=EquationComponent(y,i)) and
					x!.activity = y!.activity;
		end);

InstallMethod( OneOp, "for an DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep],
		x->	Equation(x!.group,List(x!.group!.alph,a->[]))
	);

InstallMethod( \*,   "for two DecomposedEquations",
	IsIdenticalObj,
    [ IsEquation and IsDecomposedEquationRep, IsEquation and IsDecomposedEquationRep ],0,
    function( x, y )
    	return Equation(x!.group,
    			List([1..Length(x!.words)],
    				i->Concatenation(x!.words[i],y!.words[i^x!.activity])),
    			x!.activity*y!.activity);
    end);

InstallMethod( InverseOp, "for a DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep],
	function(x)
		return Equation(x!.group,
				Permuted(List(x!.words,w->Reversed(List(w,Inverse))),x!.activity^-1),
    			x!.activity^-1);
	end);
#################################################################################
####                                                                         ####
####	          Normalization for Decomposed Equations                     ####
####                                                                         ####
#################################################################################
InstallMethod(DecomposedEquationDisjointForm," for a decomposed Equation",
		[IsEquation and IsDecomposedEquationRep],
		function(x)
		local Comp,Vars,EqG,change,Hom,Homs,L,i,CommonVars,I,j,v1,v2,pos,sign;
		if not IsQuadraticEquation(x) then
			TryNextMethod();
		fi;
		#Step 1 find common variables.
		Comp := List(EquationComponents(x),EquationLetterRep);
		EqG := x!.group;
		change := true;
		Hom := EquationHomomorphism(EqG,[],[]);

		while change do		
			change := false;
			Vars := List(Comp,eq->EquationVariables(eq));
			for i in [1..Length(Comp)] do
				CommonVars := [];
				for j in [i+1..Length(Comp)] do
					I := Intersection(Vars[i],Vars[j]);
					if Length(I)>0 then
						Add(CommonVars,[j,I[1]]);
					fi;
				od;
				if Length(CommonVars)>0 then
					break;
				fi;
			od;
			# The components i and CommonVars[k][1] have the variable CommonVars[k][2]
			# in common for all k.
			Homs := rec(gens:=[],imgs:=[]);
			for L in CommonVars do
				pos := Position(Comp[L[1]],L[2]);
				sign := 1;
				if pos = fail then
					pos := Position(Comp[L[1]],L[2]^-1);
					sign := -1;
				fi;
				v1 := Comp[L[1]]{[1..pos-1]};
				v2 := Comp[L[1]]{[pos+1..Length(Comp[L[1]])]};
				Add(Homs.gens,L[2]);
				Add(Homs.imgs,(v2*v1)^(-sign));
				change := true;
			od;
			#The mappings don't interfere because the equation is quadratic
			# and hence each variable can occure in at most two components.
			Homs := EquationHomomorphism(EqG,Homs.gens,Homs.imgs);
			Comp := List(Comp,eq->Equation(eq^Homs));
			Hom := Hom*Homs;
		od;
		# Now each component is again a quadratic equation, and the 
		# variables of all components are pairwise disjoint.
		return rec(eq:=Equation(EqG,List(Comp,eq->eq!.word),x!.activity),hom:=Hom);
	end);


InstallMethod(LiftSolution, "For a Decomposed Equation, an Equation, a group hom, and a solution for Deq",
	[IsEquation and IsDecomposedEquationRep, IsEquation, IsGroupHomomorphism, IsGroupHomomorphism],
	function(Deq,eq,acts,sol)
		local Comp,NFs,imgs;
		if not DecompositionEquation(Deq!.group,eq,acts)=Deq then
			Error("The first argument must be the decomposition of the second argumen.");
		fi;
		Comp := EquationComponents(DecomposedEquationDisjointForm(Deq).eq);
		if not IsEvaluation(sol) then
			Error("The 4-th argument need to be an evaluation.");
		fi;
		if not ForAll(Comp,E-> IsSolution(sol,E)) then
			Error("The last argument must be a solution for the first argument.");
		fi;
		imgs := List(EquationVariables(eq),
			x-> UnderlyingMealyElement(FRElement(
				 [List(FreeProductInfo(Deq!.group!.free).embeddings,
				 	e->[Equation(Deq!.group,[x^e])^sol])],
				 [x^acts],
				 [1] )) );
		return EquationEvaluation(eq,EquationVariables(eq),imgs);
	end);
#
# Let sol be a list of solutions [s₁,…,sₙ] such that 
# sᵢ is a solution for the NormalForm of th iᵗʰ component
# of a DecomposedEquationDisjoint Form
# of the DecomposedEquation `Deq` wich is the decomposition of an equation `eq`
# with activities `acts`.
# 
# Then the following method computes a solution for `eq`
InstallOtherMethod(LiftSolution, "For a Decomposed Equation, an Eqation, a group hom, and a list of solutions",
	[IsEquation and IsDecomposedEquationRep, IsEquation, IsGroupHomomorphism, IsList],
	function(Deq,eq,acts,sol)
		local Comp,NFs,imgs;
		if not DecompositionEquation(Deq!.group,eq,acts)=Deq then
			Error("The first argument must be the decomposition of the second argumen.");
		fi;
		Comp := EquationComponents(DecomposedEquationDisjointForm(Deq).eq);
		NFs := List(Comp,EquationNormalForm);

		if not ForAll(ListN(sol,Comp,function(ev,eq) return IsSolution(ev,eq);end)) then
			Error("The i-th entry of the last argument must be a solution for the i-th comp.");
		fi;

		sol := Product([1..Size(Comp)],i->NFs[i]*sol[i]);
		imgs := List(EquationVariables(eq),
			x-> UnderlyingMealyElement(FRElement(
				 [List(FreeProductInfo(Deq!.group!.free).embeddings,e->[(x^e)^sol])],
				 [x^acts],
				 [1] )) );
		return EquationEvaluation(eq,EquationVariables(eq),imgs);
	end);

