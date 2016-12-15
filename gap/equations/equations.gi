#################################################################################
####                                                                         ####
####	                          EquationGroup                              ####
####                                                                         ####
#################################################################################
InstallMethod( IsEquationGroup,   "for a FreeProduct)",
   [ IsGeneralFreeProduct],
    G->Length(G!.groups)=2 and IsFreeGroup(G!.groups[2])
	);

InstallMethod( EquationGroup, "for two groups",
	[IsGroup,IsFreeGroup],
	function(G,Free)
		local Ob;
		Ob := FreeProduct(G,Free);
		Ob!.free :=Free;
		Ob!.const :=G;
		SetIsEquationGroup(Ob,true);
		return Ob;
	end);


InstallMethod( DecompositionEquationGroup, "for an EquationGroup",
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
		SetIsDecompositionEquationGroup(DEqG,true);
		return DEqG;
	end);

InstallMethod( IsDecompositionEquationGroup, "for an EquationGroup",
	[IsEquationGroup],
	EqG->HasFreeProductInfo(EqG!.free));


#################################################################################
####                                                                         ####
####	                          Equations                                  ####
####                                                                         ####
#################################################################################
InstallMethod( Equation, "(Equation) for a list of group elements and unknowns and boolean",
	[IsEquationGroup,IsList],
	function(eqG,elms)
		local eq;
		#always reduce equation cyclicaly 
		if Length(elms)>= 1 and elms[1] in eqG!.const then
			elms := Concatenation(elms{[2..Size(elms)]},[elms[1]]);
		fi;
		eq := FreeProductElm(eqG,elms,List(elms,function(e)
													if e in eqG!.const then
														return 1; 
													fi; return 2;
												 end) );
		eq!.const := eqG!.const;
		eq!.free := eqG!.free;
		SetIsEquation(eq,true);
		return eq;
	end);

InstallOtherMethod( Equation, "For a FreeProductElm",
	[IsFreeProductElm],
	function(elm)
		if not IsEquationGroup(elm!.group) then
			TryNextMethod();
		fi;
		elm!.const := elm!.group!.const;
		elm!.free := elm!.group!.free;
		SetIsEquation(elm,true);
		return elm;
	end);

InstallMethod( IsEquation, "For a FreeProductElm",
	[IsFreeProductElm],
	function(elm)
		return IsEquationGroup(elm!.group) and IsBound(elm!.const) and IsBound(elm!.free);
	end);

InstallMethod(EquationLetterRep, "for an Equation",
	[IsEquation and IsFreeProductElmRep],
	function(eq)
		local nw,elm,i,Eq;
		nw := [];
		for elm in eq!.word do
			if elm in eq!.const then
				Add(nw,elm); 
			else
				for i in LetterRepAssocWord(elm) do
					Add(nw,AssocWordByLetterRep(FamilyObj(elm),[i]));
				od;
			fi;
		od;
		Eq:= FreeProductElmLetterRep(eq!.group,nw,List(nw,function(e)
													if e in eq!.const then
														return 1;
													fi; return 2;
												 end) );
		return Equation(Eq);
	end);

InstallMethod( EquationVariables, "for a Equation",
	[IsEquation and IsFreeProductElmRep],
	function(x)
		return List(Set(List(Concatenation(
			List(Filtered(x!.word,e->e in x!.free),	fw -> LetterRepAssocWord(fw))
			),i->AbsInt(i))),
			v->AssocWordByLetterRep(FamilyObj(One(x!.free)),[v]));
	end);

InstallMethod( ViewObj,   "for Equations)",
   [ IsEquation and IsFreeProductElmRep ],
    function( x )
		local s;
		Print("Equation in ",EquationVariables(x));
	end);

InstallMethod( OneOp, "for an Equation",
	[IsEquation and IsFreeProductElmRep],
	x -> Equation(x!.group,[]) 
	);

InstallOtherMethod( One,"for an EquationGroup",
    [ IsEquationGroup ],
    eqG -> Equation(eqG,[]) 
	);



InstallMethod(IsQuadraticEquation, "for a Equation",
		[IsEquation and IsFreeProductElmRep],
		function(x)
			local i,Val;
			Val := rec();
			for i in Concatenation(List(
					Filtered(x!.word,e->e in x!.free),
					fw -> LetterRepAssocWord(fw)
					)) do
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
		end
);

InstallMethod(IsOrientedEquation, "for a square Equation",
		[IsQuadraticEquation],
		function(x)
			local LetterRep;
			LetterRep := Concatenation(List(
						Filtered(x!.word,e->e in x!.free),
						fw -> LetterRepAssocWord(fw)
						));
			return ForAll(LetterRep,i->-i in LetterRep);
		end
);

#################################################################################
####                                                                         ####
####	                     DecomposedEquations                             #### 
####                                                                         ####
#################################################################################
InstallOtherMethod(Equation, "(Equation) for a list of lists, a DecompositionEquationGroup and a permutation",
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

InstallMethod(DecompositionEquation, "for an Equation a group homomorphism and an DecompositionEquationGroup",
		[IsEquationGroup,IsEquation,IsGroupHomomorphism],
		function(DEqG,eq,acts)
			local alph,vars,DecompEq,lastperm,x,i;
			if not IsDecompositionEquationGroup(DEqG)then
				TryNextMethod();
			fi;
			if not IsFRGroup(eq!.const) then
				TryNextMethod();
			fi;
			alph := AlphabetOfFRSemigroup(eq!.const);
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
						Add(DecompEq[i^lastperm],State(x,alph[i]));
					od;
					lastperm := lastperm*Activity(x);
				else
					if LetterRepAssocWord(x)[1]<0 then
						#eq is in LetterRep so this is the inverse of a gen.
						lastperm := lastperm*x^acts;
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


InstallMethod(EquationComponent, "for an DecomposedEquation and Integer",
	[IsEquation and IsDecomposedEquationRep, IsInt],
	function(eq,comp)
		if Length(eq!.words)<comp then
			Error("This component does not exist.");
		fi;
		return Equation(eq!.group,eq!.words[comp]);
	end);

InstallMethod(EquationComponents, "for an DecomposedEquation",
	[IsEquation and IsDecomposedEquationRep ],
	eq->List([1..Length(eq!.words)],
			i->EquationComponent(eq,i) ));

InstallMethod(EquationVariables, "for an DecomposedEquation",
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
####	                     EquationsHomomorphism                           ####
####                                                                         ####
#################################################################################

InstallMethod( EquationHomomorphism, "For an EquationGroup, a list of variables, and a list of images",
	[IsEquationGroup,IsList,IsList],
	function(eqG,gens,imgs)
		local ngens,nimgs,hom,fac;
		if not Length(gens) = Length(imgs) then
			Error("There must be as many images as generators");
		fi;
		if Length(gens) = 0 then
			hom := IdentityMapping(eqG);
		    SetName(hom,"<Identity EqHom>");
		    SetIsEquationHomomorphism(hom,true);
			return hom;
		fi;
		if not ForAll(gens,g->g in GeneratorsOfGroup(eqG!.free)) then
			TryNextMethod();
		fi;
		fac := (w->List(w,function(e)
								if e in eqG!.const then
									return 1; 
								fi; return 2;
								end));

		ngens := List(gens,gen->LetterRepAssocWord(gen)[1]);
		
		nimgs := List(imgs,function(x)
				if IsList(x) then
					return FreeProductElm(eqG,x,fac(x));
				elif x in eqG then
					return x;
				elif x in eqG!.const then
					return FreeProductElm(eqG,[x],[1]);
				elif x in eqG!.free then
					return FreeProductElm(eqG,[x],[2]);
				else
					Error("Wrong Input!");
				fi; end);
		hom := GroupHomomorphismByFunction(eqG,eqG,function(eq)
			local newword;
			newword := Flat(List(eq!.word,function(x)
					if x in eq!.group!.const then
						return x;
					fi;
					return List(LetterRepAssocWord(x),function(l)
						local pos,q;
							pos := Position(ngens,AbsInt(l));
							if pos = fail then
								return AssocWordByLetterRep(FamilyObj(x),[l]);
							else
								q := nimgs[pos]^SignInt(l);
								return q!.word;
							fi;	
						end);
					end));
				return FreeProductElm(eqG,newword,fac(newword));
			end);

		SetEquationHomomorphismImageData(hom,rec(imgs:=imgs,gens:=gens));
		SetIsEquationHomomorphism(hom,true);
		return hom;
	end);

InstallMethod( ViewObj, "For an EquationHomomorphism",
	[IsEquationHomomorphism],
	function(hom)
		local imDa;
		if HasEquationHomomorphismImageData(hom) then
			imDa := EquationHomomorphismImageData(hom);
			View(imDa.gens,"->",imDa.imgs);
		else
			TryNextMethod();
		fi;
	end);

InstallMethod( CompositionMapping2, "For two EquationHomomorphisms",
	FamSource1EqFamRange2,
	[ IsEquationHomomorphism, IsEquationHomomorphism ], 0,
	function(hom1,hom2)
		local mapi,reshom;
  		reshom:= CompositionMapping2General(hom1,hom2);
  		SetIsEquationHomomorphism(reshom,true);
  		return reshom;
	end);

InstallMethod( EquationEvaluation, "For an Equation, the list of variables and a list of images",
	[IsEquation, IsList, IsList],
	function(eq,gens,imgs)
		local var,hom,hom2;
		if not ForAll(imgs,elm->elm in eq!.const) then
			Error("All images need to be in the group of constants.");
		fi;
		var := EquationVariables(eq);
		if not Length(var)=Length(gens) then
			Error("There must be as many images as variables.");
		fi;
		if not Length(imgs)=Length(gens) then
			Error("There must be as many images as generators.");
		fi;
		if not ForAll(var,v->v in gens) then
			Error("All free variables must have an image.");
		fi;
		hom := EquationHomomorphism(eq!.group,gens,imgs);
		hom2 := GroupHomomorphismByFunction(eq!.group,eq!.const,q->Product(Image(hom,q)!.word));
		SetIsEquationHomomorphism(hom2);
		SetIsEvaluation(hom2,true);
		return hom2;
	end);

InstallOtherMethod( EquationEvaluation, "For an Equation, the list of variables and a list of images",
	[IsEquationGroup, IsList, IsList],
	function(eqG,gens,imgs)
		local var,hom,hom2;
		if not ForAll(imgs,elm->elm in eqG!.const) then
			Error("All images need to be in the group of constants.");
		fi;
		if not Length(imgs)=Length(gens) then
			Error("There must be as many images as generators.");
		fi;
		hom := EquationHomomorphism(eqG,gens,imgs);
		hom2 := GroupHomomorphismByFunction(eqG,eqG!.const,q->Product(Image(hom,q)!.word));
		SetIsEvaluation(hom2,true);
		return hom2;
	end);

InstallMethod( IsEvaluation, "For a group homomorphism",
	[IsGroupHomomorphism],
	h->IsEquationGroup(Source(h)) and Range(h)=Source(h)!.const);
	
InstallMethod( IsSolution, "For an EquationsHomomorphism and an Equation",
	[IsEvaluation, IsEquation],
	function(hom,eq)
		return IsOne(eq^hom); 
	end);

