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
		Ob := GeneralFreeProduct(FreeProduct(G,Free));
		Ob!.free :=Free;
		Ob!.const :=G;
		SetIsEquationGroup(Ob,true);
		return Ob;
	end);

InstallOtherMethod( EquationGroup, "for one group",
	[IsGroup],
	function(G)
		local Free;
		Free := FreeGroup(infinity,"X");
		SetName(Free,"Free(oo)");
		return EquationGroup(G,Free);
	end);

InstallMethod( VariablesOfEquationGroup, "For an EquationGroup",
	[IsEquationGroup],
	G->G!.free);

InstallMethod( ConstantsOfEquationGroup, "For an EquationGroup",
	[IsEquationGroup],
	G->G!.const);
#################################################################################
####                                                                         ####
####	                          Equations                                  ####
####                                                                         ####
#################################################################################
InstallMethod( Equation, "(Equation) for a list of group elements and unknowns",
	[IsEquationGroup,IsList],
	function(eqG,elms)
		local eq;
		#always reduce equation cyclicaly 
		if Length(elms)>= 1 and not elms[1] in eqG!.free then
			elms := Concatenation(elms{[2..Size(elms)]},[elms[1]]);
		fi;
		eq := FreeProductElmNC(eqG,elms,List(elms,function(e)
													if e in eqG!.free then
														return 2; 
													fi; return 1;
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
			if not elm in eq!.free then
				Add(nw,elm); 
			else
				for i in LetterRepAssocWord(elm) do
					Add(nw,AssocWordByLetterRep(FamilyObj(elm),[i]));
				od;
			fi;
		od;
		Eq:= FreeProductElmLetterRepNC(eq!.group,nw,List(nw,function(e)
													if e in eq!.free then
														return 2;
													fi; return 1;
												 end) );
		return Equation(Eq);
	end);

InstallOtherMethod( EquationLetterRep, "For a list of group elements and unknowns",
	[IsEquationGroup,IsList],
	function(eqG,elms)
		return EquationLetterRep(Equation(eqG,elms));
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



InstallMethod( IsQuadraticEquation, "for a Equation",
		[IsEquation and IsFreeProductElmRep],
		function(x)
			local i,e,Val;
			Val := [];
			for e in EquationVariables(x) do
				Val[LetterRepAssocWord(e)[1]]:=0;
			od;
			for e in x!.word do
				if e in x!.free then
					for i in LetterRepAssocWord(e) do
						i := AbsInt(i);
						Val[i] := Val[i]+1;
						if Val[i]>2 then
							return false;
						fi;
					od;
				fi;
			od;
			return ForAll(Val,i->IsEvenInt(i));
		end
);

InstallMethod( IsOrientedEquation, "for a square Equation",
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
####	                     Constrained Equation                            ####
####                                                                         ####
#################################################################################
InstallMethod( SetEquationConstraint, "for an equation and a list of images",
	[IsEquation,IsList,IsGroupHomomorphism],
	function(eq,const,hom)
		if not Length(const) = Length(EquationVariables(eq)) then 
			Error("There need to be as many images as equation variables.");
		fi;
		if not ForAll(const,x->x in Range(hom)) then
			Error("All constraint components need to be in the image of hom");
		fi;
		eq!.constraint := const;
		eq!.constrainthom := hom;
		SetIsConstrainedEquation(eq,true);
	end
);
InstallOtherMethod( Equation, "for an equation Group, a list of group elements, a constraint and a corresponding homomorphism.",
	[IsEquationGroup, IsList, IsList, IsGroupHomomorphism],
	function(eqG,word,const,hom)
		local eq;
		eq := Equation(eqG,word);
		SetEquationConstraint(eq,const,hom);
		return eq;
	end
);
InstallMethod( IsConstrainedEquation, "for an equation",
	[IsEquation],
	function(eq)
		return IsBound(eq!.constraint) and IsBound(eq!.constrainthom);
	end
);
InstallMethod( ViewObj,   "for constrained equations)",
   [ IsConstrainedEquation and IsFreeProductElmRep ],
    function( x )
		local s;
		Print("Constrained equation in ",EquationVariables(x));
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
								if e in eqG!.free then
									return 2; 
								fi; return 1;
								end));

		ngens := List(gens,gen->LetterRepAssocWord(gen)[1]);
		
		nimgs := List(imgs,function(x)
				if IsList(x) then
					return FreeProductElmNC(eqG,x,fac(x));
				elif x in eqG then
					return x;
				elif x in eqG!.free then
					return FreeProductElmNC(eqG,[x],[2]);	
				#elif x in eqG!.const then
				else
					return FreeProductElmNC(eqG,[x],[1]);
				# else
				# 	Error("Wrong Input!");
				fi; end);
		hom := GroupHomomorphismByFunction(eqG,eqG,function(eq)
			local newword;
			newword := Flat(List(eq!.word,function(x)
					if not x in eq!.group!.free then
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
				return FreeProductElmNC(eqG,newword,fac(newword));
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

InstallOtherMethod( ImageElm,
    "For an EquationHomomorphisms in CompositionMappingRep and an element",
    FamSourceEqFamElm,
    [ IsEquationHomomorphism and IsCompositionMappingRep, IsFreeProductElm ], 0,
    function( map, elm )
    return ImageElm( map!.map2, ImageElm( map!.map1, elm ));
    end );

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
		hom2 := GroupHomomorphismByFunction(eq!.group,eq!.const,q->Product(Image(hom,q)!.word),One(eq!.const));
		SetIsEquationHomomorphism(hom2,true);
		SetEquationHomomorphismImageData(hom2,rec(imgs:=imgs,gens:=gens));
		SetIsEvaluation(hom2,true);
		return hom2;
	end);
InstallMethod( EquationEvaluationNC, "For an Equation, the list of variables and a list of images",
	[IsEquation, IsList, IsList],
	function(eq,gens,imgs)
		local var,hom,hom2;
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
		hom2 := GroupHomomorphismByFunction(eq!.group,eq!.const,q->Product(Image(hom,q)!.word),One(eq!.const));
		SetIsEquationHomomorphism(hom2,true);
		SetEquationHomomorphismImageData(hom2,rec(imgs:=imgs,gens:=gens));
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
		hom2 := GroupHomomorphismByFunction(eqG,eqG!.const,q->Product(Image(hom,q)!.word,One(eqG!.const)));
		SetIsEquationHomomorphism(hom2,true);
		SetEquationHomomorphismImageData(hom2,rec(imgs:=imgs,gens:=gens));
		SetIsEvaluation(hom2,true);
		return hom2;
	end);
InstallOtherMethod( EquationEvaluationNC, "For an Equation, the list of variables and a list of images",
	[IsEquationGroup, IsList, IsList],
	function(eqG,gens,imgs)
		local var,hom,hom2;
		if not Length(imgs)=Length(gens) then
			Error("There must be as many images as generators.");
		fi;
		hom := EquationHomomorphism(eqG,gens,imgs);
		hom2 := GroupHomomorphismByFunction(eqG,eqG!.const,q->Product(Image(hom,q)!.word,One(eqG!.const)));
		SetIsEquationHomomorphism(hom2,true);
		SetEquationHomomorphismImageData(hom2,rec(imgs:=imgs,gens:=gens));
		SetIsEvaluation(hom2,true);
		return hom2;
	end);

InstallMethod( IsEvaluation, "For a group homomorphism",
	[IsGroupHomomorphism],
	h->IsEquationGroup(Source(h)) and Range(h)=Source(h)!.const);
	
InstallMethod( IsSolution, "For an EquationsHomomorphism and an Equation",
	[IsEvaluation, IsEquation],
	function(hom,eq)
		if IsConstrainedEquation(eq) then
			TryNextMethod();
		fi;
		return IsOne(eq^hom); 
	end);

InstallOtherMethod( IsSolution, "For an EquationsHomomorphism and an Equation",
	[IsGroupHomomorphism, IsEquation],
	function(hom,eq)
		if not IsEvaluation(hom) then
			TryNextMethod();
		fi;
		if IsConstrainedEquation(eq) then
			TryNextMethod();
		fi;
		return IsOne(eq^hom); 
	end);

InstallMethod( IsSolution, "For an EquationsHomomorphism and an Equation",
	[IsEvaluation, IsConstrainedEquation],
	function(hom,eq)
		local data;
		if not IsEvaluation(hom) then
			TryNextMethod();
		fi;
		data := EquationHomomorphismImageData(hom);
		return IsOne(eq^hom) and ForAll([1..Size(EquationVariables(eq))],
			i->data.imgs[Position(data.gens,EquationVariables(eq)[i])]^eq!.constrainthom = eq!.constraint[i]) ; 
	end);