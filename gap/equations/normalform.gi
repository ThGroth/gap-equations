InstallOtherMethod( FreeProductElm, "For an EquationGroup and a list",
	[IsEquationGroup,IsList],
	function(eqG,elms)
		return FreeProductElm(eqG,elms,List(elms,function(e)
													if e in eqG!.const then
														return 1; 
													fi; return 2;
												 end) );
	end);

InstallOtherMethod( \*,   "for FreeProductElms and GroupElements",
    [ IsFreeProductElm and IsFreeProductElmRep, IsMultiplicativeElementWithInverse ],
    function( x, y )
    	local pos;
    	pos := PositionProperty(x!.group!.groups,G->y in G);
    	if pos = fail then
    		TryNextMethod();
    	fi;
    	return x*y^Embedding(x!.group,pos);
    end );

InstallOtherMethod( \*,   "for FreeProductElms and GroupElements",
    [ IsMultiplicativeElementWithInverse , IsFreeProductElm and IsFreeProductElmRep ],
    function( y, x )
    	local pos;
    	pos := PositionProperty(x!.group!.groups,G->y in G);
    	if pos = fail then
    		TryNextMethod();
    	fi;
    	return y^Embedding(x!.group,pos)*x;
    end );


InstallMethod(EquationNormalForm, "for an Equation",
	[IsEquation and IsFreeProductElmRep],
	function(x)
		local G,F,EqG,NormalForm,N,H,NormalVars;
		if not IsQuadraticEquation(x) then
			TryNextMethod();
		fi;
		G := x!.const;
		F := x!.free;
		EqG := x!.group;
		
		#Recursive worker function
		NormalForm:= function(eq)
			local case10,case11a,case11b,case3,i,j,t,x,y,Hom,HomIn,N,
				  asInt,v,w,v1,v2,w1,w2,w11,w12,w21,w22,w3;
			Info(InfoEQFP,3,"Call of NormalForm with ",eq);

			case10 := function(w1,v,w2,x)
				# eq = w₁·x⁻·v·x·w₂
				# w₁,w₂ Equations v∈G,x∈F 
				local N,Hom,HomIn,c;
				N := NormalForm(w1*w2);
				Hom := EquationHomomorphism(EqG,[x],[x*w2^-1]);
				HomIn := EquationHomomorphism(EqG,[x],[x*w2]);
				if Length(N[1])=0 then
					return [FreeProductElm(EqG,[x^-1,v,x]),Hom,HomIn];
				fi;
				#Does N end with a constant?
				c:= N[1]!.word[Length(N[1])];
				if c in F then
					return [N[1]*FreeProductElm(EqG,[x^-1,v,x]),Hom*N[2],N[3]*HomIn];
				else
					Hom := EquationHomomorphism(EqG,[x],[x*(c*w2^-1)]);
					HomIn := EquationHomomorphism(EqG,[x],[x*w2*c^-1]);
					return [N[1]*c^-1*(x^-1*v*x)*c,Hom*N[2],N[3]*HomIn];
				fi;
			end;
			case11a := function(w11,w12,v,w2,x)
				# w = w₁₁·v⁻·w₁₂·x⁻·v·x·w₂
				# # w₁₁,w₁₂,w₂ Equations v,x∈F 
				local N,Hom,HomIn;
				N := NormalForm(w11*w12*w2);
				Hom := EquationHomomorphism(EqG,[x,v],[
						w11^-1*x*w11*w12,
						w11^-1*v*w11]);
				HomIn := EquationHomomorphism(EqG,[x,v],[
						w11*x*w12^-1*w11^-1,
						w11*v*w11^-1]);
				return [Comm(v,x)*N[1],Hom*N[2],N[3]*HomIn];
			end;
			case11b := function(w1,v,w21,w22,x)
				# w = w₁·x⁻·v·x·w₂₁·v⁻·w₂₂
				# # w₁,w₂₁,w₂₂ Equations v,x∈F 
				local N,Hom,HomIn;
				N := NormalForm(w1*w21*w22);
				Hom := EquationHomomorphism(EqG,[x,v],[
						w21^-1*w1^-1*x*w1,
						w21^-1*w1^-1*v^-1*w1*w21]);
				HomIn := EquationHomomorphism(EqG,[x,v],[
						w1*w21*x*w1^-1,
						w1*w21*v^-1*w21^-1*w1^-1]);
				return [Comm(x,v)*N[1],Hom*N[2],N[3]*HomIn];
			end;
			case3 := function(x,w2)
				# w = x²·w2
				# w₂ Equation, x∈F
				local N,N2,Hom,HomIn,y,z;
				N := NormalForm(w2);
				N[1]:=FreeProductElmLetterRep(N[1]);
				#Check if N[1] is now still unoriented by checking if it starts with [y,z].
				if Length(N[1])<4 or not N[1]!.word[2] in F or N[1]!.word[1]=N[1]!.word[2] then
					#Already in required form
					return [x^2*N[1],N[2],N[3]];
				else
					y := N[1]!.word[3];
					z := N[1]!.word[4];
					Hom := EquationHomomorphism(EqG,[x,y,z],[
							x*y*z,
					        (y*z)^(x*y*z),
					        (y^-1*x^-1)^z]);
					#TODO If some Error occurs look here!
					HomIn := EquationHomomorphism(EqG,[x,y,z],[
							x^2*y^-1*x^-1,
					        x*y*(x*z*x)^-1,
					        x*z]);
					N2 := case3(z,N[1]{[5..Length(N[1])]});
					return [x^2*y^2*N2[1],Hom*N[2]*N2[2],N2[3]*N[3]*HomIn];
					#return [x^2*y^2*N2[1],Hom*N2[2]*N[2],N[3]*N2[3]*HomIn];
				fi;
			end;
			eq := Equation(FreeProductElmLetterRep(eq));
			
			if Length(eq)<3 then
				return [eq,EquationHomomorphism(EqG,[],[]),EquationHomomorphism(EqG,[],[])];
			fi;
			#Added for the case the const group is also free and hence
			#Length(eq) could be >1 although it is constant.
			if ForAll(eq!.word,x->x in G) then
				return [eq,EquationHomomorphism(EqG,[],[]),EquationHomomorphism(EqG,[],[])];
			fi;
				
			if IsOrientedEquation(eq) then
				#Find x s.t. w=w₁ x⁻¹ v x w₂ with |v| minimal
				t := [];
				Perform(EquationVariables(eq),function(v) t[LetterRepAssocWord(v)[1]]:=0; end);
				for i in [1..Length(eq)] do
					x := eq!.word[i];
					if x in F then
						asInt := LetterRepAssocWord(x)[1];
						t[AbsInt(asInt)]:=i-t[AbsInt(asInt)]; 
					fi;
				od;
				x := AssocWordByLetterRep(FamilyObj(Representative(F)),
								[PositionProperty(t,i->i=Minimum(t))]);
				#Find Decomposition w₁ x⁻¹ v x w₂ 
				Info(InfoEQFP,4,"Oriented Case: Choosing x: ",x);
				i := Position(eq,x^-1);
				j := Position(eq,x);
				if i>j then 
					Hom := EquationHomomorphism(EqG,[x],[x^-1]);
					HomIn := EquationHomomorphism(EqG,[x],[x^-1]);
					j:=Position(eq,x^-1);
					i := Position(eq,x);
				else
					Hom := EquationHomomorphism(EqG,[],[]);
					HomIn := EquationHomomorphism(EqG,[],[]);
				fi;
				w1 := FreeProductElmLetterRep(eq{[1..i-1]});
				v := FreeProductElmLetterRep(eq{[i+1..j-1]});
				w2 := FreeProductElmLetterRep(eq{[j+1..Length(eq)]});
				
				#Decomposition done
				if Length(v)=1 then #Case 1
					v := v!.word[1];
					if v in F then #Case 1.1
						#v->v⁻¹ if v is not a generator. 
						Hom := Hom*EquationHomomorphism(EqG,[Abs(v)],[v]);
						HomIn := EquationHomomorphism(EqG,[Abs(v)],[v])*HomIn;
						i := Position(w1,v^-1);
						if not i = fail then #Case 1.1.a
							w11 := w1{[1..i-1]};
							w12 := w1{[i+1..Length(w1)]};
							N := case11a(w11,w12,Abs(v),w2,x);
							return [N[1],Hom*N[2],N[3]*HomIn];
						else #Case 1.1.b
							i := Position(w2,v^-1);
							if i = fail then 
								Error("Strange Error. Is Equation quadratic?");
							fi;
							w21 := w2{[1..i-1]};
							w22 := w2{[i+1..Length(w2)]};
							N:= case11b(w1,Abs(v),w21,w22,x);
							return [N[1],Hom*N[2],N[3]*HomIn];
						fi;
					else #Case 1.0
						N := case10(w1,v,w2,x);
						return [N[1],Hom*N[2],N[3]*HomIn];
					fi;
				else #Case 2
					y := First(v!.word,e->e in F);
					Hom := Hom*EquationHomomorphism(EqG,[Abs(y)],[y^-1]);
					HomIn := EquationHomomorphism(EqG,[Abs(y)],[y^-1])*HomIn;
					#v = v₁ y v₂
					i := Position(v,y);
					v1 := v{[1..i-1]};
					v2 := v{[i+1..Length(v)]};

					i := Position(w1,y^-1);
					if not i = fail then #Case 2.a
						w11 := w1{[1..i-1]};
						w12 := w1{[i+1..Length(w1)]};
						Hom := Hom*EquationHomomorphism(EqG,[x],[v2^-1*x*(Abs(y)*w12)]);
						HomIn := EquationHomomorphism(EqG,[x],[v2*x*(Abs(y)*w12)^-1])*HomIn;
						N := case11a(w11,v2*v1,x,w12*w2,Abs(y));
						return [N[1],Hom*N[2],N[3]*HomIn];
					else #Case 2.b
						i := Position(w2,y^-1);
						if i = fail then 
							Error("Strange Error. Is Equation quadratic?");
						fi;
						w21 := w2{[1..i-1]};
						w22 := w2{[i+1..Length(w2)]};
						N := case11a(w1*w21,v2*v1,x,w22,Abs(y));
						Hom := Hom*EquationHomomorphism(EqG,[x],[v2^-1*x*w21^-1]);
						HomIn := EquationHomomorphism(EqG,[x],[v2*x*w21])*HomIn;
						return [N[1],Hom*N[2],N[3]*HomIn];
					fi;
				fi; 
			else #so not oriented
				#Find x s.t. w=w₁ x v x w₂ with |v| minimal
				t := [];
				Perform(EquationVariables(eq),function(v) t[LetterRepAssocWord(v)[1]]:=1; end);
				for i in [1..Length(eq)] do
					x := eq!.word[i];
					if x in F then
						asInt := LetterRepAssocWord(x)[1];
						t[AbsInt(asInt)]:=SignInt(t[AbsInt(asInt)])*SignInt(asInt)*(i+1-AbsInt(t[AbsInt(asInt)])); 
					fi;
				od;
				x := AssocWordByLetterRep(FamilyObj(Representative(F)),
							[PositionProperty(t,i->i=Minimum(Filtered(t,IsPosInt)))]);
				Info(InfoEQFP,4,"Unoriented Case: Choosing x: ",x);
				i := Position(eq,x);
				if i=fail then
					Hom := EquationHomomorphism(EqG,[x],[x^-1]);
					HomIn := EquationHomomorphism(EqG,[x],[x^-1]);
					i := Position(eq,x^-1);
					j := Position(eq,x^-1,i);
				else	
					Hom := EquationHomomorphism(EqG,[],[]);
					HomIn := EquationHomomorphism(EqG,[],[]);
					j := Position(eq,x,i);
				fi;
				w1:= eq{[1..i-1]};
				w2:= eq{[i+1..j-1]};
				w3:= eq{[j+1..Length(eq)]};
				Hom := Hom*EquationHomomorphism(EqG,[x],[w1^-1*x*w1*w2^-1]);
				HomIn := EquationHomomorphism(EqG,[x],[w1*x*w2*w1^-1])*HomIn;
				N := case3(x,w1*w2^-1*w3);
				return [N[1],Hom*N[2],N[3]*HomIn];
			fi; #End Nonoriented Case	
		end;
		NormalVars := function(eq)
			local gens,imgs,count,found,x;
			eq := FreeProductElmLetterRep(eq);
			gens := [];
			imgs := [];
			found := [];
			count := 1;
			for x in eq!.word do
				if x in F then
					if not Abs(x) in found then 
						if not Abs(x)=F.(count) then
							Add(gens,Abs(x));
							Add(imgs,F.(count));
						fi;
						Add(found,Abs(x));
						count := count+1;
					fi;
				fi;
			od;
			return [EquationHomomorphism(EqG,gens,imgs),EquationHomomorphism(EqG,imgs,gens)];
		end;
		N := NormalForm(x);
		H :=NormalVars(N[1]);
		return rec(nf := Equation(N[1]^H[1]), hom := N[2]*H[1], homInv:=H[2]*N[3]);
	end);
