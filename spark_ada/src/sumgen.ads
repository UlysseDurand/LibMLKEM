pragma Extensions_Allowed (On);

package SumGen
    with SPARK_Mode => On 
is

    function Is_Pow_Of_Two (A : Positive) return Boolean
        with Pre => A >= 1,
             Post => Is_Pow_Of_Two'Result = ((A = 1) or (A > 1 and then (A mod 2 = 0 and Is_Pow_Of_Two (A / 2)))),
             Subprogram_Variant =>  (Decreases => A), 
             Annotate => (GNATprove, Always_Return);

    
    generic 
        type ElementType is mod <>;
        type IndexRange is range <>;
        type ArrayType is array (IndexRange range <>) of ElementType; 

    package Sum_On_Array 
        with SPARK_Mode => On
    is

        pragma Assert (IndexRange'First = 0);

        function Cut_Last (A : ArrayType) return ArrayType
            with Pre => A'Length > 0,
                 Post => Cut_Last'Result'First = A'First and Cut_Last'Result'Last = A'Last - 1 and
                         (for all I in A'First .. A'Last - 1 => (
                            Cut_Last'Result (I) = A (I)
                         ));

        function "+" (F : ArrayType;
                      G : ArrayType) return ArrayType
            with Pre => F'First = G'First and F'Last = G'Last,
                 Post => "+"'Result'First = F'First and "+"'Result'Last = F'Last and
                         (for all I in F'Range => ("+"'Result (I) = F (I) + G (I)));

        function Sum (A : ArrayType) return ElementType
            with Post => Sum'Result = (if A'Length = 0 then 0 elsif A'Length = 1 then A (A'First) else Sum (Cut_Last (A)) + A (A'Last)),
                 Subprogram_Variant => (Decreases => A'Length),
                 Annotate => (GNATprove, Always_Return);
            
        function Lemma_Add_Associative (A : ElementType;
                                        B : ElementType;
                                        C : ElementType) return Boolean
            with Post => Lemma_Add_Associative'Result and
                         (A + B) + C = A + (B + C);

        function Lemma_Add_Commutative (A : ElementType;
                                        B : ElementType) return Boolean
            with Post => Lemma_Add_Commutative'Result and
                         A + B = B + A;

        function Extract_Even (F : ArrayType) return ArrayType
            with Pre => F'First = 0 and F'Length mod 2 = 0 and F'Length > 1,
                 Post => Extract_Even'Result'First = 0 and Extract_Even'Result'Length = F'Length / 2 and 
                         (for all I in Extract_Even'Result'Range => 
                            Extract_Even'Result (IndexRange (I)) = F (IndexRange (2 * I))
                         );

        function Extract_Odd (F : ArrayType) return ArrayType
            with Pre => F'First = 0 and F'Length mod 2 = 0 and F'Length > 1,
                 Post => Extract_Odd'Result'First = 0 and Extract_Odd'Result'Length = F'Length / 2 and 
                         (for all I in Extract_Odd'Result'Range => 
                            Extract_Odd'Result (IndexRange (I)) = F (IndexRange (2 * I + 1))
                         );

        function Lemma_Split_Odd_Even (A :  ArrayType) return Boolean
            with Pre => A'First = 0 and A'Length mod 2 = 0 and A'Length > 1,
                 Subprogram_Variant => (Decreases => A'Length),
                 Annotate => (GNATprove, Always_Return),
                 Post => Lemma_Split_Odd_Even'Result and
                         Sum (A) = Sum (Extract_Even (A)) + Sum (Extract_Odd (A));

        function Lemma_Sum_Extensional (A : ArrayType;
                                        B : ArrayType) return Boolean
            with Pre => A = B,
                 Subprogram_Variant => (Decreases => A'Length),
                 Annotate => (GNATprove, Always_Return),
                 Post => Lemma_Sum_Extensional'Result and Sum (A) = Sum (B);

        function Scalar_Mult (A : ElementType;
                              B : ArrayType) return ArrayType
            with Post => Scalar_Mult'Result'First = B'First and Scalar_Mult'Result'Last = B'Last and
                        (for all I in B'Range => (Scalar_Mult'Result (I) = A * B (I)));

        function Lemma_Sum_Linear_Scal_Mult (A : ElementType;
                                             B : ArrayType) return Boolean
            with Post => Lemma_Sum_Linear_Scal_Mult'Result and
                         Sum (Scalar_Mult (A, B))= A * Sum (B);

        generic
            with function F (Param1 : ArrayType; Param2 : ElementType; Param3 : IndexRange; B : IndexRange) return ElementType;
            with function G (A : IndexRange) return IndexRange;
        function Compose (Param1 : ArrayType; Param2 : ElementType; Param3 : IndexRange; A : IndexRange) return ElementType;

        generic
            with function Func (Param1 : ArrayType;
                                Param2 : ElementType;
                                Param3 : IndexRange;
                                I : IndexRange) return ElementType;
        function InitialArray (Param1 : ArrayType;
                               Param2 : ElementType;
                               Param3 : IndexRange) return ArrayType
            with Post => (for all I in Param1'Range => InitialArray'Result (I) = Func (Param1, Param2, Param3, I)) and
                         InitialArray'Result'First = Param1'First and InitialArray'Result'Last = Param1'Last; 

        function To_Even (I : IndexRange) return IndexRange
            with Pre => I < IndexRange'Last / 2;
        function To_Even (I : IndexRange) return IndexRange
        is
            (2 * I);

        function To_Odd (I : IndexRange) return IndexRange
            with Pre => I < IndexRange'Last / 2;
        function To_Odd (I : IndexRange) return IndexRange
        is
            (2 * I + 1);

        generic 
            with function Func (Param1 : ArrayType;
                                Param2 : ElementType;
                                Param3 : IndexRange;
                                I : IndexRange) return ElementType; 
        package Generic_Lemma_Split_Sum_Func_Odd_Even
            with SPARK_Mode => On
        is


            function Even_Func is new Compose (Func, To_Even);
            function Odd_Func is new Compose (Func, To_Odd);

            function Even_Terms_Array_Generator is new InitialArray (Even_Func);
            function Odd_Terms_Array_Generator is new InitialArray (Odd_Func);
            function Array_Generator is new InitialArray (Func);
            
            function Lemma_Split_Sum_Func_Odd_Even (Param1 : ArrayType;
                                                    Param2 : ElementType;
                                                    Param3 : IndexRange;
                                                    Length : Integer) return Boolean
                with Pre => Length >= 0 and Length mod 2 = 0,
                     Post => Lemma_Split_Sum_Func_Odd_Even'Result and
                             Sum (Array_Generator (Param1, Param2, Param3)) = 
                             Sum (Even_Terms_Array_Generator (Param1, Param2, Param3)) +
                             Sum (Odd_Terms_Array_Generator (Param1, Param2, Param3));

        end Generic_Lemma_Split_Sum_Func_Odd_Even;

    end Sum_On_Array; 

end SumGen;