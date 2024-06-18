pragma Extensions_Allowed (On);

package SumGen
    with SPARK_Mode => On 
is

    function Is_Pow_Of_Two (A : Positive) return Boolean
        with Pre => A >= 1,
             Subprogram_Variant =>  (Decreases => A), 
             Annotate => (GNATprove, Always_Return);

    generic
        type InputType is private;
        type IntermediateType is private;
        type ReturnType is private;
        with function F (B : IntermediateType) return ReturnType;
        with function G (A : InputType) return IntermediateType;
    function Compose (A : InputType) return ReturnType;
    
    generic 
        type ElementType is mod <>;
        type IndexRange is range <>;
        type ArrayType is array (IndexRange range <>) of ElementType; 

    package Sum_On_Array 
        with SPARK_Mode => On
    is

        pragma Assert (IndexRange'First = 0);

        function Cut_Last (A : ArrayType) return ArrayType
            with Pre => A'First = 0 and A'Last > A'First,
                 Post => Cut_Last'Result'First = A'First and Cut_Last'Result'Last = A'Last - 1 and
                         (for all I in A'First .. A'Last - 1 => (
                            Cut_Last'Result (I) = A (I)
                         ));

        function "+" (F : ArrayType;
                      G : ArrayType) return ArrayType
            with Pre => F'First = 0 and F'Last >= F'First and F'First = G'First and F'Last = G'Last,
                 Post => "+"'Result'First = F'First and "+"'Result'Last = F'Last and
                         (for all I in F'Range => ("+"'Result (I) = F (I) + G (I)));

        function Sum (A : ArrayType) return ElementType
            with Pre => (A'First = 0 and A'Last >= A'First),
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
            with Pre => F'First = 0 and F'Last >= F'First and F'Length mod 2 = 0 and F'Length > 1,
                 Post => Extract_Even'Result'First = 0 and Extract_Even'Result'Length = F'Length / 2 and 
                         (for all I in 0 .. (F'Length / 2 - 1) => 
                            Extract_Even'Result (IndexRange (I)) = F (IndexRange (2 * I))
                         );

        function Extract_Odd (F : ArrayType) return ArrayType
            with Pre => F'First = 0 and F'Last >= F'First and F'Length mod 2 = 0 and F'Length > 1,
                 Post => Extract_Odd'Result'First = 0 and Extract_Odd'Result'Length = F'Length / 2 and 
                         (for all I in 0 .. (F'Length / 2 - 1) => 
                            Extract_Odd'Result (IndexRange (I)) = F (IndexRange (2 * I + 1))
                         );

        function Lemma_Split_Odd_Even (A :  ArrayType) return Boolean
            with Pre => A'First = 0 and A'Last >= A'First and A'Length mod 2 = 0 and A'Length > 1,
                 Subprogram_Variant => (Decreases => A'Length),
                 Annotate => (GNATprove, Always_Return),
                 Post => Lemma_Split_Odd_Even'Result and
                         Sum (A) = Sum (Extract_Even (A)) + Sum (Extract_Odd (A));

        function Lemma_Sum_Extensional (A : ArrayType;
                                        B : ArrayType) return Boolean
            with Pre => A = B and A'First = 0 and B'First = 0 and A'Last >= A'First and B'Last >= B'First,
                 Subprogram_Variant => (Decreases => A'Length),
                 Annotate => (GNATprove, Always_Return),
                 Post => Lemma_Sum_Extensional'Result and Sum (A) = Sum (B);

        generic
            with function Func (I : IndexRange) return ElementType;
        function InitialArray (Length : Integer) return ArrayType
            with Pre => Length >= 0 and Integer (IndexRange'Last) + 1 >= Length,
                 Post => (for all I in 0 .. IndexRange (Length - 1) => InitialArray'Result (I) = Func (I)); 

        generic 
            with function Func (I : IndexRange) return ElementType; 
        package Generic_Lemma_Split_Sum_Func_Odd_Even
            with SPARK_Mode => On
        is

            function To_Even (I : IndexRange) return IndexRange
            is
                (2 * I);

            function To_Odd (I : IndexRange) return IndexRange
            is
                (2 * I + 1);

            function Even_Func is new Compose (IndexRange, IndexRange, ElementType, Func, To_Even);
            function Odd_Func is new Compose (IndexRange, IndexRange, ElementType, Func, To_Odd);

            function Even_Terms_Array_Generator is new InitialArray (Even_Func);
            function Odd_Terms_Array_Generator is new InitialArray (Odd_Func);
            function Array_Generator is new InitialArray (Func);
            
            function Lemma_Split_Sum_Func_Odd_Even (Length : Integer) return Boolean
                with Pre => Length >= 0 and Length mod 2 = 0,
                     Post => Sum (Array_Generator (Length)) = Sum (Even_Terms_Array_Generator (Length / 2)) +
                                                              Sum (Odd_Terms_Array_Generator (Length / 2));

        end Generic_Lemma_Split_Sum_Func_Odd_Even;

    end Sum_On_Array; 

end SumGen;