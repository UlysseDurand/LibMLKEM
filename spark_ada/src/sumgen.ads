--  This requires the type returnType to have "+"
package SumGen
    with SPARK_Mode => On 
is
    
    generic 
        type ElementType is mod <>;
        type IndexRange is range <>;
        type InputType is array (IndexRange) of ElementType; 

    package Sum_On_Array 
        with SPARK_Mode => On
    is

        pragma Assert (IndexRange'First = 0);

        function Sum (A : InputType;
                              Max_Index : IndexRange) return ElementType
            with Subprogram_Variant => (Decreases => Max_Index),
                 Annotate => (GNATprove, Always_Return);

        function "+" (F : InputType;
                      G : InputType) return InputType
            with Post => (for all I in IndexRange => ("+"'Result (I) = F (I) + G (I)));
            
        function Lemma_Sum_Disjoint (F : InputType;
                                             G : InputType;
                                             Max_Index : IndexRange) return Boolean
            with Subprogram_Variant => (Decreases => Max_Index),
                 Annotate => (GNATprove, Always_Return),
                 Post => Lemma_Sum_Disjoint'Result and
                         Sum (F, Max_Index) + Sum (G, Max_Index) = Sum (F + G, Max_Index); 

        function Lemma_Add_Associative (A : ElementType;
                                        B : ElementType;
                                        C : ElementType) return Boolean
            with Post => Lemma_Add_Associative'Result and
                         (A + B) + C = A + (B + C);

        function Lemma_Add_Commutative (A : ElementType;
                                        B : ElementType) return Boolean
            with Post => Lemma_Add_Commutative'Result and
                         A + B = B + A;

    end Sum_On_Array;

    function Is_Pow_Of_Two (A : Positive) return Boolean
        with Pre => A >= 1,
             Subprogram_Variant =>  (Decreases => A), 
             Annotate => (GNATprove, Always_Return);

    generic
        type ElementType is mod <>;
        type IndexRange is range <>;
        type ArrayType is array (IndexRange range <>) of ElementType;

    package Generic_Split_Sum 
        with SPARK_Mode => On
    is

        pragma Assert (IndexRange'First = 0);

        function Extract_Even (F : ArrayType;
                               Length : Integer) return ArrayType
            with Pre => Length mod 2 = 0 and Length > 1 and Length <= Integer (IndexRange'Last) + 1,
                 Post => (for all I in 0 .. (Length / 2 - 1) => Extract_Even'Result (IndexRange (I)) = F (IndexRange (2 * I)));

        function Extract_Odd (F : ArrayType;
                              Length : Integer) return ArrayType
            with Pre =>  Length mod 2 = 0 and Length > 1 and Length <= Integer (IndexRange'Last) + 1,
                 Post => (for all I in 0 .. (Length / 2 - 1) => Extract_Odd'Result (IndexRange (I)) = F (IndexRange (2 * I + 1)));

        package Summer is new Sum_On_Array (ElementType, IndexRange, ArrayType);

        function Lemma_Split_Odd_Even (A :  ArrayType;
                                       Length : Integer) return Boolean
            with Pre => Length mod 2 = 0 and Length > 1 and Length <= Integer (IndexRange'Last + 1),
                 Post => Lemma_Split_Odd_Even'Result and
                         Summer.Sum (A, IndexRange(Length - 1)) = Summer.Sum (Extract_Even (A, Length), IndexRange(Length / 2 - 1)) + Summer.Sum (Extract_Odd (A, Length), IndexRange (Length / 2 - 1));

    end Generic_Split_Sum; 

    generic 
        type InType is mod <>;
        type OutType is mod <>;
        type IndexRange is range <>;
        with function Func (A : InType) return OutType;
    package Generic_Apply_To_Array 
    is
        type InputTypeA is array (IndexRange) of InType;
        type InputTypeB is array (IndexRange) of OutType;
        function Apply_To_Array (X : InputTypeA) return InputTypeB; 
    end Generic_Apply_To_Array;

end SumGen;