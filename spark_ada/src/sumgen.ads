--  This requires the type returnType to have "+"
package SumGen
    with SPARK_Mode => On 
is
    
    generic 
        type P_ElementType is mod <>;
        type P_IndexRange is range <>;
        type InputType is array (P_IndexRange) of P_ElementType; 

    package Sum_On_Array 
        with SPARK_Mode => On
    is
        subtype ElementType is P_ElementType;
        subtype IndexRange is P_IndexRange;

        function Partial_Sum (A : InputType;
                              Max_Index : IndexRange) return ElementType
            with Subprogram_Variant => (Decreases => Max_Index),
                 Annotate => (GNATprove, Always_Return);

        function "+" (F : InputType;
                      G : InputType) return InputType
            with Post => (for all I in IndexRange => ("+"'Result (I) = F (I) + G (I)));

        function Sum (X : InputType) return ElementType 
        is 
            (Partial_Sum (X, IndexRange'Last));
            
        function Lemma_Partial_Sum_Disjoint (F : InputType;
                                             G : InputType;
                                             Max_Index : IndexRange) return Boolean
            with Subprogram_Variant => (Decreases => Max_Index),
                 Annotate => (GNATprove, Always_Return),
                 Post => Lemma_Partial_Sum_Disjoint'Result and
                         Partial_Sum (F, Max_Index) + Partial_Sum (G, Max_Index) = Partial_Sum (F + G, Max_Index); 

        function Lemma_Add_Associative (A : ElementType;
                                        B : ElementType;
                                        C : ElementType) return Boolean
            with Post => Lemma_Add_Associative'Result and
                         (A + B) + C = A + (B + C);

        function Lemma_Add_Commutative (A : ElementType;
                                        B : ElementType) return Boolean
            with Post => Lemma_Add_Commutative'Result and
                         A + B = B + A;

        function Extract_Even (F : InputType) return InputType
            with Post => (for all I in IndexRange => Extract_Even'Result (i) = (if (I mod 2 = 0) then F (i) else 0));

        function Extract_Odd (F : InputType) return InputType
            with Post => (for all I in IndexRange => Extract_Odd'Result (i) = (if (I mod 2 = 0) then 0 else F(i)));

        function Lemma_Split_Odd_Even (A :  InputType) return Boolean
            with Post => Lemma_Split_Odd_Even'Result and
                         Sum (A) = Sum (Extract_Even (A) + Extract_Odd (A));

    end Sum_On_Array;

    generic
        Length : Integer;
        type ElementType is mod <>;
        type SmallIndexRange is range 0 .. (Length - 1);
        type BigIndexRange is range 0 .. (2 * Length - 1);
        type SmallArray is array (SmallIndexRange) of ElementType;
        type BigArray is array (BigIndexRange) of ElementType;

    package Generic_Split_Sum is
        function Small_To_Big (A : SmallIndexRange) return BigIndexRange
        is
            (BigIndexRange(A));

        function Extract_Even (F : BigArray) return SmallArray
            with Post => (for all I in SmallIndexRange => Extract_Even'Result (i) = F (2 * Small_To_Big (I)));

        function Extract_Odd (F : BigArray) return SmallArray
            with Post => (for all I in SmallIndexRange => Extract_Odd'Result (i) = F(2 * Small_To_Big (I) + 1));

        package SmallSummer is new Sum_On_Array (ElementType, SmallIndexRange, SmallArray);
        package BigSummer is new Sum_On_Array (ElementType, BigIndexRange, BigArray);

        function Lemma_Split_Odd_Even (A :  BigArray) return Boolean
            with Post => Lemma_Split_Odd_Even'Result and
                         BigSummer.Sum (A) = SmallSummer.Sum (Extract_Even (A)) + SmallSummer.Sum (Extract_Odd (A));

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